// Tiny stack VM: a complete interpreter of make.fun's tiny stack ISA v1.
// ISA.md states the rules; vm.mjs is authoritative — this follows vm.mjs
// step for step: same check order, same trap codes, same wrapping arithmetic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK_MAX = 256;
const CALL_MAX = 64;
const MEM_WORDS = 256;
const STEP_MAX = 1_000_000;
const OUT_MAX = 65_536;

// Trap exit codes (ISA.md "Traps").
const TRAP = { UNDERFLOW: 2, OVERFLOW: 3, DIV_ZERO: 4, BAD_OPCODE: 5, MEMORY: 6, CALL_DEPTH: 7, RET_EMPTY: 8, PC: 9, STEPS: 10, OUTPUT: 11 };

// [imm bytes, pops, pushes] per opcode; undefined = unknown opcode (trap 5).
const LOW = [[0,0,0],[1,0,1],[4,0,1],[0,1,0],[0,1,2],[0,2,2],[0,2,3],[0,3,3]];
function spec(op: number) {
  if (op < 8) return LOW[op]; // 00 HALT, 01 PUSH8, 02 PUSH32, 03 POP, 04 DUP, 05 SWAP, 06 OVER, 07 ROT
  if (op === 0x17 || op === 0x1b) return [0, 1, 1]; // NEG, NOT
  if (op >= 0x10 && op <= 0x22 && op !== 0x1f) return [0, 2, 1]; // ADD..LTU; 0x1f is no opcode
  if (op === 0x30 || op === 0x33) return [2, 0, 0]; // JMP, CALL
  if (op === 0x31 || op === 0x32) return [2, 1, 0]; // JZ, JNZ
  if (op === 0x34) return [0, 0, 0]; // RET
  if (op === 0x40) return [0, 1, 1]; // LOAD
  if (op === 0x41) return [0, 2, 0]; // STORE
  if (op === 0x50 || op === 0x51 || op === 0x53) return [0, 1, 0]; // PRINT, PUTC, EXIT
  if (op === 0x52) return [0, 0, 1]; // IN
  return undefined;
}

// Run one program on its input bytes; returns its output bytes and exit code.
function run(p: Uint8Array, inp: Uint8Array) {
  // S data stack, C call stack, M memory, o output buffer.
  const S = new Int32Array(STACK_MAX);
  const C = new Int32Array(CALL_MAX);
  const M = new Int32Array(MEM_WORDS);
  const o = new Uint8Array(OUT_MAX);
  let sp = 0, cp = 0, ip = 0, pc = 0, steps = 0, len = 0;
  const done = (code: number) => ({ out: o.subarray(0, len), code });

  for (;;) {
    // ISA.md check order: steps, pc, opcode, immediate.
    if (steps === STEP_MAX) return done(TRAP.STEPS);
    if (pc < 0 || pc >= p.length) return done(TRAP.PC);
    const op = p[pc];
    const s = spec(op);
    if (s === undefined) return done(TRAP.BAD_OPCODE);
    const [imm, pops, pushes] = s;
    if (pc + imm >= p.length) return done(TRAP.PC);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(TRAP.UNDERFLOW);
    if (sp - pops + pushes > STACK_MAX) return done(TRAP.OVERFLOW);
    pc = next;

    // Two-in, one-out ops (ADD..LTU) share a stack shape; dispatch on it.
    if (pops === 2 && pushes === 1) {
      const b = S[sp - 1], a = S[sp - 2];
      const ua = a >>> 0, ub = b >>> 0; // unsigned views, for DIVU/MODU/LTU
      if (op >= 0x13 && op <= 0x16 && b === 0) return done(TRAP.DIV_ZERO);
      let r: number;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
      else if (op === 0x14) r = b === -1 ? 0 : (a % b) | 0;
      else if (op === 0x15) r = Math.floor(ua / ub) | 0;
      else if (op === 0x16) r = (ua % ub) | 0;
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = ua < ub ? 1 : 0; // LTU
      sp -= 2;
      S[sp++] = r;
      continue;
    }

    switch (op) {
      case 0x00: return done(0);
      case 0x01: S[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: S[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: S[sp] = S[sp - 1]; sp++; break;
      case 0x05: [S[sp - 1], S[sp - 2]] = [S[sp - 2], S[sp - 1]]; break;
      case 0x06: S[sp] = S[sp - 2]; sp++; break;
      case 0x07: [S[sp - 3], S[sp - 2], S[sp - 1]] = [S[sp - 2], S[sp - 1], S[sp - 3]]; break;
      case 0x17: S[sp - 1] = -S[sp - 1] | 0; break; // NEG; -(-2147483648) wraps to itself
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16; // signed 16-bit offset
        let take = op === 0x30;
        if (!take) {
          const v = S[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: unsigned 16-bit target
        if (cp === CALL_MAX) return done(TRAP.CALL_DEPTH);
        C[cp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(TRAP.RET_EMPTY);
        pc = C[--cp];
        break;
      case 0x40: {
        const addr = S[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return done(TRAP.MEMORY);
        S[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: (v addr -- ), addr is on top
        const addr = S[sp - 1], v = S[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return done(TRAP.MEMORY);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        const text = String(S[sp - 1]);
        if (len + text.length > OUT_MAX) return done(TRAP.OUTPUT); // writes nothing
        sp--;
        for (let i = 0; i < text.length; i++) o[len++] = text.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: low byte
        if (len + 1 > OUT_MAX) return done(TRAP.OUTPUT);
        o[len++] = S[--sp] & 255;
        break;
      case 0x52: // IN: -1 once the input is used up
        S[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT: low byte of the value
        return done(S[--sp] & 255);
    }
  }
}

// Entry point: answer every instance in the input directory, in one run.
// MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR override /input and /output.
const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(INPUT_DIR).sort()) {
  const { out, code } = run(readFileSync(join(INPUT_DIR, id, 'program.bin')), readFileSync(join(INPUT_DIR, id, 'input.bin')));
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'stdout.bin'), out);
  writeFileSync(join(OUTPUT_DIR, id, 'exit.txt'), code + '\n');
}
