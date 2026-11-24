// Tiny stack VM (ISA v1): runs every program in the input dir, writes what
// each printed plus its exit code.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const STEP_LIMIT = 1000000;
const OUTPUT_LIMIT = 65536;
const MIN_INT = -2147483648;

const TRAP = { UNDERFLOW: 2, OVERFLOW: 3, DIV_ZERO: 4, BAD_OPCODE: 5, MEMORY: 6,
  CALL_DEPTH: 7, RET_EMPTY: 8, PC: 9, STEPS: 10, OUTPUT: 11 } as const;

function readOrEmpty(path: string): Uint8Array {
  try {
    return readFileSync(path);
  } catch {
    return new Uint8Array(0);
  }
}

// Runs one program; returns its output bytes and exit code.
function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const data = new Int32Array(256);
  let sp = 0;
  const calls = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(OUTPUT_LIMIT);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;

  const end = (code: number) => ({ out: out.slice(0, olen), code });

  for (;;) {
    if (steps === STEP_LIMIT) return end(TRAP.STEPS);
    if (pc < 0 || pc >= n) return end(TRAP.PC);
    const op = prog[pc];
    steps++;
    pc++;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01: {
        if (pc >= n) return end(TRAP.PC);
        if (sp === 256) return end(TRAP.OVERFLOW);
        data[sp++] = (prog[pc++] << 24) >> 24;
        break;
      }
      case 0x02: {
        if (pc + 3 >= n) return end(TRAP.PC);
        if (sp === 256) return end(TRAP.OVERFLOW);
        data[sp++] = prog[pc] | (prog[pc + 1] << 8) | (prog[pc + 2] << 16) | (prog[pc + 3] << 24);
        pc += 4;
        break;
      }
      case 0x03:
        if (sp < 1) return end(TRAP.UNDERFLOW);
        sp--;
        break;
      case 0x04:
        if (sp < 1) return end(TRAP.UNDERFLOW);
        if (sp === 256) return end(TRAP.OVERFLOW);
        data[sp] = data[sp - 1];
        sp++;
        break;
      case 0x05: {
        if (sp < 2) return end(TRAP.UNDERFLOW);
        const t = data[sp - 1];
        data[sp - 1] = data[sp - 2];
        data[sp - 2] = t;
        break;
      }
      case 0x06:
        if (sp < 2) return end(TRAP.UNDERFLOW);
        if (sp === 256) return end(TRAP.OVERFLOW);
        data[sp] = data[sp - 2];
        sp++;
        break;
      case 0x07: {
        if (sp < 3) return end(TRAP.UNDERFLOW);
        const a = data[sp - 3];
        data[sp - 3] = data[sp - 2];
        data[sp - 2] = data[sp - 1];
        data[sp - 1] = a;
        break;
      }
      case 0x17:
        if (sp < 1) return end(TRAP.UNDERFLOW);
        data[sp - 1] = -data[sp - 1] | 0;
        break;
      case 0x1b:
        if (sp < 1) return end(TRAP.UNDERFLOW);
        data[sp - 1] = ~data[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (sp < 2) return end(TRAP.UNDERFLOW);
        const b = data[sp - 1];
        const a = data[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(TRAP.DIV_ZERO);
          r = a === MIN_INT && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(TRAP.DIV_ZERO);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(TRAP.DIV_ZERO);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(TRAP.DIV_ZERO);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        data[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        if (pc + 1 >= n) return end(TRAP.PC);
        const rel = ((prog[pc] | (prog[pc + 1] << 8)) << 16) >> 16;
        pc += 2;
        let take = true;
        if (op !== 0x30) {
          if (sp < 1) return end(TRAP.UNDERFLOW);
          const v = data[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc += rel;
        break;
      }
      case 0x33: {
        if (pc + 1 >= n) return end(TRAP.PC);
        if (cp === 64) return end(TRAP.CALL_DEPTH);
        calls[cp++] = pc + 2;
        pc = prog[pc] | (prog[pc + 1] << 8);
        break;
      }
      case 0x34:
        if (cp === 0) return end(TRAP.RET_EMPTY);
        pc = calls[--cp];
        break;
      case 0x40: {
        if (sp < 1) return end(TRAP.UNDERFLOW);
        const addr = data[sp - 1];
        if (addr < 0 || addr >= 256) return end(TRAP.MEMORY);
        data[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        if (sp < 2) return end(TRAP.UNDERFLOW);
        const addr = data[sp - 1];
        const v = data[sp - 2];
        if (addr < 0 || addr >= 256) return end(TRAP.MEMORY);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: {
        if (sp < 1) return end(TRAP.UNDERFLOW);
        const s = String(data[sp - 1]);
        if (olen + s.length > OUTPUT_LIMIT) return end(TRAP.OUTPUT);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (sp < 1) return end(TRAP.UNDERFLOW);
        if (olen + 1 > OUTPUT_LIMIT) return end(TRAP.OUTPUT);
        out[olen++] = data[--sp] & 255;
        break;
      case 0x52:
        if (sp === 256) return end(TRAP.OVERFLOW);
        data[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        if (sp < 1) return end(TRAP.UNDERFLOW);
        return end(data[--sp] & 255);
      default:
        return end(TRAP.BAD_OPCODE);
    }
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const result = run(
    readOrEmpty(join(IN_DIR, id, 'program.bin')),
    readOrEmpty(join(IN_DIR, id, 'input.bin')),
  );
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), result.out);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${result.code}\n`);
}
