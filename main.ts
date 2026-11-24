import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const SL = 1000000;
const OL = 65536;
const MIN_INT = -2147483648;

const TRAP = { UNDERFLOW: 2, OVERFLOW: 3, DIV_ZERO: 4, BAD_OPCODE: 5, MEMORY: 6,
  CALL_DEPTH: 7, RET_EMPTY: 8, PC: 9, STEPS: 10, OUTPUT: 11 } as const;
const U=TRAP.UNDERFLOW,V=TRAP.OVERFLOW;

function rd(path: string): Uint8Array {
  try {
    return readFileSync(path);
  } catch {
    return new Uint8Array(0);
  }
}

function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const data = new Int32Array(256);
  let sp = 0;
  const calls = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(OL);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;

  const end = (code: number) => ({ out: out.slice(0, olen), code });

  for (;;) {
    if (steps === SL) return end(TRAP.STEPS);
    if (pc < 0 || pc >= n) return end(TRAP.PC);
    const op = prog[pc];
    steps++;
    pc++;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01: {
        if (pc >= n) return end(TRAP.PC);
        if (sp === 256) return end(V);
        data[sp++] = (prog[pc++] << 24) >> 24;
        break;
      }
      case 0x02: {
        if (pc + 3 >= n) return end(TRAP.PC);
        if (sp === 256) return end(V);
        data[sp++] = prog[pc] | (prog[pc + 1] << 8) | (prog[pc + 2] << 16) | (prog[pc + 3] << 24);
        pc += 4;
        break;
      }
      case 0x03:
        if (sp < 1) return end(U);
        sp--;
        break;
      case 0x04:
        if (sp < 1) return end(U);
        if (sp === 256) return end(V);
        data[sp] = data[sp - 1];
        sp++;
        break;
      case 0x05: {
        if (sp < 2) return end(U);
        const t = data[sp - 1];
        data[sp - 1] = data[sp - 2];
        data[sp - 2] = t;
        break;
      }
      case 0x06:
        if (sp < 2) return end(U);
        if (sp === 256) return end(V);
        data[sp] = data[sp - 2];
        sp++;
        break;
      case 0x07: {
        if (sp < 3) return end(U);
        const a = data[sp - 3];
        data[sp - 3] = data[sp - 2];
        data[sp - 2] = data[sp - 1];
        data[sp - 1] = a;
        break;
      }
      case 0x17:
        if (sp < 1) return end(U);
        data[sp - 1] = -data[sp - 1] | 0;
        break;
      case 0x1b:
        if (sp < 1) return end(U);
        data[sp - 1] = ~data[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (sp < 2) return end(U);
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
          if (sp < 1) return end(U);
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
        if (sp < 1) return end(U);
        const addr = data[sp - 1];
        if (addr < 0 || addr >= 256) return end(TRAP.MEMORY);
        data[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        if (sp < 2) return end(U);
        const addr = data[sp - 1];
        const v = data[sp - 2];
        if (addr < 0 || addr >= 256) return end(TRAP.MEMORY);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: {
        if (sp < 1) return end(U);
        const s = String(data[sp - 1]);
        if (olen + s.length > OL) return end(TRAP.OUTPUT);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (sp < 1) return end(U);
        if (olen + 1 > OL) return end(TRAP.OUTPUT);
        out[olen++] = data[--sp] & 255;
        break;
      case 0x52:
        if (sp === 256) return end(V);
        data[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        if (sp < 1) return end(U);
        return end(data[--sp] & 255);
      default:
        return end(TRAP.BAD_OPCODE);
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const result = run(
    rd(join(I, id, 'program.bin')),
    rd(join(I, id, 'input.bin')),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), result.out);
  writeFileSync(join(O, id, 'exit.txt'), `${result.code}\n`);
}
