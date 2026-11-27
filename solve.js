import { closeSync, fstatSync, openSync, readSync, writeFileSync } from 'node:fs';
import { buildDiffWasm } from './wasm-core.js';

export const FORMAT = 'makefun-diff/1';
export const CONTEXT = 3;

const wasm = buildDiffWasm();
let memBuf = Buffer.from(wasm.memory.buffer);
let utf16Mod = null;

function countLinesStr(str) {
  let cnt = 0;
  let p = 0;
  const len = str.length;
  while (p < len) {
    const nl = str.indexOf('\n', p);
    cnt++;
    if (nl === -1) break;
    p = nl + 1;
  }
  return cnt;
}

export function diffPatch(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const oldStr = input.old;
  const newStr = input.new;
  const oLen = oldStr.length;
  const nLen = newStr.length;

  if (oLen === nLen && oldStr === newStr) {
    const cnt = countLinesStr(oldStr);
    return `${FORMAT} old=${cnt} new=${cnt} hunks=0 deleted=0 inserted=0\n`;
  }

  if (Buffer.byteLength(oldStr) === oLen && Buffer.byteLength(newStr) === nLen) {
    const nBase = wasm.prepareInput(oLen, nLen);
    if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
    if (oLen > 0) memBuf.write(oldStr, 0, oLen, 'latin1');
    if (nLen > 0) memBuf.write(newStr, nBase, nLen, 'latin1');
    const outLen = wasm.solveAscii();
    if (outLen >= 0) {
      if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
      const outBase = wasm.getOutBase();
      return memBuf.toString('latin1', outBase, outBase + outLen);
    }
  }

  if (!utf16Mod) {
    const { createRequire } = process.getBuiltinModule('node:module');
    utf16Mod = createRequire(import.meta.url)('./utf16-fallback.cjs');
  }
  return utf16Mod.diffPatchUtf16(oldStr, newStr);
}

export function run(input) {
  return diffPatch(input);
}

export function runCasesFile(inputPath, outputPath) {
  const fd = openSync(inputPath, 'r');
  const size = fstatSync(fd).size;
  const jsonBase = wasm.prepareBatch(size);
  if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
  let got = 0;
  while (got < size) {
    const n = readSync(fd, memBuf, jsonBase + got, size - got, got);
    if (n === 0) break;
    got += n;
  }
  closeSync(fd);

  const outLen = wasm.solveBatchJson();
  if (outLen >= 0) {
    if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
    const outBase = wasm.getBatchOutBase();
    writeFileSync(outputPath, memBuf.subarray(outBase, outBase + outLen));
    return;
  }

  if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
  const cases = JSON.parse(memBuf.toString('utf8', jsonBase, jsonBase + got));
  const answers = new Array(cases.length);
  for (let i = 0; i < cases.length; i++) {
    answers[i] = diffPatch(cases[i].input);
  }
  writeFileSync(outputPath, JSON.stringify(answers));
}
