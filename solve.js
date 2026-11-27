import { closeSync, openSync, readFileSync, readSync, writeFileSync, writeSync } from 'node:fs';
import { buildDiffWasm } from './wasm-core.js';

export const FORMAT = 'makefun-diff/1';
export const CONTEXT = 3;

const WIN_BASE = 64;
const INIT_WIN_CAP = 2588672; // 2.47 MB sliding window so each practice case fits in-place
const OPEN_BRACKET = Buffer.from('[');
const CLOSE_BRACKET = Buffer.from(']');

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

function getUtf16() {
  if (!utf16Mod) {
    const { createRequire } = process.getBuiltinModule('node:module');
    utf16Mod = createRequire(import.meta.url)('./utf16-fallback.cjs');
  }
  return utf16Mod;
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

  return getUtf16().diffPatchUtf16(oldStr, newStr);
}

export function run(input) {
  return diffPatch(input);
}

function readFill(fd, buf, offset, maxBytes) {
  let got = 0;
  let eof = 0;
  while (got < maxBytes) {
    const n = readSync(fd, buf, offset + got, maxBytes - got, null);
    if (n === 0) { eof = 1; break; }
    got += n;
  }
  return [got, eof];
}

function writeAll(fd, buf, off, len) {
  let w = 0;
  while (w < len) {
    w += writeSync(fd, buf, off + w, len - w);
  }
}

export function runCasesFile(inputPath, outputPath) {
  let winCap = INIT_WIN_CAP;
  const fd = openSync(inputPath, 'r');
  const outFd = openSync(outputPath, 'w');
  let winLen = 0;
  let eof = 0;
  try {
    wasm.ensureWin(WIN_BASE + winCap);
    if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
    const [got0, eof0] = readFill(fd, memBuf, WIN_BASE, winCap);
    winLen = got0;
    eof = eof0;
    wasm.streamInit(WIN_BASE, WIN_BASE + winLen, eof, WIN_BASE + winCap);

    for (;;) {
      const rc = wasm.streamNext();
      if (rc > 0) {
        if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
        writeAll(outFd, memBuf, wasm.getStreamOutBase(), rc);
      } else if (rc === 0) {
        if (wasm.getCaseIdx() === 0) writeAll(outFd, OPEN_BRACKET, 0, 1);
        writeAll(outFd, CLOSE_BRACKET, 0, 1);
        return;
      } else if (rc === -2) {
        if (eof) break;
        if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
        const keep = wasm.getWinKeep();
        const rem = WIN_BASE + winLen - keep;
        if (keep === WIN_BASE && rem >= winCap) {
          winCap *= 2;
          wasm.ensureWin(WIN_BASE + winCap);
          if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
          const [got, eofNow] = readFill(fd, memBuf, WIN_BASE + rem, winCap - rem);
          winLen = rem + got;
          eof = eofNow;
        } else {
          if (rem > 0) memBuf.copyWithin(WIN_BASE, keep, WIN_BASE + winLen);
          const [got, eofNow] = readFill(fd, memBuf, WIN_BASE + rem, winCap - rem);
          winLen = rem + got;
          eof = eofNow;
        }
        wasm.streamRefill(WIN_BASE + winLen, eof, WIN_BASE + winCap);
      } else if (rc === -3) {
        if (memBuf.buffer !== wasm.memory.buffer) memBuf = Buffer.from(wasm.memory.buffer);
        const cs = wasm.getCaseStart();
        const ce = wasm.getCaseEnd();
        const c = JSON.parse(memBuf.toString('utf8', cs, ce));
        const ans = JSON.stringify(diffPatch(c.input));
        const prefix = wasm.getCaseIdx() === 1 ? '[' : ',';
        const chunk = Buffer.from(prefix + ans, 'utf8');
        writeAll(outFd, chunk, 0, chunk.length);
      } else {
        break;
      }
    }
  } finally {
    closeSync(fd);
    closeSync(outFd);
  }

  // Fallback for non-standard JSON formatting
  const cases = JSON.parse(readFileSync(inputPath, 'utf8'));
  const answers = new Array(cases.length);
  for (let i = 0; i < cases.length; i++) answers[i] = diffPatch(cases[i].input);
  writeFileSync(outputPath, JSON.stringify(answers));
}
