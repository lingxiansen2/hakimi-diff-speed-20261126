// Compact data-driven symbolic WebAssembly SIMD128 bytecode compiler for zero-JSON exact Myers diff.
// Compiles directly into a single preallocated Uint8Array in ~1 ms with zero external dependencies.

const I32 = 0x7f, I64 = 0x7e, V128 = 0x7b, VOID = 0x40;
const KEEP = 0, DELETE = 1, INSERT = 2;

// Standard WASM 1.0 opcodes
const UNR = 0x00, BLK = 0x02, LOOP = 0x03, IF = 0x04, ELSE = 0x05, END = 0x0b;
const BR = 0x0c, BRIF = 0x0d, RET = 0x0f, CALL = 0x10, DROP = 0x1a, SEL = 0x1b;
const GET = 0x20, SET = 0x21, TEE = 0x22, GGET = 0x23, GSET = 0x24;
const LD32 = 0x28, LD64 = 0x29, LD8 = 0x2d, ST32 = 0x36, ST64 = 0x37, ST8 = 0x3a;
const MEMSZ = 0x3f, MEMGR = 0x40, I32C = 0x41, I64C = 0x42;
const EQZ = 0x45, EQ = 0x46, NE = 0x47, LTS = 0x48, LTU = 0x49, GTS = 0x4a, GTU = 0x4b, LES = 0x4c, LEU = 0x4d, GES = 0x4e, GEU = 0x4f;
const I64EQZ = 0x50, I64EQ = 0x51, I64NE = 0x52;
const CLZ = 0x67, CTZ = 0x68, POP = 0x69;
const ADD = 0x6a, SUB = 0x6b, MUL = 0x6c, DIVU = 0x6e, REMU = 0x70, AND = 0x71, OR = 0x72, XOR = 0x73, SHL = 0x74, SHRS = 0x75, SHRU = 0x76;
const I64CTZ = 0x7a, I64SUB = 0x7d, I64MUL = 0x7e, I64AND = 0x83, I64OR = 0x84, I64XOR = 0x85, I64SHL = 0x86, I64SHRU = 0x88;
const WRAP = 0xa7, EXTU = 0xad;

// Symbolic multi-byte / SIMD128 / array-access macro opcodes (< 0)
const LD32U = -1, VLD = -2, VST = -3, VSPLAT8 = -4, VEQ8 = -5, VLTS8 = -6, VBM8 = -7, VOR = -8;
const MCOPY = -9, MFILL = -10;
const LA32 = -11, LA64 = -12, LA8 = -13, AP32 = -14;
const SA32L = -15, SA32C = -16, SA8L = -17, SA8C = -18;
const LD32_L = -19, ST32_L = -20, ST32_C = -21;

function writeUleb(buf, p, v) {
  v >>>= 0;
  while (v >= 0x80) { buf[p++] = (v & 0x7f) | 0x80; v >>>= 7; }
  buf[p++] = v;
  return p;
}

function writeSleb32(buf, p, v) {
  v |= 0;
  while (true) {
    const b = v & 0x7f; v >>= 7;
    if ((v === 0 && (b & 0x40) === 0) || (v === -1 && (b & 0x40) !== 0)) { buf[p++] = b; return p; }
    buf[p++] = b | 0x80;
  }
}

function writeSleb64LH(buf, p, lo, hi) {
  lo >>>= 0; hi |= 0;
  while (true) {
    const b = lo & 0x7f;
    lo = ((lo >>> 7) | (hi << 25)) >>> 0;
    hi >>= 7;
    if ((hi === 0 && lo === 0 && (b & 0x40) === 0) || (hi === -1 && lo === 0xffffffff && (b & 0x40) !== 0)) { buf[p++] = b; return p; }
    buf[p++] = b | 0x80;
  }
}

function encodeBody(ops, out, p) {
  let op, v, g, idx, val;
  for (let i = 0; i < ops.length; ) {
    op = ops[i++];
    if (op >= 0x45) {
      out[p++] = op;
    } else if (op >= 0) {
      out[p++] = op;
      switch (op) {
        case I32C:
          v = ops[i++];
          if (v >= -64 && v < 64) out[p++] = v & 0x7f;
          else p = writeSleb32(out, p, v);
          break;
        case I64C:
          p = writeSleb64LH(out, p, ops[i++], ops[i++]);
          break;
        case GET: case SET: case TEE: case GGET: case GSET: case CALL: case BR: case BRIF:
          v = ops[i++];
          if (v < 128) out[p++] = v; else p = writeUleb(out, p, v);
          break;
        case LD32: case ST32:
          out[p++] = 2; v = ops[i++];
          if (v < 128) out[p++] = v; else p = writeUleb(out, p, v);
          break;
        case LD64: case LD8: case ST64: case ST8:
          out[p++] = 0; v = ops[i++];
          if (v < 128) out[p++] = v; else p = writeUleb(out, p, v);
          break;
        case BLK: case LOOP: case IF:
          out[p++] = ops[i++];
          break;
        case MEMSZ: case MEMGR:
          out[p++] = 0;
          break;
      }
    } else {
      switch (op) {
        case LD32U: out[p++] = LD32; out[p++] = 0; v = ops[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
        case VLD: out[p++] = 0xfd; out[p++] = 0x00; out[p++] = 0; v = ops[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
        case VST: out[p++] = 0xfd; out[p++] = 0x0b; out[p++] = 0; v = ops[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
        case VSPLAT8: out[p++] = 0xfd; out[p++] = 0x0f; break;
        case VEQ8: out[p++] = 0xfd; out[p++] = 0x23; break;
        case VLTS8: out[p++] = 0xfd; out[p++] = 0x25; break;
        case VBM8: out[p++] = 0xfd; out[p++] = 0x64; break;
        case VOR: out[p++] = 0xfd; out[p++] = 0x50; break;
        case MCOPY: out[p++] = 0xfc; out[p++] = 0x0a; out[p++] = 0; out[p++] = 0; break;
        case MFILL: out[p++] = 0xfc; out[p++] = 0x0b; out[p++] = 0; break;
        case LA32:
          g = ops[i++]; idx = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 2; out[p++] = SHL; out[p++] = ADD; out[p++] = LD32; out[p++] = 2; out[p++] = 0;
          break;
        case LA64:
          g = ops[i++]; idx = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 3; out[p++] = SHL; out[p++] = ADD; out[p++] = LD64; out[p++] = 0; out[p++] = 0;
          break;
        case LA8:
          g = ops[i++]; idx = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = ADD; out[p++] = LD8; out[p++] = 0; out[p++] = 0;
          break;
        case AP32:
          g = ops[i++]; idx = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 2; out[p++] = SHL; out[p++] = ADD;
          break;
        case SA32L:
          g = ops[i++]; idx = ops[i++]; val = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 2; out[p++] = SHL; out[p++] = ADD;
          out[p++] = GET; out[p++] = val; out[p++] = ST32; out[p++] = 2; out[p++] = 0;
          break;
        case SA32C:
          g = ops[i++]; idx = ops[i++]; val = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 2; out[p++] = SHL; out[p++] = ADD;
          out[p++] = I32C; if (val >= -64 && val < 64) out[p++] = val & 0x7f; else p = writeSleb32(out, p, val);
          out[p++] = ST32; out[p++] = 2; out[p++] = 0;
          break;
        case SA8L:
          g = ops[i++]; idx = ops[i++]; val = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = ADD; out[p++] = GET; out[p++] = val; out[p++] = ST8; out[p++] = 0; out[p++] = 0;
          break;
        case SA8C:
          g = ops[i++]; idx = ops[i++]; val = ops[i++];
          out[p++] = GGET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = ADD; out[p++] = I32C; out[p++] = val & 0x7f; out[p++] = ST8; out[p++] = 0; out[p++] = 0;
          break;
        case LD32_L:
          g = ops[i++]; idx = ops[i++];
          out[p++] = GET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 2; out[p++] = SHL; out[p++] = ADD; out[p++] = LD32; out[p++] = 2; out[p++] = 0;
          break;
        case ST32_L:
          g = ops[i++]; idx = ops[i++]; val = ops[i++];
          out[p++] = GET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 2; out[p++] = SHL; out[p++] = ADD;
          out[p++] = GET; out[p++] = val; out[p++] = ST32; out[p++] = 2; out[p++] = 0;
          break;
        case ST32_C:
          g = ops[i++]; idx = ops[i++]; val = ops[i++];
          out[p++] = GET; out[p++] = g; out[p++] = GET; out[p++] = idx;
          out[p++] = I32C; out[p++] = 2; out[p++] = SHL; out[p++] = ADD;
          out[p++] = I32C; if (val >= -64 && val < 64) out[p++] = val & 0x7f; else p = writeSleb32(out, p, val);
          out[p++] = ST32; out[p++] = 2; out[p++] = 0;
          break;
      }
    }
  }
  return p;
}

export function buildDiffWasm() {
  const types = [];
  const typeMap = new Map();
  const internType = (params, results) => {
    const key = `${params.join(',')}=>${results.join(',')}`;
    let id = typeMap.get(key);
    if (id === undefined) { id = types.length; types.push({ params, results }); typeMap.set(key, id); }
    return id;
  };

  let gc = 0;
  const g = () => gc++;
  const G = {
    oBase: g(), oLen: g(), nBase: g(), nLen: g(), arenaBase: g(),
    oStart: g(), nStart: g(), oEnd: g(), nEnd: g(),
    prefix: g(), suffix: g(), n: g(), m: g(), arenaPtr: g(),
    oBounds: g(), oHash: g(), nBounds: g(), nHash: g(),
    buckets: g(), hMask: g(),
    A: g(), B: g(), cntA: g(), cntB: g(), posB: g(), seen: g(),
    remDel: g(), remIns: g(), prefUniqA: g(), prefUniqB: g(),
    tailsVal: g(), tailsA: g(), prevIdx: g(), ancA: g(), ancB: g(), gapD: g(),
    isUniq: g(), inLIS: g(), usedLIS: g(), isBridge: g(), grid64: g(),
    segX: g(), segY: g(), segU: g(), numSegs: g(),
    gVp: g(), gVc: g(), Vp: g(), Vc: g(), repBuf: g(),
    ckptMeta: g(), ckptData: g(), ckptDataPtr: g(), ckptCap: g(),
    bShift: g(), bStep: g(), bMask: g(), ansD: g(), ansK: g(), U: g(),
    revKind: g(), revCount: g(), opLen: g(),
    changesO: g(), changesP: g(), changesD: g(), changesI: g(), numChanges: g(),
    hStart: g(), hEnd: g(), numHunks: g(), deleted: g(), inserted: g(),
    outBase: g(), outEnd: g(), jsonLen: g(), jsonCur: g(), batchOutBase: g(),
  };

  let fc = 0;
  const fnId = () => fc++;
  const F = {
    ensureMem: fnId(), prepareInput: fnId(), prepareBatch: fnId(),
    countLines: fnId(), trimPrefixSuffix: fnId(), scanHashSide: fnId(), scanLines: fnId(), internLines: fnId(),
    buildBoundsAndUB: fnId(), myersSub: fnId(), solveMyers: fnId(), buildChangesAndHunks: fnId(),
    writeDec: fnId(), pushLineOut: fnId(), buildPatch: fnId(),
    solveAscii: fnId(), getOutBase: fnId(), getBatchOutBase: fnId(),
    skipWs: fnId(), skipJsonStr: fnId(), unescapeJsonStr: fnId(), escapeJsonOut: fnId(), expectByte: fnId(), solveBatchJson: fnId(),
  };

  const funcs = new Array(fc);
  const def = (id, params, results, build) => {
    const locals = [];
    const loc = (t = I32) => { const idx = params.length + locals.length; locals.push(t); return idx; };
    const ops = build(loc);
    ops.push(END);
    funcs[id] = { typeIdx: internType(params, results), locals, ops };
  };

  // 1. ensureMem(need)
  def(F.ensureMem, [I32], [], (loc) => {
    const need = 0, curBytes = loc(), needPages = loc(), curPages = loc();
    return [
      MEMSZ, TEE, curPages, I32C, 16, SHL, SET, curBytes,
      GET, need, GET, curBytes, GTU, IF, VOID,
        GET, need, I32C, 65535, ADD, I32C, 16, SHRU,
        GET, curPages, SUB, MEMGR, I32C, -1, EQ, IF, VOID, UNR, END,
      END,
    ];
  });

  // 2. prepareInput(oLen, nLen) -> nBase
  def(F.prepareInput, [I32, I32], [I32], (loc) => {
    const oLen = 0, nLen = 1, nBase = loc(), ab = loc();
    return [
      I32C, 0, GSET, G.oBase, GET, oLen, GSET, G.oLen,
      GET, oLen, I32C, 31, ADD, I32C, -16, AND, TEE, nBase, GSET, G.nBase,
      GET, nLen, GSET, G.nLen,
      GET, nBase, GET, nLen, ADD, I32C, 31, ADD, I32C, -16, AND, TEE, ab, GSET, G.arenaBase,
      GET, ab, I32C, 64, ADD, CALL, F.ensureMem,
      GET, nBase,
    ];
  });

  // 3. prepareBatch(jsonLen) -> 0
  def(F.prepareBatch, [I32], [I32], () => [
    GET, 0, GSET, G.jsonLen, GET, 0, I32C, 256, ADD, CALL, F.ensureMem, I32C, 0,
  ]);

  // 4. countLines(ptr, len) -> i32 (SIMD128)
  def(F.countLines, [I32, I32], [I32], (loc) => {
    const ptr = 0, len = 1, cnt = loc(), end = loc(), end16 = loc(), p = loc(), nl16 = loc(V128);
    return [
      GET, len, EQZ, IF, VOID, I32C, 0, RET, END,
      I32C, 0, SET, cnt, GET, ptr, SET, p,
      GET, ptr, GET, len, ADD, TEE, end, I32C, 16, SUB, SET, end16,
      I32C, 10, VSPLAT8, SET, nl16,
      BLK, VOID, LOOP, VOID,
        GET, p, GET, end16, GTS, BRIF, 1,
        GET, cnt, GET, p, VLD, 0, GET, nl16, VEQ8, VBM8, POP, ADD, SET, cnt,
        GET, p, I32C, 16, ADD, SET, p,
        BR, 0,
      END, END,
      BLK, VOID, LOOP, VOID,
        GET, p, GET, end, GEU, BRIF, 1,
        GET, p, LD8, 0, I32C, 10, EQ, GET, cnt, ADD, SET, cnt,
        GET, p, I32C, 1, ADD, SET, p,
        BR, 0,
      END, END,
      GET, end, I32C, 1, SUB, LD8, 0, I32C, 10, NE, IF, VOID, GET, cnt, I32C, 1, ADD, SET, cnt, END,
      GET, cnt,
    ];
  });

  // 5. trimPrefixSuffix() (SIMD128)
  def(F.trimPrefixSuffix, [], [], (loc) => {
    const oBase = loc(), nBase = loc(), oLen = loc(), nLen = loc(), minL = loc(), p = loc(), min16 = loc();
    const oPtr = loc(), nPtr = loc(), s = loc(), maxS = loc(), maxS16 = loc(), b1 = loc(), b2 = loc(), mask = loc();
    return [
      GGET, G.oBase, SET, oBase, GGET, G.nBase, SET, nBase, GGET, G.oLen, SET, oLen, GGET, G.nLen, SET, nLen,
      GET, oLen, GET, nLen, GET, oLen, GET, nLen, LTU, SEL, SET, minL,
      I32C, 0, SET, p, GET, minL, I32C, 16, SUB, SET, min16,
      BLK, VOID, LOOP, VOID,
        GET, p, GET, min16, GTS, BRIF, 1,
        GET, oBase, GET, p, ADD, VLD, 0, GET, nBase, GET, p, ADD, VLD, 0,
        VEQ8, VBM8, I32C, 0xffff, XOR, TEE, mask, IF, VOID,
          GET, p, GET, mask, CTZ, ADD, SET, p, BR, 2,
        END,
        GET, p, I32C, 16, ADD, SET, p, BR, 0,
      END, END,
      BLK, VOID, LOOP, VOID,
        GET, p, GET, minL, GEU, BRIF, 1,
        GET, oBase, GET, p, ADD, LD8, 0, GET, nBase, GET, p, ADD, LD8, 0, NE, BRIF, 1,
        GET, p, I32C, 1, ADD, SET, p, BR, 0,
      END, END,
      GET, p, GET, oLen, EQ, GET, p, GET, nLen, EQ, AND, IF, VOID,
        GET, oBase, GET, oLen, CALL, F.countLines, GSET, G.prefix,
        I32C, 0, GSET, G.suffix,
        GET, oLen, GSET, G.oStart, GET, nLen, GSET, G.nStart,
        GET, oLen, GSET, G.oEnd, GET, nLen, GSET, G.nEnd, RET,
      END,
      BLK, VOID, LOOP, VOID,
        GET, p, EQZ, BRIF, 1,
        GET, oBase, GET, p, ADD, I32C, 1, SUB, LD8, 0, I32C, 10, EQ, BRIF, 1,
        GET, p, I32C, 1, SUB, SET, p, BR, 0,
      END, END,
      GET, p, GSET, G.oStart, GET, p, GSET, G.nStart,
      GET, oBase, GET, p, CALL, F.countLines, GSET, G.prefix,
      GET, oLen, GET, p, SUB, SET, b1, GET, nLen, GET, p, SUB, SET, b2,
      GET, b1, GET, b2, GET, b1, GET, b2, LTU, SEL, SET, maxS,
      I32C, 0, SET, s, GET, maxS, I32C, 16, SUB, SET, maxS16,
      BLK, VOID, LOOP, VOID,
        GET, s, GET, maxS16, GTS, BRIF, 1,
        GET, oBase, GET, oLen, ADD, GET, s, SUB, I32C, 16, SUB, VLD, 0,
        GET, nBase, GET, nLen, ADD, GET, s, SUB, I32C, 16, SUB, VLD, 0,
        VEQ8, VBM8, I32C, 0xffff, XOR, TEE, mask, IF, VOID,
          GET, s, GET, mask, I32C, 16, SHL, CLZ, ADD, SET, s, BR, 2,
        END,
        GET, s, I32C, 16, ADD, SET, s, BR, 0,
      END, END,
      BLK, VOID, LOOP, VOID,
        GET, s, GET, maxS, GEU, BRIF, 1,
        GET, oBase, GET, oLen, ADD, GET, s, SUB, I32C, 1, SUB, LD8, 0,
        GET, nBase, GET, nLen, ADD, GET, s, SUB, I32C, 1, SUB, LD8, 0, NE, BRIF, 1,
        GET, s, I32C, 1, ADD, SET, s, BR, 0,
      END, END,
      GET, oLen, GET, s, SUB, SET, oPtr, GET, nLen, GET, s, SUB, SET, nPtr,
      GET, s, I32C, 0, GTS, IF, VOID,
        GET, oPtr, GET, p, EQ, IF, I32, I32C, 1, ELSE, GET, oBase, GET, oPtr, ADD, I32C, 1, SUB, LD8, 0, I32C, 10, EQ, END,
        GET, nPtr, GET, p, EQ, IF, I32, I32C, 1, ELSE, GET, nBase, GET, nPtr, ADD, I32C, 1, SUB, LD8, 0, I32C, 10, EQ, END,
        AND, EQZ, IF, VOID,
          BLK, VOID, LOOP, VOID,
            GET, oPtr, GET, oLen, GEU, BRIF, 1,
            GET, oBase, GET, oPtr, ADD, LD8, 0, I32C, 10, EQ, IF, VOID,
              GET, oPtr, I32C, 1, ADD, SET, oPtr, GET, nPtr, I32C, 1, ADD, SET, nPtr, BR, 2,
            END,
            GET, oPtr, I32C, 1, ADD, SET, oPtr, GET, nPtr, I32C, 1, ADD, SET, nPtr, BR, 0,
          END, END,
        END,
      END,
      GET, oPtr, GSET, G.oEnd, GET, nPtr, GSET, G.nEnd,
      GET, oBase, GET, oPtr, ADD, GET, oLen, GET, oPtr, SUB, CALL, F.countLines, GSET, G.suffix,
    ];
  });

  // 6. scanLines() (SIMD128 + packed oBounds/nBounds)
  def(F.scanLines, [], [], (loc) => {
    const n = loc(), m = loc(), minNM = loc(), hCap = loc(), ptr = loc();
    const ops = [
      GGET, G.oBase, GGET, G.oStart, ADD, GGET, G.oEnd, GGET, G.oStart, SUB, CALL, F.countLines, TEE, n, GSET, G.n,
      GGET, G.nBase, GGET, G.nStart, ADD, GGET, G.nEnd, GGET, G.nStart, SUB, CALL, F.countLines, TEE, m, GSET, G.m,
      GET, n, GET, m, GET, n, GET, m, LTU, SEL, SET, minNM,
      GGET, G.arenaBase, SET, ptr,
    ];
    const alloc = (gVar, emitBytes) => {
      ops.push(GET, ptr, GSET, gVar, GET, ptr, ...emitBytes, ADD, I32C, 7, ADD, I32C, -8, AND, SET, ptr);
    };
    alloc(G.oBounds, [GET, n, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.oHash, [GET, n, I32C, 4, ADD, I32C, 3, SHL]);
    alloc(G.nBounds, [GET, m, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.nHash, [GET, m, I32C, 4, ADD, I32C, 3, SHL]);

    const scanSidePlain = (baseG, stG, enG, bG) => {
      const idx = loc(), pos = loc(), end = loc(), base = loc();
      return [
        GGET, baseG, SET, base, GGET, stG, SET, pos, GGET, enG, SET, end, I32C, 0, SET, idx,
        SA32L, bG, idx, pos,
        BLK, VOID, LOOP, VOID,
          GET, pos, GET, end, GEU, BRIF, 1,
          BLK, VOID, LOOP, VOID,
            GET, pos, GET, end, GEU, BRIF, 1,
            GET, base, GET, pos, ADD, LD8, 0, I32C, 10, EQ, IF, VOID, GET, pos, I32C, 1, ADD, SET, pos, BR, 2, END,
            GET, pos, I32C, 1, ADD, SET, pos, BR, 0,
          END, END,
          GET, idx, I32C, 1, ADD, SET, idx,
          SA32L, bG, idx, pos, BR, 0,
        END, END,
      ];
    };

    ops.push(GET, n, EQZ, GET, m, EQZ, OR, IF, VOID);
    alloc(G.changesO, [I32C, 16]); alloc(G.changesP, [I32C, 16]);
    alloc(G.changesD, [I32C, 16]); alloc(G.changesI, [I32C, 16]);
    alloc(G.hStart, [I32C, 16]); alloc(G.hEnd, [I32C, 16]);
    ops.push(
      GET, ptr, GSET, G.arenaPtr, GET, ptr, I32C, 64, ADD, CALL, F.ensureMem,
      GET, n, IF, VOID, ...scanSidePlain(G.oBase, G.oStart, G.oEnd, G.oBounds), END,
      GET, m, IF, VOID, ...scanSidePlain(G.nBase, G.nStart, G.nEnd, G.nBounds), END,
      RET, END,
      I32C, 16, SET, hCap,
      BLK, VOID, LOOP, VOID,
        GET, hCap, GET, n, I32C, 1, SHL, GEU, BRIF, 1,
        GET, hCap, I32C, 1, SHL, SET, hCap, BR, 0,
      END, END,
      GET, hCap, I32C, 1, SUB, GSET, G.hMask,
    );

    alloc(G.buckets, [GET, hCap, I32C, 2, SHL]);
    alloc(G.A, [GET, n, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.B, [GET, m, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.cntA, [GET, n, I32C, 2, SHL]);
    alloc(G.cntB, [GET, n, I32C, 2, SHL]);
    alloc(G.posB, [GET, n, I32C, 2, SHL]);
    alloc(G.seen, [GET, n, I32C, 2, SHL]);
    alloc(G.remDel, [GET, n, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.remIns, [GET, m, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.prefUniqA, [GET, n, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.prefUniqB, [GET, m, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.tailsVal, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.tailsA, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.prevIdx, [GET, n, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.ancA, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.ancB, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.gapD, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.isUniq, [GET, n, I32C, 4, ADD]);
    alloc(G.inLIS, [GET, n, I32C, 4, ADD]);
    alloc(G.usedLIS, [GET, minNM, I32C, 4, ADD]);
    alloc(G.isBridge, [GET, minNM, I32C, 4, ADD]);
    alloc(G.grid64, [I32C, 65 * 65 * 4]);
    alloc(G.segX, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.segY, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.segU, [GET, minNM, I32C, 4, ADD, I32C, 2, SHL]);
    alloc(G.gVp, [I32C, 520 * 4]);
    alloc(G.gVc, [I32C, 520 * 4]);

    ops.push(
      GET, ptr, GSET, G.arenaPtr, GET, ptr, I32C, 64, ADD, CALL, F.ensureMem,
      GGET, G.buckets, I32C, 0, GET, hCap, I32C, 2, SHL, MFILL,
      GGET, G.cntA, I32C, 0, GET, n, I32C, 2, SHL, MFILL,
      GGET, G.cntB, I32C, 0, GET, n, I32C, 2, SHL, MFILL,
      GGET, G.oBase, GGET, G.oStart, GGET, G.oEnd, GGET, G.oBounds, GGET, G.oHash, CALL, F.scanHashSide,
      GGET, G.nBase, GGET, G.nStart, GGET, G.nEnd, GGET, G.nBounds, GGET, G.nHash, CALL, F.scanHashSide,
    );
    return ops;
  });

  // 6b. scanHashSide(base, st, en, bPtr, hPtr)
  def(F.scanHashSide, [I32, I32, I32, I32, I32], [], (loc) => {
    const base = 0, pos = 1, end = 2, bPtr = 3, hPtr = 4;
    const end16 = loc(), end8 = loc(), b = loc(), sh = loc(), mask = loc();
    const w = loc(I64), x = loc(I64), z = loc(I64), h = loc(I64), tailMask = loc(I64), tailW = loc(I64), nl16 = loc(V128);
    return [
      GET, bPtr, GET, pos, ST32, 0,
      GET, end, I32C, 16, SUB, SET, end16, GET, end, I32C, 8, SUB, SET, end8,
      I32C, 10, VSPLAT8, SET, nl16,
      BLK, VOID, LOOP, VOID,
        GET, pos, GET, end, GEU, BRIF, 1,
        I64C, 0x84222325, 0xcbf29ce4, SET, h,
        BLK, VOID,
          BLK, VOID, LOOP, VOID,
            GET, pos, GET, end16, GTS, BRIF, 1,
            GET, base, GET, pos, ADD, VLD, 0, GET, nl16, VEQ8, VBM8, TEE, mask, IF, VOID,
              GET, mask, CTZ, SET, b,
              GET, b, I32C, 8, GES, IF, VOID,
                GET, h, GET, base, GET, pos, ADD, LD64, 0, I64XOR, I64C, 0x1b3, 0x100, I64MUL, SET, h,
                I64C, -1, -1, I32C, 15, GET, b, SUB, I32C, 3, SHL, EXTU, I64SHRU, SET, tailMask,
                GET, h, GET, base, GET, pos, ADD, I32C, 8, ADD, LD64, 0, GET, tailMask, I64AND, I64XOR, I64C, 0x1b3, 0x100, I64MUL, SET, h,
              ELSE,
                I64C, -1, -1, I32C, 7, GET, b, SUB, I32C, 3, SHL, EXTU, I64SHRU, SET, tailMask,
                GET, h, GET, base, GET, pos, ADD, LD64, 0, GET, tailMask, I64AND, I64XOR, I64C, 0x1b3, 0x100, I64MUL, SET, h,
              END,
              GET, pos, GET, b, ADD, I32C, 1, ADD, SET, pos, BR, 3,
            END,
            GET, h, GET, base, GET, pos, ADD, LD64, 0, I64XOR, I64C, 0x1b3, 0x100, I64MUL,
            GET, base, GET, pos, ADD, I32C, 8, ADD, LD64, 0, I64XOR, I64C, 0x1b3, 0x100, I64MUL, SET, h,
            GET, pos, I32C, 16, ADD, SET, pos, BR, 0,
          END, END,
          BLK, VOID, LOOP, VOID,
            GET, pos, GET, end8, GTS, BRIF, 1,
            GET, base, GET, pos, ADD, LD64, 0, TEE, w, I64C, 0x0a0a0a0a, 0x0a0a0a0a, I64XOR, SET, x,
            GET, x, I64C, 0x01010101, 0x01010101, I64SUB, GET, x, I64C, -1, -1, I64XOR, I64AND,
            I64C, 0x80808080, 0x80808080, I64AND, TEE, z, I64EQZ, EQZ, IF, VOID,
              GET, z, I64CTZ, WRAP, I32C, 3, SHRU, SET, b,
              I64C, -1, -1, I32C, 7, GET, b, SUB, I32C, 3, SHL, EXTU, I64SHRU, SET, tailMask,
              GET, h, GET, w, GET, tailMask, I64AND, I64XOR, I64C, 0x1b3, 0x100, I64MUL, SET, h,
              GET, pos, GET, b, ADD, I32C, 1, ADD, SET, pos, BR, 3,
            END,
            GET, h, GET, w, I64XOR, I64C, 0x1b3, 0x100, I64MUL, SET, h,
            GET, pos, I32C, 8, ADD, SET, pos, BR, 0,
          END, END,
          I64C, 0, 0, SET, tailW, I32C, 0, SET, sh,
          BLK, VOID, LOOP, VOID,
            GET, pos, GET, end, GEU, BRIF, 1,
            GET, base, GET, pos, ADD, LD8, 0, SET, b,
            GET, tailW, GET, b, EXTU, GET, sh, EXTU, I64SHL, I64OR, SET, tailW,
            GET, sh, I32C, 8, ADD, SET, sh,
            GET, pos, I32C, 1, ADD, SET, pos,
            GET, b, I32C, 10, EQ, BRIF, 1, BR, 0,
          END, END,
          GET, sh, IF, VOID, GET, h, GET, tailW, I64XOR, I64C, 0x1b3, 0x100, I64MUL, SET, h, END,
        END,
        GET, bPtr, I32C, 4, ADD, TEE, bPtr, GET, pos, ST32, 0,
        GET, hPtr, GET, h, ST64, 0, GET, hPtr, I32C, 8, ADD, SET, hPtr,
        BR, 0,
      END, END,
    ];
  });

  // 7. internLines() (register-cached bases)
  def(F.internLines, [], [], (loc) => {
    const n = loc(), m = loc(), hMask = loc(), oBase = loc(), nBase = loc();
    const oB = loc(), oH = loc(), nB = loc(), nH = loc(), bkts = loc(), aB = loc(), bB = loc(), cAB = loc(), cBB = loc(), pBB = loc();
    const i = loc(), st = loc(), len = loc(), hi = loc(I64), slot = loc(), bk = loc(), rep = loc(), rs = loc(), k = loc(), p1 = loc(), p2 = loc(), found = loc(), ptr = loc();
    const checkEq = (base2L, onMatch) => [
      GET, oBase, GET, rs, ADD, SET, p1, GET, base2L, GET, st, ADD, SET, p2, I32C, 0, SET, k,
      BLK, VOID,
        BLK, VOID, LOOP, VOID,
          GET, k, I32C, 8, ADD, GET, len, GTU, BRIF, 1,
          GET, p1, GET, k, ADD, LD64, 0, GET, p2, GET, k, ADD, LD64, 0, I64NE, BRIF, 2,
          GET, k, I32C, 8, ADD, SET, k, BR, 0,
        END, END,
        BLK, VOID, LOOP, VOID,
          GET, k, GET, len, GEU, BRIF, 1,
          GET, p1, GET, k, ADD, LD8, 0, GET, p2, GET, k, ADD, LD8, 0, NE, BRIF, 2,
          GET, k, I32C, 1, ADD, SET, k, BR, 0,
        END, END,
        ...onMatch,
      END,
    ];
    return [
      GGET, G.n, SET, n, GGET, G.m, SET, m, GGET, G.hMask, SET, hMask, GGET, G.oBase, SET, oBase, GGET, G.nBase, SET, nBase,
      GGET, G.oBounds, SET, oB, GGET, G.oHash, SET, oH, GGET, G.nBounds, SET, nB, GGET, G.nHash, SET, nH,
      GGET, G.buckets, SET, bkts, GGET, G.A, SET, aB, GGET, G.B, SET, bB, GGET, G.cntA, SET, cAB, GGET, G.cntB, SET, cBB, GGET, G.posB, SET, pBB,
      I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, n, GEU, BRIF, 1,
        GET, oB, GET, i, I32C, 2, SHL, ADD, TEE, ptr, LD32, 0, TEE, st, DROP,
        GET, ptr, LD32, 4, GET, st, SUB, SET, len,
        GET, oH, GET, i, I32C, 3, SHL, ADD, LD64, 0, TEE, hi,
        GET, hi, I64C, 32, 0, I64SHRU, I64XOR, WRAP, GET, hMask, AND, SET, slot,
        BLK, VOID, LOOP, VOID,
          LD32_L, bkts, slot, TEE, bk, EQZ, IF, VOID,
            GET, bkts, GET, slot, I32C, 2, SHL, ADD, GET, i, I32C, 1, ADD, ST32, 0,
            ST32_L, aB, i, i, ST32_C, cAB, i, 1, BR, 2,
          END,
          GET, bk, I32C, 1, SUB, SET, rep,
          GET, oH, GET, rep, I32C, 3, SHL, ADD, LD64, 0, GET, hi, I64EQ,
          GET, oB, GET, rep, I32C, 2, SHL, ADD, TEE, ptr, LD32, 4, GET, ptr, LD32, 0, TEE, rs, SUB, GET, len, EQ, AND, IF, VOID,
            ...checkEq(oBase, [
              ST32_L, aB, i, rep,
              GET, cAB, GET, rep, I32C, 2, SHL, ADD, TEE, ptr, GET, ptr, LD32, 0, I32C, 1, ADD, ST32, 0,
              BR, 3,
            ]),
          END,
          GET, slot, I32C, 1, ADD, GET, hMask, AND, SET, slot, BR, 0,
        END, END,
        GET, i, I32C, 1, ADD, SET, i, BR, 0,
      END, END,
      I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, m, GEU, BRIF, 1,
        GET, nB, GET, i, I32C, 2, SHL, ADD, TEE, ptr, LD32, 0, TEE, st, DROP,
        GET, ptr, LD32, 4, GET, st, SUB, SET, len,
        GET, nH, GET, i, I32C, 3, SHL, ADD, LD64, 0, TEE, hi,
        GET, hi, I64C, 32, 0, I64SHRU, I64XOR, WRAP, GET, hMask, AND, SET, slot,
        I32C, -3, SET, found,
        BLK, VOID, LOOP, VOID,
          LD32_L, bkts, slot, TEE, bk, EQZ, BRIF, 1,
          GET, bk, I32C, 1, SUB, SET, rep,
          GET, oH, GET, rep, I32C, 3, SHL, ADD, LD64, 0, GET, hi, I64EQ,
          GET, oB, GET, rep, I32C, 2, SHL, ADD, TEE, ptr, LD32, 4, GET, ptr, LD32, 0, TEE, rs, SUB, GET, len, EQ, AND, IF, VOID,
            ...checkEq(nBase, [
              GET, rep, SET, found,
              GET, cBB, GET, rep, I32C, 2, SHL, ADD, TEE, ptr, GET, ptr, LD32, 0, I32C, 1, ADD, ST32, 0,
              ST32_L, pBB, rep, i, BR, 3,
            ]),
          END,
          GET, slot, I32C, 1, ADD, GET, hMask, AND, SET, slot, BR, 0,
        END, END,
        ST32_L, bB, i, found, GET, i, I32C, 1, ADD, SET, i, BR, 0,
      END, END,
    ];
  });

  // 8. buildBoundsAndUB() -> U (also computes LB, isBridge, and certified splits segX/segY/segU)
  def(F.buildBoundsAndUB, [], [I32], (loc) => {
    const n = loc(), m = loc(), i = loc(), acc = loc(), id = loc(), sc = loc(), kTotal = loc(), tLen = loc();
    const j = loc(), lo = loc(), hi = loc(), mid = loc(), cur = loc(), k = loc(), kHint = loc(), pk = loc(), kr = loc(), kl = loc(), steps = loc();
    const pa = loc(), pb = loc(), minA = loc(), minB = loc(), gx = loc(), gy = loc(), row = loc(), nxt = loc();
    const U = loc(), g = loc(), x0 = loc(), y0 = loc(), gn = loc(), gm = loc(), maxGD = loc(), sA = loc(), sB = loc();
    const d = loc(), idx = loc(), diag = loc(), xr = loc(), xa = loc(), cr = loc(), ca = loc(), nx = loc(), ny = loc(), solved = loc(), tmp = loc();
    const LB = loc(), slack = loc(), maxB = loc(), minB2 = loc(), ex = loc(), ey = loc(), w = loc(), ns = loc(), curU = loc(), lastG = loc(), endG = loc();
    const aB = loc(), bB = loc(), gvP = loc(), gvC = loc(), xaB = loc(), ybB = loc();
    return [
      GGET, G.n, SET, n, GGET, G.m, SET, m,
      GGET, G.A, SET, aB, GGET, G.B, SET, bB, GGET, G.gVp, SET, gvP, GGET, G.gVc, SET, gvC,
      GGET, G.seen, I32C, 0, GET, n, I32C, 2, SHL, MFILL,
      I32C, 0, SET, acc, GET, n, I32C, 1, SUB, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, I32C, 0, LTS, BRIF, 1,
        LA32, G.A, i, SET, id,
        LA32, G.seen, id, I32C, 1, ADD, SET, sc, SA32L, G.seen, id, sc,
        GET, sc, LA32, G.cntB, id, GTS, IF, VOID, GET, acc, I32C, 1, ADD, SET, acc, END,
        SA32L, G.remDel, i, acc, GET, i, I32C, 1, SUB, SET, i, BR, 0,
      END, END,
      SA32C, G.remDel, n, 0,

      GGET, G.seen, I32C, 0, GET, n, I32C, 2, SHL, MFILL,
      I32C, 0, SET, acc, GET, m, I32C, 1, SUB, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, I32C, 0, LTS, BRIF, 1,
        LA32, G.B, i, TEE, id, I32C, -3, EQ, IF, VOID,
          GET, acc, I32C, 1, ADD, SET, acc,
        ELSE,
          LA32, G.seen, id, I32C, 1, ADD, SET, sc, SA32L, G.seen, id, sc,
          GET, sc, LA32, G.cntA, id, GTS, IF, VOID, GET, acc, I32C, 1, ADD, SET, acc, END,
        END,
        SA32L, G.remIns, i, acc, GET, i, I32C, 1, SUB, SET, i, BR, 0,
      END, END,
      SA32C, G.remIns, m, 0,

      // isUniq + kTotal
      I32C, 0, SET, kTotal, I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, n, GEU, BRIF, 1,
        LA32, G.cntA, i, I32C, 1, EQ, LA32, G.cntB, i, I32C, 1, EQ, AND, TEE, tmp,
        GET, kTotal, ADD, SET, kTotal,
        SA8L, G.isUniq, i, tmp,
        GET, i, I32C, 1, ADD, SET, i, BR, 0,
      END, END,

      // prefUniqA & prefUniqB
      GGET, G.prefUniqA, I32C, 0, ST32, 0,
      I32C, 0, SET, acc, I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, n, GEU, BRIF, 1,
        LA32, G.A, i, SET, id, GET, acc, LA8, G.isUniq, id, ADD, SET, acc,
        GET, i, I32C, 1, ADD, TEE, i,
        SA32L, G.prefUniqA, i, acc, BR, 0,
      END, END,
      GGET, G.prefUniqB, I32C, 0, ST32, 0,
      I32C, 0, SET, acc, I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, m, GEU, BRIF, 1,
        LA32, G.B, i, TEE, id, I32C, 0, GES, IF, VOID, GET, acc, LA8, G.isUniq, id, ADD, SET, acc, END,
        GET, i, I32C, 1, ADD, TEE, i,
        SA32L, G.prefUniqB, i, acc, BR, 0,
      END, END,

      // Patience LIS
      I32C, 0, SET, tLen, I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, n, GEU, BRIF, 1,
        LA32, G.A, i, SET, id,
        LA8, G.isUniq, id, IF, VOID,
          LA32, G.posB, id, SET, j, I32C, 0, SET, lo, GET, tLen, SET, hi,
          BLK, VOID, LOOP, VOID,
            GET, lo, GET, hi, GES, BRIF, 1,
            GET, lo, GET, hi, ADD, I32C, 1, SHRU, SET, mid,
            LA32, G.tailsVal, mid, GET, j, LTS, IF, VOID, GET, mid, I32C, 1, ADD, SET, lo, ELSE, GET, mid, SET, hi, END,
            BR, 0,
          END, END,
          SA32L, G.tailsVal, lo, j, SA32L, G.tailsA, lo, i,
          GET, lo, I32C, 0, GTS, IF, I32, GET, lo, I32C, 1, SUB, SET, mid, LA32, G.tailsA, mid, ELSE, I32C, -1, END, SET, tmp,
          SA32L, G.prevIdx, i, tmp,
          GET, lo, GET, tLen, EQ, IF, VOID, GET, tLen, I32C, 1, ADD, SET, tLen, END,
        END,
        GET, i, I32C, 1, ADD, SET, i, BR, 0,
      END, END,

      GGET, G.inLIS, I32C, 0, GET, n, MFILL,
      GET, tLen, I32C, 0, GTS, IF, I32, GET, tLen, I32C, 1, SUB, SET, mid, LA32, G.tailsA, mid, ELSE, I32C, -1, END, SET, cur,
      GET, tLen, SET, k,
      BLK, VOID, LOOP, VOID,
        GET, k, I32C, 1, LTS, BRIF, 1,
        SA32L, G.ancA, k, cur,
        LA32, G.A, cur, SET, id, LA32, G.posB, id, SET, tmp, SA32L, G.ancB, k, tmp,
        SA8C, G.inLIS, cur, 1,
        LA32, G.prevIdx, cur, SET, cur, GET, k, I32C, 1, SUB, SET, k, BR, 0,
      END, END,
      GGET, G.ancA, I32C, -1, ST32, 0, GGET, G.ancB, I32C, -1, ST32, 0,
      GET, tLen, I32C, 1, ADD, SET, mid, SA32L, G.ancA, mid, n, SA32L, G.ancB, mid, m,

      // isBridge[1..tLen]
      GGET, G.isBridge, I32C, 0, GET, tLen, I32C, 2, ADD, MFILL,
      I32C, -1, SET, maxB, I32C, 1, SET, k, I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, n, GEU, BRIF, 1,
        LA32, G.A, i, SET, id,
        LA8, G.isUniq, id, IF, VOID,
          LA32, G.posB, id, SET, pb,
          GET, k, GET, tLen, LES, IF, VOID,
            LA32, G.ancA, k, GET, i, EQ, IF, VOID,
              GET, maxB, LA32, G.ancB, k, LTS, IF, VOID, SA8C, G.isBridge, k, 1, END,
              GET, k, I32C, 1, ADD, SET, k,
            END,
          END,
          GET, pb, GET, maxB, GTS, IF, VOID, GET, pb, SET, maxB, END,
        END,
        GET, i, I32C, 1, ADD, SET, i, BR, 0,
      END, END,
      GET, m, SET, minB2, GET, tLen, SET, k, GET, n, I32C, 1, SUB, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, I32C, 0, LTS, BRIF, 1,
        LA32, G.A, i, SET, id,
        LA8, G.isUniq, id, IF, VOID,
          LA32, G.posB, id, SET, pb,
          GET, k, I32C, 1, GES, IF, VOID,
            LA32, G.ancA, k, GET, i, EQ, IF, VOID,
              GET, minB2, LA32, G.ancB, k, LES, IF, VOID, SA8C, G.isBridge, k, 0, END,
              GET, k, I32C, 1, SUB, SET, k,
            END,
          END,
          GET, pb, GET, minB2, LTS, IF, VOID, GET, pb, SET, minB2, END,
        END,
        GET, i, I32C, 1, SUB, SET, i, BR, 0,
      END, END,

      // grid64 crossing S_uniq pairs
      GGET, G.grid64, I32C, 0, I32C, 65 * 65 * 4, MFILL,
      GGET, G.usedLIS, I32C, 0, GET, tLen, I32C, 2, ADD, MFILL,
      I32C, 1, SET, kHint, I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, n, GEU, BRIF, 1,
        LA32, G.A, i, SET, id,
        LA8, G.isUniq, id, LA8, G.inLIS, i, EQZ, AND, IF, VOID,
          LA32, G.posB, id, SET, j,
          BLK, VOID, LOOP, VOID,
            GET, kHint, GET, tLen, GTS, BRIF, 1,
            LA32, G.ancA, kHint, GET, i, GES, BRIF, 1,
            GET, kHint, I32C, 1, ADD, SET, kHint, BR, 0,
          END, END,
          I32C, -1, SET, pk, GET, kHint, SET, kr, I32C, 0, SET, steps,
          BLK, VOID, LOOP, VOID,
            GET, kr, GET, tLen, GTS, GET, steps, I32C, 64, GES, OR, BRIF, 1,
            LA32, G.ancB, kr, GET, j, GES, BRIF, 1,
            LA8, G.usedLIS, kr, EQZ, IF, VOID, GET, kr, SET, pk, BR, 2, END,
            GET, kr, I32C, 1, ADD, SET, kr, GET, steps, I32C, 1, ADD, SET, steps, BR, 0,
          END, END,
          GET, pk, I32C, -1, EQ, IF, VOID,
            GET, kHint, I32C, 1, SUB, SET, kl, I32C, 0, SET, steps,
            BLK, VOID, LOOP, VOID,
              GET, kl, I32C, 1, LTS, GET, steps, I32C, 64, GES, OR, BRIF, 1,
              LA32, G.ancB, kl, GET, j, LES, BRIF, 1,
              LA8, G.usedLIS, kl, EQZ, IF, VOID, GET, kl, SET, pk, BR, 2, END,
              GET, kl, I32C, 1, SUB, SET, kl, GET, steps, I32C, 1, ADD, SET, steps, BR, 0,
            END, END,
          END,
          GET, pk, I32C, -1, NE, IF, VOID,
            SA8C, G.usedLIS, pk, 1,
            LA32, G.ancA, pk, SET, pa, LA32, G.ancB, pk, SET, pb,
            GET, i, GET, pa, GET, i, GET, pa, LTS, SEL, SET, minA,
            GET, j, GET, pb, GET, j, GET, pb, LTS, SEL, SET, minB,
            GET, minA, I32C, 6, SHL, GET, n, DIVU, SET, gx,
            GET, minB, I32C, 6, SHL, GET, m, DIVU, SET, gy,
            GET, gx, I32C, 65, MUL, GET, gy, ADD, SET, mid,
            LA32, G.grid64, mid, I32C, 1, ADD, SET, tmp, SA32L, G.grid64, mid, tmp,
          END,
        END,
        GET, i, I32C, 1, ADD, SET, i, BR, 0,
      END, END,

      I32C, 63, SET, gx,
      BLK, VOID, LOOP, VOID,
        GET, gx, I32C, 0, LTS, BRIF, 1,
        GET, gx, I32C, 65, MUL, SET, row, GET, row, I32C, 65, ADD, SET, nxt,
        I32C, 63, SET, gy,
        BLK, VOID, LOOP, VOID,
          GET, gy, I32C, 0, LTS, BRIF, 1,
          GET, row, GET, gy, ADD, SET, mid,
          LA32, G.grid64, mid,
          GET, nxt, GET, gy, ADD, SET, cur, LA32, G.grid64, cur, ADD,
          GET, mid, I32C, 1, ADD, SET, cur, LA32, G.grid64, cur, ADD,
          GET, nxt, GET, gy, ADD, I32C, 1, ADD, SET, cur, LA32, G.grid64, cur, SUB, SET, tmp,
          SA32L, G.grid64, mid, tmp,
          GET, gy, I32C, 1, SUB, SET, gy, BR, 0,
        END, END,
        GET, gx, I32C, 1, SUB, SET, gx, BR, 0,
      END, END,

      // Gap Myers for U and gapD[0..tLen] (register-cached bases)
      I32C, 0, SET, U, I32C, 0, SET, g,
      BLK, VOID, LOOP, VOID,
        GET, g, GET, tLen, GTS, BRIF, 1,
        LA32, G.ancA, g, I32C, 1, ADD, SET, x0, LA32, G.ancB, g, I32C, 1, ADD, SET, y0,
        GET, g, I32C, 1, ADD, SET, mid,
        LA32, G.ancA, mid, GET, x0, SUB, SET, gn, LA32, G.ancB, mid, GET, y0, SUB, SET, gm,
        GET, aB, GET, x0, I32C, 2, SHL, ADD, SET, xaB,
        GET, bB, GET, y0, I32C, 2, SHL, ADD, SET, ybB,
        BLK, VOID, LOOP, VOID,
          GET, gn, I32C, 0, LES, GET, gm, I32C, 0, LES, OR, BRIF, 1,
          GET, xaB, LD32, 0, GET, ybB, LD32, 0, NE, BRIF, 1,
          GET, x0, I32C, 1, ADD, SET, x0, GET, y0, I32C, 1, ADD, SET, y0,
          GET, xaB, I32C, 4, ADD, SET, xaB, GET, ybB, I32C, 4, ADD, SET, ybB,
          GET, gn, I32C, 1, SUB, SET, gn, GET, gm, I32C, 1, SUB, SET, gm, BR, 0,
        END, END,
        BLK, VOID, LOOP, VOID,
          GET, gn, I32C, 0, LES, GET, gm, I32C, 0, LES, OR, BRIF, 1,
          GET, gn, I32C, 1, SUB, SET, cur,
          GET, gm, I32C, 1, SUB, SET, mid,
          LD32_L, xaB, cur, LD32_L, ybB, mid, NE, BRIF, 1,
          GET, cur, SET, gn, GET, mid, SET, gm, BR, 0,
        END, END,
        I32C, 0, SET, tmp, // gap result
        BLK, VOID,
          GET, gn, EQZ, IF, VOID, GET, gm, SET, tmp, BR, 1, END,
          GET, gm, EQZ, IF, VOID, GET, gn, SET, tmp, BR, 1, END,
          GET, gn, GET, gm, ADD, SET, mid,
          I32C, 256, GET, mid, I32C, 256, GET, mid, LTS, SEL, SET, maxGD,
          GET, x0, GET, gn, ADD, SET, cur, LD32_L, aB, cur, SET, sA,
          GET, y0, GET, gm, ADD, SET, mid, LD32_L, bB, mid, SET, sB,
          ST32_C, aB, cur, -1, ST32_C, bB, mid, -2,
          I32C, 0, SET, gx,
          BLK, VOID, LOOP, VOID,
            LD32_L, xaB, gx, LD32_L, ybB, gx, NE, BRIF, 1,
            GET, gx, I32C, 1, ADD, SET, gx, BR, 0,
          END, END,
          GET, gvP, GET, gx, ST32, 0,
          I32C, 0, SET, solved, I32C, 1, SET, d,
          BLK, VOID, LOOP, VOID,
            GET, d, GET, maxGD, GTS, BRIF, 1,
            I32C, 0, SET, idx, I32C, 0, GET, d, SUB, SET, diag,
            BLK, VOID, LOOP, VOID,
              GET, idx, GET, d, GTS, BRIF, 1,
              GET, idx, I32C, 0, GTS, IF, I32, GET, idx, I32C, 1, SUB, SET, lo, LD32_L, gvP, lo, ELSE, I32C, -2, END, SET, xr,
              GET, idx, GET, d, LTS, IF, I32, LD32_L, gvP, idx, ELSE, I32C, -2, END, SET, xa,
              GET, xr, I32C, 0, GES, GET, xr, GET, gn, LTS, AND, SET, cr,
              GET, xa, I32C, 0, GES, GET, xa, GET, diag, SUB, I32C, 1, SUB, GET, gm, LTS, AND, SET, ca,
              GET, cr, GET, ca, EQZ, GET, xr, I32C, 1, ADD, GET, xa, GES, OR, AND,
              IF, I32, GET, xr, I32C, 1, ADD, ELSE, GET, ca, IF, I32, GET, xa, ELSE, I32C, -2, END, END, SET, nx,
              GET, nx, I32C, 0, LTS, IF, VOID, ST32_C, gvC, idx, -2,
              ELSE,
                GET, nx, GET, diag, SUB, SET, ny,
                BLK, VOID, LOOP, VOID,
                  LD32_L, xaB, nx, LD32_L, ybB, ny, NE, BRIF, 1,
                  GET, nx, I32C, 1, ADD, SET, nx, GET, ny, I32C, 1, ADD, SET, ny, BR, 0,
                END, END,
                GET, nx, GET, gn, EQ, GET, ny, GET, gm, EQ, AND, IF, VOID,
                  GET, d, SET, tmp, I32C, 1, SET, solved, BR, 5,
                END,
                ST32_L, gvC, idx, nx,
              END,
              GET, idx, I32C, 1, ADD, SET, idx, GET, diag, I32C, 2, ADD, SET, diag, BR, 0,
            END, END,
            GET, gvP, SET, lo, GET, gvC, SET, gvP, GET, lo, SET, gvC,
            GET, d, I32C, 1, ADD, SET, d, BR, 0,
          END, END,
          ST32_L, aB, cur, sA, ST32_L, bB, mid, sB,
          GET, solved, EQZ, IF, VOID, GET, gn, GET, gm, ADD, SET, tmp, END,
        END,
        SA32L, G.gapD, g, tmp,
        GET, U, GET, tmp, ADD, SET, U,
        GET, g, I32C, 1, ADD, SET, g, BR, 0,
      END, END,
      GET, U, GSET, G.U,

      // Certified-Anchor Decomposition: compute LB, slack = U - LB, find certified snake-ends
      GGET, G.remDel, LD32, 0, GGET, G.remIns, LD32, 0, ADD, GET, kTotal, GET, tLen, SUB, I32C, 1, SHL, ADD, SET, LB,
      GET, U, GET, LB, SUB, SET, slack,
      GGET, G.segX, I32C, 0, ST32, 0, GGET, G.segY, I32C, 0, ST32, 0,
      I32C, 0, SET, ns, I32C, 0, SET, cur, I32C, 0, SET, lastG, I32C, 1, SET, k,
      BLK, VOID, LOOP, VOID,
        GET, k, GET, tLen, GTS, BRIF, 1,
        LA32, G.ancA, k, SET, ex, LA32, G.ancB, k, SET, ey,
        GET, ex, GET, cur, LTS, IF, VOID, GET, k, I32C, 1, ADD, SET, k, BR, 1, END,
        // Count isBridge anchors in maximal snake starting at (ex, ey)
        I32C, 0, SET, w, GET, k, SET, endG,
        BLK, VOID, LOOP, VOID,
          GET, ex, GET, n, GES, GET, ey, GET, m, GES, OR, BRIF, 1,
          LA32, G.A, ex, LA32, G.B, ey, NE, BRIF, 1,
          GET, endG, GET, tLen, LES, IF, VOID,
            LA32, G.ancA, endG, GET, ex, EQ, IF, VOID,
              GET, w, LA8, G.isBridge, endG, ADD, SET, w,
              GET, endG, I32C, 1, ADD, SET, endG,
            END,
          END,
          GET, ex, I32C, 1, ADD, SET, ex, GET, ey, I32C, 1, ADD, SET, ey, BR, 0,
        END, END,
        // Note: (ex, ey) is snake-end (A[ex] !== B[ey] or EOF).
        // Certified if (ex < n && ey < m) && ((w << 1) > slack)
        GET, ex, GET, n, LTS, GET, ey, GET, m, LTS, AND,
        GET, w, I32C, 1, SHL, GET, slack, GTS, AND, IF, VOID,
          I32C, 0, SET, curU, GET, lastG, SET, g,
          BLK, VOID, LOOP, VOID,
            GET, g, GET, k, GES, BRIF, 1,
            GET, curU, LA32, G.gapD, g, ADD, SET, curU,
            GET, g, I32C, 1, ADD, SET, g, BR, 0,
          END, END,
          SA32L, G.segU, ns, curU,
          GET, ns, I32C, 1, ADD, SET, ns,
          SA32L, G.segX, ns, ex, SA32L, G.segY, ns, ey,
          GET, ex, SET, cur, GET, endG, I32C, 1, SUB, SET, lastG,
        END,
        GET, endG, SET, k, BR, 0,
      END, END,
      // Final segment to (n, m)
      I32C, 0, SET, curU, GET, lastG, SET, g,
      BLK, VOID, LOOP, VOID,
        GET, g, GET, tLen, GTS, BRIF, 1,
        GET, curU, LA32, G.gapD, g, ADD, SET, curU,
        GET, g, I32C, 1, ADD, SET, g, BR, 0,
      END, END,
      SA32L, G.segU, ns, curU,
      GET, ns, I32C, 1, ADD, TEE, ns, GSET, G.numSegs,
      SA32L, G.segX, ns, n, SA32L, G.segY, ns, m,
      GET, U,
    ];
  });

  // 9. myersSub(x0, y0, x1, y1, uSub, useGlobalPrune): runs forward Myers + backward replay on [x0..x1) x [y0..y1)
  // Appends reverse ops directly to G.revKind / G.revCount (so caller loops seg = numSegs-1 down to 0).
  def(F.myersSub, [I32, I32, I32, I32, I32, I32], [], (loc) => {
    const x0p = 0, y0p = 1, x1p = 2, y1p = 3, uSub = 4, usePrune = 5;
    const n = loc(), m = loc(), delta = loc(), ptr = loc(), sA = loc(), sB = loc();
    const aBase = loc(), bBase = loc(), vpBase = loc(), vcBase = loc();
    const bShift = loc(), bStep = loc(), bMask = loc(), nCkpts = loc();
    const xs = loc(), kLo = loc(), kHi = loc(), hitBound = loc(), d = loc(), remD = loc(), lim1 = loc(), lim2 = loc();
    const loK = loc(), hiK = loc(), iLo = loc(), iHi = loc(), idx = loc(), k = loc(), endIdx = loc();
    const xRem = loc(), xAdd = loc(), nx = loc(), ny = loc(), canRem = loc(), canAdd = loc();
    const qx = loc(), qy = loc(), cc = loc(), pa = loc(), pb = loc(), exIns = loc(), exDel = loc(), tmp = loc();
    const cCount = loc(), metaPtr = loc(), bytesNeed = loc(), ansD = loc(), ansK = loc();
    const stride = loc(), opLen = loc(), curD = loc(), curK = loc(), curX = loc(), bIdx = loc(), d0 = loc(), span = loc();
    const ckData = loc(), ckILo = loc(), fLo0 = loc(), fHi0 = loc(), baseK0 = loc(), rLo0 = loc(), rHi0 = loc();
    const pLo = loc(), pHi = loc(), s = loc(), wLo = loc(), wHi = loc(), rLo = loc(), rHi = loc();
    const prevRow = loc(), curRow = loc(), shiftBase = loc(), cILo = loc(), cIHi = loc(), col = loc();
    const traceX = loc(), traceK = loc(), startX = loc(), opK = loc(), nextK = loc(), prevX = loc(), keep = loc();

    const pushOp = (kindOps, cntOps) => [
      GET, opLen, I32C, 0, GTS, IF, I32, GET, opLen, I32C, 1, SUB, SET, tmp, LA8, G.revKind, tmp, ...kindOps, EQ, ELSE, I32C, 0, END, IF, VOID,
        GET, opLen, I32C, 1, SUB, SET, tmp, LA32, G.revCount, tmp, ...cntOps, ADD, SET, pa, SA32L, G.revCount, tmp, pa,
      ELSE,
        GGET, G.revKind, GET, opLen, ADD, ...kindOps, ST8, 0,
        GGET, G.revCount, GET, opLen, I32C, 2, SHL, ADD, ...cntOps, ST32, 0,
        GET, opLen, I32C, 1, ADD, SET, opLen,
      END,
    ];

    const emitIsValid = (kL) => [
      GET, nx, I32C, 6, SHL, GET, n, ADD, I32C, 1, SUB, GET, n, DIVU, SET, qx,
      GET, ny, I32C, 6, SHL, GET, m, ADD, I32C, 1, SUB, GET, m, DIVU, SET, qy,
      GET, qx, I32C, 65, MUL, GET, qy, ADD, SET, tmp, LA32, G.grid64, tmp, SET, cc,
      LA32, G.prefUniqA, nx, SET, pa, LA32, G.prefUniqB, ny, SET, pb,
      GET, pa, GET, pb, GTS, IF, I32, GET, pa, GET, pb, SUB, ELSE, I32C, 0, END, SET, exIns,
      GET, pb, GET, pa, GTS, IF, I32, GET, pb, GET, pa, SUB, ELSE, I32C, 0, END, SET, exDel,
      LA32, G.remIns, ny, GET, exIns, ADD, GET, cc, ADD, I32C, 1, SHL, GET, lim1, GET, kL, ADD, LES,
      LA32, G.remDel, nx, GET, exDel, ADD, GET, cc, ADD, I32C, 1, SHL, GET, lim2, GET, kL, SUB, LES, AND,
    ];

    return [
      GET, x1p, GET, x0p, SUB, SET, n, GET, y1p, GET, y0p, SUB, SET, m,
      GGET, G.opLen, SET, opLen,
      GET, n, EQZ, GET, m, EQZ, AND, IF, VOID, RET, END,
      GET, n, EQZ, IF, VOID, ...pushOp([I32C, INSERT], [GET, m]), GET, opLen, GSET, G.opLen, RET, END,
      GET, m, EQZ, IF, VOID, ...pushOp([I32C, DELETE], [GET, n]), GET, opLen, GSET, G.opLen, RET, END,

      GET, n, GET, m, SUB, SET, delta,
      GET, uSub, I32C, 8192, LES, IF, VOID, I32C, 5, SET, bShift, I32C, 32, SET, bStep, I32C, 31, SET, bMask,
      ELSE, I32C, 7, SET, bShift, I32C, 128, SET, bStep, I32C, 127, SET, bMask, END,
      GET, bStep, I32C, 4, ADD, SET, stride,

      // Arena from G.arenaPtr (reused across subproblems; revKind/revCount already allocated before solveMyers)
      GGET, G.arenaPtr, SET, ptr,
      GET, ptr, TEE, vpBase, GSET, G.Vp, GET, ptr, GET, uSub, I32C, 8, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, TEE, vcBase, GSET, G.Vc, GET, ptr, GET, uSub, I32C, 8, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.repBuf,
      GET, ptr, GET, bStep, I32C, 1, ADD, GET, bStep, I32C, 4, ADD, MUL, I32C, 2, SHL, ADD, SET, ptr,
      GET, uSub, GET, bShift, SHRU, I32C, 2, ADD, SET, nCkpts,
      GET, ptr, GSET, G.ckptMeta, GET, ptr, GET, nCkpts, I32C, 4, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.ckptData, GET, ptr, GSET, G.ckptDataPtr,
      GET, ptr, I32C, 1048576, ADD, TEE, tmp, GSET, G.ckptCap,
      GET, tmp, CALL, F.ensureMem,

      GGET, G.A, GET, x0p, I32C, 2, SHL, ADD, SET, aBase,
      GGET, G.B, GET, y0p, I32C, 2, SHL, ADD, SET, bBase,
      LA32, G.A, x1p, SET, sA, LA32, G.B, y1p, SET, sB,
      SA32C, G.A, x1p, -1, SA32C, G.B, y1p, -2,

      GET, vpBase, I32C, -2, GET, uSub, I32C, 8, ADD, I32C, 2, SHL, MFILL,
      GET, vcBase, I32C, -2, GET, uSub, I32C, 8, ADD, I32C, 2, SHL, MFILL,

      I32C, 0, SET, xs,
      BLK, VOID, LOOP, VOID,
        LD32_L, aBase, xs, LD32_L, bBase, xs, NE, BRIF, 1,
        GET, xs, I32C, 1, ADD, SET, xs, BR, 0,
      END, END,
      GET, vpBase, GET, xs, ST32, 0,

      GGET, G.ckptMeta, SET, metaPtr,
      GET, metaPtr, I32C, 0, ST32, 0, GET, metaPtr, I32C, 0, ST32, 4, GET, metaPtr, I32C, 0, ST32, 8,
      GET, metaPtr, GGET, G.ckptDataPtr, ST32, 12,
      GGET, G.ckptDataPtr, GET, xs, ST32, 0,
      GGET, G.ckptDataPtr, I32C, 4, ADD, GSET, G.ckptDataPtr,
      I32C, 1, SET, cCount, I32C, 0, SET, ansD, I32C, 0, SET, ansK,
      I32C, 0, SET, kLo, I32C, 0, SET, kHi,
      GET, xs, GET, n, GES, GET, xs, GET, m, GES, OR, SET, hitBound,

      GET, xs, GET, n, LTS, GET, xs, GET, m, LTS, OR, IF, VOID,
        I32C, 1, SET, d,
        BLK, VOID, LOOP, VOID,
          GET, d, GET, uSub, GTS, BRIF, 1,
          GET, uSub, GET, d, SUB, SET, remD,
          GET, remD, GET, delta, SUB, SET, lim1, GET, remD, GET, delta, ADD, SET, lim2,
          GET, kLo, I32C, 1, SUB, SET, nx, I32C, 0, GET, lim1, SUB, SET, ny,
          GET, nx, GET, ny, GET, nx, GET, ny, GTS, SEL, SET, loK,
          GET, kHi, I32C, 1, ADD, SET, nx, GET, lim2, SET, ny,
          GET, nx, GET, ny, GET, nx, GET, ny, LTS, SEL, SET, hiK,
          GET, loK, GET, d, XOR, I32C, 1, AND, IF, VOID, GET, loK, I32C, 1, ADD, SET, loK, END,
          GET, hiK, GET, d, XOR, I32C, 1, AND, IF, VOID, GET, hiK, I32C, 1, SUB, SET, hiK, END,
          GET, loK, GET, d, ADD, I32C, 1, SHRS, SET, iLo, GET, hiK, GET, d, ADD, I32C, 1, SHRS, SET, iHi,
          GET, iLo, I32C, 0, GTS, IF, VOID, GET, iLo, I32C, 1, SUB, SET, tmp, ST32_C, vcBase, tmp, -2, END,
          GET, iHi, I32C, 1, ADD, SET, tmp, ST32_C, vcBase, tmp, -2,

          GET, hitBound, EQZ, IF, VOID,
            GET, iLo, SET, idx, GET, loK, SET, k,
            GET, idx, EQZ, IF, VOID,
              GET, vpBase, LD32, 0, SET, nx,
              GET, nx, I32C, 0, LTS, IF, VOID, GET, vcBase, I32C, -2, ST32, 0,
              ELSE,
                GET, nx, GET, k, SUB, SET, ny,
                BLK, VOID, LOOP, VOID,
                  LD32_L, aBase, nx, LD32_L, bBase, ny, NE, BRIF, 1,
                  GET, nx, I32C, 1, ADD, SET, nx, GET, ny, I32C, 1, ADD, SET, ny, BR, 0,
                END, END,
                GET, nx, GET, n, GES, GET, ny, GET, m, GES, OR, IF, VOID,
                  I32C, 1, SET, hitBound,
                  GET, nx, GET, n, EQ, GET, ny, GET, m, EQ, AND, IF, VOID, GET, d, SET, ansD, GET, k, SET, ansK, BR, 6, END,
                END,
                GET, vcBase, GET, nx, ST32, 0,
              END,
              I32C, 1, SET, idx, GET, k, I32C, 2, ADD, SET, k,
            END,
            GET, iHi, GET, d, GET, iHi, GET, d, LTS, SEL, SET, endIdx,
            GET, endIdx, GET, d, EQ, IF, VOID, GET, d, I32C, 1, SUB, SET, endIdx, END,
            GET, idx, I32C, 1, SUB, SET, tmp, LD32_L, vpBase, tmp, SET, xRem,
            BLK, VOID, LOOP, VOID,
              GET, idx, GET, endIdx, GTS, BRIF, 1,
              LD32_L, vpBase, idx, SET, xAdd,
              GET, xRem, I32C, 0, GES, GET, xRem, I32C, 1, ADD, TEE, tmp, GET, xAdd, GES, AND, IF, I32, GET, tmp, ELSE, GET, xAdd, END, SET, nx,
              GET, nx, I32C, 0, LTS, IF, VOID, ST32_C, vcBase, idx, -2,
              ELSE,
                GET, nx, GET, k, SUB, SET, ny,
                BLK, VOID, LOOP, VOID,
                  LD32_L, aBase, nx, LD32_L, bBase, ny, NE, BRIF, 1,
                  GET, nx, I32C, 1, ADD, SET, nx, GET, ny, I32C, 1, ADD, SET, ny, BR, 0,
                END, END,
                GET, nx, GET, n, GES, GET, ny, GET, m, GES, OR, IF, VOID,
                  I32C, 1, SET, hitBound,
                  GET, nx, GET, n, EQ, GET, ny, GET, m, EQ, AND, IF, VOID, GET, d, SET, ansD, GET, k, SET, ansK, BR, 7, END,
                END,
                ST32_L, vcBase, idx, nx,
              END,
              GET, xAdd, SET, xRem, GET, idx, I32C, 1, ADD, SET, idx, GET, k, I32C, 2, ADD, SET, k, BR, 0,
            END, END,
            GET, iHi, GET, d, EQ, IF, VOID,
              GET, xRem, I32C, 0, LTS, IF, VOID, ST32_C, vcBase, d, -2,
              ELSE,
                GET, xRem, I32C, 1, ADD, SET, nx, GET, nx, GET, d, SUB, SET, ny,
                BLK, VOID, LOOP, VOID,
                  LD32_L, aBase, nx, LD32_L, bBase, ny, NE, BRIF, 1,
                  GET, nx, I32C, 1, ADD, SET, nx, GET, ny, I32C, 1, ADD, SET, ny, BR, 0,
                END, END,
                GET, nx, GET, n, GES, GET, ny, GET, m, GES, OR, IF, VOID,
                  I32C, 1, SET, hitBound,
                  GET, nx, GET, n, EQ, GET, ny, GET, m, EQ, AND, IF, VOID, GET, d, SET, ansD, GET, d, SET, ansK, BR, 6, END,
                END,
                ST32_L, vcBase, d, nx,
              END,
            END,
          ELSE,
            GET, iLo, SET, idx, GET, loK, SET, k,
            BLK, VOID, LOOP, VOID,
              GET, idx, GET, iHi, GTS, BRIF, 1,
              GET, idx, I32C, 0, GTS, IF, I32, GET, idx, I32C, 1, SUB, SET, tmp, LD32_L, vpBase, tmp, ELSE, I32C, -2, END, SET, xRem,
              GET, idx, GET, d, LTS, IF, I32, LD32_L, vpBase, idx, ELSE, I32C, -2, END, SET, xAdd,
              GET, xRem, I32C, 0, GES, GET, xRem, GET, n, LTS, AND, SET, canRem,
              GET, xAdd, I32C, 0, GES, GET, xAdd, GET, k, SUB, I32C, 1, SUB, GET, m, LTS, AND, SET, canAdd,
              GET, canRem, GET, canAdd, EQZ, GET, xRem, I32C, 1, ADD, GET, xAdd, GES, OR, AND,
              IF, I32, GET, xRem, I32C, 1, ADD, ELSE, GET, canAdd, IF, I32, GET, xAdd, ELSE, I32C, -2, END, END, SET, nx,
              GET, nx, I32C, 0, LTS, IF, VOID, ST32_C, vcBase, idx, -2,
              ELSE,
                GET, nx, GET, k, SUB, SET, ny,
                BLK, VOID, LOOP, VOID,
                  LD32_L, aBase, nx, LD32_L, bBase, ny, NE, BRIF, 1,
                  GET, nx, I32C, 1, ADD, SET, nx, GET, ny, I32C, 1, ADD, SET, ny, BR, 0,
                END, END,
                GET, nx, GET, n, EQ, GET, ny, GET, m, EQ, AND, IF, VOID, GET, d, SET, ansD, GET, k, SET, ansK, BR, 6, END,
                ST32_L, vcBase, idx, nx,
              END,
              GET, idx, I32C, 1, ADD, SET, idx, GET, k, I32C, 2, ADD, SET, k, BR, 0,
            END, END,
          END,

          GET, usePrune, IF, VOID,
            BLK, VOID, LOOP, VOID,
              GET, iLo, GET, iHi, GTS, BRIF, 1,
              LD32_L, vcBase, iLo, SET, nx,
              GET, nx, I32C, 0, GES, IF, VOID,
                GET, nx, GET, loK, SUB, SET, ny, ...emitIsValid(loK), BRIF, 2, ST32_C, vcBase, iLo, -2,
              END,
              GET, iLo, I32C, 1, ADD, SET, iLo, GET, loK, I32C, 2, ADD, SET, loK, BR, 0,
            END, END,
            BLK, VOID, LOOP, VOID,
              GET, iLo, GET, iHi, GTS, BRIF, 1,
              LD32_L, vcBase, iHi, SET, nx,
              GET, nx, I32C, 0, GES, IF, VOID,
                GET, nx, GET, hiK, SUB, SET, ny, ...emitIsValid(hiK), BRIF, 2, ST32_C, vcBase, iHi, -2,
              END,
              GET, iHi, I32C, 1, SUB, SET, iHi, GET, hiK, I32C, 2, SUB, SET, hiK, BR, 0,
            END, END,
          ELSE,
            BLK, VOID, LOOP, VOID,
              GET, iLo, GET, iHi, GTS, BRIF, 1, LD32_L, vcBase, iLo, I32C, 0, GES, BRIF, 1,
              GET, iLo, I32C, 1, ADD, SET, iLo, GET, loK, I32C, 2, ADD, SET, loK, BR, 0,
            END, END,
            BLK, VOID, LOOP, VOID,
              GET, iLo, GET, iHi, GTS, BRIF, 1, LD32_L, vcBase, iHi, I32C, 0, GES, BRIF, 1,
              GET, iHi, I32C, 1, SUB, SET, iHi, GET, hiK, I32C, 2, SUB, SET, hiK, BR, 0,
            END, END,
          END,

          GET, loK, SET, kLo, GET, hiK, SET, kHi,
          GET, vpBase, SET, tmp, GET, vcBase, TEE, vpBase, GSET, G.Vp, GET, tmp, TEE, vcBase, GSET, G.Vc,

          GET, d, GET, bMask, AND, EQZ, IF, VOID,
            GET, iHi, GET, iLo, SUB, I32C, 1, ADD, I32C, 2, SHL, SET, bytesNeed,
            GET, bytesNeed, I32C, 0, LTS, IF, VOID, I32C, 0, SET, bytesNeed, END,
            GGET, G.ckptDataPtr, GET, bytesNeed, ADD, GGET, G.ckptCap, GTU, IF, VOID,
              GGET, G.ckptDataPtr, GET, bytesNeed, ADD, I32C, 1048576, ADD, TEE, tmp, GSET, G.ckptCap,
              GET, tmp, CALL, F.ensureMem,
            END,
            GGET, G.ckptMeta, GET, cCount, I32C, 4, SHL, ADD, SET, metaPtr,
            GET, metaPtr, GET, iLo, ST32, 0, GET, metaPtr, GET, loK, ST32, 4, GET, metaPtr, GET, hiK, ST32, 8,
            GET, metaPtr, GGET, G.ckptDataPtr, ST32, 12,
            GET, bytesNeed, I32C, 0, GTS, IF, VOID,
              GGET, G.ckptDataPtr, GET, vpBase, GET, iLo, I32C, 2, SHL, ADD, GET, bytesNeed, MCOPY,
              GGET, G.ckptDataPtr, GET, bytesNeed, ADD, GSET, G.ckptDataPtr,
            END,
            GET, cCount, I32C, 1, ADD, SET, cCount,
          END,
          GET, d, I32C, 1, ADD, SET, d, BR, 0,
        END, END,
      END,

      // Replay subproblem path from ansD, ansK back to (0, 0)
      GET, ansD, SET, curD, GET, ansK, SET, curK, GET, n, SET, curX,
      BLK, VOID, LOOP, VOID,
        GET, curD, I32C, 0, LES, BRIF, 1,
        GET, curD, I32C, 1, SUB, GET, bShift, SHRU, SET, bIdx,
        GET, bIdx, GET, bShift, SHL, SET, d0, GET, curD, GET, d0, SUB, SET, span,
        GGET, G.ckptMeta, GET, bIdx, I32C, 4, SHL, ADD, SET, metaPtr,
        GET, metaPtr, LD32, 0, SET, ckILo, GET, metaPtr, LD32, 4, SET, fLo0, GET, metaPtr, LD32, 8, SET, fHi0, GET, metaPtr, LD32, 12, SET, ckData,
        GET, curK, GET, span, SUB, SET, baseK0,
        GET, fLo0, GET, baseK0, GET, fLo0, GET, baseK0, GTS, SEL, SET, rLo0,
        GET, curK, GET, span, ADD, SET, tmp, GET, fHi0, GET, tmp, GET, fHi0, GET, tmp, LTS, SEL, SET, rHi0,
        GGET, G.repBuf, I32C, -2, GET, span, I32C, 3, ADD, I32C, 2, SHL, MFILL,
        GET, rLo0, SET, k,
        BLK, VOID, LOOP, VOID,
          GET, k, GET, rHi0, GTS, BRIF, 1,
          GET, k, GET, baseK0, SUB, I32C, 1, SHRS, SET, col,
          GET, k, GET, d0, ADD, I32C, 1, SHRS, GET, ckILo, SUB, SET, tmp,
          LD32_L, ckData, tmp, SET, nx, SA32L, G.repBuf, col, nx,
          GET, k, I32C, 2, ADD, SET, k, BR, 0,
        END, END,
        GET, rLo0, SET, pLo, GET, rHi0, SET, pHi, I32C, 1, SET, s,
        BLK, VOID, LOOP, VOID,
          GET, s, GET, span, GTS, BRIF, 1,
          GET, d0, GET, s, ADD, SET, d,
          GET, uSub, GET, d, SUB, SET, remD,
          GET, remD, GET, delta, SUB, SET, lim1, GET, remD, GET, delta, ADD, SET, lim2,
          GET, curK, GET, span, GET, s, SUB, SUB, SET, wLo,
          GET, curK, GET, span, GET, s, SUB, ADD, SET, wHi,
          GET, pLo, I32C, 1, SUB, SET, nx, I32C, 0, GET, lim1, SUB, SET, ny,
          GET, nx, GET, ny, GET, nx, GET, ny, GTS, SEL, SET, rLo,
          GET, wLo, GET, rLo, GET, wLo, GET, rLo, GTS, SEL, SET, rLo,
          GET, pHi, I32C, 1, ADD, SET, nx, GET, lim2, SET, ny,
          GET, nx, GET, ny, GET, nx, GET, ny, LTS, SEL, SET, rHi,
          GET, wHi, GET, rHi, GET, wHi, GET, rHi, LTS, SEL, SET, rHi,
          GET, rLo, GET, d, XOR, I32C, 1, AND, IF, VOID, GET, rLo, I32C, 1, ADD, SET, rLo, END,
          GET, rHi, GET, d, XOR, I32C, 1, AND, IF, VOID, GET, rHi, I32C, 1, SUB, SET, rHi, END,
          GET, s, I32C, 1, SUB, GET, stride, MUL, SET, prevRow,
          GET, s, GET, stride, MUL, SET, curRow,
          GET, baseK0, GET, s, SUB, SET, shiftBase,
          GET, rLo, GET, shiftBase, SUB, I32C, 1, SHRS, SET, cILo,
          GET, rHi, GET, shiftBase, SUB, I32C, 1, SHRS, SET, cIHi,
          GET, cILo, I32C, 0, GTS, IF, VOID, GET, curRow, GET, cILo, ADD, I32C, 1, SUB, SET, tmp, SA32C, G.repBuf, tmp, -2, END,
          GET, curRow, GET, cIHi, ADD, I32C, 1, ADD, SET, tmp, SA32C, G.repBuf, tmp, -2,
          GET, rLo, SET, k,
          BLK, VOID, LOOP, VOID,
            GET, k, GET, rHi, GTS, BRIF, 1,
            GET, k, GET, shiftBase, SUB, I32C, 1, SHRS, SET, col,
            GET, k, I32C, 1, SUB, TEE, tmp, GET, pLo, GES, GET, tmp, GET, pHi, LES, AND,
            IF, I32, GET, prevRow, GET, col, ADD, I32C, 1, SUB, SET, tmp, LA32, G.repBuf, tmp, ELSE, I32C, -2, END, SET, xRem,
            GET, k, I32C, 1, ADD, TEE, tmp, GET, pLo, GES, GET, tmp, GET, pHi, LES, AND,
            IF, I32, GET, prevRow, GET, col, ADD, SET, tmp, LA32, G.repBuf, tmp, ELSE, I32C, -2, END, SET, xAdd,
            GET, xRem, I32C, 0, GES, GET, xRem, GET, n, LTS, AND, SET, canRem,
            GET, xAdd, I32C, 0, GES, GET, xAdd, GET, k, SUB, I32C, 1, SUB, GET, m, LTS, AND, SET, canAdd,
            GET, canRem, GET, canAdd, EQZ, GET, xRem, I32C, 1, ADD, GET, xAdd, GES, OR, AND,
            IF, I32, GET, xRem, I32C, 1, ADD, ELSE, GET, canAdd, IF, I32, GET, xAdd, ELSE, I32C, -2, END, END, SET, nx,
            GET, curRow, GET, col, ADD, SET, tmp,
            GET, nx, I32C, 0, LTS, IF, VOID, SA32C, G.repBuf, tmp, -2,
            ELSE,
              GET, nx, GET, k, SUB, SET, ny,
              BLK, VOID, LOOP, VOID,
                LD32_L, aBase, nx, LD32_L, bBase, ny, NE, BRIF, 1,
                GET, nx, I32C, 1, ADD, SET, nx, GET, ny, I32C, 1, ADD, SET, ny, BR, 0,
              END, END,
              SA32L, G.repBuf, tmp, nx,
            END,
            GET, k, I32C, 2, ADD, SET, k, BR, 0,
          END, END,
          GET, s, GET, span, LTS, GET, usePrune, AND, IF, VOID,
            BLK, VOID, LOOP, VOID,
              GET, cILo, GET, cIHi, GTS, BRIF, 1,
              GET, curRow, GET, cILo, ADD, SET, col, LA32, G.repBuf, col, SET, nx,
              GET, nx, I32C, 0, GES, IF, VOID,
                GET, nx, GET, rLo, SUB, SET, ny, ...emitIsValid(rLo), BRIF, 2, SA32C, G.repBuf, col, -2,
              END,
              GET, cILo, I32C, 1, ADD, SET, cILo, GET, rLo, I32C, 2, ADD, SET, rLo, BR, 0,
            END, END,
            BLK, VOID, LOOP, VOID,
              GET, cILo, GET, cIHi, GTS, BRIF, 1,
              GET, curRow, GET, cIHi, ADD, SET, col, LA32, G.repBuf, col, SET, nx,
              GET, nx, I32C, 0, GES, IF, VOID,
                GET, nx, GET, rHi, SUB, SET, ny, ...emitIsValid(rHi), BRIF, 2, SA32C, G.repBuf, col, -2,
              END,
              GET, cIHi, I32C, 1, SUB, SET, cIHi, GET, rHi, I32C, 2, SUB, SET, rHi, BR, 0,
            END, END,
          END,
          GET, rLo, SET, pLo, GET, rHi, SET, pHi, GET, s, I32C, 1, ADD, SET, s, BR, 0,
        END, END,
        GET, curX, SET, traceX, GET, curK, SET, traceK, GET, span, SET, s,
        BLK, VOID, LOOP, VOID,
          GET, s, I32C, 1, LTS, BRIF, 1,
          GET, s, I32C, 1, SUB, GET, stride, MUL, SET, prevRow,
          GET, baseK0, GET, s, SUB, SET, shiftBase,
          GET, traceK, GET, shiftBase, SUB, I32C, 1, SHRS, SET, col,
          GET, col, I32C, 0, GTS, IF, I32, GET, prevRow, GET, col, ADD, I32C, 1, SUB, SET, tmp, LA32, G.repBuf, tmp, ELSE, I32C, -2, END, SET, xRem,
          GET, prevRow, GET, col, ADD, SET, tmp, LA32, G.repBuf, tmp, SET, xAdd,
          GET, xRem, I32C, 0, GES, GET, xRem, GET, n, LTS, AND, SET, canRem,
          GET, xAdd, I32C, 0, GES, GET, xAdd, GET, traceK, SUB, I32C, 1, SUB, GET, m, LTS, AND, SET, canAdd,
          GET, canRem, GET, canAdd, EQZ, GET, xRem, I32C, 1, ADD, GET, xAdd, GES, OR, AND, IF, VOID,
            GET, xRem, I32C, 1, ADD, SET, startX, I32C, DELETE, SET, opK, GET, traceK, I32C, 1, SUB, SET, nextK, GET, xRem, SET, prevX,
          ELSE,
            GET, xAdd, SET, startX, I32C, INSERT, SET, opK, GET, traceK, I32C, 1, ADD, SET, nextK, GET, xAdd, SET, prevX,
          END,
          GET, traceX, GET, startX, SUB, TEE, keep, I32C, 0, GTS, IF, VOID, ...pushOp([I32C, KEEP], [GET, keep]), END,
          ...pushOp([GET, opK], [I32C, 1]),
          GET, nextK, SET, traceK, GET, prevX, SET, traceX, GET, s, I32C, 1, SUB, SET, s, BR, 0,
        END, END,
        GET, d0, SET, curD, GET, traceK, SET, curK, GET, traceX, SET, curX, BR, 0,
      END, END,
      GET, curX, I32C, 0, GTS, IF, VOID, ...pushOp([I32C, KEEP], [GET, curX]), END,
      GET, opLen, GSET, G.opLen,
      SA32L, G.A, x1p, sA, SA32L, G.B, y1p, sB,
    ];
  });

  // 10. solveMyers() -> loops certified segments backwards, collecting revKind/revCount
  def(F.solveMyers, [], [], (loc) => {
    const ptr = loc(), ns = loc(), seg = loc(), n1 = loc(), x0 = loc(), y0 = loc(), x1 = loc(), y1 = loc(), uSub = loc(), useP = loc();
    return [
      GGET, G.arenaPtr, SET, ptr,
      GET, ptr, GSET, G.revKind,
      GET, ptr, GGET, G.U, I32C, 1, SHL, I32C, 64, ADD, I32C, 7, ADD, I32C, -8, AND, ADD, SET, ptr,
      GET, ptr, GSET, G.revCount,
      GET, ptr, GGET, G.U, I32C, 1, SHL, I32C, 64, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.arenaPtr,
      GET, ptr, I32C, 64, ADD, CALL, F.ensureMem,
      I32C, 0, GSET, G.opLen,
      GGET, G.numSegs, SET, ns,
      GET, ns, I32C, 1, EQ, SET, useP,
      GET, ns, I32C, 1, SUB, SET, seg,
      BLK, VOID, LOOP, VOID,
        GET, seg, I32C, 0, LTS, BRIF, 1,
        GET, seg, I32C, 1, ADD, SET, n1,
        LA32, G.segX, seg, SET, x0, LA32, G.segY, seg, SET, y0,
        LA32, G.segX, n1, SET, x1, LA32, G.segY, n1, SET, y1,
        LA32, G.segU, seg, SET, uSub,
        GET, x0, GET, y0, GET, x1, GET, y1, GET, uSub, GET, useP, CALL, F.myersSub,
        GET, seg, I32C, 1, SUB, SET, seg, BR, 0,
      END, END,
    ];
  });

  // 11. buildChangesAndHunks()
  def(F.buildChangesAndHunks, [], [], (loc) => {
    const opLen = loc(), ptr = loc(), idx = loc(), kind = loc(), cnt = loc(), o = loc(), p = loc(), del = loc(), ins = loc();
    const nc = loc(), last = loc(), nh = loc(), i = loc(), prev = loc(), tmp = loc();
    return [
      GGET, G.opLen, SET, opLen, GGET, G.arenaPtr, SET, ptr,
      GET, ptr, GSET, G.changesO, GET, ptr, GET, opLen, I32C, 4, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.changesP, GET, ptr, GET, opLen, I32C, 4, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.changesD, GET, ptr, GET, opLen, I32C, 4, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.changesI, GET, ptr, GET, opLen, I32C, 4, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.hStart, GET, ptr, GET, opLen, I32C, 4, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.hEnd, GET, ptr, GET, opLen, I32C, 4, ADD, I32C, 2, SHL, ADD, SET, ptr,
      GET, ptr, GSET, G.arenaPtr, GET, ptr, I32C, 64, ADD, CALL, F.ensureMem,
      GGET, G.prefix, TEE, o, SET, p, I32C, 0, SET, del, I32C, 0, SET, ins, I32C, 0, SET, nc,
      GET, opLen, I32C, 1, SUB, SET, idx,
      BLK, VOID, LOOP, VOID,
        GET, idx, I32C, 0, LTS, BRIF, 1,
        LA8, G.revKind, idx, SET, kind, LA32, G.revCount, idx, SET, cnt,
        GET, kind, I32C, KEEP, EQ, IF, VOID,
          GET, o, GET, cnt, ADD, SET, o, GET, p, GET, cnt, ADD, SET, p,
        ELSE,
          GET, nc, I32C, 1, SUB, SET, last,
          GET, last, I32C, 0, LTS, IF, I32, I32C, 1,
          ELSE, LA32, G.changesO, last, LA32, G.changesD, last, ADD, GET, o, NE,
                LA32, G.changesP, last, LA32, G.changesI, last, ADD, GET, p, NE, OR, END,
          IF, VOID,
            SA32L, G.changesO, nc, o, SA32L, G.changesP, nc, p, SA32C, G.changesD, nc, 0, SA32C, G.changesI, nc, 0,
            GET, nc, SET, last, GET, nc, I32C, 1, ADD, SET, nc,
          END,
          GET, kind, I32C, DELETE, EQ, IF, VOID,
            LA32, G.changesD, last, GET, cnt, ADD, SET, tmp, SA32L, G.changesD, last, tmp,
            GET, o, GET, cnt, ADD, SET, o, GET, del, GET, cnt, ADD, SET, del,
          ELSE,
            LA32, G.changesI, last, GET, cnt, ADD, SET, tmp, SA32L, G.changesI, last, tmp,
            GET, p, GET, cnt, ADD, SET, p, GET, ins, GET, cnt, ADD, SET, ins,
          END,
        END,
        GET, idx, I32C, 1, SUB, SET, idx, BR, 0,
      END, END,
      GET, nc, GSET, G.numChanges, GET, del, GSET, G.deleted, GET, ins, GSET, G.inserted,
      I32C, 0, SET, nh, I32C, 0, SET, i,
      BLK, VOID, LOOP, VOID,
        GET, i, GET, nc, GES, BRIF, 1,
        GET, nh, I32C, 0, GTS, IF, VOID,
          GET, nh, I32C, 1, SUB, SET, tmp, LA32, G.hEnd, tmp, SET, prev,
          LA32, G.changesO, i, LA32, G.changesO, prev, LA32, G.changesD, prev, ADD, SUB, I32C, 6, LES, IF, VOID,
            SA32L, G.hEnd, tmp, i, GET, i, I32C, 1, ADD, SET, i, BR, 2,
          END,
        END,
        SA32L, G.hStart, nh, i, SA32L, G.hEnd, nh, i,
        GET, nh, I32C, 1, ADD, SET, nh, GET, i, I32C, 1, ADD, SET, i, BR, 0,
      END, END,
      GET, nh, GSET, G.numHunks,
    ];
  });

  // 12. writeDec(ptr, val) -> newPtr
  def(F.writeDec, [I32, I32], [I32], (loc) => {
    const ptr = 0, val = 1, start = loc(), lo = loc(), hi = loc(), t = loc();
    return [
      GET, val, EQZ, IF, VOID, GET, ptr, I32C, 48, ST8, 0, GET, ptr, I32C, 1, ADD, RET, END,
      GET, ptr, SET, start,
      BLK, VOID, LOOP, VOID,
        GET, val, EQZ, BRIF, 1,
        GET, ptr, GET, val, I32C, 10, REMU, I32C, 48, ADD, ST8, 0,
        GET, ptr, I32C, 1, ADD, SET, ptr, GET, val, I32C, 10, DIVU, SET, val, BR, 0,
      END, END,
      GET, start, SET, lo, GET, ptr, I32C, 1, SUB, SET, hi,
      BLK, VOID, LOOP, VOID,
        GET, lo, GET, hi, GEU, BRIF, 1,
        GET, lo, LD8, 0, SET, t, GET, lo, GET, hi, LD8, 0, ST8, 0, GET, hi, GET, t, ST8, 0,
        GET, lo, I32C, 1, ADD, SET, lo, GET, hi, I32C, 1, SUB, SET, hi, BR, 0,
      END, END,
      GET, ptr,
    ];
  });

  // 13. pushLineOut(out, base, s, e, opB) -> newOut
  def(F.pushLineOut, [I32, I32, I32, I32, I32], [I32], (loc) => {
    const out = 0, base = 1, s = 2, e = 3, opB = 4, len = loc();
    return [
      GET, out, GET, opB, ST8, 0, GET, out, I32C, 1, ADD, SET, out,
      GET, e, GET, s, SUB, SET, len,
      GET, out, GET, base, GET, s, ADD, GET, len, MCOPY,
      GET, out, GET, len, ADD, SET, out,
      GET, base, GET, e, ADD, I32C, 1, SUB, LD8, 0, I32C, 10, NE, IF, VOID,
        GET, out, I32C, 10, ST8, 0, GET, out, I32C, 37, ST8, 1, GET, out, I32C, 10, ST8, 2,
        GET, out, I32C, 3, ADD, SET, out,
      END,
      GET, out,
    ];
  });

  // 14. buildPatch()
  def(F.buildPatch, [], [], (loc) => {
    const outBase = loc(), ptr = loc(), totalOld = loc(), totalNew = loc(), prefix = loc(), suffix = loc(), n = loc(), m = loc(), nh = loc();
    const oBase = loc(), nBase = loc(), oStart = loc(), oEnd = loc(), oLen = loc(), preNeed = loc(), sufNeed = loc(), preArr = loc(), sufArr = loc();
    const curPos = loc(), i = loc(), hi = loc(), fi = loc(), li = loc(), firstO = loc(), firstP = loc(), lastO = loc(), lastP = loc(), lastD = loc(), lastI = loc();
    const oldStart = loc(), newStart = loc(), remAfter = loc(), after = loc(), oldEnd = loc(), newEnd = loc();
    const at = loc(), ci = loc(), co = loc(), cp = loc(), cd = loc(), cins = loc(), mi = loc(), maxBytes = loc(), oB = loc(), nB = loc(), bp = loc();

    const emitStr = (str) => {
      const a = [];
      for (let k = 0; k < str.length; k++) a.push(GET, ptr, I32C, str.charCodeAt(k), ST8, k);
      a.push(GET, ptr, I32C, str.length, ADD, SET, ptr);
      return a;
    };
    const emitPushOld = (giL, opByte) => {
      const s = loc(), e = loc(), off = loc();
      return [
        GET, giL, GET, prefix, GES, GET, giL, GET, prefix, GET, n, ADD, LTS, AND, IF, VOID,
          GET, giL, GET, prefix, SUB, SET, off,
          GET, oB, GET, off, I32C, 2, SHL, ADD, TEE, bp, LD32, 0, SET, s, GET, bp, LD32, 4, SET, e,
        ELSE, GET, giL, GET, prefix, LTS, IF, VOID,
          GET, giL, GET, prefix, GET, preNeed, SUB, SUB, SET, off,
          GET, preArr, GET, off, I32C, 2, SHL, ADD, TEE, off, LD32, 0, SET, s, GET, off, LD32, 4, SET, e,
        ELSE,
          GET, giL, GET, prefix, GET, n, ADD, SUB, SET, off,
          GET, sufArr, GET, off, I32C, 2, SHL, ADD, TEE, off, LD32, 0, SET, s, GET, off, LD32, 4, SET, e,
        END, END,
        GET, ptr, GET, oBase, GET, s, GET, e, I32C, opByte, CALL, F.pushLineOut, SET, ptr,
      ];
    };

    return [
      GGET, G.prefix, SET, prefix, GGET, G.suffix, SET, suffix, GGET, G.n, SET, n, GGET, G.m, SET, m, GGET, G.numHunks, SET, nh,
      GET, prefix, GET, n, ADD, GET, suffix, ADD, SET, totalOld,
      GET, prefix, GET, m, ADD, GET, suffix, ADD, SET, totalNew,
      GGET, G.oBase, SET, oBase, GGET, G.nBase, SET, nBase, GGET, G.oStart, SET, oStart, GGET, G.oEnd, SET, oEnd, GGET, G.oLen, SET, oLen,
      GGET, G.oBounds, SET, oB, GGET, G.nBounds, SET, nB,
      GGET, G.arenaPtr, SET, ptr,
      GET, ptr, SET, preArr, GET, ptr, I32C, 16, ADD, SET, ptr,
      GET, ptr, SET, sufArr, GET, ptr, I32C, 16, ADD, SET, ptr,
      GET, ptr, TEE, outBase, GSET, G.outBase,
      GET, oLen, GGET, G.nLen, ADD, GET, totalOld, GET, totalNew, ADD, I32C, 2, SHL, ADD, GET, nh, I32C, 6, SHL, ADD, I32C, 512, ADD, SET, maxBytes,
      GET, outBase, GET, maxBytes, ADD, CALL, F.ensureMem,
      GET, outBase, SET, ptr,
      ...emitStr('makefun-diff/1 old='), GET, ptr, GET, totalOld, CALL, F.writeDec, SET, ptr,
      ...emitStr(' new='), GET, ptr, GET, totalNew, CALL, F.writeDec, SET, ptr,
      ...emitStr(' hunks='), GET, ptr, GET, nh, CALL, F.writeDec, SET, ptr,
      ...emitStr(' deleted='), GET, ptr, GGET, G.deleted, CALL, F.writeDec, SET, ptr,
      ...emitStr(' inserted='), GET, ptr, GGET, G.inserted, CALL, F.writeDec, SET, ptr,
      GET, ptr, I32C, 10, ST8, 0, GET, ptr, I32C, 1, ADD, SET, ptr,
      GET, nh, EQZ, IF, VOID, GET, ptr, GSET, G.outEnd, RET, END,
      I32C, 0, SET, preNeed,
      GGET, G.changesO, LD32, 0, GET, prefix, I32C, 3, ADD, LTS, GET, prefix, I32C, 0, GTS, AND, IF, VOID,
        GET, prefix, I32C, 3, GET, prefix, I32C, 3, LTS, SEL, SET, preNeed,
        GET, oStart, SET, curPos,
        GET, preArr, GET, preNeed, I32C, 2, SHL, ADD, GET, curPos, ST32, 0,
        GET, preNeed, I32C, 1, SUB, SET, i,
        BLK, VOID, LOOP, VOID,
          GET, i, I32C, 0, LTS, BRIF, 1,
          GET, curPos, GET, oBase, GET, curPos, ADD, I32C, 1, SUB, LD8, 0, I32C, 10, EQ, IF, I32, I32C, 2, ELSE, I32C, 1, END, SUB, SET, curPos,
          BLK, VOID, LOOP, VOID,
            GET, curPos, I32C, 0, LTS, BRIF, 1,
            GET, oBase, GET, curPos, ADD, LD8, 0, I32C, 10, EQ, BRIF, 1,
            GET, curPos, I32C, 1, SUB, SET, curPos, BR, 0,
          END, END,
          GET, curPos, I32C, 1, ADD, SET, curPos,
          GET, preArr, GET, i, I32C, 2, SHL, ADD, GET, curPos, ST32, 0,
          GET, i, I32C, 1, SUB, SET, i, BR, 0,
        END, END,
      END,
      I32C, 0, SET, sufNeed,
      GET, suffix, I32C, 0, GTS, IF, VOID,
        GGET, G.hEnd, GET, nh, I32C, 1, SUB, I32C, 2, SHL, ADD, LD32, 0, SET, li,
        LA32, G.changesO, li, LA32, G.changesD, li, ADD, I32C, 3, ADD, GET, prefix, GET, n, ADD, GTS, IF, VOID,
          GET, suffix, I32C, 3, GET, suffix, I32C, 3, LTS, SEL, SET, sufNeed,
          GET, oEnd, SET, curPos, GET, sufArr, GET, curPos, ST32, 0, I32C, 1, SET, i,
          BLK, VOID, LOOP, VOID,
            GET, i, GET, sufNeed, GTS, BRIF, 1,
            BLK, VOID, LOOP, VOID,
              GET, curPos, GET, oLen, GEU, BRIF, 1,
              GET, oBase, GET, curPos, ADD, LD8, 0, I32C, 10, EQ, IF, VOID, GET, curPos, I32C, 1, ADD, SET, curPos, BR, 2, END,
              GET, curPos, I32C, 1, ADD, SET, curPos, BR, 0,
            END, END,
            GET, sufArr, GET, i, I32C, 2, SHL, ADD, GET, curPos, ST32, 0,
            GET, i, I32C, 1, ADD, SET, i, BR, 0,
          END, END,
        END,
      END,
      I32C, 0, SET, hi,
      BLK, VOID, LOOP, VOID,
        GET, hi, GET, nh, GES, BRIF, 1,
        LA32, G.hStart, hi, SET, fi, LA32, G.hEnd, hi, SET, li,
        LA32, G.changesO, fi, SET, firstO, LA32, G.changesP, fi, SET, firstP,
        LA32, G.changesO, li, SET, lastO, LA32, G.changesP, li, SET, lastP,
        LA32, G.changesD, li, SET, lastD, LA32, G.changesI, li, SET, lastI,
        GET, firstO, I32C, 3, GTS, IF, I32, GET, firstO, I32C, 3, SUB, ELSE, I32C, 0, END, SET, oldStart,
        GET, firstP, GET, firstO, GET, oldStart, SUB, SUB, SET, newStart,
        GET, totalOld, GET, lastO, GET, lastD, ADD, SUB, SET, remAfter,
        GET, remAfter, I32C, 3, GET, remAfter, I32C, 3, LTS, SEL, SET, after,
        GET, lastO, GET, lastD, ADD, GET, after, ADD, SET, oldEnd,
        GET, lastP, GET, lastI, ADD, GET, after, ADD, SET, newEnd,
        ...emitStr('@ '), GET, ptr, GET, oldStart, I32C, 1, ADD, CALL, F.writeDec, SET, ptr,
        GET, ptr, I32C, 32, ST8, 0, GET, ptr, I32C, 1, ADD, SET, ptr,
        GET, ptr, GET, oldEnd, GET, oldStart, SUB, CALL, F.writeDec, SET, ptr,
        GET, ptr, I32C, 32, ST8, 0, GET, ptr, I32C, 1, ADD, SET, ptr,
        GET, ptr, GET, newStart, I32C, 1, ADD, CALL, F.writeDec, SET, ptr,
        GET, ptr, I32C, 32, ST8, 0, GET, ptr, I32C, 1, ADD, SET, ptr,
        GET, ptr, GET, newEnd, GET, newStart, SUB, CALL, F.writeDec, SET, ptr,
        GET, ptr, I32C, 10, ST8, 0, GET, ptr, I32C, 1, ADD, SET, ptr,
        GET, oldStart, SET, at, GET, fi, SET, ci,
        BLK, VOID, LOOP, VOID,
          GET, ci, GET, li, GTS, BRIF, 1,
          LA32, G.changesO, ci, SET, co, LA32, G.changesP, ci, SET, cp,
          LA32, G.changesD, ci, SET, cd, LA32, G.changesI, ci, SET, cins,
          BLK, VOID, LOOP, VOID,
            GET, at, GET, co, GES, BRIF, 1, ...emitPushOld(at, 61), GET, at, I32C, 1, ADD, SET, at, BR, 0,
          END, END,
          I32C, 0, SET, i,
          BLK, VOID, LOOP, VOID,
            GET, i, GET, cd, GES, BRIF, 1, GET, co, GET, i, ADD, SET, at, ...emitPushOld(at, 45), GET, i, I32C, 1, ADD, SET, i, BR, 0,
          END, END,
          I32C, 0, SET, i,
          BLK, VOID, LOOP, VOID,
            GET, i, GET, cins, GES, BRIF, 1,
            GET, cp, GET, i, ADD, GET, prefix, SUB, SET, mi,
            GET, ptr, GET, nBase, GET, nB, GET, mi, I32C, 2, SHL, ADD, TEE, bp, LD32, 0, GET, bp, LD32, 4, I32C, 43, CALL, F.pushLineOut, SET, ptr,
            GET, i, I32C, 1, ADD, SET, i, BR, 0,
          END, END,
          GET, co, GET, cd, ADD, SET, at, GET, ci, I32C, 1, ADD, SET, ci, BR, 0,
        END, END,
        BLK, VOID, LOOP, VOID,
          GET, at, GET, oldEnd, GES, BRIF, 1, ...emitPushOld(at, 61), GET, at, I32C, 1, ADD, SET, at, BR, 0,
        END, END,
        GET, hi, I32C, 1, ADD, SET, hi, BR, 0,
      END, END,
      GET, ptr, GSET, G.outEnd,
    ];
  });

  // 15. solveAscii() -> outLen
  def(F.solveAscii, [], [I32], () => [
    CALL, F.trimPrefixSuffix,
    GGET, G.oStart, GGET, G.oEnd, EQ, GGET, G.nStart, GGET, G.nEnd, EQ, AND, IF, VOID,
      I32C, 0, GSET, G.n, I32C, 0, GSET, G.m, I32C, 0, GSET, G.numHunks, I32C, 0, GSET, G.deleted, I32C, 0, GSET, G.inserted,
      GGET, G.arenaBase, GSET, G.arenaPtr, CALL, F.buildPatch, GGET, G.outEnd, GGET, G.outBase, SUB, RET,
    END,
    CALL, F.scanLines,
    GGET, G.n, EQZ, GGET, G.m, EQZ, OR, IF, VOID,
      GGET, G.changesO, GGET, G.prefix, ST32, 0, GGET, G.changesP, GGET, G.prefix, ST32, 0,
      GGET, G.changesD, GGET, G.n, ST32, 0, GGET, G.changesI, GGET, G.m, ST32, 0,
      GGET, G.hStart, I32C, 0, ST32, 0, GGET, G.hEnd, I32C, 0, ST32, 0,
      I32C, 1, GSET, G.numChanges, I32C, 1, GSET, G.numHunks,
      GGET, G.n, GSET, G.deleted, GGET, G.m, GSET, G.inserted,
      CALL, F.buildPatch, GGET, G.outEnd, GGET, G.outBase, SUB, RET,
    END,
    CALL, F.internLines,
    CALL, F.buildBoundsAndUB, DROP,
    CALL, F.solveMyers,
    CALL, F.buildChangesAndHunks,
    CALL, F.buildPatch,
    GGET, G.outEnd, GGET, G.outBase, SUB,
  ]);

  def(F.getOutBase, [], [I32], () => [GGET, G.outBase]);
  def(F.getBatchOutBase, [], [I32], () => [GGET, G.batchOutBase]);

  // 16. skipWs(pos, end) -> pos
  def(F.skipWs, [I32, I32], [I32], (loc) => {
    const pos = 0, end = 1, b = loc();
    return [
      BLK, VOID, LOOP, VOID,
        GET, pos, GET, end, GEU, BRIF, 1,
        GET, pos, LD8, 0, TEE, b,
        I32C, 32, EQ, GET, b, I32C, 9, EQ, OR, GET, b, I32C, 10, EQ, OR, GET, b, I32C, 13, EQ, OR, EQZ, BRIF, 1,
        GET, pos, I32C, 1, ADD, SET, pos, BR, 0,
      END, END,
      GET, pos,
    ];
  });

  // 17. skipJsonStr(pos, end) -> newPos or -1
  def(F.skipJsonStr, [I32, I32], [I32], (loc) => {
    const pos = 0, end = 1, b = loc();
    return [
      GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
      GET, pos, LD8, 0, I32C, 34, NE, IF, VOID, I32C, -1, RET, END,
      GET, pos, I32C, 1, ADD, SET, pos,
      BLK, VOID, LOOP, VOID,
        GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
        GET, pos, LD8, 0, SET, b,
        GET, b, I32C, 34, EQ, IF, VOID, GET, pos, I32C, 1, ADD, RET, END,
        GET, b, I32C, 92, EQ, IF, VOID,
          GET, pos, I32C, 1, ADD, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
          GET, pos, I32C, 2, ADD, SET, pos, BR, 1,
        END,
        GET, b, I32C, 32, LTU, GET, b, I32C, 127, GTU, OR, IF, VOID, I32C, -1, RET, END,
        GET, pos, I32C, 1, ADD, SET, pos, BR, 0,
      END, END,
      I32C, -1,
    ];
  });

  // 18. unescapeJsonStr(src, end, dstBase) -> len or -1 (SIMD128, \n & \r checked first!)
  def(F.unescapeJsonStr, [I32, I32, I32], [I32], (loc) => {
    const src = 0, end = 1, dstBase = 2;
    const dst = loc(), end16 = loc(), mask = loc(), k = loc(), b = loc(), esc = loc(), h1 = loc(), h2 = loc();
    const q16 = loc(V128), bs16 = loc(V128), sp16 = loc(V128), v = loc(V128);
    const emitHex = (chL, outL) => [
      GET, chL, I32C, 48, SUB, TEE, outL, I32C, 9, LEU, IF, VOID,
      ELSE, GET, chL, I32C, 32, OR, I32C, 87, SUB, TEE, outL, I32C, 10, LTU, GET, outL, I32C, 15, GTU, OR, IF, VOID, I32C, -1, RET, END, END,
    ];
    const emitHandleEsc = () => [
      GET, src, I32C, 1, ADD, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
      GET, src, I32C, 1, ADD, LD8, 0, SET, esc,
      GET, esc, I32C, 110, EQ, IF, VOID, GET, dst, I32C, 10, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 114, EQ, IF, VOID, GET, dst, I32C, 13, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 34, EQ, IF, VOID, GET, dst, I32C, 34, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 92, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 116, EQ, IF, VOID, GET, dst, I32C, 9, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 98, EQ, IF, VOID, GET, dst, I32C, 8, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 102, EQ, IF, VOID, GET, dst, I32C, 12, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 47, EQ, IF, VOID, GET, dst, I32C, 47, ST8, 0, GET, src, I32C, 2, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, GET, esc, I32C, 117, EQ, IF, VOID,
        GET, src, I32C, 5, ADD, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
        GET, src, LD8, 2, I32C, 48, NE, GET, src, LD8, 3, I32C, 48, NE, OR, IF, VOID, I32C, -1, RET, END,
        GET, src, LD8, 4, SET, b, ...emitHex(b, h1),
        GET, h1, I32C, 7, GTU, IF, VOID, I32C, -1, RET, END,
        GET, src, LD8, 5, SET, b, ...emitHex(b, h2),
        GET, dst, GET, h1, I32C, 4, SHL, GET, h2, OR, ST8, 0,
        GET, src, I32C, 6, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst,
      ELSE, I32C, -1, RET, END, END, END, END, END, END, END, END, END,
    ];
    return [
      GET, src, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
      GET, src, LD8, 0, I32C, 34, NE, IF, VOID, I32C, -1, RET, END,
      GET, src, I32C, 1, ADD, SET, src, GET, dstBase, SET, dst, GET, end, I32C, 16, SUB, SET, end16,
      I32C, 34, VSPLAT8, SET, q16, I32C, 92, VSPLAT8, SET, bs16, I32C, 32, VSPLAT8, SET, sp16,
      BLK, VOID, LOOP, VOID,
        GET, src, GET, end16, GTS, BRIF, 1,
        GET, src, VLD, 0, TEE, v,
        GET, v, GET, q16, VEQ8, GET, v, GET, bs16, VEQ8, VOR, GET, v, GET, sp16, VLTS8, VOR,
        VBM8, TEE, mask, EQZ, IF, VOID,
          GET, dst, GET, v, VST, 0,
          GET, src, I32C, 16, ADD, SET, src, GET, dst, I32C, 16, ADD, SET, dst, BR, 1,
        END,
        GET, mask, CTZ, TEE, k, IF, VOID,
          GET, dst, GET, v, VST, 0,
          GET, src, GET, k, ADD, SET, src, GET, dst, GET, k, ADD, SET, dst,
        END,
        GET, src, LD8, 0, SET, b,
        GET, b, I32C, 34, EQ, IF, VOID, GET, src, I32C, 1, ADD, GSET, G.jsonCur, GET, dst, GET, dstBase, SUB, RET, END,
        GET, b, I32C, 92, NE, IF, VOID, I32C, -1, RET, END,
        ...emitHandleEsc(), BR, 0,
      END, END,
      BLK, VOID, LOOP, VOID,
        GET, src, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
        GET, src, LD8, 0, SET, b,
        GET, b, I32C, 34, EQ, IF, VOID, GET, src, I32C, 1, ADD, GSET, G.jsonCur, GET, dst, GET, dstBase, SUB, RET, END,
        GET, b, I32C, 92, EQ, IF, VOID, ...emitHandleEsc(), BR, 1, END,
        GET, b, I32C, 32, LTU, GET, b, I32C, 127, GTU, OR, IF, VOID, I32C, -1, RET, END,
        GET, dst, GET, b, ST8, 0, GET, src, I32C, 1, ADD, SET, src, GET, dst, I32C, 1, ADD, SET, dst, BR, 0,
      END, END,
      I32C, -1,
    ];
  });

  // 19. escapeJsonOut(src, len, dst) -> newDst (SIMD128)
  def(F.escapeJsonOut, [I32, I32, I32], [I32], (loc) => {
    const src = 0, len = 1, dst = 2, end = loc(), end16 = loc(), mask = loc(), k = loc(), b = loc(), h1 = loc(), h2 = loc();
    const q16 = loc(V128), bs16 = loc(V128), sp16 = loc(V128), v = loc(V128);
    const emitEsc = () => [
      GET, b, I32C, 10, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 110, ST8, 1, GET, dst, I32C, 2, ADD, SET, dst,
      ELSE, GET, b, I32C, 34, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 34, ST8, 1, GET, dst, I32C, 2, ADD, SET, dst,
      ELSE, GET, b, I32C, 92, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 92, ST8, 1, GET, dst, I32C, 2, ADD, SET, dst,
      ELSE, GET, b, I32C, 13, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 114, ST8, 1, GET, dst, I32C, 2, ADD, SET, dst,
      ELSE, GET, b, I32C, 9, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 116, ST8, 1, GET, dst, I32C, 2, ADD, SET, dst,
      ELSE, GET, b, I32C, 8, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 98, ST8, 1, GET, dst, I32C, 2, ADD, SET, dst,
      ELSE, GET, b, I32C, 12, EQ, IF, VOID, GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 102, ST8, 1, GET, dst, I32C, 2, ADD, SET, dst,
      ELSE,
        GET, dst, I32C, 92, ST8, 0, GET, dst, I32C, 117, ST8, 1, GET, dst, I32C, 48, ST8, 2, GET, dst, I32C, 48, ST8, 3,
        GET, b, I32C, 4, SHRU, I32C, 48, ADD, SET, h1,
        GET, b, I32C, 15, AND, TEE, h2, I32C, 10, LTU, IF, I32, GET, h2, I32C, 48, ADD, ELSE, GET, h2, I32C, 87, ADD, END, SET, h2,
        GET, dst, GET, h1, ST8, 4, GET, dst, GET, h2, ST8, 5, GET, dst, I32C, 6, ADD, SET, dst,
      END, END, END, END, END, END, END,
    ];
    return [
      GET, dst, I32C, 34, ST8, 0, GET, dst, I32C, 1, ADD, SET, dst,
      GET, src, GET, len, ADD, TEE, end, I32C, 16, SUB, SET, end16,
      I32C, 34, VSPLAT8, SET, q16, I32C, 92, VSPLAT8, SET, bs16, I32C, 32, VSPLAT8, SET, sp16,
      BLK, VOID, LOOP, VOID,
        GET, src, GET, end16, GTS, BRIF, 1,
        GET, src, VLD, 0, TEE, v,
        GET, v, GET, q16, VEQ8, GET, v, GET, bs16, VEQ8, VOR, GET, v, GET, sp16, VLTS8, VOR,
        VBM8, TEE, mask, EQZ, IF, VOID,
          GET, dst, GET, v, VST, 0,
          GET, src, I32C, 16, ADD, SET, src, GET, dst, I32C, 16, ADD, SET, dst, BR, 1,
        END,
        GET, mask, CTZ, TEE, k, IF, VOID,
          GET, dst, GET, v, VST, 0,
          GET, src, GET, k, ADD, SET, src, GET, dst, GET, k, ADD, SET, dst,
        END,
        GET, src, LD8, 0, SET, b, GET, src, I32C, 1, ADD, SET, src,
        ...emitEsc(), BR, 0,
      END, END,
      BLK, VOID, LOOP, VOID,
        GET, src, GET, end, GEU, BRIF, 1,
        GET, src, LD8, 0, SET, b, GET, src, I32C, 1, ADD, SET, src,
        GET, b, I32C, 34, EQ, GET, b, I32C, 92, EQ, OR, GET, b, I32C, 32, LTU, OR, IF, VOID,
          ...emitEsc(),
        ELSE, GET, dst, GET, b, ST8, 0, GET, dst, I32C, 1, ADD, SET, dst, END,
        BR, 0,
      END, END,
      GET, dst, I32C, 34, ST8, 0, GET, dst, I32C, 1, ADD,
    ];
  });

  // 19b. expectByte(pos, end, ch) -> newPos or -1
  def(F.expectByte, [I32, I32, I32], [I32], () => [
    GET, 0, GET, 1, GEU, IF, VOID, I32C, -1, RET, END,
    GET, 0, LD8, 0, GET, 2, NE, IF, VOID, I32C, -1, RET, END,
    GET, 0, I32C, 1, ADD, GET, 1, CALL, F.skipWs,
  ]);

  // 20. solveBatchJson() -> batchOutLen or -1
  def(F.solveBatchJson, [], [I32], (loc) => {
    const end = loc(), pos = loc(), batchOutBase = loc(), batchPtr = loc(), caseIdx = loc();
    const seenInput = loc(), oLen = loc(), nLen = loc(), oBase = loc(), nBase = loc(), buf1 = loc(), len1 = loc();
    const outLen = loc(), outBase = loc(), outEnd = loc(), tmpDst = loc(), tmpEnd = loc(), escLen = loc(), b = loc(), isOld = loc(), ab = loc();
    const expectByte = (ch) => [
      GET, pos, GET, end, I32C, ch, CALL, F.expectByte, TEE, pos, I32C, 0, LTS, IF, VOID, I32C, -1, RET, END,
    ];
    return [
      GGET, G.jsonLen, SET, end,
      I32C, 0, GET, end, CALL, F.skipWs, SET, pos,
      ...expectByte(91),
      GET, end, I32C, 31, ADD, I32C, -16, AND, TEE, batchOutBase, GSET, G.batchOutBase,
      GET, batchOutBase, I32C, 1024, ADD, CALL, F.ensureMem,
      GET, batchOutBase, SET, batchPtr, GET, batchPtr, I32C, 91, ST8, 0, GET, batchPtr, I32C, 1, ADD, SET, batchPtr,
      GET, pos, GET, end, LTU, IF, VOID,
        GET, pos, LD8, 0, I32C, 93, EQ, IF, VOID,
          GET, pos, I32C, 1, ADD, GET, end, CALL, F.skipWs, GET, end, NE, IF, VOID, I32C, -1, RET, END,
          GET, batchPtr, I32C, 93, ST8, 0, GET, batchPtr, I32C, 1, ADD, GET, batchOutBase, SUB, RET,
        END,
      END,
      I32C, 0, SET, caseIdx,
      BLK, VOID, LOOP, VOID,
        GET, caseIdx, I32C, 0, GTS, IF, VOID,
          GET, batchPtr, I32C, 16, ADD, CALL, F.ensureMem,
          GET, batchPtr, I32C, 44, ST8, 0, GET, batchPtr, I32C, 1, ADD, SET, batchPtr,
        END,
        ...expectByte(123),
        I32C, 0, SET, seenInput, I32C, -1, SET, oLen, I32C, -1, SET, nLen,
        BLK, VOID, LOOP, VOID,
          GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
          GET, pos, LD8, 0, I32C, 125, EQ, BRIF, 1,
          GET, pos, I32C, 7, ADD, GET, end, LEU, IF, I32,
            GET, pos, LD32U, 0, I32C, 0x706e6922, EQ, GET, pos, LD32U, 3, I32C, 0x22747570, EQ, AND,
          ELSE, I32C, 0, END, IF, VOID,
            GET, seenInput, IF, VOID, I32C, -1, RET, END, I32C, 1, SET, seenInput,
            GET, pos, I32C, 7, ADD, GET, end, CALL, F.skipWs, SET, pos,
            ...expectByte(58), ...expectByte(123),
            GET, batchPtr, I32C, 31, ADD, I32C, -16, AND, SET, buf1, I32C, 0, SET, len1,
            BLK, VOID, LOOP, VOID,
              GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
              GET, pos, LD8, 0, I32C, 125, EQ, BRIF, 1,
              GET, pos, I32C, 5, ADD, GET, end, GTU, IF, VOID, I32C, -1, RET, END,
              GET, pos, LD8, 4, I32C, 34, NE, IF, VOID, I32C, -1, RET, END,
              GET, pos, LD32U, 0, I32C, 0x646c6f22, EQ, IF, VOID, I32C, 1, SET, isOld,
              ELSE, GET, pos, LD32U, 0, I32C, 0x77656e22, EQ, IF, VOID, I32C, 0, SET, isOld,
              ELSE, I32C, -1, RET, END, END,
              GET, isOld, IF, VOID, GET, oLen, I32C, 0, GES, IF, VOID, I32C, -1, RET, END,
              ELSE, GET, nLen, I32C, 0, GES, IF, VOID, I32C, -1, RET, END, END,
              GET, pos, I32C, 5, ADD, GET, end, CALL, F.skipWs, SET, pos,
              ...expectByte(58),
              GET, oLen, I32C, 0, LTS, GET, nLen, I32C, 0, LTS, AND, IF, VOID,
                GET, buf1, GET, end, GET, pos, SUB, ADD, I32C, 64, ADD, CALL, F.ensureMem,
                GET, pos, GET, end, GET, buf1, CALL, F.unescapeJsonStr, TEE, len1, I32C, 0, LTS, IF, VOID, I32C, -1, RET, END,
                GET, isOld, IF, VOID, GET, buf1, SET, oBase, GET, len1, SET, oLen,
                ELSE, GET, buf1, SET, nBase, GET, len1, SET, nLen, END,
              ELSE,
                GET, buf1, GET, len1, ADD, I32C, 31, ADD, I32C, -16, AND, SET, ab,
                GET, ab, GET, end, GET, pos, SUB, ADD, I32C, 64, ADD, CALL, F.ensureMem,
                GET, pos, GET, end, GET, ab, CALL, F.unescapeJsonStr, TEE, tmpEnd, I32C, 0, LTS, IF, VOID, I32C, -1, RET, END,
                GET, isOld, IF, VOID, GET, ab, SET, oBase, GET, tmpEnd, SET, oLen,
                ELSE, GET, ab, SET, nBase, GET, tmpEnd, SET, nLen, END,
              END,
              GGET, G.jsonCur, GET, end, CALL, F.skipWs, SET, pos,
              GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
              GET, pos, LD8, 0, I32C, 44, EQ, IF, VOID, GET, pos, I32C, 1, ADD, GET, end, CALL, F.skipWs, SET, pos, BR, 1, END,
              BR, 1,
            END, END,
            ...expectByte(125),
          ELSE,
            GET, pos, I32C, 4, ADD, GET, end, LEU, IF, I32, GET, pos, LD32U, 0, I32C, 0x22646922, EQ, ELSE, I32C, 0, END, IF, VOID,
              GET, pos, I32C, 4, ADD, GET, end, CALL, F.skipWs, SET, pos,
            ELSE, GET, pos, I32C, 7, ADD, GET, end, LEU, IF, I32, GET, pos, LD32U, 0, I32C, 0x6f726722, EQ, GET, pos, LD32U, 3, I32C, 0x2270756f, EQ, AND, ELSE, I32C, 0, END, IF, VOID,
              GET, pos, I32C, 7, ADD, GET, end, CALL, F.skipWs, SET, pos,
            ELSE, I32C, -1, RET, END, END,
            ...expectByte(58),
            GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
            GET, pos, LD8, 0, I32C, 34, EQ, IF, VOID,
              GET, pos, GET, end, CALL, F.skipJsonStr, TEE, pos, I32C, 0, LTS, IF, VOID, I32C, -1, RET, END,
            ELSE,
              GET, pos, LD8, 0, I32C, 45, EQ, IF, VOID, GET, pos, I32C, 1, ADD, SET, pos, END,
              GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
              GET, pos, LD8, 0, TEE, b, I32C, 48, LTU, GET, b, I32C, 57, GTU, OR, IF, VOID, I32C, -1, RET, END,
              BLK, VOID, LOOP, VOID,
                GET, pos, GET, end, GEU, BRIF, 1,
                GET, pos, LD8, 0, TEE, b, I32C, 48, LTU, GET, b, I32C, 57, GTU, OR, BRIF, 1,
                GET, pos, I32C, 1, ADD, SET, pos, BR, 0,
              END, END,
            END,
            GET, pos, GET, end, CALL, F.skipWs, SET, pos,
          END,
          GET, pos, GET, end, GEU, IF, VOID, I32C, -1, RET, END,
          GET, pos, LD8, 0, I32C, 44, EQ, IF, VOID, GET, pos, I32C, 1, ADD, GET, end, CALL, F.skipWs, SET, pos, BR, 1, END,
          BR, 1,
        END, END,
        ...expectByte(125),
        GET, seenInput, EQZ, GET, oLen, I32C, 0, LTS, OR, GET, nLen, I32C, 0, LTS, OR, IF, VOID, I32C, -1, RET, END,
        GET, oBase, GSET, G.oBase, GET, oLen, GSET, G.oLen, GET, nBase, GSET, G.nBase, GET, nLen, GSET, G.nLen,
        GET, oBase, GET, oLen, ADD, TEE, ab, GET, nBase, GET, nLen, ADD, TEE, tmpDst,
        GET, ab, GET, tmpDst, GTU, SEL, I32C, 31, ADD, I32C, -16, AND, GSET, G.arenaBase,
        CALL, F.solveAscii, TEE, outLen, I32C, 0, LTS, IF, VOID, I32C, -1, RET, END,
        GGET, G.outBase, SET, outBase, GGET, G.outEnd, SET, outEnd,
        GET, batchPtr, GET, outLen, I32C, 6, MUL, ADD, I32C, 64, ADD, GET, outBase, LEU, IF, VOID,
          GET, outBase, GET, outLen, GET, batchPtr, CALL, F.escapeJsonOut, SET, batchPtr,
        ELSE,
          GET, outEnd, I32C, 31, ADD, I32C, -16, AND, SET, tmpDst,
          GET, tmpDst, GET, outLen, I32C, 6, MUL, ADD, I32C, 64, ADD, CALL, F.ensureMem,
          GET, outBase, GET, outLen, GET, tmpDst, CALL, F.escapeJsonOut, SET, tmpEnd,
          GET, tmpEnd, GET, tmpDst, SUB, SET, escLen,
          GET, batchPtr, GET, tmpDst, GET, escLen, MCOPY,
          GET, batchPtr, GET, escLen, ADD, SET, batchPtr,
        END,
        GET, caseIdx, I32C, 1, ADD, SET, caseIdx,
        GET, pos, GET, end, LTU, IF, VOID,
          GET, pos, LD8, 0, I32C, 44, EQ, IF, VOID, GET, pos, I32C, 1, ADD, GET, end, CALL, F.skipWs, SET, pos, BR, 2, END,
        END,
        BR, 1,
      END, END,
      ...expectByte(93),
      GET, pos, GET, end, NE, IF, VOID, I32C, -1, RET, END,
      GET, batchPtr, I32C, 16, ADD, CALL, F.ensureMem,
      GET, batchPtr, I32C, 93, ST8, 0, GET, batchPtr, I32C, 1, ADD, GET, batchOutBase, SUB,
    ];
  });

  // Encode WASM module directly into a single Uint8Array
  const out = new Uint8Array(32768);
  let p = 0;
  out[p++] = 0x00; out[p++] = 0x61; out[p++] = 0x73; out[p++] = 0x6d;
  out[p++] = 0x01; out[p++] = 0x00; out[p++] = 0x00; out[p++] = 0x00;
  const beginSec = (id) => { out[p++] = id; const lp = p; p += 5; return lp; };
  const endSec = (lp) => {
    let len = p - (lp + 5);
    for (let i = 0; i < 4; i++) { out[lp + i] = (len & 0x7f) | 0x80; len >>>= 7; }
    out[lp + 4] = len & 0x7f;
  };

  let lp = beginSec(1);
  p = writeUleb(out, p, types.length);
  for (let i = 0; i < types.length; i++) {
    const t = types[i];
    out[p++] = 0x60;
    p = writeUleb(out, p, t.params.length);
    for (let j = 0; j < t.params.length; j++) out[p++] = t.params[j];
    p = writeUleb(out, p, t.results.length);
    for (let j = 0; j < t.results.length; j++) out[p++] = t.results[j];
  }
  endSec(lp);

  lp = beginSec(3);
  p = writeUleb(out, p, funcs.length);
  for (let i = 0; i < funcs.length; i++) p = writeUleb(out, p, funcs[i].typeIdx);
  endSec(lp);

  lp = beginSec(5);
  out[p++] = 0x01; out[p++] = 0x00; p = writeUleb(out, p, 256);
  endSec(lp);

  lp = beginSec(6);
  p = writeUleb(out, p, gc);
  for (let i = 0; i < gc; i++) { out[p++] = I32; out[p++] = 0x01; out[p++] = I32C; out[p++] = 0x00; out[p++] = END; }
  endSec(lp);

  const exports = [
    ['memory', 0x02, 0], ['prepareInput', 0x00, F.prepareInput], ['prepareBatch', 0x00, F.prepareBatch],
    ['solveAscii', 0x00, F.solveAscii], ['solveBatchJson', 0x00, F.solveBatchJson],
    ['getOutBase', 0x00, F.getOutBase], ['getBatchOutBase', 0x00, F.getBatchOutBase],
  ];
  lp = beginSec(7);
  p = writeUleb(out, p, exports.length);
  for (let i = 0; i < exports.length; i++) {
    const [name, kind, idx] = exports[i];
    p = writeUleb(out, p, name.length);
    for (let j = 0; j < name.length; j++) out[p++] = name.charCodeAt(j);
    out[p++] = kind; p = writeUleb(out, p, idx);
  }
  endSec(lp);

  lp = beginSec(10);
  p = writeUleb(out, p, funcs.length);
  for (let i = 0; i < funcs.length; i++) {
    const fn = funcs[i], locs = fn.locals;
    const bodyStart = p + 5;
    let bp = bodyStart;
    // Group consecutive locals
    let grpCount = 0;
    const gCounts = [], gTypes = [];
    for (let j = 0; j < locs.length; j++) {
      const t = locs[j];
      if (grpCount > 0 && gTypes[grpCount - 1] === t) gCounts[grpCount - 1]++;
      else { gCounts[grpCount] = 1; gTypes[grpCount] = t; grpCount++; }
    }
    bp = writeUleb(out, bp, grpCount);
    for (let j = 0; j < grpCount; j++) { bp = writeUleb(out, bp, gCounts[j]); out[bp++] = gTypes[j]; }
    bp = encodeBody(fn.ops, out, bp);
    let len = bp - bodyStart;
    for (let j = 0; j < 4; j++) { out[p + j] = (len & 0x7f) | 0x80; len >>>= 7; }
    out[p + 4] = len & 0x7f;
    p = bp;
  }
  endSec(lp);

  const mod = new WebAssembly.Module(out.subarray(0, p));
  return new WebAssembly.Instance(mod).exports;
}
