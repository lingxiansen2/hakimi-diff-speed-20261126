// Hand-authored WebAssembly bytecode builder for zero-copy ASCII Myers diff & patch construction.
// Compiles synchronously via WebAssembly.Module in < 0.5 ms with zero external dependencies.

const I32 = 0x7f;
const I64 = 0x7e;
const VOID = 0x40;
const KEEP = 0;
const DELETE = 1;
const INSERT = 2;

const OP = {
  unreachable: 0x00,
  nop: 0x01,
  block: 0x02,
  loop: 0x03,
  if: 0x04,
  else: 0x05,
  end: 0x0b,
  br: 0x0c,
  br_if: 0x0d,
  return: 0x0f,
  call: 0x10,
  drop: 0x1a,
  select: 0x1b,
  local_get: 0x20,
  local_set: 0x21,
  local_tee: 0x22,
  global_get: 0x23,
  global_set: 0x24,
  i32_load: 0x28,
  i64_load: 0x29,
  i32_load8_u: 0x2d,
  i32_store: 0x36,
  i64_store: 0x37,
  i32_store8: 0x3a,
  memory_size: 0x3f,
  memory_grow: 0x40,
  i32_const: 0x41,
  i64_const: 0x42,
  i32_eqz: 0x45,
  i32_eq: 0x46,
  i32_ne: 0x47,
  i32_lt_s: 0x48,
  i32_lt_u: 0x49,
  i32_gt_s: 0x4a,
  i32_gt_u: 0x4b,
  i32_le_s: 0x4c,
  i32_le_u: 0x4d,
  i32_ge_s: 0x4e,
  i32_ge_u: 0x4f,
  i64_eqz: 0x50,
  i64_eq: 0x51,
  i64_ne: 0x52,
  i64_lt_u: 0x54,
  i64_popcnt: 0x7b, // wait: i64.ctz=0x7a, i64.popcnt=0x7b? CHECK: 0x79=clz, 0x7a=ctz, 0x7b=popcnt!
  i64_ctz: 0x7a,
  i32_add: 0x6a,
  i32_sub: 0x6b,
  i32_mul: 0x6c,
  i32_div_s: 0x6d,
  i32_div_u: 0x6e,
  i32_rem_u: 0x70,
  i32_and: 0x71,
  i32_or: 0x72,
  i32_xor: 0x73,
  i32_shl: 0x74,
  i32_shr_s: 0x75,
  i32_shr_u: 0x76,
  i64_add: 0x7c,
  i64_sub: 0x7d,
  i64_mul: 0x7e,
  i64_and: 0x83,
  i64_or: 0x84,
  i64_xor: 0x85,
  i64_shl: 0x86,
  i64_shr_u: 0x88,
  i32_wrap_i64: 0xa7,
  i64_extend_i32_u: 0xad,
  memory_copy_pre: 0xfc, // bulk memory: 0xfc 0x0a 0x00 0x00
  memory_fill_pre: 0xfc, // bulk memory: 0xfc 0x0b 0x00
};

function pushUleb(out, v) {
  v >>>= 0;
  while (v >= 0x80) {
    out.push((v & 0x7f) | 0x80);
    v >>>= 7;
  }
  out.push(v);
}

function pushSleb32(out, v) {
  v |= 0;
  while (true) {
    const b = v & 0x7f;
    v >>= 7;
    if ((v === 0 && (b & 0x40) === 0) || (v === -1 && (b & 0x40) !== 0)) {
      out.push(b);
      break;
    }
    out.push(b | 0x80);
  }
}

function pushSleb64(out, v) {
  let x = BigInt.asIntN(64, BigInt(v));
  while (true) {
    const b = Number(x & 0x7fn);
    x >>= 7n;
    if ((x === 0n && (b & 0x40) === 0) || (x === -1n && (b & 0x40) !== 0)) {
      out.push(b);
      break;
    }
    out.push(b | 0x80);
  }
}

function encodeSection(id, payload) {
  const sec = [id];
  pushUleb(sec, payload.length);
  for (let i = 0; i < payload.length; i++) sec.push(payload[i]);
  return sec;
}

class FuncEmitter {
  constructor(params, results) {
    this.params = params;
    this.results = results;
    this.locals = [];
    this.code = [];
  }
  loc(type = I32) {
    const idx = this.params.length + this.locals.length;
    this.locals.push(type);
    return idx;
  }
  op(o) { this.code.push(o); return this; }
  i32(v) { this.code.push(OP.i32_const); pushSleb32(this.code, v); return this; }
  i64(v) { this.code.push(OP.i64_const); pushSleb64(this.code, v); return this; }
  get(l) { this.code.push(OP.local_get); pushUleb(this.code, l); return this; }
  set(l) { this.code.push(OP.local_set); pushUleb(this.code, l); return this; }
  tee(l) { this.code.push(OP.local_tee); pushUleb(this.code, l); return this; }
  gget(g) { this.code.push(OP.global_get); pushUleb(this.code, g); return this; }
  gset(g) { this.code.push(OP.global_set); pushUleb(this.code, g); return this; }
  call(f) { this.code.push(OP.call); pushUleb(this.code, f); return this; }
  load32(off = 0) { this.code.push(OP.i32_load, 2); pushUleb(this.code, off); return this; }
  load32u(off = 0) { this.code.push(OP.i32_load, 0); pushUleb(this.code, off); return this; }
  load64(off = 0) { this.code.push(OP.i64_load, 0); pushUleb(this.code, off); return this; }
  load8(off = 0) { this.code.push(OP.i32_load8_u, 0); pushUleb(this.code, off); return this; }
  store32(off = 0) { this.code.push(OP.i32_store, 2); pushUleb(this.code, off); return this; }
  store64(off = 0) { this.code.push(OP.i64_store, 0); pushUleb(this.code, off); return this; }
  store8(off = 0) { this.code.push(OP.i32_store8, 0); pushUleb(this.code, off); return this; }
  block(ty = VOID) { this.code.push(OP.block, ty); return this; }
  loop(ty = VOID) { this.code.push(OP.loop, ty); return this; }
  if_(ty = VOID) { this.code.push(OP.if, ty); return this; }
  else_() { this.code.push(OP.else); return this; }
  end() { this.code.push(OP.end); return this; }
  br(d) { this.code.push(OP.br); pushUleb(this.code, d); return this; }
  br_if(d) { this.code.push(OP.br_if); pushUleb(this.code, d); return this; }
  ret() { this.code.push(OP.return); return this; }
  memCopy() { this.code.push(0xfc, 0x0a, 0x00, 0x00); return this; }
  memFill() { this.code.push(0xfc, 0x0b, 0x00); return this; }
  memSize() { this.code.push(OP.memory_size, 0x00); return this; }
  memGrow() { this.code.push(OP.memory_grow, 0x00); return this; }

  // Compound helpers for clean readable expressions
  loadArr32(baseG, idxL) {
    return this.gget(baseG).get(idxL).i32(2).op(OP.i32_shl).op(OP.i32_add).load32();
  }
  storeArr32(baseG, idxL, emitVal) {
    this.gget(baseG).get(idxL).i32(2).op(OP.i32_shl).op(OP.i32_add);
    emitVal();
    return this.store32();
  }
  loadArr64(baseG, idxL) {
    return this.gget(baseG).get(idxL).i32(3).op(OP.i32_shl).op(OP.i32_add).load64();
  }
  storeArr64(baseG, idxL, emitVal) {
    this.gget(baseG).get(idxL).i32(3).op(OP.i32_shl).op(OP.i32_add);
    emitVal();
    return this.store64();
  }
  loadArr8(baseG, idxL) {
    return this.gget(baseG).get(idxL).op(OP.i32_add).load8();
  }
  storeArr8(baseG, idxL, emitVal) {
    this.gget(baseG).get(idxL).op(OP.i32_add);
    emitVal();
    return this.store8();
  }
  arrPtr32(baseG, idxL) {
    return this.gget(baseG).get(idxL).i32(2).op(OP.i32_shl).op(OP.i32_add);
  }
}

export function buildDiffWasm() {
  const types = [];
  const typeMap = new Map();
  function internType(params, results) {
    const key = `${params.join(',')}=>${results.join(',')}`;
    let id = typeMap.get(key);
    if (id === undefined) {
      id = types.length;
      types.push({ params, results });
      typeMap.set(key, id);
    }
    return id;
  }

  let globalCount = 0;
  const g = () => globalCount++;

  // Globals (all mutable i32)
  const G = {
    oBase: g(), oLen: g(), nBase: g(), nLen: g(),
    oStart: g(), nStart: g(), oEnd: g(), nEnd: g(),
    prefix: g(), suffix: g(), n: g(), m: g(),
    arenaPtr: g(),
    oStarts: g(), oEnds: g(), oHash: g(),
    nStarts: g(), nEnds: g(), nHash: g(),
    buckets: g(), hMask: g(),
    A: g(), B: g(), cntA: g(), cntB: g(), posB: g(), seen: g(),
    remDel: g(), remIns: g(),
    tailsVal: g(), tailsA: g(), prevIdx: g(), ancA: g(), ancB: g(),
    isUniq: g(), inLIS: g(), usedLIS: g(), grid64: g(),
    gVp: g(), gVc: g(),
    Vp: g(), Vc: g(), repBuf: g(),
    ckptMeta: g(), ckptData: g(), ckptDataPtr: g(), ckptCap: g(),
    bShift: g(), bStep: g(), bMask: g(),
    ansD: g(), ansK: g(), U: g(),
    revKind: g(), revCount: g(), opLen: g(),
    changesO: g(), changesP: g(), changesD: g(), changesI: g(), numChanges: g(),
    hStart: g(), hEnd: g(), numHunks: g(),
    deleted: g(), inserted: g(),
    outBase: g(), outEnd: g(),
  };

  // Function indices
  let funcCount = 0;
  const fnId = () => funcCount++;
  const F = {
    ensureMem: fnId(),
    countLines: fnId(),
    trimPrefixSuffix: fnId(),
    scanLines: fnId(),
    internLines: fnId(),
    buildBoundsAndUB: fnId(),
    myersForward: fnId(),
    replayPath: fnId(),
    buildChangesAndHunks: fnId(),
    writeDec: fnId(),
    writeStrConst: fnId(),
    pushLineOut: fnId(),
    buildPatch: fnId(),
    solveAscii: fnId(),
    getOutBase: fnId(),
    prepareInput: fnId(),
  };

  const funcs = new Array(funcCount);
  const addFunc = (id, params, results, build) => {
    const f = new FuncEmitter(params, results);
    build(f);
    f.end();
    funcs[id] = { typeIdx: internType(params, results), emitter: f };
  };

  // ------------------------------------------------------------------ 1. ensureMem(neededBytes)
  addFunc(F.ensureMem, [I32], [], (f) => {
    const need = 0;
    const curBytes = f.loc();
    const needPages = f.loc();
    const curPages = f.loc();
    f.memSize().tee(curPages).i32(16).op(OP.i32_shl).set(curBytes);
    f.get(need).get(curBytes).op(OP.i32_gt_u).if_();
    f.get(need).i32(65535).op(OP.i32_add).i32(16).op(OP.i32_shr_u).set(needPages);
    f.get(needPages).get(curPages).op(OP.i32_sub).memGrow().i32(-1).op(OP.i32_eq).if_().op(OP.unreachable).end();
    f.end();
  });

  // ------------------------------------------------------------------ 2. prepareInput(oLen, nLen) -> i32 (nBase)
  addFunc(F.prepareInput, [I32, I32], [I32], (f) => {
    const oLen = 0, nLen = 1;
    const nBase = f.loc();
    f.i32(0).gset(G.oBase);
    f.get(oLen).gset(G.oLen);
    f.get(oLen).i32(23).op(OP.i32_add).i32(-8).op(OP.i32_and).tee(nBase).gset(G.nBase);
    f.get(nLen).gset(G.nLen);
    f.get(nBase).get(nLen).op(OP.i32_add).i32(64).op(OP.i32_add).call(F.ensureMem);
    f.get(nBase);
  });

  // ------------------------------------------------------------------ 3. countLines(ptr, len) -> i32
  // Exact 8-byte SWAR newline popcount without borrow propagation.
  addFunc(F.countLines, [I32, I32], [I32], (f) => {
    const ptr = 0, len = 1;
    const cnt = f.loc(), end = f.loc(), end8 = f.loc(), p = f.loc();
    const x = f.loc(I64), u = f.loc(I64);
    f.get(len).op(OP.i32_eqz).if_().i32(0).ret().end();
    f.i32(0).set(cnt);
    f.get(ptr).set(p);
    f.get(ptr).get(len).op(OP.i32_add).set(end);
    f.get(end).i32(8).op(OP.i32_sub).set(end8);

    f.block().loop();
    f.get(p).get(end8).op(OP.i32_gt_s).br_if(1);
    f.get(p).load64().i64(0x0a0a0a0a0a0a0a0an).op(OP.i64_xor).set(x);
    f.get(x).i64(0x7f7f7f7f7f7f7f7fn).op(OP.i64_and).set(u);
    f.get(u).i64(0x7f7f7f7f7f7f7f7fn).op(OP.i64_add)
      .get(x).op(OP.i64_or)
      .i64(0x7f7f7f7f7f7f7f7fn).op(OP.i64_or)
      .i64(-1n).op(OP.i64_xor)
      .op(OP.i64_popcnt).op(OP.i32_wrap_i64)
      .get(cnt).op(OP.i32_add).set(cnt);
    f.get(p).i32(8).op(OP.i32_add).set(p);
    f.br(0).end().end();

    f.block().loop();
    f.get(p).get(end).op(OP.i32_ge_u).br_if(1);
    f.get(p).load8().i32(10).op(OP.i32_eq).if_();
    f.get(cnt).i32(1).op(OP.i32_add).set(cnt);
    f.end();
    f.get(p).i32(1).op(OP.i32_add).set(p);
    f.br(0).end().end();

    f.get(end).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_ne).if_();
    f.get(cnt).i32(1).op(OP.i32_add).set(cnt);
    f.end();
    f.get(cnt);
  });

  // ------------------------------------------------------------------ 4. trimPrefixSuffix()
  addFunc(F.trimPrefixSuffix, [], [], (f) => {
    const oBase = f.loc(), nBase = f.loc(), oLen = f.loc(), nLen = f.loc();
    const minL = f.loc(), p = f.loc(), min8 = f.loc();
    const oPtr = f.loc(), nPtr = f.loc(), s = f.loc(), maxS = f.loc(), maxS8 = f.loc();
    const b1 = f.loc(), b2 = f.loc(), diff = f.loc(I64);

    f.gget(G.oBase).set(oBase);
    f.gget(G.nBase).set(nBase);
    f.gget(G.oLen).set(oLen);
    f.gget(G.nLen).set(nLen);
    f.get(oLen).get(nLen).get(oLen).get(nLen).op(OP.i32_lt_u).op(OP.select).set(minL);

    // Common byte prefix via i64.load
    f.i32(0).set(p);
    f.get(minL).i32(8).op(OP.i32_sub).set(min8);
    f.block().loop();
    f.get(p).get(min8).op(OP.i32_gt_s).br_if(1);
    f.get(oBase).get(p).op(OP.i32_add).load64()
      .get(nBase).get(p).op(OP.i32_add).load64()
      .op(OP.i64_xor).tee(diff).op(OP.i64_eqz).op(OP.i32_eqz).if_();
    f.get(p).get(diff).op(OP.i64_ctz).op(OP.i32_wrap_i64).i32(3).op(OP.i32_shr_u).op(OP.i32_add).set(p);
    f.br(2);
    f.end();
    f.get(p).i32(8).op(OP.i32_add).set(p);
    f.br(0).end().end();

    f.block().loop();
    f.get(p).get(minL).op(OP.i32_ge_u).br_if(1);
    f.get(oBase).get(p).op(OP.i32_add).load8()
      .get(nBase).get(p).op(OP.i32_add).load8()
      .op(OP.i32_ne).br_if(1);
    f.get(p).i32(1).op(OP.i32_add).set(p);
    f.br(0).end().end();

    // If identical:
    f.get(p).get(oLen).op(OP.i32_eq).get(p).get(nLen).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(oBase).get(oLen).call(F.countLines).gset(G.prefix);
    f.i32(0).gset(G.suffix);
    f.get(oLen).gset(G.oStart);
    f.get(nLen).gset(G.nStart);
    f.get(oLen).gset(G.oEnd);
    f.get(nLen).gset(G.nEnd);
    f.ret();
    f.end();

    // Roll back p to line boundary (after previous 0x0a or 0)
    f.block().loop();
    f.get(p).op(OP.i32_eqz).br_if(1);
    f.get(oBase).get(p).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_eq).br_if(1);
    f.get(p).i32(1).op(OP.i32_sub).set(p);
    f.br(0).end().end();

    f.get(p).gset(G.oStart);
    f.get(p).gset(G.nStart);
    f.get(oBase).get(p).call(F.countLines).gset(G.prefix);

    // Common byte suffix from oLen, nLen back to p
    f.get(oLen).get(p).op(OP.i32_sub).set(b1);
    f.get(nLen).get(p).op(OP.i32_sub).set(b2);
    f.get(b1).get(b2).get(b1).get(b2).op(OP.i32_lt_u).op(OP.select).set(maxS);
    f.i32(0).set(s);
    f.get(maxS).i32(8).op(OP.i32_sub).set(maxS8);

    f.block().loop();
    f.get(s).get(maxS8).op(OP.i32_gt_s).br_if(1);
    f.get(oBase).get(oLen).op(OP.i32_add).get(s).op(OP.i32_sub).i32(8).op(OP.i32_sub).load64()
      .get(nBase).get(nLen).op(OP.i32_add).get(s).op(OP.i32_sub).i32(8).op(OP.i32_sub).load64()
      .op(OP.i64_ne).br_if(1);
    f.get(s).i32(8).op(OP.i32_add).set(s);
    f.br(0).end().end();

    f.block().loop();
    f.get(s).get(maxS).op(OP.i32_ge_u).br_if(1);
    f.get(oBase).get(oLen).op(OP.i32_add).get(s).op(OP.i32_sub).i32(1).op(OP.i32_sub).load8()
      .get(nBase).get(nLen).op(OP.i32_add).get(s).op(OP.i32_sub).i32(1).op(OP.i32_sub).load8()
      .op(OP.i32_ne).br_if(1);
    f.get(s).i32(1).op(OP.i32_add).set(s);
    f.br(0).end().end();

    f.get(oLen).get(s).op(OP.i32_sub).set(oPtr);
    f.get(nLen).get(s).op(OP.i32_sub).set(nPtr);

    f.get(s).i32(0).op(OP.i32_gt_s).if_();
    // Check if already at line boundary in both
    f.get(oPtr).get(p).op(OP.i32_eq)
      .if_(I32).i32(1).else_().get(oBase).get(oPtr).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_eq).end()
      .get(nPtr).get(p).op(OP.i32_eq)
      .if_(I32).i32(1).else_().get(nBase).get(nPtr).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_eq).end()
      .op(OP.i32_and).op(OP.i32_eqz).if_();
    // Advance oPtr & nPtr together to just after next 0x0a in [oPtr..oLen)
    f.block().loop();
    f.get(oPtr).get(oLen).op(OP.i32_ge_u).br_if(1);
    f.get(oBase).get(oPtr).op(OP.i32_add).load8().i32(10).op(OP.i32_eq).if_();
    f.get(oPtr).i32(1).op(OP.i32_add).set(oPtr);
    f.get(nPtr).i32(1).op(OP.i32_add).set(nPtr);
    f.br(2);
    f.end();
    f.get(oPtr).i32(1).op(OP.i32_add).set(oPtr);
    f.get(nPtr).i32(1).op(OP.i32_add).set(nPtr);
    f.br(0).end().end();
    f.end();
    f.end();

    f.get(oPtr).gset(G.oEnd);
    f.get(nPtr).gset(G.nEnd);
    f.get(oBase).get(oPtr).op(OP.i32_add).get(oLen).get(oPtr).op(OP.i32_sub).call(F.countLines).gset(G.suffix);
  });

  // ------------------------------------------------------------------ 5. scanLines()
  // Allocates arena arrays for exact (n, m) and scans + hashes lines using 64-bit i64 hash.
  addFunc(F.scanLines, [], [], (f) => {
    const n = f.loc(), m = f.loc(), minNM = f.loc(), hCap = f.loc(), ptr = f.loc();
    const allocArr = (gVar, bytesExpr) => {
      f.get(ptr).gset(gVar);
      f.get(ptr);
      bytesExpr();
      f.op(OP.i32_add).i32(7).op(OP.i32_add).i32(-8).op(OP.i32_and).set(ptr);
    };

    f.gget(G.oBase).gget(G.oStart).op(OP.i32_add).gget(G.oEnd).gget(G.oStart).op(OP.i32_sub).call(F.countLines).tee(n).gset(G.n);
    f.gget(G.nBase).gget(G.nStart).op(OP.i32_add).gget(G.nEnd).gget(G.nStart).op(OP.i32_sub).call(F.countLines).tee(m).gset(G.m);
    f.get(n).get(m).get(n).get(m).op(OP.i32_lt_u).op(OP.select).set(minNM);

    f.gget(G.nBase).gget(G.nLen).op(OP.i32_add).i32(31).op(OP.i32_add).i32(-8).op(OP.i32_and).set(ptr);
    allocArr(G.oStarts, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.oEnds, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.oHash, () => f.get(n).i32(4).op(OP.i32_add).i32(3).op(OP.i32_shl));
    allocArr(G.nStarts, () => f.get(m).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.nEnds, () => f.get(m).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.nHash, () => f.get(m).i32(4).op(OP.i32_add).i32(3).op(OP.i32_shl));

    // If n===0 || m===0, stop early — no intern/myers needed!
    f.get(n).op(OP.i32_eqz).get(m).op(OP.i32_eqz).op(OP.i32_or).if_();
    // Still need oStarts/oEnds or nStarts/nEnds for the single non-empty side!
    allocArr(G.changesO, () => f.i32(16));
    allocArr(G.changesP, () => f.i32(16));
    allocArr(G.changesD, () => f.i32(16));
    allocArr(G.changesI, () => f.i32(16));
    allocArr(G.hStart, () => f.i32(16));
    allocArr(G.hEnd, () => f.i32(16));
    f.get(ptr).gset(G.arenaPtr);
    f.get(ptr).i32(64).op(OP.i32_add).call(F.ensureMem);
    // Scan whichever of n, m > 0
    const scanSide = (baseG, stG, enG, startsG, endsG, hashG) => {
      const idx = f.loc(), pos = f.loc(), end = f.loc(), base = f.loc(), ls = f.loc(), e = f.loc();
      f.gget(baseG).set(base).gget(stG).set(pos).gget(enG).set(end).i32(0).set(idx);
      f.block().loop();
      f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
      f.get(pos).set(ls);
      f.block().loop();
      f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
      f.get(base).get(pos).op(OP.i32_add).load8().i32(10).op(OP.i32_eq).if_();
      f.get(pos).i32(1).op(OP.i32_add).set(pos).br(2);
      f.end();
      f.get(pos).i32(1).op(OP.i32_add).set(pos);
      f.br(0).end().end();
      f.storeArr32(startsG, idx, () => f.get(ls));
      f.storeArr32(endsG, idx, () => f.get(pos));
      f.get(idx).i32(1).op(OP.i32_add).set(idx);
      f.br(0).end().end();
    };
    f.get(n).if_(); scanSide(G.oBase, G.oStart, G.oEnd, G.oStarts, G.oEnds, G.oHash); f.end();
    f.get(m).if_(); scanSide(G.nBase, G.nStart, G.nEnd, G.nStarts, G.nEnds, G.nHash); f.end();
    f.ret();
    f.end();

    // Full arena allocation
    f.i32(16).set(hCap);
    f.block().loop();
    f.get(hCap).get(n).i32(1).op(OP.i32_shl).op(OP.i32_ge_u).br_if(1);
    f.get(hCap).i32(1).op(OP.i32_shl).set(hCap);
    f.br(0).end().end();
    f.get(hCap).i32(1).op(OP.i32_sub).gset(G.hMask);

    allocArr(G.buckets, () => f.get(hCap).i32(2).op(OP.i32_shl));
    allocArr(G.A, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.B, () => f.get(m).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.cntA, () => f.get(n).i32(2).op(OP.i32_shl));
    allocArr(G.cntB, () => f.get(n).i32(2).op(OP.i32_shl));
    allocArr(G.posB, () => f.get(n).i32(2).op(OP.i32_shl));
    allocArr(G.seen, () => f.get(n).i32(2).op(OP.i32_shl));
    allocArr(G.remDel, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.remIns, () => f.get(m).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.tailsVal, () => f.get(minNM).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.tailsA, () => f.get(minNM).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.prevIdx, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.ancA, () => f.get(minNM).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.ancB, () => f.get(minNM).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.isUniq, () => f.get(n).i32(4).op(OP.i32_add));
    allocArr(G.inLIS, () => f.get(n).i32(4).op(OP.i32_add));
    allocArr(G.usedLIS, () => f.get(minNM).i32(4).op(OP.i32_add));
    allocArr(G.grid64, () => f.i32(65 * 65 * 4));
    allocArr(G.gVp, () => f.i32(520 * 4));
    allocArr(G.gVc, () => f.i32(520 * 4));
    f.get(ptr).gset(G.arenaPtr);
    f.get(ptr).i32(64).op(OP.i32_add).call(F.ensureMem);

    // Zero buckets, cntA, cntB
    f.gget(G.buckets).i32(0).get(hCap).i32(2).op(OP.i32_shl).memFill();
    f.gget(G.cntA).i32(0).get(n).i32(2).op(OP.i32_shl).memFill();
    f.gget(G.cntB).i32(0).get(n).i32(2).op(OP.i32_shl).memFill();

    // Scan & 64-bit SWAR hash lines for A and B
    const scanHashSide = (baseG, stG, enG, startsG, endsG, hashG) => {
      const idx = f.loc(), pos = f.loc(), end = f.loc(), base = f.loc(), ls = f.loc();
      const end8 = f.loc(), w = f.loc(I64), x = f.loc(I64), z = f.loc(I64), h = f.loc(I64), b = f.loc(), tailMask = f.loc(I64), tailW = f.loc(I64), sh = f.loc();
      f.gget(baseG).set(base).gget(stG).set(pos).gget(enG).set(end).i32(0).set(idx);
      f.get(end).i32(8).op(OP.i32_sub).set(end8);
      f.block().loop();
      f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
      f.get(pos).set(ls);
      f.i64(0xcbf29ce484222325n).set(h);
      f.block(); // foundLine block (skips byte tail if SWAR already found \n)
      // 8-byte SWAR newline scan + 64-bit FNV-1a mix
      f.block().loop();
      f.get(pos).get(end8).op(OP.i32_gt_s).br_if(1);
      f.get(base).get(pos).op(OP.i32_add).load64().tee(w).i64(0x0a0a0a0a0a0a0a0an).op(OP.i64_xor).set(x);
      f.get(x).i64(0x0101010101010101n).op(OP.i64_sub)
        .get(x).i64(-1n).op(OP.i64_xor).op(OP.i64_and)
        .i64(0x8080808080808080n).op(OP.i64_and).tee(z).op(OP.i64_eqz).op(OP.i32_eqz).if_();
      // Found 0x0a at byte b = ctz(z) >> 3
      f.get(z).op(OP.i64_ctz).op(OP.i32_wrap_i64).i32(3).op(OP.i32_shr_u).set(b);
      // Mask bytes 0..b (b+1 bytes) of w: (-1 >>> ((7 - b) * 8))
      f.i64(-1n).i32(7).get(b).op(OP.i32_sub).i32(3).op(OP.i32_shl).op(OP.i64_extend_i32_u).op(OP.i64_shr_u).set(tailMask);
      f.get(h).get(w).get(tailMask).op(OP.i64_and).op(OP.i64_xor).i64(0x100000001b3n).op(OP.i64_mul).set(h);
      f.get(pos).get(b).op(OP.i32_add).i32(1).op(OP.i32_add).set(pos);
      f.br(3);
      f.end();
      f.get(h).get(w).op(OP.i64_xor).i64(0x100000001b3n).op(OP.i64_mul).set(h);
      f.get(pos).i32(8).op(OP.i32_add).set(pos);
      f.br(0).end().end();

      // Byte tail for < 8 bytes: pack into little-endian tailW so hash matches SWAR tailMask!
      f.i64(0n).set(tailW).i32(0).set(sh);
      f.block().loop();
      f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
      f.get(base).get(pos).op(OP.i32_add).load8().set(b);
      f.get(tailW).get(b).op(OP.i64_extend_i32_u).get(sh).op(OP.i64_extend_i32_u).op(OP.i64_shl).op(OP.i64_or).set(tailW);
      f.get(sh).i32(8).op(OP.i32_add).set(sh);
      f.get(pos).i32(1).op(OP.i32_add).set(pos);
      f.get(b).i32(10).op(OP.i32_eq).br_if(1);
      f.br(0).end().end();
      f.get(sh).if_();
      f.get(h).get(tailW).op(OP.i64_xor).i64(0x100000001b3n).op(OP.i64_mul).set(h);
      f.end();
      f.end(); // end foundLine block

      f.storeArr32(startsG, idx, () => f.get(ls));
      f.storeArr32(endsG, idx, () => f.get(pos));
      f.storeArr64(hashG, idx, () => f.get(h));
      f.get(idx).i32(1).op(OP.i32_add).set(idx);
      f.br(0).end().end();
    };
    scanHashSide(G.oBase, G.oStart, G.oEnd, G.oStarts, G.oEnds, G.oHash);
    scanHashSide(G.nBase, G.nStart, G.nEnd, G.nStarts, G.nEnds, G.nHash);
  });

  // ------------------------------------------------------------------ 6. internLines()
  addFunc(F.internLines, [], [], (f) => {
    const n = f.loc(), m = f.loc(), hMask = f.loc(), oBase = f.loc(), nBase = f.loc();
    const i = f.loc(), st = f.loc(), len = f.loc(), hi = f.loc(I64), slot = f.loc(), bk = f.loc(), rep = f.loc();
    const rs = f.loc(), k = f.loc(), p1 = f.loc(), p2 = f.loc(), found = f.loc();

    f.gget(G.n).set(n).gget(G.m).set(m).gget(G.hMask).set(hMask).gget(G.oBase).set(oBase).gget(G.nBase).set(nBase);

    // Emit equality helper macro for two byte slices (base1+rs, base2+st, len) -> br_if match
    const checkEq = (base2L, onMatch) => {
      f.get(oBase).get(rs).op(OP.i32_add).set(p1);
      f.get(base2L).get(st).op(OP.i32_add).set(p2);
      f.i32(0).set(k);
      f.block(); // mismatch block
      f.block().loop();
      f.get(k).i32(8).op(OP.i32_add).get(len).op(OP.i32_gt_u).br_if(1);
      f.get(p1).get(k).op(OP.i32_add).load64().get(p2).get(k).op(OP.i32_add).load64().op(OP.i64_ne).br_if(2);
      f.get(k).i32(8).op(OP.i32_add).set(k);
      f.br(0).end().end();
      f.block().loop();
      f.get(k).get(len).op(OP.i32_ge_u).br_if(1);
      f.get(p1).get(k).op(OP.i32_add).load8().get(p2).get(k).op(OP.i32_add).load8().op(OP.i32_ne).br_if(2);
      f.get(k).i32(1).op(OP.i32_add).set(k);
      f.br(0).end().end();
      onMatch();
      f.end();
    };

    // Intern old lines
    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(n).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.oStarts, i).set(st);
    f.loadArr32(G.oEnds, i).get(st).op(OP.i32_sub).set(len);
    f.loadArr64(G.oHash, i).set(hi);
    // Mix upper and lower 32 bits for slot
    f.get(hi).get(hi).i64(32n).op(OP.i64_shr_u).op(OP.i64_xor).op(OP.i32_wrap_i64).get(hMask).op(OP.i32_and).set(slot);
    f.block().loop();
    f.loadArr32(G.buckets, slot).tee(bk).op(OP.i32_eqz).if_();
    f.storeArr32(G.buckets, slot, () => f.get(i).i32(1).op(OP.i32_add));
    f.storeArr32(G.A, i, () => f.get(i));
    f.storeArr32(G.cntA, i, () => f.i32(1));
    f.br(2);
    f.end();
    f.get(bk).i32(1).op(OP.i32_sub).set(rep);
    f.loadArr64(G.oHash, rep).get(hi).op(OP.i64_eq)
      .loadArr32(G.oEnds, rep).loadArr32(G.oStarts, rep).tee(rs).op(OP.i32_sub).get(len).op(OP.i32_eq)
      .op(OP.i32_and).if_();
    checkEq(oBase, () => {
      f.storeArr32(G.A, i, () => f.get(rep));
      f.storeArr32(G.cntA, rep, () => f.loadArr32(G.cntA, rep).i32(1).op(OP.i32_add));
      f.br(3);
    });
    f.end();
    f.get(slot).i32(1).op(OP.i32_add).get(hMask).op(OP.i32_and).set(slot);
    f.br(0).end().end();
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    // Lookup new lines
    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(m).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.nStarts, i).set(st);
    f.loadArr32(G.nEnds, i).get(st).op(OP.i32_sub).set(len);
    f.loadArr64(G.nHash, i).set(hi);
    f.get(hi).get(hi).i64(32n).op(OP.i64_shr_u).op(OP.i64_xor).op(OP.i32_wrap_i64).get(hMask).op(OP.i32_and).set(slot);
    f.i32(-3).set(found);
    f.block().loop();
    f.loadArr32(G.buckets, slot).tee(bk).op(OP.i32_eqz).br_if(1);
    f.get(bk).i32(1).op(OP.i32_sub).set(rep);
    f.loadArr64(G.oHash, rep).get(hi).op(OP.i64_eq)
      .loadArr32(G.oEnds, rep).loadArr32(G.oStarts, rep).tee(rs).op(OP.i32_sub).get(len).op(OP.i32_eq)
      .op(OP.i32_and).if_();
    checkEq(nBase, () => {
      f.get(rep).set(found);
      f.storeArr32(G.cntB, rep, () => f.loadArr32(G.cntB, rep).i32(1).op(OP.i32_add));
      f.storeArr32(G.posB, rep, () => f.get(i));
      f.br(3);
    });
    f.end();
    f.get(slot).i32(1).op(OP.i32_add).get(hMask).op(OP.i32_and).set(slot);
    f.br(0).end().end();
    f.storeArr32(G.B, i, () => f.get(found));
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();
  });

  // ------------------------------------------------------------------ 7. buildBoundsAndUB() -> i32 U
  addFunc(F.buildBoundsAndUB, [], [I32], (f) => {
    const n = f.loc(), m = f.loc(), i = f.loc(), acc = f.loc(), id = f.loc(), sc = f.loc();
    const tLen = f.loc(), j = f.loc(), lo = f.loc(), hi = f.loc(), mid = f.loc(), cur = f.loc(), k = f.loc();
    const kHint = f.loc(), partnerK = f.loc(), kr = f.loc(), kl = f.loc(), steps = f.loc();
    const pa = f.loc(), pb = f.loc(), minA = f.loc(), minB = f.loc(), gx = f.loc(), gy = f.loc(), row = f.loc(), nxt = f.loc();
    const U = f.loc(), g = f.loc(), x0 = f.loc(), y0 = f.loc(), gn = f.loc(), gm = f.loc();
    const maxGD = f.loc(), sA = f.loc(), sB = f.loc(), d = f.loc(), idx = f.loc(), diag = f.loc();
    const xr = f.loc(), xa = f.loc(), cr = f.loc(), ca = f.loc(), nx = f.loc(), ny = f.loc(), solved = f.loc(), tmp = f.loc();

    f.gget(G.n).set(n).gget(G.m).set(m);

    // 1. remDel[0..n]
    f.gget(G.seen).i32(0).get(n).i32(2).op(OP.i32_shl).memFill();
    f.i32(0).set(acc).get(n).i32(1).op(OP.i32_sub).set(i);
    f.block().loop();
    f.get(i).i32(0).op(OP.i32_lt_s).br_if(1);
    f.loadArr32(G.A, i).set(id);
    f.loadArr32(G.seen, id).i32(1).op(OP.i32_add).set(sc);
    f.storeArr32(G.seen, id, () => f.get(sc));
    f.get(sc).loadArr32(G.cntB, id).op(OP.i32_gt_s).if_().get(acc).i32(1).op(OP.i32_add).set(acc).end();
    f.storeArr32(G.remDel, i, () => f.get(acc));
    f.get(i).i32(1).op(OP.i32_sub).set(i);
    f.br(0).end().end();
    f.storeArr32(G.remDel, n, () => f.i32(0));

    // remIns[0..m]
    f.gget(G.seen).i32(0).get(n).i32(2).op(OP.i32_shl).memFill();
    f.i32(0).set(acc).get(m).i32(1).op(OP.i32_sub).set(i);
    f.block().loop();
    f.get(i).i32(0).op(OP.i32_lt_s).br_if(1);
    f.loadArr32(G.B, i).tee(id).i32(-3).op(OP.i32_eq).if_();
    f.get(acc).i32(1).op(OP.i32_add).set(acc);
    f.else_();
    f.loadArr32(G.seen, id).i32(1).op(OP.i32_add).set(sc);
    f.storeArr32(G.seen, id, () => f.get(sc));
    f.get(sc).loadArr32(G.cntA, id).op(OP.i32_gt_s).if_().get(acc).i32(1).op(OP.i32_add).set(acc).end();
    f.end();
    f.storeArr32(G.remIns, i, () => f.get(acc));
    f.get(i).i32(1).op(OP.i32_sub).set(i);
    f.br(0).end().end();
    f.storeArr32(G.remIns, m, () => f.i32(0));

    // 2. isUniq & Patience LIS
    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(n).op(OP.i32_ge_u).br_if(1);
    f.storeArr8(G.isUniq, i, () =>
      f.loadArr32(G.cntA, i).i32(1).op(OP.i32_eq).loadArr32(G.cntB, i).i32(1).op(OP.i32_eq).op(OP.i32_and)
    );
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    f.i32(0).set(tLen).i32(0).set(i);
    f.block().loop();
    f.get(i).get(n).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.A, i).set(id);
    f.loadArr8(G.isUniq, id).if_();
    f.loadArr32(G.posB, id).set(j);
    f.i32(0).set(lo).get(tLen).set(hi);
    f.block().loop();
    f.get(lo).get(hi).op(OP.i32_ge_s).br_if(1);
    f.get(lo).get(hi).op(OP.i32_add).i32(1).op(OP.i32_shr_u).set(mid);
    f.loadArr32(G.tailsVal, mid).get(j).op(OP.i32_lt_s).if_();
    f.get(mid).i32(1).op(OP.i32_add).set(lo);
    f.else_();
    f.get(mid).set(hi);
    f.end();
    f.br(0).end().end();
    f.storeArr32(G.tailsVal, lo, () => f.get(j));
    f.storeArr32(G.tailsA, lo, () => f.get(i));
    f.storeArr32(G.prevIdx, i, () => f.get(lo).i32(0).op(OP.i32_gt_s).if_(I32).get(lo).i32(1).op(OP.i32_sub).set(mid).loadArr32(G.tailsA, mid).else_().i32(-1).end());
    f.get(lo).get(tLen).op(OP.i32_eq).if_().get(tLen).i32(1).op(OP.i32_add).set(tLen).end();
    f.end();
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    f.gget(G.inLIS).i32(0).get(n).memFill();
    f.get(tLen).i32(0).op(OP.i32_gt_s).if_(I32).get(tLen).i32(1).op(OP.i32_sub).set(mid).loadArr32(G.tailsA, mid).else_().i32(-1).end().set(cur);
    f.get(tLen).set(k);
    f.block().loop();
    f.get(k).i32(1).op(OP.i32_lt_s).br_if(1);
    f.storeArr32(G.ancA, k, () => f.get(cur));
    f.storeArr32(G.ancB, k, () => f.loadArr32(G.A, cur).set(id).loadArr32(G.posB, id));
    f.storeArr8(G.inLIS, cur, () => f.i32(1));
    f.loadArr32(G.prevIdx, cur).set(cur);
    f.get(k).i32(1).op(OP.i32_sub).set(k);
    f.br(0).end().end();

    f.gget(G.ancA).i32(-1).store32(0);
    f.gget(G.ancB).i32(-1).store32(0);
    f.get(tLen).i32(1).op(OP.i32_add).set(mid);
    f.storeArr32(G.ancA, mid, () => f.get(n));
    f.storeArr32(G.ancB, mid, () => f.get(m));

    // 3. Disjoint crossing S_uniq pairs -> grid64 (65x65)
    f.gget(G.grid64).i32(0).i32(65 * 65 * 4).memFill();
    f.gget(G.usedLIS).i32(0).get(tLen).i32(2).op(OP.i32_add).memFill();
    f.i32(1).set(kHint).i32(0).set(i);
    f.block().loop();
    f.get(i).get(n).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.A, i).set(id);
    f.loadArr8(G.isUniq, id).loadArr8(G.inLIS, i).op(OP.i32_eqz).op(OP.i32_and).if_();
    f.loadArr32(G.posB, id).set(j);
    f.block().loop();
    f.get(kHint).get(tLen).op(OP.i32_gt_s).br_if(1);
    f.loadArr32(G.ancA, kHint).get(i).op(OP.i32_ge_s).br_if(1);
    f.get(kHint).i32(1).op(OP.i32_add).set(kHint);
    f.br(0).end().end();

    f.i32(-1).set(partnerK).get(kHint).set(kr).i32(0).set(steps);
    f.block().loop();
    f.get(kr).get(tLen).op(OP.i32_gt_s).get(steps).i32(64).op(OP.i32_ge_s).op(OP.i32_or).br_if(1);
    f.loadArr32(G.ancB, kr).get(j).op(OP.i32_ge_s).br_if(1);
    f.loadArr8(G.usedLIS, kr).op(OP.i32_eqz).if_().get(kr).set(partnerK).br(2).end();
    f.get(kr).i32(1).op(OP.i32_add).set(kr).get(steps).i32(1).op(OP.i32_add).set(steps);
    f.br(0).end().end();

    f.get(partnerK).i32(-1).op(OP.i32_eq).if_();
    f.get(kHint).i32(1).op(OP.i32_sub).set(kl).i32(0).set(steps);
    f.block().loop();
    f.get(kl).i32(1).op(OP.i32_lt_s).get(steps).i32(64).op(OP.i32_ge_s).op(OP.i32_or).br_if(1);
    f.loadArr32(G.ancB, kl).get(j).op(OP.i32_le_s).br_if(1);
    f.loadArr8(G.usedLIS, kl).op(OP.i32_eqz).if_().get(kl).set(partnerK).br(2).end();
    f.get(kl).i32(1).op(OP.i32_sub).set(kl).get(steps).i32(1).op(OP.i32_add).set(steps);
    f.br(0).end().end();
    f.end();

    f.get(partnerK).i32(-1).op(OP.i32_ne).if_();
    f.storeArr8(G.usedLIS, partnerK, () => f.i32(1));
    f.loadArr32(G.ancA, partnerK).set(pa);
    f.loadArr32(G.ancB, partnerK).set(pb);
    f.get(i).get(pa).get(i).get(pa).op(OP.i32_lt_s).op(OP.select).set(minA);
    f.get(j).get(pb).get(j).get(pb).op(OP.i32_lt_s).op(OP.select).set(minB);
    f.get(minA).i32(6).op(OP.i32_shl).get(n).op(OP.i32_div_u).set(gx);
    f.get(minB).i32(6).op(OP.i32_shl).get(m).op(OP.i32_div_u).set(gy);
    f.get(gx).i32(65).op(OP.i32_mul).get(gy).op(OP.i32_add).set(mid);
    f.storeArr32(G.grid64, mid, () => f.loadArr32(G.grid64, mid).i32(1).op(OP.i32_add));
    f.end();
    f.end();
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    // 2D suffix sums on grid64
    f.i32(63).set(gx);
    f.block().loop();
    f.get(gx).i32(0).op(OP.i32_lt_s).br_if(1);
    f.get(gx).i32(65).op(OP.i32_mul).set(row);
    f.get(row).i32(65).op(OP.i32_add).set(nxt);
    f.i32(63).set(gy);
    f.block().loop();
    f.get(gy).i32(0).op(OP.i32_lt_s).br_if(1);
    f.get(row).get(gy).op(OP.i32_add).set(mid);
    f.storeArr32(G.grid64, mid, () =>
      f.loadArr32(G.grid64, mid)
        .get(nxt).get(gy).op(OP.i32_add).set(cur).loadArr32(G.grid64, cur).op(OP.i32_add)
        .get(mid).i32(1).op(OP.i32_add).set(cur).loadArr32(G.grid64, cur).op(OP.i32_add)
        .get(nxt).get(gy).op(OP.i32_add).i32(1).op(OP.i32_add).set(cur).loadArr32(G.grid64, cur).op(OP.i32_sub)
    );
    f.get(gy).i32(1).op(OP.i32_sub).set(gy);
    f.br(0).end().end();
    f.get(gx).i32(1).op(OP.i32_sub).set(gx);
    f.br(0).end().end();

    // 4. Gap Myers for upper bound U
    f.i32(0).set(U).i32(0).set(g);
    f.block().loop();
    f.get(g).get(tLen).op(OP.i32_gt_s).br_if(1);
    f.loadArr32(G.ancA, g).i32(1).op(OP.i32_add).set(x0);
    f.loadArr32(G.ancB, g).i32(1).op(OP.i32_add).set(y0);
    f.get(g).i32(1).op(OP.i32_add).set(mid);
    f.loadArr32(G.ancA, mid).get(x0).op(OP.i32_sub).set(gn);
    f.loadArr32(G.ancB, mid).get(y0).op(OP.i32_sub).set(gm);

    f.block().loop();
    f.get(gn).i32(0).op(OP.i32_le_s).get(gm).i32(0).op(OP.i32_le_s).op(OP.i32_or).br_if(1);
    f.loadArr32(G.A, x0).loadArr32(G.B, y0).op(OP.i32_ne).br_if(1);
    f.get(x0).i32(1).op(OP.i32_add).set(x0);
    f.get(y0).i32(1).op(OP.i32_add).set(y0);
    f.get(gn).i32(1).op(OP.i32_sub).set(gn);
    f.get(gm).i32(1).op(OP.i32_sub).set(gm);
    f.br(0).end().end();

    f.block().loop();
    f.get(gn).i32(0).op(OP.i32_le_s).get(gm).i32(0).op(OP.i32_le_s).op(OP.i32_or).br_if(1);
    f.get(x0).get(gn).op(OP.i32_add).i32(1).op(OP.i32_sub).set(cur);
    f.get(y0).get(gm).op(OP.i32_add).i32(1).op(OP.i32_sub).set(mid);
    f.loadArr32(G.A, cur).loadArr32(G.B, mid).op(OP.i32_ne).br_if(1);
    f.get(gn).i32(1).op(OP.i32_sub).set(gn);
    f.get(gm).i32(1).op(OP.i32_sub).set(gm);
    f.br(0).end().end();

    f.block(); // continue block for g
    f.get(gn).op(OP.i32_eqz).if_().get(U).get(gm).op(OP.i32_add).set(U).br(1).end();
    f.get(gm).op(OP.i32_eqz).if_().get(U).get(gn).op(OP.i32_add).set(U).br(1).end();

    f.get(gn).get(gm).op(OP.i32_add).set(mid);
    f.i32(256).get(mid).i32(256).get(mid).op(OP.i32_lt_s).op(OP.select).set(maxGD);
    f.get(x0).get(gn).op(OP.i32_add).set(cur).loadArr32(G.A, cur).set(sA);
    f.get(y0).get(gm).op(OP.i32_add).set(mid).loadArr32(G.B, mid).set(sB);
    f.storeArr32(G.A, cur, () => f.i32(-1));
    f.storeArr32(G.B, mid, () => f.i32(-2));

    f.i32(0).set(gx);
    f.block().loop();
    f.get(x0).get(gx).op(OP.i32_add).set(lo);
    f.get(y0).get(gx).op(OP.i32_add).set(hi);
    f.loadArr32(G.A, lo).loadArr32(G.B, hi).op(OP.i32_ne).br_if(1);
    f.get(gx).i32(1).op(OP.i32_add).set(gx);
    f.br(0).end().end();
    f.gget(G.gVp).get(gx).store32(0);

    f.i32(0).set(solved).i32(1).set(d);
    f.block().loop();
    f.get(d).get(maxGD).op(OP.i32_gt_s).br_if(1);
    f.i32(0).set(idx).i32(0).get(d).op(OP.i32_sub).set(diag);
    f.block().loop();
    f.get(idx).get(d).op(OP.i32_gt_s).br_if(1);
    f.get(idx).i32(0).op(OP.i32_gt_s).if_(I32).get(idx).i32(1).op(OP.i32_sub).set(lo).loadArr32(G.gVp, lo).else_().i32(-2).end().set(xr);
    f.get(idx).get(d).op(OP.i32_lt_s).if_(I32).loadArr32(G.gVp, idx).else_().i32(-2).end().set(xa);
    f.get(xr).i32(0).op(OP.i32_ge_s).get(xr).get(gn).op(OP.i32_lt_s).op(OP.i32_and).set(cr);
    f.get(xa).i32(0).op(OP.i32_ge_s).get(xa).get(diag).op(OP.i32_sub).i32(1).op(OP.i32_sub).get(gm).op(OP.i32_lt_s).op(OP.i32_and).set(ca);
    f.get(cr).get(ca).op(OP.i32_eqz).get(xr).i32(1).op(OP.i32_add).get(xa).op(OP.i32_ge_s).op(OP.i32_or).op(OP.i32_and)
      .if_(I32).get(xr).i32(1).op(OP.i32_add)
      .else_().get(ca).if_(I32).get(xa).else_().i32(-2).end().end().set(nx);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.storeArr32(G.gVc, idx, () => f.i32(-2));
    f.else_();
    f.get(nx).get(diag).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.get(x0).get(nx).op(OP.i32_add).set(lo);
    f.get(y0).get(ny).op(OP.i32_add).set(hi);
    f.loadArr32(G.A, lo).loadArr32(G.B, hi).op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(gn).op(OP.i32_eq).get(ny).get(gm).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(U).get(d).op(OP.i32_add).set(U);
    f.i32(1).set(solved);
    f.br(5);
    f.end();
    f.storeArr32(G.gVc, idx, () => f.get(nx));
    f.end();
    f.get(idx).i32(1).op(OP.i32_add).set(idx);
    f.get(diag).i32(2).op(OP.i32_add).set(diag);
    f.br(0).end().end();
    f.gget(G.gVp).set(tmp).gget(G.gVc).gset(G.gVp).get(tmp).gset(G.gVc);
    f.get(d).i32(1).op(OP.i32_add).set(d);
    f.br(0).end().end();

    f.storeArr32(G.A, cur, () => f.get(sA));
    f.storeArr32(G.B, mid, () => f.get(sB));
    f.get(solved).op(OP.i32_eqz).if_().get(U).get(gn).op(OP.i32_add).get(gm).op(OP.i32_add).set(U).end();
    f.end(); // continue block

    f.get(g).i32(1).op(OP.i32_add).set(g);
    f.br(0).end().end();
    f.get(U).tee(lo).gset(G.U);
    f.get(lo);
  });

  // ------------------------------------------------------------------ 8. myersForward()
  addFunc(F.myersForward, [], [], (f) => {
    const n = f.loc(), m = f.loc(), U = f.loc(), delta = f.loc(), ptr = f.loc();
    const bShift = f.loc(), bStep = f.loc(), bMask = f.loc(), nCkpts = f.loc();
    const x0 = f.loc(), kLo = f.loc(), kHi = f.loc(), hitBound = f.loc(), d = f.loc();
    const remD = f.loc(), lim1 = f.loc(), lim2 = f.loc(), loK = f.loc(), hiK = f.loc(), iLo = f.loc(), iHi = f.loc();
    const idx = f.loc(), k = f.loc(), endIdx = f.loc(), xRem = f.loc(), xAdd = f.loc(), nx = f.loc(), ny = f.loc();
    const canRem = f.loc(), canAdd = f.loc(), qx = f.loc(), qy = f.loc(), cc = f.loc(), tmp = f.loc();
    const cCount = f.loc(), metaPtr = f.loc(), bytesNeed = f.loc();

    f.gget(G.n).set(n).gget(G.m).set(m).gget(G.U).set(U);
    f.get(n).get(m).op(OP.i32_sub).set(delta);
    f.get(U).i32(8192).op(OP.i32_le_s).if_();
    f.i32(5).set(bShift).i32(32).set(bStep).i32(31).set(bMask);
    f.else_();
    f.i32(7).set(bShift).i32(128).set(bStep).i32(127).set(bMask);
    f.end();
    f.get(bShift).gset(G.bShift).get(bStep).gset(G.bStep).get(bMask).gset(G.bMask);

    // Arena for Vp, Vc, repBuf, ckptMeta, ckptData
    f.gget(G.arenaPtr).set(ptr);
    f.get(ptr).gset(G.Vp);
    f.get(ptr).get(U).i32(8).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.Vc);
    f.get(ptr).get(U).i32(8).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.repBuf);
    f.get(ptr).get(bStep).i32(1).op(OP.i32_add).get(bStep).i32(4).op(OP.i32_add).op(OP.i32_mul).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(U).get(bShift).op(OP.i32_shr_u).i32(2).op(OP.i32_add).set(nCkpts);
    f.get(ptr).gset(G.ckptMeta);
    f.get(ptr).get(nCkpts).i32(4).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.ckptData);
    f.get(ptr).gset(G.ckptDataPtr);
    f.get(ptr).i32(1048576).op(OP.i32_add).tee(tmp).gset(G.ckptCap);
    f.get(tmp).call(F.ensureMem);

    // Sentinels A[n]=-1, B[m]=-2
    f.storeArr32(G.A, n, () => f.i32(-1));
    f.storeArr32(G.B, m, () => f.i32(-2));
    f.gget(G.Vp).i32(-2).get(U).i32(8).op(OP.i32_add).i32(2).op(OP.i32_shl).memFill();
    f.gget(G.Vc).i32(-2).get(U).i32(8).op(OP.i32_add).i32(2).op(OP.i32_shl).memFill();

    f.i32(0).set(x0);
    f.block().loop();
    f.loadArr32(G.A, x0).loadArr32(G.B, x0).op(OP.i32_ne).br_if(1);
    f.get(x0).i32(1).op(OP.i32_add).set(x0);
    f.br(0).end().end();
    f.gget(G.Vp).get(x0).store32(0);

    // Save checkpoint 0: meta = (iLo=0, loK=0, hiK=0, dataPtr)
    f.gget(G.ckptMeta).set(metaPtr);
    f.get(metaPtr).i32(0).store32(0);
    f.get(metaPtr).i32(0).store32(4);
    f.get(metaPtr).i32(0).store32(8);
    f.get(metaPtr).gget(G.ckptDataPtr).store32(12);
    f.gget(G.ckptDataPtr).get(x0).store32(0);
    f.gget(G.ckptDataPtr).i32(4).op(OP.i32_add).gset(G.ckptDataPtr);
    f.i32(1).set(cCount);

    f.i32(0).gset(G.ansD).i32(0).gset(G.ansK);
    f.i32(0).set(kLo).i32(0).set(kHi);
    f.get(x0).get(n).op(OP.i32_ge_s).get(x0).get(m).op(OP.i32_ge_s).op(OP.i32_or).set(hitBound);

    f.get(x0).get(n).op(OP.i32_lt_s).get(x0).get(m).op(OP.i32_lt_s).op(OP.i32_or).if_();
    f.i32(1).set(d);
    f.block(); // outer break block
    f.loop();
    f.get(d).get(U).op(OP.i32_gt_s).br_if(1);
    f.get(U).get(d).op(OP.i32_sub).set(remD);
    f.get(remD).get(delta).op(OP.i32_sub).set(lim1);
    f.get(remD).get(delta).op(OP.i32_add).set(lim2);
    f.get(kLo).i32(1).op(OP.i32_sub).set(nx);
    f.i32(0).get(lim1).op(OP.i32_sub).set(ny);
    f.get(nx).get(ny).get(nx).get(ny).op(OP.i32_gt_s).op(OP.select).set(loK);
    f.get(kHi).i32(1).op(OP.i32_add).set(nx);
    f.get(nx).get(lim2).get(nx).get(lim2).op(OP.i32_lt_s).op(OP.select).set(hiK);
    f.get(loK).get(d).op(OP.i32_xor).i32(1).op(OP.i32_and).if_().get(loK).i32(1).op(OP.i32_add).set(loK).end();
    f.get(hiK).get(d).op(OP.i32_xor).i32(1).op(OP.i32_and).if_().get(hiK).i32(1).op(OP.i32_sub).set(hiK).end();
    f.get(loK).get(d).op(OP.i32_add).i32(1).op(OP.i32_shr_s).set(iLo);
    f.get(hiK).get(d).op(OP.i32_add).i32(1).op(OP.i32_shr_s).set(iHi);
    f.get(iLo).i32(0).op(OP.i32_gt_s).if_().get(iLo).i32(1).op(OP.i32_sub).set(tmp).storeArr32(G.Vc, tmp, () => f.i32(-2)).end();
    f.get(iHi).i32(1).op(OP.i32_add).set(tmp);
    f.storeArr32(G.Vc, tmp, () => f.i32(-2));

    f.get(hitBound).op(OP.i32_eqz).if_();
    f.get(iLo).set(idx).get(loK).set(k);
    f.get(idx).op(OP.i32_eqz).if_();
    f.gget(G.Vp).load32(0).set(nx);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.gget(G.Vc).i32(-2).store32(0);
    f.else_();
    f.get(nx).get(k).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.loadArr32(G.A, nx).loadArr32(G.B, ny).op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_ge_s).get(ny).get(m).op(OP.i32_ge_s).op(OP.i32_or).if_();
    f.i32(1).set(hitBound);
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(k).gset(G.ansK).br(6);
    f.end();
    f.end();
    f.gget(G.Vc).get(nx).store32(0);
    f.end();
    f.i32(1).set(idx).get(k).i32(2).op(OP.i32_add).set(k);
    f.end();

    f.get(iHi).get(d).get(iHi).get(d).op(OP.i32_lt_s).op(OP.select).set(endIdx);
    f.get(endIdx).get(d).op(OP.i32_eq).if_().get(d).i32(1).op(OP.i32_sub).set(endIdx).end();
    f.get(idx).i32(1).op(OP.i32_sub).set(tmp);
    f.loadArr32(G.Vp, tmp).set(xRem);

    f.block().loop();
    f.get(idx).get(endIdx).op(OP.i32_gt_s).br_if(1);
    f.loadArr32(G.Vp, idx).set(xAdd);
    f.get(xRem).i32(0).op(OP.i32_ge_s).get(xRem).i32(1).op(OP.i32_add).tee(tmp).get(xAdd).op(OP.i32_ge_s).op(OP.i32_and)
      .if_(I32).get(tmp).else_().get(xAdd).end().set(nx);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.storeArr32(G.Vc, idx, () => f.i32(-2));
    f.else_();
    f.get(nx).get(k).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.loadArr32(G.A, nx).loadArr32(G.B, ny).op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_ge_s).get(ny).get(m).op(OP.i32_ge_s).op(OP.i32_or).if_();
    f.i32(1).set(hitBound);
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(k).gset(G.ansK).br(7);
    f.end();
    f.end();
    f.storeArr32(G.Vc, idx, () => f.get(nx));
    f.end();
    f.get(xAdd).set(xRem);
    f.get(idx).i32(1).op(OP.i32_add).set(idx);
    f.get(k).i32(2).op(OP.i32_add).set(k);
    f.br(0).end().end();

    f.get(iHi).get(d).op(OP.i32_eq).if_();
    f.get(xRem).i32(0).op(OP.i32_lt_s).if_();
    f.storeArr32(G.Vc, d, () => f.i32(-2));
    f.else_();
    f.get(xRem).i32(1).op(OP.i32_add).set(nx);
    f.get(nx).get(d).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.loadArr32(G.A, nx).loadArr32(G.B, ny).op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_ge_s).get(ny).get(m).op(OP.i32_ge_s).op(OP.i32_or).if_();
    f.i32(1).set(hitBound);
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(d).gset(G.ansK).br(6);
    f.end();
    f.end();
    f.storeArr32(G.Vc, d, () => f.get(nx));
    f.end();
    f.end();

    f.else_();
    // hitBound branch
    f.get(iLo).set(idx).get(loK).set(k);
    f.block().loop();
    f.get(idx).get(iHi).op(OP.i32_gt_s).br_if(1);
    f.get(idx).i32(0).op(OP.i32_gt_s).if_(I32).get(idx).i32(1).op(OP.i32_sub).set(tmp).loadArr32(G.Vp, tmp).else_().i32(-2).end().set(xRem);
    f.get(idx).get(d).op(OP.i32_lt_s).if_(I32).loadArr32(G.Vp, idx).else_().i32(-2).end().set(xAdd);
    f.get(xRem).i32(0).op(OP.i32_ge_s).get(xRem).get(n).op(OP.i32_lt_s).op(OP.i32_and).set(canRem);
    f.get(xAdd).i32(0).op(OP.i32_ge_s).get(xAdd).get(k).op(OP.i32_sub).i32(1).op(OP.i32_sub).get(m).op(OP.i32_lt_s).op(OP.i32_and).set(canAdd);
    f.get(canRem).get(canAdd).op(OP.i32_eqz).get(xRem).i32(1).op(OP.i32_add).get(xAdd).op(OP.i32_ge_s).op(OP.i32_or).op(OP.i32_and)
      .if_(I32).get(xRem).i32(1).op(OP.i32_add)
      .else_().get(canAdd).if_(I32).get(xAdd).else_().i32(-2).end().end().set(nx);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.storeArr32(G.Vc, idx, () => f.i32(-2));
    f.else_();
    f.get(nx).get(k).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.loadArr32(G.A, nx).loadArr32(G.B, ny).op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(k).gset(G.ansK).br(6);
    f.end();
    f.storeArr32(G.Vc, idx, () => f.get(nx));
    f.end();
    f.get(idx).i32(1).op(OP.i32_add).set(idx);
    f.get(k).i32(2).op(OP.i32_add).set(k);
    f.br(0).end().end();
    f.end(); // end hitBound else

    // Outer edge A* pruning
    const emitTrimSide = (idxL, kL, stepIdx, stepK, cmpOp) => {
      f.block().loop();
      f.get(iLo).get(iHi).op(OP.i32_gt_s).br_if(1);
      f.loadArr32(G.Vc, idxL).set(nx);
      f.get(nx).i32(0).op(OP.i32_ge_s).if_();
      f.get(nx).get(kL).op(OP.i32_sub).set(ny);
      f.get(nx).i32(6).op(OP.i32_shl).get(n).op(OP.i32_add).i32(1).op(OP.i32_sub).get(n).op(OP.i32_div_u).set(qx);
      f.get(ny).i32(6).op(OP.i32_shl).get(m).op(OP.i32_add).i32(1).op(OP.i32_sub).get(m).op(OP.i32_div_u).set(qy);
      f.get(qx).i32(65).op(OP.i32_mul).get(qy).op(OP.i32_add).set(tmp);
      f.loadArr32(G.grid64, tmp).set(cc);
      f.loadArr32(G.remIns, ny).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl).get(lim1).get(kL).op(OP.i32_add).op(OP.i32_le_s)
        .loadArr32(G.remDel, nx).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl).get(lim2).get(kL).op(OP.i32_sub).op(OP.i32_le_s)
        .op(OP.i32_and).br_if(2);
      f.storeArr32(G.Vc, idxL, () => f.i32(-2));
      f.end();
      f.get(idxL).i32(stepIdx).op(OP.i32_add).set(idxL);
      f.get(kL).i32(stepK).op(OP.i32_add).set(kL);
      f.br(0).end().end();
    };
    emitTrimSide(iLo, loK, 1, 2);
    emitTrimSide(iHi, hiK, -1, -2);

    f.get(loK).set(kLo).get(hiK).set(kHi);
    f.gget(G.Vp).set(tmp).gget(G.Vc).gset(G.Vp).get(tmp).gset(G.Vc);

    f.get(d).get(bMask).op(OP.i32_and).op(OP.i32_eqz).if_();
    f.get(iHi).get(iLo).op(OP.i32_sub).i32(1).op(OP.i32_add).i32(2).op(OP.i32_shl).set(bytesNeed);
    f.get(bytesNeed).i32(0).op(OP.i32_lt_s).if_().i32(0).set(bytesNeed).end();
    f.gget(G.ckptDataPtr).get(bytesNeed).op(OP.i32_add).gget(G.ckptCap).op(OP.i32_gt_u).if_();
    f.gget(G.ckptDataPtr).get(bytesNeed).op(OP.i32_add).i32(1048576).op(OP.i32_add).tee(tmp).gset(G.ckptCap);
    f.get(tmp).call(F.ensureMem);
    f.end();
    f.gget(G.ckptMeta).get(cCount).i32(4).op(OP.i32_shl).op(OP.i32_add).set(metaPtr);
    f.get(metaPtr).get(iLo).store32(0);
    f.get(metaPtr).get(loK).store32(4);
    f.get(metaPtr).get(hiK).store32(8);
    f.get(metaPtr).gget(G.ckptDataPtr).store32(12);
    f.get(bytesNeed).i32(0).op(OP.i32_gt_s).if_();
    f.gget(G.ckptDataPtr).arrPtr32(G.Vp, iLo).get(bytesNeed).memCopy();
    f.gget(G.ckptDataPtr).get(bytesNeed).op(OP.i32_add).gset(G.ckptDataPtr);
    f.end();
    f.get(cCount).i32(1).op(OP.i32_add).set(cCount);
    f.end();

    f.get(d).i32(1).op(OP.i32_add).set(d);
    f.br(0).end().end();
    f.end(); // if x0<n||x0<m
  });

  // ------------------------------------------------------------------ 9. replayPath()
  addFunc(F.replayPath, [], [], (f) => {
    const n = f.loc(), m = f.loc(), U = f.loc(), delta = f.loc(), ansD = f.loc(), ptr = f.loc();
    const bShift = f.loc(), bStep = f.loc(), stride = f.loc(), opLen = f.loc();
    const curD = f.loc(), curK = f.loc(), curX = f.loc();
    const bIdx = f.loc(), d0 = f.loc(), d1 = f.loc(), span = f.loc();
    const metaPtr = f.loc(), ckData = f.loc(), ckILo = f.loc(), fLo0 = f.loc(), fHi0 = f.loc();
    const baseK0 = f.loc(), rLo0 = f.loc(), rHi0 = f.loc(), k = f.loc();
    const pLo = f.loc(), pHi = f.loc(), s = f.loc(), d = f.loc(), remD = f.loc(), lim1 = f.loc(), lim2 = f.loc();
    const wLo = f.loc(), wHi = f.loc(), rLo = f.loc(), rHi = f.loc(), prevRow = f.loc(), curRow = f.loc(), shiftBase = f.loc();
    const cILo = f.loc(), cIHi = f.loc(), col = f.loc(), xRem = f.loc(), xAdd = f.loc(), canRem = f.loc(), canAdd = f.loc(), nx = f.loc(), ny = f.loc();
    const qx = f.loc(), qy = f.loc(), cc = f.loc(), tmp = f.loc();
    const traceX = f.loc(), traceK = f.loc(), startX = f.loc(), opK = f.loc(), nextK = f.loc(), prevX = f.loc(), keep = f.loc();

    f.gget(G.n).set(n).gget(G.m).set(m).gget(G.U).set(U).gget(G.ansD).set(ansD);
    f.get(n).get(m).op(OP.i32_sub).set(delta);
    f.gget(G.bShift).set(bShift).gget(G.bStep).set(bStep);
    f.get(bStep).i32(4).op(OP.i32_add).set(stride);

    // Arena for revKind, revCount, changes, hunks
    f.gget(G.ckptDataPtr).i32(7).op(OP.i32_add).i32(-8).op(OP.i32_and).set(ptr);
    f.get(ptr).gset(G.revKind);
    f.get(ptr).get(ansD).i32(1).op(OP.i32_shl).i32(16).op(OP.i32_add).i32(7).op(OP.i32_add).i32(-8).op(OP.i32_and).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.revCount);
    f.get(ptr).get(ansD).i32(1).op(OP.i32_shl).i32(8).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.arenaPtr);
    f.get(ptr).i32(64).op(OP.i32_add).call(F.ensureMem);

    const emitPushOp = (kindExpr, cntExpr) => {
      f.get(opLen).i32(0).op(OP.i32_gt_s)
        .if_(I32).get(opLen).i32(1).op(OP.i32_sub).set(tmp).loadArr8(G.revKind, tmp); kindExpr(); f.op(OP.i32_eq).else_().i32(0).end()
        .if_();
      f.get(opLen).i32(1).op(OP.i32_sub).set(tmp);
      f.storeArr32(G.revCount, tmp, () => { f.loadArr32(G.revCount, tmp); cntExpr(); f.op(OP.i32_add); });
      f.else_();
      f.storeArr8(G.revKind, opLen, kindExpr);
      f.storeArr32(G.revCount, opLen, cntExpr);
      f.get(opLen).i32(1).op(OP.i32_add).set(opLen);
      f.end();
    };

    f.i32(0).set(opLen).get(ansD).set(curD).gget(G.ansK).set(curK).get(n).set(curX);
    f.block().loop();
    f.get(curD).i32(0).op(OP.i32_le_s).br_if(1);
    f.get(curD).i32(1).op(OP.i32_sub).get(bShift).op(OP.i32_shr_u).set(bIdx);
    f.get(bIdx).get(bShift).op(OP.i32_shl).set(d0);
    f.get(curD).get(d0).op(OP.i32_sub).set(span);

    f.gget(G.ckptMeta).get(bIdx).i32(4).op(OP.i32_shl).op(OP.i32_add).set(metaPtr);
    f.get(metaPtr).load32(0).set(ckILo);
    f.get(metaPtr).load32(4).set(fLo0);
    f.get(metaPtr).load32(8).set(fHi0);
    f.get(metaPtr).load32(12).set(ckData);

    f.get(curK).get(span).op(OP.i32_sub).set(baseK0);
    f.get(fLo0).get(baseK0).get(fLo0).get(baseK0).op(OP.i32_gt_s).op(OP.select).set(rLo0);
    f.get(curK).get(span).op(OP.i32_add).set(tmp);
    f.get(fHi0).get(tmp).get(fHi0).get(tmp).op(OP.i32_lt_s).op(OP.select).set(rHi0);

    f.gget(G.repBuf).i32(-2).get(span).i32(3).op(OP.i32_add).i32(2).op(OP.i32_shl).memFill();
    f.get(rLo0).set(k);
    f.block().loop();
    f.get(k).get(rHi0).op(OP.i32_gt_s).br_if(1);
    f.get(k).get(baseK0).op(OP.i32_sub).i32(1).op(OP.i32_shr_s).set(col);
    f.get(k).get(d0).op(OP.i32_add).i32(1).op(OP.i32_shr_s).get(ckILo).op(OP.i32_sub).set(tmp);
    f.storeArr32(G.repBuf, col, () => f.get(ckData).get(tmp).i32(2).op(OP.i32_shl).op(OP.i32_add).load32());
    f.get(k).i32(2).op(OP.i32_add).set(k);
    f.br(0).end().end();

    f.get(rLo0).set(pLo).get(rHi0).set(pHi).i32(1).set(s);
    f.block().loop();
    f.get(s).get(span).op(OP.i32_gt_s).br_if(1);
    f.get(d0).get(s).op(OP.i32_add).set(d);
    f.get(U).get(d).op(OP.i32_sub).set(remD);
    f.get(remD).get(delta).op(OP.i32_sub).set(lim1);
    f.get(remD).get(delta).op(OP.i32_add).set(lim2);
    f.get(curK).get(span).get(s).op(OP.i32_sub).op(OP.i32_sub).set(wLo);
    f.get(curK).get(span).get(s).op(OP.i32_sub).op(OP.i32_add).set(wHi);

    f.get(pLo).i32(1).op(OP.i32_sub).set(nx);
    f.i32(0).get(lim1).op(OP.i32_sub).set(ny);
    f.get(nx).get(ny).get(nx).get(ny).op(OP.i32_gt_s).op(OP.select).set(rLo);
    f.get(wLo).get(rLo).get(wLo).get(rLo).op(OP.i32_gt_s).op(OP.select).set(rLo);

    f.get(pHi).i32(1).op(OP.i32_add).set(nx);
    f.get(nx).get(lim2).get(nx).get(lim2).op(OP.i32_lt_s).op(OP.select).set(rHi);
    f.get(wHi).get(rHi).get(wHi).get(rHi).op(OP.i32_lt_s).op(OP.select).set(rHi);

    f.get(rLo).get(d).op(OP.i32_xor).i32(1).op(OP.i32_and).if_().get(rLo).i32(1).op(OP.i32_add).set(rLo).end();
    f.get(rHi).get(d).op(OP.i32_xor).i32(1).op(OP.i32_and).if_().get(rHi).i32(1).op(OP.i32_sub).set(rHi).end();

    f.get(s).i32(1).op(OP.i32_sub).get(stride).op(OP.i32_mul).set(prevRow);
    f.get(s).get(stride).op(OP.i32_mul).set(curRow);
    f.get(baseK0).get(s).op(OP.i32_sub).set(shiftBase);
    f.get(rLo).get(shiftBase).op(OP.i32_sub).i32(1).op(OP.i32_shr_s).set(cILo);
    f.get(rHi).get(shiftBase).op(OP.i32_sub).i32(1).op(OP.i32_shr_s).set(cIHi);
    f.get(cILo).i32(0).op(OP.i32_gt_s).if_().get(curRow).get(cILo).op(OP.i32_add).i32(1).op(OP.i32_sub).set(tmp).storeArr32(G.repBuf, tmp, () => f.i32(-2)).end();
    f.get(curRow).get(cIHi).op(OP.i32_add).i32(1).op(OP.i32_add).set(tmp);
    f.storeArr32(G.repBuf, tmp, () => f.i32(-2));

    f.get(rLo).set(k);
    f.block().loop();
    f.get(k).get(rHi).op(OP.i32_gt_s).br_if(1);
    f.get(k).get(shiftBase).op(OP.i32_sub).i32(1).op(OP.i32_shr_s).set(col);
    f.get(k).i32(1).op(OP.i32_sub).tee(tmp).get(pLo).op(OP.i32_ge_s).get(tmp).get(pHi).op(OP.i32_le_s).op(OP.i32_and)
      .if_(I32).get(prevRow).get(col).op(OP.i32_add).i32(1).op(OP.i32_sub).set(tmp).loadArr32(G.repBuf, tmp).else_().i32(-2).end().set(xRem);
    f.get(k).i32(1).op(OP.i32_add).tee(tmp).get(pLo).op(OP.i32_ge_s).get(tmp).get(pHi).op(OP.i32_le_s).op(OP.i32_and)
      .if_(I32).get(prevRow).get(col).op(OP.i32_add).set(tmp).loadArr32(G.repBuf, tmp).else_().i32(-2).end().set(xAdd);

    f.get(xRem).i32(0).op(OP.i32_ge_s).get(xRem).get(n).op(OP.i32_lt_s).op(OP.i32_and).set(canRem);
    f.get(xAdd).i32(0).op(OP.i32_ge_s).get(xAdd).get(k).op(OP.i32_sub).i32(1).op(OP.i32_sub).get(m).op(OP.i32_lt_s).op(OP.i32_and).set(canAdd);
    f.get(canRem).get(canAdd).op(OP.i32_eqz).get(xRem).i32(1).op(OP.i32_add).get(xAdd).op(OP.i32_ge_s).op(OP.i32_or).op(OP.i32_and)
      .if_(I32).get(xRem).i32(1).op(OP.i32_add)
      .else_().get(canAdd).if_(I32).get(xAdd).else_().i32(-2).end().end().set(nx);

    f.get(curRow).get(col).op(OP.i32_add).set(tmp);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.storeArr32(G.repBuf, tmp, () => f.i32(-2));
    f.else_();
    f.get(nx).get(k).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.loadArr32(G.A, nx).loadArr32(G.B, ny).op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.storeArr32(G.repBuf, tmp, () => f.get(nx));
    f.end();
    f.get(k).i32(2).op(OP.i32_add).set(k);
    f.br(0).end().end();

    f.get(s).get(span).op(OP.i32_lt_s).if_();
    const emitRepTrim = (colL, kL, stepCol, stepK) => {
      f.block().loop();
      f.get(cILo).get(cIHi).op(OP.i32_gt_s).br_if(1);
      f.get(curRow).get(colL).op(OP.i32_add).set(tmp).loadArr32(G.repBuf, tmp).set(nx);
      f.get(nx).i32(0).op(OP.i32_ge_s).if_();
      f.get(nx).get(kL).op(OP.i32_sub).set(ny);
      f.get(nx).i32(6).op(OP.i32_shl).get(n).op(OP.i32_add).i32(1).op(OP.i32_sub).get(n).op(OP.i32_div_u).set(qx);
      f.get(ny).i32(6).op(OP.i32_shl).get(m).op(OP.i32_add).i32(1).op(OP.i32_sub).get(m).op(OP.i32_div_u).set(qy);
      f.get(qx).i32(65).op(OP.i32_mul).get(qy).op(OP.i32_add).set(cc);
      f.loadArr32(G.grid64, cc).set(cc);
      f.loadArr32(G.remIns, ny).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl).get(lim1).get(kL).op(OP.i32_add).op(OP.i32_le_s)
        .loadArr32(G.remDel, nx).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl).get(lim2).get(kL).op(OP.i32_sub).op(OP.i32_le_s)
        .op(OP.i32_and).br_if(2);
      f.storeArr32(G.repBuf, tmp, () => f.i32(-2));
      f.end();
      f.get(colL).i32(stepCol).op(OP.i32_add).set(colL);
      f.get(kL).i32(stepK).op(OP.i32_add).set(kL);
      f.br(0).end().end();
    };
    emitRepTrim(cILo, rLo, 1, 2);
    emitRepTrim(cIHi, rHi, -1, -2);
    f.end();

    f.get(rLo).set(pLo).get(rHi).set(pHi);
    f.get(s).i32(1).op(OP.i32_add).set(s);
    f.br(0).end().end();

    // Trace backwards from s = span down to 1
    f.get(curX).set(traceX).get(curK).set(traceK).get(span).set(s);
    f.block().loop();
    f.get(s).i32(1).op(OP.i32_lt_s).br_if(1);
    f.get(s).i32(1).op(OP.i32_sub).get(stride).op(OP.i32_mul).set(prevRow);
    f.get(baseK0).get(s).op(OP.i32_sub).set(shiftBase);
    f.get(traceK).get(shiftBase).op(OP.i32_sub).i32(1).op(OP.i32_shr_s).set(col);
    f.get(col).i32(0).op(OP.i32_gt_s).if_(I32).get(prevRow).get(col).op(OP.i32_add).i32(1).op(OP.i32_sub).set(tmp).loadArr32(G.repBuf, tmp).else_().i32(-2).end().set(xRem);
    f.get(prevRow).get(col).op(OP.i32_add).set(tmp).loadArr32(G.repBuf, tmp).set(xAdd);
    f.get(xRem).i32(0).op(OP.i32_ge_s).get(xRem).get(n).op(OP.i32_lt_s).op(OP.i32_and).set(canRem);
    f.get(xAdd).i32(0).op(OP.i32_ge_s).get(xAdd).get(traceK).op(OP.i32_sub).i32(1).op(OP.i32_sub).get(m).op(OP.i32_lt_s).op(OP.i32_and).set(canAdd);

    f.get(canRem).get(canAdd).op(OP.i32_eqz).get(xRem).i32(1).op(OP.i32_add).get(xAdd).op(OP.i32_ge_s).op(OP.i32_or).op(OP.i32_and).if_();
    f.get(xRem).i32(1).op(OP.i32_add).set(startX).i32(DELETE).set(opK).get(traceK).i32(1).op(OP.i32_sub).set(nextK).get(xRem).set(prevX);
    f.else_();
    f.get(xAdd).set(startX).i32(INSERT).set(opK).get(traceK).i32(1).op(OP.i32_add).set(nextK).get(xAdd).set(prevX);
    f.end();

    f.get(traceX).get(startX).op(OP.i32_sub).tee(keep).i32(0).op(OP.i32_gt_s).if_();
    emitPushOp(() => f.i32(KEEP), () => f.get(keep));
    f.end();
    emitPushOp(() => f.get(opK), () => f.i32(1));
    f.get(nextK).set(traceK).get(prevX).set(traceX);
    f.get(s).i32(1).op(OP.i32_sub).set(s);
    f.br(0).end().end();

    f.get(d0).set(curD).get(traceK).set(curK).get(traceX).set(curX);
    f.br(0).end().end();

    f.get(curX).i32(0).op(OP.i32_gt_s).if_();
    emitPushOp(() => f.i32(KEEP), () => f.get(curX));
    f.end();
    f.get(opLen).gset(G.opLen);
  });

  // ------------------------------------------------------------------ 10. buildChangesAndHunks()
  addFunc(F.buildChangesAndHunks, [], [], (f) => {
    const opLen = f.loc(), ptr = f.loc(), idx = f.loc(), kind = f.loc(), cnt = f.loc();
    const o = f.loc(), p = f.loc(), del = f.loc(), ins = f.loc(), nc = f.loc(), last = f.loc();
    const nh = f.loc(), i = f.loc(), prev = f.loc(), tmp = f.loc();

    f.gget(G.opLen).set(opLen);
    f.gget(G.arenaPtr).set(ptr);
    f.get(ptr).gset(G.changesO); f.get(ptr).get(opLen).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.changesP); f.get(ptr).get(opLen).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.changesD); f.get(ptr).get(opLen).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.changesI); f.get(ptr).get(opLen).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.hStart);   f.get(ptr).get(opLen).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.hEnd);     f.get(ptr).get(opLen).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.arenaPtr);
    f.get(ptr).i32(64).op(OP.i32_add).call(F.ensureMem);

    f.gget(G.prefix).tee(o).set(p);
    f.i32(0).set(del).i32(0).set(ins).i32(0).set(nc);
    f.get(opLen).i32(1).op(OP.i32_sub).set(idx);
    f.block().loop();
    f.get(idx).i32(0).op(OP.i32_lt_s).br_if(1);
    f.loadArr8(G.revKind, idx).set(kind);
    f.loadArr32(G.revCount, idx).set(cnt);
    f.get(kind).i32(KEEP).op(OP.i32_eq).if_();
    f.get(o).get(cnt).op(OP.i32_add).set(o);
    f.get(p).get(cnt).op(OP.i32_add).set(p);
    f.else_();
    f.get(nc).i32(1).op(OP.i32_sub).set(last);
    f.get(last).i32(0).op(OP.i32_lt_s)
      .if_(I32).i32(1)
      .else_().loadArr32(G.changesO, last).loadArr32(G.changesD, last).op(OP.i32_add).get(o).op(OP.i32_ne)
      .loadArr32(G.changesP, last).loadArr32(G.changesI, last).op(OP.i32_add).get(p).op(OP.i32_ne).op(OP.i32_or).end()
      .if_();
    f.storeArr32(G.changesO, nc, () => f.get(o));
    f.storeArr32(G.changesP, nc, () => f.get(p));
    f.storeArr32(G.changesD, nc, () => f.i32(0));
    f.storeArr32(G.changesI, nc, () => f.i32(0));
    f.get(nc).set(last);
    f.get(nc).i32(1).op(OP.i32_add).set(nc);
    f.end();
    f.get(kind).i32(DELETE).op(OP.i32_eq).if_();
    f.storeArr32(G.changesD, last, () => f.loadArr32(G.changesD, last).get(cnt).op(OP.i32_add));
    f.get(o).get(cnt).op(OP.i32_add).set(o);
    f.get(del).get(cnt).op(OP.i32_add).set(del);
    f.else_();
    f.storeArr32(G.changesI, last, () => f.loadArr32(G.changesI, last).get(cnt).op(OP.i32_add));
    f.get(p).get(cnt).op(OP.i32_add).set(p);
    f.get(ins).get(cnt).op(OP.i32_add).set(ins);
    f.end();
    f.end();
    f.get(idx).i32(1).op(OP.i32_sub).set(idx);
    f.br(0).end().end();

    f.get(nc).gset(G.numChanges).get(del).gset(G.deleted).get(ins).gset(G.inserted);

    f.i32(0).set(nh).i32(0).set(i);
    f.block().loop();
    f.get(i).get(nc).op(OP.i32_ge_s).br_if(1);
    f.get(nh).i32(0).op(OP.i32_gt_s).if_();
    f.get(nh).i32(1).op(OP.i32_sub).set(tmp);
    f.loadArr32(G.hEnd, tmp).set(prev);
    f.loadArr32(G.changesO, i).loadArr32(G.changesO, prev).loadArr32(G.changesD, prev).op(OP.i32_add).op(OP.i32_sub).i32(6).op(OP.i32_le_s).if_();
    f.storeArr32(G.hEnd, tmp, () => f.get(i));
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(2);
    f.end();
    f.end();
    f.storeArr32(G.hStart, nh, () => f.get(i));
    f.storeArr32(G.hEnd, nh, () => f.get(i));
    f.get(nh).i32(1).op(OP.i32_add).set(nh);
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();
    f.get(nh).gset(G.numHunks);
  });

  // ------------------------------------------------------------------ 11. writeDec(outPtr, val) -> newOutPtr
  addFunc(F.writeDec, [I32, I32], [I32], (f) => {
    const ptr = 0, val = 1;
    const start = f.loc(), lo = f.loc(), hi = f.loc(), t = f.loc();
    f.get(val).op(OP.i32_eqz).if_();
    f.get(ptr).i32(48).store8();
    f.get(ptr).i32(1).op(OP.i32_add).ret();
    f.end();
    f.get(ptr).set(start);
    f.block().loop();
    f.get(val).op(OP.i32_eqz).br_if(1);
    f.get(ptr).get(val).i32(10).op(OP.i32_rem_u).i32(48).op(OP.i32_add).store8();
    f.get(ptr).i32(1).op(OP.i32_add).set(ptr);
    f.get(val).i32(10).op(OP.i32_div_u).set(val);
    f.br(0).end().end();
    f.get(start).set(lo).get(ptr).i32(1).op(OP.i32_sub).set(hi);
    f.block().loop();
    f.get(lo).get(hi).op(OP.i32_ge_u).br_if(1);
    f.get(lo).load8().set(t);
    f.get(lo).get(hi).load8().store8();
    f.get(hi).get(t).store8();
    f.get(lo).i32(1).op(OP.i32_add).set(lo);
    f.get(hi).i32(1).op(OP.i32_sub).set(hi);
    f.br(0).end().end();
    f.get(ptr);
  });

  // ------------------------------------------------------------------ 12. writeStrConst (helper unused; inline byte stores are tiny)
  addFunc(F.writeStrConst, [I32], [I32], (f) => f.get(0));

  // ------------------------------------------------------------------ 13. pushLineOut(outPtr, base, s, e, opByte) -> newOutPtr
  addFunc(F.pushLineOut, [I32, I32, I32, I32, I32], [I32], (f) => {
    const out = 0, base = 1, s = 2, e = 3, opB = 4;
    const len = f.loc();
    f.get(out).get(opB).store8();
    f.get(out).i32(1).op(OP.i32_add).set(out);
    f.get(e).get(s).op(OP.i32_sub).set(len);
    f.get(out).get(base).get(s).op(OP.i32_add).get(len).memCopy();
    f.get(out).get(len).op(OP.i32_add).set(out);
    f.get(base).get(e).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_ne).if_();
    // Write "\n%\n"
    f.get(out).i32(10).store8(0);
    f.get(out).i32(37).store8(1);
    f.get(out).i32(10).store8(2);
    f.get(out).i32(3).op(OP.i32_add).set(out);
    f.end();
    f.get(out);
  });

  // ------------------------------------------------------------------ 14. buildPatch()
  addFunc(F.buildPatch, [], [], (f) => {
    const outBase = f.loc(), ptr = f.loc(), totalOld = f.loc(), totalNew = f.loc();
    const prefix = f.loc(), suffix = f.loc(), n = f.loc(), m = f.loc(), nh = f.loc();
    const oBase = f.loc(), nBase = f.loc(), oStart = f.loc(), oEnd = f.loc(), oLen = f.loc();
    const preNeed = f.loc(), sufNeed = f.loc(), preArr = f.loc(), sufArr = f.loc();
    const curPos = f.loc(), i = f.loc(), hi = f.loc(), fi = f.loc(), li = f.loc();
    const firstO = f.loc(), firstP = f.loc(), lastO = f.loc(), lastP = f.loc(), lastD = f.loc(), lastI = f.loc();
    const oldStart = f.loc(), newStart = f.loc(), remAfter = f.loc(), after = f.loc(), oldEnd = f.loc(), newEnd = f.loc();
    const at = f.loc(), ci = f.loc(), co = f.loc(), cp = f.loc(), cd = f.loc(), cins = f.loc(), mi = f.loc(), maxBytes = f.loc();

    f.gget(G.prefix).set(prefix).gget(G.suffix).set(suffix).gget(G.n).set(n).gget(G.m).set(m).gget(G.numHunks).set(nh);
    f.get(prefix).get(n).op(OP.i32_add).get(suffix).op(OP.i32_add).set(totalOld);
    f.get(prefix).get(m).op(OP.i32_add).get(suffix).op(OP.i32_add).set(totalNew);
    f.gget(G.oBase).set(oBase).gget(G.nBase).set(nBase).gget(G.oStart).set(oStart).gget(G.oEnd).set(oEnd).gget(G.oLen).set(oLen);

    // Reserve preArr (16 bytes) and sufArr (16 bytes) + outBuf
    f.gget(G.arenaPtr).set(ptr);
    f.get(ptr).set(preArr); f.get(ptr).i32(16).op(OP.i32_add).set(ptr);
    f.get(ptr).set(sufArr); f.get(ptr).i32(16).op(OP.i32_add).set(ptr);
    f.get(ptr).tee(outBase).gset(G.outBase);
    // Max output bytes: oLen + nLen + totalOld*4 + totalNew*4 + nh*64 + 512
    f.get(oLen).gget(G.nLen).op(OP.i32_add)
      .get(totalOld).get(totalNew).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add)
      .get(nh).i32(6).op(OP.i32_shl).op(OP.i32_add)
      .i32(512).op(OP.i32_add).set(maxBytes);
    f.get(outBase).get(maxBytes).op(OP.i32_add).call(F.ensureMem);

    // Emit header: "makefun-diff/1 old="
    f.get(outBase).set(ptr);
    const emitBytes = (str) => {
      for (let k = 0; k < str.length; k++) f.get(ptr).i32(str.charCodeAt(k)).store8(k);
      f.get(ptr).i32(str.length).op(OP.i32_add).set(ptr);
    };
    emitBytes('makefun-diff/1 old=');
    f.get(ptr).get(totalOld).call(F.writeDec).set(ptr);
    emitBytes(' new=');
    f.get(ptr).get(totalNew).call(F.writeDec).set(ptr);
    emitBytes(' hunks=');
    f.get(ptr).get(nh).call(F.writeDec).set(ptr);
    emitBytes(' deleted=');
    f.get(ptr).gget(G.deleted).call(F.writeDec).set(ptr);
    emitBytes(' inserted=');
    f.get(ptr).gget(G.inserted).call(F.writeDec).set(ptr);
    f.get(ptr).i32(10).store8(0);
    f.get(ptr).i32(1).op(OP.i32_add).set(ptr);

    f.get(nh).op(OP.i32_eqz).if_().get(ptr).gset(G.outEnd).ret().end();

    // Compute preArr (up to 3 context lines before oStart) if needed
    f.i32(0).set(preNeed);
    f.gget(G.changesO).load32(0).get(prefix).i32(3).op(OP.i32_add).op(OP.i32_lt_s).get(prefix).i32(0).op(OP.i32_gt_s).op(OP.i32_and).if_();
    f.get(prefix).i32(3).get(prefix).i32(3).op(OP.i32_lt_s).op(OP.select).set(preNeed);
    f.get(oStart).set(curPos);
    f.get(preArr).get(preNeed).i32(2).op(OP.i32_shl).op(OP.i32_add).get(curPos).store32();
    f.get(preNeed).i32(1).op(OP.i32_sub).set(i);
    f.block().loop();
    f.get(i).i32(0).op(OP.i32_lt_s).br_if(1);
    f.get(curPos).get(oBase).get(curPos).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_eq).if_(I32).i32(2).else_().i32(1).end().op(OP.i32_sub).set(curPos);
    f.block().loop();
    f.get(curPos).i32(0).op(OP.i32_lt_s).br_if(1);
    f.get(oBase).get(curPos).op(OP.i32_add).load8().i32(10).op(OP.i32_eq).br_if(1);
    f.get(curPos).i32(1).op(OP.i32_sub).set(curPos);
    f.br(0).end().end();
    f.get(curPos).i32(1).op(OP.i32_add).set(curPos);
    f.get(preArr).get(i).i32(2).op(OP.i32_shl).op(OP.i32_add).get(curPos).store32();
    f.get(i).i32(1).op(OP.i32_sub).set(i);
    f.br(0).end().end();
    f.end();

    // Compute sufArr (up to 3 context lines after oEnd) if needed
    f.i32(0).set(sufNeed);
    f.get(suffix).i32(0).op(OP.i32_gt_s).if_();
    f.gget(G.hEnd).get(nh).i32(1).op(OP.i32_sub).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().set(li);
    f.loadArr32(G.changesO, li).loadArr32(G.changesD, li).op(OP.i32_add).i32(3).op(OP.i32_add).get(prefix).get(n).op(OP.i32_add).op(OP.i32_gt_s).if_();
    f.get(suffix).i32(3).get(suffix).i32(3).op(OP.i32_lt_s).op(OP.select).set(sufNeed);
    f.get(oEnd).set(curPos);
    f.get(sufArr).get(curPos).store32();
    f.i32(1).set(i);
    f.block().loop();
    f.get(i).get(sufNeed).op(OP.i32_gt_s).br_if(1);
    f.block().loop();
    f.get(curPos).get(oLen).op(OP.i32_ge_u).br_if(1);
    f.get(oBase).get(curPos).op(OP.i32_add).load8().i32(10).op(OP.i32_eq).if_();
    f.get(curPos).i32(1).op(OP.i32_add).set(curPos).br(2);
    f.end();
    f.get(curPos).i32(1).op(OP.i32_add).set(curPos);
    f.br(0).end().end();
    f.get(sufArr).get(i).i32(2).op(OP.i32_shl).op(OP.i32_add).get(curPos).store32();
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();
    f.end();
    f.end();

    const emitPushOld = (giL, opByte) => {
      const s = f.loc(), e = f.loc(), off = f.loc();
      f.get(giL).get(prefix).op(OP.i32_ge_s).get(giL).get(prefix).get(n).op(OP.i32_add).op(OP.i32_lt_s).op(OP.i32_and).if_();
      f.get(giL).get(prefix).op(OP.i32_sub).set(off);
      f.loadArr32(G.oStarts, off).set(s);
      f.loadArr32(G.oEnds, off).set(e);
      f.else_().get(giL).get(prefix).op(OP.i32_lt_s).if_();
      f.get(giL).get(prefix).get(preNeed).op(OP.i32_sub).op(OP.i32_sub).set(off);
      f.get(preArr).get(off).i32(2).op(OP.i32_shl).op(OP.i32_add).tee(off).load32(0).set(s);
      f.get(off).load32(4).set(e);
      f.else_();
      f.get(giL).get(prefix).get(n).op(OP.i32_add).op(OP.i32_sub).set(off);
      f.get(sufArr).get(off).i32(2).op(OP.i32_shl).op(OP.i32_add).tee(off).load32(0).set(s);
      f.get(off).load32(4).set(e);
      f.end().end();
      f.get(ptr).get(oBase).get(s).get(e).i32(opByte).call(F.pushLineOut).set(ptr);
    };

    f.i32(0).set(hi);
    f.block().loop();
    f.get(hi).get(nh).op(OP.i32_ge_s).br_if(1);
    f.loadArr32(G.hStart, hi).set(fi);
    f.loadArr32(G.hEnd, hi).set(li);
    f.loadArr32(G.changesO, fi).set(firstO);
    f.loadArr32(G.changesP, fi).set(firstP);
    f.loadArr32(G.changesO, li).set(lastO);
    f.loadArr32(G.changesP, li).set(lastP);
    f.loadArr32(G.changesD, li).set(lastD);
    f.loadArr32(G.changesI, li).set(lastI);

    f.get(firstO).i32(3).op(OP.i32_gt_s).if_(I32).get(firstO).i32(3).op(OP.i32_sub).else_().i32(0).end().set(oldStart);
    f.get(firstP).get(firstO).get(oldStart).op(OP.i32_sub).op(OP.i32_sub).set(newStart);
    f.get(totalOld).get(lastO).get(lastD).op(OP.i32_add).op(OP.i32_sub).set(remAfter);
    f.get(remAfter).i32(3).get(remAfter).i32(3).op(OP.i32_lt_s).op(OP.select).set(after);
    f.get(lastO).get(lastD).op(OP.i32_add).get(after).op(OP.i32_add).set(oldEnd);
    f.get(lastP).get(lastI).op(OP.i32_add).get(after).op(OP.i32_add).set(newEnd);

    emitBytes('@ ');
    f.get(ptr).get(oldStart).i32(1).op(OP.i32_add).call(F.writeDec).set(ptr);
    f.get(ptr).i32(32).store8(); f.get(ptr).i32(1).op(OP.i32_add).set(ptr);
    f.get(ptr).get(oldEnd).get(oldStart).op(OP.i32_sub).call(F.writeDec).set(ptr);
    f.get(ptr).i32(32).store8(); f.get(ptr).i32(1).op(OP.i32_add).set(ptr);
    f.get(ptr).get(newStart).i32(1).op(OP.i32_add).call(F.writeDec).set(ptr);
    f.get(ptr).i32(32).store8(); f.get(ptr).i32(1).op(OP.i32_add).set(ptr);
    f.get(ptr).get(newEnd).get(newStart).op(OP.i32_sub).call(F.writeDec).set(ptr);
    f.get(ptr).i32(10).store8(); f.get(ptr).i32(1).op(OP.i32_add).set(ptr);

    f.get(oldStart).set(at).get(fi).set(ci);
    f.block().loop();
    f.get(ci).get(li).op(OP.i32_gt_s).br_if(1);
    f.loadArr32(G.changesO, ci).set(co);
    f.loadArr32(G.changesP, ci).set(cp);
    f.loadArr32(G.changesD, ci).set(cd);
    f.loadArr32(G.changesI, ci).set(cins);

    f.block().loop();
    f.get(at).get(co).op(OP.i32_ge_s).br_if(1);
    emitPushOld(at, 61); // '='
    f.get(at).i32(1).op(OP.i32_add).set(at);
    f.br(0).end().end();

    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(cd).op(OP.i32_ge_s).br_if(1);
    f.get(co).get(i).op(OP.i32_add).set(at);
    emitPushOld(at, 45); // '-'
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(cins).op(OP.i32_ge_s).br_if(1);
    f.get(cp).get(i).op(OP.i32_add).get(prefix).op(OP.i32_sub).set(mi);
    f.get(ptr).get(nBase).loadArr32(G.nStarts, mi).loadArr32(G.nEnds, mi).i32(43).call(F.pushLineOut).set(ptr); // '+'
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    f.get(co).get(cd).op(OP.i32_add).set(at);
    f.get(ci).i32(1).op(OP.i32_add).set(ci);
    f.br(0).end().end();

    f.block().loop();
    f.get(at).get(oldEnd).op(OP.i32_ge_s).br_if(1);
    emitPushOld(at, 61); // '='
    f.get(at).i32(1).op(OP.i32_add).set(at);
    f.br(0).end().end();

    f.get(hi).i32(1).op(OP.i32_add).set(hi);
    f.br(0).end().end();
    f.get(ptr).gset(G.outEnd);
  });

  // ------------------------------------------------------------------ 15. solveAscii() -> outLen
  addFunc(F.solveAscii, [], [I32], (f) => {
    f.call(F.trimPrefixSuffix);
    f.gget(G.oStart).gget(G.oEnd).op(OP.i32_eq).gget(G.nStart).gget(G.nEnd).op(OP.i32_eq).op(OP.i32_and).if_();
    f.i32(0).gset(G.n).i32(0).gset(G.m).i32(0).gset(G.numHunks).i32(0).gset(G.deleted).i32(0).gset(G.inserted);
    f.gget(G.nBase).gget(G.nLen).op(OP.i32_add).i32(31).op(OP.i32_add).i32(-8).op(OP.i32_and).gset(G.arenaPtr);
    f.call(F.buildPatch);
    f.gget(G.outEnd).gget(G.outBase).op(OP.i32_sub).ret();
    f.end();

    f.call(F.scanLines);
    f.gget(G.n).op(OP.i32_eqz).gget(G.m).op(OP.i32_eqz).op(OP.i32_or).if_();
    f.gget(G.changesO).gget(G.prefix).store32(0);
    f.gget(G.changesP).gget(G.prefix).store32(0);
    f.gget(G.changesD).gget(G.n).store32(0);
    f.gget(G.changesI).gget(G.m).store32(0);
    f.gget(G.hStart).i32(0).store32(0);
    f.gget(G.hEnd).i32(0).store32(0);
    f.i32(1).gset(G.numChanges).i32(1).gset(G.numHunks);
    f.gget(G.n).gset(G.deleted).gget(G.m).gset(G.inserted);
    f.call(F.buildPatch);
    f.gget(G.outEnd).gget(G.outBase).op(OP.i32_sub).ret();
    f.end();

    f.call(F.internLines);
    f.call(F.buildBoundsAndUB).op(OP.drop);
    f.call(F.myersForward);
    f.call(F.replayPath);
    f.call(F.buildChangesAndHunks);
    f.call(F.buildPatch);
    f.gget(G.outEnd).gget(G.outBase).op(OP.i32_sub);
  });

  addFunc(F.getOutBase, [], [I32], (f) => f.gget(G.outBase));

  // Encode WASM module
  const bytes = [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];

  // Type section (1)
  const typeSec = [];
  pushUleb(typeSec, types.length);
  for (const t of types) {
    typeSec.push(0x60);
    pushUleb(typeSec, t.params.length);
    for (const p of t.params) typeSec.push(p);
    pushUleb(typeSec, t.results.length);
    for (const r of t.results) typeSec.push(r);
  }
  bytes.push(...encodeSection(1, typeSec));

  // Function section (3)
  const funcSec = [];
  pushUleb(funcSec, funcs.length);
  for (const fn of funcs) pushUleb(funcSec, fn.typeIdx);
  bytes.push(...encodeSection(3, funcSec));

  // Memory section (5): min 256 pages (16 MiB)
  const memSec = [0x01, 0x00];
  pushUleb(memSec, 256);
  bytes.push(...encodeSection(5, memSec));

  // Global section (6): all mutable i32 initialized to 0
  const globSec = [];
  pushUleb(globSec, globalCount);
  for (let i = 0; i < globalCount; i++) {
    globSec.push(I32, 0x01, OP.i32_const, 0x00, OP.end);
  }
  bytes.push(...encodeSection(6, globSec));

  // Export section (7)
  const exports = [
    ['memory', 0x02, 0],
    ['prepareInput', 0x00, F.prepareInput],
    ['solveAscii', 0x00, F.solveAscii],
    ['getOutBase', 0x00, F.getOutBase],
  ];
  const expSec = [];
  pushUleb(expSec, exports.length);
  for (const [name, kind, idx] of exports) {
    const nb = Buffer.from(name, 'utf8');
    pushUleb(expSec, nb.length);
    for (let i = 0; i < nb.length; i++) expSec.push(nb[i]);
    expSec.push(kind);
    pushUleb(expSec, idx);
  }
  bytes.push(...encodeSection(7, expSec));

  // Code section (10)
  const codeSec = [];
  pushUleb(codeSec, funcs.length);
  for (const fn of funcs) {
    const body = [];
    // Group consecutive locals of same type
    const groups = [];
    for (const t of fn.emitter.locals) {
      if (groups.length > 0 && groups[groups.length - 1][1] === t) groups[groups.length - 1][0]++;
      else groups.push([1, t]);
    }
    pushUleb(body, groups.length);
    for (const [cnt, t] of groups) {
      pushUleb(body, cnt);
      body.push(t);
    }
    for (let i = 0; i < fn.emitter.code.length; i++) body.push(fn.emitter.code[i]);
    pushUleb(codeSec, body.length);
    for (let i = 0; i < body.length; i++) codeSec.push(body[i]);
  }
  bytes.push(...encodeSection(10, codeSec));

  const mod = new WebAssembly.Module(new Uint8Array(bytes));
  return new WebAssembly.Instance(mod).exports;
}
