// Hand-authored WebAssembly SIMD128 bytecode builder for zero-JSON batch diff & patch construction.
// Compiles synchronously via WebAssembly.Module with zero external dependencies.

const I32 = 0x7f;
const I64 = 0x7e;
const V128 = 0x7b;
const VOID = 0x40;
const KEEP = 0;
const DELETE = 1;
const INSERT = 2;

const OP = {
  unreachable: 0x00,
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
  i32_clz: 0x67,
  i32_ctz: 0x68,
  i32_popcnt: 0x69,
  i32_add: 0x6a,
  i32_sub: 0x6b,
  i32_mul: 0x6c,
  i32_div_u: 0x6e,
  i32_rem_u: 0x70,
  i32_and: 0x71,
  i32_or: 0x72,
  i32_xor: 0x73,
  i32_shl: 0x74,
  i32_shr_s: 0x75,
  i32_shr_u: 0x76,
  i64_ctz: 0x7a,
  i64_sub: 0x7d,
  i64_mul: 0x7e,
  i64_and: 0x83,
  i64_or: 0x84,
  i64_xor: 0x85,
  i64_shl: 0x86,
  i64_shr_u: 0x88,
  i32_wrap_i64: 0xa7,
  i64_extend_i32_u: 0xad,
};

function writeUleb(buf, p, v) {
  v >>>= 0;
  while (v >= 0x80) {
    buf[p++] = (v & 0x7f) | 0x80;
    v >>>= 7;
  }
  buf[p++] = v;
  return p;
}

function writeSleb32(buf, p, v) {
  v |= 0;
  while (true) {
    const b = v & 0x7f;
    v >>= 7;
    if ((v === 0 && (b & 0x40) === 0) || (v === -1 && (b & 0x40) !== 0)) {
      buf[p++] = b;
      return p;
    }
    buf[p++] = b | 0x80;
  }
}

function writeSleb64LH(buf, p, lo, hi) {
  lo >>>= 0;
  hi |= 0;
  while (true) {
    const b = lo & 0x7f;
    lo = ((lo >>> 7) | (hi << 25)) >>> 0;
    hi >>= 7;
    if ((hi === 0 && lo === 0 && (b & 0x40) === 0) || (hi === -1 && lo === 0xffffffff && (b & 0x40) !== 0)) {
      buf[p++] = b;
      return p;
    }
    buf[p++] = b | 0x80;
  }
}

class FuncEmitter {
  constructor(params, results) {
    this.params = params;
    this.results = results;
    this.locals = [];
    this.buf = new Uint8Array(8192);
    this.pos = 0;
  }
  grow() {
    const next = new Uint8Array(this.buf.length * 2);
    next.set(this.buf);
    this.buf = next;
  }
  loc(type = I32) {
    const idx = this.params.length + this.locals.length;
    this.locals.push(type);
    return idx;
  }
  op(o) { if (this.pos >= this.buf.length) this.grow(); this.buf[this.pos++] = o; return this; }
  i32(v) {
    if (this.pos + 6 > this.buf.length) this.grow();
    this.buf[this.pos++] = OP.i32_const;
    if (v >= -64 && v < 64) { this.buf[this.pos++] = v & 0x7f; return this; }
    this.pos = writeSleb32(this.buf, this.pos, v);
    return this;
  }
  i64(lo, hi = lo < 0 ? -1 : 0) {
    if (this.pos + 11 > this.buf.length) this.grow();
    this.buf[this.pos++] = OP.i64_const;
    this.pos = writeSleb64LH(this.buf, this.pos, lo, hi);
    return this;
  }
  get(l) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.local_get; if (l < 128) this.buf[this.pos++] = l; else this.pos = writeUleb(this.buf, this.pos, l); return this; }
  set(l) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.local_set; if (l < 128) this.buf[this.pos++] = l; else this.pos = writeUleb(this.buf, this.pos, l); return this; }
  tee(l) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.local_tee; if (l < 128) this.buf[this.pos++] = l; else this.pos = writeUleb(this.buf, this.pos, l); return this; }
  gget(g) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.global_get; if (g < 128) this.buf[this.pos++] = g; else this.pos = writeUleb(this.buf, this.pos, g); return this; }
  gset(g) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.global_set; if (g < 128) this.buf[this.pos++] = g; else this.pos = writeUleb(this.buf, this.pos, g); return this; }
  call(f) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.call; if (f < 128) this.buf[this.pos++] = f; else this.pos = writeUleb(this.buf, this.pos, f); return this; }
  load32(off = 0) { if (this.pos + 7 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.i32_load; this.buf[this.pos++] = 2; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  load32u(off = 0) { if (this.pos + 7 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.i32_load; this.buf[this.pos++] = 0; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  load64(off = 0) { if (this.pos + 7 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.i64_load; this.buf[this.pos++] = 0; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  load8(off = 0) { if (this.pos + 7 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.i32_load8_u; this.buf[this.pos++] = 0; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  store32(off = 0) { if (this.pos + 7 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.i32_store; this.buf[this.pos++] = 2; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  store64(off = 0) { if (this.pos + 7 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.i64_store; this.buf[this.pos++] = 0; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  store8(off = 0) { if (this.pos + 7 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.i32_store8; this.buf[this.pos++] = 0; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  vload(off = 0) { if (this.pos + 8 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfd; this.buf[this.pos++] = 0x00; this.buf[this.pos++] = 0; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  vstore(off = 0) { if (this.pos + 8 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfd; this.buf[this.pos++] = 0x0b; this.buf[this.pos++] = 0; if (off < 128) this.buf[this.pos++] = off; else this.pos = writeUleb(this.buf, this.pos, off); return this; }
  vsplat8() { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfd; this.buf[this.pos++] = 0x0f; return this; }
  veq8() { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfd; this.buf[this.pos++] = 0x23; return this; }
  vlts8() { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfd; this.buf[this.pos++] = 0x25; return this; }
  vbitmask8() { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfd; this.buf[this.pos++] = 0x64; return this; }
  vor() { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfd; this.buf[this.pos++] = 0x50; return this; }
  block(ty = VOID) { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.block; this.buf[this.pos++] = ty; return this; }
  loop(ty = VOID) { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.loop; this.buf[this.pos++] = ty; return this; }
  if_(ty = VOID) { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.if; this.buf[this.pos++] = ty; return this; }
  else_() { if (this.pos >= this.buf.length) this.grow(); this.buf[this.pos++] = OP.else; return this; }
  end() { if (this.pos >= this.buf.length) this.grow(); this.buf[this.pos++] = OP.end; return this; }
  br(d) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.br; if (d < 128) this.buf[this.pos++] = d; else this.pos = writeUleb(this.buf, this.pos, d); return this; }
  br_if(d) { if (this.pos + 5 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.br_if; if (d < 128) this.buf[this.pos++] = d; else this.pos = writeUleb(this.buf, this.pos, d); return this; }
  ret() { if (this.pos >= this.buf.length) this.grow(); this.buf[this.pos++] = OP.return; return this; }
  memCopy() { if (this.pos + 4 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfc; this.buf[this.pos++] = 0x0a; this.buf[this.pos++] = 0; this.buf[this.pos++] = 0; return this; }
  memFill() { if (this.pos + 3 > this.buf.length) this.grow(); this.buf[this.pos++] = 0xfc; this.buf[this.pos++] = 0x0b; this.buf[this.pos++] = 0; return this; }
  memSize() { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.memory_size; this.buf[this.pos++] = 0; return this; }
  memGrow() { if (this.pos + 2 > this.buf.length) this.grow(); this.buf[this.pos++] = OP.memory_grow; this.buf[this.pos++] = 0; return this; }

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

  const G = {
    oBase: g(), oLen: g(), nBase: g(), nLen: g(), arenaBase: g(),
    oStart: g(), nStart: g(), oEnd: g(), nEnd: g(),
    prefix: g(), suffix: g(), n: g(), m: g(),
    arenaPtr: g(),
    oStarts: g(), oEnds: g(), oHash: g(),
    nStarts: g(), nEnds: g(), nHash: g(),
    buckets: g(), hMask: g(),
    A: g(), B: g(), cntA: g(), cntB: g(), posB: g(), seen: g(),
    remDel: g(), remIns: g(), prefUniqA: g(), prefUniqB: g(),
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
    jsonLen: g(), jsonCur: g(), batchOutBase: g(),
  };

  let funcCount = 0;
  const fnId = () => funcCount++;
  const F = {
    ensureMem: fnId(),
    prepareInput: fnId(),
    prepareBatch: fnId(),
    countLines: fnId(),
    trimPrefixSuffix: fnId(),
    scanLines: fnId(),
    internLines: fnId(),
    buildBoundsAndUB: fnId(),
    myersForward: fnId(),
    replayPath: fnId(),
    buildChangesAndHunks: fnId(),
    writeDec: fnId(),
    pushLineOut: fnId(),
    buildPatch: fnId(),
    solveAscii: fnId(),
    getOutBase: fnId(),
    getBatchOutBase: fnId(),
    skipWs: fnId(),
    skipJsonStr: fnId(),
    unescapeJsonStr: fnId(),
    escapeJsonOut: fnId(),
    solveBatchJson: fnId(),
  };

  const funcs = new Array(funcCount);
  const addFunc = (id, params, results, build) => {
    const f = new FuncEmitter(params, results);
    build(f);
    f.end();
    funcs[id] = { typeIdx: internType(params, results), emitter: f };
  };

  // ------------------------------------------------------------------ ensureMem(neededBytes)
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

  // ------------------------------------------------------------------ prepareInput(oLen, nLen) -> nBase
  addFunc(F.prepareInput, [I32, I32], [I32], (f) => {
    const oLen = 0, nLen = 1;
    const nBase = f.loc(), ab = f.loc();
    f.i32(0).gset(G.oBase);
    f.get(oLen).gset(G.oLen);
    f.get(oLen).i32(31).op(OP.i32_add).i32(-16).op(OP.i32_and).tee(nBase).gset(G.nBase);
    f.get(nLen).gset(G.nLen);
    f.get(nBase).get(nLen).op(OP.i32_add).i32(31).op(OP.i32_add).i32(-16).op(OP.i32_and).tee(ab).gset(G.arenaBase);
    f.get(ab).i32(64).op(OP.i32_add).call(F.ensureMem);
    f.get(nBase);
  });

  // ------------------------------------------------------------------ prepareBatch(jsonLen) -> jsonBase(0)
  addFunc(F.prepareBatch, [I32], [I32], (f) => {
    const jsonLen = 0;
    f.get(jsonLen).gset(G.jsonLen);
    f.get(jsonLen).i32(256).op(OP.i32_add).call(F.ensureMem);
    f.i32(0);
  });

  // ------------------------------------------------------------------ countLines(ptr, len) -> i32 (SIMD128)
  addFunc(F.countLines, [I32, I32], [I32], (f) => {
    const ptr = 0, len = 1;
    const cnt = f.loc(), end = f.loc(), end16 = f.loc(), p = f.loc();
    const nl16 = f.loc(V128);
    f.get(len).op(OP.i32_eqz).if_().i32(0).ret().end();
    f.i32(0).set(cnt).get(ptr).set(p).get(ptr).get(len).op(OP.i32_add).tee(end).i32(16).op(OP.i32_sub).set(end16);
    f.i32(10).vsplat8().set(nl16);

    f.block().loop();
    f.get(p).get(end16).op(OP.i32_gt_s).br_if(1);
    f.get(cnt).get(p).vload().get(nl16).veq8().vbitmask8().op(OP.i32_popcnt).op(OP.i32_add).set(cnt);
    f.get(p).i32(16).op(OP.i32_add).set(p);
    f.br(0).end().end();

    f.block().loop();
    f.get(p).get(end).op(OP.i32_ge_u).br_if(1);
    f.get(p).load8().i32(10).op(OP.i32_eq).get(cnt).op(OP.i32_add).set(cnt);
    f.get(p).i32(1).op(OP.i32_add).set(p);
    f.br(0).end().end();

    f.get(end).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_ne).if_();
    f.get(cnt).i32(1).op(OP.i32_add).set(cnt);
    f.end();
    f.get(cnt);
  });

  // ------------------------------------------------------------------ trimPrefixSuffix() (SIMD128)
  addFunc(F.trimPrefixSuffix, [], [], (f) => {
    const oBase = f.loc(), nBase = f.loc(), oLen = f.loc(), nLen = f.loc();
    const minL = f.loc(), p = f.loc(), min16 = f.loc();
    const oPtr = f.loc(), nPtr = f.loc(), s = f.loc(), maxS = f.loc(), maxS16 = f.loc();
    const b1 = f.loc(), b2 = f.loc(), mask = f.loc();

    f.gget(G.oBase).set(oBase).gget(G.nBase).set(nBase).gget(G.oLen).set(oLen).gget(G.nLen).set(nLen);
    f.get(oLen).get(nLen).get(oLen).get(nLen).op(OP.i32_lt_u).op(OP.select).set(minL);

    // Common prefix 16 bytes/iter
    f.i32(0).set(p).get(minL).i32(16).op(OP.i32_sub).set(min16);
    f.block().loop();
    f.get(p).get(min16).op(OP.i32_gt_s).br_if(1);
    f.get(oBase).get(p).op(OP.i32_add).vload()
      .get(nBase).get(p).op(OP.i32_add).vload()
      .veq8().vbitmask8().i32(0xffff).op(OP.i32_xor).tee(mask).if_();
    f.get(p).get(mask).op(OP.i32_ctz).op(OP.i32_add).set(p);
    f.br(2);
    f.end();
    f.get(p).i32(16).op(OP.i32_add).set(p);
    f.br(0).end().end();

    f.block().loop();
    f.get(p).get(minL).op(OP.i32_ge_u).br_if(1);
    f.get(oBase).get(p).op(OP.i32_add).load8().get(nBase).get(p).op(OP.i32_add).load8().op(OP.i32_ne).br_if(1);
    f.get(p).i32(1).op(OP.i32_add).set(p);
    f.br(0).end().end();

    // Identical fast exit
    f.get(p).get(oLen).op(OP.i32_eq).get(p).get(nLen).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(oBase).get(oLen).call(F.countLines).gset(G.prefix);
    f.i32(0).gset(G.suffix);
    f.get(oLen).gset(G.oStart).get(nLen).gset(G.nStart).get(oLen).gset(G.oEnd).get(nLen).gset(G.nEnd);
    f.ret();
    f.end();

    // Roll back p to line boundary
    f.block().loop();
    f.get(p).op(OP.i32_eqz).br_if(1);
    f.get(oBase).get(p).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_eq).br_if(1);
    f.get(p).i32(1).op(OP.i32_sub).set(p);
    f.br(0).end().end();

    f.get(p).gset(G.oStart).get(p).gset(G.nStart);
    f.get(oBase).get(p).call(F.countLines).gset(G.prefix);

    // Common suffix 16 bytes/iter
    f.get(oLen).get(p).op(OP.i32_sub).set(b1);
    f.get(nLen).get(p).op(OP.i32_sub).set(b2);
    f.get(b1).get(b2).get(b1).get(b2).op(OP.i32_lt_u).op(OP.select).set(maxS);
    f.i32(0).set(s).get(maxS).i32(16).op(OP.i32_sub).set(maxS16);

    f.block().loop();
    f.get(s).get(maxS16).op(OP.i32_gt_s).br_if(1);
    f.get(oBase).get(oLen).op(OP.i32_add).get(s).op(OP.i32_sub).i32(16).op(OP.i32_sub).vload()
      .get(nBase).get(nLen).op(OP.i32_add).get(s).op(OP.i32_sub).i32(16).op(OP.i32_sub).vload()
      .veq8().vbitmask8().i32(0xffff).op(OP.i32_xor).tee(mask).if_();
    f.get(s).get(mask).i32(16).op(OP.i32_shl).op(OP.i32_clz).op(OP.i32_add).set(s);
    f.br(2);
    f.end();
    f.get(s).i32(16).op(OP.i32_add).set(s);
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
    f.get(oPtr).get(p).op(OP.i32_eq)
      .if_(I32).i32(1).else_().get(oBase).get(oPtr).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_eq).end()
      .get(nPtr).get(p).op(OP.i32_eq)
      .if_(I32).i32(1).else_().get(nBase).get(nPtr).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_eq).end()
      .op(OP.i32_and).op(OP.i32_eqz).if_();
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

    f.get(oPtr).gset(G.oEnd).get(nPtr).gset(G.nEnd);
    f.get(oBase).get(oPtr).op(OP.i32_add).get(oLen).get(oPtr).op(OP.i32_sub).call(F.countLines).gset(G.suffix);
  });

  // ------------------------------------------------------------------ scanLines() (SIMD128 + 64-bit FNV-1a)
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

    f.gget(G.arenaBase).set(ptr);
    allocArr(G.oStarts, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.oEnds, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.oHash, () => f.get(n).i32(4).op(OP.i32_add).i32(3).op(OP.i32_shl));
    allocArr(G.nStarts, () => f.get(m).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.nEnds, () => f.get(m).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.nHash, () => f.get(m).i32(4).op(OP.i32_add).i32(3).op(OP.i32_shl));

    f.get(n).op(OP.i32_eqz).get(m).op(OP.i32_eqz).op(OP.i32_or).if_();
    allocArr(G.changesO, () => f.i32(16));
    allocArr(G.changesP, () => f.i32(16));
    allocArr(G.changesD, () => f.i32(16));
    allocArr(G.changesI, () => f.i32(16));
    allocArr(G.hStart, () => f.i32(16));
    allocArr(G.hEnd, () => f.i32(16));
    f.get(ptr).gset(G.arenaPtr);
    f.get(ptr).i32(64).op(OP.i32_add).call(F.ensureMem);
    const scanSide = (baseG, stG, enG, startsG, endsG) => {
      const idx = f.loc(), pos = f.loc(), end = f.loc(), base = f.loc(), ls = f.loc();
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
    f.get(n).if_(); scanSide(G.oBase, G.oStart, G.oEnd, G.oStarts, G.oEnds); f.end();
    f.get(m).if_(); scanSide(G.nBase, G.nStart, G.nEnd, G.nStarts, G.nEnds); f.end();
    f.ret();
    f.end();

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
    allocArr(G.prefUniqA, () => f.get(n).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
    allocArr(G.prefUniqB, () => f.get(m).i32(4).op(OP.i32_add).i32(2).op(OP.i32_shl));
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

    f.gget(G.buckets).i32(0).get(hCap).i32(2).op(OP.i32_shl).memFill();
    f.gget(G.cntA).i32(0).get(n).i32(2).op(OP.i32_shl).memFill();
    f.gget(G.cntB).i32(0).get(n).i32(2).op(OP.i32_shl).memFill();

    const scanHashSide = (baseG, stG, enG, startsG, endsG, hashG) => {
      const idx = f.loc(), pos = f.loc(), end = f.loc(), base = f.loc(), ls = f.loc();
      const end16 = f.loc(), end8 = f.loc(), b = f.loc(), sh = f.loc(), mask = f.loc();
      const w = f.loc(I64), x = f.loc(I64), z = f.loc(I64), h = f.loc(I64), tailMask = f.loc(I64), tailW = f.loc(I64);
      const nl16 = f.loc(V128);
      f.gget(baseG).set(base).gget(stG).set(pos).gget(enG).set(end).i32(0).set(idx);
      f.get(end).i32(16).op(OP.i32_sub).set(end16);
      f.get(end).i32(8).op(OP.i32_sub).set(end8);
      f.i32(10).vsplat8().set(nl16);

      f.block().loop();
      f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
      f.get(pos).set(ls);
      f.i64(0x84222325, 0xcbf29ce4).set(h);

      f.block(); // foundLine
      // 16-byte SIMD128 newline scan + dual i64 FNV-1a mix
      f.block().loop();
      f.get(pos).get(end16).op(OP.i32_gt_s).br_if(1);
      f.get(base).get(pos).op(OP.i32_add).vload().get(nl16).veq8().vbitmask8().tee(mask).if_();
      f.get(mask).op(OP.i32_ctz).set(b);
      f.get(b).i32(8).op(OP.i32_ge_s).if_();
      f.get(h).get(base).get(pos).op(OP.i32_add).load64().op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul).set(h);
      f.i64(-1).i32(15).get(b).op(OP.i32_sub).i32(3).op(OP.i32_shl).op(OP.i64_extend_i32_u).op(OP.i64_shr_u).set(tailMask);
      f.get(h).get(base).get(pos).op(OP.i32_add).i32(8).op(OP.i32_add).load64().get(tailMask).op(OP.i64_and).op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul).set(h);
      f.else_();
      f.i64(-1).i32(7).get(b).op(OP.i32_sub).i32(3).op(OP.i32_shl).op(OP.i64_extend_i32_u).op(OP.i64_shr_u).set(tailMask);
      f.get(h).get(base).get(pos).op(OP.i32_add).load64().get(tailMask).op(OP.i64_and).op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul).set(h);
      f.end();
      f.get(pos).get(b).op(OP.i32_add).i32(1).op(OP.i32_add).set(pos);
      f.br(3);
      f.end();
      // No newline in 16 bytes -> hash two i64 words
      f.get(h).get(base).get(pos).op(OP.i32_add).load64().op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul)
        .get(base).get(pos).op(OP.i32_add).i32(8).op(OP.i32_add).load64().op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul).set(h);
      f.get(pos).i32(16).op(OP.i32_add).set(pos);
      f.br(0).end().end();

      // 8-byte SWAR tail (< 16 bytes remaining)
      f.block().loop();
      f.get(pos).get(end8).op(OP.i32_gt_s).br_if(1);
      f.get(base).get(pos).op(OP.i32_add).load64().tee(w).i64(0x0a0a0a0a, 0x0a0a0a0a).op(OP.i64_xor).set(x);
      f.get(x).i64(0x01010101, 0x01010101).op(OP.i64_sub)
        .get(x).i64(-1).op(OP.i64_xor).op(OP.i64_and)
        .i64(0x80808080, 0x80808080).op(OP.i64_and).tee(z).op(OP.i64_eqz).op(OP.i32_eqz).if_();
      f.get(z).op(OP.i64_ctz).op(OP.i32_wrap_i64).i32(3).op(OP.i32_shr_u).set(b);
      f.i64(-1).i32(7).get(b).op(OP.i32_sub).i32(3).op(OP.i32_shl).op(OP.i64_extend_i32_u).op(OP.i64_shr_u).set(tailMask);
      f.get(h).get(w).get(tailMask).op(OP.i64_and).op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul).set(h);
      f.get(pos).get(b).op(OP.i32_add).i32(1).op(OP.i32_add).set(pos);
      f.br(3);
      f.end();
      f.get(h).get(w).op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul).set(h);
      f.get(pos).i32(8).op(OP.i32_add).set(pos);
      f.br(0).end().end();

      // Byte tail (< 8 bytes remaining)
      f.i64(0).set(tailW).i32(0).set(sh);
      f.block().loop();
      f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
      f.get(base).get(pos).op(OP.i32_add).load8().set(b);
      f.get(tailW).get(b).op(OP.i64_extend_i32_u).get(sh).op(OP.i64_extend_i32_u).op(OP.i64_shl).op(OP.i64_or).set(tailW);
      f.get(sh).i32(8).op(OP.i32_add).set(sh);
      f.get(pos).i32(1).op(OP.i32_add).set(pos);
      f.get(b).i32(10).op(OP.i32_eq).br_if(1);
      f.br(0).end().end();
      f.get(sh).if_();
      f.get(h).get(tailW).op(OP.i64_xor).i64(0x1b3, 0x100).op(OP.i64_mul).set(h);
      f.end();
      f.end(); // end foundLine

      f.storeArr32(startsG, idx, () => f.get(ls));
      f.storeArr32(endsG, idx, () => f.get(pos));
      f.storeArr64(hashG, idx, () => f.get(h));
      f.get(idx).i32(1).op(OP.i32_add).set(idx);
      f.br(0).end().end();
    };
    scanHashSide(G.oBase, G.oStart, G.oEnd, G.oStarts, G.oEnds, G.oHash);
    scanHashSide(G.nBase, G.nStart, G.nEnd, G.nStarts, G.nEnds, G.nHash);
  });

  // ------------------------------------------------------------------ internLines()
  addFunc(F.internLines, [], [], (f) => {
    const n = f.loc(), m = f.loc(), hMask = f.loc(), oBase = f.loc(), nBase = f.loc();
    const i = f.loc(), st = f.loc(), len = f.loc(), hi = f.loc(I64), slot = f.loc(), bk = f.loc(), rep = f.loc();
    const rs = f.loc(), k = f.loc(), p1 = f.loc(), p2 = f.loc(), found = f.loc();

    f.gget(G.n).set(n).gget(G.m).set(m).gget(G.hMask).set(hMask).gget(G.oBase).set(oBase).gget(G.nBase).set(nBase);

    const checkEq = (base2L, onMatch) => {
      f.get(oBase).get(rs).op(OP.i32_add).set(p1);
      f.get(base2L).get(st).op(OP.i32_add).set(p2);
      f.i32(0).set(k);
      f.block();
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

    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(n).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.oStarts, i).set(st);
    f.loadArr32(G.oEnds, i).get(st).op(OP.i32_sub).set(len);
    f.loadArr64(G.oHash, i).set(hi);
    f.get(hi).get(hi).i64(32).op(OP.i64_shr_u).op(OP.i64_xor).op(OP.i32_wrap_i64).get(hMask).op(OP.i32_and).set(slot);
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

    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(m).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.nStarts, i).set(st);
    f.loadArr32(G.nEnds, i).get(st).op(OP.i32_sub).set(len);
    f.loadArr64(G.nHash, i).set(hi);
    f.get(hi).get(hi).i64(32).op(OP.i64_shr_u).op(OP.i64_xor).op(OP.i32_wrap_i64).get(hMask).op(OP.i32_and).set(slot);
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

  // ------------------------------------------------------------------ buildBoundsAndUB() -> U
  addFunc(F.buildBoundsAndUB, [], [I32], (f) => {
    const n = f.loc(), m = f.loc(), i = f.loc(), acc = f.loc(), id = f.loc(), sc = f.loc();
    const tLen = f.loc(), j = f.loc(), lo = f.loc(), hi = f.loc(), mid = f.loc(), cur = f.loc(), k = f.loc();
    const kHint = f.loc(), partnerK = f.loc(), kr = f.loc(), kl = f.loc(), steps = f.loc();
    const pa = f.loc(), pb = f.loc(), minA = f.loc(), minB = f.loc(), gx = f.loc(), gy = f.loc(), row = f.loc(), nxt = f.loc();
    const U = f.loc(), g = f.loc(), x0 = f.loc(), y0 = f.loc(), gn = f.loc(), gm = f.loc();
    const maxGD = f.loc(), sA = f.loc(), sB = f.loc(), d = f.loc(), idx = f.loc(), diag = f.loc();
    const xr = f.loc(), xa = f.loc(), cr = f.loc(), ca = f.loc(), nx = f.loc(), ny = f.loc(), solved = f.loc(), tmp = f.loc();

    f.gget(G.n).set(n).gget(G.m).set(m);

    // 1. remDel[0..n] and remIns[0..m]
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

    // 2. isUniq + prefUniqA + prefUniqB + Patience LIS
    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(n).op(OP.i32_ge_u).br_if(1);
    f.storeArr8(G.isUniq, i, () =>
      f.loadArr32(G.cntA, i).i32(1).op(OP.i32_eq).loadArr32(G.cntB, i).i32(1).op(OP.i32_eq).op(OP.i32_and)
    );
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    f.gget(G.prefUniqA).i32(0).store32(0);
    f.i32(0).set(acc).i32(0).set(i);
    f.block().loop();
    f.get(i).get(n).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.A, i).set(id);
    f.get(acc).loadArr8(G.isUniq, id).op(OP.i32_add).set(acc);
    f.get(i).i32(1).op(OP.i32_add).tee(i);
    f.storeArr32(G.prefUniqA, i, () => f.get(acc));
    f.br(0).end().end();

    f.gget(G.prefUniqB).i32(0).store32(0);
    f.i32(0).set(acc).i32(0).set(i);
    f.block().loop();
    f.get(i).get(m).op(OP.i32_ge_u).br_if(1);
    f.loadArr32(G.B, i).tee(id).i32(0).op(OP.i32_ge_s).if_();
    f.get(acc).loadArr8(G.isUniq, id).op(OP.i32_add).set(acc);
    f.end();
    f.get(i).i32(1).op(OP.i32_add).tee(i);
    f.storeArr32(G.prefUniqB, i, () => f.get(acc));
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

    f.block();
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
    f.end();

    f.get(g).i32(1).op(OP.i32_add).set(g);
    f.br(0).end().end();
    f.get(U).tee(lo).gset(G.U);
    f.get(lo);
  });

  // ------------------------------------------------------------------ myersForward() with dominance pruning
  addFunc(F.myersForward, [], [], (f) => {
    const n = f.loc(), m = f.loc(), U = f.loc(), delta = f.loc(), ptr = f.loc();
    const bShift = f.loc(), bStep = f.loc(), bMask = f.loc(), nCkpts = f.loc();
    const x0 = f.loc(), kLo = f.loc(), kHi = f.loc(), hitBound = f.loc(), d = f.loc();
    const remD = f.loc(), lim1 = f.loc(), lim2 = f.loc(), loK = f.loc(), hiK = f.loc(), iLo = f.loc(), iHi = f.loc();
    const idx = f.loc(), k = f.loc(), endIdx = f.loc(), xRem = f.loc(), xAdd = f.loc(), nx = f.loc(), ny = f.loc();
    const canRem = f.loc(), canAdd = f.loc(), qx = f.loc(), qy = f.loc(), cc = f.loc(), tmp = f.loc();
    const pa = f.loc(), pb = f.loc(), exIns = f.loc(), exDel = f.loc();
    const cCount = f.loc(), metaPtr = f.loc(), bytesNeed = f.loc();
    const aBase = f.loc(), bBase = f.loc(), vpBase = f.loc(), vcBase = f.loc();

    f.gget(G.A).set(aBase).gget(G.B).set(bBase);
    f.gget(G.n).set(n).gget(G.m).set(m).gget(G.U).set(U);
    f.get(n).get(m).op(OP.i32_sub).set(delta);
    f.get(U).i32(8192).op(OP.i32_le_s).if_();
    f.i32(6).set(bShift).i32(64).set(bStep).i32(63).set(bMask);
    f.else_();
    f.i32(7).set(bShift).i32(128).set(bStep).i32(127).set(bMask);
    f.end();
    f.get(bShift).gset(G.bShift).get(bStep).gset(G.bStep).get(bMask).gset(G.bMask);

    f.gget(G.arenaPtr).set(ptr);
    f.get(ptr).tee(vpBase).gset(G.Vp).get(ptr).get(U).i32(8).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).tee(vcBase).gset(G.Vc).get(ptr).get(U).i32(8).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.repBuf);
    f.get(ptr).get(bStep).i32(1).op(OP.i32_add).get(bStep).i32(4).op(OP.i32_add).op(OP.i32_mul).i32(2).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(U).get(bShift).op(OP.i32_shr_u).i32(2).op(OP.i32_add).set(nCkpts);
    f.get(ptr).gset(G.ckptMeta).get(ptr).get(nCkpts).i32(4).op(OP.i32_shl).op(OP.i32_add).set(ptr);
    f.get(ptr).gset(G.ckptData).get(ptr).gset(G.ckptDataPtr);
    f.get(ptr).i32(1048576).op(OP.i32_add).tee(tmp).gset(G.ckptCap);
    f.get(tmp).call(F.ensureMem);

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

    // Pushes 1 (valid) or 0 (pruned) for (nx, ny) on diagonal kL
    const emitIsValid = (kL) => {
      f.get(nx).i32(6).op(OP.i32_shl).get(n).op(OP.i32_add).i32(1).op(OP.i32_sub).get(n).op(OP.i32_div_u).set(qx);
      f.get(ny).i32(6).op(OP.i32_shl).get(m).op(OP.i32_add).i32(1).op(OP.i32_sub).get(m).op(OP.i32_div_u).set(qy);
      f.get(qx).i32(65).op(OP.i32_mul).get(qy).op(OP.i32_add).set(tmp);
      f.loadArr32(G.grid64, tmp).set(cc);
      f.loadArr32(G.prefUniqA, nx).set(pa);
      f.loadArr32(G.prefUniqB, ny).set(pb);
      f.get(pa).get(pb).op(OP.i32_gt_s).if_(I32).get(pa).get(pb).op(OP.i32_sub).else_().i32(0).end().set(exIns);
      f.get(pb).get(pa).op(OP.i32_gt_s).if_(I32).get(pb).get(pa).op(OP.i32_sub).else_().i32(0).end().set(exDel);
      return f.loadArr32(G.remIns, ny).get(exIns).op(OP.i32_add).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl)
        .get(lim1).get(kL).op(OP.i32_add).op(OP.i32_le_s)
        .loadArr32(G.remDel, nx).get(exDel).op(OP.i32_add).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl)
        .get(lim2).get(kL).op(OP.i32_sub).op(OP.i32_le_s)
        .op(OP.i32_and);
    };

    f.get(x0).get(n).op(OP.i32_lt_s).get(x0).get(m).op(OP.i32_lt_s).op(OP.i32_or).if_();
    f.i32(1).set(d);
    f.block().loop();
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
    f.get(vpBase).load32(0).set(nx);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.get(vcBase).i32(-2).store32(0);
    f.else_();
    f.get(nx).get(k).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.get(aBase).get(nx).i32(2).op(OP.i32_shl).op(OP.i32_add).load32()
      .get(bBase).get(ny).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_ge_s).get(ny).get(m).op(OP.i32_ge_s).op(OP.i32_or).if_();
    f.i32(1).set(hitBound);
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(k).gset(G.ansK).br(6);
    f.end();
    f.end();
    f.get(vcBase).get(nx).store32(0);
    f.end();
    f.i32(1).set(idx).get(k).i32(2).op(OP.i32_add).set(k);
    f.end();

    f.get(iHi).get(d).get(iHi).get(d).op(OP.i32_lt_s).op(OP.select).set(endIdx);
    f.get(endIdx).get(d).op(OP.i32_eq).if_().get(d).i32(1).op(OP.i32_sub).set(endIdx).end();
    f.get(vpBase).get(idx).i32(1).op(OP.i32_sub).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().set(xRem);

    f.block().loop();
    f.get(idx).get(endIdx).op(OP.i32_gt_s).br_if(1);
    f.get(vpBase).get(idx).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().set(xAdd);
    f.get(xRem).i32(0).op(OP.i32_ge_s).get(xRem).i32(1).op(OP.i32_add).tee(tmp).get(xAdd).op(OP.i32_ge_s).op(OP.i32_and)
      .if_(I32).get(tmp).else_().get(xAdd).end().set(nx);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.get(vcBase).get(idx).i32(2).op(OP.i32_shl).op(OP.i32_add).i32(-2).store32();
    f.else_();
    f.get(nx).get(k).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.get(aBase).get(nx).i32(2).op(OP.i32_shl).op(OP.i32_add).load32()
      .get(bBase).get(ny).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_ge_s).get(ny).get(m).op(OP.i32_ge_s).op(OP.i32_or).if_();
    f.i32(1).set(hitBound);
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(k).gset(G.ansK).br(7);
    f.end();
    f.end();
    f.get(vcBase).get(idx).i32(2).op(OP.i32_shl).op(OP.i32_add).get(nx).store32();
    f.end();
    f.get(xAdd).set(xRem);
    f.get(idx).i32(1).op(OP.i32_add).set(idx);
    f.get(k).i32(2).op(OP.i32_add).set(k);
    f.br(0).end().end();

    f.get(iHi).get(d).op(OP.i32_eq).if_();
    f.get(xRem).i32(0).op(OP.i32_lt_s).if_();
    f.get(vcBase).get(d).i32(2).op(OP.i32_shl).op(OP.i32_add).i32(-2).store32();
    f.else_();
    f.get(xRem).i32(1).op(OP.i32_add).set(nx);
    f.get(nx).get(d).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.get(aBase).get(nx).i32(2).op(OP.i32_shl).op(OP.i32_add).load32()
      .get(bBase).get(ny).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_ge_s).get(ny).get(m).op(OP.i32_ge_s).op(OP.i32_or).if_();
    f.i32(1).set(hitBound);
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(d).gset(G.ansK).br(6);
    f.end();
    f.end();
    f.get(vcBase).get(d).i32(2).op(OP.i32_shl).op(OP.i32_add).get(nx).store32();
    f.end();
    f.end();

    f.else_();
    f.get(iLo).set(idx).get(loK).set(k);
    f.block().loop();
    f.get(idx).get(iHi).op(OP.i32_gt_s).br_if(1);
    f.get(idx).i32(0).op(OP.i32_gt_s).if_(I32).get(vpBase).get(idx).i32(1).op(OP.i32_sub).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().else_().i32(-2).end().set(xRem);
    f.get(idx).get(d).op(OP.i32_lt_s).if_(I32).get(vpBase).get(idx).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().else_().i32(-2).end().set(xAdd);
    f.get(xRem).i32(0).op(OP.i32_ge_s).get(xRem).get(n).op(OP.i32_lt_s).op(OP.i32_and).set(canRem);
    f.get(xAdd).i32(0).op(OP.i32_ge_s).get(xAdd).get(k).op(OP.i32_sub).i32(1).op(OP.i32_sub).get(m).op(OP.i32_lt_s).op(OP.i32_and).set(canAdd);
    f.get(canRem).get(canAdd).op(OP.i32_eqz).get(xRem).i32(1).op(OP.i32_add).get(xAdd).op(OP.i32_ge_s).op(OP.i32_or).op(OP.i32_and)
      .if_(I32).get(xRem).i32(1).op(OP.i32_add)
      .else_().get(canAdd).if_(I32).get(xAdd).else_().i32(-2).end().end().set(nx);
    f.get(nx).i32(0).op(OP.i32_lt_s).if_();
    f.get(vcBase).get(idx).i32(2).op(OP.i32_shl).op(OP.i32_add).i32(-2).store32();
    f.else_();
    f.get(nx).get(k).op(OP.i32_sub).set(ny);
    f.block().loop();
    f.get(aBase).get(nx).i32(2).op(OP.i32_shl).op(OP.i32_add).load32()
      .get(bBase).get(ny).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().op(OP.i32_ne).br_if(1);
    f.get(nx).i32(1).op(OP.i32_add).set(nx);
    f.get(ny).i32(1).op(OP.i32_add).set(ny);
    f.br(0).end().end();
    f.get(nx).get(n).op(OP.i32_eq).get(ny).get(m).op(OP.i32_eq).op(OP.i32_and).if_();
    f.get(d).gset(G.ansD).get(k).gset(G.ansK).br(6);
    f.end();
    f.get(vcBase).get(idx).i32(2).op(OP.i32_shl).op(OP.i32_add).get(nx).store32();
    f.end();
    f.get(idx).i32(1).op(OP.i32_add).set(idx);
    f.get(k).i32(2).op(OP.i32_add).set(k);
    f.br(0).end().end();
    f.end();

    const emitTrimSide = (idxL, kL, stepIdx, stepK) => {
      f.block().loop();
      f.get(iLo).get(iHi).op(OP.i32_gt_s).br_if(1);
      f.get(vcBase).get(idxL).i32(2).op(OP.i32_shl).op(OP.i32_add).load32().set(nx);
      f.get(nx).i32(0).op(OP.i32_ge_s).if_();
      f.get(nx).get(kL).op(OP.i32_sub).set(ny);
      emitIsValid(kL).br_if(2);
      f.get(vcBase).get(idxL).i32(2).op(OP.i32_shl).op(OP.i32_add).i32(-2).store32();
      f.end();
      f.get(idxL).i32(stepIdx).op(OP.i32_add).set(idxL);
      f.get(kL).i32(stepK).op(OP.i32_add).set(kL);
      f.br(0).end().end();
    };
    emitTrimSide(iLo, loK, 1, 2);
    emitTrimSide(iHi, hiK, -1, -2);

    f.get(loK).set(kLo).get(hiK).set(kHi);
    f.get(vpBase).set(tmp).get(vcBase).tee(vpBase).gset(G.Vp).get(tmp).tee(vcBase).gset(G.Vc);

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
    f.end();
  });

  // ------------------------------------------------------------------ replayPath()
  addFunc(F.replayPath, [], [], (f) => {
    const n = f.loc(), m = f.loc(), U = f.loc(), delta = f.loc(), ansD = f.loc(), ptr = f.loc();
    const bShift = f.loc(), bStep = f.loc(), stride = f.loc(), opLen = f.loc();
    const curD = f.loc(), curK = f.loc(), curX = f.loc();
    const bIdx = f.loc(), d0 = f.loc(), span = f.loc();
    const metaPtr = f.loc(), ckData = f.loc(), ckILo = f.loc(), fLo0 = f.loc(), fHi0 = f.loc();
    const baseK0 = f.loc(), rLo0 = f.loc(), rHi0 = f.loc(), k = f.loc();
    const pLo = f.loc(), pHi = f.loc(), s = f.loc(), d = f.loc(), remD = f.loc(), lim1 = f.loc(), lim2 = f.loc();
    const wLo = f.loc(), wHi = f.loc(), rLo = f.loc(), rHi = f.loc(), prevRow = f.loc(), curRow = f.loc(), shiftBase = f.loc();
    const cILo = f.loc(), cIHi = f.loc(), col = f.loc(), xRem = f.loc(), xAdd = f.loc(), canRem = f.loc(), canAdd = f.loc(), nx = f.loc(), ny = f.loc();
    const qx = f.loc(), qy = f.loc(), cc = f.loc(), pa = f.loc(), pb = f.loc(), exIns = f.loc(), exDel = f.loc(), tmp = f.loc();
    const traceX = f.loc(), traceK = f.loc(), startX = f.loc(), opK = f.loc(), nextK = f.loc(), prevX = f.loc(), keep = f.loc();

    f.gget(G.n).set(n).gget(G.m).set(m).gget(G.U).set(U).gget(G.ansD).set(ansD);
    f.get(n).get(m).op(OP.i32_sub).set(delta);
    f.gget(G.bShift).set(bShift).gget(G.bStep).set(bStep);
    f.get(bStep).i32(4).op(OP.i32_add).set(stride);

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
      f.loadArr32(G.prefUniqA, nx).set(pa);
      f.loadArr32(G.prefUniqB, ny).set(pb);
      f.get(pa).get(pb).op(OP.i32_gt_s).if_(I32).get(pa).get(pb).op(OP.i32_sub).else_().i32(0).end().set(exIns);
      f.get(pb).get(pa).op(OP.i32_gt_s).if_(I32).get(pb).get(pa).op(OP.i32_sub).else_().i32(0).end().set(exDel);
      f.loadArr32(G.remIns, ny).get(exIns).op(OP.i32_add).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl).get(lim1).get(kL).op(OP.i32_add).op(OP.i32_le_s)
        .loadArr32(G.remDel, nx).get(exDel).op(OP.i32_add).get(cc).op(OP.i32_add).i32(1).op(OP.i32_shl).get(lim2).get(kL).op(OP.i32_sub).op(OP.i32_le_s)
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

  // ------------------------------------------------------------------ buildChangesAndHunks()
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

  // ------------------------------------------------------------------ writeDec(outPtr, val) -> newOutPtr
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

  // ------------------------------------------------------------------ pushLineOut(outPtr, base, s, e, opByte) -> newOutPtr
  addFunc(F.pushLineOut, [I32, I32, I32, I32, I32], [I32], (f) => {
    const out = 0, base = 1, s = 2, e = 3, opB = 4;
    const len = f.loc();
    f.get(out).get(opB).store8();
    f.get(out).i32(1).op(OP.i32_add).set(out);
    f.get(e).get(s).op(OP.i32_sub).set(len);
    f.get(out).get(base).get(s).op(OP.i32_add).get(len).memCopy();
    f.get(out).get(len).op(OP.i32_add).set(out);
    f.get(base).get(e).op(OP.i32_add).i32(1).op(OP.i32_sub).load8().i32(10).op(OP.i32_ne).if_();
    f.get(out).i32(10).store8(0);
    f.get(out).i32(37).store8(1);
    f.get(out).i32(10).store8(2);
    f.get(out).i32(3).op(OP.i32_add).set(out);
    f.end();
    f.get(out);
  });

  // ------------------------------------------------------------------ buildPatch()
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

    f.gget(G.arenaPtr).set(ptr);
    f.get(ptr).set(preArr); f.get(ptr).i32(16).op(OP.i32_add).set(ptr);
    f.get(ptr).set(sufArr); f.get(ptr).i32(16).op(OP.i32_add).set(ptr);
    f.get(ptr).tee(outBase).gset(G.outBase);
    f.get(oLen).gget(G.nLen).op(OP.i32_add)
      .get(totalOld).get(totalNew).op(OP.i32_add).i32(2).op(OP.i32_shl).op(OP.i32_add)
      .get(nh).i32(6).op(OP.i32_shl).op(OP.i32_add)
      .i32(512).op(OP.i32_add).set(maxBytes);
    f.get(outBase).get(maxBytes).op(OP.i32_add).call(F.ensureMem);

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
    emitPushOld(at, 61);
    f.get(at).i32(1).op(OP.i32_add).set(at);
    f.br(0).end().end();

    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(cd).op(OP.i32_ge_s).br_if(1);
    f.get(co).get(i).op(OP.i32_add).set(at);
    emitPushOld(at, 45);
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    f.i32(0).set(i);
    f.block().loop();
    f.get(i).get(cins).op(OP.i32_ge_s).br_if(1);
    f.get(cp).get(i).op(OP.i32_add).get(prefix).op(OP.i32_sub).set(mi);
    f.get(ptr).get(nBase).loadArr32(G.nStarts, mi).loadArr32(G.nEnds, mi).i32(43).call(F.pushLineOut).set(ptr);
    f.get(i).i32(1).op(OP.i32_add).set(i);
    f.br(0).end().end();

    f.get(co).get(cd).op(OP.i32_add).set(at);
    f.get(ci).i32(1).op(OP.i32_add).set(ci);
    f.br(0).end().end();

    f.block().loop();
    f.get(at).get(oldEnd).op(OP.i32_ge_s).br_if(1);
    emitPushOld(at, 61);
    f.get(at).i32(1).op(OP.i32_add).set(at);
    f.br(0).end().end();

    f.get(hi).i32(1).op(OP.i32_add).set(hi);
    f.br(0).end().end();
    f.get(ptr).gset(G.outEnd);
  });

  // ------------------------------------------------------------------ solveAscii() -> outLen
  addFunc(F.solveAscii, [], [I32], (f) => {
    f.call(F.trimPrefixSuffix);
    f.gget(G.oStart).gget(G.oEnd).op(OP.i32_eq).gget(G.nStart).gget(G.nEnd).op(OP.i32_eq).op(OP.i32_and).if_();
    f.i32(0).gset(G.n).i32(0).gset(G.m).i32(0).gset(G.numHunks).i32(0).gset(G.deleted).i32(0).gset(G.inserted);
    f.gget(G.arenaBase).gset(G.arenaPtr);
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
  addFunc(F.getBatchOutBase, [], [I32], (f) => f.gget(G.batchOutBase));

  // ------------------------------------------------------------------ skipWs(pos, end) -> pos
  addFunc(F.skipWs, [I32, I32], [I32], (f) => {
    const pos = 0, end = 1, b = f.loc();
    f.block().loop();
    f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
    f.get(pos).load8().tee(b);
    f.i32(32).op(OP.i32_eq)
      .get(b).i32(9).op(OP.i32_eq).op(OP.i32_or)
      .get(b).i32(10).op(OP.i32_eq).op(OP.i32_or)
      .get(b).i32(13).op(OP.i32_eq).op(OP.i32_or)
      .op(OP.i32_eqz).br_if(1);
    f.get(pos).i32(1).op(OP.i32_add).set(pos);
    f.br(0).end().end();
    f.get(pos);
  });

  // ------------------------------------------------------------------ skipJsonStr(pos, end) -> newPos or -1
  addFunc(F.skipJsonStr, [I32, I32], [I32], (f) => {
    const pos = 0, end = 1, b = f.loc();
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().i32(34).op(OP.i32_ne).if_().i32(-1).ret().end();
    f.get(pos).i32(1).op(OP.i32_add).set(pos);
    f.block().loop();
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().set(b);
    f.get(b).i32(34).op(OP.i32_eq).if_().get(pos).i32(1).op(OP.i32_add).ret().end();
    f.get(b).i32(92).op(OP.i32_eq).if_();
    f.get(pos).i32(1).op(OP.i32_add).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).i32(1).op(OP.i32_add).load8().i32(117).op(OP.i32_eq).if_(); // '\u' -> fallback if non-ascii possible, skip 6 or check
    f.get(pos).i32(2).op(OP.i32_add).set(pos);
    f.else_();
    f.get(pos).i32(2).op(OP.i32_add).set(pos);
    f.end();
    f.br(1);
    f.end();
    f.get(b).i32(32).op(OP.i32_lt_u).get(b).i32(127).op(OP.i32_gt_u).op(OP.i32_or).if_().i32(-1).ret().end();
    f.get(pos).i32(1).op(OP.i32_add).set(pos);
    f.br(0).end().end();
    f.i32(-1);
  });

  // ------------------------------------------------------------------ unescapeJsonStr(src, end, dstBase) -> len or -1 (updates G.jsonCur)
  addFunc(F.unescapeJsonStr, [I32, I32, I32], [I32], (f) => {
    const src = 0, end = 1, dstBase = 2;
    const dst = f.loc(), end16 = f.loc(), mask = f.loc(), k = f.loc(), b = f.loc(), esc = f.loc(), h1 = f.loc(), h2 = f.loc();
    const q16 = f.loc(V128), bs16 = f.loc(V128), sp16 = f.loc(V128), v = f.loc(V128);

    f.get(src).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(src).load8().i32(34).op(OP.i32_ne).if_().i32(-1).ret().end();
    f.get(src).i32(1).op(OP.i32_add).set(src);
    f.get(dstBase).set(dst);
    f.get(end).i32(16).op(OP.i32_sub).set(end16);
    f.i32(34).vsplat8().set(q16);
    f.i32(92).vsplat8().set(bs16);
    f.i32(32).vsplat8().set(sp16);

    const emitHex = (chL, outL) => {
      f.get(chL).i32(48).op(OP.i32_sub).tee(outL).i32(9).op(OP.i32_le_u).if_();
      f.else_();
      f.get(chL).i32(32).op(OP.i32_or).i32(87).op(OP.i32_sub).tee(outL);
      f.i32(10).op(OP.i32_lt_u).get(outL).i32(15).op(OP.i32_gt_u).op(OP.i32_or).if_().i32(-1).ret().end();
      f.end();
    };

    const emitHandleEsc = () => {
      f.get(src).i32(1).op(OP.i32_add).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
      f.get(src).i32(1).op(OP.i32_add).load8().set(esc);
      f.get(esc).i32(34).op(OP.i32_eq).if_().get(dst).i32(34).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(92).op(OP.i32_eq).if_().get(dst).i32(92).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(110).op(OP.i32_eq).if_().get(dst).i32(10).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(114).op(OP.i32_eq).if_().get(dst).i32(13).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(116).op(OP.i32_eq).if_().get(dst).i32(9).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(98).op(OP.i32_eq).if_().get(dst).i32(8).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(102).op(OP.i32_eq).if_().get(dst).i32(12).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(47).op(OP.i32_eq).if_().get(dst).i32(47).store8().get(src).i32(2).op(OP.i32_add).set(src).get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().get(esc).i32(117).op(OP.i32_eq).if_();
      // \u00XX where XX < 0x80
      f.get(src).i32(5).op(OP.i32_add).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
      f.get(src).load8(2).i32(48).op(OP.i32_ne).get(src).load8(3).i32(48).op(OP.i32_ne).op(OP.i32_or).if_().i32(-1).ret().end();
      f.get(src).load8(4).set(b); emitHex(b, h1);
      f.get(h1).i32(7).op(OP.i32_gt_u).if_().i32(-1).ret().end();
      f.get(src).load8(5).set(b); emitHex(b, h2);
      f.get(dst).get(h1).i32(4).op(OP.i32_shl).get(h2).op(OP.i32_or).store8();
      f.get(src).i32(6).op(OP.i32_add).set(src);
      f.get(dst).i32(1).op(OP.i32_add).set(dst);
      f.else_().i32(-1).ret().end();
      f.end().end().end().end().end().end().end().end();
    };

    // SIMD128 16-byte loop
    f.block().loop();
    f.get(src).get(end16).op(OP.i32_gt_s).br_if(1);
    f.get(src).vload().tee(v);
    f.get(v).get(q16).veq8()
      .get(v).get(bs16).veq8().vor()
      .get(v).get(sp16).vlts8().vor()
      .vbitmask8().tee(mask).op(OP.i32_eqz).if_();
    f.get(dst).get(v).vstore();
    f.get(src).i32(16).op(OP.i32_add).set(src);
    f.get(dst).i32(16).op(OP.i32_add).set(dst);
    f.br(1);
    f.end();
    f.get(mask).op(OP.i32_ctz).tee(k).if_();
    f.get(dst).get(v).vstore();
    f.get(src).get(k).op(OP.i32_add).set(src);
    f.get(dst).get(k).op(OP.i32_add).set(dst);
    f.end();
    f.get(src).load8().set(b);
    f.get(b).i32(34).op(OP.i32_eq).if_();
    f.get(src).i32(1).op(OP.i32_add).gset(G.jsonCur);
    f.get(dst).get(dstBase).op(OP.i32_sub).ret();
    f.end();
    f.get(b).i32(92).op(OP.i32_ne).if_().i32(-1).ret().end();
    emitHandleEsc();
    f.br(0).end().end();

    // Byte tail (< 16 bytes remaining)
    f.block().loop();
    f.get(src).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(src).load8().set(b);
    f.get(b).i32(34).op(OP.i32_eq).if_();
    f.get(src).i32(1).op(OP.i32_add).gset(G.jsonCur);
    f.get(dst).get(dstBase).op(OP.i32_sub).ret();
    f.end();
    f.get(b).i32(92).op(OP.i32_eq).if_();
    emitHandleEsc();
    f.br(1);
    f.end();
    f.get(b).i32(32).op(OP.i32_lt_u).get(b).i32(127).op(OP.i32_gt_u).op(OP.i32_or).if_().i32(-1).ret().end();
    f.get(dst).get(b).store8();
    f.get(src).i32(1).op(OP.i32_add).set(src);
    f.get(dst).i32(1).op(OP.i32_add).set(dst);
    f.br(0).end().end();
    f.i32(-1);
  });

  // ------------------------------------------------------------------ escapeJsonOut(src, len, dst) -> newDst (SIMD128)
  addFunc(F.escapeJsonOut, [I32, I32, I32], [I32], (f) => {
    const src = 0, len = 1, dst = 2;
    const end = f.loc(), end16 = f.loc(), mask = f.loc(), k = f.loc(), b = f.loc(), h1 = f.loc(), h2 = f.loc();
    const q16 = f.loc(V128), bs16 = f.loc(V128), sp16 = f.loc(V128), v = f.loc(V128);

    f.get(dst).i32(34).store8();
    f.get(dst).i32(1).op(OP.i32_add).set(dst);
    f.get(src).get(len).op(OP.i32_add).tee(end).i32(16).op(OP.i32_sub).set(end16);
    f.i32(34).vsplat8().set(q16);
    f.i32(92).vsplat8().set(bs16);
    f.i32(32).vsplat8().set(sp16);

    const emitEscByte = () => {
      f.get(b).i32(10).op(OP.i32_eq).if_().get(dst).i32(92).store8(0).get(dst).i32(110).store8(1).get(dst).i32(2).op(OP.i32_add).set(dst);
      f.else_().get(b).i32(34).op(OP.i32_eq).if_().get(dst).i32(92).store8(0).get(dst).i32(34).store8(1).get(dst).i32(2).op(OP.i32_add).set(dst);
      f.else_().get(b).i32(92).op(OP.i32_eq).if_().get(dst).i32(92).store8(0).get(dst).i32(92).store8(1).get(dst).i32(2).op(OP.i32_add).set(dst);
      f.else_().get(b).i32(13).op(OP.i32_eq).if_().get(dst).i32(92).store8(0).get(dst).i32(114).store8(1).get(dst).i32(2).op(OP.i32_add).set(dst);
      f.else_().get(b).i32(9).op(OP.i32_eq).if_().get(dst).i32(92).store8(0).get(dst).i32(116).store8(1).get(dst).i32(2).op(OP.i32_add).set(dst);
      f.else_().get(b).i32(8).op(OP.i32_eq).if_().get(dst).i32(92).store8(0).get(dst).i32(98).store8(1).get(dst).i32(2).op(OP.i32_add).set(dst);
      f.else_().get(b).i32(12).op(OP.i32_eq).if_().get(dst).i32(92).store8(0).get(dst).i32(102).store8(1).get(dst).i32(2).op(OP.i32_add).set(dst);
      f.else_();
      // \u00XX
      f.get(dst).i32(92).store8(0).get(dst).i32(117).store8(1).get(dst).i32(48).store8(2).get(dst).i32(48).store8(3);
      f.get(b).i32(4).op(OP.i32_shr_u).i32(48).op(OP.i32_add).set(h1);
      f.get(b).i32(15).op(OP.i32_and).tee(h2).i32(10).op(OP.i32_lt_u).if_(I32).get(h2).i32(48).op(OP.i32_add).else_().get(h2).i32(87).op(OP.i32_add).end().set(h2);
      f.get(dst).get(h1).store8(4).get(dst).get(h2).store8(5).get(dst).i32(6).op(OP.i32_add).set(dst);
      f.end().end().end().end().end().end().end();
    };

    f.block().loop();
    f.get(src).get(end16).op(OP.i32_gt_s).br_if(1);
    f.get(src).vload().tee(v);
    f.get(v).get(q16).veq8()
      .get(v).get(bs16).veq8().vor()
      .get(v).get(sp16).vlts8().vor()
      .vbitmask8().tee(mask).op(OP.i32_eqz).if_();
    f.get(dst).get(v).vstore();
    f.get(src).i32(16).op(OP.i32_add).set(src);
    f.get(dst).i32(16).op(OP.i32_add).set(dst);
    f.br(1);
    f.end();
    f.get(mask).op(OP.i32_ctz).tee(k).if_();
    f.get(dst).get(v).vstore();
    f.get(src).get(k).op(OP.i32_add).set(src);
    f.get(dst).get(k).op(OP.i32_add).set(dst);
    f.end();
    f.get(src).load8().set(b);
    f.get(src).i32(1).op(OP.i32_add).set(src);
    emitEscByte();
    f.br(0).end().end();

    f.block().loop();
    f.get(src).get(end).op(OP.i32_ge_u).br_if(1);
    f.get(src).load8().set(b);
    f.get(src).i32(1).op(OP.i32_add).set(src);
    f.get(b).i32(34).op(OP.i32_eq).get(b).i32(92).op(OP.i32_eq).op(OP.i32_or).get(b).i32(32).op(OP.i32_lt_u).op(OP.i32_or).if_();
    emitEscByte();
    f.else_();
    f.get(dst).get(b).store8();
    f.get(dst).i32(1).op(OP.i32_add).set(dst);
    f.end();
    f.br(0).end().end();

    f.get(dst).i32(34).store8();
    f.get(dst).i32(1).op(OP.i32_add);
  });

  // ------------------------------------------------------------------ solveBatchJson() -> batchOutLen or -1
  addFunc(F.solveBatchJson, [], [I32], (f) => {
    const end = f.loc(), pos = f.loc(), batchOutBase = f.loc(), batchPtr = f.loc(), caseIdx = f.loc();
    const seenInput = f.loc(), oLen = f.loc(), nLen = f.loc(), oBase = f.loc(), nBase = f.loc();
    const buf1 = f.loc(), len1 = f.loc(), outLen = f.loc(), outBase = f.loc(), outEnd = f.loc(), minBase = f.loc();
    const tmpDst = f.loc(), tmpEnd = f.loc(), escLen = f.loc(), b = f.loc(), isOld = f.loc(), ab = f.loc();

    f.gget(G.jsonLen).set(end);
    f.i32(0).get(end).call(F.skipWs).set(pos);
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().i32(91).op(OP.i32_ne).if_().i32(-1).ret().end(); // '['
    f.get(pos).i32(1).op(OP.i32_add).get(end).call(F.skipWs).set(pos);

    f.get(end).i32(31).op(OP.i32_add).i32(-16).op(OP.i32_and).tee(batchOutBase).gset(G.batchOutBase);
    f.get(batchOutBase).i32(1024).op(OP.i32_add).call(F.ensureMem);
    f.get(batchOutBase).set(batchPtr);
    f.get(batchPtr).i32(91).store8();
    f.get(batchPtr).i32(1).op(OP.i32_add).set(batchPtr);

    // Empty array []
    f.get(pos).get(end).op(OP.i32_lt_u).if_();
    f.get(pos).load8().i32(93).op(OP.i32_eq).if_();
    f.get(pos).i32(1).op(OP.i32_add).get(end).call(F.skipWs).get(end).op(OP.i32_ne).if_().i32(-1).ret().end();
    f.get(batchPtr).i32(93).store8();
    f.get(batchPtr).i32(1).op(OP.i32_add).get(batchOutBase).op(OP.i32_sub).ret();
    f.end();
    f.end();

    const expectByte = (ch) => {
      f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
      f.get(pos).load8().i32(ch).op(OP.i32_ne).if_().i32(-1).ret().end();
      f.get(pos).i32(1).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    };

    f.i32(0).set(caseIdx);
    f.block().loop();
    f.get(caseIdx).i32(0).op(OP.i32_gt_s).if_();
    f.get(batchPtr).i32(16).op(OP.i32_add).call(F.ensureMem);
    f.get(batchPtr).i32(44).store8();
    f.get(batchPtr).i32(1).op(OP.i32_add).set(batchPtr);
    f.end();

    expectByte(123); // '{'
    f.i32(0).set(seenInput).i32(-1).set(oLen).i32(-1).set(nLen);

    // Outer object keys
    f.block().loop();
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().i32(125).op(OP.i32_eq).br_if(1);

    // Check key: "input" | "id" | "group"
    f.get(pos).i32(7).op(OP.i32_add).get(end).op(OP.i32_le_u)
      .if_(I32)
      .get(pos).load32u(0).i32(0x706e6922).op(OP.i32_eq)
      .get(pos).load32u(3).i32(0x22747570).op(OP.i32_eq).op(OP.i32_and)
      .else_().i32(0).end()
      .if_();
    // "input"
    f.get(seenInput).if_().i32(-1).ret().end();
    f.i32(1).set(seenInput);
    f.get(pos).i32(7).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    expectByte(58); // ':'
    expectByte(123); // '{'

    // Inner { "old": ..., "new": ... }
    f.get(batchPtr).i32(31).op(OP.i32_add).i32(-16).op(OP.i32_and).set(buf1);
    f.i32(0).set(len1);
    f.block().loop();
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().i32(125).op(OP.i32_eq).br_if(1);
    f.get(pos).i32(5).op(OP.i32_add).get(end).op(OP.i32_gt_u).if_().i32(-1).ret().end();
    f.get(pos).load8(4).i32(34).op(OP.i32_ne).if_().i32(-1).ret().end();
    f.get(pos).load32u(0).i32(0x646c6f22).op(OP.i32_eq).if_();
    f.i32(1).set(isOld);
    f.else_().get(pos).load32u(0).i32(0x77656e22).op(OP.i32_eq).if_();
    f.i32(0).set(isOld);
    f.else_().i32(-1).ret().end().end();

    f.get(isOld).if_().get(oLen).i32(0).op(OP.i32_ge_s).if_().i32(-1).ret().end();
    f.else_().get(nLen).i32(0).op(OP.i32_ge_s).if_().i32(-1).ret().end().end();

    f.get(pos).i32(5).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    expectByte(58); // ':'

    f.get(oLen).i32(0).op(OP.i32_lt_s).get(nLen).i32(0).op(OP.i32_lt_s).op(OP.i32_and).if_();
    // First string goes at buf1
    f.get(buf1).get(end).get(pos).op(OP.i32_sub).op(OP.i32_add).i32(64).op(OP.i32_add).call(F.ensureMem);
    f.get(pos).get(end).get(buf1).call(F.unescapeJsonStr).tee(len1).i32(0).op(OP.i32_lt_s).if_().i32(-1).ret().end();
    f.get(isOld).if_().get(buf1).set(oBase).get(len1).set(oLen);
    f.else_().get(buf1).set(nBase).get(len1).set(nLen).end();
    f.else_();
    // Second string goes after buf1 + len1
    f.get(buf1).get(len1).op(OP.i32_add).i32(31).op(OP.i32_add).i32(-16).op(OP.i32_and).set(ab);
    f.get(ab).get(end).get(pos).op(OP.i32_sub).op(OP.i32_add).i32(64).op(OP.i32_add).call(F.ensureMem);
    f.get(pos).get(end).get(ab).call(F.unescapeJsonStr).tee(tmpEnd).i32(0).op(OP.i32_lt_s).if_().i32(-1).ret().end();
    f.get(isOld).if_().get(ab).set(oBase).get(tmpEnd).set(oLen);
    f.else_().get(ab).set(nBase).get(tmpEnd).set(nLen).end();
    f.end();

    f.gget(G.jsonCur).get(end).call(F.skipWs).set(pos);
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().i32(44).op(OP.i32_eq).if_();
    f.get(pos).i32(1).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    f.br(1);
    f.end();
    f.br(1).end().end();
    expectByte(125); // '}'

    f.else_();
    // Check "id" or "group"
    f.get(pos).i32(4).op(OP.i32_add).get(end).op(OP.i32_le_u)
      .if_(I32).get(pos).load32u(0).i32(0x22646922).op(OP.i32_eq).else_().i32(0).end()
      .if_();
    f.get(pos).i32(4).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    f.else_().get(pos).i32(7).op(OP.i32_add).get(end).op(OP.i32_le_u)
      .if_(I32).get(pos).load32u(0).i32(0x6f726722).op(OP.i32_eq).get(pos).load32u(3).i32(0x2270756f).op(OP.i32_eq).op(OP.i32_and).else_().i32(0).end()
      .if_();
    f.get(pos).i32(7).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    f.else_().i32(-1).ret().end().end();

    expectByte(58); // ':'
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().i32(34).op(OP.i32_eq).if_();
    f.get(pos).get(end).call(F.skipJsonStr).tee(pos).i32(0).op(OP.i32_lt_s).if_().i32(-1).ret().end();
    f.else_();
    // Skip integer id
    f.get(pos).load8().i32(45).op(OP.i32_eq).if_().get(pos).i32(1).op(OP.i32_add).set(pos).end();
    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().tee(b).i32(48).op(OP.i32_lt_u).get(b).i32(57).op(OP.i32_gt_u).op(OP.i32_or).if_().i32(-1).ret().end();
    f.block().loop();
    f.get(pos).get(end).op(OP.i32_ge_u).br_if(1);
    f.get(pos).load8().tee(b).i32(48).op(OP.i32_lt_u).get(b).i32(57).op(OP.i32_gt_u).op(OP.i32_or).br_if(1);
    f.get(pos).i32(1).op(OP.i32_add).set(pos);
    f.br(0).end().end();
    f.end();
    f.get(pos).get(end).call(F.skipWs).set(pos);
    f.end();

    f.get(pos).get(end).op(OP.i32_ge_u).if_().i32(-1).ret().end();
    f.get(pos).load8().i32(44).op(OP.i32_eq).if_();
    f.get(pos).i32(1).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    f.br(1);
    f.end();
    f.br(1).end().end();
    expectByte(125); // '}'

    f.get(seenInput).op(OP.i32_eqz).get(oLen).i32(0).op(OP.i32_lt_s).op(OP.i32_or).get(nLen).i32(0).op(OP.i32_lt_s).op(OP.i32_or).if_().i32(-1).ret().end();

    // Solve current case in WASM
    f.get(oBase).gset(G.oBase).get(oLen).gset(G.oLen).get(nBase).gset(G.nBase).get(nLen).gset(G.nLen);
    f.get(oBase).get(oLen).op(OP.i32_add).tee(ab);
    f.get(nBase).get(nLen).op(OP.i32_add).tee(tmpDst);
    f.get(ab).get(tmpDst).op(OP.i32_gt_u).op(OP.select).i32(31).op(OP.i32_add).i32(-16).op(OP.i32_and).gset(G.arenaBase);

    f.call(F.solveAscii).set(outLen);
    f.gget(G.outBase).set(outBase);
    f.gget(G.outEnd).set(outEnd);

    // Check if escaping directly to batchPtr cannot reach outBase
    f.get(batchPtr).get(outLen).i32(6).op(OP.i32_mul).op(OP.i32_add).i32(64).op(OP.i32_add).get(outBase).op(OP.i32_le_u).if_();
    f.get(outBase).get(outLen).get(batchPtr).call(F.escapeJsonOut).set(batchPtr);
    f.else_();
    f.get(outEnd).i32(31).op(OP.i32_add).i32(-16).op(OP.i32_and).set(tmpDst);
    f.get(tmpDst).get(outLen).i32(6).op(OP.i32_mul).op(OP.i32_add).i32(64).op(OP.i32_add).call(F.ensureMem);
    f.get(outBase).get(outLen).get(tmpDst).call(F.escapeJsonOut).set(tmpEnd);
    f.get(tmpEnd).get(tmpDst).op(OP.i32_sub).set(escLen);
    f.get(batchPtr).get(tmpDst).get(escLen).memCopy();
    f.get(batchPtr).get(escLen).op(OP.i32_add).set(batchPtr);
    f.end();

    f.get(caseIdx).i32(1).op(OP.i32_add).set(caseIdx);
    f.get(pos).get(end).op(OP.i32_lt_u).if_();
    f.get(pos).load8().i32(44).op(OP.i32_eq).if_();
    f.get(pos).i32(1).op(OP.i32_add).get(end).call(F.skipWs).set(pos);
    f.br(2);
    f.end();
    f.end();
    f.br(1).end().end();

    expectByte(93); // ']'
    f.get(pos).get(end).op(OP.i32_ne).if_().i32(-1).ret().end();
    f.get(batchPtr).i32(16).op(OP.i32_add).call(F.ensureMem);
    f.get(batchPtr).i32(93).store8();
    f.get(batchPtr).i32(1).op(OP.i32_add).get(batchOutBase).op(OP.i32_sub);
  });

  // Encode WASM module into a single preallocated Uint8Array
  const out = new Uint8Array(65536);
  let p = 0;
  out[p++] = 0x00; out[p++] = 0x61; out[p++] = 0x73; out[p++] = 0x6d;
  out[p++] = 0x01; out[p++] = 0x00; out[p++] = 0x00; out[p++] = 0x00;

  const beginSec = (id) => {
    out[p++] = id;
    const lenPos = p;
    p += 5; // reserve 5-byte padded uleb128 length
    return lenPos;
  };
  const endSec = (lenPos) => {
    let len = p - (lenPos + 5);
    for (let i = 0; i < 4; i++) {
      out[lenPos + i] = (len & 0x7f) | 0x80;
      len >>>= 7;
    }
    out[lenPos + 4] = len & 0x7f;
  };

  // Type section (1)
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

  // Function section (3)
  lp = beginSec(3);
  p = writeUleb(out, p, funcs.length);
  for (let i = 0; i < funcs.length; i++) p = writeUleb(out, p, funcs[i].typeIdx);
  endSec(lp);

  // Memory section (5): min 256 pages (16 MiB)
  lp = beginSec(5);
  out[p++] = 0x01; out[p++] = 0x00;
  p = writeUleb(out, p, 256);
  endSec(lp);

  // Global section (6)
  lp = beginSec(6);
  p = writeUleb(out, p, globalCount);
  for (let i = 0; i < globalCount; i++) {
    out[p++] = I32; out[p++] = 0x01; out[p++] = OP.i32_const; out[p++] = 0x00; out[p++] = OP.end;
  }
  endSec(lp);

  // Export section (7)
  const exports = [
    ['memory', 0x02, 0],
    ['prepareInput', 0x00, F.prepareInput],
    ['prepareBatch', 0x00, F.prepareBatch],
    ['solveAscii', 0x00, F.solveAscii],
    ['solveBatchJson', 0x00, F.solveBatchJson],
    ['getOutBase', 0x00, F.getOutBase],
    ['getBatchOutBase', 0x00, F.getBatchOutBase],
  ];
  lp = beginSec(7);
  p = writeUleb(out, p, exports.length);
  for (let i = 0; i < exports.length; i++) {
    const [name, kind, idx] = exports[i];
    p = writeUleb(out, p, name.length);
    for (let j = 0; j < name.length; j++) out[p++] = name.charCodeAt(j);
    out[p++] = kind;
    p = writeUleb(out, p, idx);
  }
  endSec(lp);

  // Code section (10)
  lp = beginSec(10);
  p = writeUleb(out, p, funcs.length);
  const tmpLoc = new Uint8Array(64);
  for (let i = 0; i < funcs.length; i++) {
    const em = funcs[i].emitter;
    const locs = em.locals;
    let lp2 = 0;
    const groups = [];
    for (let j = 0; j < locs.length; j++) {
      const t = locs[j];
      if (groups.length > 0 && groups[groups.length - 1][1] === t) groups[groups.length - 1][0]++;
      else groups.push([1, t]);
    }
    lp2 = writeUleb(tmpLoc, lp2, groups.length);
    for (let j = 0; j < groups.length; j++) {
      lp2 = writeUleb(tmpLoc, lp2, groups[j][0]);
      tmpLoc[lp2++] = groups[j][1];
    }
    p = writeUleb(out, p, lp2 + em.pos);
    out.set(tmpLoc.subarray(0, lp2), p);
    p += lp2;
    out.set(em.buf.subarray(0, em.pos), p);
    p += em.pos;
  }
  endSec(lp);

  const mod = new WebAssembly.Module(out.subarray(0, p));
  return new WebAssembly.Instance(mod).exports;
}
