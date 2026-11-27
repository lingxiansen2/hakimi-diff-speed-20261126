export const FORMAT = 'makefun-diff/1';
export const CONTEXT = 3;

const KEEP = 0;
const DELETE = 1;
const INSERT = 2;
const B_SHIFT = 5;
const B_STEP = 1 << B_SHIFT;
const B_MASK = B_STEP - 1;
const GRID_N = 64;
const GRID_S = GRID_N + 1;

// Reusable module-level scratch buffers (completely overwritten/zeroed per call; zero cross-case state)
let oStarts = new Int32Array(45000);
let oEnds = new Int32Array(45000);
let oHash = new Int32Array(45000);
let nStarts = new Int32Array(45000);
let nEnds = new Int32Array(45000);
let nHash = new Int32Array(45000);

let buckets = new Int32Array(131072);
let A = new Int32Array(45005);
let B = new Int32Array(45005);
let cntA = new Int32Array(45000);
let cntB = new Int32Array(45000);
let posB = new Int32Array(45000);
let seen = new Int32Array(45000);
let remDel = new Int32Array(45005);
let remIns = new Int32Array(45005);

let tailsVal = new Int32Array(45005);
let tailsA = new Int32Array(45005);
let prevIdx = new Int32Array(45005);
let ancA = new Int32Array(45005);
let ancB = new Int32Array(45005);
let isUniq = new Uint8Array(45000);
let inLIS = new Uint8Array(45005);
let usedLIS = new Uint8Array(45005);
const grid64 = new Int32Array(GRID_S * GRID_S);

let Vp = new Int32Array(8192);
let Vc = new Int32Array(8192);
let gVp = new Int32Array(520);
let gVc = new Int32Array(520);
let repBuf = new Int32Array((B_STEP + 1) * (B_STEP + 4));
let revKind = new Uint8Array(16384);
let revCount = new Int32Array(16384);

function ensureNM(nCap, mCap) {
  if (nCap > oStarts.length) {
    const c = nCap + 1024;
    oStarts = new Int32Array(c);
    oEnds = new Int32Array(c);
    oHash = new Int32Array(c);
    A = new Int32Array(c + 4);
    cntA = new Int32Array(c);
    cntB = new Int32Array(c);
    posB = new Int32Array(c);
    seen = new Int32Array(c);
    remDel = new Int32Array(c + 4);
    prevIdx = new Int32Array(c + 4);
    isUniq = new Uint8Array(c);
    inLIS = new Uint8Array(c + 4);
  }
  if (mCap > nStarts.length) {
    const c = mCap + 1024;
    nStarts = new Int32Array(c);
    nEnds = new Int32Array(c);
    nHash = new Int32Array(c);
    B = new Int32Array(c + 4);
    remIns = new Int32Array(c + 4);
  }
  const minC = nCap < mCap ? nCap : mCap;
  if (minC + 4 > tailsVal.length) {
    const c = minC + 1024;
    tailsVal = new Int32Array(c);
    tailsA = new Int32Array(c);
    ancA = new Int32Array(c);
    ancB = new Int32Array(c);
    usedLIS = new Uint8Array(c);
  }
}

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

function trimAndScanAscii(oBuf, nBuf, oLen, nLen) {
  // 1. Common prefix
  let oStart = 0;
  let nStart = 0;
  let prefix = 0;
  while (oStart < oLen && nStart < nLen) {
    const oNl = oBuf.indexOf(10, oStart);
    const nNl = nBuf.indexOf(10, nStart);
    const oEndL = oNl === -1 ? oLen : oNl + 1;
    const nEndL = nNl === -1 ? nLen : nNl + 1;
    const len = oEndL - oStart;
    if (len !== nEndL - nStart) break;
    let k = 0;
    for (; k + 4 <= len; k += 4) {
      if (
        oBuf[oStart + k] !== nBuf[nStart + k] ||
        oBuf[oStart + k + 1] !== nBuf[nStart + k + 1] ||
        oBuf[oStart + k + 2] !== nBuf[nStart + k + 2] ||
        oBuf[oStart + k + 3] !== nBuf[nStart + k + 3]
      ) {
        break;
      }
    }
    if (k + 4 > len) {
      while (k < len && oBuf[oStart + k] === nBuf[nStart + k]) k++;
    }
    if (k !== len) break;
    oStart = oEndL;
    nStart = nEndL;
    prefix++;
  }

  // 2. Common suffix
  let oEnd = oLen;
  let nEnd = nLen;
  let suffix = 0;
  while (oEnd > oStart && nEnd > nStart) {
    const oS = oEnd - (oBuf[oEnd - 1] === 10 ? 2 : 1);
    const nS = nEnd - (nBuf[nEnd - 1] === 10 ? 2 : 1);
    const oNl = oS >= oStart ? oBuf.lastIndexOf(10, oS) : -1;
    const nNl = nS >= nStart ? nBuf.lastIndexOf(10, nS) : -1;
    const oL = oNl < oStart ? oStart : oNl + 1;
    const nL = nNl < nStart ? nStart : nNl + 1;
    const len = oEnd - oL;
    if (len !== nEnd - nL) break;
    let k = 0;
    for (; k + 4 <= len; k += 4) {
      if (
        oBuf[oL + k] !== nBuf[nL + k] ||
        oBuf[oL + k + 1] !== nBuf[nL + k + 1] ||
        oBuf[oL + k + 2] !== nBuf[nL + k + 2] ||
        oBuf[oL + k + 3] !== nBuf[nL + k + 3]
      ) {
        break;
      }
    }
    if (k + 4 > len) {
      while (k < len && oBuf[oL + k] === nBuf[nL + k]) k++;
    }
    if (k !== len) break;
    oEnd = oL;
    nEnd = nL;
    suffix++;
  }

  // 3. Single-pass SIMD indexOf(10) line offset scan + 4-byte packed FNV-1a hash
  let n = 0;
  let p = oStart;
  while (p < oEnd) {
    const nl = oBuf.indexOf(10, p);
    const e = nl === -1 || nl >= oEnd ? oEnd : nl + 1;
    let h = 2166136261 | 0;
    let k = p;
    for (; k + 4 <= e; k += 4) {
      const w = oBuf[k] | (oBuf[k + 1] << 8) | (oBuf[k + 2] << 16) | (oBuf[k + 3] << 24);
      h = Math.imul(h ^ w, 16777619);
    }
    for (; k < e; k++) h = Math.imul(h ^ oBuf[k], 16777619);
    if (n === oStarts.length) ensureNM(n * 2, nStarts.length);
    oStarts[n] = p;
    oEnds[n] = e;
    oHash[n] = h;
    n++;
    p = e;
  }

  let m = 0;
  p = nStart;
  while (p < nEnd) {
    const nl = nBuf.indexOf(10, p);
    const e = nl === -1 || nl >= nEnd ? nEnd : nl + 1;
    let h = 2166136261 | 0;
    let k = p;
    for (; k + 4 <= e; k += 4) {
      const w = nBuf[k] | (nBuf[k + 1] << 8) | (nBuf[k + 2] << 16) | (nBuf[k + 3] << 24);
      h = Math.imul(h ^ w, 16777619);
    }
    for (; k < e; k++) h = Math.imul(h ^ nBuf[k], 16777619);
    if (m === nStarts.length) ensureNM(oStarts.length, m * 2);
    nStarts[m] = p;
    nEnds[m] = e;
    nHash[m] = h;
    m++;
    p = e;
  }

  ensureNM(n + 4, m + 4);
  return { oStart, nStart, oEnd, nEnd, prefix, suffix, n, m };
}

function internAscii(oBuf, nBuf, n, m) {
  let hCap = 16;
  while (hCap < n * 2) hCap <<= 1;
  if (hCap > buckets.length) buckets = new Int32Array(hCap);
  buckets.fill(0, 0, hCap);
  const hMask = hCap - 1;
  cntA.fill(0, 0, n);
  cntB.fill(0, 0, n);

  for (let i = 0; i < n; i++) {
    const st = oStarts[i];
    const len = oEnds[i] - st;
    const hi = oHash[i];
    let slot = hi & hMask;
    while (true) {
      const b = buckets[slot];
      if (b === 0) {
        buckets[slot] = i + 1;
        A[i] = i;
        cntA[i] = 1;
        break;
      }
      const rep = b - 1;
      if (oHash[rep] === hi && oEnds[rep] - oStarts[rep] === len) {
        const rs = oStarts[rep];
        let k = 0;
        for (; k + 4 <= len; k += 4) {
          if (
            oBuf[rs + k] !== oBuf[st + k] ||
            oBuf[rs + k + 1] !== oBuf[st + k + 1] ||
            oBuf[rs + k + 2] !== oBuf[st + k + 2] ||
            oBuf[rs + k + 3] !== oBuf[st + k + 3]
          ) {
            break;
          }
        }
        if (k + 4 > len) {
          while (k < len && oBuf[rs + k] === oBuf[st + k]) k++;
        }
        if (k === len) {
          A[i] = rep;
          cntA[rep]++;
          break;
        }
      }
      slot = (slot + 1) & hMask;
    }
  }

  for (let i = 0; i < m; i++) {
    const st = nStarts[i];
    const len = nEnds[i] - st;
    const hi = nHash[i];
    let slot = hi & hMask;
    let found = -3;
    while (true) {
      const b = buckets[slot];
      if (b === 0) break;
      const rep = b - 1;
      if (oHash[rep] === hi && oEnds[rep] - oStarts[rep] === len) {
        const rs = oStarts[rep];
        let k = 0;
        for (; k + 4 <= len; k += 4) {
          if (
            oBuf[rs + k] !== nBuf[st + k] ||
            oBuf[rs + k + 1] !== nBuf[st + k + 1] ||
            oBuf[rs + k + 2] !== nBuf[st + k + 2] ||
            oBuf[rs + k + 3] !== nBuf[st + k + 3]
          ) {
            break;
          }
        }
        if (k + 4 > len) {
          while (k < len && oBuf[rs + k] === nBuf[st + k]) k++;
        }
        if (k === len) {
          found = rep;
          cntB[rep]++;
          posB[rep] = i;
          break;
        }
      }
      slot = (slot + 1) & hMask;
    }
    B[i] = found;
  }
}

function trimAndScanUtf16(oldStr, newStr, oLen, nLen) {
  let oStart = 0;
  let nStart = 0;
  let prefix = 0;
  while (oStart < oLen && nStart < nLen) {
    const oNl = oldStr.indexOf('\n', oStart);
    const nNl = newStr.indexOf('\n', nStart);
    const oEndL = oNl === -1 ? oLen : oNl + 1;
    const nEndL = nNl === -1 ? nLen : nNl + 1;
    const len = oEndL - oStart;
    if (len !== nEndL - nStart) break;
    let eq = true;
    for (let k = 0; k < len; k++) {
      if (oldStr.charCodeAt(oStart + k) !== newStr.charCodeAt(nStart + k)) {
        eq = false;
        break;
      }
    }
    if (!eq) break;
    oStart = oEndL;
    nStart = nEndL;
    prefix++;
  }

  let oEnd = oLen;
  let nEnd = nLen;
  let suffix = 0;
  while (oEnd > oStart && nEnd > nStart) {
    const oS = oEnd - (oldStr.charCodeAt(oEnd - 1) === 10 ? 2 : 1);
    const nS = nEnd - (newStr.charCodeAt(nEnd - 1) === 10 ? 2 : 1);
    const oNl = oS >= oStart ? oldStr.lastIndexOf('\n', oS) : -1;
    const nNl = nS >= nStart ? newStr.lastIndexOf('\n', nS) : -1;
    const oL = oNl < oStart ? oStart : oNl + 1;
    const nL = nNl < nStart ? nStart : nNl + 1;
    const len = oEnd - oL;
    if (len !== nEnd - nL) break;
    let eq = true;
    for (let k = 0; k < len; k++) {
      if (oldStr.charCodeAt(oL + k) !== newStr.charCodeAt(nL + k)) {
        eq = false;
        break;
      }
    }
    if (!eq) break;
    oEnd = oL;
    nEnd = nL;
    suffix++;
  }

  let n = 0;
  let p = oStart;
  while (p < oEnd) {
    const nl = oldStr.indexOf('\n', p);
    const e = nl === -1 || nl >= oEnd ? oEnd : nl + 1;
    if (n === oStarts.length) ensureNM(n * 2, nStarts.length);
    oStarts[n] = p;
    oEnds[n] = e;
    n++;
    p = e;
  }

  let m = 0;
  p = nStart;
  while (p < nEnd) {
    const nl = newStr.indexOf('\n', p);
    const e = nl === -1 || nl >= nEnd ? nEnd : nl + 1;
    if (m === nStarts.length) ensureNM(oStarts.length, m * 2);
    nStarts[m] = p;
    nEnds[m] = e;
    m++;
    p = e;
  }

  ensureNM(n + 4, m + 4);
  return { oStart, nStart, oEnd, nEnd, prefix, suffix, n, m };
}

function internUtf16(oldStr, newStr, n, m) {
  let hCap = 16;
  while (hCap < n * 2) hCap <<= 1;
  if (hCap > buckets.length) buckets = new Int32Array(hCap);
  buckets.fill(0, 0, hCap);
  const hMask = hCap - 1;
  cntA.fill(0, 0, n);
  cntB.fill(0, 0, n);

  for (let i = 0; i < n; i++) {
    const s = oStarts[i];
    const e = oEnds[i];
    const len = e - s;
    let h = 2166136261 | 0;
    for (let k = s; k < e; k++) h = Math.imul(h ^ oldStr.charCodeAt(k), 16777619);
    oHash[i] = h;
    let slot = h & hMask;
    while (true) {
      const b = buckets[slot];
      if (b === 0) {
        buckets[slot] = i + 1;
        A[i] = i;
        cntA[i] = 1;
        break;
      }
      const rep = b - 1;
      if (oHash[rep] === h && oEnds[rep] - oStarts[rep] === len) {
        const rs = oStarts[rep];
        let eq = true;
        for (let k = 0; k < len; k++) {
          if (oldStr.charCodeAt(rs + k) !== oldStr.charCodeAt(s + k)) {
            eq = false;
            break;
          }
        }
        if (eq) {
          A[i] = rep;
          cntA[rep]++;
          break;
        }
      }
      slot = (slot + 1) & hMask;
    }
  }

  for (let i = 0; i < m; i++) {
    const s = nStarts[i];
    const e = nEnds[i];
    const len = e - s;
    let h = 2166136261 | 0;
    for (let k = s; k < e; k++) h = Math.imul(h ^ newStr.charCodeAt(k), 16777619);
    let slot = h & hMask;
    let found = -3;
    while (true) {
      const b = buckets[slot];
      if (b === 0) break;
      const rep = b - 1;
      if (oHash[rep] === h && oEnds[rep] - oStarts[rep] === len) {
        const rs = oStarts[rep];
        let eq = true;
        for (let k = 0; k < len; k++) {
          if (oldStr.charCodeAt(rs + k) !== newStr.charCodeAt(s + k)) {
            eq = false;
            break;
          }
        }
        if (eq) {
          found = rep;
          cntB[rep]++;
          posB[rep] = i;
          break;
        }
      }
      slot = (slot + 1) & hMask;
    }
    B[i] = found;
  }
}

function buildBoundsAndUB(n, m) {
  // 1. Exact suffix excess deletions & insertions
  seen.fill(0, 0, n);
  for (let i = n - 1, acc = 0; i >= 0; i--) {
    const id = A[i];
    if (++seen[id] > cntB[id]) acc++;
    remDel[i] = acc;
  }
  remDel[n] = 0;

  seen.fill(0, 0, n);
  for (let j = m - 1, acc = 0; j >= 0; j--) {
    const id = B[j];
    if (id === -3 || ++seen[id] > cntA[id]) acc++;
    remIns[j] = acc;
  }
  remIns[m] = 0;

  // 2. Unique-in-both Patience LIS
  for (let i = 0; i < n; i++) isUniq[i] = cntA[i] === 1 && cntB[i] === 1 ? 1 : 0;
  let tLen = 0;
  for (let i = 0; i < n; i++) {
    const id = A[i];
    if (isUniq[id] === 1) {
      const j = posB[id];
      let lo = 0;
      let hi = tLen;
      while (lo < hi) {
        const mid = (lo + hi) >>> 1;
        if (tailsVal[mid] < j) lo = mid + 1;
        else hi = mid;
      }
      tailsVal[lo] = j;
      tailsA[lo] = i;
      prevIdx[i] = lo > 0 ? tailsA[lo - 1] : -1;
      if (lo === tLen) tLen++;
    }
  }

  inLIS.fill(0, 0, n);
  let cur = tLen > 0 ? tailsA[tLen - 1] : -1;
  for (let k = tLen; k >= 1; k--) {
    ancA[k] = cur;
    ancB[k] = posB[A[cur]];
    inLIS[cur] = 1;
    cur = prevIdx[cur];
  }
  ancA[0] = -1;
  ancB[0] = -1;
  ancA[tLen + 1] = n;
  ancB[tLen + 1] = m;

  // 3. Disjoint crossing S_uniq pairs -> 64x64 2D suffix sum grid
  grid64.fill(0);
  usedLIS.fill(0, 0, tLen + 2);
  let kHint = 1;
  for (let i = 0; i < n; i++) {
    const id = A[i];
    if (isUniq[id] === 1 && inLIS[i] === 0) {
      const j = posB[id];
      while (kHint <= tLen && ancA[kHint] < i) kHint++;
      // kHint is first LIS index with ancA[kHint] > i
      let partnerK = -1;
      for (let kr = kHint, steps = 0; kr <= tLen && steps < 64 && ancB[kr] < j; kr++, steps++) {
        if (usedLIS[kr] === 0) {
          partnerK = kr;
          break;
        }
      }
      if (partnerK === -1) {
        for (let kl = kHint - 1, steps = 0; kl >= 1 && steps < 64 && ancB[kl] > j; kl--, steps++) {
          if (usedLIS[kl] === 0) {
            partnerK = kl;
            break;
          }
        }
      }
      if (partnerK !== -1) {
        usedLIS[partnerK] = 1;
        const pa = ancA[partnerK];
        const pb = ancB[partnerK];
        const minA = i < pa ? i : pa;
        const minB = j < pb ? j : pb;
        const gx = Math.floor((minA * GRID_N) / n);
        const gy = Math.floor((minB * GRID_N) / m);
        grid64[gx * GRID_S + gy]++;
      }
    }
  }
  for (let gx = GRID_N - 1; gx >= 0; gx--) {
    const row = gx * GRID_S;
    const nxt = row + GRID_S;
    for (let gy = GRID_N - 1; gy >= 0; gy--) {
      grid64[row + gy] += grid64[nxt + gy] + grid64[row + gy + 1] - grid64[nxt + gy + 1];
    }
  }

  // 4. Gap Myers for upper bound U
  let U = 0;
  for (let g = 0; g <= tLen; g++) {
    let x0 = ancA[g] + 1;
    let y0 = ancB[g] + 1;
    let gn = ancA[g + 1] - x0;
    let gm = ancB[g + 1] - y0;
    while (gn > 0 && gm > 0 && A[x0] === B[y0]) {
      x0++;
      y0++;
      gn--;
      gm--;
    }
    while (gn > 0 && gm > 0 && A[x0 + gn - 1] === B[y0 + gm - 1]) {
      gn--;
      gm--;
    }
    if (gn === 0) {
      U += gm;
      continue;
    }
    if (gm === 0) {
      U += gn;
      continue;
    }
    const maxGD = 256 < gn + gm ? 256 : gn + gm;
    const sA = A[x0 + gn];
    const sB = B[y0 + gm];
    A[x0 + gn] = -1;
    B[y0 + gm] = -2;
    let gx = 0;
    while (A[x0 + gx] === B[y0 + gx]) gx++;
    gVp[0] = gx;
    let solved = false;
    for (let d = 1; d <= maxGD; d++) {
      for (let idx = 0, k = -d; idx <= d; idx++, k += 2) {
        const xr = idx > 0 ? gVp[idx - 1] : -2;
        const xa = idx < d ? gVp[idx] : -2;
        const cr = xr >= 0 && xr < gn;
        const ca = xa >= 0 && xa - k - 1 < gm;
        let nx = cr && (!ca || xr + 1 >= xa) ? xr + 1 : ca ? xa : -2;
        if (nx < 0) {
          gVc[idx] = -2;
          continue;
        }
        let ny = nx - k;
        while (A[x0 + nx] === B[y0 + ny]) {
          nx++;
          ny++;
        }
        if (nx === gn && ny === gm) {
          U += d;
          solved = true;
          break;
        }
        gVc[idx] = nx;
      }
      if (solved) break;
      const t = gVp;
      gVp = gVc;
      gVc = t;
    }
    A[x0 + gn] = sA;
    B[y0 + gm] = sB;
    if (!solved) U += gn + gm;
  }
  return U;
}

function myersForward(n, m, U) {
  A[n] = -1;
  B[m] = -2;
  const delta = n - m;
  if (U + 4 > Vp.length) {
    const c = U + 256;
    Vp = new Int32Array(c);
    Vc = new Int32Array(c);
  }
  Vp.fill(-2, 0, U + 4);
  Vc.fill(-2, 0, U + 4);

  const ckpts = [];
  const ckptILo = [];
  const ckptKLo = [];
  const ckptKHi = [];

  let x0 = 0;
  while (A[x0] === B[x0]) x0++;
  Vp[0] = x0;
  ckpts.push(new Int32Array([x0]));
  ckptILo.push(0);
  ckptKLo.push(0);
  ckptKHi.push(0);

  let ansD = 0;
  let ansK = 0;
  let kLo = 0;
  let kHi = 0;
  let hitBound = x0 >= n || x0 >= m;

  if (x0 < n || x0 < m) {
    outer: for (let d = 1; d <= U; d++) {
      const remD = U - d;
      const lim1 = remD - delta;
      const lim2 = remD + delta;
      let loK = kLo - 1 > -lim1 ? kLo - 1 : -lim1;
      let hiK = kHi + 1 < lim2 ? kHi + 1 : lim2;
      if (((loK ^ d) & 1) !== 0) loK++;
      if (((hiK ^ d) & 1) !== 0) hiK--;
      let iLo = (loK + d) >> 1;
      let iHi = (hiK + d) >> 1;
      if (iLo > 0) Vc[iLo - 1] = -2;
      Vc[iHi + 1] = -2;

      if (!hitBound) {
        let idx = iLo;
        let k = loK;
        if (idx === 0) {
          let nx = Vp[0];
          let ny = nx - k;
          while (A[nx] === B[ny]) {
            nx++;
            ny++;
          }
          if (nx >= n || ny >= m) {
            hitBound = true;
            if (nx === n && ny === m) {
              ansD = d;
              ansK = k;
              break outer;
            }
          }
          Vc[0] = nx;
          idx = 1;
          k += 2;
        }
        const endIdx = iHi < d ? iHi : d - 1;
        let xRem = Vp[idx - 1];
        for (; idx <= endIdx; idx++, k += 2) {
          const xAdd = Vp[idx];
          let nx = xRem + 1 >= xAdd ? xRem + 1 : xAdd;
          let ny = nx - k;
          while (A[nx] === B[ny]) {
            nx++;
            ny++;
          }
          if (nx >= n || ny >= m) {
            hitBound = true;
            if (nx === n && ny === m) {
              ansD = d;
              ansK = k;
              break outer;
            }
          }
          Vc[idx] = nx;
          xRem = xAdd;
        }
        if (iHi === d) {
          let nx = xRem + 1;
          let ny = nx - d;
          while (A[nx] === B[ny]) {
            nx++;
            ny++;
          }
          if (nx >= n || ny >= m) {
            hitBound = true;
            if (nx === n && ny === m) {
              ansD = d;
              ansK = d;
              break outer;
            }
          }
          Vc[d] = nx;
        }
      } else {
        for (let idx = iLo, k = loK; idx <= iHi; idx++, k += 2) {
          const xRem = idx > 0 ? Vp[idx - 1] : -2;
          const xAdd = idx < d ? Vp[idx] : -2;
          const canRem = xRem >= 0 && xRem < n;
          const canAdd = xAdd >= 0 && xAdd - k - 1 < m;
          let nx = canRem && (!canAdd || xRem + 1 >= xAdd) ? xRem + 1 : canAdd ? xAdd : -2;
          if (nx < 0) {
            Vc[idx] = -2;
            continue;
          }
          let ny = nx - k;
          while (A[nx] === B[ny]) {
            nx++;
            ny++;
          }
          if (nx === n && ny === m) {
            ansD = d;
            ansK = k;
            break outer;
          }
          Vc[idx] = nx;
        }
      }

      while (iLo <= iHi) {
        const nx = Vc[iLo];
        if (nx >= 0) {
          const ny = nx - loK;
          const qx = Math.floor((nx * GRID_N + n - 1) / n);
          const qy = Math.floor((ny * GRID_N + m - 1) / m);
          const cc = grid64[qx * GRID_S + qy];
          if (((remIns[ny] + cc) << 1) <= lim1 + loK && ((remDel[nx] + cc) << 1) <= lim2 - loK) break;
          Vc[iLo] = -2;
        }
        iLo++;
        loK += 2;
      }
      while (iHi >= iLo) {
        const nx = Vc[iHi];
        if (nx >= 0) {
          const ny = nx - hiK;
          const qx = Math.floor((nx * GRID_N + n - 1) / n);
          const qy = Math.floor((ny * GRID_N + m - 1) / m);
          const cc = grid64[qx * GRID_S + qy];
          if (((remIns[ny] + cc) << 1) <= lim1 + hiK && ((remDel[nx] + cc) << 1) <= lim2 - hiK) break;
          Vc[iHi] = -2;
        }
        iHi--;
        hiK -= 2;
      }

      kLo = loK;
      kHi = hiK;
      const tmp = Vp;
      Vp = Vc;
      Vc = tmp;
      if ((d & B_MASK) === 0) {
        ckpts.push(Vp.slice(iLo, iHi + 1));
        ckptILo.push(iLo);
        ckptKLo.push(loK);
        ckptKHi.push(hiK);
      }
    }
  }
  return { ansD, ansK, ckpts, ckptILo, ckptKLo, ckptKHi };
}

function replayPath(n, m, U, ansD, ansK, ckpts, ckptILo, ckptKLo, ckptKHi) {
  const delta = n - m;
  const maxOps = ansD * 2 + 4;
  if (maxOps > revKind.length) {
    revKind = new Uint8Array(maxOps);
    revCount = new Int32Array(maxOps);
  }
  let opLen = 0;
  const stride = B_STEP + 4;

  let curD = ansD;
  let curK = ansK;
  let curX = n;

  while (curD > 0) {
    const bIdx = (curD - 1) >> B_SHIFT;
    const d0 = bIdx << B_SHIFT;
    const d1 = curD;
    const span = d1 - d0;
    const ck = ckpts[bIdx];
    const ckILo = ckptILo[bIdx];
    const fLo0 = ckptKLo[bIdx];
    const fHi0 = ckptKHi[bIdx];
    const baseK0 = curK - span;
    const rLo0 = fLo0 > curK - span ? fLo0 : curK - span;
    const rHi0 = fHi0 < curK + span ? fHi0 : curK + span;

    repBuf.fill(-2, 0, span + 3);
    for (let k = rLo0; k <= rHi0; k += 2) {
      repBuf[(k - baseK0) >> 1] = ck[((k + d0) >> 1) - ckILo];
    }

    let pLo = rLo0;
    let pHi = rHi0;
    for (let s = 1; s <= span; s++) {
      const d = d0 + s;
      const remD = U - d;
      const lim1 = remD - delta;
      const lim2 = remD + delta;
      const wLo = curK - (span - s);
      const wHi = curK + (span - s);
      let rLo = pLo - 1 > -lim1 ? pLo - 1 : -lim1;
      if (wLo > rLo) rLo = wLo;
      let rHi = pHi + 1 < lim2 ? pHi + 1 : lim2;
      if (wHi < rHi) rHi = wHi;
      if (((rLo ^ d) & 1) !== 0) rLo++;
      if (((rHi ^ d) & 1) !== 0) rHi--;

      const prevRow = (s - 1) * stride;
      const curRow = s * stride;
      const shiftBase = baseK0 - s;
      let cILo = (rLo - shiftBase) >> 1;
      let cIHi = (rHi - shiftBase) >> 1;
      if (cILo > 0) repBuf[curRow + cILo - 1] = -2;
      repBuf[curRow + cIHi + 1] = -2;

      for (let k = rLo; k <= rHi; k += 2) {
        const col = (k - shiftBase) >> 1;
        const xRem = k - 1 >= pLo && k - 1 <= pHi ? repBuf[prevRow + col - 1] : -2;
        const xAdd = k + 1 >= pLo && k + 1 <= pHi ? repBuf[prevRow + col] : -2;
        const canRem = xRem >= 0 && xRem < n;
        const canAdd = xAdd >= 0 && xAdd - k - 1 < m;
        let nx = canRem && (!canAdd || xRem + 1 >= xAdd) ? xRem + 1 : canAdd ? xAdd : -2;
        if (nx < 0) {
          repBuf[curRow + col] = -2;
          continue;
        }
        let ny = nx - k;
        while (A[nx] === B[ny]) {
          nx++;
          ny++;
        }
        repBuf[curRow + col] = nx;
      }

      if (s < span) {
        while (cILo <= cIHi) {
          const nx = repBuf[curRow + cILo];
          if (nx >= 0) {
            const ny = nx - rLo;
            const qx = Math.floor((nx * GRID_N + n - 1) / n);
            const qy = Math.floor((ny * GRID_N + m - 1) / m);
            const cc = grid64[qx * GRID_S + qy];
            if (((remIns[ny] + cc) << 1) <= lim1 + rLo && ((remDel[nx] + cc) << 1) <= lim2 - rLo) break;
            repBuf[curRow + cILo] = -2;
          }
          cILo++;
          rLo += 2;
        }
        while (cIHi >= cILo) {
          const nx = repBuf[curRow + cIHi];
          if (nx >= 0) {
            const ny = nx - rHi;
            const qx = Math.floor((nx * GRID_N + n - 1) / n);
            const qy = Math.floor((ny * GRID_N + m - 1) / m);
            const cc = grid64[qx * GRID_S + qy];
            if (((remIns[ny] + cc) << 1) <= lim1 + rHi && ((remDel[nx] + cc) << 1) <= lim2 - rHi) break;
            repBuf[curRow + cIHi] = -2;
          }
          cIHi--;
          rHi -= 2;
        }
      }
      pLo = rLo;
      pHi = rHi;
    }

    let traceX = curX;
    let traceK = curK;
    for (let s = span; s >= 1; s--) {
      const prevRow = (s - 1) * stride;
      const shiftBase = baseK0 - s;
      const col = (traceK - shiftBase) >> 1;
      const xRem = col > 0 ? repBuf[prevRow + col - 1] : -2;
      const xAdd = repBuf[prevRow + col];
      const canRem = xRem >= 0 && xRem < n;
      const canAdd = xAdd >= 0 && xAdd - traceK - 1 < m;
      let startX, opK, nextK, prevX;
      if (canRem && (!canAdd || xRem + 1 >= xAdd)) {
        startX = xRem + 1;
        opK = DELETE;
        nextK = traceK - 1;
        prevX = xRem;
      } else {
        startX = xAdd;
        opK = INSERT;
        nextK = traceK + 1;
        prevX = xAdd;
      }
      const keep = traceX - startX;
      if (keep > 0) {
        if (opLen > 0 && revKind[opLen - 1] === KEEP) revCount[opLen - 1] += keep;
        else {
          revKind[opLen] = KEEP;
          revCount[opLen] = keep;
          opLen++;
        }
      }
      if (opLen > 0 && revKind[opLen - 1] === opK) revCount[opLen - 1]++;
      else {
        revKind[opLen] = opK;
        revCount[opLen] = 1;
        opLen++;
      }
      traceK = nextK;
      traceX = prevX;
    }
    curD = d0;
    curK = traceK;
    curX = traceX;
  }

  if (curX > 0) {
    if (opLen > 0 && revKind[opLen - 1] === KEEP) revCount[opLen - 1] += curX;
    else {
      revKind[opLen] = KEEP;
      revCount[opLen] = curX;
      opLen++;
    }
  }
  return opLen;
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

  const oBuf = Buffer.from(oldStr);
  const nBuf = Buffer.from(newStr);
  const isAscii = oBuf.length === oLen && nBuf.length === nLen;

  const { oStart, oEnd, prefix, suffix, n, m } = isAscii
    ? trimAndScanAscii(oBuf, nBuf, oLen, nLen)
    : trimAndScanUtf16(oldStr, newStr, oLen, nLen);

  const totalOld = prefix + n + suffix;
  const totalNew = prefix + m + suffix;

  if (n === 0 && m === 0) {
    return `${FORMAT} old=${totalOld} new=${totalNew} hunks=0 deleted=0 inserted=0\n`;
  }

  if (n === 0 || m === 0) {
    const oldStart = prefix > CONTEXT ? prefix - CONTEXT : 0;
    const newStart = prefix - (prefix - oldStart);
    const after = suffix < CONTEXT ? suffix : CONTEXT;
    const oldEnd = prefix + n + after;
    const newEnd = prefix + m + after;
    const out = [
      `${FORMAT} old=${totalOld} new=${totalNew} hunks=1 deleted=${n} inserted=${m}\n`,
      `@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`,
    ];
    if (prefix > oldStart) {
      let cur = oStart;
      const ctxStarts = [];
      for (let i = 0; i < prefix - oldStart; i++) {
        const s = cur - (oldStr.charCodeAt(cur - 1) === 10 ? 2 : 1);
        const nl = s >= 0 ? oldStr.lastIndexOf('\n', s) : -1;
        cur = nl === -1 ? 0 : nl + 1;
        ctxStarts.push(cur);
      }
      for (let i = ctxStarts.length - 1; i >= 0; i--) {
        out.push('=', oldStr.slice(ctxStarts[i], i > 0 ? ctxStarts[i - 1] : oStart));
      }
    }
    if (n > 0) {
      for (let i = 0; i < n; i++) {
        const line = oldStr.slice(oStarts[i], oEnds[i]);
        out.push('-', line);
        if (line.charCodeAt(line.length - 1) !== 10) out.push('\n%\n');
      }
    } else {
      for (let i = 0; i < m; i++) {
        const line = newStr.slice(nStarts[i], nEnds[i]);
        out.push('+', line);
        if (line.charCodeAt(line.length - 1) !== 10) out.push('\n%\n');
      }
    }
    if (after > 0) {
      let cur = oEnd;
      for (let i = 0; i < after; i++) {
        const nl = oldStr.indexOf('\n', cur);
        const en = nl === -1 ? oLen : nl + 1;
        const line = oldStr.slice(cur, en);
        out.push('=', line);
        if (line.charCodeAt(line.length - 1) !== 10) out.push('\n%\n');
        cur = en;
      }
    }
    return out.join('');
  }

  if (isAscii) internAscii(oBuf, nBuf, n, m);
  else internUtf16(oldStr, newStr, n, m);

  const U = buildBoundsAndUB(n, m);
  const fwd = myersForward(n, m, U);
  const opLen = replayPath(n, m, U, fwd.ansD, fwd.ansK, fwd.ckpts, fwd.ckptILo, fwd.ckptKLo, fwd.ckptKHi);

  // Build change runs
  const changesO = [];
  const changesP = [];
  const changesD = [];
  const changesI = [];
  let o = prefix;
  let p = prefix;
  let deleted = 0;
  let inserted = 0;
  for (let idx = opLen - 1; idx >= 0; idx--) {
    const kind = revKind[idx];
    const cnt = revCount[idx];
    if (kind === KEEP) {
      o += cnt;
      p += cnt;
      continue;
    }
    const last = changesO.length - 1;
    if (last < 0 || changesO[last] + changesD[last] !== o || changesP[last] + changesI[last] !== p) {
      changesO.push(o);
      changesP.push(p);
      changesD.push(0);
      changesI.push(0);
    }
    const ci = changesO.length - 1;
    if (kind === DELETE) {
      changesD[ci] += cnt;
      o += cnt;
      deleted += cnt;
    } else {
      changesI[ci] += cnt;
      p += cnt;
      inserted += cnt;
    }
  }

  const numChanges = changesO.length;
  const hStartIdx = [];
  const hEndIdx = [];
  for (let i = 0; i < numChanges; i++) {
    const hLast = hEndIdx.length - 1;
    if (hLast >= 0) {
      const prev = hEndIdx[hLast];
      if (changesO[i] - (changesO[prev] + changesD[prev]) <= 2 * CONTEXT) {
        hEndIdx[hLast] = i;
        continue;
      }
    }
    hStartIdx.push(i);
    hEndIdx.push(i);
  }
  const numHunks = hStartIdx.length;
  const out = [
    `${FORMAT} old=${totalOld} new=${totalNew} hunks=${numHunks} deleted=${deleted} inserted=${inserted}\n`,
  ];

  let preStarts = null;
  if (numHunks > 0 && changesO[hStartIdx[0]] < prefix + CONTEXT && prefix > 0) {
    const need = prefix < CONTEXT ? prefix : CONTEXT;
    preStarts = new Int32Array(need + 1);
    let curPos = oStart;
    preStarts[need] = curPos;
    for (let i = need - 1; i >= 0; i--) {
      const s = curPos - (oldStr.charCodeAt(curPos - 1) === 10 ? 2 : 1);
      const nl = s >= 0 ? oldStr.lastIndexOf('\n', s) : -1;
      curPos = nl === -1 ? 0 : nl + 1;
      preStarts[i] = curPos;
    }
  }
  let sufEnds = null;
  if (numHunks > 0 && suffix > 0) {
    const lastC = hEndIdx[numHunks - 1];
    if (changesO[lastC] + changesD[lastC] + CONTEXT > prefix + n) {
      const need = suffix < CONTEXT ? suffix : CONTEXT;
      sufEnds = new Int32Array(need + 1);
      let curPos = oEnd;
      sufEnds[0] = curPos;
      for (let i = 1; i <= need; i++) {
        const nl = oldStr.indexOf('\n', curPos);
        curPos = nl === -1 ? oLen : nl + 1;
        sufEnds[i] = curPos;
      }
    }
  }

  const pushOldLine = (gi, op) => {
    let s, e;
    if (gi >= prefix && gi < prefix + n) {
      s = oStarts[gi - prefix];
      e = oEnds[gi - prefix];
    } else if (gi < prefix) {
      const off = gi - (prefix - (preStarts.length - 1));
      s = preStarts[off];
      e = preStarts[off + 1];
    } else {
      const off = gi - (prefix + n);
      s = sufEnds[off];
      e = sufEnds[off + 1];
    }
    const line = oldStr.slice(s, e);
    out.push(op, line);
    if (line.charCodeAt(line.length - 1) !== 10) out.push('\n%\n');
  };

  for (let hi = 0; hi < numHunks; hi++) {
    const fi = hStartIdx[hi];
    const li = hEndIdx[hi];
    const firstO = changesO[fi];
    const firstP = changesP[fi];
    const lastO = changesO[li];
    const lastP = changesP[li];
    const lastD = changesD[li];
    const lastI = changesI[li];
    const oldStart = firstO > CONTEXT ? firstO - CONTEXT : 0;
    const newStart = firstP - (firstO - oldStart);
    const remAfter = totalOld - (lastO + lastD);
    const after = remAfter < CONTEXT ? remAfter : CONTEXT;
    const oldEnd = lastO + lastD + after;
    const newEnd = lastP + lastI + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (let ci = fi; ci <= li; ci++) {
      const co = changesO[ci];
      const cp = changesP[ci];
      const cd = changesD[ci];
      const cins = changesI[ci];
      for (; at < co; at++) pushOldLine(at, '=');
      for (let i = 0; i < cd; i++) pushOldLine(co + i, '-');
      for (let i = 0; i < cins; i++) {
        const mi = cp + i - prefix;
        const line = newStr.slice(nStarts[mi], nEnds[mi]);
        out.push('+', line);
        if (line.charCodeAt(line.length - 1) !== 10) out.push('\n%\n');
      }
      at = co + cd;
    }
    for (; at < oldEnd; at++) pushOldLine(at, '=');
  }

  return out.join('');
}

export function run(input) {
  return diffPatch(input);
}
