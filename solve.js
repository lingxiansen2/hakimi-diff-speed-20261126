export const FORMAT = 'makefun-diff/1';
export const CONTEXT = 3;

const KEEP = 0;
const DELETE = 1;
const INSERT = 2;
const B_SHIFT = 7;
const B_STEP = 1 << B_SHIFT;
const B_MASK = B_STEP - 1;

function countLines(str) {
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

function scanMiddleLines(str, start, end) {
  let cap = ((end - start) >>> 4) + 64;
  let starts = new Int32Array(cap);
  let ends = new Int32Array(cap);
  let count = 0;
  let p = start;
  while (p < end) {
    const nl = str.indexOf('\n', p);
    const e = nl === -1 || nl >= end ? end : nl + 1;
    if (count === cap) {
      cap <<= 1;
      const s2 = new Int32Array(cap);
      const e2 = new Int32Array(cap);
      s2.set(starts);
      e2.set(ends);
      starts = s2;
      ends = e2;
    }
    starts[count] = p;
    ends[count] = e;
    count++;
    p = e;
  }
  return { starts, ends, count };
}

function internLines(oldStr, oStarts, oEnds, n, newStr, nStarts, nEnds, m) {
  let hCap = 16;
  while (hCap < n * 2) hCap <<= 1;
  const hMask = hCap - 1;
  const buckets = new Int32Array(hCap);
  const oHash = new Int32Array(n);
  const A = new Int32Array(n + 1);
  const cntA = new Int32Array(n);

  for (let i = 0; i < n; i++) {
    const s = oStarts[i];
    const e = oEnds[i];
    const len = e - s;
    let h = 2166136261 | 0;
    for (let k = s; k < e; k++) {
      h = Math.imul(h ^ oldStr.charCodeAt(k), 16777619);
    }
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

  const B = new Int32Array(m + 1);
  const cntB = new Int32Array(n);
  const posB = new Int32Array(n);
  for (let i = 0; i < m; i++) {
    const s = nStarts[i];
    const e = nEnds[i];
    const len = e - s;
    let h = 2166136261 | 0;
    for (let k = s; k < e; k++) {
      h = Math.imul(h ^ newStr.charCodeAt(k), 16777619);
    }
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

  return { A, B, cntA, cntB, posB };
}

function computeUpperBound(A, B, n, m, cntA, cntB, posB) {
  const minNM = n < m ? n : m;
  const tailsVal = new Int32Array(minNM + 1);
  const tailsA = new Int32Array(minNM + 1);
  const prevIdx = new Int32Array(n);
  let tLen = 0;

  for (let i = 0; i < n; i++) {
    const id = A[i];
    if (cntA[id] === 1 && cntB[id] === 1) {
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

  const ancA = new Int32Array(tLen + 2);
  const ancB = new Int32Array(tLen + 2);
  let cur = tLen > 0 ? tailsA[tLen - 1] : -1;
  for (let k = tLen; k >= 1; k--) {
    ancA[k] = cur;
    ancB[k] = posB[A[cur]];
    cur = prevIdx[cur];
  }
  ancA[0] = -1;
  ancB[0] = -1;
  ancA[tLen + 1] = n;
  ancB[tLen + 1] = m;

  let U = 0;
  let gVp = new Int32Array(516);
  let gVc = new Int32Array(516);

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

function myersForward(A, B, n, m, U, remDel, remIns) {
  A[n] = -1;
  B[m] = -2;
  const delta = n - m;
  let Vp = new Int32Array(U + 4).fill(-2);
  let Vc = new Int32Array(U + 4).fill(-2);
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
          if ((remIns[ny] << 1) <= lim1 + loK && (remDel[nx] << 1) <= lim2 - loK) break;
          Vc[iLo] = -2;
        }
        iLo++;
        loK += 2;
      }
      while (iHi >= iLo) {
        const nx = Vc[iHi];
        if (nx >= 0) {
          const ny = nx - hiK;
          if ((remIns[ny] << 1) <= lim1 + hiK && (remDel[nx] << 1) <= lim2 - hiK) break;
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

function replayPath(A, B, n, m, U, remDel, remIns, ansD, ansK, ckpts, ckptILo, ckptKLo, ckptKHi) {
  const delta = n - m;
  const maxOps = ansD * 2 + 4;
  const revKind = new Uint8Array(maxOps);
  const revCount = new Int32Array(maxOps);
  let opLen = 0;

  const stride = B_STEP + 4;
  const repBuf = new Int32Array((B_STEP + 1) * stride);

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
      let nLo = 1e9;
      let nHi = -1e9;
      const cILo = (rLo - shiftBase) >> 1;
      const cIHi = (rHi - shiftBase) >> 1;
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
        if (s < span || k !== curK) {
          if ((remIns[ny] << 1) > lim1 + k || (remDel[nx] << 1) > lim2 - k) {
            repBuf[curRow + col] = -2;
            continue;
          }
        }
        repBuf[curRow + col] = nx;
        if (k < nLo) nLo = k;
        if (k > nHi) nHi = k;
      }
      pLo = nLo;
      pHi = nHi;
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
  return { revKind, revCount, opLen };
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
    const cnt = countLines(oldStr);
    return `${FORMAT} old=${cnt} new=${cnt} hunks=0 deleted=0 inserted=0\n`;
  }

  // 1. Common prefix directly on strings
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

  // 2. Common suffix directly on strings
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

  // 3. Scan trimmed middle lines
  const midOld = scanMiddleLines(oldStr, oStart, oEnd);
  const midNew = scanMiddleLines(newStr, nStart, nEnd);
  const oStarts = midOld.starts;
  const oEnds = midOld.ends;
  const n = midOld.count;
  const nStarts = midNew.starts;
  const nEnds = midNew.ends;
  const m = midNew.count;

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

  // 4. Hash & intern middle lines + suffix unmatched bounds
  const { A, B, cntA, cntB, posB } = internLines(oldStr, oStarts, oEnds, n, newStr, nStarts, nEnds, m);
  const remDel = new Int32Array(n + 1);
  for (let i = n - 1, acc = 0; i >= 0; i--) {
    if (cntB[A[i]] === 0) acc++;
    remDel[i] = acc;
  }
  const remIns = new Int32Array(m + 1);
  for (let i = m - 1, acc = 0; i >= 0; i--) {
    if (B[i] === -3) acc++;
    remIns[i] = acc;
  }

  // 5. Tight upper bound via Patience LIS
  const U = computeUpperBound(A, B, n, m, cntA, cntB, posB);

  // 6. A*-pruned Myers + Checkpointed Replay
  const fwd = myersForward(A, B, n, m, U, remDel, remIns);
  const { revKind, revCount, opLen } = replayPath(
    A, B, n, m, U, remDel, remIns,
    fwd.ansD, fwd.ansK, fwd.ckpts, fwd.ckptILo, fwd.ckptKLo, fwd.ckptKHi
  );

  // 7. Build change runs
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

  // 8. Group changes into hunks & render output
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
