// Clean symbolic WebAssembly SIMD128 compiler for zero-copy streaming raw-JSON exact Myers diff.
// Architecture:
//   - 90 initial pages (5.625 MB) with sliding JSON input window + L2-packed arena lifetime reuse.
//   - Raw-JSON in-place fast path: diffs directly on raw JSON bytes (\n / \r), emitting JSON patch strings
//     without unescape/re-escape copies; falls back cleanly to ASCII unescape/escape or JS UTF-16.
//   - SIMD128 predictive sequential line matcher + 64-bit SWAR FNV-1a line hashing.
//   - Split zero-penalty displaced-token slab + disjoint crossing pair lower bound (sufDel / sufIns).
const I32=0x7f,I64=0x7e,V128=0x7b,V=0x40;
const KP=0,DL=1,IN=2;
const UNR=0x00,BK=0x02,LP=0x03,IF=0x04,EL=0x05,E=0x0b;
const BR=0x0c,BF=0x0d,RT=0x0f,CL=0x10,DR=0x1a,SL=0x1b;
const G=0x20,S=0x21,T=0x22,GG=0x23,GS=0x24;
const L32=0x28,L64=0x29,L8=0x2d,S32=0x36,S64=0x37,S8=0x3a;
const MSZ=0x3f,MGR=0x40,C=0x41,C6=0x42;
const EZ=0x45,EQ=0x46,NE=0x47,LT=0x48,LU=0x49,GT=0x4a,GU=0x4b,LE=0x4c,LEU=0x4d,GE=0x4e,GEU=0x4f;
const I6Z=0x50,I6EQ=0x51,I6NE=0x52;
const CLZ=0x67,CTZ=0x68,POP=0x69;
const A=0x6a,B=0x6b,M=0x6c,DVU=0x6e,RMU=0x70,AN=0x71,OR=0x72,XR=0x73,SL_=0x74,SS=0x75,SR=0x76;
const I6TZ=0x7a,I6B=0x7d,I6M=0x7e,I6A=0x83,I6O=0x84,I6X=0x85,I6SL=0x86,I6SR=0x88;
const WR=0xa7,EXU=0xad;
const L32U=-1,VLD=-2,VST=-3,VS8=-4,VE8=-5,VL8=-6,VBM=-7,VOR=-8;
const MCP=-9,MFL=-10,MNT=-11;
const LA=-12,L8G=-13,SA=-14,SAC=-15,SAC8=-16,LL=-17,SL2=-18,SC2=-19,BLP=-20,EE=-21,UV=-22,BF1=-23,BR0=-24,INC=-25,DEC=-26,GA1=-27,GB1=-28,C0=-29,C1=-30,CM1=-31,CM2=-32,SH2=-33,RE=-34,B0E=-35,AS=-36,BS=-37,ZS=-38,OS=-39,L8Z=-40,S8Z=-41,L3Z=-42,S3Z=-43,EQI=-44,RM1=-45;
const HDR_STR = 'makefun-diff/1 old= new= hunks= deleted= inserted=@ \\n%\\n';
const HDR_MAP = {
'makefun-diff/1 old=': [0,19],' new=': [19,5],' hunks=': [24,7],' deleted=': [31,9],' inserted=': [40,10],'@ ': [50,2],'\\n%\\n': [52,5],};
function writeUleb(b, p, v) {v >>>= 0;while (v >= 0x80) { b[p++]=(v & 0x7f) | 0x80; v >>>= 7; }b[p++]=v;
return p;}
function writeSleb32(b, p, v) {v |= 0;
for (;;) {
const x=v & 0x7f; v >>= 7;
if ((v === 0 && (x & 0x40) === 0) || (v === -1 && (x & 0x40) !== 0)) { b[p++]=x; return p; }b[p++]=x | 0x80;}}
function writeSleb64LH(b, p, lo, hi) {lo >>>= 0; hi |= 0;
for (;;) {
const x=lo & 0x7f;
lo=((lo >>> 7) | (hi << 25)) >>> 0;hi >>= 7;
if ((hi === 0 && lo === 0 && (x & 0x40) === 0) || (hi === -1 && lo === 0xffffffff && (x & 0x40) !== 0)) { b[p++]=x; return p; }b[p++]=x | 0x80;}}
function encodeBody(q,out,p) {
let op,v,g,idx,val;
for (let i=0; i < q.length; ) {
op=q[i++];
if (op >= 0x45) {out[p++]=op;
} else if (op >= 0) {out[p++]=op;
switch (op) {
case C: v = q[i++]; if (v >= -64 && v < 64) out[p++] = v & 0x7f; else p = writeSleb32(out, p, v); break;
case C6: p = writeSleb64LH(out, p, q[i++], q[i++]); break;
case G: case S: case T: case GG: case GS: case CL: case BR: case BF:
v = q[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
case L32: case S32: out[p++] = 2; v = q[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
case L64: case L8: case S64: case S8: out[p++] = 0; v = q[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
case BK: case LP: case IF: out[p++]=q[i++]; break;
case MSZ: case MGR: out[p++]=0; break;}} else {
switch (op) {
case L32U: out[p++] = L32; out[p++] = 0; v = q[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
case VLD: out[p++] = 0xfd; out[p++] = 0x00; out[p++] = 0; v = q[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
case VST: out[p++] = 0xfd; out[p++] = 0x0b; out[p++] = 0; v = q[i++]; if (v < 128) out[p++] = v; else p = writeUleb(out, p, v); break;
case VS8: out[p++]=0xfd; out[p++]=0x0f; break;
case VE8: out[p++]=0xfd; out[p++]=0x23; break;
case VL8: out[p++]=0xfd; out[p++]=0x25; break;
case VBM: out[p++]=0xfd; out[p++]=0x64; break;
case VOR: out[p++]=0xfd; out[p++]=0x50; break;
case MCP: out[p++]=0xfc; out[p++]=0x0a; out[p++]=0; out[p++]=0; break;
case MFL: out[p++]=0xfc; out[p++]=0x0b; out[p++]=0; break;
case MNT: out[p++]=0xfc; out[p++]=0x08; out[p++]=0; out[p++]=0; break;
case LA:g=q[i++]; idx=q[i++];out[p++]=GG; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL_; out[p++]=A; out[p++]=L32; out[p++]=2; out[p++]=0; break;
case L8G:g=q[i++]; idx=q[i++];out[p++]=GG; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=A; out[p++]=L8; out[p++]=0; out[p++]=0; break;
case SA:g=q[i++]; idx=q[i++]; val=q[i++];out[p++]=GG; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL_; out[p++]=A;out[p++]=G; out[p++]=val; out[p++]=S32; out[p++]=2; out[p++]=0; break;
case SAC:g=q[i++]; idx=q[i++]; val=q[i++];out[p++]=GG; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL_; out[p++]=A;
out[p++] = C; if (val >= -64 && val < 64) out[p++] = val & 0x7f; else p = writeSleb32(out, p, val);out[p++]=S32; out[p++]=2; out[p++]=0; break;
case SAC8:g=q[i++]; idx=q[i++]; val=q[i++];out[p++]=GG; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=A; out[p++]=C; out[p++]=val & 0x7f; out[p++]=S8; out[p++]=0; out[p++]=0; break;
case LL:g=q[i++]; idx=q[i++];out[p++]=G; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL_; out[p++]=A; out[p++]=L32; out[p++]=2; out[p++]=0; break;
case SL2:g=q[i++]; idx=q[i++]; val=q[i++];out[p++]=G; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL_; out[p++]=A;out[p++]=G; out[p++]=val; out[p++]=S32; out[p++]=2; out[p++]=0; break;
case BLP: out[p++]=BK; out[p++]=V; out[p++]=LP; out[p++]=V; break; case EE: out[p++]=E; out[p++]=E; break; case UV: out[p++]=IF; out[p++]=V; break; case BF1: out[p++]=BF; out[p++]=1; break; case BR0: out[p++]=BR; out[p++]=0; break; case INC: v=q[i++]; out[p++]=G; out[p++]=v; out[p++]=C; out[p++]=1; out[p++]=A; out[p++]=S; out[p++]=v; break; case DEC: v=q[i++]; out[p++]=G; out[p++]=v; out[p++]=C; out[p++]=1; out[p++]=B; out[p++]=S; out[p++]=v; break; case GA1: v=q[i++]; out[p++]=G; out[p++]=v; out[p++]=C; out[p++]=1; out[p++]=A; break; case GB1: v=q[i++]; out[p++]=G; out[p++]=v; out[p++]=C; out[p++]=1; out[p++]=B; break; case C0: out[p++]=C; out[p++]=0; break; case C1: out[p++]=C; out[p++]=1; break; case CM1: out[p++]=C; out[p++]=0x7f; break; case CM2: out[p++]=C; out[p++]=0x7e; break; case SH2: out[p++]=C; out[p++]=2; out[p++]=SL_; out[p++]=A; break; case RE: out[p++]=RT; out[p++]=E; break; case B0E: out[p++]=BR; out[p++]=0; out[p++]=E; out[p++]=E; break; case AS: out[p++]=A; out[p++]=S; out[p++]=q[i++]; break; case BS: out[p++]=B; out[p++]=S; out[p++]=q[i++]; break; case ZS: out[p++]=C; out[p++]=0; out[p++]=S; out[p++]=q[i++]; break; case OS: out[p++]=C; out[p++]=1; out[p++]=S; out[p++]=q[i++]; break; case L8Z: out[p++]=L8; out[p++]=0; out[p++]=0; break; case S8Z: out[p++]=S8; out[p++]=0; out[p++]=0; break; case L3Z: out[p++]=L32; out[p++]=2; out[p++]=0; break; case S3Z: out[p++]=S32; out[p++]=2; out[p++]=0; break; case EQI: out[p++]=EQ; out[p++]=IF; out[p++]=V; break; case RM1: out[p++]=IF; out[p++]=V; out[p++]=C; out[p++]=0x7f; out[p++]=RT; out[p++]=E; break; case SC2:
g=q[i++]; idx=q[i++]; val=q[i++];out[p++]=G; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL_; out[p++]=A;
out[p++] = C; if (val >= -64 && val < 64) out[p++] = val & 0x7f; else p = writeSleb32(out, p, val);out[p++]=S32; out[p++]=2; out[p++]=0; break;}}}
return p;}
export function buildDiffWasm() {
const types=[],typeMap=new Map();
const internType=(params,results)=>{
const key=`${params.join(',')}=>${results.join(',')}`;
let id=typeMap.get(key);
if (id === undefined) { id=types.length; types.push({ params,results }); typeMap.set(key,id); }
return id;};
const gOB=0,gOL=1,gNB=2,gNL=3,gArB=4,gRaw=5,gOSt=6,gNSt=7,gOEn=8,gNEn=9,gPfx=10,gSfx=11,gN=12,gM=13,gArP=14,gOBnd=15,gOHsh=16,gNBnd=17,gBkts=18,gHMsk=19,gA=20,gB=21,gCA=22,gCB=23,gPA=24,gPB=25,gRDel=26,gRIns=27,gPUA=28,gPUB=29,gSlX=30,gSlY=31,gSfD=32,gSfI=33,gNSlb=34,gSgX=35,gSgY=36,gSgU=37,gNSeg=38,gVp=39,gVc=40,gRep=41,gCkM=42,gCkD=43,gCkP=44,gCkC=45,gU=46,gRKnd=47,gRCnt=48,gOpL=49,gChO=50,gChP=51,gChD=52,gChI=53,gNCh=54,gHSt=55,gHEn=56,gNHnk=57,gDel=58,gIns=59,gOutB=60,gOutE=61,gJCur=62,gWB=63,gWEn=64,gWPos=65,gWKp=66,gWEof=67,gWCap=68,gSSt=69,gCIdx=70,gCSt=71,gCEn=72,gSOut=73,gSFlg=74,gc=75;
const fnMem=0,fnPrep=1,fnCntLn=2,fnTrim=3,fnEq=4,fnScan=5,fnBnd=6,fnMyr=7,fnSMyr=8,fnCh=9,fnDec=10,fnPLn=11,fnPat=12,fnAsc=13,fnGOut=14,fnWs=15,fnSkS=16,fnScR=17,fnUn=18,fnEsc=19,fnExp=20,fnEWin=21,fnSIn=22,fnSRf=23,fnSNx=24,fnGKp=25,fnGCSt=26,fnGCEn=27,fnGSOut=28,fnGIdx=29,fc=30;
const funcs=new Array(fc);
const def=(id,params,results,build)=>{
const locals=[];
const loc=(t=I32)=>{const x=params.length+locals.length;locals.push(t);return x;};const L=(n,t=I32)=>{const a=[];for(let i=0;i<n;i++)a.push(loc(t));return a;};const q=build(loc,L);
q.push(E);funcs[id]={ typeIdx: internType(params,results),locals,q };};
def(fnMem,[I32],[],(loc,L)=>{
const need=0,curB=loc(),curP=loc();
return [MSZ,T,curP,C,16,SL_,S,curB,G,need,G,curB,GU,UV,G,need,C,65535,A,C,16,SR,G,curP,B,MGR,CM1,EQI,UNR,EE,];});
def(fnPrep,[I32,I32],[I32],(loc,L)=>{
const oLen=0,nLen=1,nBase=loc(),ab=loc();
return [C0,GS,gRaw,C0,GS,gOB,G,oLen,GS,gOL,G,oLen,C,31,A,C,-16,AN,T,nBase,GS,gNB,G,nLen,GS,gNL,G,nBase,G,nLen,A,C,31,A,C,-16,AN,T,ab,GS,gArB,G,ab,C,64,A,CL,fnMem,G,nBase,];});
def(fnCntLn,[I32,I32],[I32],(loc,L)=>{
const ptr=0,len=1,cnt=loc(),end=loc(),end16=loc(),p=loc(),carry=loc(),mask=loc(),mN=loc(),b=loc();
const [nl16,bs16,n16,v]=L(4,V128);
return [G,len,EZ,UV,C0,RE,ZS,cnt,G,ptr,S,p,G,ptr,G,len,A,T,end,C,16,BS,end16,GG,gRaw,UV,ZS,carry,C,92,VS8,S,bs16,C,110,VS8,S,n16,BLP,G,p,G,end16,GT,BF1,G,p,VLD,0,T,v,G,bs16,VE8,VBM,S,mask,G,v,G,n16,VE8,VBM,S,mN,G,cnt,G,mask,C1,SL_,G,carry,OR,G,mN,AN,POP,AS,cnt,G,mask,C,15,SR,S,carry,G,p,C,16,AS,p,B0E,BLP,G,p,G,end,GEU,BF1,G,p,L8Z,S,b,G,carry,G,b,C,110,EQ,AN,UV,INC,cnt,E,G,b,C,92,EQ,S,carry,INC,p,B0E,
G,len,C,2,GEU,IF,I32,G,end,C,2,B,L8Z,C,92,EQ,GB1,end,L8Z,C,110,EQ,AN,EL,C0,E,EZ,UV,INC,cnt,E,EL,C,10,VS8,S,nl16,BLP,G,p,G,end16,GT,BF1,G,cnt,G,p,VLD,0,G,nl16,VE8,VBM,POP,AS,cnt,G,p,C,16,AS,p,B0E,BLP,G,p,G,end,GEU,BF1,G,p,L8Z,C,10,EQ,G,cnt,AS,cnt,INC,p,B0E,GB1,end,L8Z,C,10,NE,UV,INC,cnt,EE,G,cnt,];});
def(fnTrim,[],[],(loc,L)=>{
const [oBase,nBase,oLen,nLen,minL,p,min16]=L(7);
const [oPtr,nPtr,s,maxS,maxS16,mask,raw,okO,okN]=L(9);
return [GG,gOB,S,oBase,GG,gNB,S,nBase,GG,gOL,S,oLen,GG,gNL,S,nLen,GG,gRaw,S,raw,G,oLen,G,nLen,G,oLen,G,nLen,LU,SL,S,minL,ZS,p,G,minL,C,16,BS,min16,BLP,G,p,G,min16,GT,BF1,G,oBase,G,p,A,VLD,0,G,nBase,G,p,A,VLD,0,VE8,VBM,C,0xffff,XR,T,mask,UV,G,p,G,mask,CTZ,AS,p,BR,2,E,G,p,C,16,AS,p,B0E,BLP,G,p,G,minL,GEU,BF1,G,oBase,G,p,A,L8Z,G,nBase,G,p,A,L8Z,NE,BF1,INC,p,B0E,G,p,G,oLen,EQ,G,p,G,nLen,EQ,AN,UV,G,oBase,G,oLen,CL,fnCntLn,GS,gPfx,
C0,GS,gSfx,G,oLen,GS,gOSt,G,nLen,GS,gNSt,G,oLen,GS,gOEn,G,nLen,GS,gNEn,RE,G,raw,UV,BLP,G,p,EZ,BF1,G,p,C,2,GEU,IF,I32,G,oBase,G,p,A,C,2,B,L8Z,C,92,EQ,G,oBase,G,p,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,E,BF1,DEC,p,B0E,EL,BLP,G,p,EZ,BF1,G,oBase,G,p,A,C1,B,L8Z,C,10,EQ,BF1,DEC,p,B0E,E,G,p,GS,gOSt,G,p,GS,gNSt,G,oBase,G,p,CL,fnCntLn,GS,gPfx,G,oLen,G,p,BS,maxS,G,nLen,G,p,BS,mask,G,maxS,G,mask,G,maxS,G,mask,LU,SL,S,maxS,ZS,s,G,maxS,C,16,BS,maxS16,
BLP,G,s,G,maxS16,GT,BF1,G,oBase,G,oLen,A,G,s,B,C,16,B,VLD,0,G,nBase,G,nLen,A,G,s,B,C,16,B,VLD,0,VE8,VBM,C,0xffff,XR,T,mask,UV,G,s,G,mask,C,16,SL_,CLZ,AS,s,BR,2,E,G,s,C,16,AS,s,B0E,BLP,G,s,G,maxS,GEU,BF1,G,oBase,G,oLen,A,G,s,B,C1,B,L8Z,G,nBase,G,nLen,A,G,s,B,C1,B,L8Z,NE,BF1,INC,s,B0E,G,oLen,G,s,BS,oPtr,G,nLen,G,s,BS,nPtr,G,s,C0,GT,UV,G,raw,UV,
G,oPtr,G,p,EQ,IF,I32,C1,EL,G,oPtr,G,p,C,2,A,GEU,IF,I32,G,oBase,G,oPtr,A,C,2,B,L8Z,C,92,EQ,G,oBase,G,oPtr,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,EE,S,okO,G,nPtr,G,p,EQ,IF,I32,C1,EL,G,nPtr,G,p,C,2,A,GEU,IF,I32,G,nBase,G,nPtr,A,C,2,B,L8Z,C,92,EQ,G,nBase,G,nPtr,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,EE,S,okN,G,okO,G,okN,AN,EZ,UV,BLP,G,oPtr,G,oLen,GEU,BF1,G,oBase,G,oPtr,A,L8Z,C,92,EQ,GA1,oPtr,G,oLen,LU,AN,IF,I32,G,oBase,G,oPtr,A,C1,A,L8Z,C,110,EQ,EL,C0,E,
UV,G,oPtr,C,2,AS,oPtr,G,nPtr,C,2,AS,nPtr,BR,2,E,INC,oPtr,INC,nPtr,B0E,E,EL,G,oPtr,G,p,EQ,IF,I32,C1,EL,G,oBase,G,oPtr,A,C1,B,L8Z,C,10,EQ,E,G,nPtr,G,p,EQ,IF,I32,C1,EL,G,nBase,G,nPtr,A,C1,B,L8Z,C,10,EQ,E,AN,EZ,UV,BLP,G,oPtr,G,oLen,GEU,BF1,G,oBase,G,oPtr,A,L8Z,C,10,EQI,INC,oPtr,INC,nPtr,BR,2,E,INC,oPtr,INC,nPtr,B0E,EE,E,G,oPtr,GS,gOEn,G,nPtr,GS,gNEn,
G,oBase,G,oPtr,A,G,oLen,G,oPtr,B,CL,fnCntLn,GS,gSfx,];});
def(fnEq,[I32,I32,I32],[I32],(loc,L)=>{
const p1=0,p2=1,len=2,k=loc();
return [ZS,k,BLP,G,k,C,16,A,G,len,GU,BF1,G,p1,G,k,A,VLD,0,G,p2,G,k,A,VLD,0,VE8,VBM,C,0xffff,NE,UV,C0,RE,G,k,C,16,AS,k,B0E,BLP,G,k,C,8,A,G,len,GU,BF1,G,p1,G,k,A,L64,0,G,p2,G,k,A,L64,0,I6NE,UV,C0,RE,G,k,C,8,AS,k,B0E,BLP,G,k,G,len,GEU,BF1,G,p1,G,k,A,L8Z,G,p2,G,k,A,L8Z,NE,UV,C0,RE,INC,k,B0E,C1,];});
def(fnScan,[],[],(loc,L)=>{
const [n,m,hCap,hMask,ptr,raw]=L(6);
const [oBase,nBase,oB,oH,nB,bkts]=L(6);
const [aB,bB,cAB,cBB,pAB,pBB]=L(6);
const [pos,end,end16,end8,b,sh,mask,bPtr,hPtr]=L(9);
const [hp,i,j,st,len,slot,bk,rep,rs,fnd,ap]=L(11);
const [tryI,os,oe,lenA,mtc,survEnd]=L(6);
const [h,tailW]=L(2,I64);const [nl16,bs16]=L(2,V128);
const q=[
GG,gRaw,S,raw,GG,gOB,T,oBase,GG,gOSt,A,GG,gOEn,GG,gOSt,B,CL,fnCntLn,T,n,GS,gN,GG,gNB,T,nBase,GG,gNSt,A,GG,gNEn,GG,gNSt,B,CL,fnCntLn,T,m,GS,gM,GG,gArB,S,ptr,];
const alloc=(gVar,...szOps)=>{
q.push(G,ptr,GS,gVar,G,ptr);
for (let t=0; t < szOps.length; t++) q.push(szOps[t]);
q.push(A,C,7,A,C,-8,AN,S,ptr);};alloc(gOBnd,G,n,C,4,A,C,2,SL_);alloc(gNBnd,G,m,C,4,A,C,2,SL_);q.push(G,ptr,GS,gOutB);
const pushScanPlain=(baseL,stG,enG,bG)=>{
q.push(GG,stG,S,pos,GG,enG,S,end,GG,bG,T,bPtr,G,pos,S3Z,BLP,G,pos,G,end,GEU,BF1,G,raw,UV,BLP,G,pos,G,end,GEU,BF1,G,baseL,G,pos,A,L8Z,C,92,EQ,GA1,pos,G,end,LU,AN,IF,I32,G,baseL,G,pos,A,C1,A,L8Z,C,110,EQ,EL,C0,E,UV,G,pos,C,2,AS,pos,BR,2,E,INC,pos,B0E,EL,BLP,G,pos,G,end,GEU,BF1,G,baseL,G,pos,A,L8Z,C,10,EQI,INC,pos,BR,2,E,INC,pos,B0E,E,G,bPtr,C,4,A,T,bPtr,G,pos,S3Z,B0E,);};q.push(G,n,EZ,G,m,EZ,OR,IF,V);
alloc(gChO,C,16); alloc(gChP,C,16);alloc(gChD,C,16); alloc(gChI,C,16);alloc(gHSt,C,16); alloc(gHEn,C,16);q.push(G,ptr,GS,gArP,G,ptr,C,64,A,CL,fnMem);q.push(G,n,IF,V); pushScanPlain(oBase,gOSt,gOEn,gOBnd); q.push(E);q.push(G,m,IF,V); pushScanPlain(nBase,gNSt,gNEn,gNBnd); q.push(E);q.push(RT,E,C,16,S,hCap,BLP,G,hCap,G,n,C1,SL_,GEU,BF1,G,hCap,C1,SL_,S,hCap,B0E,GB1,hCap,T,hMask,GS,gHMsk,);alloc(gA,G,n,C,4,A,C,2,SL_);alloc(gB,G,m,C,4,A,C,2,SL_);alloc(gRDel,G,n,C,4,A,C,2,SL_);
alloc(gRIns,G,m,C,4,A,C,2,SL_);alloc(gPUA,G,n,C,4,A,C,2,SL_);alloc(gPUB,G,m,C,4,A,C,2,SL_);alloc(gSlX,G,n,C,4,A,C,2,SL_);alloc(gSlY,G,m,C,4,A,C,2,SL_);alloc(gCA,G,n,C,4,A,C,2,SL_);alloc(gCB,G,n,C,4,A,C,2,SL_);alloc(gPB,G,n,C,4,A,C,2,SL_);q.push(G,ptr,S,survEnd);alloc(gOHsh,G,n,C,4,A,C,3,SL_);alloc(gBkts,G,hCap,C,2,SL_);alloc(gPA,G,n,C,4,A,C,2,SL_);
const pushFindAndHash=(baseL)=>{
q.push(G,raw,UV,BLP,G,pos,G,end16,GT,BF1,G,baseL,G,pos,A,VLD,0,G,bs16,VE8,VBM,S,mask,BLP,G,mask,EZ,BF1,G,mask,CTZ,S,b,G,pos,G,b,A,C1,A,G,end,LU,UV,G,baseL,G,pos,G,b,A,C1,A,A,L8Z,C,110,EQI,G,pos,G,b,A,C,2,AS,pos,BR,6,EE,G,mask,GB1,mask,AN,S,mask,B0E,G,pos,C,16,AS,pos,B0E,BLP,G,pos,G,end,GEU,BF1,G,baseL,G,pos,A,L8Z,C,92,EQ,GA1,pos,G,end,LU,AN,UV,G,baseL,G,pos,A,C1,A,L8Z,C,110,EQI,G,pos,C,2,AS,pos,BR,4,EE,INC,pos,B0E,EL,
BLP,G,pos,G,end16,GT,BF1,G,baseL,G,pos,A,VLD,0,G,nl16,VE8,VBM,T,mask,UV,G,pos,G,mask,CTZ,A,C1,AS,pos,BR,3,E,G,pos,C,16,AS,pos,B0E,BLP,G,pos,G,end,GEU,BF1,G,baseL,G,pos,A,L8Z,C,10,EQI,INC,pos,BR,2,E,INC,pos,B0E,E,C6,0x84222325,0xcbf29ce4,S,h,G,st,S,hp,G,pos,C,8,BS,end8,BLP,G,hp,G,end8,GT,BF1,G,h,G,baseL,G,hp,A,L64,0,I6X,C6,0x1b3,0x100,I6M,S,h,G,hp,C,8,AS,hp,B0E,G,hp,G,pos,LU,UV,C6,0,0,S,tailW,ZS,sh,BLP,
G,hp,G,pos,GEU,BF1,G,tailW,G,baseL,G,hp,A,L8Z,EXU,G,sh,EXU,I6SL,I6O,S,tailW,G,sh,C,8,AS,sh,INC,hp,B0E,G,h,G,tailW,I6X,C6,0x1b3,0x100,I6M,S,h,E,);};
const emitFastEqMatch=(p1,p2,lenL)=>{
q.push(G,p1,VLD,0,G,p2,VLD,0,VE8,VBM,C,0xffff,XR,S,ap,G,lenL,C,16,LEU,UV,G,ap,C,32,G,lenL,B,SL_,EZ,S,mtc,EL,G,ap,EZ,UV,G,lenL,C,32,LEU,UV,G,p1,G,lenL,A,C,16,B,VLD,0,G,p2,G,lenL,A,C,16,B,VLD,0,VE8,VBM,C,0xffff,EQ,S,mtc,EL,G,p1,C,16,A,G,p2,C,16,A,G,lenL,C,16,B,CL,fnEq,S,mtc,EE,E,);};q.push(G,ptr,C,64,A,CL,fnMem,GG,gBkts,T,bkts,C0,G,hCap,C,2,SL_,MFL,GG,gCA,T,cAB,C0,G,n,C,2,SL_,MFL,GG,gCB,T,cBB,C0,G,n,C,2,SL_,MFL,GG,gOBnd,S,oB,GG,gOHsh,S,oH,GG,gNBnd,S,nB,
GG,gA,S,aB,GG,gB,S,bB,GG,gPA,S,pAB,GG,gPB,S,pBB,C,10,VS8,S,nl16,C,92,VS8,S,bs16,GG,gOSt,S,pos,GG,gOEn,S,end,G,end,C,16,BS,end16,G,oB,G,pos,S3Z,G,oB,S,bPtr,G,oH,S,hPtr,ZS,i,BLP,G,i,G,n,GEU,BF1,G,pos,S,st,);pushFindAndHash(oBase);q.push(G,pos,G,st,BS,len,G,bPtr,C,4,A,T,bPtr,G,pos,S3Z,G,hPtr,G,h,S64,0,G,hPtr,C,8,AS,hPtr,G,h,G,h,C6,32,0,I6SR,I6X,WR,G,hMask,AN,S,slot,BLP,LL,bkts,slot,T,bk,EZ,UV,GA1,i,S,ap,SL2,bkts,slot,ap,SL2,aB,i,i,SC2,cAB,i,1,SL2,pAB,i,i,BR,2,E,
GB1,bk,S,rep,G,oH,G,rep,C,3,SL_,A,L64,0,G,h,I6EQ,G,oB,G,rep,SH2,T,ap,L32,4,G,ap,L3Z,T,rs,B,G,len,EQ,AN,UV,G,oBase,G,rs,A,G,oBase,G,st,A,G,len,CL,fnEq,UV,SL2,aB,i,rep,G,cAB,G,rep,SH2,T,ap,G,ap,L3Z,C1,A,S3Z,BR,3,EE,GA1,slot,G,hMask,AN,S,slot,B0E,INC,i,B0E,GG,gNSt,S,pos,GG,gNEn,S,end,G,end,C,16,BS,end16,G,nB,G,pos,S3Z,G,nB,S,bPtr,ZS,i,ZS,j,BLP,G,j,G,m,GEU,BF1,ZS,mtc,G,i,S,tryI,BK,V,G,tryI,G,n,LU,UV,
G,oB,G,tryI,SH2,T,ap,L3Z,S,os,G,ap,L32,4,S,oe,G,oe,G,os,BS,lenA,G,pos,G,lenA,A,G,end,LEU,G,pos,G,lenA,A,G,end,EQ,G,raw,IF,I32,G,lenA,C,2,GEU,IF,I32,G,oBase,G,oe,A,C,2,B,L8Z,C,92,EQ,G,oBase,G,oe,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,E,EL,G,oBase,G,oe,A,C1,B,L8Z,C,10,EQ,E,OR,AN,UV,G,oBase,G,os,AS,rs,G,nBase,G,pos,AS,bk,);emitFastEqMatch(rs,bk,lenA);q.push(G,mtc,BF,2,EE,GA1,tryI,T,tryI,G,n,LU,UV,G,oB,G,tryI,SH2,T,ap,L3Z,S,os,G,ap,L32,4,S,oe,G,oe,G,os,BS,lenA,
G,pos,G,lenA,A,G,end,LEU,G,pos,G,lenA,A,G,end,EQ,G,raw,IF,I32,G,lenA,C,2,GEU,IF,I32,G,oBase,G,oe,A,C,2,B,L8Z,C,92,EQ,G,oBase,G,oe,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,E,EL,G,oBase,G,oe,A,C1,B,L8Z,C,10,EQ,E,OR,AN,UV,G,oBase,G,os,AS,rs,G,nBase,G,pos,AS,bk,);emitFastEqMatch(rs,bk,lenA);q.push(E,EE,G,mtc,UV,G,pos,G,lenA,AS,pos,G,bPtr,C,4,A,T,bPtr,G,pos,S3Z,LL,aB,tryI,S,rep,SL2,bB,j,rep,G,cBB,G,rep,SH2,T,ap,G,ap,L3Z,C1,A,S3Z,SL2,pBB,rep,j,GA1,tryI,S,i,EL,G,pos,S,st,);
pushFindAndHash(nBase);q.push(G,pos,G,st,BS,len,G,bPtr,C,4,A,T,bPtr,G,pos,S3Z,G,h,G,h,C6,32,0,I6SR,I6X,WR,G,hMask,AN,S,slot,C,-3,S,fnd,BLP,LL,bkts,slot,T,bk,EZ,BF1,GB1,bk,S,rep,G,oH,G,rep,C,3,SL_,A,L64,0,G,h,I6EQ,G,oB,G,rep,SH2,T,ap,L32,4,G,ap,L3Z,T,rs,B,G,len,EQ,AN,UV,G,oBase,G,rs,A,G,nBase,G,st,A,G,len,CL,fnEq,UV,G,rep,S,fnd,G,cBB,G,rep,SH2,T,ap,G,ap,L3Z,C1,A,S3Z,SL2,pBB,rep,j,LL,cAB,rep,C1,EQI,LL,pAB,rep,C1,AS,i,EL,G,i,C,2,A,G,n,LU,UV,
G,i,C,2,AS,ap,LL,aB,ap,G,rep,EQI,G,i,C,3,AS,i,EE,E,BR,3,EE,GA1,slot,G,hMask,AN,S,slot,B0E,SL2,bB,j,fnd,E,INC,j,B0E,G,survEnd,GS,gArP,);
return q;});
def(fnBnd,[],[I32],(loc,L)=>{
const [n,m,minNM,ptr]=L(4);
const [i,j,acc,id,sc,kTotal,tLen]=L(7);
const [lo,hi,mid,cur,k,kHint,idx,d]=L(8);
const [au,bu,al,bl,nc,fnd]=L(6);
const [U,g,x0,y0,x1,y1,gn,gm,maxGD,sA,sB]=L(11);
const [diag,xr,xa,cr,ca,nx,ny,slv,tmp]=L(9);
const [LB,slk,maxB,minB2,ex,ey,w,ns,curU,lastG,endG]=L(11);
const [aB,bB,gvP,gvC,xaB,ybB,K,ep,d0,i0]=L(10);
const [pMax,sMin,sPrev,v,pen]=L(5);
const [cAB,cBB,rDB,rIB,psB,pAB,pBB]=L(7);
const [snB,tVB,tAB,pIB,aAB,aBB,gDB]=L(7);
const [sAB,cXB,cYB,sXB,sYB]=L(5);
const [isU,lAB,lBB,uBB,brB,okB]=L(6);
const [sCrB,sfDB,sfIB]=L(3);
const q=[
GG,gN,S,n,GG,gM,S,m,G,n,G,m,G,n,G,m,LU,SL,S,minNM,GG,gA,S,aB,GG,gB,S,bB,GG,gCA,S,cAB,GG,gCB,S,cBB,GG,gPB,S,psB,GG,gRDel,S,rDB,GG,gRIns,S,rIB,GG,gPUA,S,pAB,GG,gPUB,S,pBB,GG,gSlX,S,sXB,GG,gSlY,S,sYB,GG,gArP,S,ptr,];
const allocL=(vLoc,...szOps)=>{
q.push(G,ptr,S,vLoc,G,ptr);
for (let t=0; t < szOps.length; t++) q.push(szOps[t]);
q.push(A,C,7,A,C,-8,AN,S,ptr);};allocL(sfDB,G,minNM,C,4,A,C,2,SL_);allocL(sfIB,G,minNM,C,4,A,C,2,SL_);q.push(G,sfDB,GS,gSfD,G,sfIB,GS,gSfI);q.push(G,ptr,GS,gArP);allocL(snB,G,n,C,4,A,C,2,SL_);allocL(tVB,G,n,C,4,A,C,2,SL_);allocL(tAB,G,minNM,C,4,A,C,2,SL_);q.push(G,sXB,S,pIB);allocL(aAB,G,minNM,C,4,A,C,2,SL_);allocL(aBB,G,minNM,C,4,A,C,2,SL_);allocL(sAB,G,m,C,1050,G,m,C,1050,GT,SL,C,2,SL_);q.push(G,sAB,S,gvP,G,sAB,C,2080,A,S,gvC);allocL(isU,G,n,G,m,G,n,G,m,GT,SL,C,4,A);q.push(G,isU,S,okB);
allocL(lAB,G,n,C,4,A);allocL(lBB,G,m,C,4,A);allocL(uBB,G,m,C,4,A);q.push(G,ptr,C,64,A,CL,fnMem);q.push(G,snB,C0,G,n,C,2,SL_,MFL,ZS,acc,GB1,n,S,i,BLP,G,i,C0,LT,BF1,LL,aB,i,S,id,LL,snB,id,C1,AS,sc,SL2,snB,id,sc,G,sc,LL,cBB,id,GT,UV,INC,acc,E,SL2,rDB,i,acc,DEC,i,B0E,SC2,rDB,n,0,G,snB,C0,G,n,C,2,SL_,MFL,ZS,acc,GB1,m,S,i,BLP,G,i,C0,LT,BF1,LL,bB,i,T,id,C,-3,EQI,INC,acc,EL,LL,snB,id,C1,AS,sc,SL2,snB,id,sc,
G,sc,LL,cAB,id,GT,UV,INC,acc,EE,SL2,rIB,i,acc,DEC,i,B0E,SC2,rIB,m,0,G,isU,C0,G,n,MFL,G,pAB,C0,S3Z,ZS,kTotal,ZS,tLen,ZS,i,BLP,G,i,G,n,GEU,BF1,LL,aB,i,S,id,LL,cAB,id,C1,EQ,LL,cBB,id,C1,EQ,AN,UV,G,isU,G,id,A,C1,S8Z,INC,kTotal,LL,psB,id,S,j,G,tLen,EZ,UV,G,tVB,G,j,S3Z,G,tAB,G,i,S3Z,SC2,pIB,i,-1,OS,tLen,EL,GB1,tLen,S,mid,LL,tVB,mid,G,j,LT,UV,SL2,tVB,tLen,j,SL2,tAB,tLen,i,LL,tAB,mid,S,tmp,SL2,pIB,i,tmp,INC,tLen,
EL,ZS,lo,G,tLen,S,hi,BLP,G,lo,G,hi,GE,BF1,G,lo,G,hi,A,C1,SR,S,mid,LL,tVB,mid,G,j,LT,UV,GA1,mid,S,lo,EL,G,mid,S,hi,E,B0E,SL2,tVB,lo,j,SL2,tAB,lo,i,G,lo,C0,GT,IF,I32,GB1,lo,S,mid,LL,tAB,mid,EL,CM1,E,S,tmp,SL2,pIB,i,tmp,EE,E,GA1,i,T,i,SL2,pAB,i,kTotal,B0E,G,pBB,C0,S3Z,ZS,acc,ZS,i,BLP,G,i,G,m,GEU,BF1,LL,bB,i,T,id,C0,GE,UV,G,acc,G,isU,G,id,A,L8Z,AS,acc,E,GA1,i,T,i,SL2,pBB,i,acc,B0E,G,lAB,C0,G,n,MFL,G,lBB,C0,G,m,MFL,
G,tLen,C0,GT,IF,I32,GB1,tLen,S,mid,LL,tAB,mid,EL,CM1,E,S,cur,G,tLen,S,k,BLP,G,k,C1,LT,BF1,SL2,aAB,k,cur,LL,aB,cur,S,id,LL,psB,id,S,tmp,SL2,aBB,k,tmp,G,lAB,G,cur,A,C1,S8Z,G,lBB,G,tmp,A,C1,S8Z,LL,pIB,cur,S,cur,DEC,k,B0E,G,aAB,CM1,S3Z,G,aBB,CM1,S3Z,GA1,tLen,S,mid,SL2,aAB,mid,n,SL2,aBB,mid,m,);allocL(brB,G,tLen,C,4,A);allocL(gDB,G,tLen,C,4,A,C,2,SL_);allocL(cXB,G,tLen,C,4,A,C,2,SL_);allocL(cYB,G,tLen,C,4,A,C,2,SL_);q.push(G,ptr,C,64,A,CL,fnMem,
G,brB,C0,G,tLen,C,2,A,MFL,CM1,S,maxB,OS,k,ZS,i,BLP,G,i,G,n,GEU,BF1,LL,aB,i,S,id,G,isU,G,id,A,L8Z,UV,LL,psB,id,S,bu,G,k,G,tLen,LE,UV,LL,aAB,k,G,i,EQI,G,maxB,LL,aBB,k,LT,UV,G,brB,G,k,A,C1,S8Z,E,INC,k,EE,G,bu,G,maxB,GT,UV,G,bu,S,maxB,EE,INC,i,B0E,G,m,S,minB2,G,tLen,S,k,GB1,n,S,i,BLP,G,i,C0,LT,BF1,LL,aB,i,S,id,G,isU,G,id,A,L8Z,UV,LL,psB,id,S,bu,G,k,C1,GE,UV,LL,aAB,k,G,i,EQI,G,minB2,LL,aBB,k,LE,UV,G,brB,G,k,A,C0,S8Z,E,
DEC,k,EE,G,bu,G,minB2,LT,UV,G,bu,S,minB2,EE,DEC,i,B0E,ZS,U,ZS,g,BLP,G,g,G,tLen,GT,BF1,LL,aAB,g,C1,AS,x0,LL,aBB,g,C1,AS,y0,GA1,g,S,mid,LL,aAB,mid,G,x0,BS,gn,LL,aBB,mid,G,y0,BS,gm,G,gn,C0,GT,G,gm,C0,GT,AN,UV,G,aB,G,x0,C,2,SL_,AS,xaB,G,bB,G,y0,C,2,SL_,AS,ybB,BLP,G,gn,C0,LE,G,gm,C0,LE,OR,BF1,G,xaB,L3Z,G,ybB,L3Z,NE,BF1,INC,x0,INC,y0,G,xaB,C,4,AS,xaB,G,ybB,C,4,AS,ybB,DEC,gn,DEC,gm,B0E,
BLP,G,gn,C0,LE,G,gm,C0,LE,OR,BF1,GB1,gn,S,cur,GB1,gm,S,mid,LL,xaB,cur,LL,ybB,mid,NE,BF1,G,cur,S,gn,G,mid,S,gm,B0E,ZS,tmp,BK,V,G,gn,EZ,G,gm,EZ,OR,UV,G,gn,G,gm,AS,tmp,BR,1,E,G,gn,C1,EQ,G,gm,C1,EQ,AN,UV,C,2,S,tmp,BR,1,E,G,gn,G,gm,AS,mid,C,256,G,mid,C,256,G,mid,LT,SL,S,maxGD,G,x0,G,gn,AS,cur,LL,aB,cur,S,sA,G,y0,G,gm,AS,mid,LL,bB,mid,S,sB,SC2,aB,cur,-1,SC2,bB,mid,-2,ZS,x1,BLP,LL,xaB,x1,LL,ybB,x1,NE,BF1,INC,x1,B0E,
G,gvP,G,x1,S3Z,ZS,slv,OS,d,BLP,G,d,G,maxGD,GT,BF1,ZS,idx,C0,G,d,BS,diag,BLP,G,idx,G,d,GT,BF1,G,idx,C0,GT,IF,I32,GB1,idx,S,lo,LL,gvP,lo,EL,CM2,E,S,xr,G,idx,G,d,LT,IF,I32,LL,gvP,idx,EL,CM2,E,S,xa,G,xr,C0,GE,G,xr,G,gn,LT,AN,S,cr,G,xa,C0,GE,G,xa,G,diag,B,C1,B,G,gm,LT,AN,S,ca,G,cr,G,ca,EZ,GA1,xr,G,xa,GE,OR,AN,IF,I32,GA1,xr,EL,G,ca,IF,I32,G,xa,EL,CM2,EE,S,nx,G,nx,C0,LT,UV,SC2,gvC,idx,-2,EL,G,nx,G,diag,BS,ny,
BLP,LL,xaB,nx,LL,ybB,ny,NE,BF1,INC,nx,INC,ny,B0E,G,nx,G,gn,EQ,G,ny,G,gm,EQ,AN,UV,G,d,S,tmp,OS,slv,BR,5,E,SL2,gvC,idx,nx,E,INC,idx,G,diag,C,2,AS,diag,B0E,G,gvP,S,lo,G,gvC,S,gvP,G,lo,S,gvC,INC,d,B0E,SL2,aB,cur,sA,SL2,bB,mid,sB,G,slv,EZ,UV,G,gn,G,gm,AS,tmp,EE,EL,G,gn,G,gm,AS,tmp,E,SL2,gDB,g,tmp,G,U,G,tmp,AS,U,INC,g,B0E,G,U,GS,gU,G,uBB,C0,G,m,MFL,ZS,nc,OS,kHint,ZS,au,BLP,G,au,G,n,GEU,BF1,
LL,aB,au,S,id,G,isU,G,id,A,L8Z,G,lAB,G,au,A,L8Z,EZ,AN,UV,LL,psB,id,S,bu,BLP,G,kHint,G,tLen,GT,BF1,LL,aAB,kHint,G,au,GE,BF1,INC,kHint,B0E,CM1,S,fnd,ZS,d,BLP,G,d,C,16,GT,BF1,G,kHint,G,d,AS,idx,G,idx,C1,GE,G,idx,G,tLen,LE,AN,UV,LL,aBB,idx,S,bl,G,uBB,G,bl,A,L8Z,EZ,UV,LL,aAB,idx,S,al,G,al,G,au,B,T,tmp,C,-16,GE,G,tmp,C,16,LE,AN,UV,G,au,G,al,LT,G,bu,G,bl,GT,AN,G,au,G,al,GT,G,bu,G,bl,LT,AN,OR,UV,G,idx,S,fnd,BR,5,EE,EE,GB1,kHint,G,d,BS,idx,
G,idx,C1,GE,G,idx,G,tLen,LE,AN,UV,LL,aBB,idx,S,bl,G,uBB,G,bl,A,L8Z,EZ,UV,LL,aAB,idx,S,al,G,al,G,au,B,T,tmp,C,-16,GE,G,tmp,C,16,LE,AN,UV,G,au,G,al,LT,G,bu,G,bl,GT,AN,G,au,G,al,GT,G,bu,G,bl,LT,AN,OR,UV,G,idx,S,fnd,BR,5,EE,EE,INC,d,B0E,G,fnd,C0,GT,UV,LL,aAB,fnd,S,al,LL,aBB,fnd,S,bl,G,uBB,G,bu,A,C1,S8Z,G,uBB,G,bl,A,C1,S8Z,SL2,snB,nc,au,SL2,tVB,nc,bu,SL2,tAB,nc,al,SL2,sYB,nc,bl,INC,nc,EE,INC,au,B0E,G,sAB,C0,S3Z,ZS,sPrev,ZS,pMax,ZS,i,
BLP,G,i,G,m,GEU,BF1,G,sPrev,G,pMax,GE,UV,G,okB,G,i,A,C1,S8Z,G,sPrev,S,pMax,EL,G,okB,G,i,A,C0,S8Z,E,ZS,v,G,uBB,G,i,A,L8Z,EZ,UV,LL,bB,i,T,id,C0,GE,UV,LL,cAB,id,C0,GT,UV,G,lBB,G,i,A,L8Z,IF,I32,C,2,EL,CM2,E,S,v,EE,E,G,sPrev,G,v,AS,sPrev,GA1,i,T,i,SL2,sAB,i,sPrev,B0E,G,sPrev,S,sMin,GB1,m,S,i,BLP,G,i,C0,LT,BF1,GA1,i,S,tmp,LL,sAB,tmp,T,sPrev,G,sMin,LT,UV,G,sPrev,S,sMin,E,LL,sAB,i,G,sMin,GT,UV,G,okB,G,i,A,C0,S8Z,E,DEC,i,B0E,
G,cXB,C0,S3Z,G,cYB,C0,S3Z,ZS,K,OS,k,BLP,G,k,G,tLen,GT,BF1,LL,aAB,k,S,au,LL,aBB,k,S,bu,G,au,C0,GT,G,bu,C0,GT,AN,G,uBB,G,bu,A,L8Z,EZ,AN,G,okB,G,bu,A,L8Z,AN,UV,INC,K,SL2,cXB,K,au,SL2,cYB,K,bu,E,INC,k,B0E,GA1,K,T,K,GS,gNSlb,SL2,cXB,K,n,SL2,cYB,K,m,ZS,j,BLP,G,j,G,K,GEU,BF1,LL,cXB,j,S,x0,GA1,j,S,tmp,LL,cXB,tmp,S,x1,BLP,G,x0,G,x1,GEU,BF1,SL2,sXB,x0,j,INC,x0,B0E,INC,j,B0E,SL2,sXB,n,K,);
allocL(sCrB,G,K,C,4,A,C,2,SL_);q.push(G,ptr,C,64,A,CL,fnMem,G,sCrB,C0,G,K,C,2,SL_,MFL,ZS,i,BLP,G,i,G,nc,GEU,BF1,LL,snB,i,S,au,LL,sXB,au,S,j,GA1,j,S,tmp,LL,tAB,i,S,al,LL,tVB,i,S,bu,LL,sYB,i,S,bl,G,al,LL,cXB,j,GE,G,al,LL,cXB,tmp,LT,AN,G,bu,LL,cYB,j,GE,AN,G,bu,LL,cYB,tmp,LT,AN,G,bl,LL,cYB,j,GE,AN,G,bl,LL,cYB,tmp,LT,AN,UV,LL,sCrB,j,C1,AS,cur,SL2,sCrB,j,cur,E,INC,i,B0E,ZS,j,BLP,G,j,G,K,GEU,BF1,LL,cYB,j,S,y0,GA1,j,S,tmp,LL,cYB,tmp,S,y1,
BLP,G,y0,G,y1,GEU,BF1,SL2,sYB,y0,j,INC,y0,B0E,INC,j,B0E,SL2,sYB,m,K,G,snB,C0,G,n,C,2,SL_,MFL,ZS,j,BLP,G,j,G,K,GEU,BF1,GA1,j,T,ep,LL,cXB,ep,S,x1,LL,cXB,j,S,x0,LL,cYB,ep,S,y1,LL,cYB,j,S,y0,G,x1,G,x0,BS,d0,G,y1,G,y0,BS,i0,G,x0,S,cur,BLP,G,cur,G,x1,GEU,BF1,LL,aB,cur,S,id,LL,snB,id,G,ep,NE,UV,SL2,snB,id,ep,SC2,tVB,id,1,EL,LL,tVB,id,C1,AS,tmp,SL2,tVB,id,tmp,E,INC,cur,B0E,G,y0,S,cur,BLP,G,cur,G,y1,GEU,BF1,
LL,bB,cur,T,id,C0,GE,UV,LL,snB,id,G,ep,EQI,LL,tVB,id,T,tmp,C0,GT,UV,DEC,tmp,SL2,tVB,id,tmp,DEC,d0,DEC,i0,EE,E,INC,cur,B0E,LL,sAB,y1,LL,sAB,y0,B,T,tmp,C0,LT,IF,I32,G,tmp,C1,SS,EL,C0,E,S,pen,LL,sCrB,j,S,sc,G,d0,G,sc,A,G,pen,A,T,tmp,C0,GT,IF,I32,G,tmp,EL,C0,E,S,d0,G,i0,G,sc,A,G,pen,A,T,tmp,C0,GT,IF,I32,G,tmp,EL,C0,E,S,i0,SL2,tAB,j,d0,SL2,cXB,j,i0,INC,j,B0E,SC2,sfDB,K,0,SC2,sfIB,K,0,
GA1,K,S,tmp,SC2,sfDB,tmp,0,SC2,sfIB,tmp,0,GB1,K,S,j,BLP,G,j,C0,LT,BF1,GA1,j,S,tmp,LL,sfDB,tmp,LL,tAB,j,AS,d0,SL2,sfDB,j,d0,LL,sfIB,tmp,LL,cXB,j,AS,i0,SL2,sfIB,j,i0,DEC,j,B0E,G,cAB,GS,gSgX,G,cBB,GS,gSgY,G,psB,GS,gSgU,G,rDB,L3Z,G,rIB,L3Z,A,G,kTotal,G,tLen,B,C1,SL_,AS,LB,G,U,G,LB,BS,slk,G,cAB,C0,S3Z,G,cBB,C0,S3Z,ZS,ns,ZS,cur,ZS,lastG,OS,k,BLP,G,k,G,tLen,GT,BF1,LL,aAB,k,S,ex,LL,aBB,k,S,ey,G,ex,G,cur,LT,UV,INC,k,BR,1,E,
ZS,w,G,k,S,endG,BLP,G,ex,G,n,GE,G,ey,G,m,GE,OR,BF1,LL,aB,ex,LL,bB,ey,NE,BF1,G,endG,G,tLen,LE,UV,LL,aAB,endG,G,ex,EQI,G,w,G,brB,G,endG,A,L8Z,AS,w,INC,endG,EE,INC,ex,INC,ey,B0E,G,ex,G,n,LT,G,ey,G,m,LT,AN,G,w,C1,SL_,G,slk,GT,AN,UV,ZS,curU,G,lastG,S,g,BLP,G,g,G,k,GE,BF1,G,curU,LL,gDB,g,AS,curU,INC,g,B0E,SL2,psB,ns,curU,INC,ns,SL2,cAB,ns,ex,SL2,cBB,ns,ey,G,ex,S,cur,GB1,endG,S,lastG,E,G,endG,S,k,B0E,
ZS,curU,G,lastG,S,g,BLP,G,g,G,tLen,GT,BF1,G,curU,LL,gDB,g,AS,curU,INC,g,B0E,SL2,psB,ns,curU,GA1,ns,T,ns,GS,gNSeg,SL2,cAB,ns,n,SL2,cBB,ns,m,G,U,);
return q;});
def(fnMyr,[I32,I32,I32,I32,I32,I32],[],(loc,L)=>{
const x0p=0,y0p=1,x1p=2,y1p=3,uSub=4,useP=5;
const [n,m,dlt,ptr,sA,sB]=L(6);
const [aBase,bBase,vpBase,vcBase,K]=L(5);
const [bSh,bSt,bMk,nCk]=L(4);
const [xs,kLo,kHi,d,remD,lim1,lim2]=L(7);
const [loK,hiK,iLo,iHi,idx,k]=L(6);
const [xRem,xAdd,nx,ny,cRm,cAd]=L(6);
const [jx,jy,sm,pa,pb,exI,exD,sd,si,tmp]=L(10);
const [cCnt,mPtr,bNd,ansD,ansK]=L(5);
const [strd,opLen,curD,curK,curX,bIdx,d0,span]=L(8);
const [ckD,ckL,fLo0,fHi0,bk0,rLo0,rHi0]=L(7);
const [pLo,pHi,s,wLo,wHi,rLo,rHi]=L(7);
const [prR,crR,shB,cILo,cIHi,col]=L(6);
const [trX,trK,stX,opK,nextK,prevX,keep]=L(7);
const [sXB,sYB,pAB,pBB,sfIB,rIB,sfDB,rDB]=L(8);
const q=[
G,x1p,G,x0p,BS,n,G,y1p,G,y0p,BS,m,GG,gOpL,S,opLen,G,n,EZ,G,m,EZ,AN,UV,RE,GG,gSlX,S,sXB,GG,gSlY,S,sYB,GG,gPUA,S,pAB,GG,gPUB,S,pBB,GG,gSfI,S,sfIB,GG,gRIns,S,rIB,GG,gSfD,S,sfDB,GG,gRDel,S,rDB,];
const emitPushOp=(kindOp0,kindOp1,cntOp0,cntOp1)=>{
q.push(G,opLen,C0,GT,IF,I32,GB1,opLen,S,tmp,L8G,gRKnd,tmp,kindOp0,kindOp1,EQ,EL,C0,E,UV,GB1,opLen,S,tmp,LA,gRCnt,tmp,cntOp0,cntOp1,AS,pa,SA,gRCnt,tmp,pa,EL,GG,gRKnd,G,opLen,A,kindOp0,kindOp1,S8Z,GG,gRCnt,G,opLen,SH2,cntOp0,cntOp1,S3Z,INC,opLen,E,);};
const emitIsValid=(kL)=>{
q.push(LL,sXB,nx,S,jx,LL,sYB,ny,S,jy,G,jx,G,jy,G,jx,G,jy,GT,SL,S,sm,G,sm,G,K,LU,IF,I32,GA1,sm,EL,G,K,E,S,tmp,LL,pAB,nx,S,pa,LL,pBB,ny,S,pb,G,pa,G,pb,GT,IF,I32,G,pa,G,pb,B,EL,C0,E,S,exI,G,pb,G,pa,GT,IF,I32,G,pb,G,pa,B,EL,C0,E,S,exD,LL,sfIB,tmp,T,si,LL,rIB,ny,G,exI,A,T,sd,G,si,G,sd,GT,SL,C1,SL_,G,lim1,G,kL,A,LE,LL,sfDB,tmp,T,sd,LL,rDB,nx,G,exD,A,T,si,G,sd,G,si,GT,SL,C1,SL_,G,lim2,G,kL,B,LE,AN,);};q.push(G,n,EZ,IF,V); emitPushOp(C,IN,G,m); q.push(G,opLen,GS,gOpL,RT,E);
q.push(G,m,EZ,IF,V); emitPushOp(C,DL,G,n); q.push(G,opLen,GS,gOpL,RT,E);q.push(G,n,G,m,BS,dlt,GG,gNSlb,S,K,G,uSub,C,8192,LE,UV,C,5,S,bSh,C,32,S,bSt,C,31,S,bMk,EL,C,7,S,bSh,C,128,S,bSt,C,127,S,bMk,E,G,bSt,C,4,AS,strd,GG,gArP,S,ptr,G,ptr,C,16,A,T,vpBase,GS,gVp,G,vpBase,G,uSub,C,12,A,C,2,SL_,AS,ptr,G,ptr,C,16,A,T,vcBase,GS,gVc,G,vcBase,G,uSub,C,12,A,SH2,T,ptr,GS,gRep,G,ptr,GA1,bSt,G,strd,M,C,2,SL_,AS,ptr,G,uSub,G,bSh,SR,C,2,AS,nCk,G,ptr,GS,gCkM,G,ptr,G,nCk,C,4,SL_,AS,ptr,
G,ptr,GS,gCkD,G,ptr,GS,gCkP,G,ptr,C,65536,A,T,tmp,GS,gCkC,G,tmp,CL,fnMem,G,vpBase,C,-16,A,CM2,G,uSub,C,12,A,C,2,SL_,MFL,G,vcBase,C,-16,A,CM2,G,uSub,C,12,A,C,2,SL_,MFL,GG,gA,G,x0p,C,2,SL_,AS,aBase,GG,gB,G,y0p,C,2,SL_,AS,bBase,LA,gA,x1p,S,sA,LA,gB,y1p,S,sB,SAC,gA,x1p,-1,SAC,gB,y1p,-2,ZS,xs,BLP,LL,aBase,xs,LL,bBase,xs,NE,BF1,INC,xs,B0E,G,vpBase,G,xs,S3Z,GG,gCkM,S,mPtr,G,mPtr,C0,S3Z,G,mPtr,C0,S32,4,G,mPtr,C0,S32,8,G,mPtr,GG,gCkP,S32,12,GG,gCkP,G,xs,S3Z,
GG,gCkP,C,4,A,GS,gCkP,OS,cCnt,ZS,ansD,ZS,ansK,ZS,kLo,ZS,kHi,G,xs,G,n,LT,G,xs,G,m,LT,OR,UV,OS,d,BLP,G,d,G,uSub,GT,BF1,G,uSub,G,d,BS,remD,G,remD,G,dlt,BS,lim1,G,remD,G,dlt,AS,lim2,GB1,kLo,S,nx,C0,G,lim1,BS,ny,G,nx,G,ny,G,nx,G,ny,GT,SL,S,loK,GA1,kHi,S,nx,G,lim2,S,ny,G,nx,G,ny,G,nx,G,ny,LT,SL,S,hiK,G,loK,G,d,XR,C1,AN,UV,INC,loK,E,G,hiK,G,d,XR,C1,AN,UV,DEC,hiK,E,G,loK,G,d,A,C1,SS,S,iLo,G,hiK,G,d,A,C1,SS,S,iHi,
GB1,iLo,S,tmp,SC2,vcBase,tmp,-2,GA1,iHi,S,tmp,SC2,vcBase,tmp,-2,SC2,vpBase,d,-2,G,iLo,S,idx,G,loK,S,k,GB1,iLo,S,tmp,LL,vpBase,tmp,S,xRem,BLP,G,idx,G,iHi,GT,BF1,LL,vpBase,idx,S,xAdd,G,xRem,G,n,LU,S,cRm,G,xAdd,C0,GE,G,xAdd,G,k,B,C1,B,G,m,LU,AN,S,cAd,G,cRm,G,cAd,EZ,GA1,xRem,G,xAdd,GE,OR,AN,IF,I32,GA1,xRem,EL,G,cAd,IF,I32,G,xAdd,EL,CM2,EE,S,nx,G,nx,C0,LT,UV,SC2,vcBase,idx,-2,EL,G,nx,G,k,BS,ny,
BLP,LL,aBase,nx,LL,bBase,ny,NE,BF1,INC,nx,INC,ny,B0E,G,nx,G,n,EQ,G,ny,G,m,EQ,AN,UV,G,d,S,ansD,G,k,S,ansK,BR,5,E,SL2,vcBase,idx,nx,E,G,xAdd,S,xRem,INC,idx,G,k,C,2,AS,k,B0E,G,useP,UV,BLP,G,iLo,G,iHi,GT,BF1,LL,vcBase,iLo,S,nx,G,nx,C0,GE,UV,G,nx,G,loK,BS,ny,);emitIsValid(loK);q.push(BF,2,SC2,vcBase,iLo,-2,E,INC,iLo,G,loK,C,2,AS,loK,B0E,BLP,G,iLo,G,iHi,GT,BF1,LL,vcBase,iHi,S,nx,G,nx,C0,GE,UV,G,nx,G,hiK,BS,ny,);
emitIsValid(hiK);q.push(BF,2,SC2,vcBase,iHi,-2,E,DEC,iHi,G,hiK,C,2,BS,hiK,B0E,EL,BLP,G,iLo,G,iHi,GT,BF1,LL,vcBase,iLo,C0,GE,BF1,INC,iLo,G,loK,C,2,AS,loK,B0E,BLP,G,iLo,G,iHi,GT,BF1,LL,vcBase,iHi,C0,GE,BF1,DEC,iHi,G,hiK,C,2,BS,hiK,B0E,E,G,loK,S,kLo,G,hiK,S,kHi,G,vpBase,S,tmp,G,vcBase,T,vpBase,GS,gVp,G,tmp,T,vcBase,GS,gVc,G,d,G,bMk,AN,EZ,UV,G,iHi,G,iLo,B,C1,A,C,2,SL_,S,bNd,G,bNd,C0,LT,UV,ZS,bNd,E,
GG,gCkP,G,bNd,A,GG,gCkC,GU,UV,GG,gCkP,G,bNd,A,C,262144,A,T,tmp,GS,gCkC,G,tmp,CL,fnMem,E,GG,gCkM,G,cCnt,C,4,SL_,AS,mPtr,G,mPtr,G,iLo,S3Z,G,mPtr,G,loK,S32,4,G,mPtr,G,hiK,S32,8,G,mPtr,GG,gCkP,S32,12,G,bNd,C0,GT,UV,GG,gCkP,G,vpBase,G,iLo,SH2,G,bNd,MCP,GG,gCkP,G,bNd,A,GS,gCkP,E,INC,cCnt,E,INC,d,B0E,E,G,ansD,S,curD,G,ansK,S,curK,G,n,S,curX,BLP,G,curD,C0,LE,BF1,GB1,curD,G,bSh,SR,S,bIdx,G,bIdx,G,bSh,SL_,S,d0,G,curD,G,d0,BS,span,
GG,gCkM,G,bIdx,C,4,SL_,AS,mPtr,G,mPtr,L3Z,S,ckL,G,mPtr,L32,4,S,fLo0,G,mPtr,L32,8,S,fHi0,G,mPtr,L32,12,S,ckD,G,curK,G,span,BS,bk0,G,fLo0,G,bk0,G,fLo0,G,bk0,GT,SL,S,rLo0,G,curK,G,span,AS,tmp,G,fHi0,G,tmp,G,fHi0,G,tmp,LT,SL,S,rHi0,GG,gRep,CM2,G,span,C,3,A,C,2,SL_,MFL,G,rLo0,S,k,BLP,G,k,G,rHi0,GT,BF1,G,k,G,bk0,B,C1,SS,S,col,G,k,G,d0,A,C1,SS,G,ckL,BS,tmp,LL,ckD,tmp,S,nx,SA,gRep,col,nx,G,k,C,2,AS,k,B0E,G,rLo0,S,pLo,G,rHi0,S,pHi,OS,s,BLP,G,s,G,span,GT,BF1,G,d0,G,s,AS,d,
G,uSub,G,d,BS,remD,G,remD,G,dlt,BS,lim1,G,remD,G,dlt,AS,lim2,G,curK,G,span,G,s,B,BS,wLo,G,curK,G,span,G,s,B,AS,wHi,GB1,pLo,S,nx,C0,G,lim1,BS,ny,G,nx,G,ny,G,nx,G,ny,GT,SL,S,rLo,G,wLo,G,rLo,G,wLo,G,rLo,GT,SL,S,rLo,GA1,pHi,S,nx,G,lim2,S,ny,G,nx,G,ny,G,nx,G,ny,LT,SL,S,rHi,G,wHi,G,rHi,G,wHi,G,rHi,LT,SL,S,rHi,G,rLo,G,d,XR,C1,AN,UV,INC,rLo,E,G,rHi,G,d,XR,C1,AN,UV,DEC,rHi,E,GB1,s,G,strd,M,S,prR,G,s,G,strd,M,S,crR,G,bk0,G,s,BS,shB,G,rLo,G,shB,B,C1,SS,S,cILo,
G,rHi,G,shB,B,C1,SS,S,cIHi,G,cILo,C0,GT,UV,G,crR,G,cILo,A,C1,BS,tmp,SAC,gRep,tmp,-2,E,G,crR,G,cIHi,A,C1,AS,tmp,SAC,gRep,tmp,-2,G,rLo,S,k,BLP,G,k,G,rHi,GT,BF1,G,k,G,shB,B,C1,SS,S,col,GB1,k,T,tmp,G,pLo,GE,G,tmp,G,pHi,LE,AN,IF,I32,G,prR,G,col,A,C1,BS,tmp,LA,gRep,tmp,EL,CM2,E,S,xRem,GA1,k,T,tmp,G,pLo,GE,G,tmp,G,pHi,LE,AN,IF,I32,G,prR,G,col,AS,tmp,LA,gRep,tmp,EL,CM2,E,S,xAdd,G,xRem,G,n,LU,S,cRm,G,xAdd,C0,GE,G,xAdd,G,k,B,C1,B,G,m,LU,AN,S,cAd,
G,cRm,G,cAd,EZ,GA1,xRem,G,xAdd,GE,OR,AN,IF,I32,GA1,xRem,EL,G,cAd,IF,I32,G,xAdd,EL,CM2,EE,S,nx,G,crR,G,col,AS,tmp,G,nx,C0,LT,UV,SAC,gRep,tmp,-2,EL,G,nx,G,k,BS,ny,BLP,LL,aBase,nx,LL,bBase,ny,NE,BF1,INC,nx,INC,ny,B0E,SA,gRep,tmp,nx,E,G,k,C,2,AS,k,B0E,G,s,G,span,LT,G,useP,AN,UV,BLP,G,cILo,G,cIHi,GT,BF1,G,crR,G,cILo,AS,col,LA,gRep,col,S,nx,G,nx,C0,GE,UV,G,nx,G,rLo,BS,ny,);emitIsValid(rLo);q.push(BF,2,SAC,gRep,col,-2,E,
INC,cILo,G,rLo,C,2,AS,rLo,B0E,BLP,G,cILo,G,cIHi,GT,BF1,G,crR,G,cIHi,AS,col,LA,gRep,col,S,nx,G,nx,C0,GE,UV,G,nx,G,rHi,BS,ny,);emitIsValid(rHi);q.push(BF,2,SAC,gRep,col,-2,E,DEC,cIHi,G,rHi,C,2,BS,rHi,B0E,E,G,rLo,S,pLo,G,rHi,S,pHi,INC,s,B0E,G,curX,S,trX,G,curK,S,trK,G,span,S,s,BLP,G,s,C1,LT,BF1,GB1,s,G,strd,M,S,prR,G,bk0,G,s,BS,shB,G,trK,G,shB,B,C1,SS,S,col,
G,col,C0,GT,IF,I32,G,prR,G,col,A,C1,BS,tmp,LA,gRep,tmp,EL,CM2,E,S,xRem,G,prR,G,col,AS,tmp,LA,gRep,tmp,S,xAdd,G,xRem,G,n,LU,S,cRm,G,xAdd,C0,GE,G,xAdd,G,trK,B,C1,B,G,m,LU,AN,S,cAd,G,cRm,G,cAd,EZ,GA1,xRem,G,xAdd,GE,OR,AN,UV,GA1,xRem,S,stX,C,DL,S,opK,GB1,trK,S,nextK,G,xRem,S,prevX,EL,G,xAdd,S,stX,C,IN,S,opK,GA1,trK,S,nextK,G,xAdd,S,prevX,E,G,trX,G,stX,B,T,keep,C0,GT,UV,);emitPushOp(C,KP,G,keep);q.push(E);emitPushOp(G,opK,C,1);q.push(
G,nextK,S,trK,G,prevX,S,trX,DEC,s,B0E,G,d0,S,curD,G,trK,S,curK,G,trX,S,curX,B0E,G,curX,C0,GT,UV,);emitPushOp(C,KP,G,curX);q.push(E,G,opLen,GS,gOpL,SA,gA,x1p,sA,SA,gB,y1p,sB);
return q;});
def(fnSMyr,[],[],(loc,L)=>{
const [ptr,ns,seg,n1,x0,y0,x1,y1,uSub,useP]=L(10);
return [GG,gArP,S,ptr,G,ptr,GS,gRKnd,G,ptr,GG,gU,C1,SL_,C,64,A,C,7,A,C,-8,AN,AS,ptr,G,ptr,GS,gRCnt,G,ptr,GG,gU,C1,SL_,C,64,A,C,2,SL_,AS,ptr,G,ptr,GS,gArP,G,ptr,C,64,A,CL,fnMem,C0,GS,gOpL,GG,gNSeg,S,ns,G,ns,C1,EQ,S,useP,GB1,ns,S,seg,BLP,G,seg,C0,LT,BF1,GA1,seg,S,n1,LA,gSgX,seg,S,x0,LA,gSgY,seg,S,y0,LA,gSgX,n1,S,x1,LA,gSgY,n1,S,y1,LA,gSgU,seg,S,uSub,G,x0,G,y0,G,x1,G,y1,G,uSub,G,useP,CL,fnMyr,DEC,seg,B0E,];});
def(fnCh,[],[],(loc,L)=>{
const [opLen,ptr,idx,kind,cnt,o,p,del,ins]=L(9);
const [nc,last,nh,i,prev,tmp]=L(6);
return [GG,gOpL,S,opLen,GG,gOutB,S,ptr,G,ptr,GS,gChO,G,ptr,G,opLen,C,4,A,C,2,SL_,AS,ptr,G,ptr,GS,gChP,G,ptr,G,opLen,C,4,A,C,2,SL_,AS,ptr,G,ptr,GS,gChD,G,ptr,G,opLen,C,4,A,C,2,SL_,AS,ptr,G,ptr,GS,gChI,G,ptr,G,opLen,C,4,A,C,2,SL_,AS,ptr,G,ptr,GS,gHSt,G,ptr,G,opLen,C,4,A,C,2,SL_,AS,ptr,G,ptr,GS,gHEn,G,ptr,G,opLen,C,4,A,C,2,SL_,AS,ptr,G,ptr,GS,gArP,G,ptr,C,64,A,CL,fnMem,GG,gPfx,T,o,S,p,ZS,del,ZS,ins,ZS,nc,GB1,opLen,S,idx,BLP,G,idx,C0,LT,BF1,
L8G,gRKnd,idx,S,kind,LA,gRCnt,idx,S,cnt,G,kind,C,KP,EQI,G,o,G,cnt,AS,o,G,p,G,cnt,AS,p,EL,GB1,nc,S,last,G,last,C0,LT,IF,I32,C1,EL,LA,gChO,last,LA,gChD,last,A,G,o,NE,LA,gChP,last,LA,gChI,last,A,G,p,NE,OR,E,UV,SA,gChO,nc,o,SA,gChP,nc,p,SAC,gChD,nc,0,SAC,gChI,nc,0,G,nc,S,last,INC,nc,E,G,kind,C,DL,EQI,LA,gChD,last,G,cnt,AS,tmp,SA,gChD,last,tmp,G,o,G,cnt,AS,o,G,del,G,cnt,AS,del,EL,LA,gChI,last,G,cnt,AS,tmp,SA,gChI,last,tmp,G,p,G,cnt,AS,p,G,ins,G,cnt,AS,ins,EE,
DEC,idx,B0E,G,nc,GS,gNCh,G,del,GS,gDel,G,ins,GS,gIns,ZS,nh,ZS,i,BLP,G,i,G,nc,GE,BF1,G,nh,C0,GT,UV,GB1,nh,S,tmp,LA,gHEn,tmp,S,prev,LA,gChO,i,LA,gChO,prev,LA,gChD,prev,A,B,C,6,LE,UV,SA,gHEn,tmp,i,INC,i,BR,2,EE,SA,gHSt,nh,i,SA,gHEn,nh,i,INC,nh,INC,i,B0E,G,nh,GS,gNHnk,];});
def(fnDec,[I32,I32],[I32],(loc,L)=>{
const ptr=0,val=1,start=loc(),lo=loc(),hi=loc(),t=loc();
return [G,val,EZ,UV,G,ptr,C,48,S8Z,GA1,ptr,RE,G,ptr,S,start,BLP,G,val,EZ,BF1,G,ptr,G,val,C,10,RMU,C,48,A,S8Z,INC,ptr,G,val,C,10,DVU,S,val,B0E,G,start,S,lo,GB1,ptr,S,hi,BLP,G,lo,G,hi,GEU,BF1,G,lo,L8Z,S,t,G,lo,G,hi,L8Z,S8Z,G,hi,G,t,S8Z,INC,lo,DEC,hi,B0E,G,ptr,];});
def(fnPLn,[I32,I32,I32,I32,I32],[I32],(loc,L)=>{
const ptr=0,src=1,s=2,e=3,opB=4,len=loc();
return [G,ptr,G,opB,S8Z,INC,ptr,G,e,G,s,BS,len,G,ptr,G,src,G,s,A,G,len,MCP,G,ptr,G,len,AS,ptr,GG,gRaw,UV,G,len,C,2,GEU,IF,I32,G,src,G,e,A,C,2,B,L8Z,C,92,EQ,G,src,G,e,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,E,EZ,UV,
G, ptr, C, HDR_MAP['\\n%\\n'][0], C, 5, MNT, G, ptr, C, 5, A, S, ptr,E,EL,G,len,EZ,IF,I32,C1,EL,G,src,G,e,A,C1,B,L8Z,C,10,NE,E,UV,G,ptr,C,10,S8Z,G,ptr,C,37,S8,1,G,ptr,C,10,S8,2,G,ptr,C,3,AS,ptr,EE,G,ptr,];});
def(fnPat,[],[],(loc,L)=>{
const [outB,ptr,totO,totN,prefix,suffix,n,m,nh]=L(9);
const [oBase,nBase,oStart,oEnd,oLen,preN,sufN,preA,sufA]=L(9);
const [curPos,i,hi,fi,li,firstO,firstP,lastO,lastP,lastD,lastI]=L(11);
const [oSt,nSt,remA,after,oEn,nEn]=L(6);
const [at,ci,co,cp,cd,cins,mi,maxB,oB,nB,bp]=L(11);
const [ps,pe,poff,raw]=L(4);
const q=[
GG,gPfx,S,prefix,GG,gSfx,S,suffix,GG,gN,S,n,GG,gM,S,m,GG,gNHnk,S,nh,GG,gRaw,S,raw,G,prefix,G,n,A,G,suffix,AS,totO,G,prefix,G,m,A,G,suffix,AS,totN,GG,gOB,S,oBase,GG,gNB,S,nBase,GG,gOSt,S,oStart,GG,gOEn,S,oEnd,GG,gOL,S,oLen,GG,gOBnd,S,oB,GG,gNBnd,S,nB,GG,gArP,S,ptr,G,ptr,S,preA,G,ptr,C,16,AS,ptr,G,ptr,S,sufA,G,ptr,C,16,AS,ptr,G,ptr,C,16,A,T,outB,GS,gOutB,G,oLen,GG,gNL,A,G,totO,G,totN,A,SH2,G,nh,C,6,SL_,A,C,512,AS,maxB,G,outB,G,maxB,A,CL,fnMem,G,outB,S,ptr,
G,raw,UV,G,ptr,C,34,S8Z,INC,ptr,E,];
const emitHdr=(key)=>{
const [off, len] = HDR_MAP[key];
q.push(G,ptr,C,off,C,len,MNT,G,ptr,C,len,A,S,ptr);};
const emitNewlineOut=()=>{
q.push(G,raw,UV,G,ptr,C,92,S8Z,G,ptr,C,110,S8,1,G,ptr,C,2,AS,ptr,EL,G,ptr,C,10,S8Z,INC,ptr,E,);};
const emitPushOld=(opByte)=>{
q.push(G,at,G,prefix,GE,G,at,G,prefix,G,n,A,LT,AN,UV,G,at,G,prefix,BS,poff,G,oB,G,poff,SH2,T,bp,L3Z,S,ps,G,bp,L32,4,S,pe,EL,G,at,G,prefix,LT,UV,G,at,G,prefix,G,preN,B,BS,poff,G,preA,G,poff,SH2,T,poff,L3Z,S,ps,G,poff,L32,4,S,pe,EL,G,at,G,prefix,G,n,A,BS,poff,G,sufA,G,poff,SH2,T,poff,L3Z,S,ps,G,poff,L32,4,S,pe,EE,G,ptr,G,oBase,G,ps,G,pe,C,opByte,CL,fnPLn,S,ptr,);};emitHdr('makefun-diff/1 old='); q.push(G,ptr,G,totO,CL,fnDec,S,ptr);
emitHdr(' new='); q.push(G,ptr,G,totN,CL,fnDec,S,ptr);emitHdr(' hunks='); q.push(G,ptr,G,nh,CL,fnDec,S,ptr);emitHdr(' deleted='); q.push(G,ptr,GG,gDel,CL,fnDec,S,ptr);emitHdr(' inserted='); q.push(G,ptr,GG,gIns,CL,fnDec,S,ptr);emitNewlineOut();q.push(G,nh,EZ,UV,G,raw,UV,G,ptr,C,34,S8Z,INC,ptr,E,G,ptr,GS,gOutE,RE,ZS,preN,GG,gChO,L3Z,G,prefix,C,3,A,LT,G,prefix,C0,GT,AN,UV,G,prefix,C,3,G,prefix,C,3,LT,SL,S,preN,G,oStart,S,curPos,G,preA,G,preN,SH2,G,curPos,S3Z,
GB1,preN,S,i,BLP,G,i,C0,LT,BF1,G,raw,UV,G,curPos,G,curPos,C,2,GEU,IF,I32,G,oBase,G,curPos,A,C,2,B,L8Z,C,92,EQ,G,oBase,G,curPos,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,E,IF,I32,C,2,EL,C1,E,BS,curPos,BLP,G,curPos,C0,LE,BF1,G,curPos,C,2,GEU,IF,I32,G,oBase,G,curPos,A,C,2,B,L8Z,C,92,EQ,G,oBase,G,curPos,A,C1,B,L8Z,C,110,EQ,AN,EL,C0,E,BF1,DEC,curPos,B0E,G,curPos,C0,LT,UV,ZS,curPos,E,EL,
G,curPos,G,oBase,G,curPos,A,C1,B,L8Z,C,10,EQ,IF,I32,C,2,EL,C1,E,BS,curPos,BLP,G,curPos,C0,LT,BF1,G,oBase,G,curPos,A,L8Z,C,10,EQ,BF1,DEC,curPos,B0E,INC,curPos,E,G,preA,G,i,SH2,G,curPos,S3Z,DEC,i,B0E,E,ZS,sufN,G,suffix,C0,GT,UV,GG,gHEn,GB1,nh,SH2,L3Z,S,li,LA,gChO,li,LA,gChD,li,A,C,3,A,G,prefix,G,n,A,GT,UV,G,suffix,C,3,G,suffix,C,3,LT,SL,S,sufN,G,oEnd,S,curPos,G,sufA,G,curPos,S3Z,OS,i,BLP,
G,i,G,sufN,GT,BF1,G,raw,UV,BLP,G,curPos,G,oLen,GEU,BF1,G,oBase,G,curPos,A,L8Z,C,92,EQ,GA1,curPos,G,oLen,LU,AN,UV,G,oBase,G,curPos,A,C1,A,L8Z,C,110,EQI,G,curPos,C,2,AS,curPos,BR,3,EE,INC,curPos,B0E,EL,BLP,G,curPos,G,oLen,GEU,BF1,G,oBase,G,curPos,A,L8Z,C,10,EQI,INC,curPos,BR,2,E,INC,curPos,B0E,E,G,sufA,G,i,SH2,G,curPos,S3Z,INC,i,B0E,EE,ZS,hi,BLP,G,hi,G,nh,GE,BF1,
LA,gHSt,hi,S,fi,LA,gHEn,hi,S,li,LA,gChO,fi,S,firstO,LA,gChP,fi,S,firstP,LA,gChO,li,S,lastO,LA,gChP,li,S,lastP,LA,gChD,li,S,lastD,LA,gChI,li,S,lastI,G,firstO,C,3,GT,IF,I32,G,firstO,C,3,B,EL,C0,E,S,oSt,G,firstP,G,firstO,G,oSt,B,BS,nSt,G,totO,G,lastO,G,lastD,A,BS,remA,G,remA,C,3,G,remA,C,3,LT,SL,S,after,G,lastO,G,lastD,A,G,after,AS,oEn,G,lastP,G,lastI,A,G,after,AS,nEn,);emitHdr('@ ');q.push(G,ptr,GA1,oSt,CL,fnDec,S,ptr,G,ptr,C,32,S8Z,INC,ptr,G,ptr,G,oEn,G,oSt,B,CL,fnDec,S,ptr,
G,ptr,C,32,S8Z,INC,ptr,G,ptr,GA1,nSt,CL,fnDec,S,ptr,G,ptr,C,32,S8Z,INC,ptr,G,ptr,G,nEn,G,nSt,B,CL,fnDec,S,ptr,);emitNewlineOut();q.push(G,oSt,S,at,G,fi,S,ci,BLP,G,ci,G,li,GT,BF1,LA,gChO,ci,S,co,LA,gChP,ci,S,cp,LA,gChD,ci,S,cd,LA,gChI,ci,S,cins,BLP,G,at,G,co,GE,BF1,);emitPushOld(61);q.push(G,at,C1,AS,at,B0E,ZS,i,BLP,G,i,G,cd,GE,BF1,G,co,G,i,A,S,at);emitPushOld(45);q.push(G,i,C1,AS,i,B0E,ZS,i,BLP,G,i,G,cins,GE,BF1,
G,cp,G,i,A,G,prefix,BS,mi,G,ptr,G,nBase,G,nB,G,mi,SH2,T,bp,L3Z,G,bp,L32,4,C,43,CL,fnPLn,S,ptr,INC,i,B0E,G,co,G,cd,AS,at,INC,ci,B0E,BLP,G,at,G,oEn,GE,BF1,);emitPushOld(61);q.push(G,at,C1,AS,at,B0E,INC,hi,B0E,G,raw,UV,G,ptr,C,34,S8Z,INC,ptr,E,G,ptr,GS,gOutE,);
return q;});
def(fnAsc,[],[I32],()=>[CL,fnTrim,GG,gOSt,GG,gOEn,EQ,GG,gNSt,GG,gNEn,EQ,AN,UV,C0,GS,gN,C0,GS,gM,C0,GS,gNHnk,C0,GS,gDel,C0,GS,gIns,GG,gArB,GS,gArP,CL,fnPat,GG,gOutE,GG,gOutB,B,RE,CL,fnScan,GG,gN,EZ,GG,gM,EZ,OR,UV,GG,gChO,GG,gPfx,S3Z,GG,gChP,GG,gPfx,S3Z,GG,gChD,GG,gN,S3Z,GG,gChI,GG,gM,S3Z,GG,gHSt,C0,S3Z,GG,gHEn,C0,S3Z,C1,GS,gNCh,C1,GS,gNHnk,GG,gN,GS,gDel,GG,gM,GS,gIns,CL,fnPat,GG,gOutE,GG,gOutB,B,RE,CL,fnBnd,DR,CL,fnSMyr,CL,fnCh,CL,fnPat,GG,gOutE,GG,gOutB,B,]);
def(fnGOut,[],[I32],()=>[GG,gOutB]);
def(fnWs,[I32,I32],[I32],(loc,L)=>{
const pos=0,end=1,b=loc();
return [BLP,G,pos,G,end,GEU,BF1,G,pos,L8Z,T,b,C,32,EQ,G,b,C,9,EQ,OR,G,b,C,10,EQ,OR,G,b,C,13,EQ,OR,EZ,BF1,INC,pos,B0E,G,pos,];});
def(fnSkS,[I32,I32],[I32],(loc,L)=>{
const pos=0,end=1,b=loc();
return [G,pos,G,end,GEU,UV,CM2,RE,G,pos,L8Z,C,34,NE,RM1,INC,pos,BLP,G,pos,G,end,GEU,UV,CM2,RE,G,pos,L8Z,S,b,G,b,C,34,EQI,GA1,pos,RE,G,b,C,92,EQI,GA1,pos,G,end,GEU,UV,CM2,RE,G,pos,C,2,AS,pos,BR,1,E,G,b,C,32,LU,RM1,G,b,C,127,GU,UV,C,2,GS,gSFlg,E,INC,pos,B0E,CM2,];});
def(fnScR,[I32,I32],[I32],(loc,L)=>{
const pos=0,end=1,end16=loc(),mask=loc(),k=loc(),b=loc(),esc=loc();
const [q16,bs16,sp16,v]=L(4,V128);
return [G,pos,G,end,GEU,UV,CM2,RE,G,pos,L8Z,C,34,NE,RM1,C0,GS,gSFlg,INC,pos,G,end,C,16,BS,end16,C,34,VS8,S,q16,C,92,VS8,S,bs16,C,32,VS8,S,sp16,BLP,G,pos,G,end16,GT,BF1,G,pos,VLD,0,T,v,G,v,G,q16,VE8,G,v,G,bs16,VE8,VOR,G,v,G,sp16,VL8,VOR,VBM,T,mask,EZ,UV,G,pos,C,16,AS,pos,BR,1,E,G,pos,G,mask,CTZ,AS,pos,G,pos,L8Z,S,b,G,b,C,34,EQI,GA1,pos,RE,G,b,C,92,EQI,GA1,pos,G,end,GEU,UV,CM2,RE,GA1,pos,L8Z,S,esc,
G,esc,C,110,EQ,G,esc,C,114,EQ,OR,UV,G,pos,C,2,AS,pos,BR,2,E,C1,GS,gSFlg,G,pos,C,2,AS,pos,BR,1,E,G,b,C,127,GU,UV,C,2,GS,gSFlg,INC,pos,BR,1,E,CM1,RT,EE,BLP,G,pos,G,end,GEU,UV,CM2,RE,G,pos,L8Z,S,b,G,b,C,34,EQI,GA1,pos,RE,G,b,C,92,EQI,GA1,pos,G,end,GEU,UV,CM2,RE,GA1,pos,L8Z,S,esc,G,esc,C,110,EQ,G,esc,C,114,EQ,OR,EZ,UV,GG,gSFlg,EZ,UV,C1,GS,gSFlg,EE,G,pos,C,2,AS,pos,BR,1,E,G,b,C,127,GU,UV,C,2,GS,gSFlg,INC,pos,BR,1,E,
G,b,C,32,LU,RM1,INC,pos,B0E,CM2,];});
def(fnUn,[I32,I32,I32],[I32],(loc,L)=>{
const src=0,end=1,dstB=2;
const [dst,end16,mask,k,b,esc,h1,h2]=L(8);
const [q16,bs16,sp16,v]=L(4,V128);
const q=[
G,src,G,end,GEU,RM1,G,src,L8Z,C,34,NE,RM1,INC,src,G,dstB,S,dst,G,end,C,16,BS,end16,C,34,VS8,S,q16,C,92,VS8,S,bs16,C,32,VS8,S,sp16,];
const pushHex=(chL,outL)=>{
q.push(G,chL,C,48,B,T,outL,C,9,LEU,UV,EL,G,chL,C,32,OR,C,87,B,T,outL,C,10,LU,G,outL,C,15,GU,OR,UV,CM1,RT,EE,);};
const pushHandleEsc=()=>{
q.push(G,src,C1,A,G,end,GEU,RM1,GA1,src,L8Z,S,esc,G,esc,C,110,EQI,G,dst,C,10,S8Z,G,src,C,2,AS,src,INC,dst,EL,G,esc,C,114,EQI,G,dst,C,13,S8Z,G,src,C,2,AS,src,INC,dst,EL,G,esc,C,34,EQI,G,dst,C,34,S8Z,G,src,C,2,AS,src,INC,dst,EL,G,esc,C,92,EQI,G,dst,C,92,S8Z,G,src,C,2,AS,src,INC,dst,EL,G,esc,C,116,EQI,G,dst,C,9,S8Z,G,src,C,2,AS,src,INC,dst,
EL,G,esc,C,98,EQI,G,dst,C,8,S8Z,G,src,C,2,AS,src,INC,dst,EL,G,esc,C,102,EQI,G,dst,C,12,S8Z,G,src,C,2,AS,src,INC,dst,EL,G,esc,C,47,EQI,G,dst,C,47,S8Z,G,src,C,2,AS,src,INC,dst,EL,G,esc,C,117,EQI,G,src,C,5,A,G,end,GEU,RM1,G,src,L8,2,C,48,NE,G,src,L8,3,C,48,NE,OR,RM1,G,src,L8,4,S,b,);pushHex(b,h1);q.push(G,h1,C,7,GU,RM1,G,src,L8,5,S,b);pushHex(b,h2);q.push(G,dst,G,h1,C,4,SL_,G,h2,OR,S8Z,
G,src,C,6,AS,src,INC,dst,EL,CM1,RT,EE,EE,EE,EE,E,);};q.push(BK,V,LP,V,G,src,G,end16,GT,BF1,G,src,VLD,0,T,v,G,v,G,q16,VE8,G,v,G,bs16,VE8,VOR,G,v,G,sp16,VL8,VOR,VBM,T,mask,EZ,UV,G,dst,G,v,VST,0,G,src,C,16,AS,src,G,dst,C,16,AS,dst,BR,1,E,G,mask,CTZ,T,k,UV,G,dst,G,v,VST,0,G,src,G,k,AS,src,G,dst,G,k,AS,dst,E,G,src,L8Z,S,b,G,b,C,34,EQI,GA1,src,GS,gJCur,G,dst,G,dstB,B,RE,G,b,C,92,NE,RM1,);pushHandleEsc();q.push(BR,0,EE,BLP,
G,src,G,end,GEU,RM1,G,src,L8Z,S,b,G,b,C,34,EQI,GA1,src,GS,gJCur,G,dst,G,dstB,B,RE,G,b,C,92,EQI,);pushHandleEsc();q.push(BR,1,E,G,b,C,32,LU,G,b,C,127,GU,OR,RM1,G,dst,G,b,S8Z,INC,src,INC,dst,B0E,CM1,);
return q;});
def(fnEsc,[I32,I32,I32],[I32],(loc,L)=>{
const src=0,len=1,dst=2,end=loc(),end16=loc(),mask=loc(),k=loc(),b=loc(),h1=loc(),h2=loc();
const [q16,bs16,sp16,v]=L(4,V128);
const q=[
G,dst,C,34,S8Z,INC,dst,G,src,G,len,A,T,end,C,16,BS,end16,C,34,VS8,S,q16,C,92,VS8,S,bs16,C,32,VS8,S,sp16,];
const pushEsc=()=>{
q.push(G,b,C,10,EQI,G,dst,C,92,S8Z,G,dst,C,110,S8,1,G,dst,C,2,AS,dst,EL,G,b,C,34,EQI,G,dst,C,92,S8Z,G,dst,C,34,S8,1,G,dst,C,2,AS,dst,EL,G,b,C,92,EQI,G,dst,C,92,S8Z,G,dst,C,92,S8,1,G,dst,C,2,AS,dst,EL,G,b,C,13,EQI,G,dst,C,92,S8Z,G,dst,C,114,S8,1,G,dst,C,2,AS,dst,EL,G,b,C,9,EQI,G,dst,C,92,S8Z,G,dst,C,116,S8,1,G,dst,C,2,AS,dst,EL,G,b,C,8,EQI,G,dst,C,92,S8Z,G,dst,C,98,S8,1,G,dst,C,2,AS,dst,EL,G,b,C,12,EQI,G,dst,C,92,S8Z,G,dst,C,102,S8,1,G,dst,C,2,AS,dst,EL,
G,dst,C,92,S8Z,G,dst,C,117,S8,1,G,dst,C,48,S8,2,G,dst,C,48,S8,3,G,b,C,4,SR,C,48,AS,h1,G,b,C,15,AN,T,h2,C,10,LU,IF,I32,G,h2,C,48,A,EL,G,h2,C,87,A,E,S,h2,G,dst,G,h1,S8,4,G,dst,G,h2,S8,5,G,dst,C,6,AS,dst,EE,EE,EE,E,);};q.push(BK,V,LP,V,G,src,G,end16,GT,BF1,G,src,VLD,0,T,v,G,v,G,q16,VE8,G,v,G,bs16,VE8,VOR,G,v,G,sp16,VL8,VOR,VBM,T,mask,EZ,UV,G,dst,G,v,VST,0,G,src,C,16,AS,src,G,dst,C,16,AS,dst,BR,1,E,G,mask,CTZ,T,k,UV,G,dst,G,v,VST,0,G,src,G,k,AS,src,G,dst,G,k,AS,dst,E,
G,src,L8Z,S,b,INC,src,);pushEsc();q.push(BR,0,EE,BLP,G,src,G,end,GEU,BF1,G,src,L8Z,S,b,INC,src,G,b,C,34,EQ,G,b,C,92,EQ,OR,G,b,C,32,LU,OR,UV,);pushEsc();q.push(EL,G,dst,G,b,S8Z,INC,dst,E,B0E,G,dst,C,34,S8Z,GA1,dst,);
return q;});
def(fnExp,[I32,I32,I32],[I32],()=>[G,0,G,1,GEU,UV,CM2,RE,G,0,L8Z,G,2,NE,RM1,G,0,C1,A,G,1,CL,fnWs,]);
def(fnEWin,[I32],[],()=>[G,0,C,256,A,CL,fnMem]);
def(fnSIn,[I32,I32,I32,I32],[],()=>[G,0,GS,gWB,G,0,GS,gWPos,G,0,GS,gWKp,G,1,GS,gWEn,G,2,GS,gWEof,G,3,GS,gWCap,C0,GS,gSSt,C0,GS,gCIdx,]);
def(fnSRf,[I32,I32,I32],[],()=>[GG,gWB,GS,gWPos,GG,gWB,GS,gWKp,G,0,GS,gWEn,G,1,GS,gWEof,G,2,GS,gWCap,]);
def(fnGKp,[],[I32],()=>[GG,gWKp]);
def(fnGCSt,[],[I32],()=>[GG,gCSt]);
def(fnGCEn,[],[I32],()=>[GG,gCEn]);
def(fnGSOut,[],[I32],()=>[GG,gSOut]);
def(fnGIdx,[],[I32],()=>[GG,gCIdx]);
def(fnSNx,[],[I32],(loc,L)=>{
const [pos,end,keep,st,snIn]=L(5);
const [oRawS,oRawE,nRawS,nRawE,anyEsc,anyUtf]=L(6);
const [isOld,b,ab,dst,oLen,nLen,outL,outB,tmp,escE]=L(10);
const q=[
GG,gWPos,S,pos,GG,gWEn,S,end,GG,gSSt,S,st,G,pos,S,keep,];
const retNeed=()=>q.push(G,keep,GS,gWKp,GG,gWEof,IF,I32,CM1,EL,CM2,E,RT);
const expect=(ch)=>{
q.push(G,pos,G,end,C,ch,CL,fnExp,T,pos,CM2,EQ,IF,V);retNeed();q.push(E,G,pos,CM1,EQI,CM1,RT,E);};
const checkPos=()=>{
q.push(G,pos,G,end,GEU,IF,V); retNeed(); q.push(E);};
const skipStr=()=>{
q.push(G,pos,G,end,CL,fnSkS,S,pos,G,pos,CM2,EQ,IF,V); retNeed(); q.push(E,G,pos,CM1,EQI,CM1,RT,E);};q.push(G,st,EZ,UV,G,pos,G,end,CL,fnWs,S,pos,G,pos,S,keep,);expect(91);q.push(checkPos(),G,pos,L8Z,C,93,EQI,GA1,pos,G,end,CL,fnWs,S,pos,G,pos,G,end,LU,RM1,GG,gWEof,EZ,UV,G,keep,GS,gWKp,CM2,RE,C,3,GS,gSSt,C0,RE,OS,st,C1,GS,gSSt,EL,G,st,C,2,EQI,G,pos,G,end,CL,fnWs,S,pos,G,pos,S,keep,);q.push(G,pos,G,end,GEU,IF,V); retNeed(); q.push(E);q.push(
G,pos,L8Z,C,93,EQI,GA1,pos,G,end,CL,fnWs,S,pos,G,pos,G,end,LU,RM1,GG,gWEof,EZ,UV,G,keep,GS,gWKp,CM2,RE,C,3,GS,gSSt,C0,RE,G,pos,L8Z,C,44,NE,RM1,GA1,pos,G,end,CL,fnWs,S,pos,G,pos,S,keep,OS,st,C1,GS,gSSt,EL,G,st,C,3,EQI,C0,RT,EE,E,G,pos,S,keep,);expect(123);q.push(C,0,S,snIn,CM1,S,oRawS,CM1,S,nRawS,ZS,anyEsc,ZS,anyUtf,BLP,G,pos,G,end,GEU,UV,);retNeed();q.push(E,G,pos,L8Z,C,125,EQ,BF1,G,pos,C,7,A,G,end,LEU,IF,I32,
G,pos,L32U,0,C,0x706e6922,EQ,G,pos,L32U,3,C,0x22747570,EQ,AN,EL,C0,E,UV,G,snIn,RM1,OS,snIn,G,pos,C,7,A,G,end,CL,fnWs,S,pos,);expect(58); expect(123);q.push(BK,V,LP,V,G,pos,G,end,GEU,UV,);retNeed();q.push(E,G,pos,L8Z,C,125,EQ,BF1,G,pos,C,5,A,G,end,GU,UV,);retNeed();q.push(E,G,pos,L8,4,C,34,NE,RM1,G,pos,L32U,0,C,0x646c6f22,EQI,OS,isOld,EL,G,pos,L32U,0,C,0x77656e22,EQI,ZS,isOld,EL,CM1,RT,EE,G,isOld,UV,G,oRawS,C0,GE,RM1,
EL,G,nRawS,C0,GE,UV,CM1,RT,EE,G,pos,C,5,A,G,end,CL,fnWs,S,pos,);expect(58);q.push(G,isOld,UV,G,pos,S,oRawS,EL,G,pos,S,nRawS,E,G,pos,G,end,CL,fnScR,S,pos,G,pos,CM2,EQI,);retNeed();q.push(E,G,pos,CM1,EQI,CM1,RE,G,isOld,UV,G,pos,S,oRawE,EL,G,pos,S,nRawE,E,GG,gSFlg,C1,EQI,OS,anyEsc,EL,GG,gSFlg,C,2,EQI,OS,anyUtf,EE,G,pos,G,end,CL,fnWs,S,pos,G,pos,G,end,GEU,UV,);retNeed();q.push(E,G,pos,L8Z,C,44,EQI,GA1,pos,G,end,CL,fnWs,S,pos,BR,1,E,BR,1,EE,);
expect(125);q.push(EL,C0,GS,gSFlg,);skipStr();q.push(GG,gSFlg,C,2,EQI,OS,anyUtf,E,G,pos,G,end,CL,fnWs,S,pos,);expect(58);q.push(G,pos,G,end,GEU,UV,);retNeed();q.push(E,G,pos,L8Z,C,34,EQI,C0,GS,gSFlg,);skipStr();q.push(GG,gSFlg,C,2,EQI,OS,anyUtf,E,EL,G,pos,L8Z,C,45,EQI,INC,pos,E,G,pos,G,end,GEU,UV,);retNeed();q.push(E,G,pos,L8Z,T,b,C,48,LU,G,b,C,57,GU,OR,RM1,BLP,G,pos,G,end,GEU,UV,);retNeed();q.push(E,
G,pos,L8Z,T,b,C,48,LU,G,b,C,57,GU,OR,BF1,INC,pos,B0E,E,G,pos,G,end,CL,fnWs,S,pos,E,G,pos,G,end,GEU,UV,);retNeed();q.push(E,G,pos,L8Z,C,44,EQI,GA1,pos,G,end,CL,fnWs,S,pos,BR,1,E,BR,1,EE,);expect(125);q.push(G,snIn,EZ,G,oRawS,C0,LT,OR,G,nRawS,C0,LT,OR,RM1,G,anyUtf,UV,G,keep,GS,gCSt,G,pos,GS,gCEn,G,pos,GS,gWPos,C,2,GS,gSSt,GG,gCIdx,C1,A,GS,gCIdx,C,-3,RE,G,anyEsc,EZ,UV,C1,GS,gRaw,GA1,oRawS,GS,gOB,G,oRawE,G,oRawS,B,C,2,B,GS,gOL,
GA1,nRawS,GS,gNB,G,nRawE,G,nRawS,B,C,2,B,GS,gNL,GG,gWCap,GS,gArB,CL,fnAsc,S,outL,GG,gOutB,C1,B,T,tmp,GS,gSOut,G,tmp,GG,gCIdx,EZ,IF,I32,C,91,EL,C,44,E,S8Z,G,pos,GS,gWPos,C,2,GS,gSSt,GG,gCIdx,C1,A,GS,gCIdx,GA1,outL,RE,GG,gWCap,S,ab,G,ab,G,oRawE,G,oRawS,B,A,C,64,A,CL,fnMem,G,oRawS,G,oRawE,G,ab,CL,fnUn,T,oLen,C0,LT,UV,G,keep,GS,gCSt,G,pos,GS,gCEn,G,pos,GS,gWPos,C,2,GS,gSSt,GG,gCIdx,C1,A,GS,gCIdx,C,-3,RE,G,ab,G,oLen,A,C,31,A,C,-16,AN,S,dst,G,dst,G,nRawE,G,nRawS,B,A,C,64,A,CL,fnMem,
G,nRawS,G,nRawE,G,dst,CL,fnUn,T,nLen,C0,LT,UV,G,keep,GS,gCSt,G,pos,GS,gCEn,G,pos,GS,gWPos,C,2,GS,gSSt,GG,gCIdx,C1,A,GS,gCIdx,C,-3,RE,C0,GS,gRaw,G,ab,GS,gOB,G,oLen,GS,gOL,G,dst,GS,gNB,G,nLen,GS,gNL,G,dst,G,nLen,A,C,31,A,C,-16,AN,GS,gArB,CL,fnAsc,S,outL,GG,gOutB,S,outB,GG,gOutE,C,31,A,C,-16,AN,C,16,AS,tmp,G,tmp,G,outL,C,6,M,A,C,64,A,CL,fnMem,G,outB,G,outL,G,tmp,CL,fnEsc,S,escE,GB1,tmp,T,dst,GS,gSOut,G,dst,GG,gCIdx,EZ,IF,I32,C,91,EL,C,44,E,S8Z,G,pos,GS,gWPos,C,2,GS,gSSt,
GG,gCIdx,C1,A,GS,gCIdx,G,escE,G,dst,B,);
return q;});
const out=new Uint8Array(24576);
let p=0;
out[p++]=0x00; out[p++]=0x61; out[p++]=0x73; out[p++]=0x6d;out[p++]=0x01; out[p++]=0x00; out[p++]=0x00; out[p++]=0x00;
const beginSec=(id)=>{ out[p++]=id; const lp=p; p += 5; return lp; };
const endSec=(lp)=>{
let len=p - (lp + 5);
for (let i=0; i < 4; i++) { out[lp + i]=(len & 0x7f) | 0x80; len >>>= 7; }
out[lp + 4]=len & 0x7f;};
let lp=beginSec(1);
p = writeUleb(out, p, types.length);
for (let i=0; i < types.length; i++) {
const t=types[i];
out[p++] = 0x60; p = writeUleb(out, p, t.params.length);
for (let j=0; j < t.params.length; j++) out[p++]=t.params[j];
p = writeUleb(out, p, t.results.length);
for (let j=0; j < t.results.length; j++) out[p++]=t.results[j];
}endSec(lp);lp=beginSec(3);p = writeUleb(out, p, funcs.length);
for (let i = 0; i < funcs.length; i++) p = writeUleb(out, p, funcs[i].typeIdx);
endSec(lp);lp=beginSec(5);out[p++] = 0x01; out[p++] = 0x00; p = writeUleb(out, p, 90);endSec(lp);lp=beginSec(6);p = writeUleb(out, p, gc);
for (let i=0; i < gc; i++) { out[p++]=I32; out[p++]=0x01; out[p++]=C; out[p++]=0x00; out[p++]=E; }
endSec(lp);
const exports = [
['memory',0x02,0],['prepareInput',0x00,fnPrep],['solveAscii',0x00,fnAsc],['getOutBase',0x00,fnGOut],['ensureWin',0x00,fnEWin],['streamInit',0x00,fnSIn],['streamRefill',0x00,fnSRf],['streamNext',0x00,fnSNx],['getWinKeep',0x00,fnGKp],['getCaseStart',0x00,fnGCSt],['getCaseEnd',0x00,fnGCEn],['getStreamOutBase',0x00,fnGSOut],['getCaseIdx',0x00,fnGIdx],];lp=beginSec(7);p = writeUleb(out, p, exports.length);
for (let i=0; i < exports.length; i++) {
const [name,kind,idx]=exports[i];
p = writeUleb(out, p, name.length);
for (let j=0; j < name.length; j++) out[p++]=name.charCodeAt(j);
out[p++] = kind; p = writeUleb(out, p, idx);}endSec(lp);out[p++]=12; out[p++]=1; out[p++]=1;
const gCounts=new Int32Array(16),gTypes=new Uint8Array(16);
lp=beginSec(10);p = writeUleb(out, p, funcs.length);
for (let i=0; i < funcs.length; i++) {
const fn=funcs[i],locs=fn.locals,bodyStart=p + 5;
let bp=bodyStart,grpCount=0;
for (let j=0; j < locs.length; j++) {
const t=locs[j];
if (grpCount > 0 && gTypes[grpCount - 1] === t) gCounts[grpCount - 1]++;else { gCounts[grpCount]=1; gTypes[grpCount]=t; grpCount++; }}bp = writeUleb(out, bp, grpCount);
for (let j = 0; j < grpCount; j++) { bp = writeUleb(out, bp, gCounts[j]); out[bp++] = gTypes[j]; }
bp=encodeBody(fn.q,out,bp);
let len=bp - bodyStart;
for (let j=0; j < 4; j++) { out[p + j]=(len & 0x7f) | 0x80; len >>>= 7; }
out[p + 4]=len & 0x7f;p=bp;}endSec(lp);lp=beginSec(11);out[p++]=1; out[p++]=0x01;
p = writeUleb(out, p, HDR_STR.length);
for (let i = 0; i < HDR_STR.length; i++) out[p++] = HDR_STR.charCodeAt(i);
endSec(lp);
const mod=new WebAssembly.Module(out.subarray(0,p));
return new WebAssembly.Instance(mod).exports;}
