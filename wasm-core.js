// Compact symbolic WASM SIMD128 compiler: passive headers, SIMD128 predictive line matcher + 64-bit SWAR hash, sufDel/sufIns slab LB.
const I=0x7f,J=0x7e,W=0x7b,V=0x40;
const KP=0,DL=1,IN=2;
const UN=0x00,K=0x02,O=0x03,U=0x04,H=0x05,E=0x0b;
const R=0x0c,F=0x0d,X=0x0f,Y=0x10,D=0x1a,Z=0x1b;
const G=0x20,S=0x21,T=0x22,P=0x23,Q=0x24;
const L32=0x28,L64=0x29,L8=0x2d,S32=0x36,S64=0x37,S8=0x3a;
const MZ=0x3f,MG=0x40,C=0x41,C6=0x42;
const EZ=0x45,EQ=0x46,NE=0x47,LT=0x48,LU=0x49,GT=0x4a,GU=0x4b,LE=0x4c,LEU=0x4d,GE=0x4e,GEU=0x4f;
const I6Z=0x50,I6E=0x51,I6N=0x52;
const CZ=0x67,TZ=0x68,PP=0x69;
const A=0x6a,B=0x6b,M=0x6c,DV=0x6e,RM=0x70,AN=0x71,OR=0x72,XR=0x73,SL=0x74,SS=0x75,SR=0x76;
const I6T=0x7a,I6S=0x7d,I6M=0x7e,I6A=0x83,I6O=0x84,I6X=0x85,I6L=0x86,I6R=0x88;
const WR=0xa7,EX=0xad;
const U32=-1,VL=-2,VS=-3,VS8=-4,VE8=-5,VL8=-6,VBM=-7,VOR=-8;
const MCP=-9,MFL=-10,MNT=-11;
const LA=-12,L6G=-13,L8G=-14,SA=-15,SC=-16,S8G=-17,S8C=-18,LD=-19,ST=-20,SK=-21,BL=-22,EE=-23,IC=-24,DC=-25,GA1=-26,GB1=-27,UV=-28,BF1=-29,R0=-30,C0=-31,C1=-32,CM1=-33,CM2=-34,SH2=-35;
const HDR_STR = 'makefun-diff/1 old= new= hunks= deleted= inserted=@ ';
const HDR_MAP = { 'makefun-diff/1 old=': [0, 19], ' new=': [19, 5], ' hunks=': [24, 7], ' deleted=': [31, 9], ' inserted=': [40, 10], '@ ': [50, 2] };
function writeUleb(b,p,v) {v >>>= 0;while (v >= 0x80) { b[p++]=(v & 0x7f) | 0x80; v >>>= 7; }b[p++]=v;
return p;}
function writeSleb32(b,p,v) {v |= 0;
for (;;) {
const x=v & 0x7f; v >>= 7;
if ((v === 0 && (x & 0x40) === 0) || (v === -1 && (x & 0x40) !== 0)) { b[p++]=x; return p; }b[p++]=x | 0x80;}}
function writeSleb64LH(b,p,lo,hi) {lo >>>= 0; hi |= 0;
for (;;) {
const x=lo & 0x7f;
lo=((lo >>> 7) | (hi << 25)) >>> 0;hi >>= 7;
if ((hi === 0 && lo === 0 && (x & 0x40) === 0) || (hi === -1 && lo === 0xffffffff && (x & 0x40) !== 0)) { b[p++]=x; return p; }b[p++]=x | 0x80;}}
function encodeBody(ops,out,p) {
let op,v,g,idx,val;
for (let i=0; i < ops.length; ) {
op=ops[i++];
if (op >= 0x45) {out[p++]=op;
} else if (op >= 0) {out[p++]=op;
switch (op) {
case C: v=ops[i++]; if (v >= -64 && v < 64) out[p++]=v & 0x7f; else p=writeSleb32(out,p,v); break;
case C6: p=writeSleb64LH(out,p,ops[i++],ops[i++]); break;
case G: case S: case T: case P: case Q: case Y: case R: case F:
v=ops[i++]; if (v < 128) out[p++]=v; else p=writeUleb(out,p,v); break;
case L32: case S32: out[p++]=2; v=ops[i++]; if (v < 128) out[p++]=v; else p=writeUleb(out,p,v); break;
case L64: case L8: case S64: case S8: out[p++]=0; v=ops[i++]; if (v < 128) out[p++]=v; else p=writeUleb(out,p,v); break;
case K: case O: case U: out[p++]=ops[i++]; break;
case MZ: case MG: out[p++]=0; break;}} else {
switch (op) {
case U32: out[p++]=L32; out[p++]=0; v=ops[i++]; if (v < 128) out[p++]=v; else p=writeUleb(out,p,v); break;
case VL: out[p++]=0xfd; out[p++]=0x00; out[p++]=0; v=ops[i++]; if (v < 128) out[p++]=v; else p=writeUleb(out,p,v); break;
case VS: out[p++]=0xfd; out[p++]=0x0b; out[p++]=0; v=ops[i++]; if (v < 128) out[p++]=v; else p=writeUleb(out,p,v); break;
case VS8: out[p++]=0xfd; out[p++]=0x0f; break;
case VE8: out[p++]=0xfd; out[p++]=0x23; break;
case VL8: out[p++]=0xfd; out[p++]=0x25; break;
case VBM: out[p++]=0xfd; out[p++]=0x64; break;
case VOR: out[p++]=0xfd; out[p++]=0x50; break;
case MCP: out[p++]=0xfc; out[p++]=0x0a; out[p++]=0; out[p++]=0; break;
case MFL: out[p++]=0xfc; out[p++]=0x0b; out[p++]=0; break;
case MNT: out[p++]=0xfc; out[p++]=0x08; out[p++]=0; out[p++]=0; break;
case LA:g=ops[i++]; idx=ops[i++];out[p++]=P; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL; out[p++]=A; out[p++]=L32; out[p++]=2; out[p++]=0; break;
case L6G:g=ops[i++]; idx=ops[i++];out[p++]=P; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=3; out[p++]=SL; out[p++]=A; out[p++]=L64; out[p++]=0; out[p++]=0; break;
case L8G:g=ops[i++]; idx=ops[i++];out[p++]=P; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=A; out[p++]=L8; out[p++]=0; out[p++]=0; break;
case SA:g=ops[i++]; idx=ops[i++]; val=ops[i++];out[p++]=P; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL; out[p++]=A;out[p++]=G; out[p++]=val; out[p++]=S32; out[p++]=2; out[p++]=0; break;
case SC:g=ops[i++]; idx=ops[i++]; val=ops[i++];out[p++]=P; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL; out[p++]=A;
out[p++]=C; if (val >= -64 && val < 64) out[p++]=val & 0x7f; else p=writeSleb32(out,p,val);out[p++]=S32; out[p++]=2; out[p++]=0; break;
case S8G:g=ops[i++]; idx=ops[i++]; val=ops[i++];out[p++]=P; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=A; out[p++]=G; out[p++]=val; out[p++]=S8; out[p++]=0; out[p++]=0; break;
case S8C:g=ops[i++]; idx=ops[i++]; val=ops[i++];out[p++]=P; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=A; out[p++]=C; out[p++]=val & 0x7f; out[p++]=S8; out[p++]=0; out[p++]=0; break;
case LD:g=ops[i++]; idx=ops[i++];out[p++]=G; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL; out[p++]=A; out[p++]=L32; out[p++]=2; out[p++]=0; break;
case ST:g=ops[i++]; idx=ops[i++]; val=ops[i++];out[p++]=G; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL; out[p++]=A;out[p++]=G; out[p++]=val; out[p++]=S32; out[p++]=2; out[p++]=0; break;
case BL:out[p++]=K;out[p++]=V;out[p++]=O;out[p++]=V;break;case EE:out[p++]=E;out[p++]=E;break;case IC:v=ops[i++];out[p++]=G;out[p++]=v;out[p++]=C;out[p++]=1;out[p++]=A;out[p++]=S;out[p++]=v;break;case DC:v=ops[i++];out[p++]=G;out[p++]=v;out[p++]=C;out[p++]=1;out[p++]=B;out[p++]=S;out[p++]=v;break;case GA1:v=ops[i++];out[p++]=G;out[p++]=v;out[p++]=C;out[p++]=1;out[p++]=A;break;case GB1:v=ops[i++];out[p++]=G;out[p++]=v;out[p++]=C;out[p++]=1;out[p++]=B;break;case UV:out[p++]=U;out[p++]=V;break;case BF1:out[p++]=F;out[p++]=1;break;case R0:out[p++]=R;out[p++]=0;break;case C0:out[p++]=C;out[p++]=0;break;case C1:out[p++]=C;out[p++]=1;break;case CM1:out[p++]=C;out[p++]=0x7f;break;case CM2:out[p++]=C;out[p++]=0x7e;break;case SH2:out[p++]=C;out[p++]=2;out[p++]=SL;out[p++]=A;break;case SK:
g=ops[i++]; idx=ops[i++]; val=ops[i++];out[p++]=G; out[p++]=g; out[p++]=G; out[p++]=idx;out[p++]=C; out[p++]=2; out[p++]=SL; out[p++]=A;
out[p++]=C; if (val >= -64 && val < 64) out[p++]=val & 0x7f; else p=writeSleb32(out,p,val);out[p++]=S32; out[p++]=2; out[p++]=0; break;}}}
return p;}
export function buildDiffWasm() {
const types=[],typeMap=new Map();
const internType=(params,results)=>{
const key=`${params.join(',')}=>${results.join(',')}`;
let id=typeMap.get(key);
if (id === undefined) { id=types.length; types.push({ params,results }); typeMap.set(key,id); }
return id;};
const qa=0,qb=1,qc=2,qd=3,qe=4,qf=5,qg=6,qh=7,qi=8,qj=9,qk=10,ql=11,qm=12,qn=13,qo=14,qp=15,qq=16,qr=17,qs=18,qt=19,qu=20,qv=21,qw=22,qx=23,qy=24,qz=25,qA=26,qB=27,qC=28,qD=29,qE=30,qF=31,qG=32,qH=33,qI=34,qJ=35,qK=36,qL=37,qM=38,qN=39,qO=40,qP=41,qQ=42,qR=43,qS=44,qT=45,qU=46,qV=47,qW=48,qX=49,qY=50,qZ=51,q0=52,q1=53,q2=54,q3=55,q4=56,q5=57,q6=58,q7=59,q8=60,q9=61,Qa=62,Qb=63,Qc=64,Qd=65,Qe=66,Qf=67,Qg=68,Qh=69,Qi=70,Qj=71,Qk=72,Ql=73,Qm=74,Qn=75,Qo=76,Qp=77,Qq=78,Qr=79,Qs=80,Qt=81,Qu=82,Qv=83,Qw=84,Qx=85,Qy=86,Qz=87,QA=88,QB=89,QC=90,gc=91;
const Fa=0,Fb=1,Fc=2,Fd=3,Fe=4,Ff=5,Fg=6,Fh=7,Fi=8,Fj=9,Fk=10,Fl=11,Fm=12,Fn=13,Fo=14,Fp=15,Fq=16,Fr=17,Fs=18,Ft=19,Fu=20,Fv=21,Fw=22,fc=23;
const funcs=new Array(fc);
const def=(id,params,results,build)=>{
const locals=[];
const loc=(t=I)=>{ const idx=params.length + locals.length; locals.push(t); return idx; };
const ops=build(loc);
ops.push(E);funcs[id]={ typeIdx: internType(params,results),locals,ops };};
def(Fa,[I],[],(loc)=>{
const a=0,b=loc(),c=loc();
return [MZ,T,c,C,16,SL,S,b,G,a,G,b,GU,UV,G,a,C,65535,A,C,16,SR,G,c,B,MG,CM1,EQ,UV,UN,EE,];});
def(Fb,[I,I],[I],(loc)=>{
const a=0,b=1,c=loc(),d=loc();
return [C0,Q,qa,G,a,Q,qb,G,a,C,31,A,C,-16,AN,T,c,Q,qc,G,b,Q,qd,G,c,G,b,A,C,31,A,C,-16,AN,T,d,Q,qe,G,d,C,64,A,Y,Fa,G,c,];});
def(Fc,[I],[I],()=>[G,0,Q,qf,G,0,C,256,A,Y,Fa,C0,]);
def(Fd,[I,I],[I],(loc)=>{
const a=0,b=1,c=loc(),d=loc(),e=loc(),f=loc(),g=loc(W);
return [G,b,EZ,UV,C0,X,E,C0,S,c,G,a,S,f,G,a,G,b,A,T,d,C,16,B,S,e,C,10,VS8,S,g,BL,G,f,G,e,GT,BF1,G,c,G,f,VL,0,G,g,VE8,VBM,PP,A,S,c,G,f,C,16,A,S,f,R0,EE,BL,G,f,G,d,GEU,BF1,G,f,L8,0,C,10,EQ,G,c,A,S,c,IC,f,R0,EE,GB1,d,L8,0,C,10,NE,UV,IC,c,E,G,c,];});
def(Fe,[],[],(loc)=>{
const a=loc(),b=loc(),c=loc(),d=loc(),e=loc(),f=loc(),g=loc();
const h=loc(),i=loc(),j=loc(),k=loc(),l=loc(),m=loc(),n=loc(),o=loc();
return [P,qa,S,a,P,qc,S,b,P,qb,S,c,P,qd,S,d,G,c,G,d,G,c,G,d,LU,Z,S,e,C0,S,f,G,e,C,16,B,S,g,BL,G,f,G,g,GT,BF1,G,a,G,f,A,VL,0,G,b,G,f,A,VL,0,VE8,VBM,C,0xffff,XR,T,o,UV,G,f,G,o,TZ,A,S,f,R,2,E,G,f,C,16,A,S,f,R0,EE,BL,G,f,G,e,GEU,BF1,G,a,G,f,A,L8,0,G,b,G,f,A,L8,0,NE,BF1,IC,f,R0,EE,G,f,G,c,EQ,G,f,G,d,EQ,AN,UV,G,a,G,c,Y,Fd,Q,qg,C0,Q,qh,G,c,Q,qi,G,d,Q,qj,G,c,Q,qk,G,d,Q,ql,X,E,BL,G,f,EZ,BF1,G,a,G,f,A,C1,B,L8,0,C,10,EQ,BF1,DC,f,R0,EE,G,f,Q,qi,G,f,Q,qj,G,a,G,f,Y,Fd,Q,qg,G,c,G,f,B,S,m,G,d,G,f,B,S,n,G,m,G,n,G,m,G,n,LU,Z,S,k,C0,S,j,G,k,C,16,B,S,l,BL,G,j,G,l,GT,BF1,G,a,G,c,A,G,j,B,C,16,B,VL,0,G,b,G,d,A,G,j,B,C,16,B,VL,0,VE8,VBM,C,0xffff,XR,T,o,UV,G,j,G,o,C,16,SL,CZ,A,S,j,R,2,E,G,j,C,16,A,S,j,R0,EE,BL,G,j,G,k,GEU,BF1,G,a,G,c,A,G,j,B,C1,B,L8,0,
G,b,G,d,A,G,j,B,C1,B,L8,0,NE,BF1,IC,j,R0,EE,G,c,G,j,B,S,h,G,d,G,j,B,S,i,G,j,C0,GT,UV,G,h,G,f,EQ,U,I,C1,H,G,a,G,h,A,C1,B,L8,0,C,10,EQ,E,G,i,G,f,EQ,U,I,C1,H,G,b,G,i,A,C1,B,L8,0,C,10,EQ,E,AN,EZ,UV,BL,G,h,G,c,GEU,BF1,G,a,G,h,A,L8,0,C,10,EQ,UV,IC,h,IC,i,R,2,E,IC,h,IC,i,R0,EE,EE,G,h,Q,qk,G,i,Q,ql,G,a,G,h,A,G,c,G,h,B,Y,Fd,Q,qh,];});
def(Ff,[I,I,I],[I],(loc)=>{
const a=0,b=1,c=2,d=loc();
return [C0,S,d,BL,G,d,C,16,A,G,c,GU,BF1,G,a,G,d,A,VL,0,G,b,G,d,A,VL,0,VE8,VBM,C,0xffff,NE,UV,C0,X,E,G,d,C,16,A,S,d,R0,EE,BL,G,d,C,8,A,G,c,GU,BF1,G,a,G,d,A,L64,0,G,b,G,d,A,L64,0,I6N,UV,C0,X,E,G,d,C,8,A,S,d,R0,EE,BL,G,d,G,c,GEU,BF1,G,a,G,d,A,L8,0,G,b,G,d,A,L8,0,NE,UV,C0,X,E,IC,d,R0,EE,C1,];});
def(Fg,[],[],(loc)=>{
const a=loc(),b=loc(),c=loc(),d=loc(),e=loc(),f=loc();
const g=loc(),h=loc(),i=loc(),j=loc(),k=loc(),l=loc();
const m=loc(),n=loc(),o=loc(),p=loc(),q=loc(),r=loc();
const s=loc(),u=loc(),v=loc(),w=loc(),x=loc(),y=loc(),z=loc(),_a=loc(),_b=loc();
const _c=loc(J),_d=loc(J),_e=loc(J),_f=loc(J),_g=loc(J),_h=loc(J),_i=loc(W);
const _j=loc(),_k=loc(),_l=loc(),_m=loc(),_n=loc(),_o=loc(),_p=loc(),_q=loc(),_r=loc(),_s=loc();
const _t=loc(),_u=loc(),_v=loc(),_w=loc(),_x=loc();
const ops=[
P,qa,T,g,P,qi,A,P,qk,P,qi,B,Y,Fd,T,a,Q,qm,P,qc,T,h,P,qj,A,P,ql,P,qj,B,Y,Fd,T,b,Q,qn,G,a,G,b,G,a,G,b,LU,Z,S,c,P,qe,S,f,];
const alloc=(gVar,...szOps)=>{
ops.push(G,f,Q,gVar,G,f);
for (let t=0; t < szOps.length; t++) ops.push(szOps[t]);
ops.push(A,C,7,A,C,-8,AN,S,f);};alloc(qo,G,a,C,4,A,C,2,SL);alloc(qp,G,a,C,4,A,C,3,SL);alloc(qq,G,b,C,4,A,C,2,SL);
const pushScanPlain=(baseL,stG,enG,bG)=>{
ops.push(P,stG,S,s,P,enG,S,u,P,bG,T,_a,G,s,S32,0,BL,G,s,G,u,GEU,BF1,BL,G,s,G,u,GEU,BF1,G,baseL,G,s,A,L8,0,C,10,EQ,UV,IC,s,R,2,E,IC,s,R0,EE,G,_a,C,4,A,T,_a,G,s,S32,0,R0,EE,);};ops.push(G,a,EZ,G,b,EZ,OR,U,V);alloc(qr,C,16); alloc(qs,C,16);alloc(qt,C,16); alloc(qu,C,16);alloc(qv,C,16); alloc(qw,C,16);ops.push(G,f,Q,qx,G,f,C,64,A,Y,Fa);ops.push(G,a,U,V); pushScanPlain(g,qi,qk,qo); ops.push(E);ops.push(G,b,U,V); pushScanPlain(h,qj,ql,qq); ops.push(E);ops.push(X,E,C,16,S,d,BL,G,d,G,a,C1,SL,GEU,BF1,G,d,C1,SL,S,d,R0,EE,GB1,d,T,e,Q,qy,);alloc(qz,G,d,C,2,SL);alloc(qA,G,a,C,4,A,C,2,SL);alloc(qB,G,b,C,4,A,C,2,SL);alloc(qC,G,a,C,2,SL);alloc(qD,G,a,C,2,SL);alloc(qE,G,a,C,2,SL);alloc(qF,G,a,C,2,SL);alloc(qG,G,a,C,2,SL);alloc(qH,G,a,C,4,A,C,2,SL);
alloc(qI,G,b,C,4,A,C,2,SL);alloc(qJ,G,a,C,4,A,C,2,SL);alloc(qK,G,b,C,4,A,C,2,SL);alloc(qL,G,c,C,4,A,C,2,SL);alloc(qM,G,c,C,4,A,C,2,SL);alloc(qN,G,a,C,4,A,C,2,SL);alloc(qO,G,c,C,4,A,C,2,SL);alloc(qP,G,c,C,4,A,C,2,SL);alloc(qQ,G,c,C,4,A,C,2,SL);alloc(qR,G,a,C,4,A);alloc(qS,G,a,C,4,A);alloc(qT,G,b,C,4,A);alloc(qU,G,b,C,4,A);alloc(qV,G,c,C,4,A);alloc(qW,G,b,C,4,A);alloc(qX,G,c,C,4,A,C,2,SL);alloc(qY,G,c,C,4,A,C,2,SL);alloc(qZ,G,c,C,4,A,C,2,SL);alloc(q0,G,c,C,4,A,C,2,SL);alloc(q1,G,b,C,4,A,C,2,SL);alloc(q2,G,c,C,4,A,C,2,SL);alloc(q3,G,c,C,4,A,C,2,SL);alloc(q4,G,a,C,4,A,C,2,SL);alloc(q5,G,b,C,4,A,C,2,SL);alloc(q6,G,c,C,4,A,C,2,SL);alloc(q7,G,c,C,4,A,C,2,SL);alloc(q8,G,c,C,4,A,C,2,SL);alloc(q9,G,c,C,4,A,C,2,SL);alloc(Qa,G,c,C,4,A,C,2,SL);alloc(Qb,G,a,C,4,A,C,2,SL);alloc(Qc,G,a,C,4,A,C,2,SL);
alloc(Qd,G,c,C,4,A,C,2,SL);alloc(Qe,G,c,C,4,A,C,2,SL);alloc(Qf,G,c,C,4,A,C,2,SL);alloc(Qg,C,520 * 4);alloc(Qh,C,520 * 4);
const pushHashOneLine=(baseL)=>{
ops.push(C6,0x84222325,0xcbf29ce4,S,_f,K,V,BL,G,s,G,v,GT,BF1,G,baseL,G,s,A,VL,0,G,_i,VE8,VBM,T,z,UV,G,z,TZ,S,x,G,x,C,8,GE,UV,G,_f,G,baseL,G,s,A,L64,0,I6X,C6,0x1b3,0x100,I6M,S,_f,C6,-1,-1,C,15,G,x,B,C,3,SL,EX,I6R,S,_g,G,_f,G,baseL,G,s,A,C,8,A,L64,0,G,_g,I6A,I6X,C6,0x1b3,0x100,I6M,S,_f,H,C6,-1,-1,C,7,G,x,B,C,3,SL,EX,I6R,S,_g,G,_f,G,baseL,G,s,A,L64,0,G,_g,I6A,I6X,C6,0x1b3,0x100,I6M,S,_f,E,G,s,G,x,A,C1,A,S,s,R,3,E,G,_f,G,baseL,G,s,A,L64,0,I6X,C6,0x1b3,0x100,I6M,G,baseL,G,s,A,C,8,A,L64,0,I6X,C6,0x1b3,0x100,I6M,S,_f,G,s,C,16,A,S,s,R0,EE,BL,G,s,G,w,GT,BF1,G,baseL,G,s,A,L64,0,T,_c,C6,0x0a0a0a0a,0x0a0a0a0a,I6X,S,_d,G,_d,C6,0x01010101,0x01010101,I6S,G,_d,C6,-1,-1,I6X,I6A,C6,0x80808080,0x80808080,I6A,T,_e,I6Z,EZ,UV,G,_e,I6T,WR,C,3,SR,S,x,C6,-1,-1,C,7,G,x,B,C,3,SL,EX,I6R,S,_g,
G,_f,G,_c,G,_g,I6A,I6X,C6,0x1b3,0x100,I6M,S,_f,G,s,G,x,A,C1,A,S,s,R,3,E,G,_f,G,_c,I6X,C6,0x1b3,0x100,I6M,S,_f,G,s,C,8,A,S,s,R0,EE,C6,0,0,S,_h,C0,S,y,BL,G,s,G,u,GEU,BF1,G,baseL,G,s,A,L8,0,S,x,G,_h,G,x,EX,G,y,EX,I6L,I6O,S,_h,G,y,C,8,A,S,y,IC,s,G,x,C,10,EQ,BF1,R0,EE,G,y,UV,G,_f,G,_h,I6X,C6,0x1b3,0x100,I6M,S,_f,EE,);};ops.push(G,f,Q,qx,G,f,C,64,A,Y,Fa,P,qz,T,l,C0,G,d,C,2,SL,MFL,P,qC,T,o,C0,G,a,C,2,SL,MFL,P,qD,T,p,C0,G,a,C,2,SL,MFL,P,Qb,C0,G,a,C,2,SL,MFL,P,qo,S,i,P,qp,S,j,P,qq,S,k,P,qA,S,m,P,qB,S,n,P,qE,S,q,P,qF,S,r,C,10,VS8,S,_i,P,qi,S,s,P,qk,S,u,G,u,C,16,B,S,v,G,u,C,8,B,S,w,G,i,G,s,S32,0,G,i,S,_a,G,j,S,_b,C0,S,_j,BL,G,_j,G,a,GEU,BF1,G,s,S,_l,);pushHashOneLine(g);ops.push(G,s,G,_l,B,S,_m,G,_a,C,4,A,T,_a,G,s,S32,0,G,_b,G,_f,S64,0,G,_b,C,8,A,S,_b,
G,_f,G,_f,C6,32,0,I6R,I6X,WR,G,e,AN,S,_n,BL,LD,l,_n,T,_o,EZ,UV,GA1,_j,S,_s,ST,l,_n,_s,ST,m,_j,_j,SK,o,_j,1,ST,q,_j,_j,R,2,E,GB1,_o,S,_p,G,j,G,_p,C,3,SL,A,L64,0,G,_f,I6E,G,i,G,_p,SH2,T,_s,L32,4,G,_s,L32,0,T,_q,B,G,_m,EQ,AN,UV,G,g,G,_q,A,G,g,G,_l,A,G,_m,Y,Ff,UV,ST,m,_j,_p,G,o,G,_p,SH2,T,_s,G,_s,L32,0,C1,A,S32,0,R,3,EE,GA1,_n,G,e,AN,S,_n,R0,EE,IC,_j,R0,EE,);
const emitFastEqMatch=(p1,p2,lenL)=>{
ops.push(G,p1,VL,0,G,p2,VL,0,VE8,VBM,C,0xffff,XR,S,_s,G,lenL,C,16,LEU,UV,G,_s,C,32,G,lenL,B,SL,EZ,S,_x,H,G,_s,EZ,UV,G,lenL,C,32,LEU,UV,G,p1,G,lenL,A,C,16,B,VL,0,G,p2,G,lenL,A,C,16,B,VL,0,VE8,VBM,C,0xffff,EQ,S,_x,H,G,p1,C,16,A,G,p2,C,16,A,G,lenL,C,16,B,Y,Ff,S,_x,EE,E,);};ops.push(P,qj,S,s,P,ql,S,u,G,u,C,16,B,S,v,G,u,C,8,B,S,w,G,k,G,s,S32,0,G,k,S,_a,C0,S,_j,C0,S,_k,BL,G,_k,G,b,GEU,BF1,C0,S,_x,G,_j,S,_t,K,V,G,_t,G,a,LU,UV,G,i,G,_t,SH2,T,_s,L32,0,S,_u,G,_s,L32,4,S,_v,G,_v,G,_u,B,S,_w,G,s,G,_w,A,G,u,LEU,G,s,G,_w,A,G,u,EQ,G,g,G,_v,A,C1,B,L8,0,C,10,EQ,OR,AN,UV,G,g,G,_u,A,S,_q,G,h,G,s,A,S,_o,);emitFastEqMatch(_q,_o,_w);ops.push(G,_x,F,2,EE,GA1,_t,T,_t,G,a,LU,UV,G,i,G,_t,SH2,T,_s,L32,0,S,_u,G,_s,L32,4,S,_v,G,_v,G,_u,B,S,_w,G,s,G,_w,A,G,u,LEU,
G,s,G,_w,A,G,u,EQ,G,g,G,_v,A,C1,B,L8,0,C,10,EQ,OR,AN,UV,G,g,G,_u,A,S,_q,G,h,G,s,A,S,_o,);emitFastEqMatch(_q,_o,_w);ops.push(E,EE,G,_x,UV,G,s,G,_w,A,S,s,G,_a,C,4,A,T,_a,G,s,S32,0,LD,m,_t,S,_p,ST,n,_k,_p,G,p,G,_p,SH2,T,_s,G,_s,L32,0,C1,A,S32,0,ST,r,_p,_k,GA1,_t,S,_j,H,G,s,S,_l,);pushHashOneLine(h);ops.push(G,s,G,_l,B,S,_m,G,_a,C,4,A,T,_a,G,s,S32,0,G,_f,G,_f,C6,32,0,I6R,I6X,WR,G,e,AN,S,_n,C,-3,S,_r,BL,LD,l,_n,T,_o,EZ,BF1,GB1,_o,S,_p,G,j,G,_p,C,3,SL,A,L64,0,G,_f,I6E,G,i,G,_p,SH2,T,_s,L32,4,G,_s,L32,0,T,_q,B,G,_m,EQ,AN,UV,G,g,G,_q,A,G,h,G,_l,A,G,_m,Y,Ff,UV,G,_p,S,_r,G,p,G,_p,SH2,T,_s,G,_s,L32,0,C1,A,S32,0,ST,r,_p,_k,LD,o,_p,C1,EQ,UV,LD,q,_p,C1,A,S,_j,H,G,_j,C,2,A,G,a,LU,UV,G,_j,C,2,A,S,_s,LD,m,_s,G,_p,EQ,UV,G,_j,C,3,A,S,_j,EE,E,R,3,EE,
GA1,_n,G,e,AN,S,_n,R0,EE,ST,n,_k,_r,E,IC,_k,R0,EE,);
return ops;});
def(Fh,[],[I],(loc)=>{
const a=loc(),b=loc(),c=loc(),d=loc(),e=loc(),f=loc(),g=loc(),h=loc(),i=loc();
const j=loc(),k=loc(),l=loc(),m=loc(),n=loc(),o=loc(),p=loc(),q=loc();
const r=loc(),s=loc(),u=loc(),v=loc(),w=loc(),x=loc();
const y=loc(),z=loc(),_a=loc(),_b=loc(),_c=loc(),_d=loc(),_e=loc(),_f=loc(),_g=loc(),_h=loc(),_i=loc();
const _j=loc(),_k=loc(),_l=loc(),_m=loc(),_n=loc(),_o=loc(),_p=loc(),_q=loc(),_r=loc();
const _s=loc(),_t=loc(),_u=loc(),_v=loc(),_w=loc(),_x=loc(),_y=loc(),_z=loc(),_A=loc(),_B=loc(),_C=loc();
const _D=loc(),_E=loc(),_F=loc(),_G=loc(),_H=loc(),_I=loc(),_J=loc(),_K=loc(),_L=loc(),_M=loc();
const _N=loc(),_O=loc(),_P=loc(),_Q=loc(),_R=loc();
const _S=loc(),_T=loc(),_U=loc(),_V=loc(),_W=loc(),_X=loc(),_Y=loc();
const _Z=loc(),_0=loc(),_1=loc(),_2=loc(),_3=loc(),_4=loc(),_5=loc();
const _6=loc(),_7=loc(),_8=loc(),_9=loc(),_aa=loc(),_ab=loc(),_ac=loc();
return [P,qm,S,a,P,qn,S,b,P,qA,S,_D,P,qB,S,_E,P,Qg,S,_F,P,Qh,S,_G,P,qG,S,_S,P,qC,S,_T,P,qD,S,_U,P,qH,S,_V,P,qI,S,_W,P,qR,S,_X,P,qF,S,_Y,P,qJ,S,_Z,P,qK,S,_0,P,qL,S,_1,P,qM,S,_2,P,qN,S,_3,P,qO,S,_4,P,qP,S,_5,P,qV,S,_6,P,qU,S,_7,P,qW,S,_8,P,q1,S,_9,P,q2,S,_aa,P,q3,S,_ab,P,qT,S,_ac,G,_S,C0,G,a,C,2,SL,MFL,C0,S,e,GB1,a,S,c,BL,G,c,C0,LT,BF1,LD,_D,c,S,f,LD,_S,f,C1,A,S,g,ST,_S,f,g,G,g,LD,_U,f,GT,UV,IC,e,E,ST,_V,c,e,DC,c,R0,EE,SK,_V,a,0,G,_S,C0,G,a,C,2,SL,MFL,C0,S,e,GB1,b,S,c,BL,G,c,C0,LT,BF1,LD,_E,c,T,f,C,-3,EQ,UV,IC,e,H,LD,_S,f,C1,A,S,g,ST,_S,f,g,G,g,LD,_T,f,GT,UV,IC,e,EE,ST,_W,c,e,DC,c,R0,EE,SK,_W,b,0,G,_X,C0,G,a,MFL,G,_Z,C0,S32,0,C0,S,h,C0,S,i,C0,S,c,BL,G,c,G,a,GEU,BF1,LD,_D,c,S,f,
LD,_T,f,C1,EQ,LD,_U,f,C1,EQ,AN,UV,G,_X,G,f,A,C1,S8,0,IC,h,LD,_Y,f,S,d,G,i,EZ,UV,G,_1,G,d,S32,0,G,_2,G,c,S32,0,SK,_3,c,-1,C1,S,i,H,GB1,i,S,l,LD,_1,l,G,d,LT,UV,ST,_1,i,d,ST,_2,i,c,LD,_2,l,S,_r,ST,_3,c,_r,IC,i,H,C0,S,j,G,i,S,k,BL,G,j,G,k,GE,BF1,G,j,G,k,A,C1,SR,S,l,LD,_1,l,G,d,LT,UV,GA1,l,S,j,H,G,l,S,k,E,R0,EE,ST,_1,j,d,ST,_2,j,c,G,j,C0,GT,U,I,GB1,j,S,l,LD,_2,l,H,CM1,E,S,_r,ST,_3,c,_r,EE,E,GA1,c,T,c,ST,_Z,c,h,R0,EE,G,_0,C0,S32,0,C0,S,e,C0,S,c,BL,G,c,G,b,GEU,BF1,LD,_E,c,T,f,C0,GE,UV,G,e,G,_X,G,f,A,L8,0,A,S,e,E,GA1,c,T,c,ST,_0,c,e,R0,EE,P,qS,C0,G,a,MFL,P,qT,C0,G,b,MFL,G,i,C0,GT,U,I,GB1,i,S,l,LA,qM,l,H,CM1,E,S,m,G,i,S,n,BL,G,n,C1,LT,BF1,SA,qO,n,m,LD,_D,m,S,f,LA,qF,f,S,_r,SA,qP,n,_r,S8C,qS,m,1,S8C,qT,_r,1,
LA,qN,m,S,m,DC,n,R0,EE,P,qO,CM1,S32,0,P,qP,CM1,S32,0,GA1,i,S,l,SA,qO,l,a,SA,qP,l,b,G,_6,C0,G,i,C,2,A,MFL,CM1,S,_u,C1,S,n,C0,S,c,BL,G,c,G,a,GEU,BF1,LD,_D,c,S,f,G,_X,G,f,A,L8,0,UV,LD,_Y,f,S,s,G,n,G,i,LE,UV,LD,_4,n,G,c,EQ,UV,G,_u,LD,_5,n,LT,UV,G,_6,G,n,A,C1,S8,0,E,IC,n,EE,G,s,G,_u,GT,UV,G,s,S,_u,EE,IC,c,R0,EE,G,b,S,_v,G,i,S,n,GB1,a,S,c,BL,G,c,C0,LT,BF1,LD,_D,c,S,f,G,_X,G,f,A,L8,0,UV,LD,_Y,f,S,s,G,n,C1,GE,UV,LD,_4,n,G,c,EQ,UV,G,_v,LD,_5,n,LE,UV,G,_6,G,n,A,C0,S8,0,E,DC,n,EE,G,s,G,_v,LT,UV,G,s,S,_v,EE,DC,c,R0,EE,C0,S,y,C0,S,z,BL,G,z,G,i,GT,BF1,LA,qO,z,C1,A,S,_a,LA,qP,z,C1,A,S,_b,GA1,z,S,l,LA,qO,l,G,_a,B,S,_e,LA,qP,l,G,_b,B,S,_f,G,_e,C0,GT,G,_f,C0,GT,AN,UV,
G,_D,G,_a,SH2,S,_H,G,_E,G,_b,SH2,S,_I,BL,G,_e,C0,LE,G,_f,C0,LE,OR,BF1,G,_H,L32,0,G,_I,L32,0,NE,BF1,IC,_a,IC,_b,G,_H,C,4,A,S,_H,G,_I,C,4,A,S,_I,DC,_e,DC,_f,R0,EE,BL,G,_e,C0,LE,G,_f,C0,LE,OR,BF1,GB1,_e,S,m,GB1,_f,S,l,LD,_H,m,LD,_I,l,NE,BF1,G,m,S,_e,G,l,S,_f,R0,EE,C0,S,_r,K,V,G,_e,EZ,G,_f,EZ,OR,UV,G,_e,G,_f,A,S,_r,R,1,E,G,_e,C1,EQ,G,_f,C1,EQ,AN,UV,C,2,S,_r,R,1,E,G,_e,G,_f,A,S,l,C,256,G,l,C,256,G,l,LT,Z,S,_g,G,_a,G,_e,A,S,m,LD,_D,m,S,_h,G,_b,G,_f,A,S,l,LD,_E,l,S,_i,SK,_D,m,-1,SK,_E,l,-2,C0,S,_c,BL,LD,_H,_c,LD,_I,_c,NE,BF1,IC,_c,R0,EE,G,_F,G,_c,S32,0,C0,S,_q,C1,S,q,BL,G,q,G,_g,GT,BF1,C0,S,p,C0,G,q,B,S,_j,BL,G,p,G,q,GT,BF1,G,p,C0,GT,U,I,GB1,p,S,j,LD,_F,j,H,CM2,E,S,_k,
G,p,G,q,LT,U,I,LD,_F,p,H,CM2,E,S,_l,G,_k,C0,GE,G,_k,G,_e,LT,AN,S,_m,G,_l,C0,GE,G,_l,G,_j,B,C1,B,G,_f,LT,AN,S,_n,G,_m,G,_n,EZ,GA1,_k,G,_l,GE,OR,AN,U,I,GA1,_k,H,G,_n,U,I,G,_l,H,CM2,EE,S,_o,G,_o,C0,LT,UV,SK,_G,p,-2,H,G,_o,G,_j,B,S,_p,BL,LD,_H,_o,LD,_I,_p,NE,BF1,IC,_o,IC,_p,R0,EE,G,_o,G,_e,EQ,G,_p,G,_f,EQ,AN,UV,G,q,S,_r,C1,S,_q,R,5,E,ST,_G,p,_o,E,IC,p,G,_j,C,2,A,S,_j,R0,EE,G,_F,S,j,G,_G,S,_F,G,j,S,_G,IC,q,R0,EE,ST,_D,m,_h,ST,_E,l,_i,G,_q,EZ,UV,G,_e,G,_f,A,S,_r,EE,H,G,_e,G,_f,A,S,_r,E,SA,qQ,z,_r,G,y,G,_r,A,S,y,IC,z,R0,EE,G,y,Q,Qi,P,qU,C0,G,b,MFL,C0,S,w,C1,S,o,C0,S,r,BL,G,r,G,a,GEU,BF1,LD,_D,r,S,f,L8G,qR,f,L8G,qS,r,EZ,AN,UV,LA,qF,f,S,s,BL,G,o,G,i,GT,BF1,LA,qO,o,G,r,GE,BF1,IC,o,R0,EE,
CM1,S,x,C0,S,q,BL,G,q,C,16,GT,BF1,G,o,G,q,A,S,p,G,p,C1,GE,G,p,G,i,LE,AN,UV,LA,qP,p,S,v,L8G,qU,v,EZ,UV,LA,qO,p,S,u,G,u,G,r,B,T,_r,C,-16,GE,G,_r,C,16,LE,AN,UV,G,r,G,u,LT,G,s,G,v,GT,AN,G,r,G,u,GT,G,s,G,v,LT,AN,OR,UV,G,p,S,x,R,5,EE,EE,GB1,o,G,q,B,S,p,G,p,C1,GE,G,p,G,i,LE,AN,UV,LA,qP,p,S,v,L8G,qU,v,EZ,UV,LA,qO,p,S,u,G,u,G,r,B,T,_r,C,-16,GE,G,_r,C,16,LE,AN,UV,G,r,G,u,LT,G,s,G,v,GT,AN,G,r,G,u,GT,G,s,G,v,LT,AN,OR,UV,G,p,S,x,R,5,EE,EE,IC,q,R0,EE,G,x,C0,GT,UV,LA,qO,x,S,u,LA,qP,x,S,v,S8C,qU,s,1,S8C,qU,v,1,SA,qX,w,r,SA,qY,w,s,SA,qZ,w,u,SA,q0,w,v,IC,w,EE,IC,r,R0,EE,G,_9,C0,S32,0,C0,S,_P,C0,S,_N,C0,S,c,BL,G,c,G,b,GEU,BF1,G,_P,G,_N,GE,UV,G,_8,G,c,A,C1,S8,0,G,_P,S,_N,H,G,_8,G,c,A,C0,S8,0,E,C0,S,_Q,G,_7,G,c,A,L8,0,EZ,UV,
LD,_E,c,T,f,C0,GE,UV,LD,_T,f,C0,GT,UV,G,_ac,G,c,A,L8,0,U,I,C,2,H,CM2,E,S,_Q,EE,E,G,_P,G,_Q,A,S,_P,GA1,c,T,c,ST,_9,c,_P,R0,EE,G,_P,S,_O,GB1,b,S,c,BL,G,c,C0,LT,BF1,GA1,c,S,_r,LD,_9,_r,T,_P,G,_O,LT,UV,G,_P,S,_O,E,LD,_9,c,G,_O,GT,UV,G,_8,G,c,A,C0,S8,0,E,DC,c,R0,EE,G,_aa,C0,S32,0,G,_ab,C0,S32,0,C0,S,_J,C1,S,n,BL,G,n,G,i,GT,BF1,LD,_4,n,S,r,LD,_5,n,S,s,G,r,C0,GT,G,s,C0,GT,AN,G,_7,G,s,A,L8,0,EZ,AN,G,_8,G,s,A,L8,0,AN,UV,IC,_J,ST,_aa,_J,r,ST,_ab,_J,s,E,IC,n,R0,EE,GA1,_J,T,_J,Q,Qj,ST,_aa,_J,a,ST,_ab,_J,b,C0,S,d,BL,G,d,G,_J,GEU,BF1,LA,q2,d,S,_a,GA1,d,S,_r,LA,q2,_r,S,_c,BL,G,_a,G,_c,GEU,BF1,SA,q4,_a,d,IC,_a,R0,EE,LA,q3,d,S,_b,LA,q3,_r,S,_d,BL,G,_b,G,_d,GEU,BF1,SA,q5,_b,d,IC,_b,R0,
EE,IC,d,R0,EE,SA,q4,a,_J,SA,q5,b,_J,P,q6,C0,G,_J,C,2,SL,MFL,C0,S,c,BL,G,c,G,w,GEU,BF1,LA,qX,c,S,r,LA,q4,r,S,d,GA1,d,S,_r,LA,qZ,c,S,u,LA,qY,c,S,s,LA,q0,c,S,v,G,u,LA,q2,d,GE,G,u,LA,q2,_r,LT,AN,G,s,LA,q3,d,GE,AN,G,s,LA,q3,_r,LT,AN,G,v,LA,q3,d,GE,AN,G,v,LA,q3,_r,LT,AN,UV,LA,q6,d,C1,A,S,m,SA,q6,d,m,E,IC,c,R0,EE,C0,S,d,BL,G,d,G,_J,GEU,BF1,GA1,d,T,_K,LA,q2,_K,S,_c,LA,q2,d,S,_a,LA,q3,_K,S,_d,LA,q3,d,S,_b,G,_c,G,_a,B,S,_L,G,_d,G,_b,B,S,_M,G,_a,S,m,BL,G,m,G,_c,GEU,BF1,LD,_D,m,S,f,LA,Qb,f,G,_K,NE,UV,SA,Qb,f,_K,SC,Qc,f,1,H,LA,Qc,f,C1,A,S,_r,SA,Qc,f,_r,E,IC,m,R0,EE,G,_b,S,m,BL,G,m,G,_d,GEU,BF1,LD,_E,m,T,f,C0,GE,UV,LA,Qb,f,G,_K,EQ,UV,LA,Qc,f,T,_r,C0,GT,UV,DC,_r,SA,Qc,f,_r,DC,_L,DC,_M,EE,E,
IC,m,R0,EE,LA,q1,_d,LA,q1,_b,B,T,_r,C0,LT,U,I,G,_r,C1,SS,H,C0,E,S,_R,LA,q6,d,S,g,G,_L,G,g,A,G,_R,A,T,_r,C0,GT,U,I,G,_r,H,C0,E,S,_L,G,_M,G,g,A,G,_R,A,T,_r,C0,GT,U,I,G,_r,H,C0,E,S,_M,SA,q7,d,_L,SA,q8,d,_M,IC,d,R0,EE,SC,q9,_J,0,SC,Qa,_J,0,GA1,_J,S,_r,SC,q9,_r,0,SC,Qa,_r,0,GB1,_J,S,d,BL,G,d,C0,LT,BF1,GA1,d,S,_r,LA,q9,_r,LA,q7,d,A,S,_L,SA,q9,d,_L,LA,Qa,_r,LA,q8,d,A,S,_M,SA,Qa,d,_M,DC,d,R0,EE,P,qH,L32,0,P,qI,L32,0,A,G,h,G,i,B,C1,SL,A,S,_s,G,y,G,_s,B,S,_t,P,Qd,C0,S32,0,P,Qe,C0,S32,0,C0,S,_z,C0,S,m,C0,S,_B,C1,S,n,BL,G,n,G,i,GT,BF1,LA,qO,n,S,_w,LA,qP,n,S,_x,G,_w,G,m,LT,UV,IC,n,R,1,E,C0,S,_y,G,n,S,_C,BL,G,_w,G,a,GE,G,_x,G,b,GE,OR,BF1,LD,_D,_w,LD,_E,_x,NE,BF1,G,_C,G,i,LE,UV,LA,qO,_C,G,_w,EQ,UV,
G,_y,L8G,qV,_C,A,S,_y,IC,_C,EE,IC,_w,IC,_x,R0,EE,G,_w,G,a,LT,G,_x,G,b,LT,AN,G,_y,C1,SL,G,_t,GT,AN,UV,C0,S,_A,G,_B,S,z,BL,G,z,G,n,GE,BF1,G,_A,LA,qQ,z,A,S,_A,IC,z,R0,EE,SA,Qf,_z,_A,IC,_z,SA,Qd,_z,_w,SA,Qe,_z,_x,G,_w,S,m,GB1,_C,S,_B,E,G,_C,S,n,R0,EE,C0,S,_A,G,_B,S,z,BL,G,z,G,i,GT,BF1,G,_A,LA,qQ,z,A,S,_A,IC,z,R0,EE,SA,Qf,_z,_A,GA1,_z,T,_z,Q,Qk,SA,Qd,_z,a,SA,Qe,_z,b,G,y,];});
def(Fi,[I,I,I,I,I,I],[],(loc)=>{
const a=0,b=1,c=2,d=3,e=4,f=5;
const g=loc(),h=loc(),i=loc(),j=loc(),k=loc(),l=loc();
const m=loc(),n=loc(),o=loc(),p=loc(),q=loc();
const r=loc(),s=loc(),u=loc(),v=loc();
const w=loc(),x=loc(),y=loc(),z=loc(),_a=loc(),_b=loc(),_c=loc();
const _d=loc(),_e=loc(),_f=loc(),_g=loc(),_h=loc(),_i=loc();
const _j=loc(),_k=loc(),_l=loc(),_m=loc(),_n=loc(),_o=loc();
const _p=loc(),_q=loc(),_r=loc(),_s=loc(),_t=loc(),_u=loc(),_v=loc(),_w=loc(),_x=loc(),_y=loc();
const _z=loc(),_A=loc(),_B=loc(),_C=loc(),_D=loc();
const _E=loc(),_F=loc(),_G=loc(),_H=loc(),_I=loc(),_J=loc(),_K=loc(),_L=loc();
const _M=loc(),_N=loc(),_O=loc(),_P=loc(),_Q=loc(),_R=loc(),_S=loc();
const _T=loc(),_U=loc(),_V=loc(),_W=loc(),_X=loc(),_Y=loc(),_Z=loc();
const _0=loc(),_1=loc(),_2=loc(),_3=loc(),_4=loc(),_5=loc();
const _6=loc(),_7=loc(),_8=loc(),_9=loc(),_aa=loc(),_ab=loc(),_ac=loc();
const _ad=loc(),_ae=loc(),_af=loc(),_ag=loc(),_ah=loc(),_ai=loc(),_aj=loc(),_ak=loc();
const ops=[
G,c,G,a,B,S,g,G,d,G,b,B,S,h,P,Ql,S,_F,G,g,EZ,G,h,EZ,AN,UV,X,E,P,q4,S,_ad,P,q5,S,_ae,P,qJ,S,_af,P,qK,S,_ag,P,Qa,S,_ah,P,qI,S,_ai,P,q9,S,_aj,P,qH,S,_ak,];
const emitPushOp=(kindOp0,kindOp1,cntOp0,cntOp1)=>{
ops.push(G,_F,C0,GT,U,I,GB1,_F,S,_y,L8G,Qm,_y,kindOp0,kindOp1,EQ,H,C0,E,UV,GB1,_F,S,_y,LA,Qn,_y,cntOp0,cntOp1,A,S,_s,SA,Qn,_y,_s,H,P,Qm,G,_F,A,kindOp0,kindOp1,S8,0,P,Qn,G,_F,SH2,cntOp0,cntOp1,S32,0,IC,_F,E,);};
const emitIsValid=(kL)=>{
ops.push(LD,_ad,_l,S,_p,LD,_ae,_m,S,_q,G,_p,G,_q,G,_p,G,_q,GT,Z,S,_r,G,_r,G,q,LU,U,I,GA1,_r,H,G,q,E,S,_y,LD,_af,_l,S,_s,LD,_ag,_m,S,_t,G,_s,G,_t,GT,U,I,G,_s,G,_t,B,H,C0,E,S,_u,G,_t,G,_s,GT,U,I,G,_t,G,_s,B,H,C0,E,S,_v,LD,_ah,_y,T,_x,LD,_ai,_m,G,_u,A,T,_w,G,_x,G,_w,GT,Z,C1,SL,G,_b,G,kL,A,LE,LD,_aj,_y,T,_w,LD,_ak,_l,G,_v,A,T,_x,G,_w,G,_x,GT,Z,C1,SL,G,_c,G,kL,B,LE,AN,);};ops.push(G,g,EZ,U,V); emitPushOp(C,IN,G,h); ops.push(G,_F,Q,Ql,X,E);ops.push(G,h,EZ,U,V); emitPushOp(C,DL,G,g); ops.push(G,_F,Q,Ql,X,E);ops.push(G,g,G,h,B,S,i,P,Qj,S,q,G,e,C,8192,LE,UV,C,5,S,r,C,32,S,s,C,31,S,u,H,C,7,S,r,C,128,S,s,C,127,S,u,E,G,s,C,4,A,S,_E,P,qx,S,j,G,j,C,16,A,T,o,Q,Qo,G,o,G,e,C,12,A,SH2,S,j,G,j,C,16,A,T,p,Q,Qp,G,p,G,e,C,12,A,SH2,T,j,Q,Qq,G,j,GA1,s,G,_E,M,SH2,S,j,
G,e,G,r,SR,C,2,A,S,v,G,j,Q,Qr,G,j,G,v,C,4,SL,A,S,j,G,j,Q,Qs,G,j,Q,Qt,G,j,C,1048576,A,T,_y,Q,Qu,G,_y,Y,Fa,G,o,C,-16,A,CM2,G,e,C,12,A,C,2,SL,MFL,G,p,C,-16,A,CM2,G,e,C,12,A,C,2,SL,MFL,P,qA,G,a,SH2,S,m,P,qB,G,b,SH2,S,n,LA,qA,c,S,k,LA,qB,d,S,l,SC,qA,c,-1,SC,qB,d,-2,C0,S,w,BL,LD,m,w,LD,n,w,NE,BF1,IC,w,R0,EE,G,o,G,w,S32,0,P,Qr,S,_A,G,_A,C0,S32,0,G,_A,C0,S32,4,G,_A,C0,S32,8,G,_A,P,Qt,S32,12,P,Qt,G,w,S32,0,P,Qt,C,4,A,Q,Qt,C1,S,_z,C0,S,_C,C0,S,_D,C0,S,x,C0,S,y,G,w,G,g,LT,G,w,G,h,LT,OR,UV,C1,S,z,BL,G,z,G,e,GT,BF1,G,e,G,z,B,S,_a,G,_a,G,i,B,S,_b,G,_a,G,i,A,S,_c,GB1,x,S,_l,C0,G,_b,B,S,_m,G,_l,G,_m,G,_l,G,_m,GT,Z,S,_d,GA1,y,S,_l,G,_c,S,_m,G,_l,G,_m,G,_l,G,_m,LT,Z,S,_e,G,_d,G,z,XR,C1,AN,UV,IC,_d,E,G,_e,G,z,XR,C1,AN,UV,DC,_e,E,
G,_d,G,z,A,C1,SS,S,_f,G,_e,G,z,A,C1,SS,S,_g,GB1,_f,S,_y,SK,p,_y,-2,GA1,_g,S,_y,SK,p,_y,-2,SK,o,z,-2,G,_f,S,_h,G,_d,S,_i,GB1,_f,S,_y,LD,o,_y,S,_j,BL,G,_h,G,_g,GT,BF1,LD,o,_h,S,_k,G,_j,G,g,LU,S,_n,G,_k,C0,GE,G,_k,G,_i,B,C1,B,G,h,LU,AN,S,_o,G,_n,G,_o,EZ,GA1,_j,G,_k,GE,OR,AN,U,I,GA1,_j,H,G,_o,U,I,G,_k,H,CM2,EE,S,_l,G,_l,C0,LT,UV,SK,p,_h,-2,H,G,_l,G,_i,B,S,_m,BL,LD,m,_l,LD,n,_m,NE,BF1,IC,_l,IC,_m,R0,EE,G,_l,G,g,EQ,G,_m,G,h,EQ,AN,UV,G,z,S,_C,G,_i,S,_D,R,5,E,ST,p,_h,_l,E,G,_k,S,_j,IC,_h,G,_i,C,2,A,S,_i,R0,EE,G,f,UV,BL,G,_f,G,_g,GT,BF1,LD,p,_f,S,_l,G,_l,C0,GE,UV,G,_l,G,_d,B,S,_m,);emitIsValid(_d);ops.push(F,2,SK,p,_f,-2,E,IC,_f,G,_d,C,2,A,S,_d,R0,EE,BL,G,_f,G,_g,GT,BF1,LD,p,_g,S,_l,G,_l,C0,GE,UV,
G,_l,G,_e,B,S,_m,);emitIsValid(_e);ops.push(F,2,SK,p,_g,-2,E,DC,_g,G,_e,C,2,B,S,_e,R0,EE,H,BL,G,_f,G,_g,GT,BF1,LD,p,_f,C0,GE,BF1,IC,_f,G,_d,C,2,A,S,_d,R0,EE,BL,G,_f,G,_g,GT,BF1,LD,p,_g,C0,GE,BF1,DC,_g,G,_e,C,2,B,S,_e,R0,EE,E,G,_d,S,x,G,_e,S,y,G,o,S,_y,G,p,T,o,Q,Qo,G,_y,T,p,Q,Qp,G,z,G,u,AN,EZ,UV,G,_g,G,_f,B,C1,A,C,2,SL,S,_B,G,_B,C0,LT,UV,C0,S,_B,E,P,Qt,G,_B,A,P,Qu,GU,UV,P,Qt,G,_B,A,C,1048576,A,T,_y,Q,Qu,G,_y,Y,Fa,E,P,Qr,G,_z,C,4,SL,A,S,_A,G,_A,G,_f,S32,0,G,_A,G,_d,S32,4,G,_A,G,_e,S32,8,G,_A,P,Qt,S32,12,G,_B,C0,GT,UV,P,Qt,G,o,G,_f,SH2,G,_B,MCP,P,Qt,G,_B,A,Q,Qt,E,IC,_z,E,IC,z,R0,EE,E,G,_C,S,_G,G,_D,S,_H,G,g,S,_I,BL,G,_G,C0,LE,BF1,GB1,_G,G,r,SR,S,_J,G,_J,G,r,SL,S,_K,G,_G,G,_K,B,S,_L,
P,Qr,G,_J,C,4,SL,A,S,_A,G,_A,L32,0,S,_N,G,_A,L32,4,S,_O,G,_A,L32,8,S,_P,G,_A,L32,12,S,_M,G,_H,G,_L,B,S,_Q,G,_O,G,_Q,G,_O,G,_Q,GT,Z,S,_R,G,_H,G,_L,A,S,_y,G,_P,G,_y,G,_P,G,_y,LT,Z,S,_S,P,Qq,CM2,G,_L,C,3,A,C,2,SL,MFL,G,_R,S,_i,BL,G,_i,G,_S,GT,BF1,G,_i,G,_Q,B,C1,SS,S,_5,G,_i,G,_K,A,C1,SS,G,_N,B,S,_y,LD,_M,_y,S,_l,SA,Qq,_5,_l,G,_i,C,2,A,S,_i,R0,EE,G,_R,S,_T,G,_S,S,_U,C1,S,_V,BL,G,_V,G,_L,GT,BF1,G,_K,G,_V,A,S,z,G,e,G,z,B,S,_a,G,_a,G,i,B,S,_b,G,_a,G,i,A,S,_c,G,_H,G,_L,G,_V,B,B,S,_W,G,_H,G,_L,G,_V,B,A,S,_X,GB1,_T,S,_l,C0,G,_b,B,S,_m,G,_l,G,_m,G,_l,G,_m,GT,Z,S,_Y,G,_W,G,_Y,G,_W,G,_Y,GT,Z,S,_Y,GA1,_U,S,_l,G,_c,S,_m,G,_l,G,_m,G,_l,G,_m,LT,Z,S,_Z,G,_X,G,_Z,G,_X,G,_Z,LT,Z,S,_Z,G,_Y,G,z,XR,C1,AN,UV,IC,_Y,E,G,_Z,G,z,XR,C1,AN,UV,DC,_Z,E,
GB1,_V,G,_E,M,S,_0,G,_V,G,_E,M,S,_1,G,_Q,G,_V,B,S,_2,G,_Y,G,_2,B,C1,SS,S,_3,G,_Z,G,_2,B,C1,SS,S,_4,G,_3,C0,GT,UV,G,_1,G,_3,A,C1,B,S,_y,SC,Qq,_y,-2,E,G,_1,G,_4,A,C1,A,S,_y,SC,Qq,_y,-2,G,_Y,S,_i,BL,G,_i,G,_Z,GT,BF1,G,_i,G,_2,B,C1,SS,S,_5,GB1,_i,T,_y,G,_T,GE,G,_y,G,_U,LE,AN,U,I,G,_0,G,_5,A,C1,B,S,_y,LA,Qq,_y,H,CM2,E,S,_j,GA1,_i,T,_y,G,_T,GE,G,_y,G,_U,LE,AN,U,I,G,_0,G,_5,A,S,_y,LA,Qq,_y,H,CM2,E,S,_k,G,_j,G,g,LU,S,_n,G,_k,C0,GE,G,_k,G,_i,B,C1,B,G,h,LU,AN,S,_o,G,_n,G,_o,EZ,GA1,_j,G,_k,GE,OR,AN,U,I,GA1,_j,H,G,_o,U,I,G,_k,H,CM2,EE,S,_l,G,_1,G,_5,A,S,_y,G,_l,C0,LT,UV,SC,Qq,_y,-2,H,G,_l,G,_i,B,S,_m,BL,LD,m,_l,LD,n,_m,NE,BF1,IC,_l,IC,_m,R0,EE,SA,Qq,_y,_l,E,G,_i,C,2,A,S,_i,R0,EE,G,_V,G,_L,LT,G,f,AN,UV,BL,G,_3,G,_4,GT,BF1,
G,_1,G,_3,A,S,_5,LA,Qq,_5,S,_l,G,_l,C0,GE,UV,G,_l,G,_Y,B,S,_m,);emitIsValid(_Y);ops.push(F,2,SC,Qq,_5,-2,E,IC,_3,G,_Y,C,2,A,S,_Y,R0,EE,BL,G,_3,G,_4,GT,BF1,G,_1,G,_4,A,S,_5,LA,Qq,_5,S,_l,G,_l,C0,GE,UV,G,_l,G,_Z,B,S,_m,);emitIsValid(_Z);ops.push(F,2,SC,Qq,_5,-2,E,DC,_4,G,_Z,C,2,B,S,_Z,R0,EE,E,G,_Y,S,_T,G,_Z,S,_U,IC,_V,R0,EE,G,_I,S,_6,G,_H,S,_7,G,_L,S,_V,BL,G,_V,C1,LT,BF1,GB1,_V,G,_E,M,S,_0,G,_Q,G,_V,B,S,_2,G,_7,G,_2,B,C1,SS,S,_5,G,_5,C0,GT,U,I,G,_0,G,_5,A,C1,B,S,_y,LA,Qq,_y,H,CM2,E,S,_j,G,_0,G,_5,A,S,_y,LA,Qq,_y,S,_k,G,_j,G,g,LU,S,_n,G,_k,C0,GE,G,_k,G,_7,B,C1,B,G,h,LU,AN,S,_o,G,_n,G,_o,EZ,GA1,_j,G,_k,GE,OR,AN,UV,GA1,_j,S,_8,C,DL,S,_9,GB1,_7,S,_aa,G,_j,S,_ab,H,G,_k,S,_8,C,IN,S,_9,GA1,_7,S,_aa,G,_k,S,_ab,E,
G,_6,G,_8,B,T,_ac,C0,GT,UV,);emitPushOp(C,KP,G,_ac);ops.push(E);emitPushOp(G,_9,C,1);ops.push(G,_aa,S,_7,G,_ab,S,_6,DC,_V,R0,EE,G,_K,S,_G,G,_7,S,_H,G,_6,S,_I,R0,EE,G,_I,C0,GT,UV,);emitPushOp(C,KP,G,_I);ops.push(E,G,_F,Q,Ql,SA,qA,c,k,SA,qB,d,l,);
return ops;});
def(Fj,[],[],(loc)=>{
const a=loc(),b=loc(),c=loc(),d=loc(),e=loc(),f=loc(),g=loc(),h=loc(),i=loc(),j=loc();
return [P,qx,S,a,G,a,Q,Qm,G,a,P,Qi,C1,SL,C,64,A,C,7,A,C,-8,AN,A,S,a,G,a,Q,Qn,G,a,P,Qi,C1,SL,C,64,A,SH2,S,a,G,a,Q,qx,G,a,C,64,A,Y,Fa,C0,Q,Ql,P,Qk,S,b,G,b,C1,EQ,S,j,GB1,b,S,c,BL,G,c,C0,LT,BF1,GA1,c,S,d,LA,Qd,c,S,e,LA,Qe,c,S,f,LA,Qd,d,S,g,LA,Qe,d,S,h,LA,Qf,c,S,i,G,e,G,f,G,g,G,h,G,i,G,j,Y,Fi,DC,c,R0,EE,];});
def(Fk,[],[],(loc)=>{
const a=loc(),b=loc(),c=loc(),d=loc(),e=loc(),f=loc(),g=loc(),h=loc(),i=loc();
const j=loc(),k=loc(),l=loc(),m=loc(),n=loc(),o=loc();
return [P,Ql,S,a,P,qx,S,b,G,b,Q,qr,G,b,G,a,C,4,A,SH2,S,b,G,b,Q,qs,G,b,G,a,C,4,A,SH2,S,b,G,b,Q,qt,G,b,G,a,C,4,A,SH2,S,b,G,b,Q,qu,G,b,G,a,C,4,A,SH2,S,b,G,b,Q,qv,G,b,G,a,C,4,A,SH2,S,b,G,b,Q,qw,G,b,G,a,C,4,A,SH2,S,b,G,b,Q,qx,G,b,C,64,A,Y,Fa,P,qg,T,f,S,g,C0,S,h,C0,S,i,C0,S,j,GB1,a,S,c,BL,G,c,C0,LT,BF1,L8G,Qm,c,S,d,LA,Qn,c,S,e,G,d,C,KP,EQ,UV,G,f,G,e,A,S,f,G,g,G,e,A,S,g,H,GB1,j,S,k,G,k,C0,LT,U,I,C1,H,LA,qr,k,LA,qt,k,A,G,f,NE,LA,qs,k,LA,qu,k,A,G,g,NE,OR,E,UV,SA,qr,j,f,SA,qs,j,g,SC,qt,j,0,SC,qu,j,0,G,j,S,k,IC,j,E,G,d,C,DL,EQ,UV,LA,qt,k,G,e,A,S,o,SA,qt,k,o,G,f,G,e,A,S,f,G,h,G,e,A,S,h,H,LA,qu,k,G,e,A,S,o,SA,qu,k,o,G,g,G,e,A,S,g,G,i,G,e,A,S,i,EE,DC,c,R0,EE,G,j,Q,Qv,G,h,Q,Qw,G,i,Q,Qx,C0,S,l,C0,S,m,BL,G,m,G,j,GE,BF1,
G,l,C0,GT,UV,GB1,l,S,o,LA,qw,o,S,n,LA,qr,m,LA,qr,n,LA,qt,n,A,B,C,6,LE,UV,SA,qw,o,m,IC,m,R,2,EE,SA,qv,l,m,SA,qw,l,m,IC,l,IC,m,R0,EE,G,l,Q,Qy,];});
def(Fl,[I,I],[I],(loc)=>{
const a=0,b=1,c=loc(),d=loc(),e=loc(),f=loc();
return [G,b,EZ,UV,G,a,C,48,S8,0,GA1,a,X,E,G,a,S,c,BL,G,b,EZ,BF1,G,a,G,b,C,10,RM,C,48,A,S8,0,IC,a,G,b,C,10,DV,S,b,R0,EE,G,c,S,d,GB1,a,S,e,BL,G,d,G,e,GEU,BF1,G,d,L8,0,S,f,G,d,G,e,L8,0,S8,0,G,e,G,f,S8,0,IC,d,DC,e,R0,EE,G,a,];});
def(Fm,[I,I,I,I,I],[I],(loc)=>{
const a=0,b=1,c=2,d=3,e=4,f=loc();
return [G,a,G,e,S8,0,IC,a,G,d,G,c,B,S,f,G,a,G,b,G,c,A,G,f,MCP,G,a,G,f,A,S,a,G,b,G,d,A,C1,B,L8,0,C,10,NE,UV,G,a,C,10,S8,0,G,a,C,37,S8,1,G,a,C,10,S8,2,G,a,C,3,A,S,a,E,G,a,];});
def(Fn,[],[],(loc)=>{
const a=loc(),b=loc(),c=loc(),d=loc(),e=loc(),f=loc(),g=loc(),h=loc(),i=loc();
const j=loc(),k=loc(),l=loc(),m=loc(),n=loc(),o=loc(),p=loc(),q=loc(),r=loc();
const s=loc(),u=loc(),v=loc(),w=loc(),x=loc(),y=loc(),z=loc(),_a=loc(),_b=loc(),_c=loc(),_d=loc();
const _e=loc(),_f=loc(),_g=loc(),_h=loc(),_i=loc(),_j=loc();
const _k=loc(),_l=loc(),_m=loc(),_n=loc(),_o=loc(),_p=loc(),_q=loc(),_r=loc(),_s=loc(),_t=loc(),_u=loc();
const _v=loc(),_w=loc(),_x=loc();
const ops=[
P,qg,S,e,P,qh,S,f,P,qm,S,g,P,qn,S,h,P,Qy,S,i,G,e,G,g,A,G,f,A,S,c,G,e,G,h,A,G,f,A,S,d,P,qa,S,j,P,qc,S,k,P,qi,S,l,P,qk,S,m,P,qb,S,n,P,qo,S,_s,P,qq,S,_t,P,qx,S,b,G,b,S,q,G,b,C,16,A,S,b,G,b,S,r,G,b,C,16,A,S,b,G,b,T,a,Q,Qz,G,n,P,qd,A,G,c,G,d,A,SH2,G,i,C,6,SL,A,C,512,A,S,_r,G,a,G,_r,A,Y,Fa,G,a,S,b,];
const emitHdr=(key)=>{
const [off, len] = HDR_MAP[key];
ops.push(G,b,C,off,C,len,MNT,G,b,C,len,A,S,b);};
const emitPushOld=(opByte)=>{
ops.push(G,_k,G,e,GE,G,_k,G,e,G,g,A,LT,AN,UV,G,_k,G,e,B,S,_x,G,_s,G,_x,SH2,T,_u,L32,0,S,_v,G,_u,L32,4,S,_w,H,G,_k,G,e,LT,UV,G,_k,G,e,G,o,B,B,S,_x,G,q,G,_x,SH2,T,_x,L32,0,S,_v,G,_x,L32,4,S,_w,H,G,_k,G,e,G,g,A,B,S,_x,G,r,G,_x,SH2,T,_x,L32,0,S,_v,G,_x,L32,4,S,_w,EE,G,b,G,j,G,_v,G,_w,C,opByte,Y,Fm,S,b,);};emitHdr('makefun-diff/1 old='); ops.push(G,b,G,c,Y,Fl,S,b);emitHdr(' new='); ops.push(G,b,G,d,Y,Fl,S,b);emitHdr(' hunks='); ops.push(G,b,G,i,Y,Fl,S,b);emitHdr(' deleted='); ops.push(G,b,P,Qw,Y,Fl,S,b);emitHdr(' inserted='); ops.push(G,b,P,Qx,Y,Fl,S,b);ops.push(G,b,C,10,S8,0,IC,b,G,i,EZ,UV,G,b,Q,QA,X,E,C0,S,o,P,qr,L32,0,G,e,C,3,A,LT,G,e,C0,GT,AN,UV,G,e,C,3,G,e,C,3,LT,Z,S,o,G,l,S,s,G,q,G,o,SH2,G,s,S32,0,GB1,o,S,u,BL,G,u,C0,LT,BF1,
G,s,G,j,G,s,A,C1,B,L8,0,C,10,EQ,U,I,C,2,H,C1,E,B,S,s,BL,G,s,C0,LT,BF1,G,j,G,s,A,L8,0,C,10,EQ,BF1,DC,s,R0,EE,IC,s,G,q,G,u,SH2,G,s,S32,0,DC,u,R0,EE,E,C0,S,p,G,f,C0,GT,UV,P,qw,GB1,i,SH2,L32,0,S,x,LA,qr,x,LA,qt,x,A,C,3,A,G,e,G,g,A,GT,UV,G,f,C,3,G,f,C,3,LT,Z,S,p,G,m,S,s,G,r,G,s,S32,0,C1,S,u,BL,G,u,G,p,GT,BF1,BL,G,s,G,n,GEU,BF1,G,j,G,s,A,L8,0,C,10,EQ,UV,IC,s,R,2,E,IC,s,R0,EE,G,r,G,u,SH2,G,s,S32,0,IC,u,R0,EE,EE,C0,S,v,BL,G,v,G,i,GE,BF1,LA,qv,v,S,w,LA,qw,v,S,x,LA,qr,w,S,y,LA,qs,w,S,z,LA,qr,x,S,_a,LA,qs,x,S,_b,LA,qt,x,S,_c,LA,qu,x,S,_d,G,y,C,3,GT,U,I,G,y,C,3,B,H,C0,E,S,_e,G,z,G,y,G,_e,B,B,S,_f,G,c,G,_a,G,_c,A,B,S,_g,G,_g,C,3,G,_g,C,3,LT,Z,S,_h,G,_a,G,_c,A,G,_h,A,S,_i,
G,_b,G,_d,A,G,_h,A,S,_j,);emitHdr('@ ');ops.push(G,b,GA1,_e,Y,Fl,S,b,G,b,C,32,S8,0,IC,b,G,b,G,_i,G,_e,B,Y,Fl,S,b,G,b,C,32,S8,0,IC,b,G,b,GA1,_f,Y,Fl,S,b,G,b,C,32,S8,0,IC,b,G,b,G,_j,G,_f,B,Y,Fl,S,b,G,b,C,10,S8,0,IC,b,G,_e,S,_k,G,w,S,_l,BL,G,_l,G,x,GT,BF1,LA,qr,_l,S,_m,LA,qs,_l,S,_n,LA,qt,_l,S,_o,LA,qu,_l,S,_p,BL,G,_k,G,_m,GE,BF1,);emitPushOld(61);ops.push(G,_k,C1,A,S,_k,R0,EE,C0,S,u,BL,G,u,G,_o,GE,BF1,G,_m,G,u,A,S,_k);emitPushOld(45);ops.push(G,u,C1,A,S,u,R0,EE,C0,S,u,BL,G,u,G,_p,GE,BF1,G,_n,G,u,A,G,e,B,S,_q,G,b,G,k,G,_t,G,_q,SH2,T,_u,L32,0,G,_u,L32,4,C,43,Y,Fm,S,b,IC,u,R0,EE,G,_m,G,_o,A,S,_k,IC,_l,R0,EE,BL,G,_k,G,_i,GE,BF1,);emitPushOld(61);ops.push(G,_k,C1,A,S,_k,R0,EE,
IC,v,R0,EE,G,b,Q,QA,);
return ops;});
def(Fo,[],[I],()=>[Y,Fe,P,qi,P,qk,EQ,P,qj,P,ql,EQ,AN,UV,C0,Q,qm,C0,Q,qn,C0,Q,Qy,C0,Q,Qw,C0,Q,Qx,P,qe,Q,qx,Y,Fn,P,QA,P,Qz,B,X,E,Y,Fg,P,qm,EZ,P,qn,EZ,OR,UV,P,qr,P,qg,S32,0,P,qs,P,qg,S32,0,P,qt,P,qm,S32,0,P,qu,P,qn,S32,0,P,qv,C0,S32,0,P,qw,C0,S32,0,C1,Q,Qv,C1,Q,Qy,P,qm,Q,Qw,P,qn,Q,Qx,Y,Fn,P,QA,P,Qz,B,X,E,Y,Fh,D,Y,Fj,Y,Fk,Y,Fn,P,QA,P,Qz,B,]);
def(Fp,[],[I],()=>[P,Qz]);
def(Fq,[],[I],()=>[P,QB]);
def(Fr,[I,I],[I],(loc)=>{
const a=0,b=1,c=loc();
return [BL,G,a,G,b,GEU,BF1,G,a,L8,0,T,c,C,32,EQ,G,c,C,9,EQ,OR,G,c,C,10,EQ,OR,G,c,C,13,EQ,OR,EZ,BF1,IC,a,R0,EE,G,a,];});
def(Fs,[I,I],[I],(loc)=>{
const a=0,b=1,c=loc();
return [G,a,G,b,GEU,UV,CM1,X,E,G,a,L8,0,C,34,NE,UV,CM1,X,E,IC,a,BL,G,a,G,b,GEU,UV,CM1,X,E,G,a,L8,0,S,c,G,c,C,34,EQ,UV,GA1,a,X,E,G,c,C,92,EQ,UV,GA1,a,G,b,GEU,UV,CM1,X,E,G,a,C,2,A,S,a,R,1,E,G,c,C,32,LU,G,c,C,127,GU,OR,UV,CM1,X,E,IC,a,R0,EE,CM1,];});
def(Ft,[I,I,I],[I],(loc)=>{
const a=0,b=1,c=2;
const d=loc(),e=loc(),f=loc(),g=loc(),h=loc(),i=loc(),j=loc(),k=loc();
const l=loc(W),m=loc(W),n=loc(W),o=loc(W);
const ops=[
G,a,G,b,GEU,UV,CM1,X,E,G,a,L8,0,C,34,NE,UV,CM1,X,E,IC,a,G,c,S,d,G,b,C,16,B,S,e,C,34,VS8,S,l,C,92,VS8,S,m,C,32,VS8,S,n,];
const pushHex=(chL,outL)=>{
ops.push(G,chL,C,48,B,T,outL,C,9,LEU,UV,H,G,chL,C,32,OR,C,87,B,T,outL,C,10,LU,G,outL,C,15,GU,OR,UV,CM1,X,EE,);};
const pushHandleEsc=()=>{
ops.push(G,a,C1,A,G,b,GEU,UV,CM1,X,E,GA1,a,L8,0,S,i,G,i,C,110,EQ,UV,G,d,C,10,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,114,EQ,UV,G,d,C,13,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,34,EQ,UV,G,d,C,34,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,92,EQ,UV,G,d,C,92,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,116,EQ,UV,G,d,C,9,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,98,EQ,UV,G,d,C,8,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,102,EQ,UV,G,d,C,12,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,47,EQ,UV,G,d,C,47,S8,0,G,a,C,2,A,S,a,IC,d,H,G,i,C,117,EQ,UV,G,a,C,5,A,G,b,GEU,UV,CM1,X,E,G,a,L8,2,C,48,NE,G,a,L8,3,C,48,NE,OR,UV,CM1,X,E,G,a,L8,4,S,h,);pushHex(h,j);ops.push(G,j,C,7,GU,UV,CM1,X,E,G,a,L8,5,S,h);pushHex(h,k);ops.push(G,d,G,j,C,4,SL,G,k,OR,S8,0,G,a,C,6,A,S,a,IC,d,
H,CM1,X,EE,EE,EE,EE,E,);};ops.push(K,V,O,V,G,a,G,e,GT,BF1,G,a,VL,0,T,o,G,o,G,l,VE8,G,o,G,m,VE8,VOR,G,o,G,n,VL8,VOR,VBM,T,f,EZ,UV,G,d,G,o,VS,0,G,a,C,16,A,S,a,G,d,C,16,A,S,d,R,1,E,G,f,TZ,T,g,UV,G,d,G,o,VS,0,G,a,G,g,A,S,a,G,d,G,g,A,S,d,E,G,a,L8,0,S,h,G,h,C,34,EQ,UV,GA1,a,Q,QC,G,d,G,c,B,X,E,G,h,C,92,NE,UV,CM1,X,E,);pushHandleEsc();ops.push(R,0,EE,BL,G,a,G,b,GEU,UV,CM1,X,E,G,a,L8,0,S,h,G,h,C,34,EQ,UV,GA1,a,Q,QC,G,d,G,c,B,X,E,G,h,C,92,EQ,UV,);pushHandleEsc();ops.push(R,1,E,G,h,C,32,LU,G,h,C,127,GU,OR,UV,CM1,X,E,G,d,G,h,S8,0,IC,a,IC,d,R0,EE,CM1,);
return ops;});
def(Fu,[I,I,I],[I],(loc)=>{
const a=0,b=1,c=2,d=loc(),e=loc(),f=loc(),g=loc(),h=loc(),i=loc(),j=loc();
const k=loc(W),l=loc(W),m=loc(W),n=loc(W);
const ops=[
G,c,C,34,S8,0,IC,c,G,a,G,b,A,T,d,C,16,B,S,e,C,34,VS8,S,k,C,92,VS8,S,l,C,32,VS8,S,m,];
const pushEsc=()=>{
ops.push(G,h,C,10,EQ,UV,G,c,C,92,S8,0,G,c,C,110,S8,1,G,c,C,2,A,S,c,H,G,h,C,34,EQ,UV,G,c,C,92,S8,0,G,c,C,34,S8,1,G,c,C,2,A,S,c,H,G,h,C,92,EQ,UV,G,c,C,92,S8,0,G,c,C,92,S8,1,G,c,C,2,A,S,c,H,G,h,C,13,EQ,UV,G,c,C,92,S8,0,G,c,C,114,S8,1,G,c,C,2,A,S,c,H,G,h,C,9,EQ,UV,G,c,C,92,S8,0,G,c,C,116,S8,1,G,c,C,2,A,S,c,H,G,h,C,8,EQ,UV,G,c,C,92,S8,0,G,c,C,98,S8,1,G,c,C,2,A,S,c,H,G,h,C,12,EQ,UV,G,c,C,92,S8,0,G,c,C,102,S8,1,G,c,C,2,A,S,c,H,G,c,C,92,S8,0,G,c,C,117,S8,1,G,c,C,48,S8,2,G,c,C,48,S8,3,G,h,C,4,SR,C,48,A,S,i,G,h,C,15,AN,T,j,C,10,LU,U,I,G,j,C,48,A,H,G,j,C,87,A,E,S,j,G,c,G,i,S8,4,G,c,G,j,S8,5,G,c,C,6,A,S,c,EE,EE,EE,E,);};ops.push(K,V,O,V,G,a,G,e,GT,BF1,G,a,VL,0,T,n,G,n,G,k,VE8,G,n,G,l,VE8,VOR,G,n,G,m,VL8,VOR,VBM,T,f,EZ,UV,G,c,G,n,VS,0,G,a,C,16,A,S,a,G,c,C,16,A,S,c,R,1,E,G,f,TZ,T,g,UV,
G,c,G,n,VS,0,G,a,G,g,A,S,a,G,c,G,g,A,S,c,E,G,a,L8,0,S,h,IC,a,);pushEsc();ops.push(R,0,EE,BL,G,a,G,d,GEU,BF1,G,a,L8,0,S,h,IC,a,G,h,C,34,EQ,G,h,C,92,EQ,OR,G,h,C,32,LU,OR,UV,);pushEsc();ops.push(H,G,c,G,h,S8,0,IC,c,E,R0,EE,G,c,C,34,S8,0,GA1,c,);
return ops;});
def(Fv,[I,I,I],[I],()=>[G,0,G,1,GEU,UV,CM1,X,E,G,0,L8,0,G,2,NE,UV,CM1,X,E,GA1,0,G,1,Y,Fr,]);
def(Fw,[],[I],(loc)=>{
const a=loc(),b=loc(),c=loc(),d=loc(),e=loc();
const f=loc(),g=loc(),h=loc(),i=loc(),j=loc(),k=loc(),l=loc();
const m=loc(),n=loc(),o=loc(),p=loc(),q=loc(),r=loc(),s=loc(),u=loc(),v=loc();
const ops=[
P,qf,S,a,C0,G,a,Y,Fr,S,b,];
const expect=(ch)=>ops.push(G,b,G,a,C,ch,Y,Fv,T,b,C0,LT,UV,CM1,X,E);
expect(91);ops.push(G,a,C,31,A,C,-16,AN,T,c,Q,QB,G,c,C,1024,A,Y,Fa,G,c,S,d,G,d,C,91,S8,0,IC,d,G,b,G,a,LU,UV,G,b,L8,0,C,93,EQ,UV,GA1,b,G,a,Y,Fr,G,a,NE,UV,CM1,X,E,G,d,C,93,S8,0,GA1,d,G,c,B,X,EE,C0,S,e,BL,G,e,C0,GT,UV,G,d,C,16,A,Y,Fa,G,d,C,44,S8,0,IC,d,E,);expect(123);ops.push(C,0,S,f,CM1,S,g,CM1,S,h,BL,G,b,G,a,GEU,UV,CM1,X,E,G,b,L8,0,C,125,EQ,BF1,G,b,C,7,A,G,a,LEU,U,I,G,b,U32,0,C,0x706e6922,EQ,G,b,U32,3,C,0x22747570,EQ,AN,H,C0,E,UV,G,f,UV,CM1,X,E,C1,S,f,G,b,C,7,A,G,a,Y,Fr,S,b,);expect(58); expect(123);ops.push(G,d,C,31,A,C,-16,AN,S,k,C0,S,l,BL,G,b,G,a,GEU,UV,CM1,X,E,G,b,L8,0,C,125,EQ,BF1,G,b,C,5,A,G,a,GU,UV,CM1,X,E,G,b,L8,4,C,34,NE,UV,CM1,X,E,G,b,U32,0,C,0x646c6f22,EQ,UV,C1,S,u,H,G,b,U32,0,C,0x77656e22,EQ,UV,C0,S,u,
H,CM1,X,EE,G,u,UV,G,g,C0,GE,UV,CM1,X,E,H,G,h,C0,GE,UV,CM1,X,EE,G,b,C,5,A,G,a,Y,Fr,S,b,);expect(58);ops.push(G,g,C0,LT,G,h,C0,LT,AN,UV,G,k,G,a,G,b,B,A,C,64,A,Y,Fa,G,b,G,a,G,k,Y,Ft,T,l,C0,LT,UV,CM1,X,E,G,u,UV,G,k,S,i,G,l,S,g,H,G,k,S,j,G,l,S,h,E,H,G,k,G,l,A,C,31,A,C,-16,AN,S,v,G,v,G,a,G,b,B,A,C,64,A,Y,Fa,G,b,G,a,G,v,Y,Ft,T,q,C0,LT,UV,CM1,X,E,G,u,UV,G,v,S,i,G,q,S,g,H,G,v,S,j,G,q,S,h,EE,P,QC,G,a,Y,Fr,S,b,G,b,G,a,GEU,UV,CM1,X,E,G,b,L8,0,C,44,EQ,UV,GA1,b,G,a,Y,Fr,S,b,R,1,E,R,1,EE,);expect(125);ops.push(H,G,b,C,4,A,G,a,LEU,U,I,G,b,U32,0,C,0x22646922,EQ,H,C0,E,UV,G,b,C,4,A,G,a,Y,Fr,S,b,H,G,b,C,7,A,G,a,LEU,U,I,G,b,U32,0,C,0x6f726722,EQ,G,b,U32,3,C,0x2270756f,EQ,AN,H,C0,E,UV,G,b,C,7,A,G,a,Y,Fr,S,b,H,CM1,X,EE,);expect(58);ops.push(G,b,G,a,GEU,UV,CM1,X,E,
G,b,L8,0,C,34,EQ,UV,G,b,G,a,Y,Fs,T,b,C0,LT,UV,CM1,X,E,H,G,b,L8,0,C,45,EQ,UV,IC,b,E,G,b,G,a,GEU,UV,CM1,X,E,G,b,L8,0,T,s,C,48,LU,G,s,C,57,GU,OR,UV,CM1,X,E,BL,G,b,G,a,GEU,BF1,G,b,L8,0,T,s,C,48,LU,G,s,C,57,GU,OR,BF1,IC,b,R0,EE,E,G,b,G,a,Y,Fr,S,b,E,G,b,G,a,GEU,UV,CM1,X,E,G,b,L8,0,C,44,EQ,UV,GA1,b,G,a,Y,Fr,S,b,R,1,E,R,1,EE,);expect(125);ops.push(G,f,EZ,G,g,C0,LT,OR,G,h,C0,LT,OR,UV,CM1,X,E,G,i,Q,qa,G,g,Q,qb,G,j,Q,qc,G,h,Q,qd,G,i,G,g,A,T,v,G,j,G,h,A,T,p,G,v,G,p,G,v,G,p,GU,Z,C,31,A,C,-16,AN,Q,qe,Y,Fo,S,m,P,Qz,S,n,P,QA,S,o,G,d,G,m,C,6,M,A,C,64,A,G,n,LEU,UV,G,n,G,m,G,d,Y,Fu,S,d,H,G,o,C,31,A,C,-16,AN,S,p,G,p,G,m,C,6,M,A,C,64,A,Y,Fa,G,n,G,m,G,p,Y,Fu,S,q,G,q,G,p,B,S,r,G,d,G,p,G,r,MCP,G,d,G,r,A,S,d,E,IC,e,G,b,G,a,LU,UV,
G,b,L8,0,C,44,EQ,UV,GA1,b,G,a,Y,Fr,S,b,R,2,EE,R,1,EE,);expect(93);ops.push(G,b,G,a,NE,UV,CM1,X,E,G,d,C,16,A,Y,Fa,G,d,C,93,S8,0,GA1,d,G,c,B,);
return ops;});
const out=new Uint8Array(32768);
let p=0;
out[p++]=0x00; out[p++]=0x61; out[p++]=0x73; out[p++]=0x6d;out[p++]=0x01; out[p++]=0x00; out[p++]=0x00; out[p++]=0x00;
const beginSec=(id)=>{ out[p++]=id; const lp=p; p += 5; return lp; };
const endSec=(lp)=>{
let len=p - (lp + 5);
for (let i=0; i < 4; i++) { out[lp + i]=(len & 0x7f) | 0x80; len >>>= 7; }
out[lp + 4]=len & 0x7f;};
let lp=beginSec(1);
p=writeUleb(out,p,types.length);
for (let i=0; i < types.length; i++) {
const t=types[i];
out[p++]=0x60; p=writeUleb(out,p,t.params.length);
for (let j=0; j < t.params.length; j++) out[p++]=t.params[j];
p=writeUleb(out,p,t.results.length);
for (let j=0; j < t.results.length; j++) out[p++]=t.results[j];
}endSec(lp);lp=beginSec(3);p=writeUleb(out,p,funcs.length);
for (let i=0; i < funcs.length; i++) p=writeUleb(out,p,funcs[i].typeIdx);
endSec(lp);lp=beginSec(5);out[p++]=0x01; out[p++]=0x00; p=writeUleb(out,p,320);endSec(lp);lp=beginSec(6);p=writeUleb(out,p,gc);
for (let i=0; i < gc; i++) { out[p++]=I; out[p++]=0x01; out[p++]=C; out[p++]=0x00; out[p++]=E; }
endSec(lp);
const exports=[
['memory',0x02,0],['prepareInput',0x00,Fb],['prepareBatch',0x00,Fc],['solveAscii',0x00,Fo],['solveBatchJson',0x00,Fw],['getOutBase',0x00,Fp],['getBatchOutBase',0x00,Fq],];lp=beginSec(7);p=writeUleb(out,p,exports.length);
for (let i=0; i < exports.length; i++) {
const [name,kind,idx]=exports[i];
p=writeUleb(out,p,name.length);
for (let j=0; j < name.length; j++) out[p++]=name.charCodeAt(j);
out[p++]=kind; p=writeUleb(out,p,idx);}endSec(lp);out[p++]=12; out[p++]=1; out[p++]=1;lp=beginSec(10);p=writeUleb(out,p,funcs.length);
for (let i=0; i < funcs.length; i++) {
const fn=funcs[i],locs=fn.locals,bodyStart=p + 5;
let bp=bodyStart,grpCount=0;
const gCounts=[],gTypes=[];
for (let j=0; j < locs.length; j++) {
const t=locs[j];
if (grpCount > 0 && gTypes[grpCount - 1] === t) gCounts[grpCount - 1]++;else { gCounts[grpCount]=1; gTypes[grpCount]=t; grpCount++; }}bp=writeUleb(out,bp,grpCount);
for (let j=0; j < grpCount; j++) { bp=writeUleb(out,bp,gCounts[j]); out[bp++]=gTypes[j]; }
bp=encodeBody(fn.ops,out,bp);
let len=bp - bodyStart;
for (let j=0; j < 4; j++) { out[p + j]=(len & 0x7f) | 0x80; len >>>= 7; }
out[p + 4]=len & 0x7f;p=bp;}endSec(lp);lp=beginSec(11);out[p++]=1; out[p++]=0x01;
p = writeUleb(out, p, HDR_STR.length);
for (let i = 0; i < HDR_STR.length; i++) out[p++] = HDR_STR.charCodeAt(i);
endSec(lp);
const mod=new WebAssembly.Module(out.subarray(0,p));
return new WebAssembly.Instance(mod).exports;}