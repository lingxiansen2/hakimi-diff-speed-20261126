'use strict';
const fs=process.getBuiltinModule('node:fs');
process.getBuiltinModule('node:v8').setFlagsFromString('--liftoff-only --no-wasm-tier-up --no-wasm-dynamic-tiering --wasm-tiering-budget=2147483647 --no-incremental-marking');
const FORMAT='makefun-diff/1',CONTEXT=3;
const HDR='makefun-diff/1 old= new= hunks= deleted= inserted=@ \\n%\\n';
const GV=['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z','A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y'];
const FN=['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z','A','B','C','D','E','F'];
const TY={i:0x7f,j:0x7e,v:0x40};
const OP={
  unr:0,bk:2,lp:3,if:4,dr:0x1a,sl:0x1b,l:0x28,A:0x29,u:0x2d,K:0x2f,s:0x36,H:0x37,w:0x3a,n:0x3b,
  msz:0x3f,mgr:0x40,c6:0x42,Q:0x46,N:0x47,Y:0x49,G:0x4a,U:0x4b,L:0x4c,M:0x4d,E:0x4e,R:0x4f,
  q:0x51,c:0x67,t:0x68,p:0x69,r:0x70,S:0x74,D:0x75,Z:0x76,m:0x7e,o:0x84,x:0x85,
  h:0x86,v:0x88,e:0xa7,f:0xad,br:0x0c,bf:0x0d,
  W:0x128,V:0x200,C:0x20f,X:0x223,T:0x225,B:0x264,O:0x250,P:0x30a,F:0x30b,N0:0x308,
  a:0x400,g:0x401,b:0x402,d:0x403,y:0x404,z:0x405,k:0x406,I:0x41d,J:0x41e
};
const CH={37:0x20,33:0x21,61:0x22,35:0x41,36:0x23,62:0x24,64:0x10,43:0x6a,45:0x6b,42:0x6c,47:0x6e,38:0x71,124:0x72,94:0x73,126:0x45,60:0x48,58:0x05,125:0x0b,93:0x0f};
const BT=new Uint8Array(128);
for(const ch of ' %!=#$>@+-*/&|^~<(){}:[];,?._')BT[ch.charCodeAt(0)]=1;
const GMAP=Object.create(null),FMAP=Object.create(null);
for(let i=0;i<GV.length;i++)GMAP[GV[i]]=i;
for(let i=0;i<FN.length;i++)FMAP[FN[i]]=i;
const FN_SPEC=`a	i		1i	msz=1#16 S%0 Y{%0#65535+#16 Z%1-mgr#-1 Q{unr)
b	i,i	i	2i	#0>a%0>b%0#31+#-16&=2>c%1>d%2%1+#31+#-16&=3>e%3#64+@a%2
c	i,i,i	i		%2#2 R[%0%1+#2-K#0#28252 Q:#0}
d	i,i,i	i	2i 1v	#92 C!5(%1#17+%2 M{%0%1+V#0%5 X B!3(%3~?%3 t!4%0%1%4+#1++u#0#110 Q{%1%4+#2+]}%3%3#1-&!3;)%1#16+!1 br#1}%1%2 R?%0%1+u#0#92 Q%1#1+%2 Y&{%0%1#1++u#0#110 Q{%1#2+])I%1;)%1
e	i,i	i		%1%0%1%1@c[#2:#0}-!1(%1#0 L?%0%1%1@c?J%1;)%1#0<[#0:%1}
f	i,i,i	j	3i 1j	%2%1-=3~{c6#0#0]}%0%1+!4%0%2+!5%3#8 R{%3 f c6#2135587861#-1640531527 m%4 A#0 c6#484763065#-1084733587 m x%4%3#8-#1 Z+A#0 c6#321982955#-1798288965 m x%5#8-A#0 x!6%6%6 c6#30#0 v x c6#484763065#-1084733587 m]}%3#4 R{%4 W#0 f%5#4-W#0 f c6#32#0 h o%3 f c6#2135587861#-1640531527 m x c6#484763065#-1084733587 m]}%4 u#0%4%3#1 Z+u#0#8 S|%5#1-u#0#16 S|%3#24 S|f c6#2135587861#-1640531527 m
g	i,i	i	7i 3v	%1~{#0]}#0!2%0!4%0%1+!3#92 C!9#110 C!10#0!5(%4#16+%3 U?%4 V#0=11%9 X B!6%11%10 X B!7%2%5%7#1&&%6%7#1 Z&p++!2%6#15 Z!5%4#16+!4;)(%4%3 R?%4 u#0=8#110 Q%5&{I%2}%8#92 Q!5 I%4;)%0%1%1@c~{I%2}%2
h			11i	$a!0$c!1$b!2$d!3%2%3%2%3 Y sl!4#0!5(%5#16+%4 M{%0%5+V#0%1%5+V#0 X B#65535^=10{%5%10 t+!5 br#3}%5#16+!5 br#1}%5%4 R?%0%5+u#0%1%5+u#0 N?I%5;)%5%2 Q%5%3 Q&{%0%2@g>j#0>k%2>f%3>g%2>h%3>i]}(%5~?%0%5%5@c?J%5;)%5>f%5>g%0%5@g>j%2%5-!9%3%5-!10%9%10%9%10 Y sl!9#0!8(%8#16+%9 M{%0%2+%8-#16-V#0%1%3+%8-#16-V#0 X B#65535^=10{%8%10#16 S c+!8 br#3}%8#16+!8 br#1}%8%9 R?%0%2+%8-#1-u#0%1%3+%8-#1-u#0 N?I%8;)%2%8-!6%3%8-!7%8#0 G{%6%5 Q[#1:%0%6%6%5-@c}%7%5 Q[#1:%1%7%7%5-@c}&~{%0%6%2@d=8%6-!10%8!6%7%10+!7)%6>h%7>i%0%6+%2%6-@g>k
i	i,i,i	i	1i	%2#16 R{#0!3(%3#16+%2 U?%0%3+V#0%1%3+V#0 X B#65535 N{#0]}%3#16+!3;)%0%2#16-+V#0%1%2#16-+V#0 X B#65535 Q]}#0!3(%3%2 R?%0%3+u#0%1%3+u#0 N{#0]}I%3;)#1
j	i,i,i,i,i		1i	%3%1.#0!5(%5%4 R?%0%1%2@d!1%3#4+=3%1.I%5;)
k	i,i,i,i,j	i	2i	$p%0#3 S+A#0%4 q$o%0_=5 l#4%5,=6-%3 Q&[$a%6+%1%2+%3@i:#0}
l			42i 1j 1v	$a=7$f+$h=20$f-@g=0>l$c=8$g+$i$g-@g=1>m%0#4+#2 S#7+#-8&!2%1#4+#2 S#7+#-8&!3$e!6%6>o%6%2+!6%6>q%6%3+!6%0~%1~|{%6>I%6>C%6#64+>D%6#80+>E%6#96+=6>n%6#64+@a%7$f%20$o%0@j%8$g$i$q%1@j]}%6>z%6%0%1+#8+#2 S#7+#-8&+!6#16!4(%4%0#1 S R?%4#1 S!4;)%4#1-=5>s%6=12>t%6%2+!6%6=13>u%6%3+!6%6=14>v%6%2+!6%6=15>w%6%2+!6%6=17>y%6%2+!6%6!41%6>p%6%2#1 S+!6%6=11>r%6%4_!6%6=16>x%6%2+!6%6#64+@a%11#0%4#2 S F%14#0%2 F%15#0%2 F$o!9$q!10$f!18%20!19#92 C!43%9%18.%9!21$p!22#0!23(%23%0 R?%18!25(%18#17+%19 M{%7%18+V#0%43 X B!37(%37~?%37 t!40%7%18%40+#1++u#0#110 Q{%18%40+#2+!18 br#5}%37%37#1-&!37;)%18#16+!18 br#1}%7%18%19@d!18 br#1)%7%25%18@f!42%18%25-!26%21#4+=21%18.%22%42 H#0%22#8+!22%42%42 c6#32#0 v x e%5&!27(y%11%27=28~{%23#1+!31 z%11%27%31 z%12%23%23 k%14%23#1 z%16%23%23 br#2}%28#1-!29%29%7%25%26%42@k{z%12%23%29%14%29_=31%31,#1+.br#2}%27#1+%5&!27;)I%23;)$g!18$i!19%10%18.%10!21#0!23#0!24(%24%1 R?#0!34%23%0 Y{y%9%23!32%20%32-!33%19%18-!31%33%31%33%31 Y sl!33%7%32+!35%8%18+!36(%34#16+%33 M{%35%34+V#0%36%34+V#0 X B#65535^=37{%34%37 t+!34 br#3}%34#16+!34 br#1}%34%33 R?%35%34+u#0%36%34+u#0 N?I%34;)(%23%0 R?%9%23#1+_,!38%38%32-!39%39%34 U?%38%20 Y%18%39+%19 Q|%7%38%38 y%9%23-@c|~?%21#4+=21%18%39+.y%12%23!29 z%13%24%29%15%29_=31%31,#1+.z%17%29%24 I%23 I%24;)%23%0 Y[y%9%23:%20}%32-%18+!18}%24%1 R?%18!25%8%18%19@d!18%8%25%18@f!42%18%25-!26%21#4+=21%18.%42%42 c6#32#0 v x e%5&!27#-3!30(y%11%27=28~?%28#1-!29%29%8%25%26%42@k{%29!30 z%13%24%29%15%29_=31%31,#1+.z%17%29%24 y%14%29#1 Q{y%16%29#1+!23:%23#2+%0 Y{%23#2+!31 y%12%31%29 Q{%23#3+!23)}br#2}%27#1+%5&!27;)%30#0<{z%13%24%30}I%24;)%41>n
m	i,i		3i	%1#0 L{]}$A!2%2#0 G[$z%2#1-_=3,=4#3&%0 Q:#0}{%3%4%1_.:$z%2_%1#2 S%0|.%2#1+>A}
n	i,i,i,i,i,i	i	17i	%1%0-!6%3%2-!7$t%0_!8$u%2_!9#0!21(%21%6 R%21%7 R|?y%8%21 y%9%21 N?I%21;)%21%6 Q%21%7 Q&{#0]}%5!10%5#1032+!11%10%21.#1!13(%13%4 G?#0!15#0%13-!14(%15%13 G?%15#0 G[%15#1-!16 y%10%16:#-2}!17%15%13<[y%10%15:#-2}!18%17#0 E%17%6<&!19%18#0 E%18%14-#1-%7<&!20%19%20~%17#1+%18 E|&[%17#1+:%20[%18:#-2)!21%21#0<{k%11%15#-2:%21%14-!22(%21%6 R%22%7 R|?y%8%21 y%9%22 N?I%21 I%22;)%21%6 Q%22%7 Q&{%13]}z%11%15%21}I%15%14#2+!14;)%10!16%11!10%16!11 I%13;)%4#1+
o	i,i,i,i,i		54i	%1%0-!5%3%2-!6%4%5%6+%4%5%6+<sl!4%5%6-!7$n=58!8%8!13%8%4#1 S#64+_!8#0!14%8!15%8%4#4+#3 S+!8%8!16%8#8192+=17@a$t%0_!9$u%2_!10 y%9%5!11 y%10%6!12 k%9%5#-1 k%10%6#-2#0!20(y%9%20 y%10%20 N?I%20;)%16!18%18#-2.%18%20 s#4%18#-2 s#8%15=33#0.%33%18 s#4%18#12+!19#0!35#0!36#0!21#0!22%20%5<%20%6<|{#1!23(%23%4 G?%4%23-!24%24%7-!25%24%7+!26%21#1-#0%25-%21#1-#0%25-G sl!27%22#1+%26%22#1+%26<sl!28%27%23^#1&{I%27}%28%23^#1&{J%28}%27%28 G{I%23 br#1}%28%27-#1 Z#3+#2 S!34%19%34+%17 U{%19%34+#65536+=17@a}%19#-2.%18%27#1+%21-#1 D_!54%19#4+!55%54,!44%27!53(%53%28 G?%54 l#4!45%44%5 Y!46%45#0 E%45%53-#1-%6 Y&!47%46%47~%44#1+%45 E|&[%44#1+:%47[%45:#-2)!56%56#0 E{%56%53-!57(y%9%56 y%10%57 N?I%56 I%57;)%56%5 Q%57%6 Q&{%23!35%53!36 br#5)%55%56.%45!44%54#4+!54%55#4+!55%53#2+!53;)%55#-2.%28%27-#1 Z#1+!29#1!30%29!31%19#4+!42%19%29_!43(%30%31 G?%42,#0 E?%42#4+!42 I%30%27#2+!27;)(%30%31 G?%43,#0 E?%43#4-!43 J%31%28#2-!28;)%42#4-#-2.%43#4+#-2.%27!21%28!22%42#4-!18%43#8+!19%19%18%19%18 U sl!19%15%23#3 S+=33%27.%33%18 s#4 I%23;)}z%9%5%11 z%10%6%12%35!23%36!38%5!37(%23#1<?%15%23#1-#3 S+=33,!39%33 l#4!40%40%38#1+%39-#1 D_!41%41,!44%41 l#4!45%44%5 Y!46%45#0 E%45%38-#1-%6 Y&!47%46%47~%44#1+%45 E|&{%44#1+!48#1!49%38#1-!50%44!51:%45!48#2!49%38#1+!50%45!51}%37%48-=52#0 G{%13%14_%52#2 S.I%14}%13%14_#4%49|.I%14%50!38%51!37 J%23;)%37#0 G{#0%37@m}(%14#1-=14#0<?y%13%14=32#3&%32#2 D@m;)%58>n
p			58i	$l!0$m!1%0#4+#2 S#7+#-8&!2$t!5$u!6$v!7$w!8$y!9$n!3#0>A%3!10%3%2+!3%3!11%3%2+!3%3!12%3%2+!3%3!23%3%2#1 S+!3%3#64+@a#0!16#0!13(%13%0 R?y%5%13!15 y%7%15#1 Q y%8%15#1 Q&{y%9%15!14#0!17%16!18%16#0 G{%16#1-!19 y%10%19%14<{%16!17:(%17%18 E?%17%18+#1 Z!19 y%10%19%14<{%19#1+!17:%19!18};))z%10%17%14 z%11%17%13%17#0 G[%17#1-!19 y%11%19:#-1}!22 z%12%13%22%17%16 Q{I%16)I%13;)%16#0 G[%16#1-!19 y%11%19:#-1}!20%16#1-!21(%21#0<?%23%21#3 S+=31%20.y%5%20!15%31 y%9%15 s#4 y%12%20!20 J%21;)%10!24#0!25#0!13(%13%16 R?%23%13#3 S+=31,!29%31 l#4!30#1!26%13#1+!14(%14%16 R?%23%14#3 S+=31,%29%26+N%31 l#4%30%26+N|?I%26 I%14;)%24%25#12*+=31%29.%31%30 s#4%31%26 s#8 I%25%14!13;)%24%25#12*+#7+#-8&!3%25#2+#2 S!22%3!32%3%22+!3%3!33%3%22+!3%3!34%3%22+!3%3!35%3%22+!3%3!36%3%22+!3%3!37%3#2080+=3>n%3#64+@a#0!27#0!28#0!38(%38%25 G?%38%25<{%24%38#12*+=31,!39%31 l#4!40:%0!39%1!40}%39%27-!41%40%28-!42%41~{%42!43:%42~{%41!43:%41#1 Q%42#1 Q&{y%5%27 y%6%28 Q[#0:#2}!43:%41%42+=22#256%22#256 Y sl!22%27%39%28%40%22%37@n=43#256 G{%41%42+!43))#0!44%27!46(%46%39 R?y%5%46!15 y%8%15~{I%44}I%46;)#0!45%28!47(%47%40 R?y%6%47#0<{I%45}I%47;)z%32%38%43%43%44-%45-=22#0 G[%22:#0}!22 z%33%38%22%38%25<{%31 l#8!26%39%26+!27%40%26+!28}I%38;)#0!48#0!38(%38%25 R?%48 y%33%38+!48 z%34%38%48%48%24%38#12*+l#8#1 S-!48 z%35%38%48 I%38;)%48 y%33%25+!49 z%34%25%49%25#1-!38(%38#0<?z%36%38%49 y%34%38=22%49 G{%22!49}J%38;)#0!50#0!51#0!52#-1!53#0!38(%38%25 G?%38%25 Q[#1:y%36%38%50<}{%38%25<{%24%38#12*+=31,!54%31 l#4!55:%0!54%1!55}%54%51 G%55%52 G|{%54%51 Q{#2%55%52-@m:%55%52 Q{#1%54%51-@m:#0!56%53#1+!57(%57%38 G?%56 y%32%57+!56 I%57;)%51%54%52%55%56@o)}%38%25<{%31 l#8!26#0%26@m%54%26+!51%55%26+!52%38!53)%38%25<{y%35%38=22%50<{%22!50)I%38;)$z$A_#7+#-8&>n
q			20i	$A!0$n!1%1=15=19>C%1%0#4+#4 S+!1%1=17>D%1%0#4+_!1%1=18>E%1%0#4+_!1%1>n%1#64+@a$j=5!6#0!7#0!8#0!9#0!14#0!2$z!16(%2%0 R?%16,=13#3&!3%13#2 D!4%3#0 Q{%5%4+!5%6%4+!6:%14~[#1:%14,%14 l#8+%5 N%14 l#4%14 l#12+%6 N|}{%19!14%19#16+!19%14%5.%14%6 s#4%14#0 s#8%14#0 s#12 I%9}%3#1 Q{%14%14 l#8%4+s#8%5%4+!5%7%4+!7:%14%14 l#12%4+s#12%6%4+!6%8%4+!8)%16#4+!16 I%2;)%7>G%8>H#0!10#0!11%15!14#0!12(%11%9 E?%10#0 G{%14,%12-#6 L{%18#4-%11.%14,%14 l#8+!12%14#16+!14 I%11 br#2)%17%11.%18%11.%17#4+!17%18#4+!18%14,%14 l#8+!12 I%10%14#16+!14 I%11;)%10>F
r	i,i	i	4i	%1~{%0#48 w#0%0#1+]}%0!2(%1~?%0%1#10 r#48+w#0 I%0%1#10/!1;)%2!3%0#1-!4(%3%4 R?%3 u#0!5%3%4 u#0 w#0%4%5 w#0 I%3 J%4;)%0
s	i,i	i		%0%1@r=0#32 w#0%0#1+
t	i,i,i,i	i		%0%1%2 N0%0%2+%3@r
u	i,i,i,i,i	i	1i	%0%4 w#0 I%0%3%2-!5%0%1%2+%5 P%0%5+!0%1%3%5@c~{%0#52#5 N0%0#5+!0}%0
v	i,i,i	i	6i	$j!3$l!4%1%3 E%1%3%4+<&{%1%3-!5$o%5_=6,!7%6 l#4!8:%1%3<{%1%3$K--!5$L%5_=5,!7%5 l#4!8:%1%3%4+-!5$M%5_=5,!7%5 l#4!8)%0$a%7%8%2@u
w			53i	$j!4$k!5$l!6$m!7$F!8$C!49%4%6+%5+!2%4%7+%5+!3$a!9$c!10$f!11$h!12$b!13$q!43$n!1%1=16>L%1#16+=17>M%1#32+=0>I%13$d+%2%3+_%8#6 S+#512+!42%0%42+@a%0#34 w#0%0#1+!1%1#0#19%2@t!1%1#19#5%3@t!1%1#24#7%8@t!1%1#31#9$G@t!1%1#40#10$H@t!1%1#28252 n#0%1#2+!1%8~{%1#34 w#0%1#1+>J]}#0>K%49,%4#3+<%4#0 G&{%4#3%4#3<sl=14>K%11!18%16%14_=50%18.%14!19(%19#0 L?%9%18@e!18%50#4-=50%18.J%19;)}%5#0 G{$E%8#1-_,!22%49%22#4 S+=48,%48 l#8+#3+%4%6+G{%5#3%5#3<sl!15%12!18%17=50%18.#1!19(%19%15 G?%9%18%13@d!18%50#4+=50%18.I%19;))#0!20$D!51$E!52(%20%8 E?%51,!21%52,!22%49%21#4 S+=48,!23%48 l#4!24%49%22#4 S+=48,!25%48 l#4!26%48 l#8!27%48 l#12!28%23#3-=48#0 G[%48:#0}!29%24#3-=48#0 G[%48:#0}!30%2%25%27+-!31%31#3<[%31:#3}!32%25%27+%32+!33%26%28+%32+!34%1#50#2 N0%1#2+%29#1+@s%33%29-@s%30#1+@s%34%30-@r!1%1#28252 n#0%1#2+!1%29!35%21!36%49%21#4 S+!48(%36%22 G?%48,!37%48 l#4!38%48 l#8!39%48 l#12!40(%35%37 E?%1%35#61@v!1 I%35;)#0!41(%41%39 E?%1%35#45@v!1 I%35 I%41;)#0!41(%41%40 E?%38%41+%4-!47%43%47_=44,!45%44 l#4!46%1%10%45%46#43@u!1 I%41;)%48#16+!48 I%36;)(%35%33 E?%1%35#61@v!1 I%35;)%51#4+!51%52#4+!52 I%20;)%1#34 w#0%1#1+>J
x		i		@h$f$h Q$g$i Q&{#0>l#0>m#0>F#0>G#0>H$e>n@w$J$I-]}@l$l~$m~|{$C$j.$C$j s#4$C$l s#8$C$m s#12$D#0.$E#0.#1>F$l>G$m>H@w$J$I-]}@p@q@w$J$I-
y	i	i	2i	$O!1(%0%1 R?%0 u#0!2%2#32 Q%2#10 Q%2#13 Q%2#9 Q|||~?I%0;)%0
z	i	i	5i 7v	$O!1%0%1 R{#-2]}%0 u#0#34 N{#-1]}I%0#34 C!6#92 C!7#32 C!8#110 C!9#114 C!10(%0#17+%1 M{%0 V#0!11%0#1+V#0!12%11%7 X B!3%11%6 X%11%8 T O B%3%12%9 X%12%10 X O B#65535^&|=2~{%0%3#32768&[#17:#16}+!0 br#2}%0%2 t+!0:%0%1 R{#-2])%0 u#0!4%4#34 Q{%0#1+]}%4#92 Q{%0#1+%1 R{#-2]}%0#1+u#0!5%5#110 Q%5#114 Q|~{#1>Y}%0#2+!0 br#1}%4#127 U{#1>Y:%4#32 Y{#-1])I%0;)#-2
A	i,i	i		%0$O R{#-2]}%0 u#0%1 N{#-1]}%0#1+@y
B	i			%0#256+@a
C	i,i,i,i			%0>N%0>P%0>Q%1>O%2>R%3>S#0>T#0>U
D	i,i,i			$N>P$N>Q%0>O%1>R%2>S
E		i	13i	$P!0$O!1$T!3%0!2 bk v bk v bk v%3#3 Q{#0]}%0@y!0%0!2%3~{%0#91@A=0#0<{br#2)%0%1 R{br#2}%0 u#0#93 Q{%0#1+@y!0%0%1 Y{br#4}$R~{br#3}#3>T#0]}%3#2 Q{%0#44@A=0#0<{br#2}%0!2}#1!3#1>T%0!2%0#123@A=0#0<{br#1}#0!4#-1!5#-1!7#0>Y(%0%1 R{br#4}%0 u#0#125 Q?%0#7+%1 M[%0 W#0#1886284066 Q%0 W#3#578057584 Q&:#0}{%4{br#6}#1!4%0#7+@y!0%0#58@A=0#0<{br#4}%0#123@A=0#0<{br#4}(%0%1 R{br#7}%0 u#0#125 Q?%0#5+%1 U{br#7}%0 u#4#34 N{br#8}%0 W#0#1684827938 Q{#1!9:%0 W#0#2003136034 Q{#0!9:br#9)%9[%5:%7}#0 E{br#8}%0#5+@y!0%0#58@A=0#0<{br#6}%9{%0!5:%0!7}%0@z=0#0<{br#6}%9{%0!6:%0!8}%0@y!0%0%1 R{br#7}%0 u#0#44 N?%0#1+@y!0;)%0#125@A=0#0<{br#4}:%0@z=0#0<{br#4}%0@y!0%0#58@A=0#0<{br#4}%0%1 R{br#5}%0 u#0#34 Q{%0@z=0#0<{br#5}:%0 u#0#45 Q{I%0}#0!12(%0%1 R?%0 u#0=10#48 Y%10#57 U|?I%0 I%12;)%0%1 R{br#6}%12~{br#7)%0@y!0}%0%1 R{br#4}%0 u#0#44 N?%0#1+@y!0;)%0#125@A=0#0<{br#1}%4~%5#0<|%7#0<|{br#3}$Y{%2>V%0>W%0>P#2>T$U#1+>U#-3]}%5#1+>a%6%5-#2->b%7#1+>c%8%7-#2->d$S>e@x!11$I#1-=12>X%12$U~[#91:#44}w#0%0>P#2>T$U#1+>U%11#1+]}$R~{%2>Q#-2])}#-1
F	i	i		%0#0 Q[$I:%0#1 Q[$Q:%0#2 Q[$V:%0#3 Q[$W:%0#4 Q[$X:$U))}`;
function wU(b,p,v){v>>>=0;while(v>=0x80){b[p++]=(v&0x7f)|0x80;v>>>=7;}b[p++]=v;return p;}
function wS(b,p,v){v|=0;for(;;){const x=v&0x7f;v>>=7;if((!v&&!(x&0x40))||(v===-1&&(x&0x40))){b[p++]=x;return p;}b[p++]=x|0x80;}}
function wS64(b,p,lo,hi){lo>>>=0;hi|=0;for(;;){const x=lo&0x7f;lo=((lo>>>7)|(hi<<25))>>>0;hi>>=7;if((!hi&&!lo&&!(x&0x40))||(hi===-1&&lo===0xffffffff&&(x&0x40))){b[p++]=x;return p;}b[p++]=x|0x80;}}

function buildDiffWasm(){
  const types=[],fT=new Int32Array(FN.length),fL=new Array(FN.length),fC=new Array(FN.length);
  const iT=(ps,rs)=>{
    for(let i=0;i<types.length;i++){const t=types[i];if(t[0].length===ps.length&&t[1].length===rs.length){let ok=1;for(let j=0;j<ps.length;j++)if(t[0][j]!==ps[j]){ok=0;break;}if(ok)for(let j=0;j<rs.length;j++)if(t[1][j]!==rs[j]){ok=0;break;}if(ok)return i;}}
    types.push([ps,rs]);return types.length-1;
  };
  for(const line of FN_SPEC.split('\n')){
    const[fn,ps,rs,ls,c]=line.split('\t');
    const id=FMAP[fn];
    fT[id]=iT(ps?ps.split(',').map(x=>TY[x]):[],rs?rs.split(',').map(x=>TY[x]):[]);
    fL[id]=ls;fC[id]=c;
  }

  const out=new Uint8Array(16384);let p=0;
  out[p++]=0;out[p++]=0x61;out[p++]=0x73;out[p++]=0x6d;out[p++]=1;out[p++]=0;out[p++]=0;out[p++]=0;
  const sec=(id,fn)=>{out[p++]=id;const lp=p;p+=5;fn();let l=p-(lp+5);for(let i=0;i<4;i++){out[lp+i]=(l&0x7f)|0x80;l>>>=7;}out[lp+4]=l&0x7f;};
  sec(1,()=>{p=wU(out,p,types.length);for(let i=0;i<types.length;i++){const[ps,rs]=types[i];out[p++]=0x60;p=wU(out,p,ps.length);for(let j=0;j<ps.length;j++)out[p++]=ps[j];p=wU(out,p,rs.length);for(let j=0;j<rs.length;j++)out[p++]=rs[j];}});
  sec(3,()=>{p=wU(out,p,FN.length);for(let i=0;i<FN.length;i++)p=wU(out,p,fT[i]);});
  sec(5,()=>{out[p++]=1;out[p++]=0;p=wU(out,p,90);});
  sec(6,()=>{p=wU(out,p,GV.length);for(let i=0;i<GV.length;i++){out[p++]=0x7f;out[p++]=1;out[p++]=0x41;out[p++]=0;out[p++]=0x0b;}});
  const exps=[['memory',2,0],['prepareInput',0,FMAP.b],['solveRaw',0,FMAP.x],['ensureWin',0,FMAP.B],['streamInit',0,FMAP.C],['streamRefill',0,FMAP.D],['streamNext',0,FMAP.E],['getMeta',0,FMAP.F]];
  sec(7,()=>{p=wU(out,p,exps.length);for(let i=0;i<exps.length;i++){const[nm,k,id]=exps[i];p=wU(out,p,nm.length);for(let j=0;j<nm.length;j++)out[p++]=nm.charCodeAt(j);out[p++]=k;p=wU(out,p,id);}});
  out[p++]=12;out[p++]=1;out[p++]=1;

  let s='',len=0,idx=0;
  const rInt=()=>{while(idx<len&&s.charCodeAt(idx)===32)idx++;const c=s.charCodeAt(idx);if(c===37||c===35)idx++;let neg=0,v=0;if(s.charCodeAt(idx)===45){neg=1;idx++;}while(idx<len){const d=s.charCodeAt(idx);if(d<48||d>57)break;v=v*10+(d-48);idx++;}return neg?-v:v;};
  const rId=()=>{while(idx<len&&s.charCodeAt(idx)===32)idx++;if(s.charCodeAt(idx)===36)idx++;const st=idx;while(idx<len&&!BT[s.charCodeAt(idx)])idx++;return s.slice(st,idx);};
  const u=(v)=>{if(v<128)out[p++]=v;else p=wU(out,p,v);};
  const sl=(v)=>{if(v>=-64&&v<64)out[p++]=v&0x7f;else p=wS(out,p,v);};

  sec(10,()=>{
    p=wU(out,p,FN.length);
    for(let fi=0;fi<FN.length;fi++){
      const bs=p+5;p=bs;
      const ls=fL[fi];
      if(!ls)out[p++]=0;
      else{const gs=ls.split(' ');p=wU(out,p,gs.length);for(let i=0;i<gs.length;i++){const g=gs[i],c=g[g.length-1];p=wU(out,p,+g.slice(0,-1));out[p++]=c==='i'?0x7f:c==='j'?0x7e:0x7b;}}
      s=fC[fi];len=s.length;idx=0;
      while(idx<len){
        const ch=s.charCodeAt(idx);
        if(ch===32){idx++;continue;}
        if(ch===40){idx++;out[p++]=2;out[p++]=0x40;out[p++]=3;out[p++]=0x40;continue;}
        if(ch===41){idx++;out[p++]=0x0b;out[p++]=0x0b;continue;}
        if(ch===123){idx++;out[p++]=4;out[p++]=0x40;continue;}
        if(ch===91){idx++;out[p++]=4;out[p++]=0x7f;continue;}
        if(ch===63){idx++;out[p++]=0x0d;out[p++]=1;continue;}
        if(ch===59){idx++;out[p++]=0x0c;out[p++]=0;continue;}
        if(ch===44){idx++;out[p++]=0x28;out[p++]=2;out[p++]=0;continue;}
        if(ch===46){idx++;out[p++]=0x36;out[p++]=2;out[p++]=0;continue;}
        if(ch===95){idx++;out[p++]=0x41;out[p++]=2;out[p++]=0x74;out[p++]=0x6a;continue;}
        const c1=CH[ch];
        if(c1!==undefined){
          idx++;out[p++]=c1;
          if(ch===37||ch===33||ch===61)u(rInt());
          else if(ch===35)sl(rInt());
          else if(ch===36||ch===62)u(GMAP[rId()]);
          else if(ch===64)u(FMAP[rId()]);
          continue;
        }
        const st=idx;while(idx<len&&!BT[s.charCodeAt(idx)])idx++;
        const op=OP[s.slice(st,idx)];
        if(op<0x100){
          out[p++]=op;
          if(op>=0x45)continue;
          if(op===0x42)p=wS64(out,p,rInt(),rInt());
          else if(op===0x0c||op===0x0d)u(rInt());
          else if(op===0x28||op===0x36){out[p++]=2;u(rInt());}
          else if(op===0x29||op===0x2d||op===0x2f||op===0x37||op===0x3a||op===0x3b){out[p++]=0;u(rInt());}
          else if(op===2||op===3||op===4)out[p++]=TY[rId()];
          else if(op===0x3f||op===0x40)out[p++]=0;
        }else if(op<0x200){out[p++]=0x28;out[p++]=0;u(rInt());}
        else if(op<0x300){out[p++]=0xfd;out[p++]=op&0xff;if(op===0x200){out[p++]=0;u(rInt());}}
        else if(op<0x400){out[p++]=0xfc;out[p++]=op&0xff;out[p++]=0;if(op!==0x30b)out[p++]=0;}
        else if(op<=0x406){
          if(op<=0x403){out[p++]=0x23;out[p++]=GMAP[rId()];}else{out[p++]=0x20;u(rInt());}
          out[p++]=0x20;u(rInt());
          if(op===0x401){out[p++]=0x6a;out[p++]=0x2d;out[p++]=0;out[p++]=0;}
          else{
            out[p++]=0x41;out[p++]=2;out[p++]=0x74;out[p++]=0x6a;
            if(op===0x400||op===0x404){out[p++]=0x28;}
            else{if(op===0x402||op===0x405){out[p++]=0x20;u(rInt());}else{out[p++]=0x41;sl(rInt());}out[p++]=0x36;}
            out[p++]=2;out[p++]=0;
          }
        }else{const v=rInt();out[p++]=0x20;out[p++]=v;out[p++]=0x41;out[p++]=1;out[p++]=op===0x41d?0x6a:0x6b;out[p++]=0x21;out[p++]=v;}
      }
      out[p++]=0x0b;
      let bl=p-bs;for(let j=0;j<4;j++){out[bs-5+j]=(bl&0x7f)|0x80;bl>>>=7;}out[bs-1]=bl&0x7f;
    }
  });
  sec(11,()=>{out[p++]=1;out[p++]=1;p=wU(out,p,HDR.length);for(let i=0;i<HDR.length;i++)out[p++]=HDR.charCodeAt(i);});
  buildDiffWasm._bytes=out.slice(0,p);
  return new WebAssembly.Instance(new WebAssembly.Module(out.subarray(0,p)),{}).exports;
}

let wasmInst=null,memBuf=null,utf16Mod=null;
function getWasm(){if(!wasmInst){wasmInst=buildDiffWasm();memBuf=Buffer.from(wasmInst.memory.buffer);}return wasmInst;}
function getUtf16(){if(!utf16Mod)utf16Mod=require('./utf16-fallback.cjs');return utf16Mod;}
function countLinesStr(s){let c=0,p=0,l=s.length;while(p<l){const n=s.indexOf('\n',p);c++;if(n===-1)break;p=n+1;}return c;}
function diffPatch(input){
  if(input===null||typeof input!=='object'||typeof input.old!=='string'||typeof input.new!=='string')
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  const o=input.old,n=input.new,ol=o.length,nl=n.length;
  if(ol===nl&&o===n){const c=countLinesStr(o);return FORMAT+' old='+c+' new='+c+' hunks=0 deleted=0 inserted=0\n';}
  if(!/[\\"\x00-\x09\x0b\x0c\x0e-\x1f\x80-\uffff]/.test(o)&&!/[\\"\x00-\x09\x0b\x0c\x0e-\x1f\x80-\uffff]/.test(n)){
    const w=getWasm(),ro=JSON.stringify(o).slice(1,-1),rn=JSON.stringify(n).slice(1,-1);
    const nb=w.prepareInput(ro.length,rn.length);
    if(memBuf.buffer!==w.memory.buffer)memBuf=Buffer.from(w.memory.buffer);
    if(ro.length>0)memBuf.write(ro,0,ro.length,'latin1');
    if(rn.length>0)memBuf.write(rn,nb,rn.length,'latin1');
    const outLen=w.solveRaw();
    if(memBuf.buffer!==w.memory.buffer)memBuf=Buffer.from(w.memory.buffer);
    const ob=w.getMeta(0);
    return JSON.parse(memBuf.toString('latin1',ob,ob+outLen));
  }
  return getUtf16().diffPatchUtf16(o,n);
}
function readFill(fd,buf,off,max){let g=0,eof=0;while(g<max){const n=fs.readSync(fd,buf,off+g,max-g,null);if(n===0){eof=1;break;}g+=n;}return[g,eof];}
function writeAll(fd,buf,off,len){let w=0;while(w<len)w+=fs.writeSync(fd,buf,off+w,len-w);}
const WIN_BASE=256,INIT_WIN_CAP=2621440,OPEN_BR=Buffer.from('['),CLOSE_BR=Buffer.from(']');
function runCasesFile(inputPath,outputPath){
  const w=getWasm();let winCap=INIT_WIN_CAP,winLen=0,eof=0;
  const fd=fs.openSync(inputPath,'r'),outFd=fs.openSync(outputPath,'w');
  try{
    w.ensureWin(WIN_BASE+winCap);
    if(memBuf.buffer!==w.memory.buffer)memBuf=Buffer.from(w.memory.buffer);
    const[g0,e0]=readFill(fd,memBuf,WIN_BASE,winCap);winLen=g0;eof=e0;
    w.streamInit(WIN_BASE,WIN_BASE+winLen,eof,WIN_BASE+winCap);
    for(;;){
      const rc=w.streamNext();
      if(rc>0){if(memBuf.buffer!==w.memory.buffer)memBuf=Buffer.from(w.memory.buffer);writeAll(outFd,memBuf,w.getMeta(4),rc);}
      else if(rc===0){if(w.getMeta(5)===0)writeAll(outFd,OPEN_BR,0,1);writeAll(outFd,CLOSE_BR,0,1);return;}
      else if(rc===-2){
        if(eof)break;
        if(memBuf.buffer!==w.memory.buffer)memBuf=Buffer.from(w.memory.buffer);
        const keep=w.getMeta(1),rem=WIN_BASE+winLen-keep;
        if(keep===WIN_BASE&&rem>=winCap){winCap*=2;w.ensureWin(WIN_BASE+winCap);if(memBuf.buffer!==w.memory.buffer)memBuf=Buffer.from(w.memory.buffer);}
        else if(rem>0)memBuf.copyWithin(WIN_BASE,keep,WIN_BASE+winLen);
        const[g,e]=readFill(fd,memBuf,WIN_BASE+rem,winCap-rem);winLen=rem+g;eof=e;
        w.streamRefill(WIN_BASE+winLen,eof,WIN_BASE+winCap);
      }else if(rc===-3){
        if(memBuf.buffer!==w.memory.buffer)memBuf=Buffer.from(w.memory.buffer);
        const c=JSON.parse(memBuf.toString('utf8',w.getMeta(2),w.getMeta(3)));
        const chunk=Buffer.from((w.getMeta(5)===1?'[':',')+JSON.stringify(diffPatch(c.input)),'utf8');
        writeAll(outFd,chunk,0,chunk.length);
      }else break;
    }
  }finally{fs.closeSync(fd);fs.closeSync(outFd);}
  const cases=JSON.parse(fs.readFileSync(inputPath,'utf8')),answers=new Array(cases.length);
  for(let i=0;i<cases.length;i++)answers[i]=diffPatch(cases[i].input);
  fs.writeFileSync(outputPath,JSON.stringify(answers));
}
function runMain(){
  const inDir=process.env.MAKEFUN_INPUT_DIR??'/input',outDir=process.env.MAKEFUN_OUTPUT_DIR??'/output';
  runCasesFile(inDir+'/cases.json',outDir+'/answers.json');
}
module.exports=Object.assign(runMain,{FORMAT,CONTEXT,diffPatch,run:diffPatch,runCasesFile,buildDiffWasm});
