z:=2^5 + 2^34 + 2^40 + 2^45-2^58;
p:=Ceiling((z^14-4*z^13+7*z^12+683*z^8-2510*z^7+4781*z^6+117649*z^2-386569*z+823543)/28749);
r:=Ceiling((z^12+683*z^6+117649) div (7^6*37^2));
t:=Ceiling((2*z^7+757*z+259) div 259);
Fp:=GF(p);

F2<u>:=ExtensionField<Fp,u|u^2+4>;
F6<v>:=ExtensionField<F2,v|v^3-(u+1)>;
F18<w>:=ExtensionField<F6,w|w^3-v>;
F36<x>:=ExtensionField<F18,x|x^2-w>;
E:=EllipticCurve([Fp|0,2]);
E36:=EllipticCurve([F36|0,2]);

Et:=EllipticCurve([F6|0,2*v]);
h1:=(p+1-t) div r;
//h2:=#Et div r;
h2:=3569264135135314029167490670315135087775619285709711985856808686871281692048923\
2062280284636949282597128519886731329073764703315261959265621830573166593601774\
9953896966720450863654152043664428499217529152597906124196756648166896090706342\
4615188214217563701655438207011609773929185178019949177971994577525407758337116\
0738204390476391217163507471758966317354337605355407885803634693196934279920025\
3962792743285487430269834937371075826422157560356306876080807805429783716075521\
0226341249585919580620784875886489712207223176097016171470641813021189334868144\
5625629494411118246822535046330259432216948981200152363153780393585469332950891\
3911550478495876633770300949806123481051048290869882550757048485132175250420957\
3277840986318699250303451992608469888795740583291492242748801909640911982419776\
3544897521429804307563788243618832674786286317278377498942950459404642934193305\
1934517210354707186736306884649468344660274737814982955004525227129946086912243\
3489158466831553258027991984893858147631793921404257400732834660757720575798442\
4673118114654210656360914834140813125965662345088127349022823171074284664854881\
2666760996514653975025488297580560448170971906923735238312403745267077857220136\
871476960827452265563491075415350434819207281403527637;
ht:=(p^6-p^3+1) div r;
//Random(Fp)^((p-1) div 3);
/*GLV endmorphism: (x,y)->(w1*x, y)=lambda(x,y) if (x,y) in G1*/
w1:=5361864304360453800744172988000287586791354726639833049245276368405814892230532\
8148665261812480099605992988027248157849499229811271194742157614487042453353305\
0156751410025698858825254222446280427960491067421487122012375209473430637706863\
775;
lambda:=(z^6+343) div 37;

//******endmo() is the efficiently computable edmorphism $\psi$ in the paper******//
x2:=x^2;x3:=x^3;x2_inv:=1/x^2;x3_inv:=1/x^3;
function endmo(Q,i)
        R:=E36![x2_inv*Q[1],x3_inv*Q[2],1];
        R:=E36![Frobenius(R[1],Fp,i),Frobenius(R[2],Fp,i),1];
        R:=Et![x2*R[1],x3*R[2],1];
        return R;
end function;
//********************function of G1 memebrship testing*****************************//
//********************the short vector [a0, a1]=[z^6/117649,(−323*a0 −1)/37]******************//
//since -323*a0-37*a1=1, and GCD((37*a0)^2-(37*a0)*(37*a1)+(37*a1)^2, h1*r) eq r.
//we can replace a0 and a1 by 37*a0 and 37*a1, respectively. Thus we only need to check that
// [37*a0]*P= \psi((323*a0+1)*P)
a0:=(z^6 div 117649);a1:=(-323*a0 -1) div 37;
function TestG1(P)
   R0:=a0*P;
   R1:=37*R0; R2:=323*R0+P;
   R3:=E![w1*R2[1], R2[2], 1];
   if R1[1] eq R3[1] and R1[2] eq R3[2] then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;

//*********************************G2 memebrship testing***************************//
u0:=-(z-308) div 777;
function TestG2(Q)
    R0:=u0*Q; R10:=3*R0-Q;
    R5:=6*R10-Q;R8:=R5;
    R6:=R5+R10;R7:=R6+2*R10-Q;
    R4:=R7+2*R10;R3:=-R4;R2:=R3;
    R1:=R2-2*R10+Q;R11:=Q-2*R1;
    R9:=3*R7+Q;R0:=3*R10-3*R1+Q;
    
    R0:=R0+endmo(R1,1)+endmo(R2,2)+endmo(R3,3)+endmo(R4,4)+endmo(R5,5)+endmo(R6,6)+endmo(R7,7)+endmo(R8,8)+endmo(R9,9)+endmo(R10,10)+endmo(R11,11);
    if R0[3] eq 0 then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;


//********************************functional testing****************************************//

//G1:
sum:=1;
for i:=1 to 50 do
/*Generating points P1 and P2, where P1 in G1 and P2 not in G1*/
    repeat
        P1:=h1*Random(E);
        P2:=r*Random(E);
    until P1[3] eq 1 and P2[3] eq 1;
    if TestG1(P1) eq "PASS" and TestG1(P2) eq "REJECT" then
        sum:=sum*1;
    else
        sum:=0;
    end if;
end for;

if sum eq 1 then
    printf"function TestG1 is CORRECT!\n";
else 
    printf"function TestG1 is ERROR!\n";
end if; 

//G2:
sum:=1;
for i:=1 to 50 do
/*Generating points Q1 and Q2,  where Q1 in G2 and Q2 not in G2*/
    repeat
        Q1:=h2*Random(Et);
        Q2:=r*Random(Et);
    until Q1[3] eq 1 and Q2[3] eq 1;
    if TestG2(Q1) eq "PASS" and TestG2(Q2) eq "REJECT" then
        sum:=sum*1;
    else
        sum:=0;
    end if;
end for;

if sum eq 1 then
    printf"function TestG2 is CORRECT!\n";
else 
    printf"function TestG2 is ERROR!\n";
end if;