//**********************The parameters of KSS16-P330*******************************//
z:=2^78-2^76-2^28+2^14+2^7+1;
r:=(z^8+48*z^4+625) div 61250;
t:=(2*z^5+41*z+35)div 35;
p:=(z^10+2*z^9+5*z^8+48*z^6+152*z^5+240*z^4+625*z^2+2398*z+3125) div 980;
Fp:=GF(p);
F4<u>:=ExtensionField<Fp,u|u^4+2>;
F8<v>:=ExtensionField<F4,v|v^2-u>;
F16<w>:=ExtensionField<F8,w|w^2-v>;
E:=EllipticCurve([Fp|1,0]);
E16:=EllipticCurve([F16|1,0]);
Et:=EllipticCurve([F4|u,0]);
w2:=w^2;w3:=w^3;w2_inv:=1/w^2;w3_inv:=1/w^3;
//GLV endmorphism: (x,y)->(-x, w1*y)
w1:=Sqrt(Fp!-1);
//h1, h2 and ht are the cofactors of G1, G2 and G2, respectively.
h1:=(p+1-t) div r;
h2:=#Et div r;
ht:=(p^8+1) div r;

//******endmo() is the efficiently computable edmorphism $\psi$ in the paper******//
function endmo(Q,i)
        R:=Q;
        for t:=1 to i do
        R:=E16![R[1]/w2,R[2]/w3,1];
        R:=E16![Frobenius(R[1], Fp),Frobenius(R[2], Fp),1];
        R:=Et![w2*R[1],w3*R[2],1];
        end for;
        return R;
end function;

//********************function of G1 memebrship testing*****************************//
//********short vector [a0, a1]=[(31z^4+625)/8750, -(17x^4+625)/8750]***************//
//****************we use [17a0, 17a1] in this testing*******************************//

a1:=-(17*z^4+625) div 8750;

function TestG1(P)
    R:=a1*P;
    R2:=2*R;R4:=2*R2;R8:=2*R4;R16:=2*R8;R17:=R16+R;R32:=2*R16;R31:=R32-R;
    R:=E![-R17[1], w1*R17[2],1]-R31;
    if R[1] eq P[1] and R[2] eq P[2] then 
 return "PASS";
     else 
       return "REJECT";
    end if;
end function;

//******************************function of G2 memebrship testing********************//
//*******short vector [c0,c1,..,c7]， where c6=(-z-25)/70, c2=c3=3c6+1,c1=-3c2,******//
//*************c5=2c2+c6+1,c4=-2c5+c6+1,c0=c_7=2c6-c1+1******************************//

u:=(z-25) div 70;
c6:=u;c2:=3*c6+1;c1:=-3*c2;c5:=2*c2+c6+1;c4:=-2*c5+c6+1;c0:=2*c6-c1+1;
c6:=u;c2:=3*c6+1;c1:=3*c2;c5:=-(2*c2+c6+1);c4:=2*c5+c6+1;c0:=2*c6+c1+1;

function TestG2(Q)
    R6:=u*Q;T1:=R6+Q;T2:=T1+R6;
    R3:=-(R6+T2);R2:=-R3;T3:=2*R2;
    R1:=T3+R2;
    R5:=-(T1+T3);
    R4:=T1+2*R5;
    R0:=T2+R1;
    R7:=-endmo(R0,7);
    R0:=R0+endmo(R1,1)+endmo(R2,2)+endmo(R3,3)+endmo(R4,4)+endmo(R5,5)+endmo(R6,6);
    if R0[1] eq  R7[1] and R0[2] eq -R7[2] then
       return "PASS";
     else 
       return "REJECT";
    end if;
end function;


//********************************functional testing****************************************//
//G1:
sum:=1;
for i:=1 to 100 do
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
for i:=1 to 100 do
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



//************************************benchmarking results****************************//
//G1:
P:=Random(E);
time_begin:=Cputime();
for i:=1 to 100 do
    R:=a1*P;
    R2:=2*R;R4:=2*R2;R8:=2*R4;R16:=2*R8;R17:=R16+R;R32:=2*R16;R31:=R32-R;
    R:=E![-R17[1], w1*R17[2],1]-R31;
end for;
T:=Cputime(time_begin);
printf"Timing of the G1 memerbship testing  is %o*10^-2\n",T;

//G2:
Q:=Random(Et);
time_begin:=Cputime();
for i:=1 to 100 do
    R6:=u*Q;T1:=R6+Q;T2:=T1+R6;
    R3:=R6+T2;R2:=R3;T3:=2*R2;
    R1:=-T3-R2;
    R5:=T1+T3;
    R4:=T1-2*R5;
    R0:=T2-R1;
    R7:=endmo(R0,7);
    R0:=R0+endmo(R1,1)+endmo(R2,2)+endmo(R3,3)+endmo(R4,4)+endmo(R5,5)+endmo(R6,6);
end for;
T:=Cputime(time_begin);

printf"Timing of the G2 memerbship testing  is %o*10^-2\n",T;
