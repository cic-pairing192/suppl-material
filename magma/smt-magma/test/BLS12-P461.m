//**********************The parameters of BLS12-P461*******************************//
z:=-2^77+2^50+2^33;
p:=(z-1)^2*(z^4-z^2+1) div 3+z;
t:=z+1;
r:=z^4-z^2+1;
Fp:=GF(p);
F2<u>:=ExtensionField<Fp,u|u^2+1>;
F6<v>:=ExtensionField<F2,v|v^3-u-2>;
F12<w>:=ExtensionField<F6,w|w^2-v>;
E:=EllipticCurve([Fp|0,4]);
E12:=EllipticCurve([F12|0,4]);
Et:=EllipticCurve([F2|0,4*(2+u)]);
//h1, h2 and ht are the cofactors of G1, G2 and G2, respectively.
h1:=(p+1-t) div r;
h2:=#Et div r;
ht:=(p^4-p^2+1) div r;
w2:=w^2;w3:=w^3;w2_inv:=1/w^2;w3_inv:=1/w^3;
/*GLV endmorphism: (x,y)->(w1*x, y)*/
w1:=7880400945708837625552799996195794517320839498224072696258089854634610041561273\
1200443912142466655860687269376557054;

//******endmo() is the efficiently computable edmorphism $\psi$ in the paper******//
function endmo(Q,i)
        R:=E12![w2_inv*Q[1],w3_inv*Q[2],1];
        R:=E12![Frobenius(R[1],Fp,i),Frobenius(R[2],Fp,i),1];
        R:=Et![w2*R[1],w3*R[2],1];
        return R;
end function;

//********************function of G1 memebrship testing*****************************//
//********************************the short vector [a0, a1]=[1, -z^2]***************//

function TestG1(P)
    R0:=-z^2*P;
    R1:=E![w1*P[1], P[2],1];
    if R0[1] eq R1[1] and R0[2] eq R1[2] then 
        return "PASS";
     else 
       return "REJECT";
    end if;
end function;

//***********************function of G2 memebrship testing*************************//
//******************** the short vector is [z,-1,0,0]******************************//
function TestG2(Q)
    R0:=z*Q;
    R1:=endmo(Q,1);
    if R0[1] eq  R1[1] and R0[2] eq R1[2] then 
        return "PASS";
    else 
        return "REJECT";
    end if;
end function;
//**********************functio of GT memebrship testing***************************//
//******************** the short vector is [z,-1,0,0]******************************//
function TestGT(a)
    r0:=a^(-z);
    r1:=Frobenius(a,Fp,1);
    if r0*r1 eq 1 then 
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

//GT:
sum:=1;
for i:=1 to 100 do

/*Generating random elements a1 and a2, where a1 in GT and Q2 not in GT*/
    repeat 
        a1:=Random(F12);
        a2:=Random(F12);
        a1:=Frobenius(a1,Fp,6)/a1;
        a1:=Frobenius(a1,Fp,2)*a1;
        a1:=a1^ht;
        a2:=a2^r;
    until a1 ne 1 and a2 ne 1;

    if TestGT(a1) eq "PASS" and TestGT(a2) eq "REJECT" then
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
time_begin:=Cputime();
for i:=1 to 100 do
    R0:=-z^2*P1;
    R1:=E![w1*P1[1], P1[2],1];
end for;
T:=Cputime(time_begin);
printf"Timing of the G1 memerbship testing  is %o*10^-2\n",T;

//G2:
time_begin:=Cputime();
for i:=1 to 100 do
    R0:=z*Q1;
    R1:=endmo(Q1,1);
end for;
T:=Cputime(time_begin);

printf"Timing of the G2 memerbship testing  is %o*10^-2\n",T;

//GT:
time_begin:=Cputime();
for i:=1 to 100 do
    r0:=a1^(-z);
    r1:=Frobenius(a1,Fp,1);
end for;
T:=Cputime(time_begin);

printf"Timing of the GT memerbship testing  is %o*10^-2\n",T;
