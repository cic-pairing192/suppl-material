//**********************The parameters of BN-P446*******************************//
z:=2^110+2^36+1;
p:=36*z^4+36*z^3+24*z^2+6*z+1;
r:=36*z^4+36*z^3+18*z^2+6*z+1;
t:=6*z^2+1;
Fp:=GF(p);
F2<u>:=ExtensionField<Fp,u|u^2+1>;
F6<v>:=ExtensionField<F2,v|v^3-(u+5)>;
F12<w>:=ExtensionField<F6,w|w^2-v>;
E:=EllipticCurve([Fp|0,257]);
E12:=EllipticCurve([F12|0,257]);
Et:=EllipticCurve([F2|0,257*(u+5)]);
//h2 and ht are the cofactors of G2 and GT, respectively.
h2:=#Et div r;
ht:=(p^4-p^2+1) div r;

//******endmo() is the efficiently computable edmorphism $\psi$ in the paper******//
w2:=w^2;w3:=w^3;w2_inv:=1/w^2;w3_inv:=1/w^3;

function endmo(Q,i)
        R:=E12![w2_inv*Q[1],w3_inv*Q[2],1];
        R:=E12![Frobenius(R[1],Fp,i),Frobenius(R[2],Fp,i),1];
        R:=Et![w2*R[1],w3*R[2],1];
        return R;
end function;


//******************************function of G2 memebrship testing********************//
//***********************************the short vector [z+1, z,z,-2z]*********************//
function TestG2(Q)
    R0:=z*Q;
    R1:=R0+Q;
    R2:=2*R0;
    R2:=endmo(R2, 3);
    R0:=R1+endmo(R0, 1)+endmo(R0, 2);
    if R0[1] eq  R2[1] and R0[2] eq R2[2] then 
        return "PASS";
    else 
        return "REJECT";
    end if;
end function;

//*********************function of GT memebrship testing ***************************//
//********************************the short vector [z+1, z,z,-2z]]**********************//
function TestGT(a)
    r0:=a^z;
    r1:=r0*a;
    r2:=r0^2;
    r2:=Frobenius(r2,Fp,3);
    r0:=r1*Frobenius(r0,Fp,1)*Frobenius(r0,Fp,2);
    if r0 eq r2 then 
        return "PASS";
    else 
        return "REJECT";
    end if;
end function;

//********************************functional testing****************************************//

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
    printf"function TestGT is CORRECT!\n";
else 
    printf"function TestGT is ERROR!\n";
end if;
    
//************************************benchmarking results****************************//

//G2:
time_begin:=Cputime();
for i:=1 to 100 do
    R0:=z*Q1;
    R1:=R0+Q1;
    R2:=2*R0;
    R2:=endmo(R2, 3);
    R0:=R1+endmo(R0, 1)+endmo(R0, 2);
end for;
T:=Cputime(time_begin);
printf"Timing of the G2 memerbship testing  is %o*10^-2\n",T;

time_begin:=Cputime();
for i:=1 to 100 do
    r0:=a1^z;
    r1:=r0*a1;
    r2:=r0^2;
    r2:=Frobenius(r2,Fp,3);
    r0:=r1*Frobenius(r0,Fp,1)*Frobenius(r0,Fp,2);
end for;
T:=Cputime(time_begin);

printf"Timing of the GT memerbship testing  is %o*10^-2\n",T;



