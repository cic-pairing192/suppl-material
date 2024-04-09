//**********************The parameters of BW6-P761*******************************//
z:=0x8508C00000000001;
z0:=(z-1) div 3;
r:=(z^6-2*z^5+2*z^3+z+1) div 3;
p:=(103*z^12-379*z^11+250*z^10+691*z^9-911*z^8 - 79*z^7 + 623*z^6- 640*z^5 + 274*z^4 + 763*z^3 + 73*z^2 + 254*z + 229)div 9;
t:=(13*z^6 - 23*z^5 - 9*z^4 + 35*z^3 + 10*z + 22) div 3;
Fp:=GF(p);
F6<u>:=ExtensionField<Fp,u|u^6+4>;
E:=EllipticCurve([Fp|0,-1]);
E6:=EllipticCurve([F6|0,-1]);
Et:=EllipticCurve([Fp|0,4]);
h1:=(p+1-t) div r;
h2:=#Et div r;
ht:=(p^2-p+1) div r;
lambda:=z^5-3*z^4+3*z^3-z+1;

/*GLV endmorphism: (x,y)->(w*x, y)=lambda*(x,y)*/
w:=1968985824090209297278610739700577151397666382303825728450741611566800370218827\
2577508650134219372923700061758423812757439140233807275828199050212295831922074\
21122272650305267822868639090213645505120388400344940985710520836292650;
//******endmo() is the efficiently computable edmorphism $\psi$ in the paper******//
u2:=u^2;u3:=u^3;u2_inv:=1/u^2;u3_inv:=1/u^3;
function endmo(Q,i)
        R:=E6![u2_inv*Q[1],u3_inv*Q[2],1];
        R:=E6![Frobenius(R[1],Fp,i),Frobenius(R[2],Fp,i),1];
        R:=Et![u2*R[1],u3*R[2],1];
        return R;
end function;

//*******************************function of G1 memebrship testing*****************************//
//********************the short vector [a0, a1]=[z0*(z^2-2)-1, -z0*(z^2-2)-z]******************//

function TestG1(P)
    R0:=z*P;R1:=z*R0;R2:=R1-2*P;R3:=z0*R2;R4:=R3-P;R5:=R3+R0;
    R6:=E![w*R5[1], R5[2],1];
    if R4[1] eq R6[1] and R4[2] eq R6[2] then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;

//*******************************function of G2 memebrship testing*****************************//
//********************the short vector [c0, c1]=[z0*(z^2-2)+z, z0*(z^2-2)-1]*******************//
function TestG2(Q)
    R0:=z*Q;R1:=z*R0;R2:=R1-2*Q;R3:=z0*R2;R4:=R3-Q;R5:=R3+R0;
    R6:=endmo(R4,1);
    if R5[1] eq  R6[1] and R5[2] eq -R6[2] then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;

//*******************************function of GT memebrship testing*****************************//
//********************the short vector [c0, c1]=[z0*(z^2-2)+z, z0*(z^2-2)-1]*******************//
function TestGT(a)
    r0:=a^z;r1:=r0^z;r2:=r1/a^2;r3:=r2^z0;r4:=r3/a;r5:=r3*r0;
    r6:=Frobenius(r4,Fp,1);r7:=r5*r6;

    r0:=a*Frobenius(a,Fp,2);
    r1:=Frobenius(a,Fp,1);
    if r0 eq r1 and r7 eq 1 then 
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
        a1:=Random(F6);
        a2:=Random(F6);
        a1:=Frobenius(a1,Fp,3)/a1;
        a1:=Frobenius(a1,Fp,1)*a1;
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

