z :=0x8508C00000000001;
z0:=(z-1) div 3;
r:=(z-1)^2*(z^4-z^2+1) div 3+z;
p:=0x3848c4d2263babf8941fe959283d8f526663bc5d176b746af0266a7223ee72023d07830c728d80f9d78bab3596c8617\
c579252a3fb77c79c13201ad533049cfe6a399c2f764a12c4024bee135c065f4d26b7545d85c16dfd424adace79b57b942ae9;
a:=5;
b:=177643151186516790382863290692950915068014681181467126498863360455358080553612741484667721912433055\
283128432363477772602471389343368505482431515345387347241915059533414034630400675716522612293083333920\
40104884438208594329793895206056414;
t:=0xcda91b419cd3f63a81dba4eb8fc81231d84f4491c1e1a4dfaf393e5c14beec4affbc93fba900003f8fbe3c000000007a6;
Fp:=GF(p);
F3<u>:=ExtensionField<Fp,u|u^3+13>;
F6<v>:=ExtensionField<F3,v|v^2-u>;
E:=EllipticCurve([Fp|a,b]);
E6:=EllipticCurve([F6|a,b]);
Et:=EllipticCurve([F3|a/u^2,b/u^3]);

t2:=t^2-2*p;
t3:=t*t2-t*p;
h2:=(p^3+1+t3)div r;
ht:=(p^2-p+1) div r;

//******endmo() is the efficiently computable edmorphism $\psi$ in the paper******//
v2:=v^2;v3:=v^3;v2_inv:=1/v^2;v3_inv:=1/v^3;

function endmo(Q,i)
        R:=E6![v2*Q[1],v3*Q[2],1];
        R:=E6![Frobenius(R[1],Fp,i),Frobenius(R[2],Fp,i),1];
        R:=Et![v2_inv*R[1],v3_inv*R[2],1];
        return R;
end function;

//*********************************G2 memebrship testing***************************//
//********************the short vector C=[2*z0*(z^2-2)+z-1, -z0*(z^2-2)+1]************************//
c0:=2*z0*(z^2-2)+z-1;
c1:=-z0*(z^2-2)+1;
function TestG2(Q)
   R0:=z*Q;R1:=z*R0-2*Q;R2:=z0*R1;
    R3:=2*R2+R0-Q; R4:=R2-Q;
    R5:=endmo(R4, 1);
    if R3[1] eq  R5[1] and R3[2] eq R5[2] then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;

//*********************************GT memebrship testing***************************//
//********************the short vector C=[z0*(z^2-2)-1, (z0*(z^2-2)-1)+z]************************//
c0:=z0*(z^2-2)-1;
c1:=z0*(z^2-2)+z;


function TestGT(a)
    b0:=Frobenius(a,Fp,2)*a;
    b1:=Frobenius(a,Fp,1);
    a0:=a^z; a1:=a0^z/a^2; a2:= a1^z0;
    a3:=a2/a;a4:=a2*a0;
    a5:=Frobenius(a4,Fp,1);
    
   
    if b0 eq  b1 and a3*a5 eq 1 then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;
//********************************functional testing****************************************//


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



//GT:
sum:=1;
for i:=1 to 50 do

/*Generating random elements a1 and a2, where a1 in GT and a2 not in GT*/
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
