//**********************The parameters of  KSS18-P348*******************************//
z:=2^44+2^22-2^9+2;
x:=z div 7;
r:=Ceiling((z^6+37*z^3+343)/343);
t:=(z^4+16*z+7)div 7;
p:=Ceiling((z^8+5*z^7+7*z^6+37*z^5+188*z^4+259*z^3+343*z^2+1763*z+2401)/21);
f:=29*17628883*2609815993167423713*17092188708684442834305509;
s:=5444521764485075480836860980926216661018;
w:=4368577123740566675106566649785592356161010496818595952740538619772484275351318\
19717017676708913034748308;
Fp:=GF(p);
F3<u>:=ExtensionField<Fp,u|u^3+7>;
F6<v>:=ExtensionField<F3,v|v^2-u>;
F18<w>:=ExtensionField<F6,w|w^3-v>;
E:=EllipticCurve([Fp|0,3]);
E18:=EllipticCurve([F18|0,3]);
Et:=EllipticCurve([F3|0,3/u]);
//h1, h2 and ht are the cofactors of G1, G2 and G2, respectively.
h1:=(p+1-t) div r;
/*h2=#Et div r*/
h2:=9647053017183846247407587346851852477723302252014897837190815463447679093245699\
8094365283840474439301860519260707034829445465602656195359034273574581783622598\
6671906536019818492436310427263288984126762401815333515288862503156572441242623;
ht:= (p^6-p^3+1) div r;


/*GLV endmorphism: (x,y)->(w1*x, y)*/
w1:=4368577123740566675106566649785592356161010496818595952740538619772484275351318\
19717017676708913034748308;

//******endmo() is the efficiently computable edmorphism $\psi$ in the paper******//
w2:=w^2;w3:=w^3;w2_inv:=1/w^2;w3_inv:=1/w^3;

function endmo(Q,i)
        R:=E18![w2*Q[1],w3*Q[2],1];
        R:=E12![Frobenius(R[1],Fp,i),Frobenius(R[2],Fp,i),1];
        R:=Et![w2_inv*R[1],w3_inv*R[2],1];
        return R;
end function;

//********************function of G1 memebrship testing*****************************//
//********************the short vector [a0, a1]=[(z/7)^3, -18a0-1]******************//
a0:=(z  div 7)^3;
function TestG1(P)
    R0:=a0*P;
    R1:=(18*R0+P);
    R1:=E![w1*R1[1], R1[2],1];
    if R0[1] eq R1[1] and R0[2] eq R1[2] then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;
/*u=z div 7 is a paramemter used for G2 ans GT membership testing*/
u:=z div 7;

//*********************************G2 memebrship testing***************************//
//********************the short vector C=[2z/7,1,0,z/7,0,0]************************//
function TestG2(Q)
    R0:=u*Q;
    R1:=2*R0;
    R0:=endmo(Q,1)+endmo(R0,3);
    if R0[1] eq  R1[1] and R0[2] eq -R1[2] then 
        return "PASS";
    else 
       return "REJECT";
    end if;
end function;


//*********************************GT memebrship testing***************************//
//********************the short vector C=[2z/7,1,0,z/7,0,0]************************//
function TestGT(a)
    r0:=a^u;
    r1:=r0^2;
    r0:=r1*Frobenius(a,Fp,1)*Frobenius(r0,Fp,3);
    r2:=Frobenius(a,Fp,6)*a;
    r3:=Frobenius(a,Fp,3);
    if r0 eq 1 and r2 eq r3 then 
         return "PASS";
    else 
       return "REJECT";
    end if;
end function;

/*Generating points P1 and P2, where P1 in G1 and P2 not in G1*/
repeat
P1:=h1*Random(E);
P2:=r*Random(E);
until P1[3] eq 1 and P2[3] eq 1;

/*Generating points Q1 and Q2,  where Q1 in G2 and Q2 not in G2*/
repeat
    Q1:=h2*Random(Et);
    Q2:=r*Random(Et);
until Q1[3] eq 1 and Q2[3] eq 1;

/*Generating random elemrnts a1 and a2, where a1 in GT and Q2 not in GT*/
repeat 
    a1:=Random(F18);
    a2:=Random(F18);
    a1:=Frobenius(a1,Fp,9)/a1;
    a1:=Frobenius(a1,Fp,3)*a1;
    a1:=a1^ht;
    a2:=a2^r;
until a1 ne 1 and a2 ne 1;
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
        a1:=Random(F18);
        a2:=Random(F18);
        a1:=Frobenius(a1,Fp,9)/a1;
        a1:=Frobenius(a1,Fp,3)*a1;
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
//G1:
time_begin:=Cputime();
for i:=1 to 100 do
    R0:=a0*P1;
    R1:=(18*R0+P1);
    R1:=E![w1*R1[1], R1[2],1];
end for;
T:=Cputime(time_begin);
printf"Timing of the G1 memerbship testing  is %o*10^-2\n",T;

//G2:

time_begin:=Cputime();
for i:=1 to 100 do
    R0:=u*Q1;
    R1:=2*R0;
    R0:=endmo(Q1,1)+endmo(R0,3);
end for;
T:=Cputime(time_begin);
printf"Timing of the G2 memerbship testing  is %o*10^-2\n",T;

//GT:
time_begin:=Cputime();
for i:=1 to 100 do
    r0:=a1^u;
    r1:=r0^2;
    r0:=r1*Frobenius(a1,Fp,1)*Frobenius(r0,Fp,3);
    r2:=Frobenius(a1,Fp,6)*a1;
    r3:=Frobenius(a1,Fp,3);
end for;
T:=Cputime(time_begin);

printf"Timing of the GT memerbship testing  is %o*10^-2\n",T;
