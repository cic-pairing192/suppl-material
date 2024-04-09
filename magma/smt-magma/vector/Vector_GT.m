//*VectorGT function is used for finding out a short vector for GT membership testing*//
function VectorGT(r,p,k,ht,v)
    u:=EulerPhi(k);
    B:=RMatrixSpace(Integers(), u,u)!0;
    B[1][1]:=r;
    for i:=2 to u do
        B[i][1]:=-p^(i-1);B[i][i]:=1;
    end for;
    L:= LatticeWithBasis(B);
    S:=ShortestVectors(L);
    for i:=1 to #S do
        C:=S[i];
        b:=0;
        for j:=1 to u do
            b:=(b+C[j]*p^(j-1));
        end for;
        htd:= b div r;
        if GCD(ht,htd) eq 1 then        
            return C;
        end if;
    end for;
    min:=Norm(ShortestVector(L));max:=v*min;
    V:=ShortVectorsProcess(L, min, max);
    repeat
        C:=NextVector(V);
        if Norm(C) eq 0 then
            return "Please reselect the value of v";
        end if;
        b:=0;
        for j:=1 to u do
            b:=(b+C[j]*p^(j-1));
        end for;
        htd:= b div r;
    until GCD(ht,htd) eq 1;
    return C;
end function;

//*************************************Curve parmamters*************************//

printf("BN-P446:\n");
z:=2^110+2^36+1;
p:=36*z^4+36*z^3+24*z^2+6*z+1;
r:=36*z^4+36*z^3+18*z^2+6*z+1;
ht:=(p^4-p^2+1) div r;
v:=1;
k:=12;
VectorGT(r,p,k,ht,v);


printf("BLS12-P461:\n");
z:=-2^77+2^50+2^33;
p:=(z-1)^2*(z^4-z^2+1) div 3+z;
r:=z^4-z^2+1;
ht:=(p^4-p^2+1) div r;
v:=1;
k:=12;
VectorGT(r,p,k,ht,v);



printf("KSS16-P330:\n");
z:=-2^34+2^27-2^23+2^20-2^11+1;
r:=(z^8+48*z^4+625) div 61250;
t:=(2*z^5+41*z+35)div 35;
p:=(z^10+2*z^9+5*z^8+48*z^6+152*z^5+240*z^4+625*z^2+2398*z+3125) div 980;
ht:=(p^8+1) div r;
v:=2;
k:=16;
VectorGT(r,p,k,ht,v);


printf("KSS18-P348:\n");
z:=2^44+2^22-2^9+2;
x:=z div 7;
r:=Ceiling((z^6+37*z^3+343)/343);
p:=Ceiling((z^8+5*z^7+7*z^6+37*z^5+188*z^4+259*z^3+343*z^2+1763*z+2401)/21);
ht:=(p^6-p^3+1) div r;
v:=1;
k:=18;
VectorGT(r,p,k,ht,v);

printf("BW13-P310:\n");
z:=-2224;
p:=1749234309176102157657582860550885176950582224007184238236721873530271444092780\
387026731606667;
r:=2143085360734996117913472445644488914854141302995428209978212956147876055499508\
01;
ht:=(p^13-1) div ((p-1)*r);
v:=1;
k:=13;
VectorGT(r,p,k,ht,v);

C:=[z^2,-z,1, 0,0,0,0,0,0,0,0,0];
sum:=0;
for i:=1 to #C do
    sum:=sum+C[i]*p^(i-1);
end for;
C:=Vector(C);
if sum mod r eq 0 then 
    printf("C1=(4946176 2224 1 0 0 0 0 0 0 0 0 0) is also a vector in the lattice:\n");
end if;
htd:=sum div r;
if GCD(ht, htd) eq 1 then
    printf("It also feasible to select the vector as C1.\n");
end if;



printf("BW19-P286:\n");            
z:=-145;
p:=(z+1)^2*(z^38-z^19+1)div 3-z^39;
r:=Evaluate(CyclotomicPolynomial(114),z);
v:=1;
k:=19;
ht:=(p^19-1) div((p-1)*r);
VectorGT(r,p,k,ht,v);
C:=[z^2,-z,1, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
sum:=0;
for i:=1 to #C do
    sum:=sum+C[i]*p^(i-1);
end for;
C:=Vector(C);
if sum mod r eq 0 then 
    printf("C1=(21025 145 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) is also a vector in the lattice:\n");
end if;
htd:=sum div r;
if GCD(ht, htd) eq 1 then
    printf("It also feasible to select the vector as C1.\n");
end if;


printf("KSS36-P798:\n");
z:=2^5 + 2^34 + 2^40 + 2^45-2^58;
p:=(z^14-4*z^13+7*z^12+683*z^8-2510*z^7+4781*z^6+117649*z^2-386569*z+823543) div 28749;
r:=(z^12+683*z^6+117649) div (7^6*37^2);
ht:=(p^12-p^6+1) div r;
v:=1;
k:=36;
VectorGT(r,p,k,ht,v);


printf("CP6-P782:\n");
r:=0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001;
p:=0x3848c4d2263babf8941fe959283d8f526663bc5d176b746af0266a7223ee72023d07830c728d80f9d78bab3596c8617\
c579252a3fb77c79c13201ad533049cfe6a399c2f764a12c4024bee135c065f4d26b7545d85c16dfd424adace79b57b942ae9;
ht:=(p^2-p+1)div r;
v:=1;
k:=6;
VectorGT(r,p,k,ht,v);


printf("BW6-P761:\n");
z:=0x8508C00000000001;
r:=(z^6-2*z^5+2*z^3+z+1) div 3;
p:=(103*z^12-379*z^11+250*z^10+691*z^9-911*z^8 - 79*z^7 + 623*z^6- 640*z^5 + 274*z^4 + 763*z^3 + 73*z^2 + 254*z + 229)div 9;
ht:=(p^2-p+1) div r;
v:=1;
k:=6;
VectorGT(r,p,k,ht,v);
