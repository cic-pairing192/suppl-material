//*VectorG1 function is used for finding out a short vector for G1 membership testing*//
function VectorG1(r,lambda, D, h1,v)
    B:=RMatrixSpace(Integers(), 2,2)![r,0,-lambda,1];
    L:= LatticeWithBasis(B);
    S:=ShortestVectors(L);
    for i:=1 to #S do
        C:=S[i];
        if GCD(C[1]^2-(D mod 2)*C[1]*C[2]+C[2]^2, h1*r) eq r then
            return C;
        end if;
    end for;
    min:=Norm(ShortestVector(L));max:=v*min;
    V:=ShortVectorsProcess(L, min, max);
    repeat
        C:=NextVector(V);
        if Norm(C) eq 0  then
            return "Please reselect the value of max";
        end if;
    until GCD(C[1]^2-(D mod 2)*C[1]*C[2]+C[2]^2, h1*r) eq r;
     return C;
end function;

//*************************************Curve parmamters*************************//


printf("BLS12-P461:\n");
z:=-2^77+2^50+2^33;
p:=(z-1)^2*(z^4-z^2+1) div 3+z;
t:=z+1;
r:=z^4-z^2+1;
h1:=(p+1-t) div r;
D:=-3;
v:=1;
lambda:=-z^2;

VectorG1(r,lambda, D, h1,v);


printf("KSS16-P330:\n");
z:=-2^34+2^27-2^23+2^20-2^11+1;
r:=(z^8+48*z^4+625) div 61250;
t:=(2*z^5+41*z+35)div 35;
p:=(z^10+2*z^9+5*z^8+48*z^6+152*z^5+240*z^4+625*z^2+2398*z+3125) div 980;
h1:=(p+1-t) div r;
D:=-4;
v:=1;
lambda:=-(z^4+24) div 7;
VectorG1(r,lambda, D, h1,v);


printf("KSS18-P348:\n");
z:=2^44+2^22-2^9+2;
x:=z div 7;
t:=(z^4+16*z+7)div 7;
r:=Ceiling((z^6+37*z^3+343)/343);
p:=Ceiling((z^8+5*z^7+7*z^6+37*z^5+188*z^4+259*z^3+343*z^2+1763*z+2401)/21);
h1:=(p+1-t);
lambda:=z^3+18;
D:=-3;
v:=1;
VectorG1(r,lambda, D, h1,v);

printf("BW13-P310:\n");
z:=-2224;
p:=1749234309176102157657582860550885176950582224007184238236721873530271444092780\
387026731606667;
r:=2143085360734996117913472445644488914854141302995428209978212956147876055499508\
01;
t:=-72424742659885778123097924206425573989051009199;
h1:=(p+1-t);
lambda:=-z^13;
D:=-3;
v:=1;
VectorG1(r,lambda, D, h1,v);



printf("BW19-P286:\n");            
z:=-145;
p:=(z+1)^2*(z^38-z^19+1)div 3-z^39;
t:=-z^20+z+1;
r:=Evaluate(CyclotomicPolynomial(114),z);
h1:=(p+1-t) div r;
lambda:=-z^19;
D:=-3;
v:=2;
VectorG1(r,lambda, D, h1,v);

printf("KSS36-P798:\n");
z:=2^5 + 2^34 + 2^40 + 2^45-2^58;
p:=(z^14-4*z^13+7*z^12+683*z^8-2510*z^7+4781*z^6+117649*z^2-386569*z+823543) div 28749;
r:=(z^12+683*z^6+117649) div (7^6*37^2);
t:=(2*z^7+757*z+259) div 259;
h1:=(p+1-t) div r;
lambda:=(z^6+343) div 37;
D:=-3;
v:=1;
VectorG1(r,lambda, D, h1,v);



printf("BW6-P761:\n");
z:=0x8508C00000000001;
r:=(z^6-2*z^5+2*z^3+z+1) div 3;
p:=(103*z^12-379*z^11+250*z^10+691*z^9-911*z^8 - 79*z^7 + 623*z^6- 640*z^5 + 274*z^4 + 763*z^3 + 73*z^2 + 254*z + 229)div 9;
t:=(13*z^6 - 23*z^5 - 9*z^4 + 35*z^3 + 10*z + 22) div 3;
h1:=(p+1-t) div r;
t:=(13*z^6 - 23*z^5 - 9*z^4 + 35*z^3 + 10*z + 22) div 3;
lambda:=z^5 - 3*z^4 + 3*z^3 - z + 1;
D:=-3;
v:=1;
VectorG1(r,lambda, D, h1,v);
