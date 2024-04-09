z:=-145;
p:=(z+1)^2*(z^38-z^19+1)div 3-z^39;
t:=-z^20+z+1;
r:=Evaluate(CyclotomicPolynomial(114),z);
Fp:=GF(p);
F19<u>:=ExtensionField<Fp,u|u^19+u+31>;
E:=EllipticCurve([Fp|0,31]);
E19:=EllipticCurve([F19|0,31]);

/*compute the order of E(F_{p^19})*/
t2:=t^2-2*p;
t3:=t*t2-t*p;
t4:=t*t3-t2*p;
t5:=t*t4-t3*p;
t6:=t*t5-t4*p;
t7:=t*t6-t5*p;
t8:=t*t7-t6*p;
t9:=t*t8-t7*p;
t10:=t*t9-t8*p;
t11:=t*t10-t9*p;
t12:=t*t11-t10*p;
t13:=t*t12-t11*p;
t14:=t*t13-t12*p;
t15:=t*t14-t13*p;
t16:=t*t15-t14*p;
t17:=t*t16-t15*p;
t18:=t*t17-t16*p;
t19:=t*t18-t17*p;
//h1, h2 and ht are the cofactors of G1, G2 and G2, respectively.
h1:=(p+1-t) div r;
h2:=(p^19+1-t19) div (r*(p+1-t));
ht:=(p^19-1) div ((p-1)*r);

//GLV endmorphism: (x,y)->(-x, w*y)
w:=9561856609697676887108507068813558963674902373779955480974873474191350327753040\
8892292;

//*****The function TR19 maps a random point into the trace zero subgroup*****//
TR19:=function(Q)
    T:=Q;
    Q1i := Q[1];
    Q2i := Q[2];
     for i:=1 to 18 do
         Q1i := Frobenius(Q1i, Fp);
         Q2i := Frobenius(Q2i, Fp);
         T:=T+E19![Q1i,Q2i,1];
    end for;
return T;
end function;

//*********************************G1 memebrship testing***************************//
//************short vector[a0, a1]=[-(z^10-z)*(z^6-z^3+1)*(z+1),a0*z-1]************//
a0:=-(z^10-z)*(z^6-z^3+1)*(z+1);

function TestG1(P)
    R1:=a0*P;R2:=P-z*R1;
    R2:=[w*R2[1],R2[2],1];
    if R1[1] eq R2[1] and R1[2] eq R2[2] then 
        return "PASS";
    else 
        return "REJECT";
    end if;
end function;

//*********************************G2 memebrship testing***************************//
//******Checking that (1+\pi+...\pi^18)(Q)=0 and \pi(Q)=-z*(w*Q[1], Q[2])**********//
a0:=-(z^10-z)*(z^6-z^3+1)*(z+1);

function TestG2(Q)
    R0:=E19![Frobenius(Q[1],Fp,1),Frobenius(Q[2],Fp,1),1];
    R1:=R0+E19![Frobenius(Q[1],Fp,2),Frobenius(Q[2],Fp,2),1]+E19![Frobenius(Q[1],Fp,3),Frobenius(Q[2],Fp,3),1];
    R2:=E19![Frobenius(R1[1],Fp,3),Frobenius(R1[2],Fp,3),1];
    R3:=R1+R2;
    R4:=E19![Frobenius(R3[1],Fp,6),Frobenius(R3[2],Fp,6),1];
    R5:=R3+R4;
    R6:=E19![Frobenius(R4[1],Fp,6),Frobenius(R4[2],Fp,6),1];
    R7:=Q+R5+R6;
    R1:=E19![w*Q[1], Q[2]];
    R1:=-z*R1;
    if R7[3] eq 0 and R0[1] eq R1[1] and R0[2] eq R1[2] then 
        return "PASS";
    else 
        return "REJECT";
    end if;
end function;

//*********************************GT memebrship testing***************************//
//************************the short vector C=[z^2,-z,1,0...0,]*********************//
function TestGT(a)
    r0:=Frobenius(a,Fp,1);r1:=r0*Frobenius(a,Fp,2)*Frobenius(a,Fp,3);
    r2:=Frobenius(r1,Fp,3);r3:=r1*r2;
    r4:=Frobenius(r3,Fp,6);r5:=r3*r4;
    r6:=Frobenius(r4,Fp,6);
    r7:=a*r5*r6;
    r1:=a^(-z);
    r2:=r1^(-z);
    r1:=r2*Frobenius(r1,Fp,1)*Frobenius(a,Fp,2);
    if r7 eq 1 and r1 eq 1 then 
        return "PASS";
    else 
        return "REJECT";
    end if;
end function;


//********************************functional testing****************************************//
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
    repeat
        Q1:=Random(E19);
        Q1:=TR19(Q1)-19*Q1;
        Q1:=h2*Q1;
        Q2:=r*Random(E19);
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

//GT
/*Since the time of expontiation by ht is too long, we give a fixed element a1 in GT*/
a1:=3570450943411368132427555922028421756517217176140528955317750572144861117533404\
    7333085*u^18 + 547067271442280242142363379064686382717806416137488001323792\
    41211441084545762836174045*u^17 + 26676765215742733596199169134745204158691\
    439644661415826125439934650175231150116666582*u^16 +
    248500267296583379545538678044948126717964079481612252784597162427877650739\
    43203382408*u^15 + 32118208961645511823612468109686903773554609090868889218\
    788104288150738570715478802874*u^14 + 1656319721322359454675636231006510345\
    5747776075955706625253463533591740737142064803943*u^13 +
    722670809254025005292765574242989604453389880317793793682235152871828228649\
    48567282449*u^12 + 76902058074416706251567667630273140627711894336162979271\
    21677996479389049463518947880*u^11 + 35168322758782509768795905174470584952\
    86250169244825326765153129251457613133416517630*u^10 +
    332554728049663330410660821934354614669735337292750055428803083824938378333\
    12725549293*u^9 + 164751342846749297304087720381907895745169509798554146631\
    29206205430549167344714458576*u^8 + 587736609941550047657065138492292966491\
    40254262962312469028190200772835427186575779214*u^7 +
    172099454574376014542680533673903118122082191295265877441241417622851848641\
    27616197119*u^6 + 932183072722109574106467407214254436477556314099508427312\
    83135032779382464211310342576*u^5 + 840362891239573555068475922692224446557\
    54894288801077185629220474795217359885918566611*u^4 +
    964684219565540315118395035433004398512353030761442127629537154563805056217\
    2699737230*u^3 + 7536815887792192090259543732342328758508422224701663436874\
    3999502064390979136418096604*u^2 + 9189968332602972360597743327727538625535\
    6589966024197264679278802882429672558669668211*u +
    230350756350786701532016867268570711653515617643627928566461623557061242874\
    20469059924;

/*Generating random elemrnts a1 and a2, where a1 in GT and Q2 not in GT*/
sum:=1;
for i:=1 to 100 do
    repeat
        a1:=a1^i;
        a2:=Random(F19);
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
    R1:=a0*P1;R2:=P1-z*R1;
    R2:=[w*R2[1],R2[2],1];
end for;
T:=Cputime(time_begin);
printf"Timing of the G1 memerbship testing  is %o*10^-2\n",T;

//G2:

time_begin:=Cputime();
for i:=1 to 100 do
    R0:=E19![Frobenius(Q1[1],Fp,1),Frobenius(Q1[2],Fp,1),1];
    R1:=R0+E19![Frobenius(Q1[1],Fp,2),Frobenius(Q1[2],Fp,2),1]+E19![Frobenius(Q1[1],Fp,3),Frobenius(Q1[2],Fp,3),1];
    R2:=E19![Frobenius(R1[1],Fp,3),Frobenius(R1[2],Fp,3),1];
    R3:=R1+R2;
    R4:=E19![Frobenius(R3[1],Fp,6),Frobenius(R3[2],Fp,6),1];
    R5:=R3+R4;
    R6:=E19![Frobenius(R4[1],Fp,6),Frobenius(R4[2],Fp,6),1];
    R7:=Q1+R5+R6;
    R1:=E19![w*Q1[1], Q1[2]];
    R1:=-z*R1; 
end for;
T:=Cputime(time_begin);
printf"Timing of the G2 memerbship testing  is %o*10^-2\n",T;

time_begin:=Cputime();
for i:=1 to 100 do
    r0:=Frobenius(a1,Fp,1);r1:=r0*Frobenius(a1,Fp,2)*Frobenius(a1,Fp,3);
    r2:=Frobenius(r1,Fp,3);r3:=r1*r2;
    r4:=Frobenius(r3,Fp,6);r5:=r3*r4;
    r6:=Frobenius(r4,Fp,6);
    r7:=a1*r5*r6;
    r1:=a1^(-z);
    r2:=r1^(-z);   
end for;
T:=Cputime(time_begin);

printf"Timing of the GT memerbship testing  is %o*10^-2\n",T;
