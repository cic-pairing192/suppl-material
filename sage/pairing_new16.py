"""
a new curve like the Fotiadis-Mardindale FM23 k=16 but with a square cofactor
Fotiadis 2023

k = 16
D = 1
qx = (x^16 + 2*x^13 + x^10 + 5*x^8 + 6*x^5 + x^2 + 4)/4
tx = x^8+x^5+2
rx = x^8+1
cx = (x*(x^3 + 1)/2)^2
yx = x*(x^3 + 1)
any x is fine (x = 0,1 mod 2 provides integer parameters)

Miller loop: formulas are
x + p^5 = 0 mod r
-1 + x*p^3 = 0 mod r

"""
from pairing import *

def cofactor_clearing_g1_new16(P, u):
    """
    cofactor clearing on G1.
    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed

    G1 cofactor is c1 = x^2 * (x^3 + 1)^2/4
    c1 satisfies Schoof criterion:
    P -> [u * (u^3+1)/2] * P = Q
    generic proof in ePrint 2022/352
    This is Rene Schoof Fq-rational l-torsion criterion from Proposition 3.7 in
    Schoof, R.: Nonsingular plane cubic curves over finite fields.
    Journal of Combinatorial Theory, Series A 46(2), 183–211 (1987).
    https://doi.org/10.1016/0097-3165(87)90003-3
    """
    if (u % 2) == 0:
        Q = (u * (u**3+1)//2)*P
    else:
        Q = (u * (u**3+1))*P
    return Q

def membership_testing_g1_new16(P, u, omega=None):
    """
    G1 membership testing, phi(P) = (-x, y*omega) = [-u^4]*P if P is in G1

    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed
    - `omega`: sqrt(-1) mod q, such that (-x, y*omega) has eigenvalue -u^4
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((u**12 + u**9 + 3*u**4 + u)/2)
    phiP = P.curve()((-P[0], P[1]*omega, P[2]))
    if (u % 2) == 0:
        R = P - (u**4)*phiP
    else:
        R = (u**4-1)//2 * (P - phiP) + P
        # (1+u^4)/2 * P + (1-u^4)/2*phi(P)
    return R.is_zero()

def cofactor_clearing_g2_new16_even(Q, u, Fq4, D_twist=True, case=0):
    """
    Multiply Q by the cofactor of G2, with the endomorphism psi on E' of characteristic polynomial X^2 -t*X + p
    INPUT:
    - `Q`: point in E'(Fp4) containing G2 compressed
    - `u`: curve seed
    - `Fq4`: explicit degree 4 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    G2 cofactor: h2 = 1/256*(x^56 + 8*x^53 + 28*x^50 + 19*x^48 + 56*x^47 + 136*x^45 + 70*x^44 + 420*x^42 + 56*x^41 + 147*x^40 + 728*x^39 + 28*x^38 + 920*x^37 + 770*x^36 + 8*x^35 + 2436*x^34 + 504*x^33 + 594*x^32 + 3528*x^31 + 196*x^30 + 3128*x^29 + 3010*x^28 + 40*x^27 + 6764*x^26 + 1512*x^25 + 1331*x^24 + 7656*x^23 + 420*x^22 + 5536*x^21 + 4662*x^20 + 56*x^19 + 8880*x^18 + 1096*x^17 + 1635*x^16 + 6720*x^15 - 500*x^14 + 4736*x^13 + 1808*x^12 - 488*x^11 + 4416*x^10 - 992*x^9 + 897*x^8 + 1152*x^7 - 752*x^6 + 1536*x^5 - 928*x^4 + 256*x^3 + 256*x^2 - 1024*x + 512)
    lambda mod h2 = a degree 55 polynomial

    [      (1+u^3), -u^3*(1+u^3)/2,             -u,    u*(1+u^3)/2, -u^4*(u^3+1)/2,           -u^2,  u^2*(1+u^3)/2,               1]
    [ -u*(1+u^3)/2,  u^4*(1+u^3)/2,            u^2, -u^2*(1+u^3)/2,             -1,        (1+u^3), -u^3*(1+u^3)/2,              -u]
    [u^2*(1+u^3)/2,              1,       -(u^3+1),  u^3*(1+u^3)/2,              u,   -u*(1+u^3)/2,  u^4*(1+u^3)/2,             u^2]
    [u^3*(1+u^3)/2,              u,   -u*(1+u^3)/2,  u^4*(1+u^3)/2,            u^2, -u^2*(1+u^3)/2,             -1,         (u^3+1)]
    [u^4*(1+u^3)/2,            u^2, -u^2*(1+u^3)/2,             -1,        (u^3+1), -u^3*(1+u^3)/2,             -u,     u*(1+u^3)/2]
    [            1,       -(1+u^3),  u^3*(1+u^3)/2,              u,   -u*(1+u^3)/2,  u^4*(1+u^3)/2,            u^2,  -u^2*(1+u^3)/2]
    [            u,   -u*(1+u^3)/2,  u^4*(1+u^3)/2,            u^2, -u^2*(1+u^3)/2,             -1,         (u^3+1), -u^3*(1+u^3)/2]
    [         -u^2,  u^2*(1+u^3)/2,              1,       -(u^3+1),  u^3*(1+u^3)/2,              u,    -u*(1+u^3)/2,  u^4*(1+u^3)/2]
    """
    assert (u % 2) == 0
    xi = -Fq4.modulus().constant_coefficient()
    p = Fq4.characteristic()
    mu = xi**((p-1)//4)
    mu2 = mu.frobenius()*mu
    mu3 = mu.frobenius(2)*mu2
    mu4 = mu2.frobenius(2)*mu2
    mu5 = mu4 * mu.frobenius(4)
    mu6 = mu4 * mu2.frobenius(4)
    mu7 = mu4 * mu3.frobenius(4)
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 4, 1, D_twist)
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 4, 2, D_twist)
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 4, 3, D_twist)
    psi4Q = endomorphism_g2_psi_p(Q, None, mu4, 4, 4, D_twist)
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 4, 5, D_twist)
    psi6Q = endomorphism_g2_psi_p(Q, None, mu6, 4, 6, D_twist)
    psi7Q = endomorphism_g2_psi_p(Q, None, mu7, 4, 7, D_twist)

    if case == 0:
        return         (1+u**3)*Q + -u**3*(1+u**3)//2*psi1Q +                -u*psi2Q +     u*(1+u**3)//2*psi3Q + -u**4*(u**3+1)//2*psi4Q +             -u**2*psi5Q +  u**2*(1+u**3)//2*psi6Q +                   psi7Q
    if case == 1:
        return   -u*(1+u**3)//2*Q +  u**4*(1+u**3)//2*psi1Q +              u**2*psi2Q + -u**2*(1+u**3)//2*psi3Q +                -  psi4Q +          (1+u**3)*psi5Q + -u**3*(1+u**3)//2*psi6Q +                -u*psi7Q
    if case == 2:
        return u**2*(1+u**3)//2*Q +                   psi1Q +         -(u**3+1)*psi2Q +  u**3*(1+u**3)//2*psi3Q +                 u*psi4Q +    -u*(1+u**3)//2*psi5Q +  u**4*(1+u**3)//2*psi6Q +              u**2*psi7Q
    if case == 3:
        return u**3*(1+u**3)//2*Q +                 u*psi1Q +    -u*(1+u**3)//2*psi2Q +  u**4*(1+u**3)//2*psi3Q +              u**2*psi4Q + -u**2*(1+u**3)//2*psi5Q +                -  psi6Q +          (u**3+1)*psi7Q
    if case == 4:
        return u**4*(1+u**3)//2*Q +              u**2*psi1Q + -u**2*(1+u**3)//2*psi2Q +                -  psi3Q +          (u**3+1)*psi4Q + -u**3*(1+u**3)//2*psi5Q +                -u*psi6Q +     u*(1+u**3)//2*psi7Q
    if case == 5:
        return                  Q +         -(1+u**3)*psi1Q +  u**3*(1+u**3)//2*psi2Q +                 u*psi3Q +    -u*(1+u**3)//2*psi4Q +  u**4*(1+u**3)//2*psi5Q +              u**2*psi6Q + -u**2*(1+u**3)//2*psi7Q
    if case == 6:
        return                u*Q +    -u*(1+u**3)//2*psi1Q +  u**4*(1+u**3)//2*psi2Q +              u**2*psi3Q + -u**2*(1+u**3)//2*psi4Q +                -  psi5Q +          (u**3+1)*psi6Q + -u**3*(1+u**3)//2*psi7Q
    if case == 7:
        return            -u**2*Q +  u**2*(1+u**3)//2*psi1Q +                   psi2Q +         -(u**3+1)*psi3Q +  u**3*(1+u**3)//2*psi4Q +                 u*psi5Q +    -u*(1+u**3)//2*psi6Q +  u**4*(1+u**3)//2*psi7Q

def cofactor_clearing_g2_new16_odd(Q, u, Fq4, D_twist=True, case=0):
    """
    Multiply Q by the cofactor of G2, with the endomorphism psi on E' of characteristic polynomial X^2 -t*X + p
    INPUT:
    - `Q`: point in E'(Fp4) containing G2 compressed
    - `u`: curve seed
    - `Fq4`: explicit degree 4 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    G2 cofactor: h2 = 1/128*(x^56 + 8*x^53 + 28*x^50 + 19*x^48 + 56*x^47 + 136*x^45 + 70*x^44 + 420*x^42 + 56*x^41 + 147*x^40 + 728*x^39 + 28*x^38 + 920*x^37 + 770*x^36 + 8*x^35 + 2436*x^34 + 504*x^33 + 594*x^32 + 3528*x^31 + 196*x^30 + 3128*x^29 + 3010*x^28 + 40*x^27 + 6764*x^26 + 1512*x^25 + 1331*x^24 + 7656*x^23 + 420*x^22 + 5536*x^21 + 4662*x^20 + 56*x^19 + 8880*x^18 + 1096*x^17 + 1635*x^16 + 6720*x^15 - 500*x^14 + 4736*x^13 + 1808*x^12 - 488*x^11 + 4416*x^10 - 992*x^9 + 897*x^8 + 1152*x^7 - 752*x^6 + 1536*x^5 - 928*x^4 + 256*x^3 + 256*x^2 - 1024*x + 512)
    lambda mod h2 = a degree 55 polynomial

    [  2*(1+u^3), -u^3*(1+u^3),         -2*u,    u*(1+u^3), -u^4*(u^3+1),       -2*u^2,  u^2*(1+u^3),            2]
    [ -u*(1+u^3),  u^4*(1+u^3),        2*u^2, -u^2*(1+u^3),           -2,    2*(1+u^3), -u^3*(1+u^3),         -2*u]
    [u^2*(1+u^3),            2,   -2*(u^3+1),  u^3*(1+u^3),          2*u,   -u*(1+u^3),  u^4*(1+u^3),        2*u^2]
    [u^3*(1+u^3),          2*u,   -u*(1+u^3),  u^4*(1+u^3),        2*u^2, -u^2*(1+u^3),           -2,    2*(u^3+1)]
    [u^4*(1+u^3),        2*u^2, -u^2*(1+u^3),           -2,    2*(u^3+1), -u^3*(1+u^3),         -2*u,    u*(1+u^3)]
    [          2,   -2*(1+u^3),  u^3*(1+u^3),          2*u,   -u*(1+u^3),  u^4*(1+u^3),        2*u^2, -u^2*(1+u^3)]
    [        2*u,   -u*(1+u^3),  u^4*(1+u^3),        2*u^2, -u^2*(1+u^3),           -2,    2*(u^3+1), -u^3*(1+u^3)]
    [     -2*u^2,  u^2*(1+u^3),            2,   -2*(u^3+1),  u^3*(1+u^3),          2*u,   -u*(1+u^3),  u^4*(1+u^3)]
    """
    xi = -Fq4.modulus().constant_coefficient()
    p = Fq4.characteristic()
    mu = xi**((p-1)//4)
    mu2 = mu.frobenius()*mu
    mu3 = mu.frobenius(2)*mu2
    mu4 = mu2.frobenius(2)*mu2
    mu5 = mu4 * mu.frobenius(4)
    mu6 = mu4 * mu2.frobenius(4)
    mu7 = mu4 * mu3.frobenius(4)
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 4, 1, D_twist)
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 4, 2, D_twist)
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 4, 3, D_twist)
    psi4Q = endomorphism_g2_psi_p(Q, None, mu4, 4, 4, D_twist)
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 4, 5, D_twist)
    psi6Q = endomorphism_g2_psi_p(Q, None, mu6, 4, 6, D_twist)
    psi7Q = endomorphism_g2_psi_p(Q, None, mu7, 4, 7, D_twist)

    if case == 0:
        return    2*(1+u**3)*Q + -u**3*(1+u**3)*psi1Q +           -2*u*psi2Q +     u*(1+u**3)*psi3Q + -u**4*(u**3+1)*psi4Q +        -2*u**2*psi5Q +  u**2*(1+u**3)*psi6Q +              2*psi7Q
    if case == 1:
        return   -u*(1+u**3)*Q +  u**4*(1+u**3)*psi1Q +         2*u**2*psi2Q + -u**2*(1+u**3)*psi3Q +             -2*psi4Q +     2*(1+u**3)*psi5Q + -u**3*(1+u**3)*psi6Q +           -2*u*psi7Q
    if case == 2:
        return u**2*(1+u**3)*Q +              2*psi1Q +    -2*(u**3+1)*psi2Q +  u**3*(1+u**3)*psi3Q +            2*u*psi4Q +    -u*(1+u**3)*psi5Q +  u**4*(1+u**3)*psi6Q +         2*u**2*psi7Q
    if case == 3:
        return u**3*(1+u**3)*Q +            2*u*psi1Q +    -u*(1+u**3)*psi2Q +  u**4*(1+u**3)*psi3Q +         2*u**2*psi4Q + -u**2*(1+u**3)*psi5Q +             -2*psi6Q +     2*(u**3+1)*psi7Q
    if case == 4:
        return u**4*(1+u**3)*Q +         2*u**2*psi1Q + -u**2*(1+u**3)*psi2Q +             -2*psi3Q +     2*(u**3+1)*psi4Q + -u**3*(1+u**3)*psi5Q +           -2*u*psi6Q +     u*(1+u**3)*psi7Q
    if case == 5:
        return             2*Q +    -2*(1+u**3)*psi1Q +  u**3*(1+u**3)*psi2Q +            2*u*psi3Q +    -u*(1+u**3)*psi4Q +  u**4*(1+u**3)*psi5Q +         2*u**2*psi6Q + -u**2*(1+u**3)*psi7Q
    if case == 6:
        return           2*u*Q +    -u*(1+u**3)*psi1Q +  u**4*(1+u**3)*psi2Q +         2*u**2*psi3Q + -u**2*(1+u**3)*psi4Q +             -2*psi5Q +     2*(u**3+1)*psi6Q + -u**3*(1+u**3)*psi7Q
    if case == 7:
        return       -2*u**2*Q +  u**2*(1+u**3)*psi1Q +              2*psi2Q +    -2*(u**3+1)*psi3Q +  u**3*(1+u**3)*psi4Q +            2*u*psi5Q +    -u*(1+u**3)*psi6Q +  u**4*(1+u**3)*psi7Q

def membership_testing_g2_new16(Q, u, Fq4, D_twist=True):
    """
    G2 membership testing
    INPUT:
    - `Q`: point on compressed G2 in E'(Fp4)
    - `u`: curve seed
    - `Fq4`: explicit degree 4 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    formula: -Q + psi^3(u*Q) = 0
    see membership_testing_g2_new16_alt for the other with u*Q + psi^5(Q) = 0
    """
    assert (u % 2) == 0
    xi = -Fq4.modulus().constant_coefficient()
    p = Fq4.characteristic()
    mu = xi**((p-1)//4)
    mu3 = mu * mu.frobenius() * mu.frobenius(2)

    uQ = u*Q
    psi3uQ = endomorphism_g2_psi_p(uQ, None, mu3, 4, 3, D_twist)
    return (-Q + psi3uQ).is_zero()

def membership_testing_g2_new16_odd(Q, u, Fq4, D_twist=True):
    """
    G2 membership testing
    INPUT:
    - `Q`: point on compressed G2 in E'(Fp4)
    - `u`: curve seed
    - `Fq4`: explicit degree 4 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    formula: (u-1)/2(1+q+q^2+q^3+q^4) + (u+1)/2*(q^5+q^6+q^7)
    = (u-1)/2*(1+q+q^2+q^3+q^4+q^5+q^6+q^7) + (q^5+q^6+q^7)
    """
    assert (u % 2) == 1
    xi = -Fq4.modulus().constant_coefficient()
    p = Fq4.characteristic()
    mu = xi**((p-1)//4)
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 4, 1, D_twist)
    mu2 = mu.frobenius()*mu
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 4, 2, D_twist)
    mu3 = mu.frobenius(2)*mu2
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 4, 3, D_twist)
    mu4 = mu2.frobenius(2)*mu2
    psi4Q = endomorphism_g2_psi_p(Q, None, mu4, 4, 4, D_twist)
    mu5 = mu4 * mu.frobenius(4)
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 4, 5, D_twist)
    mu6 = mu4 * mu2.frobenius(4)
    psi6Q = endomorphism_g2_psi_p(Q, None, mu6, 4, 6, D_twist)
    mu7 = mu4 * mu3.frobenius(4)
    psi7Q = endomorphism_g2_psi_p(Q, None, mu7, 4, 7, D_twist)

    return (((u-1)//2)*(Q + psi1Q + psi2Q + psi3Q + psi4Q + psi5Q + psi6Q + psi7Q) + (psi5Q + psi6Q + psi7Q)).is_zero()

def membership_testing_g2_new16_alt(Q, u, Fq4, D_twist=True):
    """
    G2 membership testing
    INPUT:
    - `Q`: point on compressed G2 in E'(Fp4)
    - `u`: curve seed
    - `Fq4`: explicit degree 4 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    formula: u*Q + psi^5(Q) = 0
    see membership_testing_g2_new16 for the other with -Q + psi^3(u*Q) = 0
    """
    assert (u % 2) == 0
    xi = -Fq4.modulus().constant_coefficient()
    p = Fq4.characteristic()
    mu = xi**((p-1)//4)
    mu2 = mu * mu.frobenius()
    mu3 = mu2 * mu.frobenius(2)
    mu5 = mu2 * mu3.frobenius(2)

    uQ = u*Q
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 4, 5, D_twist)
    return (uQ + psi5Q).is_zero()

######################## PAIRINGS ########################

def miller_loop_opt_ate_new16(Q, P, a, u):
    """Miller loop f_{u,Q}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters
    """
    m, uQ = miller_function_ate(Q, P, a, u, m0=1)

    return m

def miller_loop_opt_ate_new16_cln_b0(Q, P, a, u):
    """Miller loop f_{u,Q}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x
    - `u`: seed for curve parameters
    """
    m, uQ = miller_function_ate_cln_b0(Q, P, a, u)

    return m

def final_exp_hard_new16(f, u):
    """
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 16
    D = 1
    px = (x**16 + 2*x**13 + x**10 + 5*x**8 + 6*x**5 + x**2 + 4)/4
    rx = x**8 + 1
    tx = x**8 + x + 2
    cx = (x*(x**3 + 1))**2/4
    assert (px**8+1) % rx == 0
    exponent = (px**8+1) // rx

    ***Not claiming that this is the most efficient way to do the final expo***

    l0=(x**8 + 2*x**5 + x**2 + 4)
    l1=-(x**11 + 2*x**8 + x**5 + 4*x**3 + 4)
    l2=(x**14 + 2*x**11 + x**8 + 4*x**6 + 4*x**3)
    l3=(x**9 + 2*x**6 + x**3 + 4*x)
    l4=-(x**12 + 2*x**9 + x**6 + 4*x**4 + 4*x)
    l5=(x**15 + 2*x**12 + x**9 + 4*x**7 + 4*x**4)
    l6=(x**10 + 2*x**7 + x**4 + 4*x**2)
    l7=-(x**13 + 2*x**10 + x**7 + 4*x**5 + 4*x**2)

    l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*l7)))))) == (-4*x**5) * exponent

    # total cost for hard part: 11 M + 15 exp(u) + 3 S + 7*f16

    FIXME: it does not work with positive seeds.
    """
    u  = abs(u)
    t0 = 1
    g1 = f**u                       # f^u
    g2 = g1**u                      # f^(u^2)
    g3 = g2**u                      # f^(u^3)
    g4 = g3**u                      # f^(u^4)
    g5 = g4**u                      # f^(u^5)
    g6 = g5**u                      # f^(u^6)
    gu32 = g3**2                    # f^(2*u^3)
    f2 = f**2                       # f^2
    f4 = f2**2                      # f^4
    m1 = g6 * f                     # f^(u^6+1)
    t1 = gu32.frobenius(8)          # f^(-2*u^3)
    m2 = m1 * t1                    # f^(u^6-2*u^3+1)
    h1 = m2**u                      # f^(u^7-2*u^4+u)
    h2 = h1**u                      # f^(u^8-2*u^5+u^2)
    fl0 = h2 * f4                   # f^(u^8-2*u^5+u^2+4)
    k1 = fl0**u                     # f^(u^9-2*u^6+u^3+4*u)
    k2 = k1**u                      # f^(u^10-2*u^7+u^4+4*u^2)
    k3 = k2**u                      # f^(u^11-2*u^8+u^5+4*u^3)
    t2 = f4.frobenius(8)            # f^(-4)
    fl1 = k3 * t2                   # f^(u^11-2*u^8+u^5+4*u^3-4)
    n1 = fl1**u                     # f^(u^12-2*u^9+u^6+4*u^4-4*u)
    n2 = n1**u                      # f^(u^13-2*u^10+u^7+4*u^5-4*u^2)
    fl2 = n2**u                     # f^(u^14-2*u^11+u^8+4*u^6-4*u^3)
    fl3 = k1                        # f^(u^9-2*u^6+u^3+4*u)
    fl4 = n1                        # f^(u^12-2*u^9+u^6+4*u^4-4*u)
    fl5 = fl2**u                    # f^(u^15-2*u^12+u^9+4*u^7-4*u^4)
    fl6 = k2                        # f^(u^10-2*u^7+u^4+4*u^2)
    fl7 = n2                        # f^(u^13-2*u^10+u^7+4*u^5-4*u^2)
    fl1 = fl1.frobenius(1)          # f^(q(u^11-2*u^8+u^5+4*u^3-4))
    fl2 = fl2.frobenius(2)          # f^(q^2(u^14-2*u^11+u^8+4*u^6-4*u^3))
    fl3 = fl3.frobenius(3)          # f^(q^3(u^9-2*u^6+u^3+4*u))
    fl4 = fl4.frobenius(4)          # f^(q^4(u^12-2*u^9+u^6+4*u^4-4*u))
    fl5 = fl5.frobenius(5)          # f^(q^5(u^15-2*u^12+u^9+4*u^7-4*u^4))
    fl6 = fl6.frobenius(6)          # f^(q^6(u^10-2*u^7+u^4+4*u^2))
    fl7 = fl7.frobenius(7)          # f^(q^7(u^13-2*u^10+u^7+4*u^5-4*u^2))
    F = fl0 * fl1 * fl2 * fl6 * fl7
    G = fl3 * fl4 * fl5
    E = G.frobenius(8)
    t0 = F * E
    
    return t0

def final_exp_hard_new16_v1(m, u):
    """
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 16
    D = 1
    px = (x**16 + 2*x**13 + x**10 + 5*x**8 + 6*x**5 + x**2 + 4)/4
    rx = x**8 + 1
    tx = x**8 + x + 2
    cx = (x*(x**3 + 1))**2/4
    assert (px**8+1) % rx == 0
    exponent = (px**8+1) // rx
    q = px; u = x

    (q^2-u^2) * ((u^2/4*(u^3 + 1)^2 + 1) * (q^5 + u * (-1 + u^2 * u*q*(1 + u*q^3))) + u*q * (1 + u*q^3)) + 1 == exponent
    if u is odd, r is actually r/2, multiply the exponent by 2

    total cost: 9 M + 2 exp(u/2) + 13 exp(u) + 4 Frobenius
    """

    u_ = abs(u)
    m1 = (m**u_)**u_
    m1 = m.frobenius(2) * m1.conjugate() # m^(q^2-u^2)
    if u > 0:
        m2 = ((m1 * (m1**u).frobenius(3)).frobenius())**u # (1+u*q^3)*u*q
    else:
        m2 = ((m1.conjugate() * (m1**u_).frobenius(3)).frobenius())**u_
                                         # m2 = m1^(|u|*q*(-1 + |u|*q^3))
    m3 = (m2**u_)**u_
    if u > 0:
        m1 = (m3 * m1.conjugate())**u * m1.frobenius(5)
    else:
        m1 = (m3.conjugate() * m1)**u_ * m1.frobenius(5)
                                         # m1 = m1^q^5 * (m2^u^2 * m1^-1)^u
    if (u % 2) == 0:
        if u > 0:
            m3 = ((m1**u)**u)**u * m1
            m3 = ((m3**u)**u)**u * m3
        else:
            m3 = ((m1**u_)**u_)**u_ * m1.conjugate()
            m3 = ((m3**u_)**u_)**u_ * m3.conjugate()
        u2 = u_//2
        m1 = m1 * (m3**u2)**u2
    else:
        u3 = abs(u**3+1)//2
        m3 = (m1**u3)**u3
        m3 = (m3**u_)**u_
        m1 = m1 * m3
    m1 = m1 * m2
    m1 = m1 * m
    if (u % 2) == 1:
        m1 = m1**2
    return m1

def final_exp_hard_new16_v2(m, u):
    """
    Phi_16(q)/r =
    (q^2-u^2) * ((u^2/4*(u^3+1)^2 +1) * (q^5 + u*(-1 + u^2 * u*q*(1+u*q^3))) + u*q * (1+u*q^3)) + 1
    where c = (u*(u^3 + 1)/2)^2 is g1 cofactor

    if u is odd, r is actually r/2, multiply the exponent by 2
    """
    u_ = abs(u)
    if u > 0:
        m1 = m * (m**u_).frobenius(3)             # 1 + u*q^3
        m1 = (m1**u_).frobenius()                 # u*q * (1+u*q^3)
    else:
        m1 = m.conjugate() * (m**u_).frobenius(3) # -1 + |u|*q^3
        m1 = (m1**u_).frobenius()                 # |u|*q * (-1 + |u|*q^3)

    m2 = m.conjugate() * (m1**u_)**u_             # -1 + u^2 * ...
    m2 = m2**u_
    if u < 0:
        m2 = m2.conjugate()
    m2 = m.frobenius(5) * m2

    # (u^2/4*(u^3+1)^2 +1)
    if (u_ % 2) == 0:
        u2 = u_//2
        m3 = (m2**u2)**u2
        if u < 0:
            m3 = ((m3**u_)**u_)**u_ * m3.conjugate()
            m3 = ((m3**u_)**u_)**u_ * m3.conjugate()
        else:
            m3 = ((m3**u_)**u_)**u_ * m3
            m3 = ((m3**u_)**u_)**u_ * m3
    else: # (u^3+1) is even, (u^3+1) = (u+1)*(u^2-u+1) = (u+1)*(u*(u-1)+1)
        m3 = (m2**u_)**u_                         # u^2
        u3 = abs((u**3+1)//2)
        m3 = (m3**u3)**u3                         # (u^3+1)^2/4
    m2 = m3 * m2

    m2 = m1 * m2
    # (q^2-u^2)
    m2 = m2.frobenius(2) * ((m2**u_)**u_).conjugate()

    m2 = m2 * m
    if (u % 2) == 1:
        m2 = m2**2
    return m2
