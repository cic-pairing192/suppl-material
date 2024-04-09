"""
Fotiadis-Martindale curve FM23 k=16

k = 16
D = 1
qx = (x^16+x^10+5*x^8+x^2+4*x+4)/4
tx = x^8+x+2
rx = x^8+1
cx = x^2*(x^6 + 1)/4
yx = (x-1)*x^4

any x gives integer parameters, however
x=0 mod 2 is required, otherwise qx is even

Miller loop: formula is x - p = 0 mod r
"""
from pairing import *

def cofactor_clearing_g1_fm16(P, u, omega=None):
    """
    cofactor clearing with endomorphism on G1
    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed, u = 0 mod 2
    - `omega`: sqrt(-1) mod q

    G1 cofactor is c1 = x^2/4 * (x^6 + 1)
    first part because of Schoof criterion:
    P -> (u//2)*P = Q
    second part with endomorphism:
    Q -> Q + [u^3]*phi(Q)
    generic proof in ePrint 2022/352
    This is Rene Schoof Fq-rational l-torsion criterion from Proposition 3.7 in
    Schoof, R.: Nonsingular plane cubic curves over finite fields.
    Journal of Combinatorial Theory, Series A 46(2), 183–211 (1987).
    https://doi.org/10.1016/0097-3165(87)90003-3
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((x**15 + 2*x**14 + 4*x**12 - 4*x**11 - 4*x**10 - 3*x**9 - 2*x**8 + x**7 + 10*x**6 - 8*x**5 + 12*x**4 - 12*x**3 - 12*x**2 - 11*x - 6)/16)

    Q = (u//2)*P
    phiQ = P.curve()([-Q[0], Q[1]*omega, Q[2]])
    return Q + (u**3)*phiQ

def membership_testing_g1_fm16(P, u, omega=None):
    """
    G1 membership testing, phi(P) = (-x, y*omega) = [-u^4]*P if P is in G1

    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed
    - `omega`: sqrt(-1) mod q, such that (-x, y*omega) has eigenvalue -u^4
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = (Fp(u**15 + 2*u**14 + 4*u**12 - 4*u**11 - 4*u**10 - 3*u**9 - 2*u**8 + u**7 + 10*u**6 - 8*u**5 + 12*u**4 - 12*u**3 - 12*u**2 - 11*u - 6))/16
    phiP = P.curve()((-P[0], P[1]*omega, P[2]))
    return (P - (u**4)*phiP).is_zero()

def cofactor_clearing_g2_fm16_even(Q, u, Fq4, D_twist=True, case=0):
    """
    Multiply Q by the cofactor of G2, with the endomorphism psi on E' of characteristic polynomial X^2 -t*X + p
    INPUT:
    - `Q`: point in E'(Fp4) containing G2 compressed
    - `u`: curve seed, even
    - `Fq4`: explicit degree 4 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    G2 cofactor h2 = 1/256*(x^56 + 8*x^53 + 28*x^50 + 19*x^48 + 56*x^47 + 136*x^45 + 70*x^44 + 420*x^42 + 56*x^41 + 147*x^40 + 728*x^39 + 28*x^38 + 920*x^37 + 770*x^36 + 8*x^35 + 2436*x^34 + 504*x^33 + 594*x^32 + 3528*x^31 + 196*x^30 + 3128*x^29 + 3010*x^28 + 40*x^27 + 6764*x^26 + 1512*x^25 + 1331*x^24 + 7656*x^23 + 420*x^22 + 5536*x^21 + 4662*x^20 + 56*x^19 + 8880*x^18 + 1096*x^17 + 1635*x^16 + 6720*x^15 - 500*x^14 + 4736*x^13 + 1808*x^12 - 488*x^11 + 4416*x^10 - 992*x^9 + 897*x^8 + 1152*x^7 - 752*x^6 + 1536*x^5 - 928*x^4 + 256*x^3 + 256*x^2 - 1024*x + 512)
    lambda mod h2 = a degree 55 polynomial
    [  (x^7+2)/2,       x^6/2,       x^5/2,        x^4/2,  x^3*(2-x)/2, x^2*(2-x)/2,   x*(2-x)/2,     (2-x)/2]
    [    (x-2)/2,   (x^7+2)/2,       x^6/2,        x^5/2,        x^4/2, x^3*(2-x)/2, x^2*(2-x)/2,   x*(2-x)/2]
    [  x*(x-2)/2,     (x-2)/2,   (x^7+2)/2,        x^6/2,        x^5/2,       x^4/2, x^3*(2-x)/2, x^2*(2-x)/2]
    [x^2*(x-2)/2,   x*(x-2)/2,     (x-2)/2,    (x^7+2)/2,        x^6/2,       x^5/2,       x^4/2, x^3*(2-x)/2]
    [x^3*(x-2)/2, x^2*(x-2)/2,   x*(x-2)/2,      (x-2)/2,    (x^7+2)/2,       x^6/2,       x^5/2,       x^4/2]
    [     -x^4/2, x^3*(x-2)/2, x^2*(x-2)/2,    x*(x-2)/2,      (x-2)/2,   (x^7+2)/2,       x^6/2,       x^5/2]
    [     -x^5/2,      -x^4/2, x^3*(x-2)/2,  x^2*(x-2)/2,    x*(x-2)/2,     (x-2)/2,   (x^7+2)/2,       x^6/2]
    [      x^6/2,       x^5/2,       x^4/2, -x^3*(x-2)/2, -x^2*(x-2)/2,  -x*(x-2)/2,    -(x-2)/2,  -(x^7+2)/2]
    this matrix has determinant -c2 (the order of the cofactor)
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
        return   (u**7+2)//2*Q +       u**6//2*psi1Q +       u**5//2*psi2Q +        u**4//2*psi3Q +  u**3*(2-u)//2*psi4Q + u**2*(2-u)//2*psi5Q +    u*(2-u)//2*psi6Q +      (2-u)//2*psi7Q
    if case == 1:
        return      (u-2)//2*Q +   (u**7+2)//2*psi1Q +       u**6//2*psi2Q +        u**5//2*psi3Q +        u**4//2*psi4Q + u**3*(2-u)//2*psi5Q + u**2*(2-u)//2*psi6Q +    u*(2-u)//2*psi7Q
    if case == 2:
        return    u*(u-2)//2*Q +      (u-2)//2*psi1Q +   (u**7+2)//2*psi2Q +        u**6//2*psi3Q +        u**5//2*psi4Q +       u**4//2*psi5Q + u**3*(2-u)//2*psi6Q + u**2*(2-u)//2*psi7Q
    if case == 3:
        return u**2*(u-2)//2*Q +    u*(u-2)//2*psi1Q +      (u-2)//2*psi2Q +    (u**7+2)//2*psi3Q +        u**6//2*psi4Q +       u**5//2*psi5Q +       u**4//2*psi6Q + u**3*(2-u)//2*psi7Q
    if case == 4:
        return u**3*(u-2)//2*Q + u**2*(u-2)//2*psi1Q +    u*(u-2)//2*psi2Q +       (u-2)//2*psi3Q +    (u**7+2)//2*psi4Q +       u**6//2*psi5Q +       u**5//2*psi6Q +       u**4//2*psi7Q
    if case == 5:
        return      -u**4//2*Q + u**3*(u-2)//2*psi1Q + u**2*(u-2)//2*psi2Q +     u*(u-2)//2*psi3Q +       (u-2)//2*psi4Q +   (u**7+2)//2*psi5Q +       u**6//2*psi6Q +       u**5//2*psi7Q
    if case == 6:
        return      -u**5//2*Q +      -u**4//2*psi1Q + u**3*(u-2)//2*psi2Q +  u**2*(u-2)//2*psi3Q +     u*(u-2)//2*psi4Q +      (u-2)//2*psi5Q +   (u**7+2)//2*psi6Q +       u**6//2*psi7Q
    if case == 7:
        return       u**6//2*Q +       u**5//2*psi1Q +       u**4//2*psi2Q + -u**3*(u-2)//2*psi3Q + -u**2*(u-2)//2*psi4Q +   -u*(u-2)//2*psi5Q +     -(u-2)//2*psi6Q +  -(u**7+2)//2*psi7Q

def membership_testing_g2_fm16(Q, u, Fq4, D_twist=True):
    """
    G2 membership testing
    INPUT:
    - `Q`: point on compressed G2 in E'(Fp4)
    - `u`: curve seed
    - `Fq4`: explicit degree 4 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    formula: u*Q - psi(Q) = 0
    """
    xi = -Fq4.modulus().constant_coefficient()
    p = Fq4.characteristic()
    mu = xi**((p-1)//4)

    uQ = u*Q
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 4, 1, D_twist)
    return (uQ - psi1Q).is_zero()

######################## PAIRINGS ########################

def miller_loop_opt_ate_fm16(Q, P, a, u):
    """Miller loop f_{u,Q}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters
    """
    m, uQ = miller_function_ate(Q, P, a, u, m0=1)

    return m

def miller_loop_opt_ate_fm16_cln_b0(Q, P, a, u):
    """Miller loop f_{u,Q}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x
    - `u`: seed for curve parameters
    """
    m, uQ = miller_function_ate_cln_b0(Q, P, a, u)

    return m

def final_exp_hard_fm16_v1(m, u):
    """
    Phi_16(q)/r = (u^2/4*(u^6+1)+1)*(q + u)*(q^2 + u^2)*(q^4 + u^4) + 1
    where x^2*(x^6 + 1)/4 + 1 = c + 1 (c is g1 cofactor)
    cost 13 exp(|u|) + 2 exp(|u/2|) + 6 M + 3f (+ 1 conj if u < 0)
    note that u is even
    """
    #q = m.parent().characteristic()
    u_ = abs(u)
    m1 = (((m**u_)**u_)**u_)**u_ * m.frobenius(4)  # q^4 + u^4
    m1 = (m1**u_)**u_ * m1.frobenius(2)            # q^2 + u^2
    if u < 0:
        m1 = (m1**u_).conjugate() * m1.frobenius() # q + u
    else:
        m1 = m1**u_ * m1.frobenius()
    u2 = u_//2
    m2 = (m1**u2)**u2                              # u^2/4
    m2 = (((((m2**u_)**u_)**u_)**u_)**u_)**u_ * m2 # u^6+1
    m1 = m2 * m1                                   # u^2/4 * (u^6+1) + 1
    return m1 * m

def final_exp_hard_fm16(f, u, u2):
    """
    k = 16
    D = 1
    px = (x**16 + x**10 + 5*x**8+ x**2 + 4*x + 4)/4
    rx = x**8 + 1
    tx = x**8 + x + 2
    cx = (x**8 + x**2)/4
    assert ((px^8+1) % rx) == 0
    exponent = (px^8+1) // rx

    ***Not claiming that this is the most efficient way to do the final expo***

    l0=(4+4*x**7+x**9+x**15)/4
    l1=(4*x**6+x**8+x**14)/4
    l2=(4*x**5+x**7+x**13)/4
    l3=(4*x**4+x**6+x**12)/4
    l4=(4*x**3+x**5+x**11)/4
    l5=(4*x**2+x**4+x**10)/4
    l6=(4*x+x**3+x**9)/4
    l7=(4+x**2+x**8)/4

    l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*l7)))))) == exponent

    # total cost for hard part: 10 M + 2 exp(u/2) + 13 exp(u) + 7*f16
    """
    t0 = 1
    f1 = f**u2
    f1 = f1**u2
    g1 = f1**u
    g2 = g1**u
    g3 = g2**u
    g4 = g3**u
    g5 = g4**u
    g6 = g5**u
    y = g6*f1*f
    t = y.frobenius(7)
    t0 = t0*t
    y = y**u
    t = y.frobenius(6)
    t0 = t0*t
    y = y**u
    t = y.frobenius(5)
    t0 = t0*t
    y = y**u
    t = y.frobenius(4)
    t0 = t0*t
    y = y**u
    t = y.frobenius(3)
    t0 = t0*t
    y = y**u
    t = y.frobenius(2)
    t0 = t0*t
    y = y**u
    t = y.frobenius(1)
    y = y**u
    t0 = t0*t*y*f

    return t0
