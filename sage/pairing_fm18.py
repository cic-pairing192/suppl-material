"""
Fotiadis-Martindale curve FM25 k=18 from ePrint 2019/555
Date: 2023

px = (3*x**12 - 3*x**9 + x**8 - 2*x**7 + 7*x**6 - x**5 - x**4 - 4*x**3 + x**2 - 2*x + 4)/3
rx = x**6 - x**3 + 1
tx = x**6 - x**4 - x**3 + 2 # t(x) = -x^4 + 1 + r(x)
cx = (3*x**6 + x**2 - 2*x + 1)/3    # cofactor of curve order #E(Fp) = c(x)*r(x) = p(x) + 1 - t(x)
yx = (3*x**6 + x**4 - x**3 - 2*x + 2)/3         # y such that t(x)^2 - 4*p(x) = -D*y(x)^2
c2x = (27*x**30 - 54*x**27 + 27*x**26 - 54*x**25 + 189*x**24 - 54*x**23 + 36*x**22 - 306*x**21 + 189*x**20 - 243*x**19 + 514*x**18 - 168*x**17 + 150*x**16 - 616*x**15 + 423*x**14 - 396*x**13 + 656*x**12 - 165*x**11 + 273*x**10 - 541*x**9 + 336*x**8 - 408*x**7 + 278*x**6 - 135*x**5 + 180*x**4 - 130*x**3 + 150*x**2 - 96*x + 19)/27
lambrx = x**3-1
lambcx = -(3*x**5 + 3*x**4 + 3*x**3 + x)/2
x = 1 mod 3
"""
from pairing import *

def miller_loop_opt_ate_fm18(Q, P, u):
    """Miller loop f_{u,Q}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters, u = 1 mod 3

    The curve coefficient a is zero.
    """
    m, uQ = miller_function_ate_2naf(Q, P, 0, u, m0=1)

    return m

def miller_loop_opt_ate_aklgl_fm18(Q, P, b_t, u, Fq6, map_Fq6_Fpk, D_twist=False, xi=None, check=False):
    """FM18 optimal ate Miller loop f_{u,Q}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `b_t`: the curve coefficient of the twist curve
    - `u`: seed for curve parameters, u = 1 mod 3
    - `Fq6`: the extension compatible with the twist
    - `map_Fq6_Fpk`: map from Fq6 (with explicit degree 6) to absolute extension Fpk
    - `D_twist`: is it a D-twist of a M-twist

    The curve coefficient a is zero.
    """
    if xi is None:
        xi = -Fq6.modulus().constant_coefficient() # works with absolute and towering of extension
    m, uQ = miller_function_ate_aklgl(Q, P, b_t, u, Fq6, D_twist=D_twist)

    return m

def final_exp_hard_fm18_v0(f, u, u0):
    """
    INPUT:
    - `f`: element in GF(p^18)
    - `u`: curve seed, u = 1 mod 3
    - `u0`: (u-1)/3 (integer)

    Cost: 12 M + 5 Frobenius powers + 11 exponentiations to u + 1 exponentiations to u0 + 5 Inversions with Frobenius power p^9
    """
    v = abs(u)
    v0 = abs(u0)
    #####
    fv1 = f**v
    fv2 = fv1**v
    fv3 = fv2**v
    fv4 = fv3**v
    fv5 = fv4**v
    fv6 = fv5**v
    #####
    fvp1 = fv1*f
    fv01 = fvp1**v0
    y5 = fv6*f*fv01
    #####
    y51 = y5**v
    y52 = y51**v
    #####
    x52 = 1/y52
    z = x52*f
    zv1 = z**v
    zv2 = zv1**v
    y4 = zv2
    #####
    zv3 = zv2**v
    y3 = zv3*x52
    #####
    x5 = 1/y5
    y2 = zv1*x5
    #####
    y1 = 1/y51
    #####
    wv3 = 1/zv3
    y0 = wv3*f
    #####
    w0 = y0
    w1 = y1.frobenius(1)
    w2 = y2.frobenius(2)
    w3 = y3.frobenius(3)
    w4 = y4.frobenius(4)
    w5 = y5.frobenius(5)
    #####
    t0 = w0*w1*w2*w3*w4*w5
    t0 = 1/t0
    
    return t0

def final_exp_hard_fm18_v1(m, u):
    """
    INPUT:
    - `m`: element in GF(p^18)
    - `u`: curve seed, u = 1 mod 3
    RETURN: m^(Phi_18(q)/r) = m^((q^6-q^3+1)/r)

    (q - u)*((u^6 + (u-1)^2/3 + 1)*(q^4 + q^3*u - q - u^3*(q^3*u - q - u)) + u * (q^3*u - q - u)) + 1
    Cost 7 exp(|u|) + exp(|u-1|) + exp(|u-1|/3) + 2 exp(|u+1|) + 13 M + 2 S + 4 f + 4 cj
    """
    u1 = abs(u-1)
    u3 = u1//3
    u_ = abs(u)
    u2 = abs(u+1)
    mu = m**u_
    if u > 0:
        mu = mu.conjugate()
    m0 = m.frobenius() * mu                                 # ^(q - u)
    # ^(u * (q^3*u - q - u))
    m1 = m0**u_                                             # ^u
    if u > 0:
        m2 = m1.frobenius(3) * m0.frobenius().conjugate()   # (q^3*u - q)
    else:
        m2 = (m1.frobenius(3) * m0.frobenius()).conjugate() # (q^3*u - q)
    if u > 0:
        m1 = m2 * m1.conjugate()                            # (q^3*u - q - u)
    else:
        m1 = m2 * m1                                        # (q^3*u - q - u)
    m1 = m1**u_                                             # u * (q^3*u - q - u)
    if u < 0:
        m1 = m1.conjugate()
    m0 = m0.frobenius(4) * m2 * ((m1**u_)**u_).conjugate()   # (q^4 + q^3*u - q - u^3*(q^3*u - q - u))
    # m2^c5
    #m2 = m2**(u**6 + (u-1)**2/3 + 1)                       #
    # but, the idea is to share and re-use the exponentiations to u, so instead we write
    # u**6 + (u-1)**2/3 + 1 = u^6 + 1 + (u-1)^2/3
    #                       = (u^2 + 1)(u^4-u^2+1) + (u-1)^2/3
    #                       = (u^2 + 1)((u-1)^2(u^2+2u+2) + 2(u-1)+1) + (u-1)^2/3
    # u**6 + (u-1)**2/3 + 1 == (u^2 + 1)*((u-1)^2*((u+1)^2+1) + 2*(u-1)+1) + (u-1)^2/3
    m2 = m0**u1                                             # m2^(|u-1|)
    if u > 0:
        m3 = m2**2 * m0                                     # 2(u-1)+1
    else:
        m3 = m2.conjugate()**2 * m0                         # 2(u-1)+1
    m2 = m2**u3                                             # m2**((u-1)^2/3)
    m4 = m2**2 * m2                                         # ^((u-1)^2)
    m4 = (m4**u2)**u2 * m4 * m3                             # ^((u-1)^2((u+1)^2 + 1) + 2(u-1)+1)
    m4 = (m4**u_)**u_ * m4                                  # ^(u^2+1)
    m2 = m4 * m2
    return m2 * m1 * m

def final_exp_hard_fm18_v2(m, u):
    """
    INPUT:
    - `m`: element in GF(p^18)
    - `u`: curve seed, u = 1 mod 3
    RETURN: m^(3*Phi_18(q)/r) = m^(3*(q^6-q^3+1)/r)

    (q - u)*((3*(u^6 + 1) + (u-1)^2)*(q^4 + q^3*u - q - u^3*(q^3*u - q - u)) + 3*u * (q^3*u - q - u)) + 3
    Cost 11 exp(|u|) + 12 M + 3 S + 4 f + 6 cj
    exponent multiplied by 3 to avoid division (u-1)/3 (of unexpected Hamming weight) compared to final_exp_hard_fm18_v1
    """
    u_ = abs(u)
    mu = m**u_
    if u > 0:
        mu = mu.conjugate()
    m0 = m.frobenius() * mu                                 # ^(q - u)
    # ^(u * (q^3*u - q - u))
    m1 = m0**u_                                             # ^u
    if u > 0:
        m2 = m1.frobenius(3) * m0.frobenius().conjugate()   # (q^3*u - q)
    else:
        m2 = (m1.frobenius(3) * m0.frobenius()).conjugate() # (q^3*u - q)
    if u > 0:
        m1 = m2 * m1.conjugate()                            # (q^3*u - q - u)
    else:
        m1 = m2 * m1                                        # (q^3*u - q - u)
    m1 = m1**u_                                             # u * (q^3*u - q - u)
    if u < 0:
        m1 = m1.conjugate()
    m0 = m0.frobenius(4) * m2 * ((m1**u_)**u_).conjugate()  # (q^4 + q^3*u - q - u^3*(q^3*u - q - u))
    # 3*u^6 + u^2 - 2*u + 4
    #m2 = m0**(3*(u**6 + 1) + (u-1)**2)                     #
    # but, the idea is to share and re-use the exponentiations to u, so instead we write
    # 3*u^6 + u^2 - 2*u + 4
    m3 = m0**u_                                             # |u|
    m4 = m3**u_                                             # u^2
    if u > 0:
        m3 = m3.conjugate()
    m6 = (((m4**u_)**u_)**u_)**u_                           # u^6
    m2 = ((m6 * m0)**2 * m3)**2 * m4 * m6.conjugate()       # ((u^6 + 1)*2 - u)*2 + u^2 -u^6
    m3 = m1 * m
    return m2 * m3**2 * m3

def cofactor_clearing_g1_fm18(P, u, omega=None):
    """
    cofactor clearing with endomorphism phi on E(Fp): phi^2 + phi + 1 = 0
    INPUT:
    -`P`: point on a FM18 curve E
    -`u`: seed for the curve parameters, u = 1 mod 3
    -`omega`: (-1+sqrt(-3))/2 mod p

    The cofactor is c(x) = (3*x^6 + x^2 - 2*x + 1)/3
    The eigenvalue mod cx is -(3*x^5 + 3*x^4 + 3*x^3 + x)/2 so that is matches with phi having eigenvalue u^3-1 mod r
    The endomorphism is psi(P) = (omega*xP, yP) where omega is a primitive cubic root of unity mod p

    short vector for fast G1 cofactor clearing:
    [    2*(x - 1)/3  x^3 + (x - 1)/3]
    [x^3 - (x - 1)/3     -2*(x - 1)/3]
    x^3 = (x-1)/3 * 3*(x^2+x+1) + 1
    x^3 - (x - 1)/3 = (x-1)/3 * (3*(x^2+x+1) - 1) + 1
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((93*u**11 - 48*u**10 - 240*u**9 - 267*u**8 + 235*u**7 - 84*u**6 + 139*u**5 - 191*u**4 - 131*u**3 - 266*u**2 + 411*u - 230)/342)
        # this is a rational, not an integer, do not use // but use /
    S = (u-1)//3 * P
    phiS = P.curve()(S[0]*omega, S[1], S[2])
    P = (u**2+u+1)*3*S - S + P - 2*phiS
    return P

def membership_testing_g1_fm18(P, u, omega=None):
    """
    G1 membership testing, phi(P) = (omega*x, y) = [u^3-1]*P if P is in G1

    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed, u = 1 mod 3
    - `omega`: such that (omega*x, y) has eigenvalue u^3-1

    P -> P + [1+lambda]phi(P) = P + [u^3]phi(P)
    Then, 1 + (1+lambda)*lambda = 1 + (u^3)*(u^3-1) = 1 -u^3 + u^6 = r(u)
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((93*u**11 - 48*u**10 - 240*u**9 - 267*u**8 + 235*u**7 - 84*u**6 + 139*u**5 - 191*u**4 - 131*u**3 - 266*u**2 + 411*u - 230)/342)
        # !!! this is a rational, not an integer, do not use // but use /
    phiP = P.curve()((P[0]*omega, P[1], P[2]))
    lphiP = (u**3)*phiP
    return (P + lphiP).is_zero()

def membership_testing_g1_fm18_alt(P, u, omega=None):
    """
    G1 membership testing, phi(P) = (omega*x, y) = [u^3-1]*P if P is in G1

    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed, u = 1 mod 3
    - `omega`: such that (omega*x, y) has eigenvalue u^3-1

    P -> [-lambda]P + phi(P) = [-u^3+1]P + phi(P)
    the result should be 0
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((93*u**11 - 48*u**10 - 240*u**9 - 267*u**8 + 235*u**7 - 84*u**6 + 139*u**5 - 191*u**4 - 131*u**3 - 266*u**2 + 411*u - 230)/342)
        # !!! this is a rational, not an integer, do not use // but use /
    phiP = P.curve()((P[0]*omega, P[1], P[2]))
    S = (-u**3+1)*P
    return (S + phiP).is_zero()

def cofactor_clearing_g2_fm18(Q, u, Fq6, D_twist=True, case=0):
    """
    Multiply Q by the cofactor of G2
    INPUT:
    - `Q`: point on E'(Fp3) containing (compressed) G2
    - `u`: seed of the FM25-k18 curve
    - `Fq6`: finite field extension of explicit degree 6 on top of Fq
    - `D_twist`: True/False (M_twist)

    cofactor clearing with endomorphism on G2
    G2 is supposed to be given in compressed representation over GF(p^3)
    That is, P.curve() is E'(Fp3) a sixth twist of E

    Note that it is possible to multiply everything by 3 to cancel the
    denominator in (u+2)/3 if the Hamming weight of (u+2)/3 is higher than
    the Hamming weight of (u+2), plus one square and one multiplication

    The endomorphism is
    psi(P) = twist o Frobenius o untwist (P)

    The eigenvalue is a root of the characteristic polynomial X^2 - t*X + p
    That is one of (t +/- y sqrt(-3))/2 (the one that matches p on G2 mod r)
    G2 has order p^3 + 1 - t3' where t3' is the trace of E', the appropriate sixth twist of E(Fp3)
    Let t be the trace of E(Fp), t2 = t^2-2*p and t3 = t*t2-p*t = t^3-3*p*t
    y3 = y * (p-t^2) where p = (t^2 + 3*y^2)/4
    Then #E'(Fp3) = p^3 + 1 - (3*y3+t3)/2 = r * c2
    G2 cofactor = (27*x^30 - 54*x^27 + 27*x^26 - 54*x^25 + 189*x^24 - 54*x^23 + 36*x^22 - 306*x^21 + 189*x^20 - 243*x^19 + 514*x^18 - 168*x^17 + 150*x^16 - 616*x^15 + 423*x^14 - 396*x^13 + 656*x^12 - 165*x^11 + 273*x^10 - 541*x^9 + 336*x^8 - 408*x^7 + 278*x^6 - 135*x^5 + 180*x^4 - 130*x^3 + 150*x^2 - 96*x + 19)/27
    reduced matrix:

    [            2*x*(x + 2)/3,           x^3 - (x + 2)/3,          -2*x^2*(x + 2)/3,      -x*(x^3 + (x + 2)/3),                 2*(x+2)/3, x^2*(x^3 + (x + 2)/3) - 1 ]
    [          x^3 - (x + 2)/3,          -2*x^2*(x + 2)/3,      -x*(x^3 - (x + 2)/3),                 2*(x+2)/3, x^2*(x^3 + (x + 2)/3) - 1,            -2*x*(x + 2)/3 ]
    [         -2*x^2*(x + 2)/3,      -x*(x^3 - (x + 2)/3),           x^3 + (x + 2)/3, x^2*(x^3 + (x + 2)/3) - 1,            -2*x*(x + 2)/3,          -x^3 + (x + 2)/3 ]
    [     -x*(x^3 - (x + 2)/3),           x^3 + (x + 2)/3, x^2*(x^3 - (x + 2)/3) - 1,            -2*x*(x + 2)/3,          -x^3 + (x + 2)/3,           2*x^2*(x + 2)/3 ]
    [          x^3 + (x + 2)/3, x^2*(x^3 - (x + 2)/3) - 1,      -x*(x^3 + (x + 2)/3),          -x^3 + (x + 2)/3,           2*x^2*(x + 2)/3,       x*(x^3 - (x + 2)/3) ]
    [x^2*(x^3 - (x + 2)/3) - 1,      -x*(x^3 + (x + 2)/3),                 2*(x+2)/3,           2*x^2*(x + 2)/3,       x*(x^3 - (x + 2)/3),          -x^3 - (x + 2)/3 ]
    note that (x+2)/3 is integer as x = 1 mod 3
    for each row [l0 l1 l2 l3 l4 l5] of the matrix, l0 + l1*L + l2*L^2 + l3*L^3 + l4*L^4 + l5*L^5 is a multiple of c2, where L is the eigenvalue mod c2, such that L mod r = q mod r.
    """
    if Q.is_zero():
        return Q
    # note that all these mu values could be precomputed and stored
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu
    mu3 = mu.frobenius(2)*mu2
    mu4 = mu2.frobenius(2)*mu2
    mu5 = mu3 * mu2.frobenius(3)
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 6, 1, D_twist)
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 6, 2, D_twist)
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 6, 3, D_twist)
    psi4Q = endomorphism_g2_psi_p(Q, None, mu4, 6, 4, D_twist)
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 6, 5, D_twist)
    if case == 0:
        return             2*u*(u+2)//3*Q +          (u**3-(u+2)//3)*psi1Q +         -2*u**2*(u+2)//3*psi2Q +       -u*(u**3+(u+2)//3)*psi3Q +               2*(u+2)//3*psi4Q + (u**2*(u**3+(u+2)//3)-1)*psi5Q
    if case == 1:
        return          (u**3-(u+2)//3)*Q +         -2*u**2*(u+2)//3*psi1Q +       -u*(u**3-(u+2)//3)*psi2Q +               2*(u+2)//3*psi3Q + (u**2*(u**3+(u+2)//3)-1)*psi4Q +            -2*u*(u+2)//3*psi5Q
    if case == 2:
        return         -2*u**2*(u+2)//3*Q +       -u*(u**3-(u+2)//3)*psi1Q +          (u**3+(u+2)//3)*psi2Q + (u**2*(u**3+(u+2)//3)-1)*psi3Q +            -2*u*(u+2)//3*psi4Q +         (-u**3+(u+2)//3)*psi5Q
    if case == 3:
        return       -u*(u**3-(u+2)//3)*Q +          (u**3+(u+2)//3)*psi1Q + (u**2*(u**3-(u+2)//3)-1)*psi2Q +            -2*u*(u+2)//3*psi3Q +         (-u**3+(u+2)//3)*psi4Q +          2*u**2*(u+2)//3*psi5Q
    if case == 4:
        return          (u**3+(u+2)//3)*Q + (u**2*(u**3-(u+2)//3)-1)*psi1Q +       -u*(u**3+(u+2)//3)*psi2Q +         (-u**3+(u+2)//3)*psi3Q +          2*u**2*(u+2)//3*psi4Q +        u*(u**3-(u+2)//3)*psi5Q
    if case == 5:
        return (u**2*(u**3-(u+2)//3)-1)*Q +       -u*(u**3+(u+2)//3)*psi1Q +               2*(u+2)//3*psi2Q +          2*u**2*(u+2)//3*psi3Q +        u*(u**3-(u+2)//3)*psi4Q +         (-u**3-(u+2)//3)*psi5Q

def membership_testing_g2_fm18(Q, u, Fq6, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^e, e=k/d, a d-twist of E(Fqd)
    - `u`: curve seed
    - `Fq6`: Finite field extension of degree 6 on top of Fq = Fp3
    - `D_twist`: True/False

    Formula
    eq1 := 1 + x*(qx^2 mod rx);
    eq2 := x + qx - qx^4;

    short vectors for fast G2 subgroup membership testing: rows of the matrix
    [ 0  0  0  1  0  x]
    [ 0  0  1  0  x  0]
    [ 0  1  0  x  0  0]
    [ 1  0  x  0  0  0]
    [ 0  x  1  0  0 -1]
    [ x  1  0  0 -1  0]

    (1 0 x 0 0 0) -> resultant = rx*1
    resulant(res, g2cx) = 4059473246533848947381055389847709/16677181699666569 = [ <15366271699, 1>, <264180754190232735606991, 1> ]/[ <3, 34> ]
    l = 15366271699, ra = [ 8210404777, 8909636407, 11803430521 ], rb = [ 4975253219, 11803430521, 14059698872, 14276492378 ], common roots are [ 11803430521 ]
    l = 264180754190232735606991, ra = [ 483871160662534969264, 95923141787330440983882, 101023430526834047575622, 110981580108940659595332 ], rb = [ 88737497276011493356340, 101023430526834047575622, 104934892429844289897730, 108719734852812472635148, 114797402765876869822439, 166797530103103891604235, 229163572727765032363772 ], common roots are [ 101023430526834047575622 ]
    """
    assert (u % 15366271699) != 11803430521 and (u % 264180754190232735606991) != 101023430526834047575622
    if Q.is_zero():
        return Q
    # note that all these mu values could be precomputed and stored
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 6, 2, D_twist)
    return (Q + u*psi2Q).is_zero()

def membership_testing_g2_fm18_alt(Q, u, Fq6, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^e, e=k/d, a d-twist of E(Fqd)
    - `u`: curve seed
    - `Fq6`: Finite field extension of degree 6 on top of Fq = Fp3
    - `D_twist`: True/False

    Formula
    eq1 := 1 + x*(qx^2 mod rx);
    eq2 := x + qx - qx^4;

    short vectors for fast G2 subgroup membership testing: rows of the matrix
    [ 0  0  0  1  0  x]
    [ 0  0  1  0  x  0]
    [ 0  1  0  x  0  0]
    [ 1  0  x  0  0  0]
    [ 0  x  1  0  0 -1]
    [ x  1  0  0 -1  0]

    ( x  1  0  0 -1  0) -> resultant = rx*1
    resulant(res, g2cx) = 762572497597471159157055595486701990117418428241309896704713103191/834385168331080533771857328695283 = [ <19, 1>, <523, 1>, <1009, 1>, <2251, 1>, <33787743393537403193292240167841642724986217996664658277, 1> ]/[ <3, 69> ]
    l = 19, ra = [ 17, 18 ], rb = [ 0, 4, 8, 9, 11, 16, 17 ], common roots are [ 17 ]
    l = 523, ra = [ 9, 116, 254, 435 ], rb = [ 107, 116, 244, 282, 292, 298, 299, 428 ], common roots are [ 116 ]
    l = 1009, ra = [ 269, 766, 921 ], rb = [ 37, 595, 660, 679, 766 ], common roots are [ 766 ]
    l = 2251, ra = [ 197, 222, 1221 ], rb = [ 27, 222, 852, 1754 ], common roots are [ 222 ]
    l = 33787743393537403193292240167841642724986217996664658277, ra = [ 14887093232092150249951524224620059086784115864284421756, 20075329133722339089807875467047659246564652260855718968, 26182425400280097713158790212745398031420554155814408652, 31483493276931341593354736602431835053855963098515318255 ], rb = [ 1874780109118896202829666030653180870634313694739759362, 5939871132310791813384205005184028774332102176514054176, 14887093232092150249951524224620059086784115864284421756, 24272063227982046569461648400298480525028054224621451917, 25102248071263203011727900187264325840916789509737581234 ], common roots are [ 14887093232092150249951524224620059086784115864284421756 ]
    """
    assert (u % 19) != 17 and (u % 523) != 116 and (u % 1009) != 766 and (u % 2251) != 222 and (u % 33787743393537403193292240167841642724986217996664658277) != 14887093232092150249951524224620059086784115864284421756
    if Q.is_zero():
        return Q
    # note that all these mu values could be precomputed and stored
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu
    mu4 = mu2.frobenius(2)*mu2
    psiQ = endomorphism_g2_psi_p(Q, None, mu, 6, 1, D_twist)
    psi4Q = endomorphism_g2_psi_p(Q, None, mu4, 6, 4, D_twist)
    return (u*Q + psiQ - psi4Q).is_zero()
