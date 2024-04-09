from pairing import *

"""
LLL reduced Matrix for optimal ate pairing (and subgroup membership testing)
[-1  0  0  0  2  0  0  x]
[ 0  0  0  2  0  0  x  1]
[ 0  0  2  0  0  x  1  0]
[ 0  2  0  0  x  1  0  0]
[ 2  0  0  x  1  0  0  0]
[ 0  0  x  1  0  0  0 -2]
[ 0  x  1  0  0  0 -2  0]
[ x  1  0  0  0 -2  0  0]
Formulas:
(row 0) -1 + 2*pi^4 + u*p^7 = 0 mod r
(row 4)  2 + u*pi^3 + pi^4 = 0 mod r
(row 7)  u + pi -2*pi^5 = 0 mod r
"""

def miller_loop_opt_ate_kss16(Q, P, a, u):
    """
    Miller loop (f_{u,Q}(P) l_{[u]Q,\pi(Q)}(P))^{p^3} l_{Q,Q}(P)
    Formula: 2 + u*pi^3 + pi^4 = 0 mod r

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters
    """
    m, uQ = miller_function_ate(Q, P, a, u, m0=1)
    piQ = [(Q[0]).frobenius(), (Q[1]).frobenius()]
    PP = (P[0], P[1])
    l1, uQ_piQ = add_line_j(uQ, piQ, PP)
    QQ = (Q[0], Q[1])
    l2, Q2 = double_line_affine_j(QQ, PP, a)

    return (l1 *  m).frobenius(3) * l2

def miller_loop_opt_ate_kss16_v2(Q, P, a, u):
    """
    Miller loop l_{Q,Q}(P) * f_{u, pi3(Q)} * l_{pi4Q, u*pi3(Q)}(P)
    Formula: 2 + u*pi^3 + pi^4 = 0 mod r

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters
    """
    pi3Q = [(Q[0]).frobenius(3), (Q[1]).frobenius(3)]
    pi4Q = [(Q[0]).frobenius(4), (Q[1]).frobenius(4)]
    m, upi3Q = miller_function_ate(pi3Q, P, a, u, m0=1)
    QQ = (Q[0],Q[1])
    PP = (P[0],P[1])
    l2, Q2 = double_line_affine_j(QQ, PP, a)
    l1, pi4Q_u_pi3Q = add_line_j(upi3Q, pi4Q, PP)

    return l2 *  m * l1

def miller_loop_opt_ate_kss16_cln_b0(Q, P, a, u):
    """
    Miller loop (f_{u,Q}(P) l_{[u]Q,\pi(Q)}(P))^{p^3} l_{Q,Q}(P)
    Formula: 2 + u*pi^3 + pi^4 = 0 mod r

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x
    - `u`: seed for curve parameters
    """
    m, uQ = miller_function_ate_cln_b0(Q, P, a, u)
    piQ = [(Q[0]).frobenius(), (Q[1]).frobenius()]
    PP = (P[0], P[1])
    l1, uQ_piQ = add_line_cln_b0(uQ, piQ, PP)
    QQ = (Q[0], Q[1], 1)
    l2, Q2 = double_line_cln_b0(QQ, PP, a)

    return (l1 *  m).frobenius(3) * l2

def miller_loop_opt_ate_kss16_cln_b0_v2(Q, P, a, u):
    """Miller loop
    l_{Q,Q}(P) * f_{u, pi3(Q)} * l_{pi4Q, u*pi3(Q)}(P)
    Formula: 2 + u*pi^3 + pi^4 = 0 mod r

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters
    """
    pi3Q = [(Q[0]).frobenius(3), (Q[1]).frobenius(3)]
    pi4Q = [(Q[0]).frobenius(4), (Q[1]).frobenius(4)]
    m, upi3Q = miller_function_ate_cln_b0(pi3Q, P, a, u, m0=1)
    QQ = (Q[0],Q[1], 1)
    PP = (P[0],P[1])
    l2, Q2 = double_line_cln_b0(QQ, PP, a)
    l1, pi4Q_u_pi3Q = add_line_cln_b0(upi3Q, pi4Q, PP)

    return l2 *  m * l1

def gfp16_frobenius(s, i):
    return s.frobenius(i)

def inversion_easy_gfp16(s):
    """1/s = s^(p^8) in the cyclotomic subgroup """
    return gfp16_frobenius(s, 8)

def final_exp_hard_kss16(m, u):
    """
    k := 16;
    D := 1;
    px := (x^10 + 2*x^9 + 5*x^8 + 48*x^6 + 152*x^5 + 240*x^4 + 625*x^2 + 2398*x + 3125)/980;
    rx := (x^8 + 48*x^4 + 625)/61250; // 625 = 5^4, 61250 = 2*5^4*7^2
    tx := (2*x^5 + 41*x + 35)/35;
    cx := 125 * (x^2 + 2*x + 5)/2; // C such that P+1-T = C*R
    exponent := (px^8+1) div rx;

    C5[1] =   -2*x^8 - 4*x^7 - 10*x^6 - 55*x^4 - 222*x^3 - 275*x^2 = (  -2*x^3) * (x^5 + 2*x^4 + 5*x^3 + 56) +  55 * (-x^4 - 2*x^3 - 5*x^2) = ... + ((-x^2) * (x^2 + 2*x + 5) + 0
    C5[2] =      4*x^7 + 8*x^6 + 20*x^5 + 75*x^3 + 374*x^2 + 375*x = (   4*x^2) * (x^5 + 2*x^4 + 5*x^3 + 56) +  75 * (x^3 + 2*x^2 + 5*x)    = ... + ((x)    * (x^2 + 2*x + 5) + 0
    C5[3] =         2*x^6 + 4*x^5 + 10*x^4 + 125*x^2 + 362*x + 625 = (     2*x) * (x^5 + 2*x^4 + 5*x^3 + 56) + 125 * (x^2 + 2*x + 5)        = ... + ((1)    * (x^2 + 2*x + 5) + 0
    C5[4] = x^9 + 2*x^8 + 5*x^7 + 24*x^5 + 104*x^4 + 120*x^3 - 196 = (x^4 + 24) * (x^5 + 2*x^4 + 5*x^3 + 56) +   1 * (-1540)                = ... + ((0)    * (x^2 + 2*x + 5) + -1540
    C5[5] =        -x^8 - 2*x^7 - 5*x^6 - 10*x^4 - 76*x^3 - 50*x^2 = (    -x^3) * (x^5 + 2*x^4 + 5*x^3 + 56) +  10 * (-x^4 - 2*x^3 - 5*x^2) = ... + ((-x^2) * (x^2 + 2*x + 5) + 0
    C5[6] =    -3*x^7 - 6*x^6 - 15*x^5 - 100*x^3 - 368*x^2 - 500*x = (  -3*x^2) * (x^5 + 2*x^4 + 5*x^3 + 56) + 100 * (-x^3 - 2*x^2 - 5*x)   = ... + ((-x)   * (x^2 + 2*x + 5) + 0
    C5[7] =     11*x^6 + 22*x^5 + 55*x^4 + 250*x^2 + 1116*x + 1250 = (    11*x) * (x^5 + 2*x^4 + 5*x^3 + 56) + 250 * (x^2 + 2*x + 5)        = ... + ((1)    * (x^2 + 2*x + 5) + 0
    C5[8] =                         -7*x^5 - 14*x^4 - 35*x^3 - 392 = (      -7) * (x^5 + 2*x^4 + 5*x^3 + 56) +   1 * (0)                    = ... + ((0)    * (x^2 + 2*x + 5) + 0

    e5 := (x^3*(x^2+2*x+5)+56)*(-(8-1)*px^7 + (16+8)*px^3 + 4*px + x*((8+2+1)*px^6 + 2*px^2) + x^2*(-(4-1)*px^5) + x^4*px^3 -x^3*(px^4+2)) + 5*((x^2+2*x+5)*(25*(px^2 + 2*px^6) -5*x*(4*px^5 - 3*px) -x^2*(2*px^4 + 11)) - 308*px^3);
    e5 eq -14/125*x^3 * exponent;

    # total cost 33 S + 31 M + 2 exp(u+1) + 7 exp(u) + 14*f16 + 8 inv_frob_8
    """
    # 0. compute m^(308*p^3)
    m4 = (m**2)**2
    m8 = m4**2                                   # 3 S
    f0 = (((((m8 * m)**2 * m)**2)**2 * m)**2)**2 # 5 S + 3 M
    #assert f0 == m**308
    f0 = f0.frobenius(3)
    f0 = f0.frobenius(8)                         # cyclo inv
    #1. compute m^(x^2+2*x+5) = m^((x+1)^2 + 4)
    f1 = (m**(u+1))**(u+1) * m4                  # M + 2*exp(u+1)
    #assert f1 == m**(u**2 + 2*u + 5)
    # compute the term in (x^2+2*x+5)
    f1a = f1.frobenius(2) * f1.frobenius(6)**2   # (px^2 + 2*px^6)
    f1a = (f1a**2)**2 * f1a                      # power 5 -> 5*(px^2 + 2*px^6)
    f1x = f1**u
    # -5*x*(4*px^5 - 3*px) = -5*x*(4*px^5 - (4-1)*px) = -5*x*(4*(px^5-px) + px)
    f1xp = f1x.frobenius()
    f1b = ((f1x.frobenius(5) * f1xp.frobenius(8))**2)**2 * f1xp
    #assert f1b == f1x.frobenius(5)**4 * f1x.frobenius()**(-3)
    f1ab = f1a * f1b.frobenius(8)
    f1ab = (f1ab**2)**2 * f1ab
    # f1ab = f1^(25*(px^2 + 2*px^6) -5*x*(4*px^5 - 3*px))
    f1x2 = f1x**u
    # -x^2*(2*px^4 + 11) = (2*px^4 + 8+2+1)
    f1c = (f1x2.frobenius(4) * ((f1x2**2)**2 * f1x2))**2 * f1x2 # 3 S + 3 M
    #assert f1c == (f1.frobenius(4)**2 * f1**11)**(u**2)
    f1c = f1c.frobenius(8)
    f1abc = f1ab * f1c
    f01 = f1abc * f0
    f01 = (f01**2)**2 * f01
    # all the term 5*((x^2+2*x+5)*(25*(px^2 + 2*px^6) -5*x*(4*px^5 - 3*px) -x^2*(2*px^4 + 11)) - 308*px^3)
    # so far 20 S + 16 M + 2 exp(u+2) + 2 exp(u) + 6 Frob + 4 cyclo-inv with Frob-8
    # (x^2+2*x+5)*(50*px^6 -20*x*px^5 -2*x^2*px^4 + 25*px^2 + 15*x*px - 11*x^2)
    #assert f1abc == f1.frobenius(6)**50 * f1.frobenius(5)**(-20*u) * f1.frobenius(4)**(-2*u**2) * f1.frobenius(2)**25 * f1.frobenius()**(15*u) * f1**(-11*u**2)

    # 2. compute m^(x^3*(x^2+2*x+5)+56) from f1 = m^(x^2+2*x+5)
    f1x3 = f1x2**u
    m56 = (((m8 * m.frobenius(8))**2)**2)**2 # M + 3 S
    assert m56 == m**56
    f2 = f1x3 * m56                           # M
    # exp(u) + 2M + 3 S

    # 3. compute ((-8+1)*px^7 + (16+8)*px^3 + x*((8+2+1)*px^6 + 2*px^2) + x^2*(-(4-1)*px^5 + 4*px) + x^4*px^3 -x^3*(px^4+2))
    f2p3 = f2.frobenius(3)
    f2p7 = f2.frobenius(7)
    f2a = (((f2p3**2 * f2p3 * f2p7.frobenius(8))**2)**2)**2 * f2p7
    #assert f2a == f2.frobenius(3)**24 * f2.frobenius(7)**(-7)
    f2x = f2**u
    f2xp6 = f2x.frobenius(6)
    f2b = ((f2xp6**2)**2 * f2xp6 * f2x.frobenius(2))**2 * f2xp6 # 3 S + 3 M
    #assert f2b == f2.frobenius(6)**(11*u) * f2.frobenius(2)**(2*u)
    f2x2 = f2x**u
    f2x2p5 = f2x2.frobenius(5)
    f2c = ((f2x2p5.frobenius(8) * f2x2.frobenius())**2)**2 * f2x2p5
    #assert f2c == f2.frobenius(5)**(-3*u**2) * f2.frobenius()**(4*u**2)
    f2x3 = f2x2**u
    f2e = (f2x3.frobenius(4) * f2x3**2).frobenius(8)
    #assert f2e == f2.frobenius(4)**(-u**3) * f2**(-2*u**3)
    f2x4 = f2x3**u
    f2d = f2x4.frobenius(3)
    #assert f2d == f2.frobenius(3)**(u**4)
    # more 10 S + 4 exp(u) + 9 M
    fC = f2a * f2b * f2c * f2d * f2e
    # -7*px^7 + 11*x*px^6 -3*x^2*px^5 -x^3*px^4 + (x^4+24)*px^3 + 2*x*px^2 + 4*x^2*px -2*x^3
    # p = m.base_ring().characteristic()
    #assert fC == f2.frobenius(7)**(-7) * f2.frobenius(6)**(11*u) * f2.frobenius(5)**(-3*u**2) * f2.frobenius(4)**(-u**3) * f2.frobenius(3)**(u**4+24) * f2.frobenius(2)**(2*u) * f2.frobenius()**(4*u**2) * f2**(-2*u**3)
    # total cost 33 S + 31 M + 2 exp(u+1) + 7 exp(u)
    return (fC) * f01

def final_exp_hard_kss16_ghammam(m, u):
    """Hard part of final exponentiation Phi_8(p)/r

    Loubna Ghammam
    https://tel.archives-ouvertes.fr/tel-01469981v1
    Utilisation des Couplages en Cryptographie asymétrique pour la micro-électronique.
    PhD thesis, Universite de Rennes I, France
    Section 4.3 p. 107
    Eq (4.9) p. 114 Section 4.3.

    Loubna Ghammam and Emmanuel Fouotsa. Adequate Elliptic Curves for Computing the Product of n Pairings.
    International Workshop on the Arithmetic of Finite Fields, WAIFI 2016
    https://link.springer.com/chapter/10.1007/978-3-319-55227-9_3
    https://eprint.iacr.org/2016/472

    s = 14*(u//5)**3
    # for KSS16 curve we have u = 25,45 mod 70 <=> +/- 25 mod 70 --> 5 | u
    m_0 = 2*u**8 + 4*u**7 + 10*u**6 + 55*u**4 + 222*u**3 + 275*u**2
    m_1 = -4*u**7 - 8*u**6 - 20*u**5 - 75*u**3 - 374*u**2 - 375*u
    m_2 = -2*u**6 - 4*u**5 - 10*u**4 - 125*u**2 - 362*u - 625
    m_3 = -*u**9 - 2*u**8 - 5*u**7 - 24*u**5 - 104*u**4 - 120*u**3 + 196
    m_4 = *u**8 + 2*u**7 + 5*u**6 + 10*u**4 + 76*u**3 + 50*u**2
    m_5 = 3*u**7 + 6*u**6 + 15*u**5 + 100*u**3 + 368*u**2 + 500*u
    m_6 = -11*u**6 - 22*u**5 - 55*u**4 - 250*u**2 - 1116*u - 1250
    m_7 = 7*u**5 + 14*u**4 + 35*u**3 + 392
    m_0 + m_1*p + m_2*p**2 + m_3*p**3 + m_4*p**4 + m_5*p**5 + m_6*p**6 + m_7*p**7 == s*d1

    B = (u+1)**2 + 4
    A = u**3*B + 56
    m0 == 2*u**3*A + 55*u**2*B
    m1 == -4*u**2*A - 75*u*B
    m2 == -2*u*A - 125*B
    m3 == -u**4*A -24*u**3*B + 196
    m4 == u**3*A + 10*u**2*B
    m5 == 3*u**2*A + 100*u*B
    m6 == -11*u*A-250*B
    m7 == 7*A

    Cost: 37 S + 35 M + 2*exp(u+1) + 7*exp(u) + 4 frob + 2 frob(2) + frob(4)
    expected cost: 7*exp_u + 2*exp_u1 + 34*s16_cyclo + 32*m16 + 7*f16 + 3*c16_cyclo
    where c16_cyclo is a cube, hence 3*c16_cyclo = 3*(S_cyclo + M) = 3*S_cyclo + 3*M
    """
    t0 = m**2                               # t0  = m^2
    t1 = t0**2                              # t1  = m^4
    t2 = m**(u+1)                           # t2  = m^(u+1)
    t3 = t2**(u+1)                          # t3  = m^(u+1)^2
    t4 = t3 * t1                            # t4  = m^(4 + (u+1)^2)                = m^B
    t5 = t4**u                              # t5  = m^(u*B)
    t6 = (t4**2)**2 * t4                    # t6  = m^(5*B)
    t7 = ((t1**2)**2)**2                    # t7  = m^32
    t8 = t7**2                              # t8  = m^64
    inv_t1 = inversion_easy_gfp16(t1)       # m^(-4)
    t9 = t7 * inv_t1                        # t9  = m^(28)
    t10 = t9**2                             # t10 = m^56
    t11 = t5**u                             # t11 = m^(u^2*B)
    t12 = t11**u                            # t12 = m^(u^3*B)
    t01 = t12 * t10                         # t01 = m^(u^3*B + 56)                 = m^A
    t14 = t01**u                            # t14 = m^(u*A)
    inv_t14 = inversion_easy_gfp16(t14)     # m^(-u*A)
    t13 = inv_t14**2                        # t13 = m^(-2*u*A)
    t00 = (t6**2)**2 * t6                   # t00 = m^(25*B)
    t15 = (t00**2)**2 * t00                 # t15 = m^(125*B)
    inv_t15 = inversion_easy_gfp16(t15)     # m^(-125*B)
    t0 = t13 * inv_t15                      # t0 = m^(-2*u*A - 125*B)              = m^m2
    t16 = t0**2                             # t16 = m^(-4*u*A - 250*B)
    t17 = (t13**2)**2                       # t17 = m^(-8*u*A)
    t18 = t17 * t14                         # t18 = m^(-7*u*A)
    t2 = t16 * t18                          # t2  = m^(-11*u*A - 250*B)            = m^m6
    t19 = t14**u                            # t19 = m^(u^2*A)
    t20 = t19**u                            # t20 = m^(u^3*A)
    t21 = t20**u                            # t21 = m^(u^4*A)
    t22 = t19**2                            # t22 = m^(2*u^2*A)
    t23 = (t5**2)**2 * t5                   # t23 = m^(5*u*B)
    t24 = (t23**2)**2 * t23                 # t24 = m^(25*u*B)
    t25 = t24**2 * t24                      # t25 = m^(75*u*B)
    t26 = t24 * t25                         # t26 = m^(100*u*B)
    t27 = t22**2                            # t27 = m^(4*u^2*A)
    t37 = inversion_easy_gfp16(t27 * t25)   # t37 = m^(-4*u^2*A - 75*u*B) = m^m1
    t28 = t27 * inversion_easy_gfp16(t19)   # t28 = m^(3*u^2*A)
    t3 = t28 * t26                          # t3  = m^(3*u^2*A + 100*u*B)          = m^m5
    t29 = (t11**2)**2 * t11                 # t29 = m^(5*u^2*B)
    t30 = t29**2                            # t30 = m^(10*u^2*B)
    t4 = t20 * t30                          # t4  = m^(u^3*A + 10*u^2*B)           = m^m4
    s0 = t20**2                             # s0  = m^(2*u^3*A)
    s1 = (t30**2)**2 * t30                  # s1  = m^(50*u^2*B)
    s2 = s1 * t29                           # s2  = m^(55*u^2*B)
    s3 = s0 * s2                            # s3  = m^(2*u^3*A + 55*u^2*B)         = m^m0
    #t31 = t12**24    # t31 = m^(24*u^3*B)
    t31 = (((t12**2 * t12)**2)**2)**2       # t31 = m^(24*u^3*B)
    t5 = inversion_easy_gfp16(t21 * t31)    # m^(-u^4*A-24*u^3*B)
    t6 = (t8**2 * t8) * t1                  # t6  = m^196
    t7 = t5 * t6                            # t7  = m^(-u^4*A-24*u^3*B+196)        = m^m3
    t8 = (t01**2 * t01)**2 * t01            # m^(7*A)                             = m^m7
    t32 = t37.frobenius() * t7.frobenius(3) * t3.frobenius(5) * t8.frobenius(7)
    # t32 = m^(m1^p + m3*p^3 + m5*p^5 + m7*p^7)
    t33 = t0.frobenius(2) * t2.frobenius(6) # t33 = m^(m2*p^2 + m6*p^6)
    t = s3 * t32 * t33 * t4.frobenius(4)
    # m^(m0 + m1^p + m2*p^2 + m3*p^3 + m4*p^4 + m5*p^5 + m6*p^6 + m7*p^7)
    # B = (u+1)**2 + 4
    # A = u**3*B + 56
    # m0 = 2*u**3*A + 55*u**2*B
    # m1 = -4*u**2*A - 75*u*B
    # m2 = -2*u*A - 125*B
    # m3 = -u**4*A -24*u**3*B + 196
    # m4 = u**3*A + 10*u**2*B
    # m5 = 3*u**2*A + 100*u*B
    # m6 = -11*u*A-250*B
    # m7 = 7*A
    # #assert t4 == m**B
    # assert t01 == m**A
    # assert t0 == m**m2
    # assert t2 == m**m6
    # assert t37 == m**m1
    # assert t3 == m**m5
    # assert t4 == m**m4
    # assert s3 == m**m0
    # assert t7 == m**m3
    # assert t8 == m**m7
    return t

def final_exp_hard_kss16_v2(m, u):
    """
c=5
C5[1] =     -2*x^8 - 4*x^7 - 10*x^6 - 55*x^4 - 222*x^3 - 275*x^2 = (    2*x^3) * (-x^5 - 2*x^4 - 5*x^3 - 56) +  55 * (-x^4 - 2*x^3 - 5*x^2) = ... + (( -55*x^2) * (x^2 + 2*x + 5) + 0
C5[2] =        4*x^7 + 8*x^6 + 20*x^5 + 75*x^3 + 374*x^2 + 375*x = (   -4*x^2) * (-x^5 - 2*x^4 - 5*x^3 - 56) +  75 * (   x^3 + 2*x^2 + 5*x) = ... + ((    75*x) * (x^2 + 2*x + 5) + 0
C5[3] =           2*x^6 + 4*x^5 + 10*x^4 + 125*x^2 + 362*x + 625 = (     -2*x) * (-x^5 - 2*x^4 - 5*x^3 - 56) + 125 * (       x^2 + 2*x + 5) = ... + ((     125) * (x^2 + 2*x + 5) + 0
C5[4] =   x^9 + 2*x^8 + 5*x^7 + 24*x^5 + 104*x^4 + 120*x^3 - 196 = (-x^4 - 24) * (-x^5 - 2*x^4 - 5*x^3 - 56) + 125 * (             -308/25) = ... + ((       0) * (x^2 + 2*x + 5) + -1540
C5[5] =          -x^8 - 2*x^7 - 5*x^6 - 10*x^4 - 76*x^3 - 50*x^2 = (      x^3) * (-x^5 - 2*x^4 - 5*x^3 - 56) +  10 * (-x^4 - 2*x^3 - 5*x^2) = ... + (( -10*x^2) * (x^2 + 2*x + 5) + 0
C5[6] =      -3*x^7 - 6*x^6 - 15*x^5 - 100*x^3 - 368*x^2 - 500*x = (    3*x^2) * (-x^5 - 2*x^4 - 5*x^3 - 56) + 100 * (  -x^3 - 2*x^2 - 5*x) = ... + ((  -100*x) * (x^2 + 2*x + 5) + 0
C5[7] =       11*x^6 + 22*x^5 + 55*x^4 + 250*x^2 + 1116*x + 1250 = (    -11*x) * (-x^5 - 2*x^4 - 5*x^3 - 56) + 250 * (       x^2 + 2*x + 5) = ... + ((     250) * (x^2 + 2*x + 5) + 0
C5[8] =                           -7*x^5 - 14*x^4 - 35*x^3 - 392 = (        7) * (-x^5 - 2*x^4 - 5*x^3 - 56) + 250 * (                   0) = ... + ((       0) * (x^2 + 2*x + 5) + 0

(7*p^7 - 11*p^6*z + 3*p^5*z^2 + p^4*z^3 - p^3*z^4 - 24*p^3 - 2*p^2*z - 4*p*z^2 + 2*z^3) * (-x^5 - 2*x^4 - 5*x^3 - 56) + (250*p^6 - 100*p^5*z - 10*p^4*z^2 + 125*p^2 + 75*p*z - 55*z^2) * (x^2 + 2*x + 5) + (-1540*p^3)

    9*exp(u) + 34*S + 34*M + 13 Frobenius + 10 conjugations
    """
    p = m.parent().characteristic()
    # 1. (x^2 + 2*x + 5) = x^2 + 2*(x+2) + 1
    mu = m**u                              # exp(u)
    mu2 = mu**u                            # exp(u)
    m2 = m**2
    m4 = m2**2
    mc = mu2 * mu**2 * m4 * m              # 3M + 3S

    # 2.  -(x^5 + 2*x^4 + 5*x^3 + 56) = -(x^3*(x^2 + 2*x + 5) + 56)
    # 56 = 2*28 and 28 = 32 - 4
    m8 = m4**2
    m32 = (m8**2)**2                       # 2S
    m28 = m32 * inversion_easy_gfp16(m4)   # M
    m56 = m28**2                           # S

    mcu = mc**u
    mcu2 = mcu**u
    md = mcu2**u * m56                     # 3*exp(u) + M
    md = inversion_easy_gfp16(md)
    #assert md == m**(-(u**5 + 2*u**4 + 5*u**3 + 56))

    # 3. 7*p^7 - 11*p^6*x + 3*p^5*x^2 + p^4*x^3 - p^3*x^4 - 24*p^3 - 2*p^2*x - 4*p*x^2 + 2*x^3
    #    p^4 * (7*p^3 - 11*p^2*x + 3*p*x^2 + x^3) - p^3*x^4 - 24*p^3 - 2*p^2*x - 4*p*x^2 + 2*x^3
    mdu = md**u
    mdu2 = mdu**u
    mdu3 = mdu2**u
    mdu4 = mdu3**u
    mdu2_2= mdu2**2
    # 11  = 8 + 4 - 1 = 8+2+1 = 1011
    mdu_11= ((mdu**2)**2 * mdu)**2 * mdu
    md4 = (md**2)**2
    md8 = md4**2
    mm = (mdu3 * inversion_easy_gfp16((mdu2_2).frobenius() * mdu.frobenius(2) * (md8 * md4).frobenius(3)))**2 * inversion_easy_gfp16(mdu4.frobenius(3))
    mn = mdu3 * (mdu2_2 * mdu2).frobenius() * inversion_easy_gfp16((mdu_11).frobenius(2)) * (md8 * inversion_easy_gfp16(md)).frobenius(3)
    mf = mm * mn.frobenius(4)
    #assert mf == md ** (p**4 * (7*p**3 - 11*p**2*u + 3*p*u**2 + u**3) - p**3*u**4 - 24*p**3 - 2*p**2*u - 4*p*u**2 + 2*u**3)

    # 4. (250*p^6 - 100*p^5*x - 10*p^4*x^2 + 125*p^2 + 75*p*x - 55*x^2)
    #= 5*(50*p^6 - 20*p^5*x - 2*p^4*x^2 + 25*p^2 + 15*p*x - 11*x^2)
    #= 5*(2*(25*p^2 - 10*p*x - x^2)*p^4 + 25*p^2 + 15*p*x - 11*x^2)
    #(250*p^6 - 100*p^5*z - 10*p^4*z^2 + 125*p^2 + 75*p*z - 55*z^2) eq 5*(2*(25*p^2 - 10*p*z - z^2)*p^4 + 25*p^2 + 15*p*z - 11*z^2)

    # 11 = 1011 in binary
    mcu2_11 = ((mcu2**2)**2 * mcu2)**2 * mcu2 # 3 S + 2M
    # 5*(5*p^2 + 3*p*x)
    # 5 = 101 in bits 5 = 4+1 + 4+2-1
    # 25 = 11001
    mc_25 = (((mc**2 * mc)**2)**2)**2 * mc
    # 15 = 16-1 = 1111 = 10000 - 1
    # 10 = 8+2 = 1010
    mcu_2 = mcu**2
    mcu_8 = (mcu_2**2)**2
    mcu_10 = mcu_8 * mcu_2
    mcu_15 = mcu_8**2 * inversion_easy_gfp16(mcu)

    mc_25_p2 = mc_25.frobenius(2)
    me0 = (mc_25_p2 * mcu_15.frobenius() * inversion_easy_gfp16(mcu2_11))
    me1 = ((mc_25_p2 * inversion_easy_gfp16(mcu_10.frobenius() * mcu2))**2).frobenius(4)
    #assert me0 == mc**(25*p**2 + 15*p*u - 11*u**2)
    #assert me1 == mc**(2*(25*p**2 - 10*p*u - u**2)*p**4)
    me = me1 * me0
    # me^5
    me = (me**2)**2 * me
    #assert me == mc**(250*p**6 - 100*p**5*u - 10*p**4*u**2 + 125*p**2 + 75*p*u - 55*u**2)

    # 1540 = 28 * 55
    # 56 = 2*28
    # 55 = 64 - 8 - 1
    m28_8 = (m56**2)**2
    m28_64 = ((m28_8**2)**2)**2
    m1540 = inversion_easy_gfp16(m28_64) * m28_8 * m28

    return me * mf * m1540.frobenius(3)

def final_exp_hard_kss16_v3(m, u):
    """
    Another final exp hard whose operation schedule is inspired from the technique with gg20a, gg20b
    See also final_exp_hard_kss16_v4
    Note that the curve cofactor is c(u) = 125/2*(x^2 + 2*x + 5)
    Obtain the LLL reduced matrix of coefficients like in Fuentes et al. at SAC'11.
    Then factor a multiple of the cofactor u^i*c(u) + some constant, and a scond time factor c(u)
    One obtains, with the 1st row of the LLL-reduced matrix:
    ee = (u^5 + 2*u^4 + 5*u^3 + 56)*(u^4*q^7 + u^3*(1 - 2*q^4) + u^2*q*(3 + 4*q^4) + u*q^2*(-11 + 2*q^4) + q^3*(7 + 24*q^4)) \
         + (u^2 + 2*u + 5)         *(       125*q^2*(q^4 - 2) + 25*u*q*(3*q^4 + 4) + 5*u^2*(-11*q^4 + 2)) - 1540*q^7
    ee == (2*u^7 + 48*u^3)/125 * (q^8+1)/r

    ma = m^(u^2 + 2*u + 5)
    mb = m^(u^5 + 2*u^4 + 5*u^3 + 56) = ma^(u^3) * m^56
    56 == 64 - 8
    1540 == 2^10 + 2^9 + 2^2
    1540 11000000100
    56   0000100-000

    cost 2 exp(u-1) + 7 exp(u) + 29 S + 30 M + 10 frob(4) + 4 frob
    """
    #q = m.parent().characteristic()
    m4 = (m**2)**2
    m8 = m4**2
    m32 = ((m8)**2)**2
    m64 = m32**2
    m56 = m64 * m8.conjugate()
    # assert m56 == m**56
    #m512 = (((m64)**2)**2)**2
    #m1024 = m512**2
    #m1540 = m1024 * m512 * m4
    # assert m1540 == m**1540
    # 6 S + M
    u1 = abs(u+1)
    ma = (m**u1)**u1 * m4
    u_ = abs(u)
    mau = ma**u_
    mauu = mau**u_
    mauuu = mauu**u_
    if u < 0:
        mau = mau.conjugate()
        mauuu = mauuu.conjugate()
    mb = mauuu * m56

    mbu = mb**u_
    mbuu = mbu**u_
    mbuuu = mbuu**u_
    mbuuuu = mbuuu**u_
    if u < 0:
        mbu = mbu.conjugate()
        mbuuu = mbuuu.conjugate()
    # mb^(q^3*(7 + 24*q^4)) 7 = 8-1 = 0100-, 24 = 16+8 = 1100
    mb1r = mb.frobenius(4)
    #mb1 = (((mb1r**2 * mb1r * mb)**2)**2)**2 * mb.conjugate()
    # assert mb1 == mb**(7 + 24*q**4)
    #mb1 = mb1.frobenius(3)
    # assert mb1 == mb**(q**3*(7 + 24*q**4))
    # mutualise further m^(-1540*q^7) and mb^(u^4*q^7), mb^((7 + 24*q^4)*q^3) -> (m^(-1540*q^4) * mb^(7 + 24*q^4) * mb^(u^4*q^4))^(q^3)
    # 7 = 8-1
    # 24 = 16+8
    # 1540 = 1024 + 512 + 4
    # it costs: 6M + 4 S + 2 Frob(4) and can replace 6 M + 8 S
    m1540_mb7_24q4 = (((((m64 * m32).frobenius(4).conjugate() * mb1r)**2 * mb1r * mb)**2 * m.frobenius(4).conjugate())**2)**2 * mb.conjugate()
    #assert m1540_mb7_24q4 == m**(-1540*q**4) * mb**(7 + 24*q**4)
    m1540_mb7_24q4 = m1540_mb7_24q4 * mbuuuu.frobenius(4)
    m1540_mb7_24q4 = m1540_mb7_24q4.frobenius(3)
    # 10 S + 10 M
    # ma^(5*u^2*(2 - 11*q^4)) * mb^(u*q^2*(2*q^4 - 11)) where -11 = -12 + 1 = -8 -4 +1 = -(8+4 -1)
    mauu5 = (mauu**2)**2 * mauu
    # assert mauu5 == ma**(5*u**2)
    mbuq = mbu.frobenius(2)
    # assert mbuq == mb**(u*q**2)
    f1 = mauu5 * mbuq.frobenius(4)
    f2 = mauu5.frobenius(4) * mbuq
    mab2 = ((f2**2 * f2).conjugate()**2 * f1)**2 * f2
    # assert mab2 == ma**(5*u**2*(2 - 11*q**4)) * mb**(u*q**2*(2*q**4 - 11))
    # (ma^(25*u*(4 + 3*q^4)) * mb^(u^2*(4*q^4 + 3)))^q
    # 25 = 24 + 1 = 16 + 8 + 1
    mau1 = (((mau**2 * mau)**2)**2)**2 * mau
    # assert mau1 == mau**25
    f1 = mau1 * mbuu.frobenius(4)
    f2 = mau1.frobenius(4) * mbuu
    mab3 = ((f1 * f2)**2)**2 * f2.conjugate()
    mab3 = mab3.frobenius()
    # assert mab3 == (ma**(25*u*(4 + 3*q**4)) * mb**(u**2*(4*q**4 + 3)))**q
    # ma^(125*q^2*(-2 + q^4)) * mb^(u^3*(-2*q^4 + 1))
    # 125 = 128-2-1 = 128 - 4 + 1
    ma1 = ((((((ma**2)**2)**2)**2)**2 * ma.conjugate())**2)**2 * ma
    ma1 = ma1.frobenius(2)
    f1 = (ma1 * mbuuu.frobenius(4)).conjugate()
    f2 = ma1.frobenius(4) * mbuuu
    mab4 = f1**2 * f2
    # 29 S + 27 M
    #return mb1 * mab2 * mab3 * mab4 * (mbuuuu * m1540.conjugate()).frobenius(7)
    return m1540_mb7_24q4 * mab2 * mab3 * mab4

def final_exp_hard_kss16_v4(m, u):
    """
    Another final exp hard whose operation schedule is inspired from the technique with gg20a, gg20b
    See also final_exp_hard_kss16_v3
    Note that the curve cofactor is c(u) = 125/2*(x^2 + 2*x + 5)
    Obtain the LLL reduced matrix of coefficients like in Fuentes et al. at SAC'11.
    Then factor a multiple of the cofactor u^i*c(u) + some constant, and a scond time factor c(u)
    One obtains, with the 1st row of the LLL-reduced matrix:
    ee = (u^5 + 2*u^4 + 5*u^3 + 56)*(u^4*q^7 + u^3*(1 - 2*q^4) + u^2*q*(3 + 4*q^4) + u*q^2*(-11 + 2*q^4) + q^3*(7 + 24*q^4)) \
         + 5*((u^2 + 2*u + 5)*(u^2*(2 - 11*q^4) + 5*u*q*(4 + 3*q^4) + 25*q^2*(-2 + q^4)) - 308*q^7)
    ee == (2*u^7 + 48*u^3)/125 * (q^8+1)/r

    ma = m^(u^2 + 2*u + 5)
    mb = m^(u^5 + 2*u^4 + 5*u^3 + 56) = ma^(u^3) * m^56
    56 == 64 - 8
    308 == 256 + 32 + 16 + 4
    308  100110100
    56   00100-000

    cost 2 exp(u-1) + 7 exp(u) + 30 S + 32 M + 7 frob(4) + 6 frob
    """
    # q = m.parent().characteristic()
    m4 = (m**2)**2
    m8 = m4**2
    m16 = m8**2
    m32 = m16**2
    m64 = m32**2
    m56 = m64 * m8.conjugate()
    # assert m56 == m**56
    m256 = ((m64)**2)**2
    m308 = m256 * m32 * m16 * m4
    # assert m308 == m**308

    u1 = abs(u+1)
    ma = (m**u1)**u1 * m4
    # 5*q^2*(-2 + q^4)
    ma1 = ma.conjugate()**2 * ma.frobenius(4)
    ma1 = ma1.frobenius(2)
    ma1 = (ma1**2)**2 * ma1
    # assert ma1 == ma**(5*q**2*(-2 + q**4))

    u_ = abs(u)
    mau = ma**u_
    mauu = mau**u_
    mauuu = mauu**u_
    if u < 0:
        mau = mau.conjugate()
        mauuu = mauuu.conjugate()
    # u*q*(4 + 3*q^4)
    mauq = mau.frobenius(4)
    ma2 = ((mau * mauq)**2)**2 * mauq.conjugate()
    ma2 = ma2.frobenius()
    # assert ma2 == ma**(u*q*(4 + 3*q**4))
    # power 5
    ma12 = ma1 * ma2
    ma12 = (ma12**2)**2 * ma12

    # u^2*(2 - 11*q^4) where -11 = -8 - 4 + 1
    mauuq = mauu.frobenius(4)
    ma3 = ((mauuq**2 * mauuq).conjugate()**2 * mauu)**2 * mauuq
    # assert ma3 == ma**(u**2*(2 - 11*q**4))

    ma123 = ma3 * ma12
    ma123 = ma123 * m308.frobenius(7).conjugate()
    # power 5
    ma123 = (ma123**2)**2 * ma123
    # assert ma123 == m**(5*((u**2 + 2*u + 5)*(u**2*(2 - 11*q**4) + 5*u*q*(4 + 3*q**4) + 25*q**2*(-2 + q**4)) - 308*q**7))

    mb = mauuu * m56
    # assert mb == m**(u**5 + 2*u**4 + 5*u**3 + 56)
    # mb^(q^3*(7 + 24*q^4)) 7 = 8-1 = 0100-, 24 = 16+8 = 1100
    mbq = mb.frobenius(4)
    mb1 = (((mbq**2 * mbq * mb)**2)**2)**2 * mb.conjugate()
    # assert mb1 == mb**(7 + 24*q**4)
    mb1 = mb1.frobenius(3)
    # assert mb1 == mb**(q**3*(7 + 24*q**4))

    mbu = mb**u_
    mbuu = mbu**u_
    mbuuu = mbuu**u_
    mbuuuu = mbuuu**u_
    if u < 0:
        mbu = mbu.conjugate()
        mbuuu = mbuuu.conjugate()

    # mb^(u*q^2*(2*q^4 - 11)) where -11 = -12 + 1 = -8 -4 +1 = -(8+4 -1)
    mb2 = mbu.frobenius(2)
    mb2 = ((mb2**2 * mb2).conjugate()**2 * mb2.frobenius(4))**2 * mb2
    # assert mb2 == mb**(u*q**2*(2*q**4 - 11))

    # mb^(u^2*q*(4*q^4 + 3))
    mb3 = ((mbuu.frobenius(4) * mbuu)**2)**2 * mbuu.conjugate()
    mb3 = mb3.frobenius()
    # assert mb3 == mb**(u**2*q*(4*q**4 + 3))

    # mb^(u^3*(-2*q^4 + 1))
    mb4 = mbuuu.frobenius(4).conjugate()**2 * mbuuu
    # assert mb4 == mb**(u**3*(-2*q**4 + 1))

    mb5 = mbuuuu.frobenius(7)
    # assert mb5 == mb**(u**4*q**7)

    # assert mb1 * mb2 * mb3 * mb4 * mb5 == mb**((u**4*q**7 + u**3*(1 - 2*q**4) + u**2*q*(3 + 4*q**4) + u*q**2*(-11 + 2*q**4) + q**3*(7 + 24*q**4)))
    # assert mb1 * mb2 * mb3 * mb4 * mb5 == m**((u**5 + 2*u**4 + 5*u**3 + 56)*(u**4*q**7 + u**3*(1 - 2*q**4) + u**2*q*(3 + 4*q**4) + u*q**2*(-11 + 2*q**4) + q**3*(7 + 24*q**4)))

    return mb1 * mb2 * mb3 * mb4 * mb5 * ma123

### Group operations
"""
G1 order: rx =1/61250*(x^8 + 48*x^4 + 625)
G1 cofactor: 125/2*(x^2 + 2*x + 5)
G1 eigenvalue lambda mod r: 1/7*(x^4 + 24)
G1 eigenvalue lambda mod c: 1/2*(x + 1)
G2 cofactor: 1/15059072*(x^32 + 8*x^31 + 44*x^30 + 152*x^29 + 550*x^28 + 2136*x^27 + 8780*x^26 + 28936*x^25 + 83108*x^24 + 236072*x^23 + 754020*x^22 + 2287480*x^21 + 5986066*x^20 + 14139064*x^19 + 35932740*x^18 + 97017000*x^17 + 237924870*x^16 + 498534968*x^15 + 1023955620*x^14 + 2353482920*x^13 + 5383092978*x^12 + 10357467880*x^11 + 17391227652*x^10 + 31819075896*x^9 + 65442538660*x^8 + 117077934360*x^7 + 162104974700*x^6 + 208762740168*x^5 + 338870825094*x^4 + 552745197960*x^3 + 632358687500*x^2 + 414961135000*x + 126854087873)
G2 eigenvalue lambda mod r:  1/35*(2*x^5 + 41*x)
G2 eigenvalue lambda mod c2: polynomial of large coeffs and degree 31
G2 eigenvalue not reduced:   polynomial of large coeffs and degree 39

[-1  0  0  0  2  0  0  x]
[ 0  0  0  2  0  0  x  1]
[ 0  0  2  0  0  x  1  0]
[ 0  2  0  0  x  1  0  0]
[ 2  0  0  x  1  0  0  0]
[ 0  0  x  1  0  0  0 -2]
[ 0  x  1  0  0  0 -2  0]
[ x  1  0  0  0 -2  0  0]
"""

def cofactor_clearing_g1_kss16(P, u, omega=None):
    """
    cofactor clearing with endomorphism on G1
    INPUT:
    -`P`: point on a KSS16 curve E
    -`u`: seed for the curve parameters
    -`omega`: sqrt(-1) mod p

    The cofactor is c(x) = 125/2*(x^2 + 2*x + 5) and note that with x=25,45 mod 70, then 5 | x
    The endomorphism is psi(P) = (-xP, yP*omega) where omega=sqrt(-1) is a primitive quartic root of unity mod p
    It has eigenvalue (x+1)/2 mod c(x) -> (x+1)^2/4 + 1 = (x^2+2x+1+ 4)/4 = (x^2 + 2x + 5)/4 = 0 mod cx
    The other eigenvalue is -(x+1)/2
    But actually this is mod (x^2+2x+5)/4 which is 2*cx/125

    with x=70*s+25: c(x) = 1250*(245*s^2 + 182*s + 34), lambc(x) = 35*s + 13, lambc^2 + 1 = 5*(245*s^2 + 182*s + 34) = c/250
    with x=70*s+45: c(x) = 1250*(245*s^2 + 322*s + 106), lambc(x) = 35*s + 23, lambc^2 + 1 = 5*(245*s^2 + 322*s + 106) = c/250
    
    Finally there is the rational torsion: the 2-torsion is fully rational.
    It does not work with P -> [250]P only, [1250]P is required and I cannot explain why.
    
    A fast cofactor multiplication is then
    P -> R := [1250]P -> R + [lambda] phi(R)
    where lambda is (u+1)/2

    it assumes that lambda = (u+1)/2 and computes 1250*(P + [(u+1)/2]phi(P))
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((u**9-11*u**8-16*u**7-120*u**6-32*u**5-498*u**4-748*u**3-2740*u**2-3115*u-5651)/4018)
        # this is a rational, not an integer, do not use // but use /
    # 250, 500, 625 is not enough, 1250 is fine.
    #P = 1250*P
    P = 2*P
    phiP = P.curve()(-P[0], P[1]*omega, P[2])
    P = P + 182*phiP # assuming the eigenvalue of phi mod 5 is 2 (->182 mod 625), the other one is 3 (-> -182 mod 625)
    # maybe P was of order 125, P could be 0 here... include the third coordinate P[2] that could be 0
    phiP = P.curve()(-P[0], P[1]*omega, P[2])
    P = P + ((u+1)//2)*phiP
    return P

def cofactor_clearing_g2_kss16(Q, u, Fq4, D_twist=True, case=0):
    """
    INPUT:
    - `Q`: point on E'(Fp4) containing G2
    - `u`: seed of the KSS16 curve, u=25, 45 mod 70
    - `Fq4`: finite field extension of explicit degree 4 on top of Fq
    - `D_twist`: True/False (M_twist)

    cofactor clearing with endomorphism on G2
    G2 is supposed to be given in compressed representation over GF(p^4)
    That is, P.curve() is E'(Fp4) a degree 4 twist of E

    The endomorphism is
    psi(P) = twist o Frobenius o untwist (P)

    The eigenvalue is a root of the characteristic polynomial X^2 - t*X + p
    That is one of (t +/- y sqrt(-3))/2
    G2 has order p^4 + 1 - t4' where t4' is the trace of E', the appropriate degree 4 twist of E(Fp4)
    Let t be the trace of E(Fp), t2 = t^2-2*p and t4 = t2^2-2*p^2
    y4 = y * t * (t^2-2*p) where p = (t^2 + y^2)/4
    Then #E'(Fp4) = p^4 + 1 + y4
    c2 = 1/15059072*(x^32 + 8*x^31 + 44*x^30 + 152*x^29 + 550*x^28 + 2136*x^27 + 8780*x^26 + 28936*x^25 + 83108*x^24 + 236072*x^23 + 754020*x^22 + 2287480*x^21 + 5986066*x^20 + 14139064*x^19 + 35932740*x^18 + 97017000*x^17 + 237924870*x^16 + 498534968*x^15 + 1023955620*x^14 + 2353482920*x^13 + 5383092978*x^12 + 10357467880*x^11 + 17391227652*x^10 + 31819075896*x^9 + 65442538660*x^8 + 117077934360*x^7 + 162104974700*x^6 + 208762740168*x^5 + 338870825094*x^4 + 552745197960*x^3 + 632358687500*x^2 + 414961135000*x + 126854087873)
    reduced matrix:
    short vector for fast G2 cofactor clearing:
    [   x^3-3*x^2,  3*x^2+11*x,     -11*x-7,    2*x^3+14,-2*x^3-4*x^2,   4*x^2-2*x,      2*x+24,     x^4+x^3]
    [  3*x^2+11*x,     -11*x-7,    2*x^3+14,-2*x^3-4*x^2,   4*x^2-2*x,      2*x+24,     x^4+x^3,  -x^3+3*x^2]
    [     -11*x-7,    2*x^3+14,-2*x^3-4*x^2,   4*x^2-2*x,      2*x+24,     x^4+x^3,  -x^3+3*x^2, -3*x^2-11*x]
    [    2*x^3+14,-2*x^3-4*x^2,   4*x^2-2*x,      2*x+24,     x^4+x^3,  -x^3+3*x^2, -3*x^2-11*x,      11*x+7]
    [-2*x^3-4*x^2,   4*x^2-2*x,      2*x+24,     x^4+x^3,  -x^3+3*x^2, -3*x^2-11*x,      11*x+7,   -2*x^3-14]
    [   4*x^2-2*x,      2*x+24,     x^4+x^3,  -x^3+3*x^2, -3*x^2-11*x,      11*x+7,   -2*x^3-14, 2*x^3+4*x^2]
    [      2*x+24,     x^4+x^3,  -x^3+3*x^2, -3*x^2-11*x,      11*x+7,   -2*x^3-14, 2*x^3+4*x^2,  -4*x^2+2*x]
    [     x^4+x^3,  -x^3+3*x^2, -3*x^2-11*x,      11*x+7,   -2*x^3-14, 2*x^3+4*x^2,  -4*x^2+2*x,     -2*x-24]
    for each row [l0 l1 l2 l3 l4 l5 l6 l7] of the matrix,
    l0 + l1*L + l2*L^2 + l3*L^3 + l4*L^4 + l5*L^5 + l6*L^6 + l7*L^7
    is a multiple of c2, where L is the eigenvalue mod c2, such that L mod r = q mod r.
    """
    if Q.is_zero():
        return Q
    xi = -Fq4.modulus().constant_coefficient()
    p = Fq4.characteristic()
    mu = xi**((p-1)//4)
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 4, 1, D_twist)
    # xi**((p^2-1)//4) = mu^(p+1)
    mu2 = mu.frobenius()*mu
    # assert mu2 == xi**((p**2-1)//4)
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 4, 2, D_twist)
    # xi**((p^3-1)//4) = mu^(p^2+p+1)
    mu3 = mu.frobenius(2)*mu2
    # assert mu3 == xi**((p**3-1)//4)
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 4, 3, D_twist)
    # xi**((p^4-1)//4) = xi^((p+1)*(p-1)*(p^2+1)//4)
    #                  = mu2^(p^2+1)
    mu4 = mu2.frobenius(2)*mu2
    # assert mu4 == xi**((p**4-1)//4)
    psi4Q = endomorphism_g2_psi_p(Q, None, mu4, 4, 4, D_twist)
    # xi**((p^5-1)//4) = mu^(1+p+p^2+p^3+p^4)
    mu5 = mu4 * mu.frobenius(4)
    # assert mu5 == xi**((p**5-1)//4)
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 4, 5, D_twist)
    # xi**((p^6-1)//4) = mu^(1+p+p^2+p^3+p^4+p^5)
    #                  = xi^((p^3-1)*(p^3+1)//4)
    mu6 = mu4 * mu2.frobenius(4)
    # assert mu6 == xi**((p**6-1)//4)
    psi6Q = endomorphism_g2_psi_p(Q, None, mu6, 4, 6, D_twist)
    # xi**((p^7-1)//4) = mu^(1+p+p^2+p^3+p^4+p^5+p^6)
    mu7 = mu4 * mu3.frobenius(4)
    # assert mu7 == xi**((p**7-1)//4)
    psi7Q = endomorphism_g2_psi_p(Q, None, mu7, 4, 7, D_twist)

    if case == 0:
        return    (u**3-3*u**2)*Q +   (3*u**2+11*u)*psi1Q +       (-11*u-7)*psi2Q +     (2*u**3+14)*psi3Q +(-2*u**3-4*u**2)*psi4Q +   (4*u**2-2*u)*psi5Q +       (2*u+24)*psi6Q +    (u**4+u**3)*psi7Q
    elif case == 1:
        return    (3*u**2+11*u)*Q +       (-11*u-7)*psi1Q +     (2*u**3+14)*psi2Q +(-2*u**3-4*u**2)*psi3Q +    (4*u**2-2*u)*psi4Q +       (2*u+24)*psi5Q +    (u**4+u**3)*psi6Q + (-u**3+3*u**2)*psi7Q
    elif case == 2:
        return        (-11*u-7)*Q +     (2*u**3+14)*psi1Q +(-2*u**3-4*u**2)*psi2Q +    (4*u**2-2*u)*psi3Q +        (2*u+24)*psi4Q +    (u**4+u**3)*psi5Q + (-u**3+3*u**2)*psi6Q + (-3*u**2-11*u)*psi7Q
    elif case == 3:
        return      (2*u**3+14)*Q +(-2*u**3-4*u**2)*psi1Q +    (4*u**2-2*u)*psi2Q +        (2*u+24)*psi3Q +     (u**4+u**3)*psi4Q + (-u**3+3*u**2)*psi5Q + (-3*u**2-11*u)*psi6Q +       (11*u+7)*psi7Q
    elif case == 4:
        return (-2*u**3-4*u**2)*Q +    (4*u**2-2*u)*psi1Q +        (2*u+24)*psi2Q +     (u**4+u**3)*psi3Q +  (-u**3+3*u**2)*psi4Q + (-3*u**2-11*u)*psi5Q +       (11*u+7)*psi6Q +   (-2*u**3-14)*psi7Q
    elif case == 5:
        return     (4*u**2-2*u)*Q +        (2*u+24)*psi1Q +     (u**4+u**3)*psi2Q +  (-u**3+3*u**2)*psi3Q +  (-3*u**2-11*u)*psi4Q +       (11*u+7)*psi5Q +   (-2*u**3-14)*psi6Q +(2*u**3+4*u**2)*psi7Q
    elif case == 6:
        return         (2*u+24)*Q +     (u**4+u**3)*psi1Q +  (-u**3+3*u**2)*psi2Q +  (-3*u**2-11*u)*psi3Q +        (11*u+7)*psi4Q +   (-2*u**3-14)*psi5Q +(2*u**3+4*u**2)*psi6Q +  (-4*u**2+2*u)*psi7Q
    elif case == 7:
        return      (u**4+u**3)*Q +  (-u**3+3*u**2)*psi1Q +  (-3*u**2-11*u)*psi2Q +        (11*u+7)*psi3Q +    (-2*u**3-14)*psi4Q +(2*u**3+4*u**2)*psi5Q +  (-4*u**2+2*u)*psi6Q +      (-2*u-24)*psi7Q

def membership_testing_g1_kss16(P, u, omega=None):
    """
    test if P belongs to G1 <=> P has order r
    INPUT:
    -`P`: point on KSS16 curve E(Fp)
    -`u`: seed for the curve parameters
    -`omega`: sqrt(-1) mod p, such that (-x, y*omega) has eigenvalue (u^4+24)/7 mod r, (u+1)/2 mod c/1250

    The order of G1 is r(x) =1/61250*(x^8 + 48*x^4 + 625) where x=25,45 mod 70, 61250 = 2 * 5^4 * 7^2
    The endomorphism is phi(P) = (-xP, yP*omega) where omega=sqrt(-1) is a primitive quartic root of unity mod p
    It has eigenvalue lambda = (x^4 + 24)/7 mod r(x) -> (x^4 + 24)^2/7^2 + 1 = (x^8 + 48*x^4 + 625)/49 = rx * 2 * 5^4
    A short vector is (a0, a1) = ((-443*(x/5)^4-17)/14, ((x/5)^4+5)/14) s.t. a0 + a1*lambda == r (exact equality)
    (a0+a1*X).resultant(X^2+1) = a0^2 + a1^2 == 157*r
    a0 = -443*a1 + 157
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((u**9-11*u**8-16*u**7-120*u**6-32*u**5-498*u**4-748*u**3-2740*u**2-3115*u-5651)/4018)
    a1 = ((u//5)**4 + 5)//14 # it is an integer by definition of u= 25, 45 mod 70
    P1 = a1*P
    phiP1 = P.curve()((-P1[0], P1[1]*omega, P1[2]))
    P0 = -443*P1 + 157*P
    return (P0 + phiP1).is_zero()

def membership_testing_g2_kss16_u25mod70(Q, u, Fq4, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^k/4, a quartic twist of E(Fq)
    - `u`: curve seed
    - `Fq4`: Finite field extension of degree 4 on top of Fq = Fp4
    - `D_twist`: True/False

    formula
    s = (u-25)/70
    v = [27*s+10, 3*s+2, 15*s+6, 13*s+5, 19*s+7, 21*s+7, 5*s+2, s]
    """
    assert ((u-25) % 70) == 0
    s = (u-25)//70
    
    if Q.is_zero():
        return Q
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

    return ((27*s+10)*Q + (3*s+2)*psi1Q + (15*s+6)*psi2Q + (13*s+5)*psi3Q + (19*s+7)*psi4Q + (21*s+7)*psi5Q + (5*s+2)*psi6Q + s*psi7Q).is_zero()

def membership_testing_g2_kss16_u45mod70(Q, u, Fq4, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^k/4, a quartic twist of E(Fq)
    - `u`: curve seed
    - `Fq4`: Finite field extension of degree 4 on top of Fq = Fp4
    - `D_twist`: True/False

    formula
    s = (x-45)/70
    v = [29*s+19, 3*s+3, 27*s+18, 13*s+9, 23*s+15, 21*s+13, 9*s+6, s]
    """
    assert ((u-45) % 70) == 0
    s = (u-45)//70
    
    if Q.is_zero():
        return Q
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

    return ((29*s+19)*Q + (3*s+3)*psi1Q + (27*s+18)*psi2Q + (13*s+9)*psi3Q + (23*s+15)*psi4Q + (21*s+13)*psi5Q + (9*s+6)*psi6Q + s*psi7Q).is_zero()

def membership_testing_g2_kss16_u45mod70_yudai(Q, u, Fq4, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^k/4, a quartic twist of E(Fq)
    - `u`: curve seed, u=45 mod 70
    - `Fq4`: Finite field extension of degree 4 on top of Fq = Fp4
    - `D_twist`: True/False

    formula
    u_330 = -2**34 +2**27 -2**23 +2**20 -2**11 +1 # 45 mod 70
    (u_330 % 70) == 45
    s = (-u-25)/70
    v = [11*s+4, -9*s-3, 3*s+1, 3*s+1, -13*s-5, 7*s+3, s, 11*s+4]
    """
    assert ((u-45) % 70) == 0
    s = (-u-25)//70

    if Q.is_zero():
        return Q
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

    return ((11*s+4)*Q - (9*s+3)*psi1Q + (3*s+1)*psi2Q + (3*s+1)*psi3Q - (13*s+5)*psi4Q + (7*s+3)*psi5Q + s*psi6Q + (11*s+4)*psi7Q).is_zero()
