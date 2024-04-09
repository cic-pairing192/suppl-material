"""
date: September 2023

Implementation of pairing on Gasnier-Guillevic new curves with k=20 and D=1.
The final exponentiation is optimized.
"""
from pairing import *
from sage.rings.integer_ring import ZZ

def miller_loop_opt_ate_gg20a(Q, P, a, u):
    """
    The first GG20 family (GG20a)
    generic formula: x - qx + 2*qx^6
    Miller loop f_{u,Q}(P) f_{2,\pi_q6(Q)}(P) l_{uQ, -\pi(Q)}(P)
       where u can be positive or negative
    the formula is (x - qx + 2*qx^6) = 0 mod rx so the pairing equation is
    f_{u,Q}(P) f_{2,pi_q6(Q)}(P) l_{[u]Q,\pi(-Q)}(P) l_{uQ-\pi(Q), \pi_6([2]Q)}(P)
    --> it is not necessary to do the second line as it will be a vertical
    (it is possible to make a different choice of lines to implement)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters, non-zero integer in ZZ

    The curve coefficient b is zero.
    """
    PP = (P[0], P[1])
    m, uQ = miller_function_ate(Q, PP, a, u, m0=1)
    piQ_ = [(Q[0]).frobenius(), -(Q[1]).frobenius()]
    pi6Q = [(Q[0]).frobenius(6), (Q[1]).frobenius(6)]
    l2, Q2 = double_line_affine_j(pi6Q, PP, a)
    l3, Q3 = add_line_j(uQ, piQ_, PP)

    return m * l2 * l3

def final_exp_hard_gg20a_v0(m, u):
    """
    Final exponentiation, hard part, on the 1st family of GG20 curves (GG20a)
    INPUT:
    - `m`: element in Fp^20 where a Frobenius map is allowed in SageMath
    - `u`: seed, such that u = 1715 or 1815 mod 2050 that is,
           u=1 mod 2, u=0 mod 5, u=11 or 34 mod 41, and (q-1)/5 is integer (u=15 mod 25).

    Phi_20(q) = q^8 - q^6 + q^4 - q^2 + 1 -> q^8 = q^6 - q^4 + q^2 - 1

    A first non-optimized solution, as suggested in
    https://eprint.iacr.org/2020/875
    using the curve cofactor cx(u), write
    exponent_hard = Phi_20(px)/rx = (px^8 - px^6 + px^4 - px^2 + 1)/rx
    = cx * (px^7 + l6*px^6 + l5*px^5 + l4*px^4 + l3*px^3 + l2*px^2 + l1*px + l0)
      + i6*px^6 + i5*px^5 + i4*px^4 + i3*px^3 + i2*px^2 + i1*px + i0
    where
    cx = 125*(x**4 - 6*x**3 + 18*x**2 - 30*x + 25)/164
    rx = (x**8 + 4*x**7 + 11*x**6 + 24*x**5 + 41*x**4 + 120*x**3 + 275*x**2 + 500*x + 625)/25625
    qx = (x**12 - 2*x**11 + 5*x**10 + 76*x**7 + 176*x**6 + 380*x**5 + 3125*x**2 + 12938*x + 15625)/33620
    tx = (2*x**6 + 117*x + 205)/205
    assert (cyclotomic_polynomial(20)(qx) % rx) == 0
    exponent = cyclotomic_polynomial(20)(qx)//rx
    41*exponent == (cx/125) * (41*125*qx^7 \
    + 25*(2*x^6 + 117*x + 656)*qx^6 \
    + 5*(4*x^7 + 29*x^2 + 1312*x + 1599)*qx^5 \
    + (8*x^7 - 28*x^6 + 48*x^5 + 82*x^4 - 287*x^3 + 550*x^2 + 699*x - 2686)*qx^4 \
    + (-44*x^7 - 96*x^6 - 264*x^5 - 451*x^4 - 984*x^3 - 3025*x^2 - 21032*x - 67227)*qx^3 \
    + (-8*x^7 + 28*x^6 + 77*x^5 - 82*x^4 + 287*x^3 - 550*x^2 - 699*x + 7436)*qx^2 \
    + (44*x^7 + 121*x^6 + 264*x^5 + 451*x^4 + 984*x^3 + 3025*x^2 + 19932*x + 75427)*qx \
    + (-7*x^7 - 28*x^6 - 77*x^5 + 82*x^4 - 287*x^3 - 840*x^2 - 4221*x - 17276)) \
    + 25*4*(2*x^3 - 13*x^2 + 30*x - 25)*qx^6 \
    + 5*2*(-4*x^3 - 24*x^2 + 140*x - 241)*qx^5 \
    + 2*(-16*x^3 + 206*x^2 - 935*x + 2268)*qx^4 \
    + 2*(-412*x^3 + 2117*x^2 - 4920*x + 4026)*qx^3 \
    + 2*(141*x^3 - 706*x^2 + 1560*x - 2268)*qx^2 \
    + 2*(462*x^3 - 2442*x^2 + 5670*x - 4651)*qx \
    + (-252*x^3 + 1592*x^2 - 4170*x + 3781)

    cost: more than 11*exp(u) + 13*frob + many M
    """
    r = ZZ((u**8 + 4*u**7 + 11*u**6 + 24*u**5 + 41*u**4 + 120*u**3 + 275*u**2 + 500*u + 625)//25625)
    c0 = ZZ(u**4 - 6*u**3 + 18*u**2 - 30*u + 25)
    assert c0 == (u**2 - 2*u + 5) * (u**2 - 4*u + 5)
    assert (c0 % ZZ(164)) == 0
    c0 = c0 // ZZ(164) # forget the factor 125 here
    l7 = ZZ(41*125)
    l6 = ZZ(25*(2*u**6 + 117*u + 656))
    l5 = ZZ(5*(4*u**7 + 29*u**2 + 1312*u + 1599))
    l4 = ZZ(8*u**7 - 28*u**6 + 48*u**5 + 82*u**4 - 287*u**3 + 550*u**2 + 699*u - 2686)
    l3 = ZZ(-(44*u**7 + 96*u**6 + 264*u**5 + 451*u**4 + 984*u**3 + 3025*u**2 + 21032*u + 67227))
    l2 = ZZ(-8*u**7 + 28*u**6 + 77*u**5 - 82*u**4 + 287*u**3 - 550*u**2 - 699*u + 7436)
    l1 = ZZ(44*u**7 + 121*u**6 + 264*u**5 + 451*u**4 + 984*u**3 + 3025*u**2 + 19932*u + 75427)
    l0 = ZZ(-(7*u**7 + 28*u**6 + 77*u**5 - 82*u**4 + 287*u**3 + 840*u**2 + 4221*u + 17276))

    i6 = ZZ(25*4*(2*u**3 - 13*u**2 + 30*u - 25))
    assert i6 == 25*4*(2*u - 5) * (u**2 - 4*u + 5)
    i5 = ZZ(5*2*(-4*u**3 - 24*u**2 + 140*u - 241))
    i4 = ZZ(2*(-16*u**3 + 206*u**2 - 935*u + 2268))
    i3 = ZZ(2*(-412*u**3 + 2117*u**2 - 4920*u + 4026))
    i2 = ZZ(2*(141*u**3 - 706*u**2 + 1560*u - 2268))
    i1 = ZZ(2*(462*u**3 - 2442*u**2 + 5670*u - 4651))
    i0 = ZZ((-252*u**3 + 1592*u**2 - 4170*u + 3781))

    p = m.parent().characteristic()
    p = ZZ(p)
    e1 = (l7*p**7 + l6*p**6 + l5*p**5 + l4*p**4 + l3*p**3 + l2*p**2 + l1*p + l0)
    e0 = (i6*p**6 + i5*p**5 + i4*p**4 + i3*p**3 + i2*p**2 + i1*p + i0)
    assert ZZ(e0 + e1*c0) == ZZ(41*(p**8 - p**6 + p**4 - p**2 + 1)//r)

    f = m**l7
    f = f.frobenius() * m**l6
    f = f.frobenius() * m**l5
    f = f.frobenius() * m**l4
    f = f.frobenius() * m**l3
    f = f.frobenius() * m**l2
    f = f.frobenius() * m**l1
    f = f.frobenius() * m**l0
    assert f == m**e1
    f = f**c0

    g = m**i6
    g = g.frobenius() * m**i5
    g = g.frobenius() * m**i4
    g = g.frobenius() * m**i3
    g = g.frobenius() * m**i2
    g = g.frobenius() * m**i1
    g = g.frobenius() * m**i0
    assert g == m**e0
    
    return f * g

def final_exp_hard_gg20a_v1(m, u):
    """
    Final exponentiation, hard part, on the 1st family of GG20 curves (GG20a)
    INPUT:
    - `m`: element in Fp^20 where a Frobenius map is allowed in SageMath
    - `u`: seed, such that u = 1715 or 1815 mod 2050 that is,
           u=1 mod 2, u=0 mod 5, u=11 or 34 mod 41, and (q-1)/5 is integer (u=15 mod 25).

    Phi_20(q) = q^8 - q^6 + q^4 - q^2 + 1 -> q^8 = q^6 - q^4 + q^2 - 1
    Cost: 2 exp(u-1) + 9 exp(u) + 52 S + 43 M + 8 frob(5) + 10 frob

    e1a = (u^6 - 2*u^5 + 5*u^4 + 328)*(-41*q^2 + u*q*(7 - 24*q^5) + u^2*(11 - 2*q^5) + u^3*q^4*(4 - 3*q^5) + u^4*q^3*(2 + q^5) + u^5*q^7)
        + (u^2 - 2*u + 5) * (625*q*(2 - q^5) + 125*u*(4 + 3*q^5) + 25*u^2*q^4*(11 + 2*q^5) + 5*u^3*q^3*(7 + 24*q^5) + 38*u^4*q^7)
        + 6724*q^7
    """
    # 4*41^2 = 6724 = 0x1A44 = 0001101001000100 = 4*(2^10 + 2^9 + 2^7 + 2^4 + 1)
    #           328 =  0x148 =     000101001000 = 8 + 64 + 256 = 2^3 + 2^6 + 2^8
    #   m0 = m**6724  # 6724 = 4*41^2
    # m328 = m**328   #  328 = 8*41

    # q = m.parent().characteristic()
    m8 = ((m**2)**2)**2
    m64 = ((m8**2)**2)**2
    m256 = (m64**2)**2
    m328 = m8 * m64 * m256
    # assert m328 == m**328
    m512 = m256**2
    m0 = (m328 * m512)**2 * m
    m0 = (m0**2)**2                      # 12 S + 4 M
    # assert m0 == m**6724

    # u^2 - 2*u + 5 = (u-1)^2 + 2^2
    u1 = abs(u-1)
    ma = (m**u1)**u1 * (m**2)**2      # 2*exp(|u-1|) + M + 2S
    # assert ma == m**(u**2 - 2*u + 5)

    # with (u^2 - 2*u + 5), the exponent is
    # (q*(2 - q^5)*5^4 + u*( 4 + 3*q^5)*5^3 + u^2*q^4*(11 + 2*q^5)*5^2 + u^3*q^3*(7 + 24*q^5)*5 + 38*u^4*q^7)
    m1 = (ma.frobenius(5).conjugate() * ma**2).frobenius()
    # assert m1 == ma**(q*(2 - q**5))
    ma1 = ma**u
    ma1_ = ma1.frobenius(5)
    m2 = ((ma1 * ma1_)**2)**2 * ma1_.conjugate()
    # assert m2 == ma1**(4 + 3*q**5)
    ma2 = ma1**u
    ma2_ = ma2.frobenius(5)
    # 11 = 1011
    m3 = ((ma2**2)**2 * ma2 * ma2_)**2 * ma2
    m3 = m3.frobenius(4)
    # assert m3 == ma2**(q**4*(11 + 2*q**5))
    ma3 = ma2**u
    ma3_ = ma3.frobenius(5)
    # 7 = 111 = 100(-1)
    # 24 = 16 + 8 = 11000
    m4 = (((ma3_**2 * ma3_ * ma3)**2)**2)**2 * ma3.conjugate()
    m4 = m4.frobenius(3)
    # assert m4 == ma3**(q**3*(7 + 24*q**5))
    ma4 = ma3**u
    # 38 = 0x26 = 00100110 = 32 + 4 + 2
    m5 = ((((ma4**2)**2)**2 * ma4)**2 * ma4)**2
    m5 = m5.frobenius(7)
    # assert m5 == ma4**(38*q**7)

    mb = (m1**2)**2 * m1 * m2
    mb = (mb**2)**2 * mb * m3
    mb = (mb**2)**2 * mb * m4
    mb = (mb**2)**2 * mb * m5
    # assert mb == (((m1**5 * m2)**5 * m3)**5 * m4)**5 * m5 # exp(5) = 2*S + M -> 4*(2*S + M) + 4M = 8S + 8M

    # total mb: 15 S + 15 M + 4 frob(5) + 4 frob + 4*exp(u)
    # if sequentially: 9S + 3M + 7S + 2M + 4S + 2M + 2S + M = 22S + 8M, total 14S more
    # 5^4 = 625 = 0x271 =        001001110001 = 1 - 16 + 128 + 512 = 2^9 + 2^7 - 2^4 + 1
    # 5^3 = 125 = 0x7D =         000001111101 = 128 - 4 + 1 = 2^7 - 2^2 + 1
    # 5^2 =  25 = 0x19 =         000000011001 = 16 + 8 + 1 = 2^4 + 2^3 + 1
    # 5         = 0x5  =         000000000101 = 4 + 1 = 2^2 + 1

    # total:    37 S + 24 M + 4 frob(5) + 4 frob + 4*exp(u) + 2*exp(u-1)
    # b = (q*(2 - q**5)*5**4 + u*(4 + 3*q**5)*5**3 + u**2*q**4*(11 + 2*q**5)*5**2 + u**3*q**3*(7 + 24*q**5)*5 + 38*u**4*q**7)
    # assert b == (625*q*(2 - q**5) + 125*u*(4 + 3*q**5) + 25*u**2*q**4*(11 + 2*q**5) + 5*u**3*q**3*(7 + 24*q**5) + 38*u**4*q**7)
    # assert mb == ma**b

    ma6 = ma4 * m328
    # assert ma6 == m**(u**6 - 2*u**5 + 5*u**4 + 328)
    # and with (u^6 - 2*u^5 + 5*u^4 + 328), the exponent is
    # (-41*q^2 + u*q*(7 - 24*q^5) + u^2*(11 - 2*q^5) + u^3*q^4*(4 - 3*q^5) + u^4*q^3*(2 + q^5) + u^5*q^7)

    # 41 = 0x29 = 00101001
    m6 = ((((ma6**2)**2 * ma6)**2)**2)**2 * ma6
    m6 = m6.frobenius(2).conjugate()
    # assert m6 == ma6**(-41*q**2)

    ma7 = ma6**u
    # q*(8-1 - 24*q^5)
    ma7_ = ma7.frobenius(5).conjugate()
    # 24 = 16 + 8 =  00011000
    #  7 =  8 - 1 =  0000100-1
    m7 = (((ma7_**2 * ma7_ * ma7)**2)**2)**2 * ma7.conjugate()
    m7 = m7.frobenius()
    # assert m7 == ma7**(q*(7 - 24*q**5))

    ma8 = ma7**u
    # (11 - 2*q^5)
    # 11 = 1011
    ma8_ = ma8.frobenius(5).conjugate()
    m8 = ((ma8**2)**2 * ma8 * ma8_)**2 * ma8
    # assert m8 == ma8**(11 - 2*q**5)

    ma9 = ma8**u
    # q^4*(4 - 3*q^5)
    ma9_ = ma9.frobenius(5)
    ma9__ = ma9_.conjugate()
    m9 = ((ma9 * ma9__)**2)**2 * ma9_
    m9 = m9.frobenius(4)
    # assert m9 == ma9**(q**4*(4 - 3*q**5))

    ma10 = ma9**u
    # q^3*(2 + q^5)
    ma10_ = ma10.frobenius(5)
    m10 = ma10**2 * ma10_
    m10 = m10.frobenius(3)
    # assert m10 == ma10**(q**3*(2 + q**5))

    ma11 = ma10**u
    # q^7
    m11 = ma11.frobenius(7)

    mc = m6 * m7 * m8 * m9 * m10 * m11
    # c = (-41*q**2 + u*q*(7 - 24*q**5) + u**2*(11 - 2*q**5) + u**3*q**4*(4 - 3*q**5) + u**4*q**3*(2 + q**5) + u**5*q**7)
    # assert mc == ma6**c
    # 17 M + 15 S + 5 exp(u) + 4 frob(5) + 5 frob

    r = m0.frobenius(7) * mb * mc # 2 M + frob
    # r == m**e1
    return r

def final_exp_hard_gg20a_v2(m, u):
    """
    Final exponentiation, hard part, on the 1st family of GG20 curves (GG20a)
    INPUT:
    - `m`: element in Fp^20 where a Frobenius map is allowed in SageMath
    - `u`: seed, such that u = 1715 or 1815 mod 2050 that is,
           u=1 mod 2, u=0 mod 5, u=11 or 34 mod 41, and (q-1)/5 is integer (u=15 mod 25).

    Phi_20(q) = q^8 - q^6 + q^4 - q^2 + 1 -> q^8 = q^6 - q^4 + q^2 - 1

    Cost: 2*exp(u-1) + 9 exp(u) + 51 S + 42 M + 4 frob(5) + 9 frob
    It seems slightly better than v1

    e1a = (u^6 - 2*u^5 + 5*u^4 + 328)*(-41*q^2 + u*q*(7 - 24*q^5) + u^2*(11 - 2*q^5) + u^3*q^4*(4 - 3*q^5) + u^4*q^3*(2 + q^5) + u^5*q^7)
        + (u^2 - 2*u + 5) * (625*q*(2 - q^5) + 125*u*(4 + 3*q^5) + 25*u^2*q^4*(11 + 2*q^5) + 5*u^3*q^3*(7 + 24*q^5) + 38*u^4*q^7)
        + 6724*q^7
    """
    # 4*41^2 = 6724 = 0x1A44 = 0001101001000100 = 4*(2^10 + 2^9 + 2^7 + 2^4 + 1)
    # 328 = 0x148 =             000101001000 = 8 + 64 + 256 = 2^3 + 2^6 + 2^8
    #m0 = m**6724    # 6724 = 4*41^2
    #m328 = m**328   #  328 = 8*41

    # q = m.parent().characteristic()
    m8 = ((m**2)**2)**2
    m64 = ((m8**2)**2)**2
    m256 = (m64**2)**2
    m328 = m8 * m64 * m256
    # assert m328 == m**328
    m512 = m256**2
    m0 = (m328 * m512)**2 * m
    m0 = (m0**2)**2                      # 12 S + 4 M
    # assert m0 == m**6724

    # u^2 - 2*u + 5 = (u-1)^2 + 2^2
    u1 = abs(u-1)
    ma = (m**u1)**u1 * (m**2)**2      # 2*exp(|u-1|) + M + 2S
    # assert ma == m**(u**2 - 2*u + 5)

    # with a = (u^2 - 2*u + 5), the exponent is
    # (q*(-q^5 + 2)*5^4 + u*(4 + 3*q^5)*5^3 + u^2*q^4*(11 + 2*q^5)*5^2 + u^3*q^3*(7 + 24*q^5)*5 + 38*u^4*q^7)
    # and with b = (u^6 - 2*u^5 + 5*u^4 + 328), the exponent is
    # (-41*q^2 + u*q*(7 - 24*q^5) + u^2*(11 - 2*q^5) + u^3*q^4*(4 - 3*q^5) + u^4*q^3*(2 + q^5) + u^5*q^7)

    # ma^(q*5^4*(2 - q^5)) * mb^(u^4*q^3*(2 + q^5))
    # ma^(u*5^3*(4 + 3*q^5)) * mb^(u^3*q^4*(4 - 3*q^5))
    # ma^(u^2*5^2*q^4*(11 + 2*q^5)) * mb^(u^2*(11 - 2*q^5))
    # ma^(u^3*5*q^3*(7 + 24*q^5)) * mb^(u*q*(7 - 24*q^5))
    # ma^(38*u^4*q^7) * mb^(-41*q^2) * mb^(u^5*q^7)

    ma1 = ma**u
    ma2 = ma1**u
    ma3 = ma2**u
    ma4 = ma3**u

    ma6 = ma4 * m328 # M
    # assert ma6 == m**(u**6 - 2*u**5 + 5*u**4 + 328)
    ma7 = ma6**u
    ma8 = ma7**u
    ma9 = ma8**u
    ma10 = ma9**u
    ma11 = ma10**u

    # Horner exp(5) = 2*S + M -> 4*(2*S + M) + 4M = 8S + 8M
    # if sequentially: 9S + 3M + 7S + 2M + 4S + 2M + 2S + M = 22S + 8M, total 14S more
    # 5^4 = 625 = 0x271 =        001001110001 = 1 - 16 + 128 + 512 = 2^9 + 2^7 - 2^4 + 1
    # 5^3 = 125 = 0x7D =         000001111101 = 128 - 4 + 1 = 2^7 - 2^2 + 1
    # 5^2 =  25 = 0x19 =         000000011001 = 16 + 8 + 1 = 2^4 + 2^3 + 1
    # 5         = 0x5  =         000000000101 = 4 + 1 = 2^2 + 1

    # q*5^4*(2 - q^5)
    # q
    m1 = ma.frobenius()
    # 5^4
    m1 = ((((((((m1**2)**2 * m1)**2)**2)**2 * m1.conjugate())**2)**2)**2)**2 * m1 # 9 S + 3 M
    # q^3*(2 - q^5)
    # q^3
    m10 = ma10.frobenius(3)
    # share (2-q^5) and (2+q^5)
    # (2 + q^5)
    #m1 = (m1.frobenius(5).conjugate() * m1**2)
    #m10 = m10.frobenius(5) * m10**2
    f1 = m1.conjugate() * m10                      # M
    f2 = m1 * m10                                  # M
    m1_m10 = f1.frobenius(5) * f2**2               # M + S + frob(5)
    # assert m1_m10 == ma**(q*5**4*(-q**5 + 2)) * ma10**(q**3*(2 + q**5))

    # u*5^3*(4 + 3*q^5)
    m2 = ma1
    # 5^3
    m2 = ((((((m2**2)**2)**2)**2)**2 * m2.conjugate())**2)**2 * m2 # 7 S + 2 M
    # q^4*(4 - 3*q^5)
    # q^4
    m9 = ma9.frobenius(4)                                          # frob
    # share m2: (4 + 3*q^5) and m9: 4 - 3*q^5
    f1 = m2 * m9                                                   # M
    f2 = (m2 * m9.conjugate()).frobenius(5)                        # M + frob(5)
    m2_m9 = ((f2 * f1)**2)**2 * f2.conjugate()                     # 2M + 2S
    # assert m2_m9 == ma1**(5**3*(4 + 3*q**5)) * ma9**(q**4*(4 - 3*q**5))

    # 5^2*q^4*(11 + 2*q^5)
    # q^4
    m3 = ma2.frobenius(4)                                          # frob
    # 5^2
    # m30 = m3 # only for testing
    m3 = (((m3**2 * m3)**2)**2)**2 * m3                            # 4 S + 2M
    # assert m3 == m30**(5**2)
    # share m3: (11 + 2*q^5) and m8: (11 - 2*q^5)
    m8 = ma8
    f1 = (m3 * m8.conjugate()).frobenius(5)                        # M + frob(5)
    f2 = m3 * m8                                                   # M
    # 11 = 1011
    m3_m8 = ((f2**2)**2 * f2 * f1)**2 * f2                         # 3 S + 3 M
    # assert m3_m8 == ma2**(q**4*5**2*(11 + 2*q**5)) * ma8**(11 - 2*q**5)

    # 5*q^3*(7 + 24*q^5)
    # q^3
    m4 = ma3.frobenius(3)                                          # frob
    # 5
    m4 = (m4**2)**2 * m4                                           # 2 S + M
    # q*(7 - 24*q^5) = q*(8-1 - 24*q^5)
    m7 = ma7.frobenius()                                           # frob
    # share m4: (7 + 24*q^5) and m7: (7 - 24*q^5)
    f1 = m4 * m7                                                   # M
    f2 = (m4 * m7.conjugate()).frobenius(5)                        # M + frob(5)
    # 7 = 111 = 100(-1)
    # 24 = 16 + 8 = 11000
    m4_m7 = (((f2**2 * f2 * f1)**2)**2)**2 * f1.conjugate()        # 4 S + 3M
    # assert m4_m7 == ma3**(q**3*5*(7 + 24*q**5)) * ma7**(q*(7 - 24*q**5))

    # ma^(38*u^4*q^7) * mb^(-41*q^2) * mb^(u^5*q^7)
    # m5: 38*q^7
    m5 = ma4.frobenius(7)                                          # frob
    # 38 = 0x26 = 00100110 = 32 + 4 + 2 = 2^5 + 2^2 + 2^1
    # m6: -41*q^2
    m6 = ma6.frobenius(2).conjugate()                              # frob
    # 41 = 0x29 = 00101001 = 32 + 8 + 1 = 2^5 + 2^3 + 2^0
    m5_m6 = (((((m5 * m6)**2)**2 * m6)**2 * m5)**2 * m5)**2 * m6   # 5 S + 5 M
    # assert m5_m6 == ma4**(38*q**7) * ma6**(-41*q**2)

    md = m1_m10 * m2_m9 * m3_m8 * m4_m7 * m5_m6  # 4 M

    # q^7
    # m11 = ma11.frobenius(7)

    r = (m0 * ma11).frobenius(7) * md # 2 M + frob
    #e1 = (u**6 - 2*u**5 + 5*u**4 + 328)*(-41*q**2 + u*q*(7 - 24*q**5) + u**2*(11 - 2*q**5) + u**3*q**4*(4 - 3*q**5) + u**4*q**3*(2 + q**5) + u**5*q**7) \
    #    + (u**2 - 2*u + 5) * (625*q*(2 - q**5) + 125*u*(4 + 3*q**5) + 25*u**2*q**4*(11 + 2*q**5) + 5*u**3*q**3*(7 + 24*q**5) + 38*u**4*q**7) \
    #    + 6724*q**7
    # assert r == m**e1
    return r

def miller_loop_opt_ate_gg20b(Q, P, a, u):
    """
    The second GG20 family (GG20b)
    generic formula: x - qx - 2*qx^6
    Miller loop f_{u,Q}(P) f_{-2,\pi_q6(Q)}(P) l_{uQ, -\pi(Q)}(P)
       where u can be positive or negative
    the formula is (x - qx - 2*qx^6) = 0 mod rx so the pairing equation is
    f_{u,Q}(P) f_{-2,pi_q6(Q)}(P) l_{[u]Q,\pi(-Q)}(P) l_{uQ-\pi(Q), \pi_6([2]Q)}(P)
    --> it is not necessary to do the second line as it will be a vertical
    (it is possible to make a different choice of lines to implement)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters, non-zero integer in ZZ

    The curve coefficient b is zero.
    """
    PP = (P[0], P[1])
    m, uQ = miller_function_ate(Q, PP, a, u, m0=1)
    piQ_ = [(Q[0]).frobenius(), -(Q[1]).frobenius()]
    pi6Q_ = [(Q[0]).frobenius(6), -(Q[1]).frobenius(6)]
    l2, Q2 = double_line_affine_j(pi6Q_, PP, a)
    l3, Q3 = add_line_j(uQ, piQ_, PP)

    return m * l2 * l3

def final_exp_hard_gg20b_v0(m, u):
    """
    Final exponentiation, hard part, on the 2nd family of GG20 curves (GG20b)
    INPUT:
    - `m`: element in Fp^20 where a Frobenius map is allowed in SageMath
    - `u`: seed, such that u = 1465 or 1565 mod 2050 that is,
           u=1 mod 2, u=0 mod 5, u=7 or 30 mod 41, and (q-1)/5 is integer (u=15 mod 25).

    Phi_20(q) = q^8 - q^6 + q^4 - q^2 + 1 -> q^8 = q^6 - q^4 + q^2 - 1

    A first non-optimized solution, as suggested in
    https://eprint.iacr.org/2020/875
    using the curve cofactor cx(u), write
    exponent_hard = Phi_20(px)/rx = (px^8 - px^6 + px^4 - px^2 + 1)/rx
    = cx * (px^7 + l6*px^6 + l5*px^5 + l4*px^4 + l3*px^3 + l2*px^2 + l1*px + l0)
      + i6*px^6 + i5*px^5 + i4*px^4 + i3*px^3 + i2*px^2 + i1*px + i0
    where
    cx = 125*(x**4 + 2*x**3 + 2*x**2 + 10*x + 25)/164
    rx = (x**8 - 4*x**7 + 11*x**6 - 24*x**5 + 41*x**4 - 120*x**3 + 275*x**2 - 500*x + 625)/(205*125)
    qx = (x**12 - 2*x**11 + 5*x**10 - 76*x**7 - 176*x**6 - 380*x**5 + 3125*x**2 + 12938*x + 15625)/33620
    tx = (-2*x**6 + 117*x + 205)/205
    assert (cyclotomic_polynomial(20)(qx) % rx) == 0
    exponent = cyclotomic_polynomial(20)(qx)//rx
    41*exponent == (cx/125) * (41*125*qx^7 \
    + 25*(-2*x**6 + 117*x + 656)*qx^6 \
    + 5*(-4*x**7 + 29*x**2 + 1312*x + 1599)*qx^5 \
    + (8*x**7 + 28*x**6 + 48*x**5 - 82*x**4 - 287*x**3 - 550*x**2 - 4549*x - 15682)*qx^4 \
    + (44*x**7 - 96*x**6 + 264*x**5 - 451*x**4 + 984*x**3 - 3025*x**2 - 7832*x - 4251)*qx^3 \
    + (-8*x**7 - 28*x**6 + 77*x**5 + 82*x**4 + 287*x**3 + 550*x**2 + 4549*x + 10932)*qx^2 \
    + (-44*x**7 + 121*x**6 - 264*x**5 + 451*x**4 - 984*x**3 + 3025*x**2 + 8932*x - 3949)*qx \
    + (-7*x**7 + 28*x**6 - 77*x**5 - 82*x**4 - 287*x**3 + 840*x**2 + 371*x - 1092)) \
    + 25*4*(2*x**3 + 3*x**2 - 10*x - 25)*qx^6 \
    - 5*2*(4*x**3 + 56*x**2 + 180*x + 159)*qx^5 \
    - 2*(96*x**3 + 82*x**2 - 1015*x - 3068)*qx^4 \
    - 2*(28*x**3 - 299*x**2 - 520*x - 374)*qx^3 \
    - 2*(29*x**3 + 418*x**2 + 1640*x + 3068)*qx^2 \
    - 2*(22*x**3 + 374*x**2 + 270*x - 251)*qx \
    + (28*x**3 + 416*x**2 + 1930*x + 2381)

    cost: more than 11*exp(u) + 13*frob + many M
    """

    r = ZZ((u**8 - 4*u**7 + 11*u**6 - 24*u**5 + 41*u**4 - 120*u**3 + 275*u**2 - 500*u + 625)/(205*125))
    c0 = ZZ(u**4 + 2*u**3 + 2*u**2 + 10*u + 25)
    assert c0 == (u**2 - 2*u + 5) * (u**2 + 4*u + 5)
    assert (c0 % ZZ(164)) == 0
    c = c0 // ZZ(164)
    l7 = ZZ(41*125)
    l6 = ZZ(25*(-2*u**6 + 117*u + 656))
    l5 = ZZ(5*(-4*u**7 + 29*u**2 + 1312*u + 1599))
    l4 = ZZ(8*u**7 + 28*u**6 + 48*u**5 - 82*u**4 - 287*u**3 - 550*u**2 - 4549*u - 15682)
    l3 = ZZ(44*u**7 - 96*u**6 + 264*u**5 - 451*u**4 + 984*u**3 - 3025*u**2 - 7832*u - 4251)
    l2 = ZZ(-8*u**7 - 28*u**6 + 77*u**5 + 82*u**4 + 287*u**3 + 550*u**2 + 4549*u + 10932)
    l1 = ZZ(-44*u**7 + 121*u**6 - 264*u**5 + 451*u**4 - 984*u**3 + 3025*u**2 + 8932*u - 3949)
    l0 = ZZ(-7*u**7 + 28*u**6 - 77*u**5 - 82*u**4 - 287*u**3 + 840*u**2 + 371*u - 1092)

    i6 = ZZ(25*4*(2*u**3 + 3*u**2 - 10*u - 25))
    assert i6 == 25*4*(2*u - 5) * (u**2 + 4*u + 5)
    i5 = ZZ(-5*2*(4*u**3 + 56*u**2 + 180*u + 159))
    i4 = ZZ(-2*(96*u**3 + 82*u**2 - 1015*u - 3068))
    i3 = ZZ(-2*(28*u**3 - 299*u**2 - 520*u - 374))
    i2 = ZZ(-2*(29*u**3 + 418*u**2 + 1640*u + 3068))
    i1 = ZZ(-2*(22*u**3 + 374*u**2 + 270*u - 251))
    i0 = ZZ(28*u**3 + 416*u**2 + 1930*u + 2381)

    p = m.parent().characteristic()
    p = ZZ(p)
    e1 = (l7*p**7 + l6*p**6 + l5*p**5 + l4*p**4 + l3*p**3 + l2*p**2 + l1*p + l0)
    e0 = (i6*p**6 + i5*p**5 + i4*p**4 + i3*p**3 + i2*p**2 + i1*p + i0)
    assert ZZ(e0 + e1*c) == ZZ(41*(p**8 - p**6 + p**4 - p**2 + 1)//r)

    f = m**l7
    f = f.frobenius() * m**l6
    f = f.frobenius() * m**l5
    f = f.frobenius() * m**l4
    f = f.frobenius() * m**l3
    f = f.frobenius() * m**l2
    f = f.frobenius() * m**l1
    f = f.frobenius() * m**l0
    assert f == m**e1
    f = f**c

    g = m**i6
    g = g.frobenius() * m**i5
    g = g.frobenius() * m**i4
    g = g.frobenius() * m**i3
    g = g.frobenius() * m**i2
    g = g.frobenius() * m**i1
    g = g.frobenius() * m**i0
    assert g == m**e0
    
    return f * g

def final_exp_hard_gg20b_v1(m, u):
    """
    Final exponentiation, hard part, on the 2nd family of GG20 curves (GG20b)
    INPUT:
    - `m`: element in Fp^20 where a Frobenius map is allowed in SageMath
    - `u`: seed, such that u = 1465 or 1565 mod 2050 that is,
           u=1 mod 2, u=0 mod 5, u=7 or 30 mod 41, and (q-1)/5 is integer (u=15 mod 25).

    Phi_20(q) = q^8 - q^6 + q^4 - q^2 + 1 -> q^8 = q^6 - q^4 + q^2 - 1
    Cost: 2 exp(u-1) + 9 exp(u) + 52 S + 43 M + 8 frob(5) + 10 frob

    e1b = (u^6 - 2*u^5 + 5*u^4 - 328)*(-41*q^2 + u*q*(7 + 24*q^5) + u^2*(11 + 2*q^5) - u^3*q^4*(4 + 3*q^5) + u^4*q^3*(-2 + q^5) + u^5*q^7)
        + (u^2 - 2*u + 5)            *(-q*(q^5 + 2)*5^4 + u*(-4 + 3*q^5)*5^3 + u^2*q^4*(11 - 2*q^5)*5^2 + u^3*q^3*(7 - 24*q^5)*5 - 38*u^4*q^7)
        + 4*41^2*q^7
    """
    # 4*41^2 = 6724 = 0x1A44 = 0001101001000100 = 4*(2^10 + 2^9 + 2^7 + 2^4 + 1)
    # 328 = 0x148 =             000101001000 = 8 + 64 + 256 = 2^3 + 2^6 + 2^8
    #m0 = m**6724    # 6724 = 4*41^2
    #m328 = m**328   #  328 = 8*41

    # q = m.parent().characteristic()
    m8 = ((m**2)**2)**2
    m64 = ((m8**2)**2)**2
    m256 = (m64**2)**2
    m328 = m8 * m64 * m256
    # m328 == m**328
    m512 = m256**2
    m0 = (m328 * m512)**2 * m
    m0 = (m0**2)**2                      # 12 S + 4 M
    # m0 == m**6724

    # u^2 - 2*u + 5 = (u-1)^2 + 2^2
    u1 = abs(u-1)
    ma = (m**u1)**u1 * (m**2)**2      # 2*exp(|u-1|) + M + 2S
    # ma == m**(u**2 - 2*u + 5)

    # (-q*(q^5 + 2)*5^4 + u*(-4 + 3*q^5)*5^3 + u^2*q^4*(11 - 2*q^5)*5^2 + u^3*q^3*(8-1 - 24*q^5)*5 - 38*u^4*q^7)
    m1 = (ma.frobenius(5) * ma**2).frobenius().conjugate()
    # m1 == ma**(-q*(q**5 + 2))
    ma1 = ma**u
    ma1_ = ma1.frobenius(5)
    m2 = ((ma1.conjugate() * ma1_)**2)**2 * ma1_.conjugate()
    # m2 == ma1**(-4 + 3*q**5)
    ma2 = ma1**u
    ma2_ = ma2.frobenius(5).conjugate()
    # 11 = 1011
    m3 = ((ma2**2)**2 * ma2 * ma2_)**2 * ma2
    m3 = m3.frobenius(4)
    # m3 == ma2**(q**4*(11 - 2*q**5))
    ma3 = ma2**u
    ma3_ = ma3.frobenius(5).conjugate()
    # 7 = 111 = 100(-1)
    # 24 = 16 + 8 = 11000
    m4 = (((ma3_**2 * ma3_ * ma3)**2)**2)**2 * ma3.conjugate()
    m4 = m4.frobenius(3)
    # m4 == ma3**(q**3*(8-1 - 24*q**5))
    ma4 = ma3**u
    # 38 = 0x26 = 00100110 = 32 + 4 + 2
    m5 = ((((ma4**2)**2)**2 * ma4)**2 * ma4)**2
    m5 = m5.frobenius(7).conjugate()
    # m5 == ma4**(-38*q**7)

    mb = (m1**2)**2 * m1 * m2
    mb = (mb**2)**2 * mb * m3
    mb = (mb**2)**2 * mb * m4
    mb = (mb**2)**2 * mb * m5
    # assert mb == (((m1**5*m2)**5*m3)**5*m4)**5*m5 # exp(5) = 2*S + M -> 4*(2*S + M) + 4M = 8S + 8M
    # total mb: 15 S + 15 M + 4 frob(5) + 4 frob + 4*exp(u)
    # if sequentially: 9S + 3M + 7S + 2M + 4S + 2M + 2S + M = 22S + 8M, total 14S more
    # 5^4 = 625 = 0x271 =        001001110001 = 1 - 16 + 128 + 512 = 2^9 + 2^7 - 2^4 + 1
    # 5^3 = 125 = 0x7D =         000001111101 = 128 - 4 + 1 = 2^7 - 2^2 + 1
    # 5^2 =  25 = 0x19 =         000000011001 = 16 + 8 + 1 = 2^4 + 2^3 + 1
    # 5         = 0x5  =         000000000101 = 4 + 1 = 2^2 + 1

    #b = (-q*(q**5 + 2)*5**4 + u*(-4 + 3*q**5)*5**3 + u**2*q**4*(11 - 2*q**5)*5**2 + u**3*q**3*(8-1 - 24*q**5)*5 - 38*u**4*q**7)
    # mb == ma**b
    # total: 37 S + 24 M + 2 exp(u-1) + 4 exp(u) + 4 frob(5) + 4 frob

    ma6 = ma4 * m328.conjugate()
    # ma6 == m**(u**6 - 2*u**5 + 5*u**4 - 328)
    # (-41*q^2 + u*q*(8-1 + 24*q^5) + u^2*(11 + 2*q^5) - u^3*q^4*(4 + (4-1)*q^5) + u^4*q^3*(-2 + q^5) + u^5*q^7)

    # 41 = 0x29 = 00101001
    m6 = ((((ma6**2)**2 * ma6)**2)**2)**2 * ma6
    m6 = m6.frobenius(2).conjugate()
    # m6 == ma6**(-41*q**2)

    ma7 = ma6**u
    # q*(8-1 + 24*q^5)
    ma7_ = ma7.frobenius(5)
    # 24 = 16 + 8 =  00011000
    m7 = (((ma7_**2 * ma7_ * ma7)**2)**2)**2 * ma7.conjugate()
    m7 = m7.frobenius()
    # m7 == ma7**(q*(7 + 24*q**5))

    ma8 = ma7**u
    # (11 + 2*q^5)
    # 11 = 1011
    ma8_ = ma8.frobenius(5)
    m8 = ((ma8**2)**2 * ma8 * ma8_)**2 * ma8
    # m8 == ma8**(11 + 2*q**5)

    ma9 = ma8**u
    # -q^4*(4 + 3*q^5)
    ma9_ = ma9.frobenius(5)
    m9 = ((ma9 * ma9_)**2)**2 * ma9_.conjugate()
    m9 = m9.frobenius(4).conjugate()
    # m9 == ma9**(-q**4*(4 + 3*q**5))

    ma10 = ma9**u
    # q^3*(-2 + q^5)
    ma10_ = ma10.frobenius(5)
    m10 = ma10.conjugate()**2 * ma10_
    m10 = m10.frobenius(3)
    # m10 == ma10**(q**3*(-2 + q**5))

    ma11 = ma10**u
    # q^7
    m11 = ma11.frobenius(7)

    mc = m6 * m7 * m8 * m9 * m10 * m11
    # c = (-41*q**2 + u*q*(7 + 24*q**5) + u**2*(11 + 2*q**5) - u**3*q**4*(4 + 3*q**5) + u**4*q**3*(-2 + q**5) + u**5*q**7)
    # mc == ma6**c
    # 17 M + 15 S + 5 exp(u) + 4 frob(5) + 5 frob

    r = m0.frobenius(7) * mb * mc # 2 M + frob
    # r == m**e1
    return r

def final_exp_hard_gg20b_v2(m, u):
    """
    Final exponentiation, hard part, on the 2nd family of GG20 curves (GG20b)
    INPUT:
    - `m`: element in Fp^20 where a Frobenius map is allowed in SageMath
    - `u`: seed, such that u = 1465 or 1565 mod 2050 that is,
           u=1 mod 2, u=0 mod 5, u=7 or 30 mod 41, and (q-1)/5 is integer (u=15 mod 25).

    Phi_20(q) = q^8 - q^6 + q^4 - q^2 + 1 -> q^8 = q^6 - q^4 + q^2 - 1

    Cost: 2*exp(u-1) + 9 exp(u) + 51 S + 42 M + 4 frob(5) + 9 frob
    It seems slightly better than v1

    e1 = (u^6 - 2*u^5 + 5*u^4 - 328)*(-41*q^2 + u*q*(7 + 24*q^5) + u^2*(11 + 2*q^5) - u^3*q^4*(4 + 3*q^5) + u^4*q^3*(-2 + q^5) + u^5*q^7)
       + (u^2 - 2*u + 5)            *(-q*(q^5 + 2)*5^4 + u*(-4 + 3*q^5)*5^3 + u^2*q^4*(11 - 2*q^5)*5^2 + u^3*q^3*(7 - 24*q^5)*5 - 38*u^4*q^7)
       + 4*41^2*q^7
    """
    # 4*41^2 = 6724 = 0x1A44 = 0001101001000100 = 4*(2^10 + 2^9 + 2^7 + 2^4 + 1)
    # 328 = 0x148 =             000101001000 = 8 + 64 + 256 = 2^3 + 2^6 + 2^8
    #m0 = m**6724    # 6724 = 4*41^2
    #m328 = m**328   #  328 = 8*41

    # q = m.parent().characteristic()
    m8 = ((m**2)**2)**2
    m64 = ((m8**2)**2)**2
    m256 = (m64**2)**2
    m328 = m8 * m64 * m256
    # assert m328 == m**328
    m512 = m256**2
    m0 = (m328 * m512)**2 * m
    m0 = (m0**2)**2                      # 12 S + 4 M
    # assert m0 == m**6724

    # u^2 - 2*u + 5 = (u-1)^2 + 2^2
    u1 = abs(u-1)
    ma = (m**u1)**u1 * (m**2)**2      # 2*exp(|u-1|) + M + 2S
    # assert ma == m**(u**2 - 2*u + 5)

    # with a = (u^2 - 2*u + 5), the exponent is
    # (-q*(q^5 + 2)*5^4 + u*(-4 + 3*q^5)*5^3 + u^2*q^4*(11 - 2*q^5)*5^2 + u^3*q^3*(7 - 24*q^5)*5 - 38*u^4*q^7)
    # and with b = (u^6 - 2*u^5 + 5*u^4 - 328), the exponent is
    # (-41*q^2 + u*q*(7 + 24*q^5) + u^2*(11 + 2*q^5) -u^3*q^4*(4 + 3*q^5) + u^4*q^3*(-2 + q^5) + u^5*q^7)

    # ma^(-q*5^4*(2 + q^5)) * mb^(u^4*q^3*(-2 + q^5))
    # ma^(u*5^3*(-4 + 3*q^5)) * mb^(-u^3*q^4*(4 + 3*q^5))
    # ma^(u^2*5^2*q^4*(11 - 2*q^5)) * mb^(u^2*(11 + 2*q^5))
    # ma^(u^3*5*q^3*(7 - 24*q^5)) * mb^(u*q*(7 + 24*q^5))
    # ma^(-38*u^4*q^7) * mb^(-41*q^2) * mb^(u^5*q^7)

    ma1 = ma**u
    ma2 = ma1**u
    ma3 = ma2**u
    ma4 = ma3**u

    ma6 = ma4 * m328.conjugate() # M
    # assert ma6 == m**(u**6 - 2*u**5 + 5*u**4 - 328)
    ma7 = ma6**u
    ma8 = ma7**u
    ma9 = ma8**u
    ma10 = ma9**u
    ma11 = ma10**u

    # Horner exp(5) = 2*S + M -> 4*(2*S + M) + 4M = 8S + 8M
    # if sequentially: 9S + 3M + 7S + 2M + 4S + 2M + 2S + M = 22S + 8M, total 14S more
    # 5^4 = 625 = 0x271 =        001001110001 = 1 - 16 + 128 + 512 = 2^9 + 2^7 - 2^4 + 1
    # 5^3 = 125 = 0x7D =         000001111101 = 128 - 4 + 1 = 2^7 - 2^2 + 1
    # 5^2 =  25 = 0x19 =         000000011001 = 16 + 8 + 1 = 2^4 + 2^3 + 1
    # 5         = 0x5  =         000000000101 = 4 + 1 = 2^2 + 1

    # -q*5^4*(2 + q^5)
    # -q
    m1 = ma.frobenius().conjugate()
    # 5^4
    m1 = ((((((((m1**2)**2 * m1)**2)**2)**2 * m1.conjugate())**2)**2)**2)**2 * m1 # 9 S + 3 M
    # q^3*(-2 + q^5)
    # q^3
    m10 = ma10.frobenius(3)
    # share (2+q^5) and (-2+q^5)
    # (2 + q^5)
    #m1 = (m1.frobenius(5) * m1**2)
    #m10 = m10.frobenius(5) * m10.conjugate()**2
    f1 = m1 * m10                                  # M
    f2 = m1 * m10.conjugate()                      # M
    m1_m10 = f1.frobenius(5) * f2**2               # M + S + frob(5)
    # assert m1_m10 == ma**(-q*5**4*(q**5 + 2)) * ma10**(q**3*(-2 + q**5))

    # u*5^3*(-4 + 3*q^5)
    m2 = ma1
    # 5^3
    m2 = ((((((m2**2)**2)**2)**2)**2 * m2.conjugate())**2)**2 * m2 # 7 S + 2 M
    # -q^4*(4 + 3*q^5)
    # -q^4
    m9 = ma9.frobenius(4).conjugate()                              # frob
    # share m2: (-4 + 3*q^5) and m9: 4 + 3*q^5
    f1 = (m2 * m9).frobenius(5)                                    # M + frob(5)
    f2 = m2.conjugate() * m9                                       # M
    m2_m9 = ((f2 * f1)**2)**2 * f1.conjugate()                     # 2M + 2S
    # assert m2_m9 == ma1**(5**3*(-4 + 3*q**5)) * ma9**(-q**4*(4 + 3*q**5))

    # 5^2*q^4*(11 - 2*q^5)
    # q^4
    m3 = ma2.frobenius(4)                                          # frob
    # 5^2
    # m30 = m3 # only for testing
    m3 = (((m3**2 * m3)**2)**2)**2 * m3                            # 4 S + 2M
    # assert m3 == m30**(5**2)
    # share m3: (11 - 2*q^5) and m8: (11 + 2*q^5)
    m8 = ma8
    f1 = (m3.conjugate() * m8).frobenius(5)                        # M + frob(5)
    f2 = m3 * m8                                                   # M
    # 11 = 1011
    m3_m8 = ((f2**2)**2 * f2 * f1)**2 * f2                         # 3 S + 3 M
    # assert m3_m8 == ma2**(q**4*5**2*(11 - 2*q**5)) * ma8**(11 + 2*q**5)

    # 5*q^3*(7 - 24*q^5)
    # q^3
    m4 = ma3.frobenius(3)                                          # frob
    # 5
    m4 = (m4**2)**2 * m4                                           # 2 S + M
    # q*(7 + 24*q^5) = q*(8-1 + 24*q^5)
    m7 = ma7.frobenius()                                           # frob
    # share m4: (7 - 24*q^5) and m7: (7 + 24*q^5)
    f1 = m4 * m7                                                   # M
    f2 = (m4.conjugate() * m7).frobenius(5)                        # M + frob(5)
    # 7 = 111 = 100(-1)
    # 24 = 16 + 8 = 11000
    m4_m7 = (((f2**2 * f2 * f1)**2)**2)**2 * f1.conjugate()        # 4 S + 3M
    # assert m4_m7 == ma3**(q**3*5*(8-1 - 24*q**5)) * ma7**(q*(7 + 24*q**5))

    # ma^(-38*u^4*q^7) * mb^(-41*q^2) * mb^(u^5*q^7)
    # m5: -38*q^7
    m5 = ma4.frobenius(7).conjugate()                              # frob
    # 38 = 0x26 = 00100110 = 32 + 4 + 2 = 2^5 + 2^2 + 2^1
    # m6: -41*q^2
    m6 = ma6.frobenius(2).conjugate()                              # frob
    # 41 = 0x29 = 00101001 = 32 + 8 + 1 = 2^5 + 2^3 + 2^0

    m5_m6 = (((((m5 * m6)**2)**2 * m6)**2 * m5)**2 * m5)**2 * m6   # 5 S + 5 M
    # assert m5_m6 == ma4**(-38*q**7) * ma6**(-41*q**2)

    md = m1_m10 * m2_m9 * m3_m8 * m4_m7 * m5_m6  # 4 M

    # q^7
    # m11 = ma11.frobenius(7)

    r = (m0 * ma11).frobenius(7) * md # 2 M + frob
    # e1 = (u**6 - 2*u**5 + 5*u**4 - 328)*(-41*q**2 + u*q*(7 + 24*q**5) + u**2*(11 + 2*q**5) -u**3*q**4*(4 + 3*q**5) + u**4*q**3*(-2 + q**5) + u**5*q**7) \
    #     + (u**2 - 2*u + 5)            *(-q*(q**5 + 2)*5**4 + u*(-4 + 3*q**5)*5**3 + u**2*q**4*(11 - 2*q**5)*5**2 + u**3*q**3*(7 - 24*q**5)*5 - 38*u**4*q**7) \
    #     + 4*41**2*q**7
    # assert r == m**e1
    return r
