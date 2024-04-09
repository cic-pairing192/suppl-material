"""
date: April 2024

Implementation of pairing on Gasnier-Guillevic new curves with k=28 and D=1.
The final exponentiation is not yet optimized.
"""
from pairing import *
from sage.rings.integer_ring import ZZ

def miller_loop_opt_ate_gg28a(Q, P, a, u):
    """
    The first GG28 family (GG28a)
    generic formula: u - q - 2*q^8

    Miller loop f_{u,Q}(P) f_{2,-\pi_q8(Q)}(P) l_{uQ, -\pi(Q)}(P)
    Miller loop f_{u,Q}(P) f_{2,-\pi_q8(Q)}(P) l_{-2\pi_q8Q, -\pi(Q)}(P)
    where u can be positive or negative
    the formula is (u - q - 2*q^8) = 0 mod r so the pairing equation is
    f_{u,Q}(P) f_{2,-pi_q8(Q)}(P) l_{[u]Q,\pi(-Q)}(P) l_{uQ-\pi(Q), -\pi_8([2]Q)}(P)
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
    pi8Q_ = [(Q[0]).frobenius(8), -(Q[1]).frobenius(8)]
    l2, Q2 = double_line_affine_j(pi8Q_, PP, a)
    l3, Q3 = add_line_j(Q2, piQ_, PP)

    return m * l2 * l3

def miller_loop_opt_ate_gg28a_alt(Q, P, a, u):
    """
    The first GG28 family (GG28a)
    generic formula: 2 + u*q^6 - q^7

    Miller loop f_{u,\pi_q6(Q)}(P) f_{2,Q}(P) l_{2Q, -\pi_q7(Q)}(P)
    where u can be positive or negative
    the formula is (2 + u*q^6 - q^7) = 0 mod r so the pairing equation is
    f_{u,\pi_q6(Q)}(P) f_{2,Q}(P) l_{[u]pi_q6(Q),\pi(2Q)}(P) l_{[u]pi_q6(Q)-\pi_q^7(Q), [2]Q}(P)
    --> it is not necessary to do the second line as it will be a vertical
    (it is possible to make a different choice of lines to implement)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters, non-zero integer in ZZ

    The curve coefficient b is zero.
    """
    PP = (P[0], P[1])
    pi6Q = [(Q[0]).frobenius(6), (Q[1]).frobenius(6)]
    m, uq6Q = miller_function_ate(pi6Q, PP, a, u, m0=1)
    l2, Q2 = double_line_affine_j(Q, PP, a)
    pi7Q_ = [(Q[0]).frobenius(7), -(Q[1]).frobenius(7)]
    l3, Q3 = add_line_j(Q2, pi7Q_, PP)

    return m * l2 * l3

def final_exp_hard_gg28a_v1(m, u):
    """
    Final exponentiation, hard part, on the 1st family of GG28 curves (GG28a)
    INPUT:
    - `m`: element in Fp^28 where a Frobenius map is allowed in SageMath
    - `u`: seed, such that u = 309, 449, 1759, 1899 mod 2030=2*5*7*29 that is,
           u=1 mod 2, u=4 mod 5, u=1 or 2 mod 7, u=14 or 19 mod 29, and (q-1)/7 is integer (u=1,2 mod 7).

    Phi_28(q) = q^12 - q^10 + q^8 - q^6 + q^4 - q^2 + 1 -> q^12 = q^10 - q^8 + q^6 - q^4 + q^2 - 1
    Cost: 2 exp(u-1) + 13 exp(u) +  83 S + 68 M + 12 frob(7) + 14 frob

    e1a = (u^8 - 2*u^7 + 5*u^6-232)*(-29*q^4 + u*q^3*(-117-44*q^7) + u^2*q^2*(-41+38*q^7) + u^3*q*(7+24*q^7) + u^4*(11+2*q^7) + u^5*q^6*(-4-3*q^7) + u^6*q^5*(-2+q^7) + u^7*q^11)
        + (u^2 - 2*u + 5) * (5^6*q^3*(-2-q^7) + 5^5*u*q^2*(-4+3*q^7) + 5^4*u^2*q*(11*q^7+2) + 5^3*u^3*(24+7*q^7) + 5^2*u^4*q^6*(-41-38*q^7) + 5*u^5*q^5*(-117+44*q^7) + 278*u^6*q^11)
        + 3364*q^11

    3364 = 0xd24 = 2^11+2^10+2^8+2^5+2^2 = 4*(2^9+2^8+2^6+2^3+1) = 4*(110100101)
    232  = 0xe8  = 2^7+2^6+2^5+2^3 =  11101000 = 2^8 - 2^5 + 2^3 = 100-101000
    278  = 0x116 = 2^8+2^4+2^2+2   = 100010110                   = 100 010110

    3364 = 116*29 where 29 = 32-3 = 2^5-2-1 = 16+8+4+1 and 116 = 2^7-2^4+2^2
     232 = 116*2

    or: 3364 = 232*14 + 116
    compute m^116 -> m^232 -> m^232^14 * m^116
    many similarities with the formulas for GG20a and GG20b
    """

    q = m.parent().characteristic()
    # precompute m^3364 and store the intermediate values shared with 232
    m4 = (m**2)**2
    m16 = (m4**2)**2
    m128 = ((m16**2)**2)**2
    m116 = m4 * m16.conjugate() * m128
    assert m116 == m**116
    m232 = m116**2
    assert m232 == m**232
    # 3364 = 232*14 + 116, 14 = 16-2 = 2^4-2
    m464 = m232**2
    m0 = ((m464**2)**2)**2 * m464.conjugate() * m116
    assert m0 == m**3364
    # 12S + 4M

    # u^2 - 2*u + 5 = (u-1)^2 + 2^2
    u1 = abs(u-1)
    ma = (m**u1)**u1 * (m**2)**2      # 2*exp(|u-1|) + M + 2S
    assert ma == m**(u**2 - 2*u + 5)

    # with (u^2 - 2*u + 5), the exponent is
    # (q^3*(-2-q^7)*5^6 + u*q^2*(-4+3*q^7)*5^5 + u^2*q*(2+11*q^7)*5^4 + u^3*(24+7*q^7)*5^3 + u^4*q^6*(-41-38*q^7)*5^2 + u^5*q^5*(-117+44*q^7)*5 + u^6*q^11*278)

    m1 = (ma.frobenius(7) * ma**2).conjugate().frobenius(3)
    assert m1 == ma**(q**3*(-2-q**7))
    ma1 = ma**u
    ma1_ = ma1.frobenius(7)
    m2 = (((ma1.conjugate() * ma1_)**2)**2 * ma1_.conjugate()).frobenius(2)
    assert m2 == ma1**(q**2*(-4+3*q**7))

    ma2 = ma1**u
    ma2_ = ma2.frobenius(7)
    #  2 = 0010
    # 11 = 1011
    m3 = ((ma2_**2)**2 * ma2_ * ma2)**2 * ma2_
    m3 = m3.frobenius()
    assert m3 == ma2**(q*(2+11*q**7))

    ma3 = ma2**u
    ma3_ = ma3.frobenius(7)
    # 7 = 111 = 100(-1)
    # 24 = 16 + 8 = 11000
    m4 = (((ma3**2 * ma3 * ma3_)**2)**2)**2 * ma3_.conjugate()
    assert m4 == ma3**((24+7*q**7))

    ma4 = ma3**u
    ma4_ = ma4.frobenius(7)
    # 38 = 0x26 = 00100110 = 32 + 4 + 2 = 32 + 8 - 2
    # 41 = 0x29 = 00101001              = 32 + 8 + 1
    ma4_q7 = ma4 * ma4_
    m5 = ((((ma4_q7**2)**2 * ma4_q7)**2)**2 * ma4_.conjugate())**2 * ma4
    m5 = m5.frobenius(6).conjugate()
    assert m5 == ma4**(q**6*(-41-38*q**7))

    ma5 = ma4**u
    ma5_ = ma5.frobenius(7)
    # 117 = 0x75 = 128 - 11   = 2^7 - 2^4 + 2^2 + 1 = 100-10101 = 100-10101 = 2^7 - 2^4 + 2^2 + 1
    #-117 =-0x75 =-128 + 11   =-2^7 + 2^4 - 2^2 - 1 =-10010-10-1=-10010-10-1 = 2^7 - 2^4 + 2^2 + 1
    # 44  = 0x2c = 32 + 8 + 4 = 2^5 + 2^3 + 2^2     = 00101 10 0= 00110-10 0 = 2^5 + 2^4 - 2^2
    ma5_q7 = ma5 * ma5_
    m6 = ((((((ma5.conjugate()**2)**2 * ma5_)**2 * ma5_q7)**2)**2 * ma5_q7.conjugate())**2)**2 * ma5.conjugate()
    m6 = m6.frobenius(5)
    assert m6 == ma5**(q**5*(-117+44*q**7))

    ma6 = ma5**u
    ma6_ = ma6.frobenius(11)
    # 278 = 0x116 = 2^8 + 2^4 + 2^2 + 2 = 100010110
    m7 = (((((((ma6_**2)**2)**2)**2 * ma6_)**2)**2 * ma6_)**2 * ma6_)**2
    assert m7 == ma6**(q**11*278)

    # now Horner-like for all the 5^6, 5^5, 5^4, 5^3, 5^2, 5 factors
    mb = (m1**2)**2 * m1 * m2
    mb = (mb**2)**2 * mb * m3
    mb = (mb**2)**2 * mb * m4
    mb = (mb**2)**2 * mb * m5
    mb = (mb**2)**2 * mb * m6
    mb = (mb**2)**2 * mb * m7
    assert mb == (((((m1**5 * m2)**5 * m3)**5 * m4)**5 * m5)**5 * m6)**5 * m7 # exp(5) = 2*S + M -> 6*(2*S + M) + 6M = 12S + 12M

    # total mb:  31S + 21 M + 12S + 12M + 6 frob(7) + 6 frob + 6*exp(u)
    #         :  43S + 33 M + 6 frob(7) + 6 frob + 6*exp(u)

    # if sequentially:
    # 5^6 = ...
    # 5^5 = ...
    # 5^4 = 625 = 0x271 =        001001110001 = 1 - 16 + 128 + 512 = 2^9 + 2^7 - 2^4 + 1
    # 5^3 = 125 = 0x7D =         000001111101 = 128 - 4 + 1 = 2^7 - 2^2 + 1
    # 5^2 =  25 = 0x19 =         000000011001 = 16 + 8 + 1 = 2^4 + 2^3 + 1
    # 5         = 0x5  =         000000000101 = 4 + 1 = 2^2 + 1

    b = (q**3*(-2-q**7)*5**6 + u*q**2*(-4+3*q**7)*5**5 + u**2*q*(2+11*q**7)*5**4 + u**3*(24+7*q**7)*5**3 + u**4*q**6*(-41-38*q**7)*5**2 + u**5*q**5*(-117+44*q**7)*5 + u**6*q**11*278)
    assert mb == ma**b

    ma7 = ma6 * m232.conjugate()
    assert ma7 == m**(u**8 - 2*u**7 + 5*u**6 - 232)
    # and with (u^8 - 2*u^7 + 5*u^6 - 232), the exponent is
    # (-29*q^4 + u*q^3*(-117-44*q^7) + u^2*q^2*(-41+38*q^7) + u^3*q*(7+24*q^7) + u^4*(11+2*q^7) + u^5*q^6*(-4-3*q^7) + u^6*q^5*(-2+q^7) + u^7*q^11)

    # -29 = -32+3 = -2^5+2+1 = -16-8-4-1 = -100011
    ma7_ = ma7.conjugate()
    m8 = ((((ma7_**2)**2)**2)**2 * ma7)**2 * ma7
    m8 = m8.frobenius(4)
    assert m8 == ma7**(-29*q**4)

    ma8 = ma7**u
    ma8_ = ma8.frobenius(7)
    # 117 = 0x75 = 128 - 11   = 2^7 - 2^4 + 2^2 + 1 = 100-10101 = 100-10101 = 2^7 - 2^4 + 2^2 + 1
    # 44  = 0x2c = 32 + 8 + 4 = 2^5 + 2^3 + 2^2     = 00101 10 0= 00110-10 0 = 2^5 + 2^4 - 2^2
    ma8_x = ma8.conjugate() * ma8_
    m9 = ((((((ma8**2)**2 * ma8_)**2 * ma8_x)**2)**2 * ma8_x.conjugate())**2)**2 * ma8
    m9 = m9.frobenius(3).conjugate()
    assert m9 == ma8**(q**3*(-117-44*q**7))

    ma9 = ma8**u
    ma9_ = ma9.frobenius(7)
    #-41 =-0x29 =- 00101001              =-32 - 8 - 1
    # 38 = 0x26 =  00100110 = 32 + 4 + 2 = 32 + 8 - 2
    ma9_cj = ma9.conjugate()
    ma9_x = ma9_cj * ma9_
    m10 = ((((ma9_x**2)**2 * ma9_x)**2)**2 * ma9_.conjugate())**2 * ma9_cj
    m10 = m10.frobenius(2)
    assert m10 == ma9**(q**2*(-41+38*q**7))

    ma10 = ma9**u
    ma10_ = ma10.frobenius(7)
    #  7 =  8 - 1 =  0000100-1
    # 24 = 16 + 8 =  00011000
    m11 = (((ma10_**2 * ma10_ * ma10)**2)**2)**2 * ma10.conjugate()
    m11 = m11.frobenius()
    assert m11 == ma10**(q*(7 + 24*q**7))

    ma11 = ma10**u
    ma11_ = ma11.frobenius(7)
    # (11 + 2*q^7)
    # 11 = 1011
    #  2 = 0010
    m12 = ((ma11**2)**2 * ma11 * ma11_)**2 * ma11
    assert m12 == ma11**(11 + 2*q**7)

    ma12 = ma11**u
    ma12_ = ma12.frobenius(7)
    # q^6*(-4 - 3*q^7)
    # -4 = -100
    # -3 = -101
    m13 = ((ma12 * ma12_).conjugate()**2)**2 * ma12_
    m13 = m13.frobenius(6)
    assert m13 == ma12**(q**6*(-4 - 3*q**7))

    ma13 = ma12**u
    ma13_ = ma13.frobenius(7)
    # q^5*(-2 + q^7)
    m14 = ma13.conjugate()**2 * ma13_
    m14 = m14.frobenius(5)
    assert m14 == ma13**(q**5*(-2 + q**7))

    ma14 = ma13**u
    # q^11
    m15 = ma14.frobenius(11)

    mc = m8 * m9 * m10 * m11 * m12 * m13 * m14 * m15
    c = (-29*q**4 + u*q**3*(-117-44*q**7) + u**2*q**2*(-41+38*q**7) + u**3*q*(7+24*q**7) + u**4*(11+2*q**7) + u**5*q**6*(-4-3*q**7) + u**6*q**5*(-2+q**7) + u**7*q**11)
    assert mc == ma7**c

    r = m0.frobenius(11) * mb * mc # 2 M + frob
    # r == m**e1a
    return r
