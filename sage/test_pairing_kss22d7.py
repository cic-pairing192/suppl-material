"""
Test pairings on new Gasnier curve k=22 D=7
Date: 2023, May 30
"""
from sage.all_cmdline import *   # import sage library

from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.misc.functional import cyclotomic_polynomial
from sage.rings.finite_rings.finite_field_constructor import FiniteField, GF
from sage.schemes.elliptic_curves.constructor import EllipticCurve

# this is much much faster with this statement:
# proof.arithmetic(False)
from sage.structure.proof.all import arithmetic

from pairing import *
from pairing_kss22d7 import *
from test_pairing import *
#from test_scalar_mult import test_glv_scalar_mult_g1_j_3375
from cost_pairing import cost_pairing_kss22d7

def test_curve(u0, a=None, b=None):
    # u0 = (-2**21+2**19+2**14-2**11-2**9-2**3+2)
    # a = -35
    # b = 98
    print("u0 = {:#x}".format(u0))
    #preparse("QQx.<x> = QQ[]")
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    # from gitlab.inria.fr/tnfs-alpha/alpha sage/tnfs/curve/kss.py
    k = 22
    D = 7
    px = (x**24 - x**23 + 2*x**22 + 67*x**13 + 94*x**12 + 134*x**11 + 2048*x**2 + 5197*x + 4096)/7406
    qx = px
    rx = (x**20 - x**19 - x**18 + 3*x**17 - x**16 - 5*x**15 + 7*x**14 + 3*x**13 - 17*x**12 + 11*x**11 + 23*x**10 + 22*x**9 - 68*x**8 + 24*x**7 + 112*x**6 - 160*x**5 - 64*x**4 + 384*x**3 - 256*x**2 - 512*x + 1024)/23 # and sometimes / 23^2
    cx = (x**2 - x + 2) * (x**2 + x + 2) / (2 * 7 * 23)
    tx = (x**12 + 45*x + 46)/46
    yx = (x**12 - 4*x**11 - 47*x - 134)/322
    # D = 7 = 3 mod 4 -> Chi = x**2 + x + 2 has roots (-1+sqrt(-7))/2 and (-1 - sqrt(-7))/2
    betax = (11*x**23 - 20*x**22 + 53*x**21 - 58*x**20 + 106*x**19 - 116*x**18 + 212*x**17 - 232*x**16 + 424*x**15 - 464*x**14 + 848*x**13 - 191*x**12 + 1322*x**11 + 1051*x**10 - 172*x**9 + 2102*x**8 - 344*x**7 + 4204*x**6 - 688*x**5 + 8408*x**4 - 1376*x**3 + 16816*x**2 + 19776*x + 36142)/18515 # mod p
    lambx = (x**11 + 22)/23 # mod r
    assert ((betax**2 + betax + 2) % px) == 0
    mux = -lambx-1
    assert ((lambx**2 + lambx + 2) % rx) == 0
    chi = x**2 + x + 2
    if (D % 4) == 3:
        assert ((betax**2 + betax + (D+1)//4) % px) == 0
        assert ((lambx**2 + lambx + (D+1)//4) % rx) == 0
        assert ((mux**2 + mux + (D+1)//4) % rx) == 0
    else:
        assert ((betax**2 + 1) % px) == 0
        assert ((lambx**2 + 1) % rx) == 0
        assert ((mux**2 + 1) % rx) == 0

    m = 161 # 7 * 23
    print("u0 mod {} = {}".format(m, u0 % m))
    u1_mod_m = [32, 151]
    u2_mod_m = [4,18,25,39,81,95,116,123,144]
    if (u0 % m) in u2_mod_m:
        rx = rx/23
        cx = cx*23
        u_mod_m = u2_mod_m
    else:
        assert (u0 % m) in u1_mod_m
        u_mod_m = u1_mod_m
    ### cofactor of G2 defined over GF(p^11)
    #ZZqty.<q,t,y> = ZZ[]
    #t2 = t*t - 2*q
    #t3 = t*t2 -q*t
    #t4 = t*t3 -q*t2
    #t5 = t*t4 -q*t3
    #t6 = t*t5 -q*t4
    #t7 = t*t6 -q*t5
    #t8 = t*t7 -q*t6
    #t9 = t*t8 -q*t7
    #t10 = t*t9 -q*t8
    #t11 = t*t10 -q*t9
    tx11 = tx**11 - 11*px*tx**9 + 44*px**2*tx**7 - 77*px**3*tx**5 + 55*px**4*tx**3 - 11*px**5*tx
    E2_order = px**11 + 1 + tx11
    assert E2_order % (px + 1 + tx) == 0 # this is (q + 1 + t)
    assert ((E2_order // (px + 1 + tx)) % rx) == 0
    assert (E2_order % rx) == 0
    c2x = E2_order // rx # reducible with 3 factors
    c2xa = (x**2 + x + 2)/2
    c2xb = (x**22 - 2*x**21 + 2*x**20 + 2*x**19 - 6*x**18 + 2*x**17 + 10*x**16 - 14*x**15 - 6*x**14 + 34*x**13 - 22*x**12 + 21*x**11 + 278*x**10 - 186*x**9 - 370*x**8 + 742*x**7 - 2*x**6 - 1482*x**5 + 1486*x**4 + 1478*x**3 - 4450*x**2 + 1494*x + 9454)/(2 * 23)
    c2xc = c2x//(c2xa*c2xb)
    if u0 in u1_mod_m:
        c2xa = c2xa/23
        c2xb = c2xb/7
        c2xc = c2xc * 7 * 23
    else:
        c2xb = c2xb/(7*23)
        c2xc = c2xc * 7 * 23
    #if (u0 % 2) == 0:
    ### final exp
    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**11-1)*(x+1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**10 - px**9 + px**8 - px**7 + px**6 - px**5 + px**4 - px**3 + px**2 - px + 1)//rx
    exponent = ZZ(exponent_x(u0))
    sx = (x**41 - 2*x**40 + 2*x**39 + 2*x**38 - 6*x**37 + 2*x**36 + 10*x**35 - 14*x**34 - 6*x**33 + 34*x**32 - 22*x**31 + 89*x**30 - 19*x**29 + 111*x**28 - 73*x**27 - 149*x**26 + 295*x**25 + 3*x**24 - 593*x**23 + 587*x**22 + 599*x**21 - 1773*x**20 + 7179*x**19 + 7956*x**18 - 1700*x**17 - 14212*x**16 + 17612*x**15 + 10812*x**14 - 46036*x**13 + 24412*x**12 + 67660*x**11 - 116484*x**10 - 18836*x**9 + 391068*x**8)
    s1 = ZZ(sx(u0))
    expected_exp =  sx * exponent_x
    eee = ZZ(expected_exp(u0))
    assert eee == s1 * exponent
    ee1 = 23**2 * eee

    p = ZZ(px(u0))
    r = ZZ(rx(u0))
    c = ZZ(cx(u0))
    c2 = ZZ(c2x(u0))
    t = ZZ(tx(u0))
    y = ZZ(yx(u0))
    Fp = GF(p, proof=False)
    t11 = ZZ(tx11(u0))
    assert (p**11 + 1 + t11) == c2 * r
    #if a is None or b is None:
    #    a, b, E = find_curve_parameter_ab(Fp, r, c)
    #else:
    j = -3375
    a_ = Fp(3*j)/Fp(1728-j)
    b_ = Fp(2*j)/Fp(1728-j)
    if (Fp(-3/a_)).is_square():
        s1 = sqrt(Fp(-3/a_))
        a1 = -3
        b1 = b_ * s1**3
        E1 = EllipticCurve(Fp, [a1, b1])
        P = E1.random_element()
        if not r*c *P == E1(0) and not Fp(-1).is_square():
            b1 = -b1
            E1 = EllipticCurve(Fp, [a1, b1])
            P = E1.random_element()
            if r*c *P == E1(0):
                a = a1
                b = b1
        else:
            a = a1
            b = b1
    E = EllipticCurve(Fp, [a, b])

    if a == -3:
        print("new Gasnier k{}D{}-{} E: y^2 = x^3 {:+d}*x {:+d} /Fp of {} bits".format(k, D, p.nbits(), a, ZZ(b), p.nbits()))
    else:
        print("new Gasnier k{}D{}-{} E: y^2 = x^3 {:+d}*x {:+d} /Fp of {} bits".format(k, D, p.nbits(), a, b, p.nbits()))
    print("u = {:#x}".format(u0))
    print("p = {:#x} # {} bits, {} mod k, log_2 p^{} = {:.2f}, {} bits".format(p, p.nbits(), p % k, k, float((k*log(p)/log(2)).n()), ceil((k*log(p)/log(2)).n())))
    print("r = {:#x} # {} bits".format(r, r.nbits()))
    print("c = {:#x} # {} bits".format(c, c.nbits()))
    print("y = {:#x}".format(y))
    print("t = {:#x}".format(t))

    print("p = {} mod 4".format(p % 4))
    print("p-1 has 2-valuation {}".format((p-1).valuation(2)))
    print("r-1 has 2-valuation {}".format((r-1).valuation(2)))
    lambda_mod_r = ZZ(lambx(u0))
    beta_mod_p = Fp(betax(u0))

    Fpz = Fp['z']; (z,) = Fpz._first_ngens(1)
    # define Fp11
    d = 2 # quadratic twist
    e = k//d
    a0 = -1
    if (p % e) == 1:
        a1 = 0
    else:
        a1 = 1
    while not (z**e + a1*z - a0).is_irreducible():
        a0 = a0+1
    if a0 == 0:
        print("Fp{} = Fp[x]/(x^{} - {})".format(e, e, a0))
    else:
        print("Fp{} = Fp[x]/(x^{} + x - {})".format(e, e, a0))
    Fpe = Fp.extension(z**e + a1*z - a0, names=('i',)); (i,) = Fpe._first_ngens(1)
    Fp11 = Fpe
    Fq = Fpe
    Fp11s = Fp11['s']; (s,) = Fp11s._first_ngens(1)
    xiM, atwM, btwM = find_twist_curve_parameter_xi_ab(a, Fq, r, c2, d=2, D_twist=False, ba=b, find_mult_i=False)
    EM = EllipticCurve(Fq, [Fq(atwM), Fq(btwM)])

    Fq2M = Fq.extension(s**2 - xiM, names=('wM',)); (wM,) = Fq2M._first_ngens(1)
    Eq2M = EllipticCurve([Fq2M(a), Fq2M(b)])

    try:
        coeffs_xiM = xiM.polynomial().list()
    except AttributeError as err:
        coeffs_xiM = xiM.list()
    i0M = coeffs_xiM[0]
    i1M = coeffs_xiM[1]
    i0m = ZZ(i0M)
    if abs(i0m - p) < abs(i0m):
        i0m = i0m - p
    i1m = ZZ(i1M)
    if abs(i1m - p) < abs(i1m):
        i1m = i1m - p
    if i0m == 0:
        str_xiM = ""
    else:
        str_xiM = "{}".format(i0m)
    if i1m == 1:
        if len(str_xiM) == 0:
            str_xiM = "i"
        else:
            str_xiM += "+i"
    elif i1m == -1:
        str_xiM += "-i"
    elif i1m != 0:
        if len(str_xiM) == 0:
            str_xiM = "{}*i".format(i1m)
        else:
            str_xiM += "{:+}*i".format(i1m)
    print("M-twist xiM = {}".format(str_xiM))
    # xi = i0 + i*i1
    # s^d - xi = 0 <=> s^d - i0 = i1*i <=> (s^d - i0)^e = i1^e*(i^e) where here i^e + a1*i - a0 = 0
    #                                  <=> (s^d - i0)^e = i1^e*(-a1*i + a0) and where i = (s^d-i0)/i1
    # resultant(s^d-xi, z^e - a0)
    # resultant(s^d-xi, z^e -z - a0)
    poly_M = Fpz((z**d - i0M)**e - i1M**e * (a0-a1*(z**d-i0M)/i1M))
    assert poly_M.is_irreducible()
    FpkM = Fp.extension(poly_M, names=('SM',)); (SM,) = FpkM._first_ngens(1)
    EkM = EllipticCurve(FpkM, [FpkM(a), FpkM(b)])
    
    def map_Fq2M_FpkM(x, aM=None):
        if aM is None:
            # evaluate elements of Fq2M = Fp[i]/(i^e-a1*z-a0)[s]/(s^2-xiM) at i=S^2-i0 and s=S
            return sum([xi.polynomial()((SM**2-i0M)/i1M) * SM**ei for ei,xi in enumerate(x.list())])
        else:
            return sum([xi.polynomial()((aM**2-i0M)/i1M) * aM**ei for ei,xi in enumerate(x.list())])

    def map_Fq_FpkM(x):
        # evaluate elements of Fq=Fp[i] at i0+i1*i=wM^2 <=> i = (wM^2 - i0)/i1
        return x.polynomial()((SM**2-i0M)/i1M)

    print("test E (G1)")
    test_order(E,r*c)
    print("test E' (G2) M-twist")
    test_order(EM,r*c2)

    print("test Frobenius map on G2 with M-twist")
    test_g2_frobenius_eigenvalue(EkM, EM, Fq2M, map_Fq2M_FpkM, r, c2, D_twist=False)
    test_g2_frobenius_eigenvalue_alt(EkM, EM, map_Fq_FpkM, r, c2, D_twist=False)

    #print("test GLV on G1") # this function is defined in test_scalar_mult.py
    #test_glv_scalar_mult_g1_j_3375(E, lambda_mod_r, beta_mod_p, r, c)

    print("\nFinal exponentiation")
    test_final_exp_easy_k22(FpkM)
    test_final_exp_hard_k22(FpkM, u0, r, final_exp_hard_kss22d7, expected_exponent=ee1)

    print("test Miller M-twist tate")
    test_miller_function_tate(E, Eq2M, EM, r, c, c2, D_twist=False)
    test_miller_function_tate_2naf(E, Eq2M, EM, r, c, c2, D_twist=False)

    print("test Miller M-twist ate")
    test_miller_function_ate(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_2naf(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)

    print("test Miller M-twist optimal ate")
    assert ((u0**2 - u0*p + 2*p**2) % r) == 0
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_kss22d7_v0, curve_a_is_0=False)
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_kss22d7_v1, curve_a_is_0=False)
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_kss22d7, curve_a_is_0=False)

"""
Seed for the tests.
There are very few seeds for small r.
To ensure valid parameters, these congruences are required:

- u mod 161 in [4, 18, 25, 39, 81, 95, 116, 123, 144], in which case
  rx = (x^20-x^19-x^18+3*x^17-x^16-5*x^15+7*x^14+3*x^13-17*x^12+11*x^11+23*x^10+22*x^9-68*x^8+24*x^7+112*x^6-160*x^5-64*x^4+384*x^3-256*x^2-512*x+1024)/23^2
  can take prime values (the denominator is 23^2),
  the smallest seed in absolute value is u0 = 0x21e0d (r 333 bits), the next ones are
  -0x2a1df (r 339 bits), 0x459dd (r 354 bits), 0x4c545 (r 357 bits), -0x6ea5b (r 367 bits),
  0x7657d (r 369 bits), -0x81387 (r 372 bits), -0x9921f (r 377 bits), -0xaa07f (r 380 bits),
  -0xbad1f (r 382 bits), -0xbe503 (r 383 bits).
- u mod 161 in [32, 151], in that case rx has denominator 23 instead of 23^2.
  The smallest possible seeds are 0x2acc4d (r 424 bits), -0x30c83b (r 428 bits).
  they are not considered here as the target is r of 384 bits.

"""

def test_curve_398_r333():
    """
    the smallest possible positive seed for this family such that r is prime (no extra cofactor)
    """
    u0 = ZZ(0x21e0d)
    assert u0 == ZZ(2**17+2**13-2**9+2**4-2**2+1)
    a = -35
    b = 98
    test_curve(u0, a, b)

def test_curve_405_r339():
    """
    the smallest possible (in absolute value) negative seed for this family such that r is prime (no extra cofactor)
    """
    u0 = ZZ(-0x2a1df)
    assert u0 == ZZ(-2**17-2**15-2**13-2**9+2**5+1)
    a = -140
    b = -784
    test_curve(u0, a, b)

def test_curve_423_r354():
    u0 = ZZ(0x459dd)
    assert u0 == ZZ(2**18+2**15-2**13-2**11+2**9-2**5-2**2+1)
    a = -35
    b = 98
    test_curve(u0, a, b)

def test_curve_426_r357():
    u0 = ZZ(0x4c545)
    assert u0 == ZZ(2**18+2**16-2**14+2**10+2**8+2**6+2**2+1)
    a = -35
    b = 98
    test_curve(u0, a, b)

def test_curve_457_r383():
    """
    a candidate seed for the 192-bit security level, where r is 383-bit long
    u = 39 mod 161
    p = 3 mod 4
    p = 3 mod 22
    Fp11 = Fp[x]/(x^11 + x - 19)
    """
    u0 = ZZ(-2**20+2**18+2**13-2**10-2**8-2**2+1)
    assert u0 == ZZ(-0xbe503)
    a = -35
    b = 98
    a = -3
    b = 16806296633675137692941161698425243995945536384673987074099085232255627899013123230887236540008521324983146155427204619039320988876685056
    cost_pairing_kss22d7(u0,lower_bound_m11=False, a_3=True)
    test_curve(u0, a, b)

def test_curve_457_r382():
    """
    a candidate seed for the 192-bit security level, where r is 382-bit long
    u = 18 mod 161
    p = 1 mod 4
    p = 5 mod 22
    Fp11 = Fp[x]/(x^11 + x - 7)
    """
    u0 = ZZ(-2**20+2**18+2**14+2**12+2**10-2**8-2**5+1)
    assert u0 == ZZ(-0xbad1f)
    a = -140
    b = -784
    cost_pairing_kss22d7(u0,lower_bound_m11=False)
    test_curve(u0, a, b)

def test_curve_453_r380():
    """
    a candidate seed for the 192-bit security level, where r is 380-bit long
    u = 39 mod 161
    p = 1 mod 4
    p = 17 mod 22
    Fp11 = Fp[x]/(x^11 + x - 9)
    """
    u0 = ZZ(-2**19-2**17-2**15-2**13-2**7+1)
    assert u0 == ZZ(-0xaa07f)
    a = -140
    b = -784
    cost_pairing_kss22d7(u0,lower_bound_m11=False)
    test_curve(u0, a, b)

def test_curve_450_r377():
    """
    a candidate seed for the 192-bit security level, where r is 377-bit long
    u = 25 mod 161
    p = 1 mod 4
    p = 5 mod 22
    Fp11 = Fp[x]/(x^11 + x - 3)
    """
    u0 = ZZ(-2**19-2**17+2**15-2**12-2**9-2**5+1)
    assert u0 == ZZ(-0x9921f)
    a = -140
    b = -784
    cost_pairing_kss22d7(u0,lower_bound_m11=False)
    test_curve(u0, a, b)

def test_curve_441_r369():
    """
    a seed where r is 369-bit long
    u = 123 mod 161
    p = 3 mod 4
    p = 17 mod 22
    Fp11 = Fp[x]/(x^11 + x - 19)
    """
    u0 = ZZ(2**19-2**15-2**13+2**11-2**9-2**7-2**2+1)
    assert u0 == ZZ(0x7657d)
    a = -35
    b = 98
    cost_pairing_kss22d7(u0,lower_bound_m11=False)
    test_curve(u0, a, b)

def test_curve_502_r424():
    """
    a seed u mod 161 in [32, 151] such that r = (u^20 + ...)/23 is prime,
    with denominator 23 (not 23^2)
    this is the smallest possible seed with congurence mod 161 in [32, 151] such that r is prime
    u = 32 mod 161
    p = 3 mod 4
    p = 5 mod 22
    Fp11 = Fp[x]/(x^11 + x - 10)
    """
    u0 = ZZ(2**22-2**20-2**18-2**16-2**14+2**12-2**10+2**6+2**4-2**2+1)
    assert u0 == ZZ(0x2acc4d)
    a = -35
    b = 98
    cost_pairing_kss22d7(u0,lower_bound_m11=False)
    test_curve(u0, a, b)

def test_curve_506_r428():
    """
    a seed u mod 161 in [32, 151] such that r = (u^20 + ...)/23 is prime,
    with denominator 23 (not 23^2)
    this is the smallest possible (|u| in absolute value) negatitve seed
    with congurence mod 161 in [32, 151] such that r is prime
    u = 151 mod 161
    p = 3 mod 4
    p = 19 mod 22
    Fp11 = Fp[x]/(x^11 + x - 16)
    """
    u0 = ZZ(-2**22+2**20-2**16+2**14-2**11-2**6+2**2+1)
    assert u0 == ZZ(-0x30c83b)
    a = -35
    b = 98
    cost_pairing_kss22d7(u0,lower_bound_m11=False)
    test_curve(u0, a, b)

def test_curve_511_r432():
    """
    another seed just for the tests
    u = 32 mod 161
    p = 1 mod 4
    p = 21 mod 22
    Fp11 = Fp[x]/(x^11 + x - 22)
    """
    u0 = ZZ(-2**22+2**19+2**14+2**12-2**9+2**6-2**4+1)
    assert u0 == ZZ(-0x37b1cf)
    a = -140
    b = -784
    a = -3
    b = 2451688138135442916130863854973309588719794023758485677037705616128265466751694590750433115907196548865937949001139011482295470329114698059875580033637373
    cost_pairing_kss22d7(u0,lower_bound_m11=False, a_3=True)
    test_curve(u0, a, b)

if __name__ == "__main__":
    arithmetic(False)
    # size of r compatible with the 192-bit security level:
    test_curve_457_r383()
    test_curve_457_r382()
    test_curve_453_r380()
    test_curve_450_r377()

    # other seeds for smaller sizes of parameters for the tests:
    #test_curve_398_r333()
    #test_curve_405_r339()
    #test_curve_423_r354()
    #test_curve_426_r357()
    #test_curve_441_r369()

    # seeds with r = (u^20 + ...)/23 (not 23^2 but 23 at the denominator)
    #test_curve_502_r424()
    #test_curve_506_r428()
    #test_curve_511_r432()

