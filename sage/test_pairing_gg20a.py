"""
Test file for the first GG20 family (GG20a)
"""
from sage.all_cmdline import *   # import sage library
#
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.misc.functional import cyclotomic_polynomial
from sage.rings.finite_rings.finite_field_constructor import FiniteField, GF
from sage.schemes.elliptic_curves.constructor import EllipticCurve
#
# this is much much faster with this statement:
# proof.arithmetic(False)
from sage.structure.proof.all import arithmetic
##
from pairing import *
from pairing_gg20 import *
from test_pairing import *
from test_scalar_mult import test_glv_scalar_mult_g1_j1728
from cost_pairing import cost_pairing_gg20
#

def test_miller_loop_opt_ate_gg20a(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=False):
    """Testing Miller loop of optimal ate pairing on Gasnier-Guillevic GG20a curve

    Testing the function miller_loop_opt_ate_gg20a(Q2, P, u)
    where Q2 and P are both of order r and in E(Fpk) but in distinct subgroups
    To obtain valid Q2, first Q of order r is sampled from E2(Fq) then
    a map (D-twist or M-twist) is applied to Q to obtain Q2 in E_Fqd,
    and then finally in E(Fpk).

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E2`: quartic twist over GF(q) where q = p^{k/d} of order r*c2
    - `Fqd`: degree d extension over Fq, where q = p^{k/d}
    - `Fpk`: absolute extension over Fp, isomorphic to Fqd
    - `map_Fqd_Fpk`: the isomorphism map from Fqd to Fpk
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `u`: the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    return test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=D_twist, function_name=miller_loop_opt_ate_gg20a, curve_a_is_0=False)

def test_curve(u0, a=None):
    """
    INPUT:
    - `u0`: seed of a GG20a curve, where u0 = 1715, 1815 mod 2050. Note that 2050 = 2*5^2*41.
    - `a`: optional, curve coefficient in y^2 = x^3 + a*x (b=0 as j=1728).
    """
    u0 = ZZ(u0)
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 20
    D = 1
    px = (x**12 - 2*x**11 + 5*x**10 + 76*x**7 + 176*x**6 + 380*x**5 + 3125*x**2 + 12938*x + 15625)/33620
    rx = (x**8 + 4*x**7 + 11*x**6 + 24*x**5 + 41*x**4 + 120*x**3 + 275*x**2 + 500*x + 625)/25625
    cx = 125*(x**4 - 6*x**3 + 18*x**2 - 30*x + 25)/164
    assert cx == 125*(x**2 - 2*x + 5) * (x**2 - 4*x + 5)/164
    tx = (2*x**6 + 117*x + 205)/205
    yx = (x**6 - 5*x**5 - 44*x - 190)/205
    betax = (7*x**11 - 23*x**10 + 88*x**9 - 160*x**8 + 440*x**7 - 268*x**6 + 1682*x**5 + 1868*x**4 - 340*x**3 + 9340*x**2 + 20175*x + 68633)/43706
    lambx = (x**5 + 38)/41
    # m = 410
    # u_mod_m = [69, 75, 79, 135, 175, 239, 299, 315, 325, 339]
    m = 2050 # 2*5**2*41
    #u_mod_m = [315, 1365, 1715, 1815, 1965]
    #cofactor_r = [41, 41, 1, 1, 41]
    u_mod_m = [1715, 1815]
    cofactor_r = [1, 1]
    assert (u0 % m) in u_mod_m

    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**10-1)*(x**2+1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**8 - px**6 + px**4 - px**2 + 1)//rx
    exponent = ZZ(exponent_x(u0))

    # for G2, compute #E(Fp5) then compute its 4-th twist
    d = 4
    tx5 = tx**5 - 5*px*tx**3 + 5*px**2*tx
    #yx5 = yx * (5*tx**4 - 10*tx**2*yx**2 + yx**4)/16
    yx5 = yx * (tx**4 - 3*px*tx**2 + px**2) # generic formula
    px5 = px**5
    assert tx5**2 - 4*px5 == -D*yx5**2
    E2_order = px5 + 1 + yx5
    assert (E2_order % rx) == 0
    c2x = E2_order // rx

    #print("tx^2-4*px/yx^2 = {}".format((tx**2 - 4*px)/yx**2))
    assert tx**2 - 4*px == -D*yx**2
    p = ZZ(px(u0))
    r = ZZ(rx(u0))
    c = ZZ(cx(u0))
    t = ZZ(tx(u0))
    y = ZZ(yx(u0))
    c2 = ZZ(c2x(u0))
    lambda_mod_r = ZZ(lambx(u0))

    Fp = GF(p, proof=False)
    beta_mod_p = Fp(betax(u0))
    if a is None:
        a, E = find_curve_parameter_a(Fp, r, c) #E/Fp: y^2 = x^3 + a*x
    else:
        E = EllipticCurve(Fp, [a, 0])
    print("Gasnier-Guillevic GG20a-{} E: y^2 = x^3 {:+d}x /Fp of {} bits".format(p.nbits(), a, p.nbits()))
    print("u = {:#x} {} bits".format(u0, u0.nbits()))
    print("p = {:#x} {} bits".format(p, p.nbits()))
    print("r = {:#x} {} bits".format(r, r.nbits()))
    print("c = {:#x} {} bits".format(c, c.nbits()))
    print("t = {:#x} {} bits".format(t, t.nbits()))
    print("c2 = {:#x} {} bits".format(c2, c2.nbits()))

    print("short vector for optimal ate pairing")
    print("generic formula: x - qx + 2*qx^6: {}".format( ((x - px + 2*px**6) % rx) == 0))
    # LLL in SageMath
    # euler_phi = Phi_k.degree()
    # col1 = Matrix(ZZ, euler_phi-1, 1, [((t-1)**j) % r for j in range(1, euler_phi)])
    # N = block_matrix(ZZ, [ [Matrix(ZZ, 1, 1, [r]), zero_matrix(ZZ, 1, euler_phi-1)], [col1, 1]])
    # print(N.LLL())

    Fpz = Fp['z']; (z,) = Fpz._first_ngens(1)
    # extension of degree k//4
    e = k//4
    print("p mod 4 = {} p mod 5 = {} p mod 20 = {}".format(p % 4, p % 5, p % 20))
    #assert (p % k) == 1
    assert (p % 4) == 1
    #assert (p % (k//4)) == 1
    # we should have p = 1 mod k//4 to be able to define the extension with a binomial x^(k//4)+a0, and because D=1, we have p=1 mod 4, consequently p = 1 mod k
    # do not start with a0 = -1: p = 1 mod 4 so (-1) is a square
    a0 = 2
    if (p % e) != 1:
        a1 = 1
    else:
        a1 = 0
    while not (z**e + a1*z - a0).is_irreducible():
        a0 = a0+1
    if a1 == 0:
        print("Fp{} = Fp[x]/(x^{} - {})".format(e, e, a0))
    else:
        print("Fp{} = Fp[x]/(x^{} + x - {})".format(e, e, a0))
    Fpe = Fp.extension(z**e + a1*z - a0, names=('i',)); (i,) = Fpe._first_ngens(1)
    Fq = Fpe
    Fpes = Fpe['s']; (s,) = Fpes._first_ngens(1)
    xiM, atwM = find_twist_curve_parameter_xi_ab(a, Fpe, r, c2, d=4, D_twist=False)
    EM = EllipticCurve([Fpe(atwM), Fpe(0)])
    Fq4M = Fpe.extension(s**4 - xiM, names=('wM',)); (wM,) = Fq4M._first_ngens(1)
    Eq4M = EllipticCurve([Fq4M(a), Fq4M(0)])

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
    # s^4 - xi = 0 <=> s^4 - i0 = i1*i <=> (s^4 - i0)^e = i1^e*(i^e) where i^e + a1*i - a0 = 0
    #                                  <=> (s^4 - i0)^e = i1^e*(-a1*i + a0) and where i = (s^4 - i0)/i1
    # resultant(s^4-xi, z^e +a1*z - a0)
    poly_M = Fpz((z**4 - i0M)**e - i1M**e * (a0-a1*(z**4-i0M)/i1M))
    assert poly_M.is_irreducible()
    FpkM = Fp.extension(poly_M, names=('SM',)); (SM,) = FpkM._first_ngens(1)
    EkM = EllipticCurve([FpkM(a), FpkM(0)])

    try:
        test_xiM = -Fq4M.modulus().constant_coefficient()
        print("xiM == -Fq4M.modulus().constant_coefficient(): {}".format(xiM == test_xiM))
    except AttributeError as err:
        print("xiM = -Fq4M.modulus().constant_coefficient() raised an error:\n{}".format(err))
    try:
        test_xiM = -Fq4M.polynomial().constant_coefficient() # works only for absolute extensions on prime fields
        print("xiM == -Fq4M.polynomial().constant_coefficient(): {}".format(xiM == test_xiM))
    except AttributeError as err:
        print("xiM = -Fq4M.polynomial().constant_coefficient() raised an error:\n{}".format(err))

    def map_Fq4M_FpkM(x, aM=None):
        if aM is None:
            # evaluate elements of Fq4M = Fp[i]/(i^e-a1*z-a0)[s]/(s^4-xiM) at i=S^4-i0 and s=S
            return sum([xi.polynomial()((SM**4-i0M)/i1M) * SM**ei for ei,xi in enumerate(x.list())])
        else:
            return sum([xi.polynomial()((aM**4-i0M)/i1M) * aM**ei for ei,xi in enumerate(x.list())])

    def map_Fq_FpkM(x):
        # evaluate elements of Fq=Fp[i] at i0+i1*i=wM^4 <=> i = (wM^4 - i0)/i1
        return x.polynomial()((SM**4-i0M)/i1M)

    print("test E (G1)")
    test_order(E,r*c)
    print("test E' (G2) M-twist")
    test_order(EM,r*c2)

    print("test Frobenius map on G2 with M-twist")
    test_g2_frobenius_eigenvalue(EkM, EM, Fq4M, map_Fq4M_FpkM, r, c2, D_twist=False)
    test_g2_frobenius_eigenvalue_alt(EkM, EM, map_Fq_FpkM, r, c2, D_twist=False)

    #print("Test endomorphism on G2")
    #test_G2_endomorphism(EM, Eq4M, D_twist=False)
    # TODO check updates of test_pairing.py in snark2chains
    # this function is defined in test_pairing_bls12 but it works only for G2 defined over Fp2

    print("test GLV on G1") # this function is defined in test_scalar_mult.py
    test_glv_scalar_mult_g1_j1728(E, lambda_mod_r, beta_mod_p, r, c)

    print("test Miller M-twist tate")
    test_miller_function_tate(E, Eq4M, EM, r, c, c2, D_twist=False)
    test_miller_function_tate_2naf(E, Eq4M, EM, r, c, c2, D_twist=False)

    print("test Miller M-twist ate")
    test_miller_function_ate(E, Eq4M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_2naf(E, Eq4M, EM, r, c, c2, t-1, D_twist=False)

    print("test Miller M-twist optimal ate")
    test_miller_loop_opt_ate_gg20a(E, EM, Fq4M, FpkM, map_Fq4M_FpkM, r, c, c2, u0, D_twist=False)

    print("\nFinal exponentiation")
    test_final_exp_easy_k20(FpkM)
    test_final_exp_hard_k20(FpkM, u0, r, function_name=final_exp_hard_gg20a_v0, expected_exponent=41*exponent)
    q = p
    u = u0
    e2 = (u**6 - 2*u**5 + 5*u**4 + 328)*(-41*q**2 + u*q*(7 - 24*q**5) + u**2*(11 - 2*q**5) + u**3*q**4*(4 - 3*q**5) + u**4*q**3*(2 + q**5) + u**5*q**7) \
       + (u**2 - 2*u + 5) * (625*q*(2 - q**5) + 125*u*(4 + 3*q**5) + 25*u**2*q**4*(11 + 2*q**5) + 5*u**3*q**3*(7 + 24*q**5) + 38*u**4*q**7) \
       + 6724*q**7
    assert (e2 % exponent) == 0
    sx2 = QQx(-(3*x**29 + 27*x**27 + 48*x**26 + 132*x**25 + 694*x**24 + 2460*x**23 + 8118*x**22 + 21892*x**21 + 57128*x**20 + 147530*x**19 + 422464*x**18 + 1209858*x**17 + 3317032*x**16 + 7930788*x**15 + 15961692*x**14 + 31386156*x**13 + 68674492*x**12 + 153733828*x**11 + 292155352*x**10 + 405499143*x**9 + 250478512*x**8 - 695646185*x**7 - 3588683800*x**6 - 7346919200*x**5 - 11932539050*x**4 - 15038685200*x**3 - 13744450250*x**2)/861512500)
    s2 = ZZ(sx2(u0))
    assert s2 * exponent == e2
    test_final_exp_hard_k20(FpkM, u0, r, function_name=final_exp_hard_gg20a_v1, expected_exponent=e2)
    test_final_exp_hard_k20(FpkM, u0, r, function_name=final_exp_hard_gg20a_v2, expected_exponent=e2)
    print("\n")

def test_curve_gg20a_576d():
    """
    p is 576-bit long
    r is 379-bit long
    u = 1715 mod 2050
    u has Hamming weight 7
    u is negative
    """
    u0 = -ZZ(2**49+2**46+2**41+2**18+2**3+2**2+1)
    assert u0 == ZZ(-0x242000004000d)
    a = 2
    cost_pairing_gg20(u0)
    test_curve(u0, a)

def test_curve_gg20a_576a():
    """
    p is 576-bit long
    r is 380-bit long
    u = 1715 mod 2050
    u has Hamming weight 8
    u is positive
    u is the largest possible positive seed of Hamming weight <= 8 such that r is the largest possible (380 bits) while p is machine-word aligned of 576 bits
    """
    u0 = ZZ(2**49+2**46+2**44+2**40+2**34+2**27+2**14+1)
    assert u0 == ZZ(0x2510408004001)
    a = 2
    cost_pairing_gg20(u0)
    test_curve(u0, a)

def test_curve_gg20a_576b():
    """
    p is 576-bit long
    r is 380-bit long
    u = 1715 mod 2050
    u has Hamming weight 8 in 2-naf form
    u is positive
    u is the largest possible positive seed of Hamming weight 2-NAF <= 8 such that r is the largest possible (380 bits) while p is machine-word aligned of 576 bits
    """
    u0 = ZZ(2**49+2**46+2**44+2**42-2**40-2**17-2**5-1)
    assert u0 == ZZ(0x252fffffdffdf)
    a = 1
    cost_pairing_gg20(u0)
    test_curve(u0, a)

def test_curve_gg20a_576c():
    """
    p is 576-bit long
    r is 380-bit long
    u = 1715 mod 2050
    u has Hamming weight 8 in 2-naf form
    u is negative
    u is the largest possible (in absolute value) negative seed of Hamming weight 2-NAF <= 8 such that r is the largest possible (380 bits) while p is machine-word aligned of 576 bits
    """
    u0 = ZZ(-2**49-2**47+2**45+2**43+2**28+2**21+2**3-1)
    assert u0 == ZZ(-0x257ffefdffff9)
    a = 1
    cost_pairing_gg20(u0)
    test_curve(u0, a)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_gg20a_576d()
    test_curve_gg20a_576a()
    test_curve_gg20a_576b()
    test_curve_gg20a_576c()
