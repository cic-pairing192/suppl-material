"""
Test file for the first GG28 family (GG28a)
See https://gitlab.inria.fr/tnfs-alpha/alpha/-/blob/master/sage/tnfs/curve/kss.py?ref_type=heads#L382
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
from pairing_gg28 import *
from test_pairing import *
from test_scalar_mult import test_glv_scalar_mult_g1_j1728
from cost_pairing import cost_pairing_gg28a
#

def test_miller_loop_opt_ate_gg28a(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=False):
    """Testing Miller loop of optimal ate pairing on Gasnier-Guillevic GG28a curve

    Testing the function miller_loop_opt_ate_gg28a(Q2, P, u)
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
    return test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=D_twist, function_name=miller_loop_opt_ate_gg28a, curve_a_is_0=False)

def test_miller_loop_opt_ate_gg28a_alt(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=False):
    """Testing Miller loop of optimal ate pairing on Gasnier-Guillevic GG28a curve

    Testing the function miller_loop_opt_ate_gg28a_alt(Q2, P, u)
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
    return test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=D_twist, function_name=miller_loop_opt_ate_gg28a_alt, curve_a_is_0=False)

def test_final_exp_hard_k28(Fpk, u, r, function_name, expected_exponent=None):
    p = Fpk.characteristic()
    if expected_exponent is None:
        expected_exponent = cyclotomic_polynomial(28)(p)//r
    ok_exp = True
    ok_r = True
    ok_inv = True
    i = 0
    while (ok_r and ok_inv and ok_exp) and i < 10:
        f0 = Fpk.random_element()
        f = final_exp_easy_k28(f0)
        g = function_name(f, u)
        ok_r = g**r == Fpk(1)
        ok_exp = g == f**expected_exponent
        ok_inv = g.frobenius(14) == 1/g
        i += 1
    print("test {}: f^r == 1: {}, f == m^expected_exp: {}, f^(p^{}) == 1/f: {}".format(function_name.__name__, ok_r, ok_exp, 14, ok_inv))
    return ok_r and ok_exp and ok_inv

def test_curve(u0, a=None):
    """
    INPUT:
    - `u0`: seed of a GG28a curve, where u0 = 309, 449, 1759, 1899 mod 2030. Note that 2030 = 2*5*7*29.
    - `a`: optional, curve coefficient in y^2 = x^3 + a*x (b=0 as j=1728).
    """
    u0 = ZZ(u0)
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 28
    D = 1
    px = (x**16 - 2*x**15 + 5*x**14 + 556*x**9 - 1344*x**8 + 2780*x**7 + 78125*x**2 - 217382*x + 390625)/16820
    rx = (x**12 + 4*x**11 + 11*x**10 + 24*x**9 + 41*x**8 + 44*x**7 - 29*x**6 + 220*x**5 + 1025*x**4 + 3000*x**3 + 6875*x**2 + 12500*x + 15625)/29
    cx = (x**4 - 6*x**3 + 18*x**2 - 30*x + 25)/580
    assert cx == (x**2 - 4*x + 5) * (x**2 - 2*x + 5) / 580 # same as GG20a
    tx = (-2*x**8 - 527*x + 145)/145
    yx = (-x**8 + 5*x**7 - 336*x + 1390)/145
    betax = (13*x**15 - 57*x**14 + 192*x**13 - 440*x**12 + 960*x**11 - 2200*x**10 + 4800*x**9 - 3772*x**8 - 9722*x**7 + 56972*x**6 - 129860*x**5 + 284860*x**4 - 649300*x**3 + 1424300*x**2 - 2230875*x + 2147767)/28594
    lambx = (x**7 + 278)/29
    m = 2030
    u_mod_m = [309, 449, 1759, 1899] # so that rx can take prime values and p = 1 mod 7
    cofactor_r = [1, 1, 1, 1]
    assert (u0 % m) in u_mod_m

    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**14-1)*(x**2+1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**12 - px**10 + px**8 - px**6 + px**4 - px**2 + 1)//rx
    exponent = ZZ(exponent_x(u0))

    # for G2, compute #E(Fp7) then compute its 4-th twist
    d = 4
    tx7 = tx**7 - 7*px*tx**5 + 14*px**2*tx**3 - 7*px**3*tx
    yx7 = yx * (tx**6 - 5*tx**4*px + 6*tx**2*px**2 - px**3) # generic formula
    px7 = px**7
    assert tx7**2 - 4*px7 == -D*yx7**2
    E2_order = px7 + 1 - yx7
    assert (E2_order % rx) == 0
    c2x = E2_order // rx
    c2xa = (x**2 - 4*x + 5)
    c2xb = (x**14 + 2*x**13 + 8*x**12 + 22*x**11 + 48*x**10 + 82*x**9 + 88*x**8 + 498*x**7 + 92*x**6 + 1238*x**5 + 4492*x**4 + 11778*x**3 + 24652*x**2 + 39718*x + 113737)
    c2xc = (c2x // c2xa) // c2xb

    txe = yx7
    yxe = tx * (tx**6 - 21*tx**4*yx**2 + 35*tx**2*yx**4 - 7*yx**6) / 2**6
    assert txe**2 - 4*px7 == -yxe**2
    g2twx = px7 + 1 + yx7

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
    print("generic formula: u - q - 2*q^8: {}".format( ((x - px - 2*px**8) % rx) == 0))
    print("generic formula: 2 + u*q^6 - q^7: {}".format( ((2 + x*px**6 - px**7) % rx) == 0))

    Fpz = Fp['z']; (z,) = Fpz._first_ngens(1)
    # extension of degree k//4
    e = k//4
    print("p mod 4 = {} p mod {} = {} p mod {} = {}".format(p % 4, e, p % e, k, p % k))
    assert (p % k) == 1
    assert (p % 4) == 1
    assert (p % e) == 1
    # we should have p = 1 mod k//4
    # to be able to define the extension with a binomial x^(k//4)+a0,
    # and because D=1, we have p=1 mod 4, consequently p = 1 mod k
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
    test_miller_loop_opt_ate_gg28a(E, EM, Fq4M, FpkM, map_Fq4M_FpkM, r, c, c2, u0, D_twist=False)
    test_miller_loop_opt_ate_gg28a_alt(E, EM, Fq4M, FpkM, map_Fq4M_FpkM, r, c, c2, u0, D_twist=False)

    print("\nFinal exponentiation")
    #test_final_exp_easy_k28(FpkM)
    #test_final_exp_hard_k28(FpkM, u0, r, function_name=final_exp_hard_gg28a_v0, expected_exponent=exponent)
    q = p
    u = u0
    e1a = (u**8 - 2*u**7 + 5*u**6-232)*(-29*q**4 + u*q**3*(-117-44*q**7) + u**2*q**2*(-41+38*q**7) + u**3*q*(7+24*q**7) + u**4*(11+2*q**7) + u**5*q**6*(-4-3*q**7) + u**6*q**5*(-2+q**7) + u**7*q**11) \
        + (u**2 - 2*u + 5) * (5**6*q**3*(-2-q**7) + 5**5*u*q**2*(-4+3*q**7) + 5**4*u**2*q*(11*q**7+2) + 5**3*u**3*(24+7*q**7) + 5**2*u**4*q**6*(-41-38*q**7) + 5*u**5*q**5*(-117+44*q**7) + 278*u**6*q**11) \
        + 3364*q**11
    assert (e1a % exponent) == 0
    test_final_exp_hard_k28(FpkM, u0, r, function_name=final_exp_hard_gg28a_v1, expected_exponent=e1a)
    print("\n")


# https://gitlab.inria.fr/tnfs-alpha/alpha/-/blob/master/sage/tnfs/param/testvector_other_sparseseed.py?ref_type=heads#L397
def test_curve_gg28a_498():
    """
    p is 498-bit long
    r is 380-bit long
    u = 309 mod 2030
    u has Hamming weight 7
    u is positive
    """
    u0 = ZZ(2**32-2**25-2**19+2**9+2**4+2**2+1)
    assert u0 == ZZ(0xfdf80215)
    a = 2
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_499():
    """
    p is 499-bit long
    r is 380-bit long
    u = 1759 mod 2030
    u has Hamming weight 7
    u is positive
    # https://gitlab.inria.fr/tnfs-alpha/alpha/-/blob/master/sage/tnfs/param/testvector_other_sparseseed.py?ref_type=heads#L397
    """
    u0 = ZZ(2**32+2**26+2**19+2**14+2**10+2**6-1)
    assert u0 == ZZ(0x10408443f)
    a = 2
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_500():
    """
    p is 500-bit long
    r is 381-bit long
    u = 1759 mod 2030
    u has Hamming weight 6
    u is negative
    # https://gitlab.inria.fr/tnfs-alpha/alpha/-/blob/master/sage/tnfs/param/testvector_other_sparseseed.py?ref_type=heads#L397
    """
    u0 = ZZ(-2**32-2**28+2**19+2**9-2**3-1)
    assert u0 == ZZ(-0x10ff7fe09)
    a = 9
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_501a():
    """
    p is 501-bit long
    r is 382-bit long
    u = 1759 mod 2030
    u has Hamming weight 7
    u is negative
    """
    u0 = ZZ(-2**32-2**29+2**24-2**16+2**10-2**8-1)
    assert u0 == ZZ(-0x11f00fd01)
    a = 2
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_501b():
    """
    p is 501-bit long
    r is 382-bit long
    u = 1759 mod 2030
    u has Hamming weight 7
    u is negative
    """
    u0 = ZZ(-2**32-2**29+2**20+2**9-2**7+2**3-1)
    assert u0 == ZZ(-0x11feffe79)
    a = 9
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_501c():
    """
    p is 501-bit long
    r is 382-bit long
    u = 1759 mod 2030
    u has Hamming weight 7
    u is negative
    """
    u0 = ZZ(-2**32-2**29-2**24+2**18+2**9-2**5-1)
    assert u0 == ZZ(-0x120fbfe21)
    a = 2
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_503():
    """
    p is 503-bit long
    r is 383-bit long
    u = 1759 mod 2030
    u has Hamming weight 7
    u is negative
    """
    u0 = ZZ(-2**32-2**30+2**28-2**26+2**17+2**2+1)
    assert u0 == ZZ(-0x133fdfffb)
    a = 2
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_504a():
    """
    p is 504-bit long
    r is 384-bit long
    u = 449 mod 2030
    u has Hamming weight 7
    u is positive
    """
    u0 = ZZ(2**32+2**30+2**23-2**16-2**8+2**5+1)
    assert u0 == ZZ(0x1407eff21)
    a = 13
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

def test_curve_gg28a_504b():
    """
    p is 504-bit long
    r is 384-bit long
    u = 1759 mod 2030
    u has Hamming weight 7
    u is negative
    """
    u0 = ZZ(-2**32-2**30-2**27-2**22-2**17-2**3+1)
    assert u0 == ZZ(-0x148420007)
    a = 13
    cost_pairing_gg28a(u0)
    test_curve(u0, a)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_gg28a_500()
    test_curve_gg28a_498()
    test_curve_gg28a_499()
    test_curve_gg28a_501a()
    test_curve_gg28a_501b()
    test_curve_gg28a_501c()
    test_curve_gg28a_503()
    test_curve_gg28a_504a()
    test_curve_gg28a_504b()
