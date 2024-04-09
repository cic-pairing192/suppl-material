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
from test_pairing import *
from cost_pairing import cost_pairing_bls21


def test_curve(u0, b):
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 21
    D = 3
    rx = x**12 - x**11 + x**9 - x**8 + x**6 - x**4 + x**3 - x + 1
    tx = x + 1
    yx = (x - 1)/3 * (2*x**7 + 1)
    cx = (x - 1)**2/3 * (x**2 + x + 1)
    #px = (x^16 - 2*x^15 + x^14 + x^9 - 2*x^8 + x^7 + x^2 + x + 1)/3
    px = cx*rx + tx - 1
    assert px == (tx**2 + 3*yx**2)/4
    px7 = px**7
    tx7 = tx**7 - 7*px*tx**5 + 14*px**2*tx**3 - 7*px**3*tx
    yx7 = yx * (tx**6 - 5*px*tx**4 + 6*px**2*tx**2 - px**3)
    assert tx7**2 - 4*px7 == -D*yx7**2
    # now the 3-rd twist
    E2_order = px7+1+( 3*yx7+tx7)/2
    assert (E2_order % rx) == 0
    c2x = E2_order // rx # 3 factors of degrees 2, 14, 84

    #final exponentiation tests
    exponent_x = (px**12 - px**11 + px**9 - px**8 + px**6 - px**4 + px**3 - px + 1)//rx
    
    l0 = x**11 - x**10 + x**8 - x**7 + x**5 - x**3 + x**2 - 1
    l1 = x**10 - x**9 + x**7 - x**6 + x**4 - x**2 + x
    l2 = x**9 - x**8 + x**6 - x**5 + x**3 - x + 1
    l3 = x**8 - x**7 + x**5 - x**4 + x**2 - 1
    l4 = x**7 - x**6 + x**4 - x**3 + x
    l5 = x**6 - x**5 + x**3 - x**2 + 1
    l6 = x**5 - x**4 + x**2 - x
    l7 = x**4 - x**3 + x - 1
    l8 = x**3 - x**2 + 1
    l9 = x**2 - x
    l10 = x - 1
    l11 = 1
    e = (x - 1)*(x**3 - 1)
    
    assert e*(l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*(l7 + px*(l8 + px*(l9 + px*(l10 + px*l11))))))))))) + 3 == 3*exponent_x

    print("BLS21 u={:#x}".format(u0))
    cost_pairing_bls21(u0)
    # TODO:
    # build the finite field extension
    # define the curve and its twists
    # test the Miller loop, final exponentiation easy, final exponentiation hard
    print("")
    
    p = ZZ(px(u0))
    r = ZZ(rx(u0))
    c = ZZ(cx(u0))
    t = ZZ(tx(u0))
    y = ZZ(yx(u0))
    c2 = ZZ(c2x(u0))
#    lambda_mod_r = ZZ(lambx(u0))
    Fp = GF(p, proof=False)
    if b is None:
        b, E = find_curve_parameter_b(Fp, r, c) #E/Fp: y^2 = x^3 + 15
    else:
        E = EllipticCurve(Fp, [0, b])

    print("BLS21-{} E: y^2 = x^3 {:+d} /Fp of {} bits".format(p.nbits(), b, p.nbits()))
    print("u = {:#x} {} bits".format(u0, u0.nbits()))
    print("p = {:#x} {} bits {} mod 3, {} mod {}, {} mod k={}".format(p, p.nbits(), p % 3, p % (k //3), (k // 3), p % k, k))
    print("r = {:#x} {} bits".format(r, r.nbits()))
    print("c = {:#x} {} bits".format(c, c.nbits()))
    print("t = {:#x} {} bits".format(t, t.nbits()))
    print("c2 = {:#x} {} bits".format(c2, c2.nbits()))

    Fpz = Fp['z']; (z,) = Fpz._first_ngens(1)
    assert (p % 3) == 1
    e = k//3
    assert (p % e) == 1
    a = -1
    while not (z**e - a).is_irreducible():
        a = a+1

    print("Fp{} = Fp[x]/(x^{} - {})".format(e, e, a))
    Fp7 = Fp.extension(z**e - a, names=('i',)); (i,) = Fp7._first_ngens(1)

    Fq = Fp7
    Fp7s = Fp7['s']; (s,) = Fp7s._first_ngens(1)

    print("find_twist_curve_parameter_xi_ab")
    xiM, btwM = find_twist_curve_parameter_xi_ab(b, Fp7, r, c2, d=3, D_twist=False)# Etw: y^2 = x^3 + b/xi^2 for cubic twist

    EM = EllipticCurve([Fp7(0), Fp7(btwM)])
    Fq3M = Fp7.extension(s**3 - xiM, names=('wM',)); (wM,) = Fq3M._first_ngens(1)
    Eq3M = EllipticCurve([Fq3M(0), Fq3M(b)])

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

    Fp21M = Fp.extension((z**3 - i0M)**7 - i1M**7*a, names=('SM',)); (SM,) = Fp21M._first_ngens(1)
    E21M = EllipticCurve([Fp21M(0), Fp21M(b)])

    def map_Fq3M_Fp21M(x):
        return sum([xi.polynomial()((SM**3-i0M)/i1M) * SM**e for e,xi in enumerate(x.list())])
    def map_Fq3M_Fp21M(x, aM = None):
        if aM is None:
            aM = SM
        return sum([xi.polynomial()((aM**3-i0M)/i1M) * aM**e for e,xi in enumerate(x.list())])
    def map_Fq_Fp21M(x):
        return x.polynomial()((SM**3-i0M)/i1M)

    print("test map_Fq3M_Fp21M")
    x0 = Fq3M.random_element()
    x1 = map_Fq3M_Fp21M(x0)

    print("test map_Fq_Fp21M")
    x0 = Fq.random_element()
    x1 = map_Fq_Fp21M(x0)

    P = EM.random_element()

    print("EM order c2*r: {}".format(r*c2*P==0))

    print("test E (G1)")
    test_order(E,r*c)
    print("test E' (G2) M-twist")
    test_order(EM,r*c2)

    print("test Frobenius map on G2 with M-twist")
    test_g2_frobenius_eigenvalue(E21M, EM, Fq3M, map_Fq3M_Fp21M, r, c2, D_twist=False)
    test_g2_frobenius_eigenvalue_alt(E21M, EM, map_Fq_Fp21M, r, c2, D_twist=False)

    print("tests lines with M-twist and cubic twist (denominators do not vanish easily)")
    test_double_line_cln_a0_cubic_twist(E, EM, Fq3M, D_twist=False)
    test_add_line_cln_a0_cubic_twist(E, EM, Fq3M, D_twist=False)
    test_add_line_cln_a0_cubic_twist_with_z(E, EM, Fq3M, D_twist=False)

    print("test Tate(P,Q) pairing with M-twist and verticals because of cubic twist")
    test_bilinearity_miller_loop_ate_cln_a0_cubic_twist(E, Eq3M, EM, r, c, c2, r, D_twist=False, function_name=miller_function_tate_cln_a0_cubic_twist, Tate=True)
    print("test Tate(Q,P) pairing with M-twist and verticals because of cubic twist")
    test_bilinearity_miller_loop_ate_cln_a0_cubic_twist(E, Eq3M, EM, r, c, c2, r, D_twist=False, function_name=miller_function_tate_cln_a0_cubic_twist, Tate=False)
    print("test ate pairing f_{u,Q}(P) with M-twist and verticals because of cubic twist")
    test_bilinearity_miller_loop_ate_cln_a0_cubic_twist(E, Eq3M, EM, r, c, c2, u0, D_twist=False, function_name=miller_function_ate_cln_a0_cubic_twist)

    print("test ate pairing with M-twist and verticals, explicit cubic twist")
    test_bilinearity_miller_loop_ate_cln_a0_cubic_twist_explicit(E, Eq3M, EM, r, c, c2, u0, D_twist=False, function_name=miller_function_ate_cln_a0_cubic_twist)

    print("\nFinal exponentiation")
    test_final_exp_easy_k21(Fp21M)
    expected_exponent = (p**12 - p**11 + p**9 - p**8 + p**6 - p**4 + p**3 - p + 1)//r
    expected_exponent2 = 3*(p**12 - p**11 + p**9 - p**8 + p**6 - p**4 + p**3 - p + 1)//r
    test_final_exp_hard_bls21_v1(Fp21M, u0, r, exponent_hard=expected_exponent)
    test_final_exp_hard_bls21_v2(Fp21M, u0, r, exponent_hard=expected_exponent2)

def test_bls21_511a():
    u0 = ZZ(2**32 - 2**20 + 2**7 -2**4)
    assert u0 == ZZ(0xfff00070)
    b = -2
    test_curve(u0, b)

def test_bls21_511b():
    u0 = ZZ(-2**32+2**24-2**22+2**3)
    assert u0 == ZZ(-0xff3ffff8)
    b = -2
    test_curve(u0, b)

def test_bls21_511c():
    u0 = ZZ(-2**32+2**25+2**6+2)
    assert u0 == ZZ(-0xfdffffbe)
    b = 16
    test_curve(u0, b)

if __name__ == "__main__":
    arithmetic(False)
    #test_bls21_511a() # problem p != 1 mod 21
    #test_bls21_511b() # problem p != 1 mod 21
    test_bls21_511c()
