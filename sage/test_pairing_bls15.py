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
from cost_pairing import cost_pairing_bls15


def test_curve(u0, b):
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 15
    D = 3
    rx = x**8 - x**7 + x**5 - x**4 + x**3 - x + 1
    tx = x + 1
    yx = (x - 1)/3 * (2*x**5 + 1)
    cx = (x - 1)**2/3 * (x**2 + x + 1)
    # px = (x**12 - 2*x**11 + x**10 + x**7 - 2*x**6 + x**5 + x**2 + x + 1)/3
    px = cx*rx + tx - 1
    assert px == (tx**2 + 3*yx**2)/4
    px5 = px**5
    tx5 = tx**5 - 5*tx**3*px + 5*tx*px**2
    yx5 = yx * (tx**4 - 3*tx**2*px + px**2)
    assert tx5**2 - 4*px5 == -D*yx5**2
    # now the 3-rd twist
    E2_order = px5+1+( 3*yx5+tx5)/2
    assert (E2_order % rx) == 0
    c2x = E2_order // rx # 3 factors of degrees 2, 10, 40

    #final exponentiation tests
    exponent_x = (px**8 - px**7 + px**5 - px**4 + px**3 - px + 1)//rx
    
    l0 = x**7 - x**6 + x**4 - x**3 + x**2 - 1
    l1 = x**6 - x**5 + x**3 - x**2 + x
    l2 = x**5 - x**4 + x**2 - x + 1
    l3 = x**4 - x**3 + x - 1
    l4 = x**3 - x**2 + 1
    l5 = x**2 - x
    l6 = x - 1
    l7 = 1
    e = (x - 1)*(x**3 - 1)

    assert l7 == 1
    assert l6 == x*l7 - 1
    assert l5 == x*l6
    assert l4 == x*l5 + 1
    assert l3 == x*l4 - 1
    assert l2 == x*l3 + 1
    assert l1 == x*l2
    assert l0 == x*l1 - 1

    assert e*(l0 + px*(l1 + px*(l2 + px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*l7))))))) + 3 == 3*exponent_x

    print("BLS15 u={:#x}".format(u0))
    cost_pairing_bls15(u0)

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
        b, E = find_curve_parameter_b(Fp, r, c) #E/Fp: y^2 = x^3 + b
    else:
        E = EllipticCurve(Fp, [0, b])

    print("BLS15-{} E: y^2 = x^3 {:+d} /Fp of {} bits".format(p.nbits(), b, p.nbits()))
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
    Fp5 = Fp.extension(z**e - a, names=('i',)); (i,) = Fp5._first_ngens(1)

    Fq = Fp5
    Fp5s = Fp5['s']; (s,) = Fp5s._first_ngens(1)

    print("find_twist_curve_parameter_xi_ab")
    xiM, btwM = find_twist_curve_parameter_xi_ab(b, Fp5, r, c2, d=3, D_twist=False)# Etw: y^2 = x^3 + b/xi^2 for cubic twist

    EM = EllipticCurve([Fp5(0), Fp5(btwM)])
    Fq3M = Fp5.extension(s**3 - xiM, names=('wM',)); (wM,) = Fq3M._first_ngens(1)
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

    Fp15M = Fp.extension((z**3 - i0M)**5 - i1M**5*a, names=('SM',)); (SM,) = Fp15M._first_ngens(1)
    E15M = EllipticCurve([Fp15M(0), Fp15M(b)])

    def map_Fq3M_Fp15M(x):
        return sum([xi.polynomial()((SM**3-i0M)/i1M) * SM**e for e,xi in enumerate(x.list())])
    def map_Fq3M_Fp15M(x, aM = None):
        if aM is None:
            aM = SM
        return sum([xi.polynomial()((aM**3-i0M)/i1M) * aM**e for e,xi in enumerate(x.list())])
    def map_Fq_Fp15M(x):
        return x.polynomial()((SM**3-i0M)/i1M)

    print("test map_Fq3M_Fp15M")
    x0 = Fq3M.random_element()
    x1 = map_Fq3M_Fp15M(x0)

    print("test map_Fq_Fp15M")
    x0 = Fq.random_element()
    x1 = map_Fq_Fp15M(x0)

    P = EM.random_element()

    print("EM order c2*r: {}".format(r*c2*P==0))

    print("test E (G1)")
    test_order(E,r*c)
    print("test E' (G2) M-twist")
    test_order(EM,r*c2)

    print("test Frobenius map on G2 with M-twist")
    test_g2_frobenius_eigenvalue(E15M, EM, Fq3M, map_Fq3M_Fp15M, r, c2, D_twist=False)
    test_g2_frobenius_eigenvalue_alt(E15M, EM, map_Fq_Fp15M, r, c2, D_twist=False)

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
    test_final_exp_easy_k15(Fp15M)
    expected_exponent = 3*(p**8 - p**7 + p**5 - p**4 + p**3 - p + 1)//r
    test_final_exp_hard_bls15(Fp15M, u0, r, exponent_hard=expected_exponent, function_name=final_exp_hard_bls15_v0)
    test_final_exp_hard_bls15(Fp15M, u0, r, exponent_hard=expected_exponent, function_name=final_exp_hard_bls15)
    print("")

def test_bls15_894():
    u0 = ZZ(2**74+2**73+2**62+2**59+2**6)
    assert u0 == ZZ(0x6004800000000000040)
    b = -2
    test_curve(u0, b)

def test_bls15_373():
    u0 = -ZZ(2**31+2**27+2**26+2**25+2**24)
    assert u0 == ZZ(-0x8f000000)
    b = -2
    test_curve(u0, b)

def test_bls15_376():
    u0 = ZZ(2**31+2**29+2**28+2**19+2**6+2**3)
    assert u0 == ZZ(0xb0080048)
    b = -2
    test_curve(u0, b)

if __name__ == "__main__":
    arithmetic(False)
    #test_bls15_373() # negative seed
    #test_bls15_376() # positive seed
    test_bls15_894()
