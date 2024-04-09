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
from pairing_fm22_k15 import *
from test_pairing import *
from cost_pairing import cost_pairing_fm15

def test_final_exp_hard_fm22_k15(Fpk, u, r, function_name=final_exp_hard_fm22_k15_v0, expected_exponent=None):
    """
    testing final_exp_hard_fm15(m, u)
    INPUT:
    - `Fpk`: absolute extension of degree 16 (where a.frobenius() is defined in SageMath)
    - `r`: prime integer, order of GT
    - `u`: curve seed
    - `function_name`: a final_exp_hard_fm22_k15_*** function (for fm22 curves with k = 15)
    - `expected_exponent`: an integer multiple of (p^8 - p^7 + p^5 - p^4 + p^3 - p +1)//r

    Test if the function computes x -> x^expected_exponent and if the result has order r
    for final_exp_hard_fm22_k15, expected_exponent = 3u(u^3 - u^2 + 1)(p^8 - p^7 + p^5 - p^4 + p^3 - p +1)/r
    """
    p = Fpk.characteristic()
    if expected_exponent is None:
        expected_exponent = (p**8 - p**7 + p**5 - p**4 + p**3 - p + 1)//r
    else:
        assert expected_exponent % ((p**8 - p**7 + p**5 - p**4 + p**3 - p + 1)//r) == 0
    ok_exp = True
    ok_r = True
    ok_inv = True
    i = 0
    while (ok_r and ok_inv and ok_exp) and i < 1:
        f0 = Fpk.random_element()
        f = final_exp_easy_k15(f0)
        if function_name == final_exp_hard_fm22_k15_v0:
            g = function_name(f, u, p, r)
        else:
            g = function_name(f, u, p, r)
        ok_r = g**r == Fpk(1)
        ok_exp = g == f**expected_exponent
        ok_inv = ((g.frobenius(10)) * (g.frobenius(5))) == 1/g
        i = i + 1
    print("test {}: f^r == 1: {}, f == m^expected_exp: {}, f^8 == 1/f: {}".format(function_name.__name__, ok_r, ok_exp, ok_inv))
    return ok_r and ok_exp and ok_inv

def test_curve(u0, b):
    """
    Fotiadis Martindale k=15 family #22
    # table 2 p. 9 of eprint 2019/555 with x -> x/3
    """
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 15
    D = 3
    m=15
    u_mod_m = [0, 3] # x = 0 mod 3 so that p is an integer, u = 0,3 mod 15 so that p = 1 mod 5
    rx = x**8 - x**7 + x**5 - x**4 + x**3 - x + 1
    tx = x**4 + 1 + rx
    yx = x * (3*x**7 - x**6 - 2*x**5 + x**4 - 2*x**3 + x**2 + 2*x - 3)/3
    cx = x**2 * (3*x**6 - 2*x**4 - x**3 - 2*x**2 + 3)/3
    px = cx*rx + tx - 1
    assert px == (3*x**16 - 3*x**15 - 2*x**14 + 4*x**13 - 4*x**12 + 3*x**11 + 4*x**10 - 9*x**9 + 7*x**8 - 4*x**6 + 7*x**5 - 2*x**4 + 3*x**2 - 3*x + 3)/3
    assert px == (tx**2 + 3*yx**2)/4
    px5 = px**5
    tx5 = tx**5 - 5*tx**3*px + 5*tx*px**2
    yx5 = yx * (tx**4 - 3*tx**2*px + px**2)
    assert tx5**2 - 4*px5 == -D*yx5**2
    # now the 3-rd twist
    E2_order = px5+1+( 3*yx5+tx5)/2
    assert (E2_order % rx) == 0
    c2x = E2_order // rx # 2 factors of degrees 16, 56
    c2xa = (3*x**16 - 3*x**15 - 2*x**14 + 4*x**13 - 4*x**12 + 3*x**11 + 4*x**10 - 9*x**9 + 4*x**8 - x**6 + 7*x**5 + x**4 + 9)/3
    assert E2_order % rx == 0
    assert c2x % c2xa == 0
    c2xb = c2x // c2xa 
    #final exponentiation tests
    exponent_x = (px**8 - px**7 + px**5 - px**4 + px**3 - px + 1)//rx

    l0 =  3*x + 3*x**2 + 3*x**3 - 3*x**4 + 3*x**5 - 2*x**7 + 4*x**8 - x**9 + 2*x**11 - 5*x**12 + 3*x**14
    l1 = -3*x - 3*x**2 - 3*x**3 - 3*x**7 - 3*x**9 + 2*x**11 + x**12 + 2*x**13 - 3*x**15
    l2 = -3*x**3 - 3*x**5 + 2*x**7 + x**8 + 2*x**9 - 3*x**11
    l3 = -3 + 3*x + 3*x**2 + 3*x**3 + 5*x**4 + x**5 + 2*x**7 - 5*x**8 + 3*x**9 + 3*x**10 - 2*x**11 - x**12 - 2*x**13 + 3*x**15
    l4 = 6 - 3*x**3 - 2*x**4 + 2*x**5 - 2*x**6 + 3*x**8 - 5*x**9 - x**10 + x**12 + 5*x**13 - 3*x**15
    l5 = -3 - 3*x**4 - 3*x**6 + 2*x**8 + x**9 + 2*x**10 - 3*x**12
    l6 = -3 - 3*x**2 + 2*x**4 + x**5 + 2*x**6 - 3*x**8
    l7 = 3 + 3*x + 3*x**4 - 5*x**5 + 2*x**6 - x**8 + 4*x**9 - 2*x**10 - 3*x**11 + 3*x**12

    exponent_x_ = l0 + l1*px + l2*px**2 + l3*px**3 + l4*px**4 + l5*px**5 + l6*px**6 + l7*px**7
    
    assert (exponent_x_ == 3*x*(x**3 - x**2 + 1)*exponent_x)


    print("FM15 u={:#x}".format(u0))
    cost_pairing_fm15(u0)

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

    print("FM15-{} E: y^2 = x^3 {:+d} /Fp of {} bits".format(p.nbits(), b, p.nbits()))
    print("u = {:#x} {} bits".format(u0, u0.nbits()))
    print("p = {:#x} {} bits {} mod 3, {} mod {}, {} mod k={}".format(p, p.nbits(), p % 3, p % (k //3), (k // 3), p % k, k))
    print("r = {:#x} {} bits".format(r, r.nbits()))
    print("c = {:#x} {} bits".format(c, c.nbits()))
    print("t = {:#x} {} bits".format(t, t.nbits()))
    print("c2 = {:#x} {} bits".format(c2, c2.nbits()))
    
    exp_hard = (p**8 - p**7 + p**5 - p**4 + p**3 - p + 1)//r
    
    l0 =  3*u0 + 3*u0**2 + 3*u0**3 - 3*u0**4 + 3*u0**5 - 2*u0**7 + 4*u0**8 - u0**9 + 2*u0**11 - 5*u0**12 + 3*u0**14
    l1 = -3*u0 - 3*u0**2 - 3*u0**3 - 3*u0**7 - 3*u0**9 + 2*u0**11 + u0**12 + 2*u0**13 - 3*u0**15
    l2 = -3*u0**3 - 3*u0**5 + 2*u0**7 + u0**8 + 2*u0**9 - 3*u0**11
    l3 = -3 + 3*u0 + 3*u0**2 + 3*u0**3 + 5*u0**4 + u0**5 + 2*u0**7 - 5*u0**8 + 3*u0**9 + 3*u0**10 - 2*u0**11 - u0**12 - 2*u0**13 + 3*u0**15
    l4 = 6 - 3*u0**3 - 2*u0**4 + 2*u0**5 - 2*u0**6 + 3*u0**8 - 5*u0**9 - u0**10 + u0**12 + 5*u0**13 - 3*u0**15
    l5 = -3 - 3*u0**4 - 3*u0**6 + 2*u0**8 + u0**9 + 2*u0**10 - 3*u0**12
    l6 = -3 - 3*u0**2 + 2*u0**4 + u0**5 + 2*u0**6 - 3*u0**8
    l7 = 3 + 3*u0 + 3*u0**4 - 5*u0**5 + 2*u0**6 - u0**8 + 4*u0**9 - 2*u0**10 - 3*u0**11 + 3*u0**12
    
    exp_hard_ = l0 + l1*p + l2*p**2 + l3*p**3 + l4*p**4 + l5*p**5 + l6*p**6 + l7*p**7
    assert (exp_hard_ == 3*u0*(u0**3 - u0**2 + 1)*exp_hard)
    
    assert (l2 == l6*u0**3)
    assert (l5 == -3 + u0*l2)
    assert (l7 == l2 - (l5 + u0*l6))
    assert (l0 == l5 - (l2 + l6*u0**6) + (3*u0**2 + 3*u0 + 3))
    assert (l1 == l6*u0**7 - (3*u0**3 + 3*u0**2 + 3*u0))
    assert (l3 == l6 - (l1 + l6*u0**2))
    assert (l4 == l1 - (l6 + l6*u0**5) + (3*u0 + 3))
    
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
    expected_exponent = (p**8 - p**7 + p**5 - p**4 + p**3 - p + 1)//r
    expected_exponent = 3*u0*(u0**3 - u0**2 + 1)*expected_exponent
    test_final_exp_hard_fm22_k15(Fp15M, u0, r, function_name=final_exp_hard_fm22_k15_v0, expected_exponent=expected_exponent)
    print("")

def test_fm15_759():
    u0 = ZZ(2**47+2**45+2**43+2**23+2**21+2**9)
    assert u0 == ZZ(0xa80000a00200)
    b = 1
    test_curve(u0, b)

def test_fm15_762():
    u0 = ZZ(2**47+2**46+2**34+2**14+2**13+2**11)
    assert u0 == ZZ(0xc00400006800)
    b = 1
    test_curve(u0, b)

if __name__ == "__main__":
    arithmetic(False)
    #test_fm15_759()
    test_fm15_762()
