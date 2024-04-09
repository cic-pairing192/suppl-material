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
from pairing_fm18 import *
from test_pairing import *
from test_scalar_mult import test_glv_scalar_mult_g1_j0
from cost_pairing import cost_pairing_fm18
#

def test_miller_loop_opt_ate_fm18(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=False):
    """Testing Miller loop of optimal ate pairing on FM18 curve

    Testing the function miller_loop_opt_ate_fm18(Q2, P, u)
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
    ok = test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=D_twist, function_name=miller_loop_opt_ate_fm18, curve_a_is_0=True)
    print("test bilinearity miller_loop_opt_ate_fm18: {}".format(ok))
    return ok

def test_final_exp_hard_fm18(Fpk, r, u, u0, function_name=final_exp_hard_fm18_v0, expected_exponent=None):
    # test final_exp_hard_fm18(m, u)
    # expected exponent is (p^6 - p^3 + 1)/r * (-3/49*x^2)
    p = Fpk.characteristic()
    if expected_exponent is None:
        expected_exponent = ((p**6 - p**3 + 1)//r)
    else:
        assert expected_exponent % ((p**6 - p**3 + 1)//r) == 0
    ok_exp = True
    ok_r = True
    ok_inv = True
    i = 0
    while (ok_r and ok_inv and ok_exp) and i < 1:
        f0 = Fpk.random_element()
        #f1 = f0.frobenius(9)
        #f = f1/f0 # f^(p^9-1)
        f = final_exp_easy_k18(f0)
        if function_name == final_exp_hard_fm18_v0:
            g = function_name(f, u, u0)
        else:
            g = function_name(f, u)
        ok_r = g**r == Fpk(1)
        ok_exp = g == f**expected_exponent
        ok_inv = g.frobenius(9) == 1/g
        i = i+1
    print("test {}: f^r == 1: {}, f == m^expected_exp: {}, f^9 == 1/f: {}".format(function_name.__name__, ok_r, ok_exp, ok_inv))
    return ok_r and ok_exp and ok_inv

def test_curve(u0):
    assert (u0 % 3) == 1
    u0 = ZZ(u0)
    u2 = (u0 - 1) // 3
    u2 = ZZ(u2)
    
    cost_pairing_fm18(u0)
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 18
    D = 3
    # FK18 polynomials
    px = (3*x**12 - 3*x**9 + x**8 - 2*x**7 + 7*x**6 - x**5 - x**4 - 4*x**3 + x**2 - 2*x + 4)/3
    rx = x**6 - x**3 + 1
    tx = x**6 - x**4 - x**3 + 2 # t(x) = -x^4 + 1 + r(x)
    cx = (3*x**6 + x**2 - 2*x + 1)/3    # cofactor of curve order #E(Fp) = c(x)*r(x) = p(x) + 1 - t(x)
    yx = (3*x**6 + x**4 - x**3 - 2*x + 2)/3         # y such that t(x)^2 - 4*p(x) = -D*y(x)^2
    c2x = (27*x**30 - 54*x**27 + 27*x**26 - 54*x**25 + 189*x**24 - 54*x**23 + 36*x**22 - 306*x**21 + 189*x**20 - 243*x**19 + 514*x**18 - 168*x**17 + 150*x**16 - 616*x**15 + 423*x**14 - 396*x**13 + 656*x**12 - 165*x**11 + 273*x**10 - 541*x**9 + 336*x**8 - 408*x**7 + 278*x**6 - 135*x**5 + 180*x**4 - 130*x**3 + 150*x**2 - 96*x + 19)/27
    px3 = px**3
    tx3 = tx**3 - 3*px*tx
    yx3 = yx * (px - tx**2)
    txe =  (tx**3 - 9*tx**2*yx - 9*tx*yx**2 + 9*yx**3)/8
    assert txe == (3*yx3+tx3)/2
    betax = (93*x**11 - 48*x**10 - 240*x**9 - 267*x**8 + 235*x**7 - 84*x**6 + 139*x**5 - 191*x**4 - 131*x**3 - 266*x**2 + 411*x - 230)/342
    lambrx = x**3-1 #lambr(x) = (-1+sqrt(-3))/2 mod r(x) and such that (beta*x, y) has eigenvalue lambda mod r
    lambcx = -(3*x**5 + 3*x**4 + 3*x**3 + x)/2
    assert ((lambrx**2 + lambrx + 1) % rx) == 0
    assert ((lambrx**2 + lambrx + 1) % rx) == 0
    
    # optimal ate pairing has Miller loop f_{u,Q}(P) with no additional terms
    
    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**12 + x**9 - x**3 - 1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**6 - px**3 + 1)//rx
    exponent = ZZ(exponent_x(u0))
    
    # breaking up exponent_x
    # final exponentiation: hard part based on Fotiadis-Martindale: https://eprint.iacr.org/2019/555.pdf
    l5 = (3*x**6 + x**2 - 2*x + 4)/3
    l4 = (-3*x**10 - x**6 + 2*x**5 - 4*x**4 + 3*x**2)/3
    l3 = (3*x**11 - 3*x**8 + x**7 - 2*x**6 + 4*x**5 - x**4 - x**3 - 4*x**2)/3
    l2 = (3*x**9 - 3*x**6 + x**5 - 2*x**4 + 4*x**3 - x**2 - x - 4)/3
    l1 = (3*x**7 + x**3 - 2*x**2 + 4*x)/3
    l0 = (-3*x**11 - x**7 + 2*x**6 - 4*x**5 + 3*x**3 + 3)/3

    assert l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*l5)))) == exponent_x
    exponent_easy = (px**9 - 1)*(px**3 + 1)
    exponent_hard = (px**6 - px**3 + 1)//rx

    # for G2, compute #E(Fp6) then compute its 6-th twist
    #print("tx^2-4*px/yx^2 = {}".format((tx**2 - 4*px)/yx**2))
    assert tx**2 - 4*px == -D*yx**2

    p = ZZ(px(u0))
    r = ZZ(rx(u0))
    c = ZZ(cx(u0))
    t = ZZ(tx(u0))
    y = ZZ(yx(u0))
    c2 = ZZ(c2x(u0))
    t3 = ZZ(txe(u0))
    lambda_mod_r = ZZ(lambrx(u0))

    Fp = GF(p, proof=False)
    beta_mod_p = Fp(betax(u0))
    b, E = find_curve_parameter_b(Fp, r, c) #E/Fp: y^2 = x^3 + 31
        
    print("FM18-{} E: y^2 = x^3 {:+d} /Fp of {} bits".format(p.nbits(), b, p.nbits()))
    print("u = {:#x} {} bits".format(u0, u0.nbits()))
    print("p = {:#x} {} bits".format(p, p.nbits()))
    print("r = {:#x} {} bits".format(r, r.nbits()))
    print("c = {:#x} {} bits".format(c, c.nbits()))
    print("t = {:#x} {} bits".format(t, t.nbits()))
    
    Fpz = Fp['z']; (z,) = Fpz._first_ngens(1)
    assert (p % 3) == 1
    a = -1
    while not (z**3 - a).is_irreducible():
        a = a+1

    print("Fp3 = Fp[x]/(x^3 - {})".format(a))
    Fp3 = Fp.extension(z**3 - a, names=('i',)); (i,) = Fp3._first_ngens(1)

    Fq = Fp3
    Fp3s = Fp3['s']; (s,) = Fp3s._first_ngens(1)
        
    xiM, btwM = find_twist_curve_parameter_xi_ab(b, Fp3, r, c2, d=6, D_twist=False)
    EM = EllipticCurve([Fp3(0), Fp3(btwM)])

    Fp18M = Fp3.extension(s**6 - xiM, names=('wM',)); (wM,) = Fp18M._first_ngens(1)
    Fq6M = Fp18M
    f = Fp18M.random_element()

    E18M = EllipticCurve([Fp18M(0), Fp18M(b)])
    E_Fq3M = E18M

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

    Fp18M_A = Fp.extension((z**6 - i0M)**3 - i1M**3*a, names=('SM',)); (SM,) = Fp18M_A._first_ngens(1)

    E18M_A = EllipticCurve([Fp18M_A(0), Fp18M_A(b)])

    def map_Fp18M_Fp18M_A(x):
        return sum([xi.polynomial()((SM**6-i0M)/i1M) * SM**e for e,xi in enumerate(x.list())])

    def map_Fq6M_Fp18M_A(x, aM=None):
        if aM is None:
            aM = SM
        return sum([xi.polynomial()((aM**6-i0M)/i1M) * aM**e for e,xi in enumerate(x.list())])

    def map_Fp3_Fp18M_A(x):
        # evaluate elements of Fq=Fp[i] at i=s^6-7 = S^6-7
        return x.polynomial()((SM**6-i0M)/i1M)

    print("test map_Fp18M_Fp18M_A")
    x0 = Fp18M.random_element()
    x1 = map_Fp18M_Fp18M_A(x0)

    print("test map_Fq6M_Fp18M")
    x0 = Fq6M.random_element()
    x1 = map_Fq6M_Fp18M_A(x0)

    print("test map_Fp3_Fp18M")
    x0 = Fp3.random_element()
    x1 = map_Fp3_Fp18M_A(x0)
    
    xiD, btwD = find_twist_curve_parameter_xi_ab(b, Fp3, r, c2, d=6, D_twist=True)
    ED = EllipticCurve([Fp3(0), Fp3(btwD)])

    Fp18D = Fp3.extension(s**6 - xiD, names=('wD',)); (wD,) = Fp18D._first_ngens(1)
    Fq6D = Fp18D
    E18D = EllipticCurve([Fp18D(0), Fp18D(b)])
    E_Fq3D = E18D

    try:
        coeffs_xiD = xiD.polynomial().list()
    except AttributeError as err:
        coeffs_xiD = xiD.list()
    i0D = coeffs_xiD[0]
    i1D = coeffs_xiD[1]
    i0d = ZZ(i0D)
    if abs(i0d - p) < abs(i0d):
        i0d = i0d - p
    i1d = ZZ(i1D)
    if abs(i1d - p) < abs(i1d):
        i1d = i1d - p
    if i0d == 0:
        str_xiD = ""
    else:
        str_xiD = "{}".format(i0d)
    if i1d == 1:
        if len(str_xiD) == 0:
            str_xiD = "i"
        else:
            str_xiD += "+i"
    elif i1d == -1:
        str_xiD += "-i"
    elif i1d != 0:
        if len(str_xiD) == 0:
            str_xiD = "{}*i".format(i1d)
        else:
            str_xiD += "{:+}*i".format(i1d)
    print("D-twist xiD = {}".format(str_xiD))
    # xiD = i0D + i*i1D
    # s^6 - xiD = 0 <=> s^6 - i0D = i1D*i <=> (s^6 - i0D)^3 = i1D^3*a
    # resultant(s^6-xiD, z^3 - a)
    Fp18D_A = Fp.extension((z**6 - i0D)**3 - i1D**3*a, names=('SD',)); (SD,) = Fp18D_A._first_ngens(1)
    E18D_A = EllipticCurve([Fp18D_A(0), Fp18D_A(b)])

    P = ED.random_element()
    print("ED order c2*r:{}".format(r*c2*P==0)) # ok

    def map_Fp18D_Fp18D_A(x):
        return sum([xi.polynomial()((SD**6-i0D)/i1D) * SD**e for e,xi in enumerate(x.list())])

    def map_Fq6D_Fp18D_A(x, aD=None):
        if aD is None:
            aD = SD
        return sum([xi.polynomial()((aD**6-i0D)/i1D) * aD**e for e,xi in enumerate(x.list())])

    def map_Fp3_Fp18D_A(x):
        # evaluate elements of Fq=Fp[i] at i=wD^6 = SD^6
        return x.polynomial()((SD**6-i0D)/i1D)

    print("test map_Fp18D_Fp18D_A")
    x0 = Fp18D.random_element()
    x1 = map_Fp18D_Fp18D_A(x0)

    print("test map_Fq6D_Fp18D_A")
    x0 = Fq6D.random_element()
    x1 = map_Fq6D_Fp18D_A(x0)

    print("test map_Fp3_Fp18D_A")
    x0 = Fp3.random_element()
    x1 = map_Fp3_Fp18D_A(x0)

    print("test E (G1)")
    test_order(E,r*c)
    print("test E' (G2) M-twist")
    test_order(EM,r*c2)
    print("test E' (G2) D-twist")
    test_order(ED,r*c2)

    print("test GLV on G1")
    test_glv_scalar_mult_g1_j0(E, lambda_mod_r, beta_mod_p, r, c)

    print("test Frobenius map on G2 with M-twist")
    test_g2_frobenius_eigenvalue(E18M_A,EM,Fp18M,map_Fq6M_Fp18M_A,r,c2,D_twist=False)
    test_g2_frobenius_eigenvalue_alt(E18M_A,EM,map_Fp3_Fp18M_A,r,c2,D_twist=False)
    print("test Frobenius map on G2 with D-twist")
    test_g2_frobenius_eigenvalue(E18D_A,ED,Fp18D,map_Fq6D_Fp18D_A,r,c2,D_twist=True)
    test_g2_frobenius_eigenvalue_alt(E18D_A,ED,map_Fp3_Fp18D_A,r,c2,D_twist=True)

    print("test cofactor clearing and subgroup membership testing")
    print("on G1")
    test_cofactor_clearing_g1(E, r, c, u0, t, None, cofactor_clearing_g1_fm18)
    test_membership_testing_g1(E, r, c, u0, t, beta_mod_p, membership_testing_g1_fm18)
    test_membership_testing_g1(E, r, c, u0, t, beta_mod_p, membership_testing_g1_fm18_alt)

    print("test cofactor clearing on G2, M-twist")
    for case in range(euler_phi(k)):
        test_cofactor_clearing_g2(EM, r, c2, u0, t3, Fq6M, cofactor_clearing_g2_fm18, False, case)
    print("test cofactor clearing on G2, D-twist")
    for case in range(euler_phi(k)):
        test_cofactor_clearing_g2(ED, r, c2, u0, t3, Fq6D, cofactor_clearing_g2_fm18, True, case)

    print("test membership_testing_g2 with M-twist")
    test_membership_testing_g2(EM, r, c2, u0, t3, Fq6M, membership_testing_g2_fm18, D_twist=False)
    test_membership_testing_g2(EM, r, c2, u0, t3, Fq6M, membership_testing_g2_fm18_alt, D_twist=False)
    print("test membership_testing_g2 with D-twist")
    test_membership_testing_g2(ED, r, c2, u0, t3, Fq6D, membership_testing_g2_fm18, D_twist=True)
    test_membership_testing_g2(ED, r, c2, u0, t3, Fq6D, membership_testing_g2_fm18_alt, D_twist=True)

    print("tests with M-twist")
    test_add_line_h_a0_twist6_aklgl_with_z(E, ED, wD, D_twist=False)
    test_double_line_j(E, EM, Fq6M, D_twist=False)
    test_double_line_affine_j(E, EM, Fq6M, D_twist=False)
    test_add_line_j(E, EM, Fq6M, D_twist=False)
    test_add_line_affine_j(E, EM, Fq6M, D_twist=False)

    print("tests with D-twist")
    test_add_line_h_a0_twist6_aklgl_with_z(E, ED, wD, D_twist=True)
    test_double_line_j(E, ED, Fq6D, D_twist=True)
    test_double_line_affine_j(E, ED, Fq6D, D_twist=True)
    test_add_line_j(E, ED, Fq6D, D_twist=True)
    test_add_line_affine_j(E, ED, Fq6D, D_twist=True)

    print("optimal ate pairing tests with M-twist")
    test_miller_function_ate_aklgl(E, EM, Fp18M, xiM, r, c, c2, (t-1) % r, D_twist=False, verbose=False)
    test_miller_function_ate_2naf_aklgl(E, EM, Fp18M, xiM, r, c, c2, (t-1) % r, D_twist=False, verbose=False)

    test_miller_loop_opt_ate_fm18(E, EM, Fp18M, Fp18M_A, map_Fp18M_Fp18M_A, r, c, c2, u0, D_twist=False)
    test_miller_loop_opt_ate_aklgl(miller_loop_opt_ate_aklgl_fm18, E, EM, Fp18M, xiM, map_Fp18M_Fp18M_A, r, c, c2, u0, D_twist=False)

    print("optimal ate pairing tests with D-twist")
    test_miller_function_ate_aklgl(E, ED, Fp18D, xiD, r, c, c2, (t-1) % r, D_twist=True, verbose=True)
    test_miller_function_ate_2naf_aklgl(E, ED, Fp18D, xiD, r, c, c2, (t-1) % r, D_twist=True, verbose=True)
    test_miller_loop_opt_ate_fm18(E, ED, Fp18D, Fp18D_A, map_Fp18D_Fp18D_A, r, c, c2, u0, D_twist=True)
    test_miller_loop_opt_ate_aklgl(miller_loop_opt_ate_aklgl_fm18, E, ED, Fp18D, xiD, map_Fp18D_Fp18D_A, r, c, c2, u0, D_twist=True)

    print("\nFinal exponentiation")
    ee = ((px**9-1)*(px**3+1)*(px**6-px**3+1)//rx)(u0)
    test_final_exp_easy_k18(Fp18M_A)
    test_final_exp_easy_k18(Fp18D_A)
    expected_exponent = (p**6 - p**3 + 1)//r
    test_final_exp_hard_fm18(Fp18M_A, r, u0, u2, function_name=final_exp_hard_fm18_v0, expected_exponent=-expected_exponent)
    test_final_exp_hard_fm18(Fp18D_A, r, u0, u2, function_name=final_exp_hard_fm18_v0, expected_exponent=-expected_exponent)
    test_final_exp_hard_fm18(Fp18M_A, r, u0, u2, function_name=final_exp_hard_fm18_v1, expected_exponent=expected_exponent)
    test_final_exp_hard_fm18(Fp18D_A, r, u0, u2, function_name=final_exp_hard_fm18_v1, expected_exponent=expected_exponent)
    test_final_exp_hard_fm18(Fp18M_A, r, u0, u2, function_name=final_exp_hard_fm18_v2, expected_exponent=3*expected_exponent)
    test_final_exp_hard_fm18(Fp18D_A, r, u0, u2, function_name=final_exp_hard_fm18_v2, expected_exponent=3*expected_exponent)

def test_curve_fm18_769():
    # FM18-769 seed from https://eprint.iacr.org/2019/555 Fotiadis-Martindale
    u0 = ZZ(-(2**64 + 2**35 - 2**11 + 1))
    test_curve(u0)

def test_curve_fm18_768():
    # FM18-768 new seed
    u0 = ZZ(-2**64+2**33+2**30+2**20+1)
    test_curve(u0)

def test_curve_fm18_768b():
    # FM18-768 positive seed
    u0 = ZZ(2**64-2**18-2**14+2**10+1)
    assert u0 == ZZ(0xfffffffffffbc401)
    b = 7
    test_curve(u0)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_fm18_768()
    test_curve_fm18_768b()
    #test_curve_fm18_769()
