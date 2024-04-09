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
from pairing_sg18 import *
from test_pairing import *
from test_scalar_mult import test_glv_scalar_mult_g1_j0
from cost_pairing import cost_pairing_sg18
#

def test_miller_loop_opt_ate_sg18(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=False):
    """Testing Miller loop of optimal ate pairing on SG18 curve

    Testing the function miller_loop_opt_ate_sg18(Q2, P, u)
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
    ok = test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=D_twist, function_name=miller_loop_opt_ate_sg18, curve_a_is_0=True)
    print("test bilinearity of SG18 optimal ate pairing: {}".format(ok))
    return ok

def test_optimal_ate_formula_sg18(E_Fpk, E_Fqd, E2, map_Fqd_Fpk, w, u, r, c2, D_twist=True):
    """
    Two short vectors: v1 = (1, 3*u, 0, 1, 0, 0) and v2 = (-3*u, 0, -2, 0, 0, 1)
    Test Q + (3*u)*pi(Q) + pi_4(Q) = 00 for Q in the trace-0 subgroup of E
    Test (-3*u)*Q - 2*pi^2(Q) + pi^5(Q) = 00

    INPUT:
    - `E_Fpk`: EllipticCurve instance defined over an absolute extension of Fp
    - `E2`: EllipticCurve instance defined over an absolute extension of Fp of degree p^{k/d}
    - `map_Fqd_Fpk`: map from the relative extension Fqd to the isomorphic absolute extension Fpk
    - `w`: the generator of Fpd (for the twisting map)
    - `u`: integer, parameter seed
    - `r`: prime integer, E(Fp) has order r*c
    - `c2`: integer, twist cofactor, E2 has order r*c2
    - `D_twist`: whether the twist is a D-twist or M-twist
    """
    ok = True
    i = 0
    p = E_Fpk.base_field().characteristic()
    p2 = p**2
    p3 = p2*p
    p4 = p2**2
    p5 = p4*p
    while ok and i < 10:
        Q = c2*E2.random_element()
        while Q == E2(0) or r*Q != E2(0):
            Q = c2*E2.random_element()
        if D_twist:
            Q2 = psi_sextic_d_twist(Q, w)
        else:
            Q2 = psi_sextic_m_twist(Q, w)
        Qd = E_Fqd((Q2[0], Q2[1]))
        piQd = E_Fqd(((Qd[0])**p, (Qd[1])**p))
        pi2Qd = E_Fqd(((Qd[0])**p2, (Qd[1])**p2))
        pi3Qd = E_Fqd(((Qd[0])**p3, (Qd[1])**p3))
        pi4Qd = E_Fqd(((Qd[0])**p4, (Qd[1])**p4))
        
        ok1 = (u*Qd + pi2Qd + u*pi3Qd) == E_Fqd(0)
        ok2 = (u*Qd + pi2Qd + u*pi3Qd) == E_Fqd(0)

        Qk = E_Fpk((map_Fqd_Fpk(Q2[0]), map_Fqd_Fpk(Q2[1])))
        piQk = E_Fpk(((Qk[0]).frobenius(), (Qk[1]).frobenius()))
        pi2Qk = E_Fpk(((Qk[0]).frobenius(2), (Qk[1]).frobenius(2)))
        pi3Qk = E_Fpk(((Qk[0]).frobenius(3), (Qk[1]).frobenius(3)))
        pi5Qk = E_Fpk(((Qk[0]).frobenius(5), (Qk[1]).frobenius(5)))
        ok3 = (u*Qk + pi2Qk + u*pi3Qk) == E_Fpk(0)
        ok4 = (u*Qk + pi2Qk + u*pi3Qk) == E_Fpk(0)
        ok = ok1 and ok2 and ok3 and ok4
        i = i+1
    if D_twist:
        print("test optimal ate formula D_twist u*Q + pi_2(Q) + u*pi_3(Q) = 0: {}".format(ok1 and ok2))
        print("test optimal ate formula D_twist u*Q + pi_2(Q) + u*pi_3(Q) = 0: {}".format(ok3 and ok4))
    else:
        print("test optimal ate formula M_twist u*Q + pi_2(Q) + u*pi_3(Q) = 0: {}".format(ok1 and ok2))
        print("test optimal ate formula M_twist u*Q + pi_2(Q) + u*pi_3(Q) = 0: {}".format(ok3 and ok4))
    return ok
    
def test_final_exp_hard_sg18(Fpk, r, u, function_name=final_exp_hard_sg18_v0, expected_exponent=None):
    # test final_exp_hard_sg18(m, u)
    # expected exponent is (p^6 - p^3 + 1)/r * (-3*u**3)
    p = Fpk.characteristic()
    if expected_exponent is None:
        expected_exponent = ((p**6 - p**3 + 1)//r)*(-3*u**3)
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
        g = function_name(f, u)
        ok_r = g**r == Fpk(1)
        ok_exp = g == f**expected_exponent
        ok_inv = g.frobenius(9) == 1/g
        i = i+1
    print("test {}: f^r == 1: {}, f == m^expected_exp: {}, f^9 == 1/f: {}".format(function_name.__name__, ok_r, ok_exp, ok_inv))
    return ok_r and ok_exp and ok_inv

def test_curve(u0, b=None):
    u0 = ZZ(u0)
    cost_pairing_sg18(u0)
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 18
    D = 3
    # SG18 polynomials
    rx = 27*x**6 + 9*x**3 + 1
    tx = 3*x**2 + 1
    cx = 9*x**4 - 6*x**2 + 1    # cofactor of curve order #E(Fp) = c(x)*r(x) = p(x) + 1 - t(x)
    px = cx*rx + tx - 1
    yx = 18*x**5 - 6*x**3 +3*x**2-1
    c2x = 531441*x**24 - 1062882*x**22 + 354294*x**21 + 885735*x**20 - 708588*x**19 -    295245*x**18 + 590490*x**17 - 78732*x**16 - 249318*x**15 + 124659*x**14 + 45927*x**13 - 58320*x**12 + 4374*x**11 + 14580*x**10 - 4617*x**9 - 1701*x**8 + 1215*x**7 - 162*x**5 + 3
    betax = (486*x**9 + 243*x**8 - 486*x**7 - 81*x**6 + 297*x**5 - 54*x**4 - 72*x**3 + 45*x**2 + 6*x - 11)/7
    lambrx = 9*x**3 + 1
    assert ((lambrx**2 + lambrx + 1) % rx) == 0
    tx3 = tx**3 - 3*px*tx
    px3 = px**3
    yx3 = yx * (px - tx**2)
    assert (tx3**2 - 4*px3) == -D*yx3**2
    # now the 6-th twist that matches rx
    E2_order = px3+1-(-3*yx3+tx3)/2
    assert E2_order == c2x * rx
    txe = (-3*yx3+tx3)/2
    
    # optimal ate pairing formula has additional terms
    # f_{u,Q}(P) * f_{u,Q}(P)^(p^3) * l_{[u*p^3]Q, [p^2]Q}(P)
    
    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**12 + x**9 - x**3 - 1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**6 - px**3 + 1)//rx
    exponent = ZZ(exponent_x(u0))
    
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
    if b is None:
        b, E = find_curve_parameter_b(Fp, r, c) #E/Fp: y^2 = x^3 + 15
    else:
        E = EllipticCurve(Fp, [0, b])

    print("SG18-{} E: y^2 = x^3 {:+d} /Fp of {} bits".format(p.nbits(), b, p.nbits()))
    print("u = {:#x} {} bits".format(u0, u0.nbits()))
    print("p = {:#x} {} bits".format(p, p.nbits()))
    print("r = {:#x} {} bits".format(r, r.nbits()))
    print("c = {:#x} {} bits".format(c, c.nbits()))
    print("t = {:#x} {} bits".format(t, t.nbits()))
    print("c2 = {:#x} {} bits".format(c2, c2.nbits()))

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
    
    f = Fp18M.random_element()

    Fq6M = Fp18M
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
    def map_Fq6M_Fp18M_A(x, aM = None):
        if aM is None:
            aM = SM
        return sum([xi.polynomial()((aM**6-i0M)/i1M) * aM**e for e,xi in enumerate(x.list())])
    def map_Fp3_Fp18M_A(x):
        return x.polynomial()((SM**6-i0M)/i1M)

    print("test map_Fp18M_Fp18M_A")
    x0 = Fp18M.random_element()
    x1 = map_Fp18M_Fp18M_A(x0)

    print("test map_Fq6D_Fp18M_A")
    x0 = Fq6M.random_element()
    x1 = map_Fq6M_Fp18M_A(x0)

    print("test map_Fp3_Fp18M")
    x0 = Fp3.random_element()
    x1 = map_Fp3_Fp18M_A(x0)
        
    P = EM.random_element()
    
    print("EM order c2*r: {}".format(r*c2*P==0))

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
    test_cofactor_clearing_g1(E, r, c, u0, t, None, cofactor_clearing_g1_sg18a)
    test_membership_testing_g1(E, r, c, u0, t, beta_mod_p, membership_testing_g1_sg18a)

    print("on G2, M-twist")
    print("test cofactor clearing on G2")
    for case in range(euler_phi(k)):
        test_cofactor_clearing_g2(EM, r, c2, u0, t3, Fq6M, cofactor_clearing_g2_sg18a, False, case)
    for case in range(euler_phi(k)):
        test_cofactor_clearing_g2(ED, r, c2, u0, t3, Fq6D, cofactor_clearing_g2_sg18a, True, case)

    print("on G2, D-twist")
    print("test membership_testing_g2 with M-twist, with D-twist")
    test_membership_testing_g2(EM, r, c2, u0, t3, Fq6M, membership_testing_g2_sg18a, D_twist=False)
    test_membership_testing_g2(ED, r, c2, u0, t3, Fq6D, membership_testing_g2_sg18a, D_twist=True)

    print("test optimal ate pairing formula")
    print("tests with M-twist")
    test_optimal_ate_formula_sg18(E18M_A, E_Fq3M, EM, map_Fp18M_Fp18M_A, wM, u0, r, c2, D_twist=False)
    print("tests with D-twist")
    test_optimal_ate_formula_sg18(E18D_A, E_Fq3D, ED, map_Fp18D_Fp18D_A, wD, u0, r, c2, D_twist=True)

    print("tests with M-twist")
    test_add_line_h_a0_twist6_aklgl_with_z(E, EM, wM, D_twist=False)
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

    print("tests with M-twist")
    test_miller_loop_opt_ate_sg18(E, EM, Fp18M, Fp18M_A, map_Fp18M_Fp18M_A, r, c, c2, u0, D_twist=False)
    print("tests with D-twist")
    test_miller_loop_opt_ate_sg18(E, ED, Fp18D, Fp18D_A, map_Fp18D_Fp18D_A, r, c, c2, u0, D_twist=True)

    print("test ate pairing with M-twist")
    test_miller_function_ate_aklgl(E,EM,Fp18M,xiM,r,c,c2,t-1,D_twist=False,verbose=False)
    test_miller_function_ate_2naf_aklgl(E,EM,Fp18M,xiM,r,c,c2,t-1,D_twist=False,verbose=False)
    test_miller_loop_opt_ate_sg18(E, EM, Fp18M, Fp18M_A, map_Fp18M_Fp18M_A, r, c, c2, u0, D_twist=False)

    print("test ate pairing with D-twist")
    test_miller_function_ate_aklgl(E,ED,Fp18D,xiD,r,c,c2,t-1,D_twist=True,verbose=False)
    test_miller_function_ate_2naf_aklgl(E,ED,Fp18D,xiD,r,c,c2,t-1,D_twist=True,verbose=False)
    test_miller_loop_opt_ate_sg18(E, ED, Fp18D, Fp18D_A, map_Fp18D_Fp18D_A, r, c, c2, u0, D_twist=True)

    print("\nFinal exponentiation")
    ee = ((px**9-1)*(px**3+1)*(px**6-px**3+1)//rx)(u0)

    test_final_exp_easy_k18(Fp18D_A)
    test_final_exp_easy_k18(Fp18M_A)
    expected_exponent = (-3*u0**3)*(p**6 - p**3 + 1)//r
    test_final_exp_hard_sg18(Fp18D_A, r, u0, function_name=final_exp_hard_sg18_v0, expected_exponent=expected_exponent)
    test_final_exp_hard_sg18(Fp18M_A, r, u0, function_name=final_exp_hard_sg18_v0, expected_exponent=expected_exponent)

    expected_exponent = (p**6 - p**3 + 1)//r
    test_final_exp_hard_sg18(Fp18D_A, r, u0, function_name=final_exp_hard_sg18_v1, expected_exponent=expected_exponent)
    test_final_exp_hard_sg18(Fp18M_A, r, u0, function_name=final_exp_hard_sg18_v1, expected_exponent=expected_exponent)

def test_curve_sg18_427():
    u0 = ZZ(0x3801ffffff0)
    assert u0 == ZZ(2**42-2**39+2**29-2**4)
    b = 11
    test_curve(u0, b)

def test_curve_sg18_426():
    u0 = ZZ(-0x377c0000000)
    assert u0 == ZZ(-2**42+2**39+2**35+2**30)
    b=31
    test_curve(u0, b)

def test_curve_sg18_638():
    # SG18-638 seed from https://eprint.iacr.org/2018/193.pdf
    u0 = ZZ(-(2**63 + 2**54 + 2**16))
    assert u0 == -0x8040000000010000
    b = 15
    test_curve(u0, b)

def test_curve_sg18_638b():
    # with a positive u this time for testing
    u0 = ZZ(2**63 + 2**46 - 2**9)
    assert u0 == ZZ(0x80003ffffffffe00)
    b = 19
    test_curve(u0, 19)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_sg18_426()
    test_curve_sg18_427()
    test_curve_sg18_638()
    test_curve_sg18_638b()
