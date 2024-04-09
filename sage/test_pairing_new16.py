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
from pairing_new16 import *
from test_pairing import *
from test_pairing_kss16 import test_lambda_omega_g1_j1728
from cost_pairing import cost_pairing_new16

def test_final_exp_hard_new16(Fpk, r, u, function_name=final_exp_hard_new16_v2, expected_exponent=None):
    """
    testing final_exp_hard_new16{,_v1,_v2}(m, u)
    INPUT:
    - `Fpk`: absolute extension of degree 16 (where a.frobenius() is defined in SageMath)
    - `r`: prime integer, order of GT
    - `u`: curve seed
    - `function_name`: a final_exp_hard_new16_*** function (for new16 curves)
    - `expected_exponent`: an integer multiple of (p^8+1)//r

    Test if the function computes x -> x^expected_exponent and if the result has order r
    for final_exp_hard_new16_v1 and _v2, expected_exponent = (p^8+1)/r
    """
    p = Fpk.characteristic()
    if expected_exponent is None:
        expected_exponent = (p**8 + 1)//r
    else:
        assert expected_exponent % ((p**8 + 1)//r) == 0
    return test_final_exp_hard_k16(Fpk, r, u, function_name, expected_exponent)

def test_curve(u0):

    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 16
    D = 1
    # new Fotiadis polynomials
    px = (x**16 + 2*x**13 + x**10 + 5*x**8 + 6*x**5 + x**2 + 4)/4
    rx = x**8 + 1
    tx = x**8 + x**5 + 2      # t(x) = x + 1 + r(x)
    cx = (x*(x**3 + 1))**2/4  # cofactor of curve order #E(Fp) = c(x)*r(x) = p(x) + 1 - t(x)
    yx = x*(x**3 + 1)         # y such that t(x)^2 - 4*p(x) = -D*y(x)^2
    betax = (x**12 + x**9 + 3*x**4 + x)/2
    assert (betax**2 % px) == -1
    lambrx = x**4             #lamb(x)^2 = -1 mod r(x)
    assert (lambrx**2 % rx) == -1
    lambcx = 0                # not defined because the c-torsion is rational
    
    # for G2, compute #E(Fp4) then compute its 4-th twist
    assert tx**2 - 4*px == -D*yx**2
    px2 = px**2
    tx2 = tx**2 - 2*px
    yx2 = yx*tx
    assert tx2**2 - 4*px2 == -D*yx2**2
    assert px2 == (tx2**2 + D*yx2**2)/4
    px4 = px2**2
    tx4 = tx2**2 - 2*px2
    assert (px4 + 1 - tx4) == (px+1-tx)*(px+1+tx)*(px2+1+tx2)
    yx4 = yx*tx*(tx**2-2*px)
    assert px4 == (tx4**2 + D*yx4**2)/4
    # now the 4-th twist
    G2_order = px4+1-( yx4)
    G2_order_= px4+1-(-yx4)
    #print("px4+1-(-yx4+tx4)/2 % rx == 0: {}".format((G2_order_ % rx) == 0))
    #print("px4+1-( yx4+tx4)/2 % rx == 0: {}".format((G2_order % rx) == 0))
    assert (G2_order % rx) == 0
    twx = yx4

    c2x = (x**56 + 8*x**53 + 28*x**50 + 19*x**48 + 56*x**47 + 136*x**45 + 70*x**44 + 420*x**42 + 56*x**41 + 147*x**40 + 728*x**39 + 28*x**38 + 920*x**37 + 770*x**36 + 8*x**35 + 2436*x**34 + 504*x**33 + 594*x**32 + 3528*x**31 + 196*x**30 + 3128*x**29 + 3010*x**28 + 40*x**27 + 6764*x**26 + 1512*x**25 + 1331*x**24 + 7656*x**23 + 420*x**22 + 5536*x**21 + 4662*x**20 + 56*x**19 + 8880*x**18 + 1096*x**17 + 1635*x**16 + 6720*x**15 - 500*x**14 + 4736*x**13 + 1808*x**12 - 488*x**11 + 4416*x**10 - 992*x**9 + 897*x**8 + 1152*x**7 - 752*x**6 + 1536*x**5 - 928*x**4 + 256*x**3 + 256*x**2 - 1024*x + 512)/256  # cofactor of quartic twist curve with order #Et(Fp^4) = c2(x)*r(x)
    assert c2x * rx == G2_order
    
    # optimal ate pairing has Miller loop f_{u,Q}(P) with no additional terms
    assert ((x + px**5) % rx) == 0
    assert ((-1 + x*px**3) % rx) == 0

    # Daiki Hayashida, Kenichiro Hayasaka, and Tadanori Teruya
    # https://eprint.iacr.org/2020/875
    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**16-1) // Phi_k) == (x**8-1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**8+1)//rx
    assert exponent_x == cx * (px+Tx) * (px**2 + Tx**2) * (px**4 + Tx**4) + h2x
    exponent = ZZ(exponent_x(u0))

    # breaking up exponent_x
    # final exponentiation: hard part
    l0=(x**8 + 2*x**5 + x**2 + 4)
    l1=-(x**11 + 2*x**8 + x**5 + 4*x**3 + 4)
    l2=(x**14 + 2*x**11 + x**8 + 4*x**6 + 4*x**3)
    l3=(x**9 + 2*x**6 + x**3 + 4*x)
    l4=-(x**12 + 2*x**9 + x**6 + 4*x**4 + 4*x)
    l5=(x**15 + 2*x**12 + x**9 + 4*x**7 + 4*x**4)
    l6=(x**10 + 2*x**7 + x**4 + 4*x**2)
    l7=-(x**13 + 2*x**10 + x**7 + 4*x**5 + 4*x**2)
    
    assert l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*l7)))))) == (-4*x**5)*exponent_x
    exponent_easy = (px**8-1)
    exponent_hard_v0 = ZZ(((-4*x**5)*exponent_x)(u0))

    p = ZZ(px(u0))
    r = ZZ(rx(u0))
    c = ZZ(cx(u0))
    c2 = ZZ(c2x(u0))
    t = ZZ(tx(u0))
    y = ZZ(yx(u0))
    t4 = ZZ(twx(u0))
    if (u0 % 2) == 1:
        r = r//2
        c = c*2
        c2 = c2*2
        exponent = exponent*2

    assert exponent == (p**8+1)//r
    Fp = GF(p, proof=False)
    omega = Fp(betax(u0))
    a, E = find_curve_parameter_a(Fp, r, c) #E/Fp: y^2 = x^3 + x

    print("AFG16-{} E: y^2 = x^3 {:+d}x /Fp of {} bits".format(p.nbits(), a, p.nbits()))
    print("AFG16-{} curve seed u = {:#x} ({} bits)".format(p.nbits(), u0, u0.nbits()))
    cost_pairing_new16(u0)
    print("u = {:#x} {} bits".format(u0, u0.nbits()))
    print("p = {:#x} {} bits".format(p, p.nbits()))
    print("r = {:#x} {} bits".format(r, r.nbits()))

    Fpz = Fp['z']; (z,) = Fpz._first_ngens(1)

    assert (p % 4) == 1
    b = 1
    while not (z**4 - b).is_irreducible():
        b = b+1
    print("Fp4 = Fp[x]/(x^4-{})".format(b)) # Fp4 = Fp[x]/(x^4 - 3)
    Fp4 = Fp.extension(z**4 - b, names=('i',)); (i,) = Fp4._first_ngens(1)
    Fp4s = Fp4['s']; (s,) = Fp4s._first_ngens(1)
    
    xiD, atwD = find_twist_curve_parameter_xi_ab(a, Fp4, r, c2, d=4, D_twist=True)
    print("Fq4 = Fq[y]/(y^4-({}))".format(xiD)) # Fq4 = Fq[y]/(y^4 - (i + 6))
    Fq4D = Fp4.extension(s**4 - xiD, names=('wD',)); (wD,) = Fq4D._first_ngens(1)
    ED = EllipticCurve([Fp4(atwD), Fp4(0)]) # ED/Fp^4: y^2 = x^3 + x/(i + 4) D-twist
    E_Fq4D = EllipticCurve([Fq4D(a), Fq4D(0)])  # ED/Fq^4: y^2 = x^3 + x

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
    Fp16D = Fp.extension((z**4 - i0D)**4 - b*i1D**4, names=('SD',)); (SD,) = Fp16D._first_ngens(1)
    E16D = EllipticCurve([Fp16D(a), Fp16D(0)])

    def map_Fq4D_Fp16D(X, aD=None):
        # evaluate elements of Fq4D = Fp[i]/(i^4-2)[s]/(s^4-i) at i=S^4 and s=S
        # i <-> wD^4 = SD^4 and wD <-> SD
        if aD is None:
            aD = SD
        return sum([xi.polynomial()((aD**4-i0D)/i1D) * aD**e for e,xi in enumerate(X.list())])

    def map_Fp4_Fp16D(X):
        # evaluate elements of Fq=Fp[i] at i=wD^4 = SD^4
        return X.polynomial()((SD**4-i0D)/i1D)

    xiM, atwM = find_twist_curve_parameter_xi_ab(a, Fp4, r, c2, d=4, D_twist=False) # should find
    print("Fq4 = Fq[y]/(y^4-({}))".format(xiM)) # Fq4 = Fq[y]/(y^4 - i)
    Fq4M = Fp4.extension(s**4 - xiM, names=('wM',)); (wM,) = Fq4M._first_ngens(1)
    print(Fq4M)
    EM = EllipticCurve([Fp4(atwM), Fp4(0)]) # EM/Fp^4: y^2 = x^3 + i*x M-twist
    E_Fq4M = EllipticCurve([Fq4M(a), Fq4M(0)])  # EM/Fq^4: y^2 = x^3 + x
    # s^4=xiM = xiM0 + i*xiM1 => (s^4-xiM0)^4 = i^4*xiM1^4 = b*xiM1^4

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
    Fp16M = Fp.extension((z**4 - i0M)**4 - b*i1M**4, names=('SM',)); (SM,) = Fp16M._first_ngens(1)
    
    E16M = EllipticCurve([Fp16M(a), Fp16M(0)])

    def map_Fq4M_Fp16M(X, aM=None):
        # converts element from Fq^4 to Fp^16 for M-twist
        if aM is None:
            aM = SM
        return sum([xi.polynomial()((aM**4-i0M)/i1M) * aM**e for e,xi in enumerate(X.list())])

    def map_Fp4_Fp16M(X):
        # converts element from Fq^4 to Fp^16 for M-twist
        return X.polynomial()((SM**4-i0M)/i1M)

    print("test map_Fq4M_Fp16M")
    x0 = Fq4M.random_element()
    x1 = map_Fq4M_Fp16M(x0)
    
    print("test map_Fq4D_Fp16D")
    x0 = Fq4D.random_element()
    x1 = map_Fq4D_Fp16D(x0)

    print("test E (G1)")
    test_order(E,r*c)
    print("test ED (G2)")
    test_order(ED,r*c2)
    print("test EM (G2)")
    test_order(EM,r*c2)

    print("test cofactor clearing on G1")
    lambr = ZZ(lambrx(u0))
    lambc = ZZ(0)

    test_lambda_omega_g1_j1728(E, r, c, c, u0, lambr, lambc, omega)
    print("c = {} = {}".format(c, c.factor()))
    g = gcd(p-1, c)
    print("gcd(c, p-1) = {} = {}".format(g, g.factor()))
    print("omega = {}".format(omega))
    # give None as argument for omega because is it not required, phi does not apply to the cofactor side
    test_cofactor_clearing_g1(E, r, c, u0, t, None, cofactor_clearing_g1_new16, verbose=False)

    print("test subgroup_membership_testing_g1")
    test_membership_testing_g1(E, r, c, u0, t, omega, membership_testing_g1_new16, verbose=False)

    print("test Frobenius map on G2 with M-twist")
    test_g2_frobenius_eigenvalue(E16M,EM,Fq4M,map_Fq4M_Fp16M,r,c2,D_twist=False)
    test_g2_frobenius_eigenvalue_alt(E16M,EM,map_Fp4_Fp16M,r,c2,D_twist=False)
    print("test Frobenius map on G2 with D-twist")
    test_g2_frobenius_eigenvalue(E16D,ED,Fq4D,map_Fq4D_Fp16D,r,c2,D_twist=True)
    test_g2_frobenius_eigenvalue_alt(E16D,ED,map_Fp4_Fp16D,r,c2,D_twist=True)

    print("test subgroup_membership_testing_g2 with D-twist, with M-twist")
    if (u0 % 2) == 0:
        test_membership_testing_g2(ED, r, c2, u0, t4, Fq4D, membership_testing_g2_new16, D_twist=True)
        test_membership_testing_g2(ED, r, c2, u0, t4, Fq4D, membership_testing_g2_new16_alt, D_twist=True)
        test_membership_testing_g2(EM, r, c2, u0, t4, Fq4M, membership_testing_g2_new16, D_twist=False)
        test_membership_testing_g2(EM, r, c2, u0, t4, Fq4M, membership_testing_g2_new16_alt, D_twist=False)
    else:
        test_membership_testing_g2(ED, r, c2, u0, t4, Fq4D, membership_testing_g2_new16_odd, D_twist=True)
        test_membership_testing_g2(EM, r, c2, u0, t4, Fq4M, membership_testing_g2_new16_odd, D_twist=False)

    if (u0 % 2) == 0:
        print("test cofactor clearing on G2, D-twist")
        for case in range(euler_phi(k)):
            test_cofactor_clearing_g2(ED, r, c2, u0, t4, Fq4D, cofactor_clearing_g2_new16_even, True, case)
        print("test cofactor clearing on G2, M-twist")
        for case in range(euler_phi(k)):
            test_cofactor_clearing_g2(EM, r, c2, u0, t4, Fq4M, cofactor_clearing_g2_new16_even, False, case)
    else:
        print("test cofactor clearing on G2, D-twist")
        for case in range(euler_phi(k)):
            test_cofactor_clearing_g2(ED, r, c2, u0, t4, Fq4D, cofactor_clearing_g2_new16_odd, True, case)
        print("test cofactor clearing on G2, M-twist")
        for case in range(euler_phi(k)):
            test_cofactor_clearing_g2(EM, r, c2, u0, t4, Fq4M, cofactor_clearing_g2_new16_odd, False, case)

    print("tests with D-twist")
    test_sparse_sparse_mult_d4_twist(Fq4D)
    test_sparse_mult_d4_twist(Fq4D)

    test_double_line_ate_cln_b0(E, ED, Fq4D, D_twist=True)
    test_add_line_ate_cln_b0(E, ED, Fq4D, D_twist=True)

    test_miller_function_ate_cln_b0_quartic_twist(miller_function_ate_cln_b0_quartic_twist, E, ED, Fq4D, r, c, c2, t-1, D_twist=True, verbose=False)
    test_miller_function_ate_cln_b0_quartic_twist(miller_function_ate_cln_b0_quartic_twist_acc_line, E, ED, Fq4D, r, c, c2, t-1, D_twist=True, verbose=False)

    test_double_line_j(E, ED, Fq4D, D_twist=True)
    test_double_line_affine_j(E, ED, Fq4D, D_twist=True)
    test_add_line_j(E, ED, Fq4D, D_twist=True)
    test_add_line_affine_j(E, ED, Fq4D, D_twist=True)
    test_double_line_cln_b0(E, ED, Fq4D, D_twist=True)
    test_add_line_cln_b0(E, ED, Fq4D, D_twist=True)
    test_add_line_cln_b0_with_z(E, ED, Fq4D, D_twist=True)

    test_miller_function_ate(E, E_Fq4D, ED, r, c, c2, t-1, D_twist=True)
    test_miller_function_ate_2naf(E, E_Fq4D, ED, r, c, c2, t-1, D_twist=True)
    test_miller_function_ate_csb(E, E_Fq4D, ED, r, c, c2, t-1, D_twist=True)
    test_miller_function_ate_cln_b0(E, E_Fq4D, ED, r, c, c2, t-1, D_twist=True)
    test_miller_function_ate_2naf_cln_b0(E, E_Fq4D, ED, r, c, c2, t-1, D_twist=True)

    test_bilinearity_miller_loop_ate_absolute_extension(E, ED, Fq4D, Fp16D, map_Fq4D_Fp16D, r, c, c2, u0, D_twist=True, function_name=miller_loop_opt_ate_new16)

    test_bilinearity_miller_loop_ate_absolute_extension(E, ED, Fq4D, Fp16D, map_Fq4D_Fp16D, r, c, c2, u0, D_twist=True, function_name=miller_loop_opt_ate_new16_cln_b0)

    print("tests with M-twist")
    test_sparse_sparse_mult_m4_twist(Fq4D)
    test_sparse_mult_m4_twist(Fq4D)

    test_double_line_ate_cln_b0(E, EM, Fq4M, D_twist=False)
    test_add_line_ate_cln_b0(E, EM, Fq4M, D_twist=False)

    test_miller_function_ate_cln_b0_quartic_twist(miller_function_ate_cln_b0_quartic_twist, E, EM, Fq4M, r, c, c2, t-1, D_twist=False, verbose=False)
    test_miller_function_ate_cln_b0_quartic_twist(miller_function_ate_cln_b0_quartic_twist_acc_line, E, EM, Fq4M, r, c, c2, t-1, D_twist=False, verbose=False)

    test_double_line_j(E, EM, Fq4M, D_twist=False)
    test_double_line_affine_j(E, EM, Fq4M, D_twist=False)
    test_add_line_j(E, EM, Fq4M, D_twist=False)
    test_add_line_affine_j(E, EM, Fq4M, D_twist=False)
    test_double_line_cln_b0(E, EM, Fq4M, D_twist=False)
    test_add_line_cln_b0(E, EM, Fq4M, D_twist=False)
    test_add_line_cln_b0_with_z(E, EM, Fq4M, D_twist=False)

    test_miller_function_ate(E, E_Fq4M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_2naf(E, E_Fq4M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_csb(E, E_Fq4M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_cln_b0(E, E_Fq4M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_2naf_cln_b0(E, E_Fq4M, EM, r, c, c2, t-1, D_twist=False)

    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq4M, Fp16M, map_Fq4M_Fp16M, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_new16)

    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq4M, Fp16M, map_Fq4M_Fp16M, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_new16_cln_b0)
    """
    print("Test Final Exp")
    """
    test_final_exp_easy_k16(Fp16D)
    test_final_exp_easy_k16(Fp16M)
    #expected_exponent = ((p**8 + 1)//r)
    test_final_exp_hard_k16(Fp16M, r, u0, function_name=final_exp_hard_new16, expected_exponent=exponent_hard_v0)# false with u>0
    test_final_exp_hard_k16(Fp16D, r, u0, function_name=final_exp_hard_new16, expected_exponent=exponent_hard_v0)# false with u>0

    test_final_exp_hard_k16(Fp16M, r, u0, function_name=final_exp_hard_new16_v1, expected_exponent=exponent)
    test_final_exp_hard_k16(Fp16D, r, u0, function_name=final_exp_hard_new16_v1, expected_exponent=exponent)
    test_final_exp_hard_k16(Fp16M, r, u0, function_name=final_exp_hard_new16_v2, expected_exponent=exponent)
    test_final_exp_hard_k16(Fp16D, r, u0, function_name=final_exp_hard_new16_v2, expected_exponent=exponent)

def test_curve_new16_765():
    # This is a new curve for k = 16 and rho = 2 with perfect square cofactor h
    # Let's call it AFG16 for Aranha-Fotiadis-Guillevic
    u0 = ZZ(-(2**48 - 2**44 + 2**37))
    test_curve(u0)

def test_curve_new16_765a():
    # with a positive u0 for the tests
    u0 = ZZ(2**48 - 2**20 + 2**15 + 2**5)
    assert u0 == ZZ(0xfffffff08020)
    test_curve(u0)

def test_curve_new16_767a():
    # with positive odd seed
    u0 = ZZ(2**48+2**39+2+1)
    assert u0 == 0x1008000000003
    test_curve(u0)

def test_curve_new16_767b():
    # with negative odd seed
    u0 = -ZZ(2**48+2**38+2**28+2**8+1)
    assert u0 == -0x1004010000101
    test_curve(u0)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_new16_765()
    test_curve_new16_765a()
    test_curve_new16_767a()
    test_curve_new16_767b()
