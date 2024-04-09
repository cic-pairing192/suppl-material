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
from pairing_sg20 import *
from test_pairing import *
from cost_pairing import cost_pairing_sg20

def test_miller_loop_opt_ate_sg20(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=False):
    """Testing Miller loop of optimal ate pairing on Scott-Guillevic k=20 (Aurifeuillean) curve

    Testing the function miller_loop_opt_ate_sg20(Q2, P, u)
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
    ok = test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=D_twist, function_name=miller_loop_opt_ate_sg20_v0, curve_a_is_0=False)
    print("test bilinearity of SG20 optimal ate pairing, vector (2*u,0,-1,0,0,0,0,1): {}".format(ok))

    ok = test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, u, D_twist=D_twist, function_name=miller_loop_opt_ate_sg20_v1, curve_a_is_0=False)
    print("test bilinearity of SG20 optimal ate pairing, vector (u,0,-1,0,0,u,0,0): {}".format(ok))

    return ok

def test_final_exp_hard_sg20(Fpk, u, r, function_name=final_exp_hard_sg20, expected_exponent=None):
    p = Fpk.characteristic()
    if expected_exponent is None:
        expected_exponent = cyclotomic_polynomial(k)(p)//r
    ok_exp = True
    ok_r = True
    ok_inv = True
    i = 0
    while (ok_r and ok_inv and ok_exp) and i < 10:
        f0 = Fpk.random_element()
        f = final_exp_easy_k20(f0)
        g = function_name(f, u)
        ok_r = g**r == Fpk(1)
        ok_exp = g == f**expected_exponent
        ok_inv = g.frobenius((20//2)) == 1/g
        i += 1
    print("test {}: f^r == 1: {}, f == m^expected_exp: {}, f^10 == 1/f: {}".format(function_name.__name__, ok_r, ok_exp, ok_inv))
    return ok_r and ok_exp and ok_inv

def test_curve(u0, a=None):
    u0 = ZZ(u0)
    cost_pairing_sg20(u0)
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 20
    D = 1
    
    A = 2
    rho = 7/4
    lambx = -8*x**5 - 1
    rx = 16*x**8 + 16*x**7 + 8*x**6 - 4*x**4 + 2*x**2 + 2*x + 1
    exp_tr = 19
    tx = 16*x**7 + 8*x**6 - 4*x**4 - 4*x**3 + 2*x**2 + 2*x + 2
    px = 128*x**14 + 128*x**13 - 32*x**12 - 96*x**11 - 48*x**10 + 32*x**9 + 56*x**8 + 32*x**7 - 4*x**6 - 12*x**5 - 6*x**4 + 4*x**2 + 2*x + 1
    yx = 16*x**7 + 8*x**6 - 8*x**5 - 4*x**4 + 2*x**2 + 2*x
    cx = 8*x**6 - 6*x**4 + 2*x**2
    betax = 128*x**12 + 128*x**11 - 32*x**10 - 96*x**9 - 48*x**8 + 24*x**6 + 24*x**5 + 4*x**4 - 4*x**3 - 6*x**2 - 4*x - 1

    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**10-1)*(x**2+1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**8 - px**6 + px**4 - px**2 + 1)//rx
    exponent = ZZ(exponent_x(u0))

    # for G2, compute #E(Fp5) then compute its 4-th twist
    d = 4
    tx5 = tx**5 - 5*px*tx**3 + 5*px**2*tx
    px5 = px**5
    # yx5 is the square root of -(tx5**2 - 4*px5)
    # fixing polynomial yx5; it was wrong before
    yx5 = 262144*x**35 + 655360*x**34 - 1310720*x**32 - 1228800*x**31 + 499712*x**30 + 2007040*x**29 + 1249280*x**28 - 1044480*x**27 - 2007040*x**26 - 724992*x**25 + 1070080*x**24 + 1367040*x**23 + 220160*x**22 - 757760*x**21 - 681216*x**20 - 14080*x**19 + 377600*x**18 + 252160*x**17 - 29120*x**16 - 141760*x**15 - 74880*x**14 + 15040*x**13 + 38800*x**12 + 16800*x**11 - 4632*x**10 - 8280*x**9 - 3200*x**8 + 640*x**7 + 1160*x**6 + 408*x**5 - 60*x**4 - 120*x**3 - 50*x**2 - 10*x
    assert tx5**2 - 4*px5 == -D*yx5**2
    E2_order = px5 + 1 - yx5
    c2x = (px5 + 1 - yx5) // rx
    assert (E2_order % rx) == 0

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
    if a is None:
        a, E = find_curve_parameter_a(Fp, r, c) #E/Fp: y^2 = x^3 + a*x
    else:
        E = EllipticCurve(Fp, [a, 0])
    print("SG20-{} E: y^2 = x^3 {:+d}x /Fp of {} bits".format(p.nbits(), a, p.nbits()))
    print("u = {:#x} {} bits".format(u0, u0.nbits()))
    print("p = {:#x} {} bits".format(p, p.nbits()))
    print("r = {:#x} {} bits".format(r, r.nbits()))
    print("c = {:#x} {} bits".format(c, c.nbits()))
    print("t = {:#x} {} bits".format(t, t.nbits()))
    print("c2 = {:#x} {} bits".format(c2, c2.nbits()))
    
    # final exp hard
    l0 = -32*x**11 + 24*x**9 - 8*x**7 - 4*x**4 + 2*x**3
    l1 = -64*x**13 + 48*x**11 - 16*x**9 - 8*x**6 + 4*x**5
    l2 = -64*x**13 - 64*x**12 + 48*x**11 + 80*x**10 - 40*x**8 - 20*x**7 - 8*x**6 + 6*x**5 + 10*x**4 + 2*x**3 - 2*x**2 - x - 1
    l3 =  64*x**13 + 64*x**12 - 48*x**11 - 48*x**10 + 16*x**9 + 16*x**8 + 8*x**7 + 8*x**6 - 2*x**5 - 4*x**4 + 2*x**3 + 1
    l4 = -64*x**13 + 48*x**11 - 16*x**9 - 16*x**8 - 8*x**7 + 4*x**6 + 10*x**5 - 4*x**4 - 2*x**3 - 2*x
    l5 = -64*x**13 - 64*x**12 + 16*x**11 + 48*x**10 + 8*x**9 - 16*x**8 - 16*x**7 - 16*x**6 + 2*x**5 + 6*x**4 - 2*x**2 - 1
    l6 =   8*x**7 - 6*x**5 + 2*x**3 + 1
    l7 =  16*x**9 - 12*x**7 + 4*x**5 + 2*x**2 - x
    
    assert (l0 + l1*px + l2*px**2 + l3*px**3 + l4*px**4 + l5*px**5 + l6*px**6 + l7*px**7) == (2*x**3*exponent_x)

    #simplified li
    m6 = x*cx + 1
    y1 = 2*x*m6 - 1
    m7 = x*y1    # = 2*x**2*m6 - x
    y2 = 2*x*m7  # = 4*x**3*m6 - 2*x**2
    m0 = -x*y2   # = -4*x**4*m6 + 2*x**3
    y3 = -2*x*m0 # = 8*x**5*m6 - 4*x**4
    m1 = -x*y3   # = -8*x**6*m6 + 4*x**5
    m4 = m1 - m6 - y1
    m3 = - m1 + y3 + m6
    m2 = m1 - y3 + y2 + m7 - m6 - cx
    m5 = m1 - y3 + m0 - m6 - cx
    
    assert (m0 + m1*px + m2*px**2 + m3*px**3 + m4*px**4 + m5*px**5 + m6*px**6 + m7*px**7) == (2*x**3*exponent_x)

    #print("short vector for optimal ate pairing")
    #euler_phi = Phi_k.degree()
    #col1 = Matrix(ZZ, euler_phi-1, 1, [((t-1)**j) % r for j in range(1, euler_phi)])
    #N = block_matrix(ZZ, [ [Matrix(ZZ, 1, 1, [r]), zero_matrix(ZZ, 1, euler_phi-1)], [col1, 1]])
    ##     R := LLL(M);
    #N = block_matrix(ZZ, euler_phi, euler_phi, [ [Matrix(ZZ, 1, 1, [r]), zero_matrix(ZZ, 1, euler_phi-1)], [col1, 1]])
    #N.LLL()

    Fpz = Fp['z']; (z,) = Fpz._first_ngens(1)
    # extension of degree k//4
    e = k//4
    print("p mod 4 = {} p mod 5 = {} p mod 20 = {}".format(p % 4, p % 5, p % 20))
    #assert (p % k) == 1
    assert (p % 4) == 1
    #assert (p % (k//4)) == 1
    # we should have p = 1 mod k//4 to be able to define the extension with a binomial x^(k//4)+a0, and because D=1, we have p=1 mod 4, consequently p = 1 mod k
    # but apparetly p=1 mod 5 is not available
    a0 = 2
    if (p % e) != 1:
        a1 = 1
    else:
        a1=0
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
    # s^4 - xi = 0 <=> s^4 - i0 = i1*i <=> (s^4 - i0)^e = i1^e*(a0-a1*x)
    # resultant(s^4-xi, z^e +a1*z - a0)

    FpkM = Fp.extension((z**4 - i0M)**e - i1M**e * (a0-a1*z), names=('SM',)); (SM,) = FpkM._first_ngens(1)
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

    print("test map_Fq4M_FpkM")
    x0 = Fq4M.random_element()
    x1 = map_Fq4M_FpkM(x0)

    print("test map_FqM_FpkM")
    x0 = Fq.random_element()
    x1 = map_Fq_FpkM(x0)

    # ok
    print("test E (G1)")
    test_order(E,r*c)
    print("test E' (G2) M-twist")
    test_order(EM,r*c2)

    print("test Frobenius map on G2 with M-twist")
    # now the Frobenius map on G2 works
    test_g2_frobenius_eigenvalue(EkM, EM, Fq4M, map_Fq4M_FpkM, r, c2, D_twist=False)
    test_g2_frobenius_eigenvalue_alt(EkM, EM, map_Fq_FpkM, r, c2, D_twist=False)

    print("tests with M-twist")
    test_sparse_sparse_mult_m4_twist(Fq4M)
    test_sparse_mult_m4_twist(Fq4M)

    test_double_line_ate_cln_b0(E, EM, Fq4M, D_twist=False)
    test_add_line_ate_cln_b0(E, EM, Fq4M, D_twist=False)

    test_double_line_j(E, EM, Fq4M, D_twist=False)
    test_double_line_affine_j(E, EM, Fq4M, D_twist=False)
    test_add_line_j(E, EM, Fq4M, D_twist=False)
    test_add_line_affine_j(E, EM, Fq4M, D_twist=False)
    test_double_line_cln_b0(E, EM, Fq4M, D_twist=False)
    test_add_line_cln_b0(E, EM, Fq4M, D_twist=False)
    test_add_line_cln_b0_with_z(E, EM, Fq4M, D_twist=False)

    print("test Miller M-twist tate")
    test_miller_function_tate(E, Eq4M, EM, r, c, c2, D_twist=False)
    test_miller_function_tate_2naf(E, Eq4M, EM, r, c, c2, D_twist=False)

    print("test Miller M-twist ate")
    test_miller_function_ate(E, Eq4M, EM, r, c, c2, abs(t-1), D_twist=False)
    test_miller_function_ate_2naf(E, Eq4M, EM, r, c, c2, abs(t-1), D_twist=False)

    print("test Miller M-twist optimal ate")
    test_miller_loop_opt_ate_sg20(E, EM, Fq4M, FpkM, map_Fq4M_FpkM, r, c, c2, u0, D_twist=False)

    print("\nFinal exponentiation")
    test_final_exp_easy_k20(FpkM)
    test_final_exp_hard_sg20(FpkM, u0, r, function_name=final_exp_hard_sg20, expected_exponent=(2*u0**3)*exponent)

def test_curve_sg20_670():
    """
    p is 670-bit long
    r is 383-bit long
    u = 0 mod 20
    u has Hamming weight 4 in 2-NAF form
    u is negative
    u is the largest possible (in absolute value) negative seed of Hamming weight 2-NAF <= 4 such that r is the largest possible <= 384 bits while p is machine-word aligned <= 672 bits
    this seed is the one in the paper
    """
    u0 = ZZ(-0x9fffffff6000)
    assert u0 == ZZ(-2**47-2**45+2**15+2**13)
    a = 1
    test_curve(u0, a)

def test_curve_sg20_666a():
    """
    p is 666-bit long
    r is 381-bit long
    u = 0 mod 20
    u has Hamming weight 4 in 2-NAF form
    u is positive
    u is the largest possible positive seed of Hamming weight <= 4 in 2-NAF form such that r is the largest possible <= 384 bits while p is machine-word aligned <= 672 bits
    """
    u0 = ZZ(2**47+2**35+2**32-2**5)
    assert u0 == ZZ(0x8008ffffffe0)
    a = 1
    test_curve(u0, a)

def test_curve_sg20_666b():
    """
    p is 666-bit long
    r is 381-bit long
    u = 0 mod 20
    u has Hamming weight 4
    u is positive
    u is the largest possible positive seed of Hamming weight <= 4 such that r is the largest possible <= 384 bits while p is machine-word aligned <= 672 bits
    """
    u0 = ZZ(2**47+2**30+2**9+2**4)
    assert u0 == ZZ(0x800040000210)
    a = 1
    test_curve(u0, a)

def test_curve_sg20_666c():
    """
    p is 666-bit long
    r is 381-bit long
    u = 0 mod 20
    u has Hamming weight 4
    u is negative
    u is the largest possible (in absolute value) negative seed of Hamming weight <= 4 such that r is the largest possible <= 384 bits while p is machine-word aligned <= 672 bits
    """
    u0 = ZZ(-2**47-2**27-2**13-2**9)
    assert u0 == ZZ(-0x800008002200)
    a = 1
    test_curve(u0, a)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_sg20_670() #p = 1 mod 5, the seed in the paper

    # only for testing with positive, negative, 2-NAF form seeds:
    #test_curve_sg20_666a() #p = 1 mod 5
    #test_curve_sg20_666b() #p = 1 mod 5
    #test_curve_sg20_666c() #p = 1 mod 5
