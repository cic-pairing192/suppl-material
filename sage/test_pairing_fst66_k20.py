"""
Test pairings on FST66 k=20 curves
Date: 2023, April 28
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
from pairing_fst66_k20 import *
from test_pairing import *
from test_scalar_mult import test_glv_scalar_mult_g1_j0
from cost_pairing import cost_pairing_fst66_k20

def test_curve(u0, b=None):
    print("u0 = {:#x}".format(u0))
    #preparse("QQx.<x> = QQ[]")
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    # from gitlab.inria.fr/tnfs-alpha/alpha sage/tnfs/curve/fst66.py
    D = 3
    k = 20
    rx = QQx(cyclotomic_polynomial(3*k))
    tx = QQx(x**(k//2+1)-x+1)
    yx = QQx((x**(k//2+1)+2*x**(k//2)+x-1)/3)
    px = QQx((x-1)**2*(x**k-x**(k//2)+1)+3*x**(k+1))/QQ(3)
    qx = px
    lambx = QQx(x**(k//2)-1)
    # now computes beta s.t. (-1+sqrt(-3))/2 = beta mod px
    # computes sqrt(-3) mod px
    # 4*px = tx^2 + 3*yx^2 <=> tx^2 = -3*yx^2 <=> tx/yx = +/- sqrt(-3)
    # computes the inverse of yx
    g,u,v = px.xgcd(yx)
    if g == 1:
        inv_yx = QQx(v)
    else:
        inv_yx = QQx(v)/QQ(g)
    betax = (QQx(-1+inv_yx*tx)/2) % px
    if betax.leading_coefficient() < 0:
        betax = -betax-1
    assert ((betax**2 + betax + 1) % px) == 0
    assert ((lambx**2 + lambx + 1) % rx) == 0
    assert betax == x**21 + x**20 + 2*x**19 + x**18 + 2*x**17 + x**16 + 2*x**15 + x**14 + 2*x**13 + x**12 + x**11 + 2*x**10 - x**9 + x**8 - x**7 + x**6 - x**5 + x**4 - x**3 + x**2 - 1
    ### end from gitlab.inria.fr/tnfs-alpha/alpha sage/tnfs/curve/fst66.py
    cx = (qx+1-tx)//rx
    ### cofactor of G2 defined over GF(p^10)
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
    tx10 = tx**10 - 10*qx*tx**8 + 35*qx**2*tx**6 - 50*qx**3*tx**4 + 25*qx**4*tx**2 - 2*qx**5
    assert (qx**10+1+tx10) % (qx**2 + tx**2 - 2*qx + 1) == 0 # this is (q^2 + 1 + t2)
    assert (((qx**10+1+tx10) // (qx**2 + tx**2 - 2*qx + 1)) % rx) == 0
    c2x = (qx**10+1+tx10) // rx
    
    ### final exp
    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**10-1)*(x**2+1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (px**8 - px**6 + px**4 - px**2 + 1)//rx
    exponent = ZZ(exponent_x(u0))

    # (exponent_x - h2x)//cx == (x-1)*(qx+tx-1)*(...)
    
    expected_exp = (-3*x**7 + 3*x**3 + 3*x) * exponent_x
    ee = ZZ(expected_exp(u0))
    
    p = ZZ(px(u0))
    r = ZZ(rx(u0))
    c = ZZ(cx(u0))
    c2 = ZZ(c2x(u0))
    t = ZZ(tx(u0))
    y = ZZ(yx(u0))
    Fp = GF(p, proof=False)
    if b is None:
        b, E = find_curve_parameter_b(Fp, r, c)
    else:
        E = EllipticCurve(Fp, [0, b])

    print("FST66k{}-{} E: y^2 = x^3 {:+d} /Fp of {} bits".format(k, p.nbits(), b, p.nbits()))
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
    # define Fp10
    d = 2 # quadratic twist
    e = k//d
    a = -1
    while not (z**10 - a).is_irreducible():
        a = a+1
    print("Fp10 = Fp[x]/(x^10 - {})".format(a))
    Fp10 = Fp.extension(z**10 - a, names=('i',)); (i,) = Fp10._first_ngens(1)
    Fq = Fp10
    Fp10s = Fp10['s']; (s,) = Fp10s._first_ngens(1)
    xiM, _, btwM = find_twist_curve_parameter_xi_ab(0, Fq, r, c2, d=2, D_twist=False, ba=b)
    EM = EllipticCurve([Fq(0), Fq(btwM)])
    Fq2M = Fq.extension(s**2 - xiM, names=('wM',)); (wM,) = Fq2M._first_ngens(1)
    Eq2M = EllipticCurve([Fq2M(0), Fq2M(b)])

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
    # s^d - xi = 0 <=> s^d - i0 = i1*i <=> (s^d - i0)^e = i1^e*(i^e) where here i^e - a = 0
    # resultant(s^d-xi, z^e - a)

    FpkM = Fp.extension((z**d - i0M)**e - i1M**e * a, names=('SM',)); (SM,) = FpkM._first_ngens(1)
    EkM = EllipticCurve([FpkM(0), FpkM(b)])
    
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

    print("test GLV on G1") # this function is defined in test_scalar_mult.py
    test_glv_scalar_mult_g1_j0(E, lambda_mod_r, beta_mod_p, r, c)

    print("\nFinal exponentiation")
    test_final_exp_easy_k20(FpkM)
    test_final_exp_hard_k20(FpkM, u0, r, final_exp_hard_fst66_k20, expected_exponent=ee)

    test_double_line_cln_a0_quad_twist(E, EM, Fq2M, D_twist=False)
    test_add_line_cln_a0_quad_twist(E, EM, Fq2M, D_twist=False)
    test_bilinearity_miller_loop_ate_cln_a0_cubic_twist_explicit(E, Eq2M, EM, r, c, c2, t-1, D_twist=False, function_name=miller_function_ate_cln_a0_quad_twist, Tate=False)
    #test_bilinearity_miller_loop_ate_cln_a0_cubic_twist_explicit(E, Eq2M, EM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_fst66_k20_cln_a0_quad_twist, Tate=False, opt=True)

    print("test Miller M-twist tate")
    test_miller_function_tate(E, Eq2M, EM, r, c, c2, D_twist=False)
    test_miller_function_tate_2naf(E, Eq2M, EM, r, c, c2, D_twist=False)

    print("test Miller M-twist ate")
    test_miller_function_ate(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_2naf(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)

    print("test Miller M-twist optimal ate")
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_fst66_k20, curve_a_is_0=True)
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_super_opt_ate_fst66_k20, curve_a_is_0=True)
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_x_super_opt_ate_fst66_k20, curve_a_is_0=True)

def test_curve_527():
    u0 = ZZ(-2**24+2**15-2**8-2**6-1)
    assert u0 == -0xff8141
    b = -9
    cost_pairing_fst66_k20(u0)
    test_curve(u0, b)

def test_curve_571():
    u0 = ZZ(2**26-2**18-2**15-2**13-2**6)
    assert u0 == 0x3fb5fc0
    b = 17
    cost_pairing_fst66_k20(u0)
    test_curve(u0, b)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_527()
    test_curve_571()
