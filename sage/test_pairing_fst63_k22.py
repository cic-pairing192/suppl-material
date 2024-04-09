"""
Test pairings on FST63 k=22 curves
Date: 2023, April 29
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
from pairing_fst63_k22 import *
from test_pairing import *
from test_scalar_mult import test_glv_scalar_mult_g1_j1728
from cost_pairing import cost_pairing_fst63_k22

def test_curve(u0, a=None):
    print("u0 = {:#x}".format(u0))
    #preparse("QQx.<x> = QQ[]")
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    # from gitlab.inria.fr/tnfs-alpha/alpha sage/tnfs/curve/fst63.py
    k = 22
    D = 1
    rx = cyclotomic_polynomial(2*k)
    tx = x**2+1
    yx = (x**2-1) * x**(k//2)
    qx = (x**4 + 2*x**2 + 1 + (x**4 - 2*x**2 + 1)*x**k)/4
    cx = (qx+1-tx) // rx
    g,u,v = qx.xgcd(yx)
    if g == 1:
        inv_yx = v
    else:
        inv_yx = v/QQ(g)
    betax = (inv_yx*tx) % qx
    if betax.leading_coefficient() < 0:
        betax = -betax
    lambx = x**(k//2)
    mux = -x**(k//2)
    assert ((betax**2 + 1) % qx) == 0
    assert ((lambx**2 + 1) % rx) == 0
    ### cofactor of G2 defined over GF(p^11)
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
    #t11 = t*t10 -q*t9
    tx11 = tx**11 - 11*qx*tx**9 + 44*qx**2*tx**7 - 77*qx**3*tx**5 + 55*qx**4*tx**3 - 11*qx**5*tx
    assert (qx**11+1+tx11) % (qx + 1 + tx) == 0 # this is (q + 1 + t)
    assert (((qx**11+1+tx11) // (qx + 1 + tx)) % rx) == 0
    c2x = (qx**11+1+tx11) // rx

    ### final exp
    Tx = tx-1
    Phi_k = cyclotomic_polynomial(k)
    assert ((x**k-1) // Phi_k) == (x**11-1)*(x+1)
    h2x = Phi_k(Tx) // rx
    exponent_x = (qx**10 - qx**9 + qx**8 - qx**7 + qx**6 - qx**5 + qx**4 - qx**3 + qx**2 - qx + 1)//rx
    exponent = ZZ(exponent_x(u0))
    expected_exp = 4 * exponent_x
    ee = ZZ(expected_exp(u0))

    p = ZZ(qx(u0))
    r = ZZ(rx(u0))
    c = ZZ(cx(u0))
    c2 = ZZ(c2x(u0))
    t = ZZ(tx(u0))
    y = ZZ(yx(u0))
    Fp = GF(p, proof=False)
    if a is None:
        a, E = find_curve_parameter_a(Fp, r, c)
    else:
        E = EllipticCurve(Fp, [a, 0])

    print("FST63k{}-{} E: y^2 = x^3 {:+d}*x /Fp of {} bits".format(k, p.nbits(), a, p.nbits()))
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
    # define Fp11
    d = 2 # quadratic twist
    e = k//d
    a0 = -1
    while not (z**11 - a0).is_irreducible():
        a0 = a0+1
    print("Fp11 = Fp[x]/(x^11 - {})".format(a0))
    Fp11 = Fp.extension(z**11 - a0, names=('i',)); (i,) = Fp11._first_ngens(1)
    Fq = Fp11
    Fp11s = Fp11['s']; (s,) = Fp11s._first_ngens(1)
    xiM, atwM, _ = find_twist_curve_parameter_xi_ab(a, Fq, r, c2, d=2, D_twist=False, ba=0)
    EM = EllipticCurve([Fq(atwM), Fq(0)])
    Fq2M = Fq.extension(s**2 - xiM, names=('wM',)); (wM,) = Fq2M._first_ngens(1)
    Eq2M = EllipticCurve([Fq2M(a), Fq2M(0)])

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
    # s^d - xi = 0 <=> s^d - i0 = i1*i <=> (s^d - i0)^e = i1^e*(i^e) where here i^e - a0 = 0
    # resultant(s^d-xi, z^e - a0)

    FpkM = Fp.extension((z**d - i0M)**e - i1M**e * a0, names=('SM',)); (SM,) = FpkM._first_ngens(1)
    EkM = EllipticCurve([FpkM(a), FpkM(0)])

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
    test_glv_scalar_mult_g1_j1728(E, lambda_mod_r, beta_mod_p, r, c)

    print("\nFinal exponentiation")
    test_final_exp_easy_k22(FpkM)
    test_final_exp_hard_k22(FpkM, u0, r, final_exp_hard_fst63_k22, expected_exponent=ee)

    print("test Miller M-twist tate")
    test_miller_function_tate(E, Eq2M, EM, r, c, c2, D_twist=False)
    test_miller_function_tate_2naf(E, Eq2M, EM, r, c, c2, D_twist=False)

    print("test Miller M-twist ate")
    test_miller_function_ate(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_2naf(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)

    print("test Miller M-twist optimal ate")
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_fst63_k22, curve_a_is_0=False)
    #test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_super_opt_ate_fst63_k22, curve_a_is_0=False)
    #test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_x_super_opt_ate_fst63_k22, curve_a_is_0=False)

def test_curve_494_r382():
    """
    a seed so that r is 382-bit long but it has only 184 bits of security in GF(p^22) because of STNFS
    """
    u0 = ZZ(2**19+2**15-2**12-2**10-1)
    assert u0 == 0x86bff
    a = 1
    #cost_pairing_fst63_k22(u0,lower_bound_m11=True)
    cost_pairing_fst63_k22(u0,lower_bound_m11=False)
    test_curve(u0, a=1)

def test_curve_544_r420():
    """
    a seed so that r is 420-bit long and offers 194 bits of security in GF(p^22) w.r.t. STNFS
    """
    u0 = ZZ(2**21-2**13+2**6+2**3+1)
    assert u0 == 0x1fe049
    a = 1
    #cost_pairing_fst63_k22(u0,lower_bound_m11=True)
    cost_pairing_fst63_k22(u0,lower_bound_m11=False)
    test_curve(u0, a=1)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_494_r382()
    test_curve_544_r420()
