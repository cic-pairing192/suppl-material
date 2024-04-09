"""
Test pairings on FST66 k=22 curves
Date: 2023, June 23
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
from pairing_fst66_k22 import *
from test_pairing import *
from test_scalar_mult import test_glv_scalar_mult_g1_j0
from cost_pairing import cost_pairing_fst66_k22

def test_curve(u0, b=None):
    print("u0 = {:#x}".format(u0))
    #preparse("QQx.<x> = QQ[]")
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    # from gitlab.inria.fr/tnfs-alpha/alpha sage/tnfs/curve/fst66.py
    D = 3
    k = 22
    rx = QQx(cyclotomic_polynomial(3*k))
    tx = QQx(x**3+1)
    yx = QQx((x**3-1)*(2*x**(k//2)-1)/3)
    px = QQx((x**3-1)**2*(x**k-x**(k//2)+1) + 3*x**3)/QQ(3)
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
    assert betax == (2*x**27 + 4*x**26 - x**25 - 6*x**24 - 12*x**23 + 3*x**22 + 8*x**21 + 16*x**20 - 4*x**19 - 8*x**18 - 16*x**17 + 2*x**16 + 4*x**15 + 17*x**14 + 2*x**13 + 4*x**12 - 10*x**11 - 4*x**10 - 8*x**9 + 2*x**8 + 4*x**7 + 8*x**6 - 9*x**3 + 2*x**2 + 4*x - 1)/9
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
    while not (z**e - a).is_irreducible():
        a = a+1
    print("Fp{} = Fp[x]/(x^{} - {})".format(e, e, a))
    Fp11 = Fp.extension(z**e - a, names=('i',)); (i,) = Fp11._first_ngens(1)
    Fq = Fp11
    Fp11s = Fp11['s']; (s,) = Fp11s._first_ngens(1)
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
    test_final_exp_easy_k22(FpkM)
    sx = x**27 + x**26 - 3*x**24 - 3*x**23 + 4*x**21 + 4*x**20 - 4*x**18 - 4*x**17 - x**16 + 3*x**15 + 4*x**14 + 3*x**13 - x**12 - 4*x**11 - 4*x**10 + 4*x**8 + 4*x**7 - 3*x**5 - 3*x**4 + 4*x**2 + 4*x
    s0 = ZZ(sx(u0))
    test_final_exp_hard_k22(FpkM, u0, r, final_exp_hard_fst66_k22, expected_exponent=s0*exponent)

    test_double_line_cln_a0_quad_twist(E, EM, Fq2M, D_twist=False)
    test_add_line_cln_a0_quad_twist(E, EM, Fq2M, D_twist=False)
    test_bilinearity_miller_loop_ate_cln_a0_cubic_twist_explicit(E, Eq2M, EM, r, c, c2, t-1, D_twist=False, function_name=miller_function_ate_cln_a0_quad_twist, Tate=False)
    #test_bilinearity_miller_loop_ate_cln_a0_cubic_twist_explicit(E, Eq2M, EM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_fst66_k22_cln_a0_quad_twist, Tate=False, opt=True)

    print("test Miller M-twist tate")
    test_miller_function_tate(E, Eq2M, EM, r, c, c2, D_twist=False)
    test_miller_function_tate_2naf(E, Eq2M, EM, r, c, c2, D_twist=False)

    print("test Miller M-twist ate")
    test_miller_function_ate(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)
    test_miller_function_ate_2naf(E, Eq2M, EM, r, c, c2, t-1, D_twist=False)

    print("test Miller M-twist optimal ate")
    test_bilinearity_miller_loop_ate_absolute_extension(E, EM, Fq2M, FpkM, map_Fq2M_FpkM, r, c, c2, u0, D_twist=False, function_name=miller_loop_opt_ate_fst66_k22, curve_a_is_0=True)

def test_curve_510():
    u0 = ZZ(-2**18-2**16+2**14+2**5+2**3+1)
    assert u0 == -0x4bfd7
    b = 1
    cost_pairing_fst66_k22(u0)
    test_curve(u0, b)

def test_curve_530():
    u0 = ZZ(2**19-2**13-2**11-2**8+2**5+2)
    assert u0 == 0x7d722
    b = -2
    cost_pairing_fst66_k22(u0)
    test_curve(u0, b)

def test_curve_534():
    u0 = ZZ(2**19+2**15+2**13+2**11+2**3)
    assert u0 == 0x8a808
    b = -2
    cost_pairing_fst66_k22(u0)
    test_curve(u0, b)

if __name__ == "__main__":
    arithmetic(False)
    test_curve_510()
    test_curve_530()
    test_curve_534()

test_vector_fst66_k22 = [
    {'u':-0x4bfd7, 'u_mod_11':1, 'b': 1, 'pnbits':510,'rnbits':365, 'label':"u=-2^18-2^16+2^14+2^5+2^3+1          Hw2NAF=6"},#
    {'u':-0x4dcb7, 'u_mod_11':1, 'b': 1, 'pnbits':511,'rnbits':366, 'label':"u=-2^18-2^16+2^13+2^10-2^8+2^6+2^3+1 Hw2NAF=8"},#
    {'u': 0x7d722, 'u_mod_11':5, 'b':-2, 'pnbits':530,'rnbits':380, 'label':"u=+2^19-2^13-2^11-2^8+2^5+2          Hw2NAF=6"},#
    {'u': 0x8919a, 'u_mod_11':1, 'b':-2, 'pnbits':534,'rnbits':382, 'label':"u=+2^19+2^15+2^12+2^9-2^7+2^5-2^3+2  Hw2NAF=8"},#
    {'u': 0x89c1a, 'u_mod_11':5, 'b':-2, 'pnbits':534,'rnbits':383, 'label':"u=+2^19+2^15+2^13-2^10+2^5-2^3+2     Hw2NAF=7"},#
    {'u': 0x89e3c, 'u_mod_11':1, 'b':-2, 'pnbits':534,'rnbits':383, 'label':"u=+2^19+2^15+2^13-2^9+2^6-2^2        Hw2NAF=6"},#
    {'u': 0x8a808, 'u_mod_11':1, 'b':-2, 'pnbits':534,'rnbits':383, 'label':"u=+2^19+2^15+2^13+2^11+2^3           Hw2NAF=5"},#
    {'u': 0x90265, 'u_mod_11':1, 'b': 1, 'pnbits':536,'rnbits':384, 'label':"u=+2^19+2^16+2^9+2^7-2^5+2^2+1       Hw2NAF=7"},#
    {'u': 0x916e4, 'u_mod_11':1, 'b':-2, 'pnbits':536,'rnbits':384, 'label':"u=+2^19+2^16+2^13-2^11-2^8-2^5+2^2   Hw2NAF=7"},#
    {'u':-0x866ed, 'u_mod_11':1, 'b': 1, 'pnbits':533,'rnbits':382, 'label':"u=-2^19-2^15+2^13-2^11+2^8+2^4+2^2-1 Hw2NAF=8"},#
    {'u':-0x8e04c, 'u_mod_11':5, 'b':-2, 'pnbits':535,'rnbits':383, 'label':"u=-2^19-2^16+2^13-2^6-2^4+2^2        Hw2NAF=6"},#
]
