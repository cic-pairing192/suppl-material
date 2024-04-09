from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.misc.functional import cyclotomic_polynomial
from pairing import bits_2naf

def cost_pairing_bls12(u0):
    """
    snark-2-chains project
    """
    # cost
    # a=0
    # AKLGL'11
    # there are three formulas in https://www.lirmm.fr/arith18/papers/Chung-Squaring.pdf for squaring in cubic extensions
    # S3 = m + 4*s; S3 = 2*m+3*s; S3 = 3*m+2*s
    u0 = ZZ(abs(u0))
    m = 1
    s = 1
    m2 = 3*m
    s2 = 2*m
    m6 = 6*m2 # multiplication in cubic extension
    #s6 = m2+4*s2 # =3*m+4*2*m = 11m squaring in cubic extension
    s6 = 2*m2+3*s2 # =2*3*m+3*2*m = 12m squaring in cubic extension
    m12 = 3*m6
    s12 = 2*m6
    f2 = 8*m
    f12 = 10*m
    inv = 25*m
    i12 = 97*m+inv # 94*m + i in Guillevic Masson Thome DCC'20 is not compatible with the tower
    i2 = 2*m + 2*s + inv
    k = 12
    e = 2
    d = 6
    assert e*d == k
    # AKLGL
    mk=m12; sk=s12; ik=i12
    me=m2 ; se=s2; sk=s12 # e = k/d
    double_line_ate = 3*me+6*se+(k//3)*m
    add_line_ate    = 11*me+2*se+(k//3)*m
    # Costello Lange Naehrig
    double_line_ate_cln = 2*me+7*se+(k//3)*m
    add_line_ate_cln    = 10*me+2*se+(k//3)*m
    sparse_dense        = 13*me
    sparse_sparse       = 6*me
    update1        = 13*me+sk
    update2        = 13*me

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    len2naf_u = len(bits_2naf_u0)
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    cost_ate = (u0.nbits()-1)*(double_line_ate+sk) - sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate+sparse_sparse+mk)
    cost_ate_2naf = (len(bits_2naf_u0)-1)*(double_line_ate+sk) - sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate+sparse_sparse+mk)
    cost_ate_cln = (u0.nbits()-1)*(double_line_ate_cln+sk) - sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln+sparse_sparse+mk)
    cost_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln+sk) - sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln+sparse_sparse+mk)
    print("m12 = {}m s12 = {}m".format(m12,s12))
    print("m2 = {}m s2 = {}m".format(m2,s2))

    print("cost ate Miller       = {}m".format(cost_ate))
    print("cost ate Miller 2-naf = {}m".format(cost_ate_2naf))
    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m + sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m + 6*m{2}+mk)".format(u0.nbits(),hw_u,e))
    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m + sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m + 6*m{2}+mk) (2-naf)".format(len(bits_2naf_u0),hw2naf_u,e))
    print("cost ate Miller       = {}m (Costello Lange Naehrig)".format(cost_ate_cln))
    print("cost ate Miller 2-naf = {}m (Costello Lange Naehrig)".format(cost_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m + sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m + 6*m{2}+mk)".format(u0.nbits(),hw_u,e))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m + sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m + 6*m{2}+mk) (2-naf)".format(len(bits_2naf_u0),hw2naf_u,e))

    min_cost_miller = min(cost_ate, cost_ate_2naf, cost_ate_cln, cost_ate_cln_2naf)
    
    # final exponentiation
    # (p^12-1)/r = (p^12-1)/Phi_12(u) * Phi_12(u)/r = (p^6-1)*(p^2+1)*(p^4-p^2+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**12-1) // cyclotomic_polynomial(12)) == (x**6-1)*(x**2+1)
    px = (x-1)**2*(x**4 - x**2 + 1)/3 + x
    rx = x**4-x**2+1
    l3 = (x-1)**2
    l2 = l3*x
    l1 = l2*x-l3
    l0 = l1*x + 3
    exponent = (px**4-px**2+1)//rx
    assert l0+px*(l1+px*(l2+px*l3)) == 3*exponent
    # now cost of exponentiation
    # easy part: exponent = (px**6-1)*(px**2+1)
    # px**6 is a conjugation: costs only 6 negations
    # one inversion in Fp12, one mult
    #f2_12 = 8*m # from cost_pairing.py DCC'2020
    # Simon Masson PhD thesis section 4.4.2
    f2_12 = 5*m2
    easy_part = i12 + m12 + f2_12 + m12
    # hard part: exponent = (px**4-px**2+1)//rx
    # assume that cyclotomic squarings are implemented (PKC'10 Granger Scott)
    # cost_exp_to_x = 4*(len2naf_u-1)*m2 + (6*(hw2naf_u - 1) -3)*m2 + (hw2naf_u - 1)*m12 + 3*(hw2naf_u - 1)*s2 + i2
    cost_exp_to_x = karabina_cost_exp(u0, m12, m2, s2, i2)
    s12cyclo = 18*m
    hard_part = 5*cost_exp_to_x + 10*m12 + 3*f12 + 2*s12cyclo
    print("cost final exp easy: {}m".format(easy_part))
    print("cost final exp hard: {}m (with Karabina technique)".format(hard_part))
    print("cost final exp:      {}m".format(easy_part + hard_part))
    print("\ncost pairing (total) {}m".format(easy_part + hard_part + min_cost_miller))

def cost_miller_loop_bls_k_odd(u, k, m, me, se, mk, sk, ik_cyclo):
    """
    The Miller loop for optimal ate pairing is f_{u,Q}(P)
    but there is no denominator elimination, hence
    the lines and tangents simplify less
    Formulas from Costello Lange Naehrig PKC 2010, Section 6
    Dbl+line evaluation: 6*me + 7*se + k*m
    mxAdd+line evaluation: 13*me + 3*se + k*m
    Add+line evaluation: 16*me + 3*se + k*m
    """
    d = 3
    assert (k % d) == 0
    e = k//d
    u0 = ZZ(u)
    double_line_ate_cln = 6*me + 7*se + k*m
    mx_add_line_ate_cln = 13*me + 3*se + k*m

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    hw_neg_u = sum([1 for bi in bits_2naf_u0 if bi == -1])

    cost_ate_cln = (u0.nbits()-1)*(double_line_ate_cln+sk+mk) -sk -mk + (hw_u-1)*(mx_add_line_ate_cln+mk)
    cost_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln+sk+mk) -sk -mk + hw_neg_u*ik_cyclo + (hw2naf_u-1)*(mx_add_line_ate_cln+mk)
    # I think there is another extra cost when the bit is -1
    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    print("cost ate Miller       = {}m (Costello Lange Naehrig)".format(cost_ate_cln))
    print("cost ate Miller 2-naf = {}m (Costello Lange Naehrig)".format(cost_ate_cln_2naf))
    print("({0}-1)*(6*m{2}+7*s{2}+k*m +sk+mk) -sk-mk + ({1}-1)*(13*m{2}+3*s{2}+k*m +mk)".format(u0.nbits(), hw_u, e))
    print("({0}-1)*(6*m{2}+7*s{2}+k*m +sk+mk) -sk-mk + ({1}-1)*(13*m{2}+3*s{2}+k*m +mk) + ({3})*({4})".format(len(bits_2naf_u0), hw2naf_u, e, hw_neg_u, ik_cyclo))
    min_cost_miller = min(cost_ate_cln, cost_ate_cln_2naf)
    return min_cost_miller

def cost_pairing_bls15(u):
    """
    The k=15 extension is built as a degree 3 extension on top of a degree 5 extension
    The arithmetic cost over GF(p^5) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M5 = 13*m and because the formulas are symmetric in the variables a_i, b_i,
    S5 = 13*s
    """
    # cost
    # a=0 E: y^2 = x^3 + b
    k = 15
    d = 3
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    # no cyclotomic squaring
    m5 = 13*m
    s5 = 13*s
    f5 = 4*m
    m15 = 6*m5
    s15 = 2*m5 + 3*s5
    s15_cyclo = s15 # no better formula known
    f15 = (k-1)*m
    # f^q, f^(q^2) where q=p^5, in GF(p^15)
    # there is a better way than (k-1)*m
    # f = f0 + f1*alpha + f2*alpha^2 where fi in GF(p^5)
    # f^q = f0^q + f1^q*alpha^q + f2^q*alpha^2^q but fi^q = fi as fi in GF(p^5) = GF(q)
    # f^q = f0 + f1*alpha^q + f2*alpha^2^q
    # alpha^3 = residue in GF(p^5)
    # (alpha^3)^((q-1)/3) * alpha = residue^((q-1)/3) * alpha
    # = residue^((p-1)/3*(1+p^2+p^3+p^4)) * alpha
    # = (Norm_{GF(p^5)/GF(p)}(residue))^((p-1)/3) * alpha
    # = omega * alpha where omega is one of the two primitive 3-rd roots of unity in GF(p)
    #                       as p = 1 mod 3
    f15_10 = 10*m
    f15_5 = 10*m
    i5 = 48*m + inv # Masson PhD thesis page ix
    assert i5 == 3*f5 + 2*m5 + 10*m + inv
    i15 = 9*m5 + 3*s5 + i5
    i15_cyclo = f15_10 + f15_5 + m15 # inversion in cyclotomic subgroup
    me=m5; se=s5; mk = m15; sk=s15; sk_cyclo = s15_cyclo; fk = f15; ik = i15; ik_cyclo = i15_cyclo # e = k/d with d=3
    u0 = ZZ(u)
    min_cost_miller = cost_miller_loop_bls_k_odd(u0, k, m, me, se, mk, sk, ik_cyclo)

    # final exponentiation - Version 1
    # From Daiki Hayashida, Kenichiro Hayasaka, and Tadanori Teruya: https://eprint.iacr.org/2020/875
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    easy_exp = ((x**15 - 1) // cyclotomic_polynomial(15))
    assert easy_exp == (x**7 + x**6 + x**5 - x**2 - x - 1)
    assert easy_exp == (x**5 - 1) * (x**2 + x + 1)
    px = (x**12 - 2*x**11 + x**10 + x**7 - 2*x**6 + x**5 + x**2 + x + 1)/3
    rx = x**8 - x**7 + x**5 - x**4 + x**3 - x + 1

    l0 = x**7 - x**6 + x**4 - x**3 + x**2 - 1
    l1 = x**6 - x**5 + x**3 - x**2 + x
    l2 = x**5 - x**4 + x**2 - x + 1
    l3 = x**4 - x**3 + x - 1
    l4 = x**3 - x**2 + 1
    l5 = x**2 - x
    l6 = x - 1
    l7 = 1

    assert l6 == x*l7 - 1
    assert l5 == x*l6
    assert l4 == x*l5 + 1
    assert l3 == x*l4 - 1
    assert l2 == x*l3 + 1
    assert l1 == x*l2
    assert l0 == x*l1 - 1

    e = ((x - 1)//3)*(x**3 - 1)

    exponent = cyclotomic_polynomial(15)(px)//rx
    assert e*(l0 + px*(l1 + px*(l2 + px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*l7))))))) + 1 == exponent

    # easy part: exponent = (p**5 - 1) * (p**2 + p + 1)
    # 1 Frobenius(5) + 2 Frobenius, 1 inversion, 3 multiplications
    easy_part = f15_5 + 2*f15 + 1*i15 + 3*m15
    # hard part
    # cost exp(u-1) + exp(u^3-1) + 7 exp(u) + 7 frob + 14 M + S + inv_cyclo
    u1 = abs(u - 1)
    cost_exp_to_u1 = GMT_cost_exp(u1, s15, m15)
    u3 = abs(u**3 - 1)
    cost_exp_to_u = GMT_cost_exp(abs(u), s15, m15)
    cost_exp_to_u3 = min(3*cost_exp_to_u + i15_cyclo + m15, GMT_cost_exp(u3, s15, m15))

    if (u > 0):
        hard_part_v1 = cost_exp_to_u1 + cost_exp_to_u3 + 7*cost_exp_to_u + 14*m15 + s15 + 7*f15 + i15_cyclo
    else:# in the worst case it consists in inverting u each time
        hard_part_v1 = cost_exp_to_u1 + cost_exp_to_u3 + 7*cost_exp_to_u + 14*m15 + s15 + 7*f15 + i15_cyclo + 7*i15_cyclo

    print("cost final exp easy: {}m".format(easy_part))
    print("cost final exp hard: {}m (for new curve)".format(hard_part_v1))
    print("cost final exp: (total){}m".format(easy_part + hard_part_v1))
    print("\ncost pairing (total) {}m".format(easy_part + hard_part_v1 + min_cost_miller))

def cost_pairing_bls21(u):
    """
    The k=21 extension is built as a degree 3 extension on top of a degree 7 extension
    The arithmetic cost over GF(p^7) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M7 = 22*m and because the formulas are symmetric in the variables a_i, b_i,
    S7 = 22*s
    """
    # cost
    # a=0 E: y^2 = x^3 + b
    k = 21
    d = 3
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    # no cyclotomic squaring
    m7 = 22*m
    s7 = 22*s
    f7 = 6*m
    m21 = 6*m7
    s21 = 2*m7 + 3*s7
    s21_cyclo = s21 # no better formula known
    f21 = (k-1)*m
    # f^q, f^(q^2) where q=p^7, in GF(p^21)
    # there is a better way than (k-1)*m
    # f = f0 + f1*alpha + f2*alpha^2 where fi in GF(p^7)
    # f^q = f0^q + f1^q*alpha^q + f2^q*alpha^2^q but fi^q = fi as fi in GF(p^7) = GF(q)
    # f^q = f0 + f1*alpha^q + f2*alpha^2^q
    # alpha^3 = residue in GF(p^7)
    # (alpha^3)^((q-1)/3) * alpha = residue^((q-1)/3) * alpha
    # = residue^((p-1)/3*(1+p^2+p^3+p^4+p^5+p^6)) * alpha
    # = (Norm_{GF(p^7)/GF(p)}(residue))^((p-1)/3) * alpha
    # = omega * alpha where omega is one of the two primitive 3-rd roots of unity in GF(p)
    #                       as p = 1 mod 3
    f21_14 = 14*m
    f21_7 = 14*m
    i7 = 104*m + inv # Masson PhD thesis page ix
    i21 = 9*m7 + 3*s7 + i7
    i21_cyclo = f21_14 + f21_7 + m21 # inversion in cyclotomic subgroup
    me=m7; se=s7; mk = m21; sk=s21; sk_cyclo = s21_cyclo; fk = f21; ik = i21; ik_cyclo = i21_cyclo # e = k/d with d=3
    u0 = ZZ(u)
    min_cost_miller = cost_miller_loop_bls_k_odd(u0, k, m, me, se, mk, sk, ik_cyclo)
    
    # final exponentiation - Version 1
    # From Daiki Hayashida, Kenichiro Hayasaka, and Tadanori Teruya: https://eprint.iacr.org/2020/875
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**21 - 1) // cyclotomic_polynomial(21)) == (x**9 + x**8 + x**7 - x**2 - x - 1)
    px = (x**16 - 2*x**15 + x**14 + x**9 - 2*x**8 + x**7 + x**2 + x + 1)/3
    rx = x**12 - x**11 + x**9 - x**8 + x**6 - x**4 + x**3 - x + 1

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
    e = ((x - 1)//3)*(x**3 - 1)

    exponent = (px**12 - px**11 + px**9 - px**8 + px**6 - px**4 + px**3 - px + 1)//rx
    assert e*(l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*(l7 + px*(l8 + px*(l9 + px*(l10 + px*l11))))))))))) + 1 == exponent

    # cost :
    # hard part:
    # 1 exponentiations by |u-1|/3, 1 exponentiation by |u^3 - 1|, 1 exponentiation byt (u - 1), 10 exponentiations by u,
    # 18 multiplications, 11 Frobenius, 1 inversions in Fp21.
    # easy part: exponent = (px**7 - 1) * (p**2 + p + 1)
    # 3 Frobenius, 1 inversion, 3 multiplications
    easy_part = 3*f21 + 1*i21 + 3*m21
    u1 = abs((u - 1)//3)
    cost_exp_to_u1 = GMT_cost_exp(u1, s21, m21)
    u3 = abs(u**3 - 1)
    cost_exp_to_u3 = GMT_cost_exp(u3, s21, m21)
    cost_exp_to_u_1 = GMT_cost_exp(abs(u-1), s21, m21)
    cost_exp_to_u = GMT_cost_exp(abs(u), s21, m21)
    
    if (u >0):
        hard_part_v1 = 1*cost_exp_to_u1 + 1*cost_exp_to_u3 + 1*cost_exp_to_u_1 + (10*cost_exp_to_u) + 18*m21 + 1*i21_cyclo + 11*f21
    else:
        hard_part_v1 = 1*cost_exp_to_u1 + 1*cost_exp_to_u3 + 1*cost_exp_to_u_1 + (10*cost_exp_to_u) + 18*m21 + 11*i21_cyclo + 11*f21

    # final exponentiation - Version 2
    # (p^16-1)/r = (p^8-1)/Phi_16(u) * Phi_16(u)/r = (p^8-1)*(p^8+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**21 - 1) // cyclotomic_polynomial(21)) == (x**9 + x**8 + x**7 - x**2 - x - 1)
    px = (x**16 - 2*x**15 + x**14 + x**9 - 2*x**8 + x**7 + x**2 + x + 1)/3
    rx = x**12 - x**11 + x**9 - x**8 + x**6 - x**4 + x**3 - x + 1

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

    exponent = (px**12 - px**11 + px**9 - px**8 + px**6 - px**4 + px**3 - px + 1)//rx
    assert e*(l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*(l7 + px*(l8 + px*(l9 + px*(l10 + px*l11))))))))))) + 3 == 3*exponent

    # cost :
    # hard part:
    # 15 exponentiations by |u|, 23 multiplications, 1 squaring, 11 Frobenius, 2 inversions in Fp21.
    # easy part: exponent = (px**7 - 1) * (p**2 + p + 1)
    # 3 Frobenius, 1 inversion, 3 multiplications
    easy_part = 3*f21 + 1*i21 + 3*m21
    cost_exp_to_x = GMT_cost_exp(u0, s21, m21)
    hard_part_v2 = (15*cost_exp_to_x) + 23*m21 + 1*s21 + 2*i21_cyclo + 11*f21

    min_cost_hard_part = min(hard_part_v1, hard_part_v2)

    print("cost final exp easy: {}m".format(easy_part))
    print("cost final exp v1 hard: {}m (for new curve)".format(hard_part_v1))
    print("cost final exp v2 hard: {}m (for new curve)".format(hard_part_v2))
    print("cost final exp: (total){}m".format(easy_part + min_cost_hard_part))
    print("\ncost pairing (total) {}m".format(easy_part + min_cost_hard_part + min_cost_miller))

def cost_pairing_bls27(u):
    """
    The k=27 extension is built as three degree 3 extensions on top of GF(p)
    """
    # cost
    # a=0 E: y^2 = x^3 + b
    k = 27
    d = 3
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    m3 = 6*m
    s3 = 2*m+3*s
    m9 = 6*m3
    s9 = 2*m3+3*s3
    m27 = 6*m9
    s27 = 2*m9+3*s9
    s27_cyclo = s27 # no formula
    i3 = 9*m + 3*s + inv
    i9 = 9*m3 + 3*s3 + i3
    i27 = 9*m9 + 3*s9 + i9
    f27 = (k-1)*m
    f27_9 = 2*(k//3)*m
    f27_18 = 2*(k//3)*m
    i27_cyclo = f27_18 + f27_9 + m27 # inversion in cyclotomic subgroup
    me=m9; se=s9; mk=m27; sk=s27; sk_cyclo=s27_cyclo; fk=f27; ik=i27; ik_cyclo=i27_cyclo

    u0 = ZZ(u)
    min_cost_miller = cost_miller_loop_bls_k_odd(u0, k, m, me, se, mk, sk, ik_cyclo)

    # final exponentiation - Version 1
    # From Zhang and Lin INDOCRYPT'2012 Section 4.3
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**27 - 1) // cyclotomic_polynomial(27)) == (x**9 - 1)
    px = (x**20 - 2*x**19 + x**18 + x**11 - 2*x**10 + x**9 + x**2 + x + 1)/3

    rx = x**18 + x**9 + 1

    exponent = (px**18 + px**9 + 1)//rx
    assert ((px**8 + x*px**7 + x**2*px**6 + x**3*px**5 + x**4*px**4 + x**5*px**3 + x**6*px**2 + x**7*px + x**8)*(px**9 + x**9 + 1)*(x - 1)**2 + 3) == 3*exponent
    
    u0 = abs(u0)

    # cost :
    # hard part:
    # 17 exponentiations by u, 2 exponentiation by (u - 1), 12 multiplications, 1 squaring, 9 Frobenius in Fp27.
    # if u < 0, 9 cyclotomic inversions in Fp27.
    # easy part: exponent = (px**9 - 1)
    # 1 Frobenius, 1 inversion, 1 multiplications
    easy_part = 1*f27 + 1*i27 + 3*m27
    cost_exp_to_u = GMT_cost_exp(u0, s27, m27)
    cost_exp_to_u_1_minus = GMT_cost_exp(u0-1, s27, m27)
    cost_exp_to_u_1_plus = GMT_cost_exp(u0+1, s27, m27)
    
    if (u > 0):
        hard_part_v1 = 17*cost_exp_to_u + 2*cost_exp_to_u_1_minus + 12*m27 + 1*s27 + 9*f27
    else:
        hard_part_v1 = 17*cost_exp_to_u + 2*cost_exp_to_u_1_minus + 12*m27 + 1*s27 + 9*f27 + 9*i27_cyclo

    # final exponentiation - Version 2
    # Improving Zhang and Lin method for negative seed u

    if (u > 0):
        hard_part_v2 = 17*cost_exp_to_u + 2*cost_exp_to_u_1_minus + 12*m27 + 1*s27 + 9*f27
    else:
        hard_part_v2 = 17*cost_exp_to_u + 2*cost_exp_to_u_1_plus + 12*m27 + 1*s27 + 9*f27 + 2*i27_cyclo

    # final exponentiation - Version 3
    # From Daiki Hayashida, Kenichiro Hayasaka, and Tadanori Teruya: https://eprint.iacr.org/2020/875
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**27 - 1) // cyclotomic_polynomial(27)) == (x**9 - 1)
    px = (x**20 - 2*x**19 + x**18 + x**11 - 2*x**10 + x**9 + x**2 + x + 1)/3

    rx = (x**18 + x**9 + 1)/3

    exponent = (px**18 + px**9 + 1)//rx
    assert ((px**9 + x**9 + 1)*(px**6 + px**3*x**3 + x**6)*(px**2 + px*x + x**2)*(x - 1)**2 + 3) == exponent
    assert ((px**9 + x**9 + 1)*(px**6 + (px**3 + x**3)*x**3)*(px**2 + (px + x)*x)*(x - 1)**2 + 3) == exponent

    if (u > 0):
        hard_part_v3 = 17*cost_exp_to_u + 2*cost_exp_to_u_1_minus + 8*m27 + 1*s27 + 5*f27
    else:
        hard_part_v3 = 17*cost_exp_to_u + 2*cost_exp_to_u_1_minus + 8*m27 + 1*s27 + 5*f27 + 3*i27_cyclo

    min_cost_hard_part = min(hard_part_v1, hard_part_v2, hard_part_v3)

    print("cost final exp easy: {}m".format(easy_part))
    print("cost final exp v1 hard: {}m (for new curve)".format(hard_part_v1))
    print("cost final exp v2 hard: {}m (for new curve)".format(hard_part_v2))
    print("cost final exp v3 hard: {}m (for new curve)".format(hard_part_v3))

    print("cost final exp (total): {}m".format(easy_part + min_cost_hard_part))
    print("\ncost pairing (total) {}m".format(easy_part + min_cost_hard_part + min_cost_miller))

def cost_pairing_fm15(u):
    """
    Fotiadis Martindale curves #22 in eprint 2019/555
    The k=15 extension is built as a degree 3 extension on top of a degree 5 extension
    The arithmetic cost over GF(p^5) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M5 = 13*m and because the formulas are symmetric in the variables a_i, b_i,
    S5 = 13*s
    """
    # cost
    # a=0 E: y^2 = x^3 + b
    k = 15
    d = 3
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    # no cyclotomic squaring
    m5 = 13*m
    s5 = 13*s
    f5 = 4*m
    m15 = 6*m5
    s15 = 2*m5 + 3*s5
    s15_cyclo = s15 # no better formula known
    f15 = (k-1)*m
    # f^q, f^(q^2) where q=p^5, in GF(p^15)
    # there is a better way than (k-1)*m
    # f = f0 + f1*alpha + f2*alpha^2 where fi in GF(p^5)
    # f^q = f0^q + f1^q*alpha^q + f2^q*alpha^2^q but fi^q = fi as fi in GF(p^5) = GF(q)
    # f^q = f0 + f1*alpha^q + f2*alpha^2^q
    # alpha^3 = residue in GF(p^5)
    # (alpha^3)^((q-1)/3) * alpha = residue^((q-1)/3) * alpha
    # = residue^((p-1)/3*(1+p^2+p^3+p^4)) * alpha
    # = (Norm_{GF(p^5)/GF(p)}(residue))^((p-1)/3) * alpha
    # = omega * alpha where omega is one of the two primitive 3-rd roots of unity in GF(p)
    #                       as p = 1 mod 3
    f15_10 = 10*m
    f15_5 = 10*m
    i5 = 48*m + inv # Masson PhD thesis page ix
    assert i5 == 3*f5 + 2*m5 + 10*m + inv
    i15 = 9*m5 + 3*s5 + i5
    i15_cyclo = f15_10 + f15_5 + m15 # inversion in cyclotomic subgroup
    me=m5; se=s5; mk = m15; sk=s15; sk_cyclo = s15_cyclo; fk = f15; ik = i15; ik_cyclo = i15_cyclo # e = k/d with d=3
    u0 = ZZ(u)
    min_cost_miller = cost_miller_loop_bls_k_odd(u0, k, m, me, se, mk, sk, ik_cyclo)

    # final exponentiation - Version 1
    # From Daiki Hayashida, Kenichiro Hayasaka, and Tadanori Teruya: https://eprint.iacr.org/2020/875
    # not sure it could work as the degree of the trace is high
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    easy_exp = ((x**15 - 1) // cyclotomic_polynomial(15))
    assert easy_exp == (x**7 + x**6 + x**5 - x**2 - x - 1)
    assert easy_exp == (x**5 - 1) * (x**2 + x + 1)
    px = (3*x**16 - 3*x**15 - 2*x**14 + 4*x**13 - 4*x**12 + 3*x**11 + 4*x**10 - 9*x**9 + 7*x**8 - 4*x**6 + 7*x**5 - 2*x**4 + 3*x**2 - 3*x + 3)/3
    rx = x**8 - x**7 + x**5 - x**4 + x**3 - x + 1

    # easy part: exponent = (p**5 - 1) * (p**2 + p + 1)
    # 1 Frobenius(5) + 2 Frobenius, 1 inversion, 3 multiplications
    easy_part = f15_5 + 2*f15 + 1*i15 + 3*m15
    
    # hard part
    l0 =  3*x + 3*x**2 + 3*x**3 - 3*x**4 + 3*x**5 - 2*x**7 + 4*x**8 - x**9 + 2*x**11 - 5*x**12 + 3*x**14
    l1 = -3*x - 3*x**2 - 3*x**3 - 3*x**7 - 3*x**9 + 2*x**11 + x**12 + 2*x**13 - 3*x**15
    l2 = -3*x**3 - 3*x**5 + 2*x**7 + x**8 + 2*x**9 - 3*x**11
    l3 = -3 + 3*x + 3*x**2 + 3*x**3 + 5*x**4 + x**5 + 2*x**7 - 5*x**8 + 3*x**9 + 3*x**10 - 2*x**11 - x**12 - 2*x**13 + 3*x**15
    l4 = 6 - 3*x**3 - 2*x**4 + 2*x**5 - 2*x**6 + 3*x**8 - 5*x**9 - x**10 + x**12 + 5*x**13 - 3*x**15
    l5 = -3 - 3*x**4 - 3*x**6 + 2*x**8 + x**9 + 2*x**10 - 3*x**12
    l6 = -3 - 3*x**2 + 2*x**4 + x**5 + 2*x**6 - 3*x**8
    l7 = 3 + 3*x + 3*x**4 - 5*x**5 + 2*x**6 - x**8 + 4*x**9 - 2*x**10 - 3*x**11 + 3*x**12

    assert l2 == l6*x**3
    assert l5 == l6*x**4 - 3
    assert l7 == (3 + l6*x**3) - (l6*x + l6*x**4)
    assert l0 == (l6*x**4 + 3*x**2 + 3*x) - (l6*x**6 + l6*x**3)
    assert l1 == l6*x**7 - (3*x**3 + 3*x**2 + 3*x)
    assert l3 == (l6 + 3*x**3 + 3*x**2 + 3*x) - (l6*x**7 + l6*x**2)
    assert l4 == (3 + l6*x**7) - (3*x**3 + 3*x**2 + l6 + l6*x**5)

    e = 3*x*(x**3 - x**2 + 1)

    exponent = cyclotomic_polynomial(15)(px)//rx
    assert (l0 + px*(l1 + px*(l2 + px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*l7))))))) == exponent*e

    # cost 15 exp(|u|) + 16 frob + 39 M + 6 S  (if u > 0)
    # cost 15 exp(|u|) + 16 frob + 38 M + 6 S  (if u < 0)
    u1 = abs(u)
    cost_exp_to_u = GMT_cost_exp(u, s15, m15)

    if (u > 0):
        hard_part_v0 = 15*cost_exp_to_u + 37*m15 + 6*s15 + 11*f15 + 2*f15_5 + 2*i15_cyclo
    else:# in the worst case it consists in inverting u each time
        hard_part_v0 = 15*cost_exp_to_u + 36*m15 + 6*s15 + 11*f15 + 2*f15_5 + 2*i15_cyclo

    print("cost final exp easy: {}m".format(easy_part))
    print("cost final exp hard: {}m (for new curve)".format(hard_part_v0))
    print("cost final exp: (total){}m".format(easy_part + hard_part_v0))
    print("\ncost pairing (total) {}m".format(easy_part + hard_part_v0 + min_cost_miller))

##New curve for k = 16 with square cofactor
def cost_pairing_new16(u0):
    # cost
    # b=0
    m = 1
    s = 1
    m2 = 3*m
    s2 = 2*m
    m4 = 3*m2   # = 9m
    s4 = 2*m2   # = 6m
    m8 = 3*m4   # = 27m
    s8 = 2*m4   # = 18m
    m16 = 3*m8  # = 81m
    s16 = 2*m8  # = 54m
    s16cyclo = 12*m2    # = 36m
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    f16 = 15*m # Ghammam PhD thesis Table 4.12 p. 113
    # INDOCRYPT 2012, Analysis of Optimum Pairing Products at High Security Levels
    # Xusheng Zhang and Dongdai Lin, but no formula provided
    inv = 25*m
    i2 = 2*m + 2*s + inv
    i4 = 2*m2 + 2*s2 + i2
    i8 = 2*m4 + 2*s4 + i4
    i16 = 2*m8 + 2*s8 + i8
    assert i16 == 134*m+inv # cf Guillevic Masson Thome DCC'20

    k = 16
    e = 4
    d = 4
    assert e*d == k
    me=m4; se=s4; mk=m16; sk=s16 # e = k/d
    # Costello Lange Naehrig, with d=4, b=0
    double_line_ate_cln = 2*me+8*se+(k//2)*m
    add_line_ate_cln    = 9*me+5*se+(k//2)*m
    sparse_dense  = 8*me
    sparse_sparse = 6*me
    update1       = 8*me+sk # 1 sparse multiplication + 1 squaring in Fpk
    update2       = 8*me    # in other words, a sparse multiplication costs 8 m4 (8, not 7)

    u0 = ZZ(u0)
    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    # Frobenius(Q) : 2 sparse Frobenius in Fp16 (actually cheaper than 2*f16)
    cost_opt_ate_cln = (u0.nbits()-1)*(double_line_ate_cln +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln+sparse_sparse+mk)
    cost_opt_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln+sparse_sparse+mk)
    min_cost_miller = min(cost_opt_ate_cln, cost_opt_ate_cln_2naf)
#    print("m16 = {}m s16 = {}m".format(m16,s16))
#    print("m4 = {}m s4 = {}m".format(m4,s4))
    #print("cost ate Miller = {}m".format(cost_ate))
    print("cost opt ate Miller = {}m (Costello Lange Naehrig)".format(cost_opt_ate_cln))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m +sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m +6*m{2}+mk)".format(u0.nbits(),hw_u,e))
    print("cost opt ate Miller = {}m (2-naf, Costello Lange Naehrig)".format(cost_opt_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m +sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m +6*m{2}+mk)".format(len(bits_2naf_u0),hw2naf_u,e))
    
    # final exponentiation
    # (p^16-1)/r = (p^8-1)/Phi_16(u) * Phi_16(u)/r = (p^8-1)*(p^8+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**16-1) // cyclotomic_polynomial(16)) == (x**8-1)
    px = (x**16 + 2*x**13 + x**10 + 5*x**8 + 6*x**5 + x**2 + 4)/4
    rx = x**8 + 1

    l0=(x**8 + 2*x**5 + x**2 + 4)
    l1=-(x**11 + 2*x**8 + x**5 + 4*x**3 + 4)
    l2=(x**14 + 2*x**11 + x**8 + 4*x**6 + 4*x**3)
    l3=(x**9 + 2*x**6 + x**3 + 4*x)
    l4=-(x**12 + 2*x**9 + x**6 + 4*x**4 + 4*x)
    l5=(x**15 + 2*x**12 + x**9 + 4*x**7 + 4*x**4)
    l6=(x**10 + 2*x**7 + x**4 + 4*x**2)
    l7=-(x**13 + 2*x**10 + x**7 + 4*x**5 + 4*x**2)

    exponent = (px**8+1)//rx
    assert l0+px*(l1+px*(l2+px*(l3+px*(l4+px*(l5+px*(l6+px*l7)))))) == (-4*x**5)*exponent
    assert (l0)+px*(-(x*x*x*l0 + 4) + px*(-x*x*x*l1 + px*(x*l0 + px*(x*l1+px*(-x*x*x*x*l1+px*(x*x*l0+px*(x*x*l1))))))) == (-4*x**5)*exponent

    # cost :
    # 15 exponentiations by u, 3 squarings, 11 multiplications, 7 Frobenius, 3 inversions in Fp16.
    # easy part: exponent = (px**8-1)
    # f^p8 is free (conjugation)
    # 1 Frobenius, 1 inversion, 1 multiplications
    easy_part = f16 + i16 + m16
    # hard part
    cost_exp_to_x2 = GMT_cost_exp(u0//2, s16cyclo, m16)
    cost_exp_to_x = GMT_cost_exp(u0, s16cyclo, m16)
    hard_part = (13*cost_exp_to_x) + (2*cost_exp_to_x2) + 9*m16 + 4*f16

    print("cost final exp easy: {}m".format(easy_part))
    print("cost final exp hard: {}m (for new curve)".format(hard_part))
    print("cost final exp:      {}m".format(easy_part + hard_part))
    print("\ncost pairing (total) {}m".format(easy_part + hard_part + min_cost_miller))
    
def cost_pairing_new16_765():
    u0 = ZZ(-(2**48 - 2**44 + 2**37))
    cost_pairing_new16(u0)

##Adding FM16 curve from https://eprint.iacr.org/2019/555
def cost_pairing_fm16(u0):
    # cost
    # b=0
    u0 = ZZ(u0)
    m = 1
    s = 1
    m2 = 3*m
    s2 = 2*m
    m4 = 3*m2   # = 9m
    s4 = 2*m2   # = 6m
    m8 = 3*m4   # = 27m
    s8 = 2*m4   # = 18m
    m16 = 3*m8  # = 81m
    s16 = 2*m8  # = 54m
    s16cyclo = 12*m2    # = 36m
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    f16 = 15*m # Ghammam PhD thesis Table 4.12 p. 113
    # INDOCRYPT 2012, Analysis of Optimum Pairing Products at High Security Levels
    # Xusheng Zhang and Dongdai Lin, but no formula provided
    inv = 25*m
    i2 = 2*m + 2*s + inv
    i4 = 2*m2 + 2*s2 + i2
    i8 = 2*m4 + 2*s4 + i4
    i16 = 2*m8 + 2*s8 + i8
    assert i16 == 134*m+inv # cf Guillevic Masson Thome DCC'20

    k = 16
    e = 4
    d = 4
    assert e*d == k
    me=m4; se=s4; mk=m16; sk=s16 # e = k/d
    # Costello Lange Naehrig, with d=4, b=0
    double_line_ate_cln = 2*me+8*se+(k//2)*m
    add_line_ate_cln    = 9*me+5*se+(k//2)*m
    sparse_dense  = 8*me
    sparse_sparse = 6*me
    update1       = 8*me+sk # 1 sparse multiplication + 1 squaring in Fpk
    update2       = 8*me    # in other words, a sparse multiplication costs 8 m4 (8, not 7)

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    # Frobenius(Q) : 2 sparse Frobenius in Fp16 (actually cheaper than 2*f16)
    cost_opt_ate_cln = (u0.nbits()-1)*(double_line_ate_cln +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln+sparse_sparse+mk)
    cost_opt_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln+sparse_sparse+mk)
    min_cost_miller = min(cost_opt_ate_cln, cost_opt_ate_cln_2naf)
#    print("m16 = {}m s16 = {}m".format(m16,s16))
#    print("m4 = {}m s4 = {}m".format(m4,s4))
    #print("cost ate Miller = {}m".format(cost_ate))
    print("cost opt ate Miller = {}m (Costello Lange Naehrig)".format(cost_opt_ate_cln))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m +sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m +6*m{2}+mk)".format(u0.nbits(),hw_u,e))
    print("cost opt ate Miller = {}m (2-naf, Costello Lange Naehrig)".format(cost_opt_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m +sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m +6*m{2}+mk)".format(len(bits_2naf_u0),hw2naf_u,e))
    
    # final exponentiation
    # (p^16-1)/r = (p^8-1)/Phi_16(u) * Phi_16(u)/r = (p^8-1)*(p^8+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**16-1) // cyclotomic_polynomial(16)) == (x**8-1)
    px = (x**16 + x**10 + 5*x**8+ x**2 + 4*x + 4)/4
    rx = x**8 + 1
    
    l0=(4+4*x**7+x**9+x**15)/4
    l1=(4*x**6+x**8+x**14)/4
    l2=(4*x**5+x**7+x**13)/4
    l3=(4*x**4+x**6+x**12)/4
    l4=(4*x**3+x**5+x**11)/4
    l5=(4*x**2+x**4+x**10)/4
    l6=(4*x+x**3+x**9)/4
    l7=(4+x**2+x**8)/4
    
    exponent = (px**8+1)//rx
    assert l0+px*(l1+px*(l2+px*(l3+px*(l4+px*(l5+px*(l6+px*l7)))))) == exponent
    assert (l7*(x*x*x*x*x*x*x)+1)+px*(l7*x*x*x*x*x*x+px*(l7*x*x*x*x*x+px*(l7*x*x*x*x+px*(l7*x*x*x+px*(l7*x*x+px*(l7*x+px*l7)))))) == exponent
    # cost from FM19:
    # 13 exponentiations by u, 2 exponentiations by u/2, 10 multiplications, 7 Frobenius in Fp16.
    # easy part: exponent = (px**8-1)
    # f^p8 is free (conjugation)
    # 1 Frobenius, 1 inversion, 1 multiplications
    easy_part = f16 + i16 + m16
    # hard part
    # exponent = (x/2)
    cost_exp_to_x2 = GMT_cost_exp(u0//2, s16cyclo, m16)
    cost_exp_to_x = GMT_cost_exp(u0, s16cyclo, m16)
    hard_part = (2*cost_exp_to_x2) + (13*cost_exp_to_x) + 6*m16 + 3*f16
    # total 18732 M + 10 I with Karabina compressed squarings
    # 23400 M + I with cyclotomic squaring of Granger-Scott.
    print("cost final exp easy: {}m".format(easy_part))
    print("cost final exp hard: {}m (with Fotiadis-Martindale technique)".format(hard_part))
    print("cost final exp:      {}m".format(easy_part + hard_part))
    print("\ncost pairing (total) {}m".format(easy_part + hard_part + min_cost_miller))

def cost_pairing_fm16_766():
    u0 = ZZ(2**48 + 2**28 + 2**26)
    cost_pairing_fm16(u0)
##

def GMT_cost_exp(u0, scyclo, mk):
    """
    TO BE UPDATES
    Karabina cost of compressed squaring
    https://www.ams.org/journals/mcom/2013-82-281/S0025-5718-2012-02625-1/
    mk = multiplication in Fpk
    mkd = multiplication in F_{p^{k/d}}
    skd = squaring in F_{p^{k/d}}
    ikd = inversion in F_{p^{k/d}}
    """
    bits_u0 = (abs(u0)).digits(2)
    len_u = len(bits_u0)
    hw_u = sum(bits_u0)
    bits_2naf_u0 = bits_2naf(abs(u0))
    len2naf_u = len(bits_2naf_u0)
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    cost_exp_to_u = (len_u-1)*scyclo + (hw_u - 1)*mk
    cost_exp_to_u_2naf = (len2naf_u-1)*scyclo + (hw2naf_u - 1)*mk
    return min(cost_exp_to_u, cost_exp_to_u_2naf)

def karabina_cost_exp(u0, mk, mkd, skd, ikd):
    """ Karabina cost of compressed squaring
    https://www.ams.org/journals/mcom/2013-82-281/S0025-5718-2012-02625-1/
    mk = multiplication in Fpk
    mkd = multiplication in F_{p^{k/d}}
    skd = squaring in F_{p^{k/d}}
    ikd = inversion in F_{p^{k/d}}
    """
    bits_u0 = (abs(u0)).digits(2)
    len_u = len(bits_u0)
    hw_u = sum(bits_u0)
    bits_2naf_u0 = bits_2naf(abs(u0))
    len2naf_u = len(bits_2naf_u0)
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    cost_exp_to_u = 4*(len_u-1)*mkd + (6*(hw_u - 1) -3)*mkd + (hw_u - 1)*mk + 3*(hw_u - 1)*skd + ikd
    cost_exp_to_u_2naf = 4*(len2naf_u-1)*mkd + (6*(hw2naf_u - 1) -3)*mkd + (hw2naf_u - 1)*mk + 3*(hw2naf_u - 1)*skd + ikd
    return min(cost_exp_to_u, cost_exp_to_u_2naf)

def cost_pairing_kss16(u0):
    # cost
    # b=0
    u0 = ZZ(u0)
    m = 1
    s = 1
    m2 = 3*m
    s2 = 2*m
    m4 = 3*m2   # = 9m
    s4 = 2*m2   # = 6m
    m8 = 3*m4   # = 27m
    s8 = 2*m4   # = 18m
    m16 = 3*m8  # = 81m
    s16 = 2*m8  # = 54m
    # s16_cyclo = 4*m4 # m4=9*m
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    s16_cyclo = 2*s8 # = 4*m4 indeed
    f16 = 14*m # Ghammam PhD thesis Table 4.12 p. 113 says 15*m but I don't see why it cannot be 14*m
    f16_4 = 8*m # specific case
    c16_cyclo = s16_cyclo + m16 #8*m4 # cube, to check: s16_cyclo + m16 = 4*m4 + 9*m4, so where is 8*m4 it from?
    # INDOCRYPT 2012, Analysis of Optimum Pairing Products at High Security Levels
    # Xusheng Zhang and Dongdai Lin, but no formula provided
    inv = 25*m
    i2 = 2*m + 2*s + inv
    i4 = 2*m2 + 2*s2 + i2
    i8 = 2*m4 + 2*s4 + i4
    i16 = 2*m8 + 2*s8 + i8
    assert i16 == 134*m+inv # cf Guillevic Masson Thome DCC'20
    k = 16
    e = 4
    d = 4
    assert e*d == k
    me=m4; se=s4; mk=m16; sk=s16 # e = k/d
    # Costello Lange Naehrig, with d=4, b=0
    double_line_ate_cln = 2*me+8*se+(k//2)*m
    add_line_ate_cln    = 9*me+5*se+(k//2)*m
    sparse_dense  = 8*me
    sparse_sparse = 6*me
    update1       = 8*me+sk
    update2       = 8*me    # in other words, a sparse multiplication costs 8 m4 (8, not 7)

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    # cost_ate = (u0.nbits()-1)*(double_line_ate +sk) - sk + (u0.nbits()-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate+sparse_sparse+mk)
    # Frobenius(Q) : 2 sparse Frobenius in Fp16 (actually cheaper than 2*f16)
    additional_terms = 2*f16 + add_line_ate_cln + double_line_ate_cln + 2*m16 + f16
    cost_opt_ate_cln = (u0.nbits()-1)*(double_line_ate_cln +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln+sparse_sparse+mk) + additional_terms
    cost_opt_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln+sparse_sparse+mk) + additional_terms
    min_cost_miller = min(cost_opt_ate_cln, cost_opt_ate_cln_2naf)
    print("m16 = {}m s16 = {}m".format(m16,s16))
    print("m4 = {}m s4 = {}m".format(m4,s4))
    #print("cost ate Miller = {}m".format(cost_ate))
    print("cost opt ate Miller = {}m (Costello Lange Naehrig)".format(cost_opt_ate_cln))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m +sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m +6*m{2}+mk)".format(u0.nbits(),hw_u,e))
    print("cost opt ate Miller = {}m (2-naf, Costello Lange Naehrig)".format(cost_opt_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m +sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m +6*m{2}+mk)".format(len(bits_2naf_u0),hw2naf_u,e))

    # final exponentiation
    # (p^16-1)/r = (p^16-1)/Phi_16(u) * Phi_16(u)/r = (p^8-1)*(p^8+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**16-1) // cyclotomic_polynomial(16)) == (x**8-1)

    px = (x**10 + 2*x**9 + 5*x**8 + 48*x**6 + 152*x**5 + 240*x**4 + 625*x**2 + 2398*x + 3125)/980
    rx = (x**8 + 48*x**4 + 625)/61250 # 625 = 5^4, 61250 = 2*5^4*7^2
    tx = (2*x**5 + 41*x + 35)/35
    cx = 125 * (x**2 + 2*x + 5)/2 # C such that P+1-T = C*R
    yx = (x**5 + 5*x**4 + 38*x + 120)/70 # Y such that T^2 - 4*P = -4*Y^2
    betax = (x**9-11*x**8-16*x**7-120*x**6-32*x**5-498*x**4-748*x**3-2740*x**2-3115*x-5651)/4018
    lambx = (x**4 + 24)/7 # sqrt(-1) mod R
    k = 16
    D = 1
    exponent = (px**8+1)//rx
    # easy part: px**8 - 1
    easy_part = i16 + m16
    # hard part: (px**8+1) // rx
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*s16_cyclo + (hw_u-1)*m16
    # exponentiation to the power u+1
    hw_u1 = sum((abs(u0+1)).digits(2))
    exp_u1 = ((u0+1).nbits()-1)*s16_cyclo + (hw_u1-1)*m16
    hard_part_main = 7*exp_u + 2*exp_u1
    # formula from Ghammam
    hard_part_ghammam = hard_part_main + 34*s16_cyclo + 32*m16 + 7*f16 + 3*c16_cyclo
    hard_part_v2 = 9*exp_u + 34*s16_cyclo + 34*m16 + 13*f16
    hard_part_v3 = hard_part_main + 29*s16_cyclo + 30*m16 + 10*f16_4 + 4*f16
    hard_part_v4 = hard_part_main + 30*s16_cyclo + 32*m16 + 7*f16_4 + 6*f16

    exp_u_2naf = (len(bits_2naf_u0)-1)*s16_cyclo + (hw2naf_u-1)*m16
    bits_2naf_u01 = bits_2naf(abs(u0+1))
    hw2naf_u1 = sum([1 for bi in bits_2naf_u01 if bi != 0])
    exp_u1_2naf = (len(bits_2naf_u01)-1)*s16_cyclo + (hw2naf_u1-1)*m16
    hard_part_main_2naf = 7*exp_u_2naf + 2*exp_u1_2naf
    hard_part_2naf_ghammam = hard_part_main_2naf + 34*s16_cyclo + 32*m16 + 7*f16 + 3*c16_cyclo
    hard_part_2naf_v2 = 9*exp_u_2naf + 34*s16_cyclo + 34*m16 + 13*f16
    hard_part_2naf_v3 = hard_part_main_2naf + 29*s16_cyclo + 30*m16 + 10*f16_4 + 4*f16
    hard_part_2naf_v4 = hard_part_main_2naf + 30*s16_cyclo + 32*m16 + 7*f16_4 + 6*f16

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (Ghammam, with cyclotomic squarings)".format(hard_part_ghammam))
    print("cost final exp hard:  {}m (Ghammam, 2-naf with cyclotomic squarings)".format(hard_part_2naf_ghammam))
    print("cost final exp hard:  {}m (v2, with cyclotomic squarings)".format(hard_part_v2))
    print("cost final exp hard:  {}m (v2, 2-naf with cyclotomic squarings)".format(hard_part_2naf_v2))
    print("cost final exp hard:  {}m (v3, with cyclotomic squarings)".format(hard_part_v3))
    print("cost final exp hard:  {}m (v3, 2-naf with cyclotomic squarings)".format(hard_part_2naf_v3))
    print("cost final exp hard:  {}m (v4, with cyclotomic squarings)".format(hard_part_v4))
    print("cost final exp hard:  {}m (v4, 2-naf with cyclotomic squarings)".format(hard_part_2naf_v4))
    hard_part = min(hard_part_ghammam, hard_part_v2, hard_part_v3, hard_part_v4)
    hard_part_2naf = min(hard_part_2naf_ghammam, hard_part_2naf_v2, hard_part_2naf_v3, hard_part_2naf_v4)
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

    print("new formula")
    # implemented in pairing_kss16.py
    # new formula     # total cost 33 S + 31 M + 2 exp(u+1) + 7 exp(u) + 14*f16 + 8 inv_frob_8
    hard_part = 7*exp_u + 2*exp_u1 + 33*s16_cyclo + 31*m16 + 14*f16
    hard_part_2naf = 7*exp_u_2naf + 2*exp_u1_2naf + 33*s16_cyclo + 31*m16 + 14*f16
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

##Adding FM18 curve from https://eprint.iacr.org/2019/555
def cost_pairing_fm18(u0):
    # extension: Fp - Fp3 - Fp9 - Fp18
    # a=0
    # AKLGL'11
    # there are three formulas in https://www.lirmm.fr/arith18/papers/Chung-Squaring.pdf for squaring in cubic extensions
    # S3 = m + 4*s; S3 = 2*m+3*s; S3 = 3*m+2*s
    v0 = ZZ(abs((u0 - 1) // 3))
    w0 = ZZ(abs(u0-1))
    z0 = ZZ(abs(u0+1))
    u0 = ZZ(abs(u0))

    m = 1
    s = 1
    m3 = 6*m
    s3 = 2*m+3*s    # = 5m
    m9 = 6*m3       # = 36m
    s9 = 2*m3+3*s3  # = 27m
    m18 = 3*m9      # = 108m
    s18 = 2*m9      # = 72m
    s18_cyclo = 6*m3    # = 36m
    f18 = 16*m # to check
    inv = 25*m
    i3 = 9*m + 3*s + inv    # = 37m
    i9 = 9*m3 + 3*s3 + i3   # = 106m
    i6 = 2*m3 + 2*s3 + i3   # = 59m
    m2 = 3*m
    s2 = 2*m
    m6 = 6*m2       # = 18m
    s6 = 2*m2+3*s2  # = 12m

    i18 = min(2*m9 + 2*s9 + i9, 9*m6 + 3*s6 + i6) # 213+inv, 232 + inv
    i18_cyclo = 0 # Frobenius power p^9 is only conjugation
    k = 18
    d = 6
    k_d = k//d
    me=m3 ; se=s3; mk=m18; sk=s18 # e = k/d
    double_line_ate = 3*me+6*se+(k//3)*m
    add_line_ate    = 11*me+2*se+(k//3)*m
    add_line_ate_with_z = 11*me+2*se+(k//3)*m + 5*me # +5*me seems the upper bound
    # Costello Lange Naehrig
    # double_line_ate_cln = 3*me+5*se+(k//3)*m    ???
    double_line_ate_cln = 2*me+7*se+(k//3)*m
    add_line_ate_cln    = 10*me+2*se+(k//3)*m
    add_line_ate_with_z_cln = 14*me+2*se+(k//3)*m
    sparse_dense  = 13*me
    sparse_sparse = 6*me
    update1       = 13*me+sk
    update2       = 13*me

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    hw_v = sum((abs(v0)).digits(2))
    bits_2naf_v0 = bits_2naf(abs(v0))
    hw2naf_v = sum([1 for bi in bits_2naf_v0 if bi != 0])
    hw_w = sum((abs(w0)).digits(2))
    bits_2naf_w0 = bits_2naf(abs(w0))
    hw2naf_w = sum([1 for bi in bits_2naf_w0 if bi != 0])
    hw_z = sum((abs(z0)).digits(2))
    bits_2naf_z0 = bits_2naf(abs(z0))
    hw2naf_z = sum([1 for bi in bits_2naf_z0 if bi != 0])
    
    cost_ate = (u0.nbits()-1)*(double_line_ate +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate+sparse_sparse+mk)
    cost_ate_2naf = (len(bits_2naf_u0)-1)*(double_line_ate +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate+sparse_sparse+mk)
    cost_ate_cln = (u0.nbits()-1)*(double_line_ate_cln +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln+sparse_sparse+mk)
    cost_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln+sparse_sparse+mk)

    print("m18 = {}m s18 = {}m".format(m18,s18))
    print("m9 = {}m s9 = {}m".format(m9,s9))
    print("m3 = {}m s3 = {}m".format(m3,s3))
    print("cost ate Miller       = {}m".format(cost_ate))
    print("cost ate Miller 2-naf = {}m".format(cost_ate_2naf))

    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(u0.nbits(), hw_u, k_d))
    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, k_d))
    print("cost ate Miller       = {}m (Costello Lange Naehrig)".format(cost_ate_cln))
    print("cost ate Miller 2-naf = {}m (Costello Lange Naehrig)".format(cost_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(u0.nbits(), hw_u, k_d))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, k_d))
    
    min_cost_miller = min(cost_ate, cost_ate_2naf, cost_ate_cln, cost_ate_cln_2naf)
    
    # final exponentiation
    # (p^18-1)/r = (p^18-1)/Phi_18(u) * Phi_18(u)/r = (p^9-1)*(p^3 + 1) * (p^6-p^3+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**18-1) // cyclotomic_polynomial(18)) == (x**9-1)*(x**3+1)
    px = (3*x**12 - 3*x**9 + x**8 - 2*x**7 + 7*x**6 - x**5 - x**4 - 4*x**3 + x**2 - 2*x + 4)/3
    rx = x**6 - x**3 + 1
    
    # easy part: (px**9 - 1)*(p**3+1)
    # where f^(p^9) is a conjugation and costs nothing
    easy_part = i18 + m18 + f18 + m18
    # exponentiation to the power |u|
    exp_u = (u0.nbits()-1)*s18_cyclo + (hw_u-1)*m18
    exp_u_2naf = (len(bits_2naf_u0)-1)*s18_cyclo + (hw2naf_u-1)*m18
    # exponentiation to the power |(u - 1)/3|
    exp_v = (v0.nbits()-1)*s18_cyclo + (hw_v-1)*m18
    exp_v_2naf = (len(bits_2naf_v0)-1)*s18_cyclo + (hw2naf_v-1)*m18
    # exponentiation to the power |(u - 1)|
    exp_w = (w0.nbits()-1)*s18_cyclo + (hw_w-1)*m18
    exp_w_2naf = (len(bits_2naf_w0)-1)*s18_cyclo + (hw2naf_w-1)*m18
    # exponentiation to the power |(u + 1)|
    exp_z = (z0.nbits()-1)*s18_cyclo + (hw_z-1)*m18
    exp_z_2naf = (len(bits_2naf_z0)-1)*s18_cyclo + (hw2naf_z-1)*m18

    hard_part = 11*exp_u + exp_v + 12*m18 + 5*f18
    hard_part_2naf = 11*exp_u_2naf + exp_v_2naf + 12*m18 + 5*f18

    # 7 exp(|u|) + exp(|u-1|) + exp(|u-1|/3) + 2 exp(|u+1|) + 13 M + 2 S + 4 f + 4 cj
    hard_part_v2 = 7*exp_u + exp_v + exp_w + 2*exp_z + 13*m18 + 2*s18_cyclo + 4*f18
    hard_part_2naf_v2 = 7*exp_u_2naf + exp_v_2naf + exp_w_2naf + 2*exp_z_2naf + 13*m18 + 2*s18_cyclo + 4*f18

    # 11 exp(|u|) + 12 M + 3 S + 4 f + 6 cj
    hard_part_v3 = 11*exp_u + 12*m18 + 3*s18_cyclo + 4*f18
    hard_part_2naf_v3 = 11*exp_u_2naf + 12*m18 + 3*s18_cyclo + 4*f18

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp hard:  {}m v2 (u-1)/3 (with cyclotomic squarings)".format(hard_part_v2))
    print("cost final exp hard:  {}m v2 (u-1)/3 (2-naf with cyclotomic squarings)".format(hard_part_2naf_v2))
    print("cost final exp hard:  {}m v3 3*above (with cyclotomic squarings)".format(hard_part_v3))
    print("cost final exp hard:  {}m v3 3*above (2-naf with cyclotomic squarings)".format(hard_part_2naf_v3))
    print("cost final exp:       {}m".format(easy_part + min(hard_part, hard_part_v2, hard_part_v3)))
    print("cost final exp 2-naf: {}m".format(easy_part + min(hard_part_2naf, hard_part_2naf_v2, hard_part_2naf_v3)))
    print("\ncost pairing (total)  {}m".format(easy_part + min(hard_part, hard_part_v2, hard_part_v3, hard_part_2naf, hard_part_2naf_v2, hard_part_2naf_v3) + min_cost_miller))

def cost_pairing_fm18_769():
    u0 = ZZ(-(2**64 + 2**35 - 2**11 + 1))
    cost_pairing_fm18(u0)
def cost_pairing_fm18_768():
    u0 = ZZ(-2**64+2**33+2**30+2**20+1)
    cost_pairing_fm18(u0)
##

def cost_pairing_sg18(u0):
    u0 = ZZ(abs(u0))

    m = 1
    s = 1
    m3 = 6*m
    s3 = 2*m+3*s    # = 5m
    m9 = 6*m3       # = 36m
    s9 = 2*m3+3*s3  # = 27m
    m18 = 3*m9      # = 108m
    s18 = 2*m9      # = 72m
    s18_cyclo = 6*m3    # = 36m
    f18 = 16*m # to check
    inv = 25*m
    i3 = 9*m + 3*s + inv    # = 37m
    i9 = 9*m3 + 3*s3 + i3   # = 106m
    i6 = 2*m3 + 2*s3 + i3   # = 59m
    m2 = 3*m
    s2 = 2*m
    m6 = 6*m2       # = 18m
    s6 = 2*m2+3*s2  # = 12m

    i18 = min(2*m9 + 2*s9 + i9, 9*m6 + 3*s6 + i6) # 213+inv, 232 + inv
    i18_cyclo = 0 # Frobenius power p^9 is only conjugation
    k = 18
    d = 6
    k_d = k//d
    me=m3 ; se=s3; mk=m18; sk=s18 # e = k/d
    double_line_ate_j = 5*me+5*se+(k//3)*m #doubling using Jacobian coordinates
    double_line_ate = 3*me+6*se+(k//3)*m
    add_line_ate_j = 10*me+7*se #addition using Jacobian coordinates
    add_line_ate    = 11*me+2*se+(k//3)*m
    add_line_ate_with_z = 11*me+2*se+(k//3)*m + 5*me # +5*me seems the upper bound
    # Costello Lange Naehrig
    # double_line_ate_cln = 3*me+5*se+(k//3)*m    ???
    double_line_ate_cln = 2*me+7*se+(k//3)*m
    add_line_ate_cln    = 10*me+2*se+(k//3)*m
    add_line_ate_with_z_cln = 14*me+2*se+(k//3)*m
    sparse_dense  = 13*me
    sparse_sparse = 6*me

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    
    additional_terms = add_line_ate_with_z + 7*f18 + 2*m18
    additional_terms_cln = add_line_ate_with_z_cln + 7*f18 + 2*m18

    cost_ate_j = (u0.nbits()-1)*(double_line_ate_j +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_j+sparse_sparse+mk) + additional_terms
    cost_ate = (u0.nbits()-1)*(double_line_ate +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate+sparse_sparse+mk) + additional_terms
    cost_ate_2naf = (len(bits_2naf_u0)-1)*(double_line_ate +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate+sparse_sparse+mk) + additional_terms
    cost_ate_cln = (u0.nbits()-1)*(double_line_ate_cln +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln+sparse_sparse+mk) + additional_terms_cln
    cost_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln+sparse_sparse+mk) + additional_terms_cln

    print("m18 = {}m s18 = {}m".format(m18,s18))
    print("m9 = {}m s9 = {}m".format(m9,s9))
    print("m3 = {}m s3 = {}m".format(m3,s3))
    print("cost ate Jac Miller   = {}m".format(cost_ate_j))
    print("cost ate Miller       = {}m".format(cost_ate))
    print("cost ate Miller 2-naf = {}m".format(cost_ate_2naf))

    print("({0}-1)*(5*m{2}+5*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+7*s{2}+13*m{2})".format(u0.nbits(), hw_u, k_d))
    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(u0.nbits(), hw_u, k_d))
    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, k_d))
    print("cost ate Miller       = {}m (Costello Lange Naehrig)".format(cost_ate_cln))
    print("cost ate Miller 2-naf = {}m (Costello Lange Naehrig)".format(cost_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(u0.nbits(), hw_u, k_d))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, k_d))

    min_cost_miller = min(cost_ate, cost_ate_2naf, cost_ate_cln, cost_ate_cln_2naf)

    # final exponentiation
    # (p^18-1)/r = (p^18-1)/Phi_18(u) * Phi_18(u)/r = (p^9-1)*(p^3 + 1) * (p^6-p^3+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**18-1) // cyclotomic_polynomial(18)) == (x**9-1)*(x**3+1)
    px = (3*x**12 - 3*x**9 + x**8 - 2*x**7 + 7*x**6 - x**5 - x**4 - 4*x**3 + x**2 - 2*x + 4)/3
    rx = x**6 - x**3 + 1

    # easy part: (px**9 - 1)*(p**3+1)
    easy_part = 2*f18 + i18 + 2*m18
    # exponentiation to the power |u|
    exp_u = (u0.nbits()-1)*s18_cyclo + (hw_u-1)*m18
    exp_u_2naf = (len(bits_2naf_u0)-1)*s18_cyclo + (hw2naf_u-1)*m18

    hard_part = 9*exp_u + 14*m18 + 5*s18 + 5*f18
    hard_part_2naf = 9*exp_u_2naf+ 14*m18 + 5*s18 + 5*f18

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

def cost_pairing_sg18_638():
    u0 = ZZ(-(2**63 + 2**54 + 2**16))
    cost_pairing_sg18(u0)

def cost_pairing_sg18_638b():
    u0 = ZZ(2**63 + 2**46 - 2**9)
    cost_pairing_sg18(u0)

def cost_pairing_kss18(u0):
    # extension: Fp - Fp3 - Fp9 - Fp18
    # a=0
    # AKLGL'11
    # there are three formulas in https://www.lirmm.fr/arith18/papers/Chung-Squaring.pdf for squaring in cubic extensions
    # S3 = m + 4*s; S3 = 2*m+3*s; S3 = 3*m+2*s
    u0 = ZZ(abs(u0))
    m = 1
    s = 1
    m3 = 6*m
    s3 = 2*m+3*s
    m9 = 6*m3
    s9 = 2*m3+3*s3
    m18 = 3*m9
    s18 = 2*m9
    s18_cyclo = 6*m3
    f18 = 16*m # to check
    inv = 25*m
    i3 = 9*m + 3*s + inv
    i9 = 9*m3 + 3*s3 + i3
    i6 = 2*m3 + 2*s3 + i3
    m2 = 3*m
    s2 = 2*m
    m6 = 6*m2
    s6 = 2*m2+3*s2

    i18 = min(2*m9 + 2*s9 + i9, 9*m6 + 3*s6 + i6) # 213+inv, 232 + inv
    i18_cyclo = 0 # Frobenius power p^9 is only conjugation
    print("m18 = {}m s18 = {}m, f18 = {}m, s18cyclo = {}m, i18={}m+i={}m".format(m18, s18, f18, s18_cyclo, i18, i18+inv))
    k = 18

    # AKLGL
    # k=18, d=6, e=k/d = 3
    k = 18
    d = 6
    k_d = k//d
    me=m3 ; se=s3; mk=m18; sk=s18 # e = k/d
    double_line_ate = 3*me+6*se+(k//3)*m
    add_line_ate    = 11*me+2*se+(k//3)*m
    add_line_ate_with_z = 11*me+2*se+(k//3)*m + 5*me # +5*me seems the upper bound
    # Costello Lange Naehrig
    # double_line_ate_cln = 3*me+5*se+(k//3)*m    ???
    double_line_ate_cln = 2*me+7*se+(k//3)*m
    add_line_ate_cln    = 10*me+2*se+(k//3)*m
    add_line_ate_with_z_cln = 14*me+2*se+(k//3)*m
    sparse_dense  = 13*me
    sparse_sparse = 6*me
    update1       = 13*me+sk
    update2       = 13*me

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    additional_terms = double_line_ate + add_line_ate + add_line_ate_with_z + 5*f18 + 3*m18
    additional_terms_cln = double_line_ate_cln + add_line_ate_cln + add_line_ate_with_z_cln + 5*f18 + 3*m18

    cost_ate = (u0.nbits()-1)*(double_line_ate +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate+sparse_sparse+mk) + additional_terms
    cost_ate_2naf = (len(bits_2naf_u0)-1)*(double_line_ate +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate+sparse_sparse+mk) + additional_terms
    cost_ate_cln = (u0.nbits()-1)*(double_line_ate_cln +sk) -sk + (u0.nbits()-2-(hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln+sparse_sparse+mk) + additional_terms_cln
    cost_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln +sk) -sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln+sparse_sparse+mk) + additional_terms_cln
    print("m18 = {}m s18 = {}m".format(m18,s18))
    print("m9 = {}m s9 = {}m".format(m9,s9))
    print("m3 = {}m s3 = {}m".format(m3,s3))
    print("cost ate Miller       = {}m".format(cost_ate))
    print("cost ate Miller 2-naf = {}m".format(cost_ate_2naf))

    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(u0.nbits(), hw_u, k_d))
    print("({0}-1)*(3*m{2}+6*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(11*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, k_d))
    print("cost ate Miller       = {}m (Costello Lange Naehrig)".format(cost_ate_cln))
    print("cost ate Miller 2-naf = {}m (Costello Lange Naehrig)".format(cost_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(u0.nbits(), hw_u, k_d))
    print("({0}-1)*(2*m{2}+7*s{2}+(k//3)*m +sk) -sk + ({0}-2-({1}-1))*(13*m{2}) + ({1}-1)*(10*m{2}+2*s{2}+(k//3)*m +6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, k_d))

    min_cost_miller = min(cost_ate, cost_ate_2naf, cost_ate_cln, cost_ate_cln_2naf)

    # final exponentiation
    # (p^18-1)/r = (p^18-1)/Phi_18(u) * Phi_18(u)/r = (p^9-1)*(p^3 + 1) * (p^6-p^3+1)/r
    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    assert ((x**18-1) // cyclotomic_polynomial(18)) == (x**9-1)*(x**3+1)
    px = (x**8 + 5*x**7 + 7*x**6 + 37*x**5 + 188*x**4 + 259*x**3 + 343*x**2 + 1763*x + 2401)/21
    rx = (x**6 + 37*x**3 + 343)/343 # 343 = 7^3
    # Algorithm 7.6 in Guide to Pairing-based cryptography: 6 S + 53 M + 29 F + 7 exp(u) + 8 F9
    # Variant a la https://eprint.iacr.org/2020/875:       19 S + 26 M + 10 F + 7 exp(u) + 6 F9
    # New variant https://eprint.iacr.org/2021/1309:       11 S + 24 M +  5 F + 7 exp(u) + 7 F9

    # easy part: (px**9 - 1)*(p**3+1)
    easy_part = 2*f18 + i18 + 2*m18
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*s18_cyclo + (hw_u-1)*m18
    exp_u_2naf = (len(bits_2naf_u0)-1)*s18_cyclo + (hw2naf_u-1)*m18

    hard_part = 7*exp_u + 6*s18_cyclo + 53*m18 + 29*f18 + 8 * i18_cyclo
    hard_part_2naf = 7*exp_u_2naf + 6*s18_cyclo + 53*m18 + 29*f18 + 8 * i18_cyclo

    new_hard_part = 7*exp_u + 19*s18_cyclo + 26*m18 + 10*f18 + 6 * i18_cyclo
    new_hard_part_2naf = 7*exp_u_2naf + 19*s18_cyclo + 26*m18 + 10*f18 + 6 * i18_cyclo
    #Cost: 7 exp(u) + 19 S + 26 M + 10 Frobenius powers + 6 Inversions with Frobenius power p^9

    hard_part_2021_1309 = 7*exp_u + 11*s18_cyclo + 24*m18 + 5*f18 + 7 * i18_cyclo
    hard_part_2naf_2021_1309 = 7*exp_u_2naf + 11*s18_cyclo + 24*m18 + 5*f18 + 7 * i18_cyclo

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

    print("\nnew formula a la ePrint 2020/875:")
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(new_hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(new_hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + new_hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + new_hard_part_2naf))
    print("\ncost pairing (total)  {}m".format(easy_part + min(new_hard_part, new_hard_part_2naf) + min_cost_miller))

    print("\nnew formula eprint 2021/1309:")
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part_2021_1309))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf_2021_1309))
    print("cost final exp:       {}m".format(easy_part + hard_part_2021_1309))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf_2021_1309))
    print("\ncost pairing (total)  {}m".format(easy_part + min(hard_part_2021_1309, hard_part_2naf_2021_1309) + min_cost_miller))

def cost_pairing_gg20(u0):
    """
    INPUT:
    - `u0`: curve seed

    The arithmetic cost over GF(p^5) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M5 = 13*m, and because the formulas are symmetric in the variables a_i, b_i,
    S5 = 13*s

    optimal ate Miller loop, gg20a: u - q + 2*q^6
    optimal ate Miller loop, gg20b: u - q - 2*q^6
    Both cases have exactly the same Miller loop cost.

    optimized final exponentiation formula, two exponents where only signs change
    e1a = (u^6 - 2*u^5 + 5*u^4 + 328)*(-41*q^2 + u*q*(7 - 24*q^5) + u^2*(11 - 2*q^5) + u^3*q^4*(4 - 3*q^5) + u^4*q^3*(2 + q^5) + u^5*q^7)
        + (u^2 - 2*u + 5) * (625*q*(2 - q^5) + 125*u*(4 + 3*q^5) + 25*u^2*q^4*(11 + 2*q^5) + 5*u^3*q^3*(7 + 24*q^5) + 38*u^4*q^7)
        + 6724*q^7

    e1b = (u^6 - 2*u^5 + 5*u^4 - 328)*(-41*q^2 + u*q*(7 + 24*q^5) + u^2*(11 + 2*q^5) - u^3*q^4*(4 + 3*q^5) + u^4*q^3*(-2 + q^5) + u^5*q^7)
        + (u^2 - 2*u + 5)            *(-q*(q^5 + 2)*5^4 + u*(-4 + 3*q^5)*5^3 + u^2*q^4*(11 - 2*q^5)*5^2 + u^3*q^3*(7 - 24*q^5)*5 - 38*u^4*q^7)
        + 4*41^2*q^7
    """
    # cost
    # b=0
    k = 20
    d = 4
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    m5 = 13*m # Montgomery formula
    s5 = 13*s # Montgomery formula
    f5 = 4*m
    m10 = 3*m5 # Karastuba in quadratic extensions
    s10 = 2*m5 # squaring in quadratic extensions
    m20 = 3*m10 # Karastuba in quadratic extensions
    s20 = 2*m10 # squaring in quadratic extensions
    s20_cyclo = 2*s10 # = 4*m5
    f20 = (k-2)*m # problem to check as p=3 mod 5, not p=1 mod 5
    i5 = 48*m + inv # Masson PhD thesis page ix
    assert i5 == 3*f5 + 2*m5 + 10*m + inv
    # it means: inv(m) = m^p*m^(p^2)*m^(p^3)*m^(p^4)/Norm(m)
    # hence 4 Frobenius f5, 3 multiplications m5,
    # 5 multiplications m to compute Norm(m) from m^(p+p^2+p^3+p^4),
    # 5 multiplications to multiply inv(Norm(m)) by the numerator in Fp5.
    # improvement: m^(p+p^2+p^3+p^4) = m^(p*(p+1)*(p^2+1)) = ((m^p)^(p+1))^(p^2+1)
    # in 3 Frobenius f5, 2 multiplications
    # total 3 f5 + 2 m5 + 10 m + inv
    i10 = 2*m5 + 2*s5 + i5
    i20 = 2*m10 + 2*s10 + i10
    me=m5; se=s5; mk = m20; sk=s20; sk_cyclo = s20_cyclo; fk = f20; ik = i20 # e = k/d with d=4
    print("m20 = {}m s20 = {}m, f20 = {}m, s20cyclo = {}m, i20={}m+i={}m".format(m20, s20, f20, s20_cyclo, i20, i20+inv))

    # Costello Lange Naehrig, with d=4, b=0
    # Table 6 and 7 page 20 of Eurocrypt'22, El Housni Guillevic, eprint.iacr.org/2021/1359
    double_line_ate_cln = 2*me+8*se+(k//2)*m
    add_line_ate_cln    = 9*me+5*se+(k//2)*m
    sparse_dense = 8*me
    sparse_sparse = 6*me

    u0 = ZZ(u0)
    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    bits_2naf_u0_ = [bits_2naf_u0[i]*i for i in range(len(bits_2naf_u0)) if bits_2naf_u0[i] != 0]
    print("bits(u) = {} HW(u) = {}".format(u0.nbits(), hw_u))
    print("bits(u) = {} HW(u) = {} bits u = {} (2-NAF)".format(len(bits_2naf_u0), hw2naf_u, bits_2naf_u0_))
    u1 = u0-1
    hw_u1 = sum((abs(u1)).digits(2))
    bits_2naf_u1 = bits_2naf(abs(u1))
    hw2naf_u1 = sum([1 for bi in bits_2naf_u1 if bi != 0])
    bits_2naf_u1_ = [bits_2naf_u1[i]*i for i in range(len(bits_2naf_u1)) if bits_2naf_u1[i] != 0]
    print("bits(u-1) = {} HW(u-1) = {}".format(u1.nbits(), hw_u1))
    print("bits(u-1) = {} HW(u-1) = {} bits u-1 = {} (2-NAF)".format(len(bits_2naf_u1), hw2naf_u1, bits_2naf_u1_))

    cost_opt_ate_cln = (u0.nbits()-1)*(double_line_ate_cln + sk) - sk + (u0.nbits()-2 - (hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln + sparse_sparse + mk)
    cost_opt_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln + sk) - sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln + sparse_sparse + mk)

    adjust_line_cost = add_line_ate_cln + 4*f5 + double_line_ate_cln + sparse_sparse + mk  # actually the doubling is in affine coordinates
    cost_opt_ate_cln += adjust_line_cost
    cost_opt_ate_cln_2naf += adjust_line_cost
    min_cost_miller = min(cost_opt_ate_cln, cost_opt_ate_cln_2naf)

    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    #print("cost ate Miller = {}m".format(cost_ate))
    print("cost opt ate Miller = {}m (Costello Lange Naehrig)".format(cost_opt_ate_cln))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format(u0.nbits(), hw_u, e))
    print("cost opt ate Miller = {}m (2-naf, Costello Lange Naehrig)".format(cost_opt_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, e))

    # final exponentiation
    # k=20 (p^20-1)/r = (p^20-1)/Phi_20(u) * Phi_20(u)/r = (p^10-1)*(p^2+1)*(p^8-p^6+p^4-p^2+1)/r
    # easy part: m^((p^(k//2-1))*(p^2+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk
    # exponentiation to the power u-1
    exp_u1 = (u1.nbits()-1)*sk_cyclo + (hw_u1-1)*mk
    # 2-naf
    exp_u1_2naf = (len(bits_2naf_u1)-1)*sk_cyclo + (hw2naf_u1-1)*mk

    # Frobenius powers fk_i = x^(q^i) for x in Fq20
    fk_2 = 16*m
    fk_3 = fk
    fk_4 = fk_2
    fk_5 = 15*m
    fk_6 = fk_2
    # final exp v1: 9*exp(u) + 2*exp(u-1) + 8*frob5 + 10*frob + 43*M + 52*S
    hard_part_aux_v1 = 43*mk + 52*sk_cyclo + 10*fk + 8*fk_5
    hard_part_aux_v2 = 42*mk + 51*sk_cyclo + 9*fk + 4*fk_5

    hard_part_main = 9*exp_u + 2*exp_u1
    hard_part_main_2naf = 9*exp_u_2naf + 2*exp_u1_2naf

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard v1:  {}m (with cyclotomic squarings)".format(hard_part_main + hard_part_aux_v1))
    print("cost final exp hard v1:  {}m (2-naf with cyclotomic squarings)".format(hard_part_main_2naf + hard_part_aux_v1))
    print("cost final exp hard v2:  {}m (with cyclotomic squarings)".format(hard_part_main + hard_part_aux_v2))
    print("cost final exp hard v2:  {}m (2-naf with cyclotomic squarings, new exact count)".format(hard_part_main_2naf + hard_part_aux_v2))
    print("cost final exp:       {}m".format(easy_part + hard_part_main + min(hard_part_aux_v1, hard_part_aux_v2)))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_main_2naf + min(hard_part_aux_v1, hard_part_aux_v2)))
    print("\ncost pairing (total)  {}m\n".format(easy_part + min(hard_part_main, hard_part_main_2naf) + min(hard_part_aux_v1, hard_part_aux_v2) + min_cost_miller))

def cost_pairing_sg20(u0):
    """
    The arithmetic cost over GF(p^5) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M5 = 13*m, and because the formulas are symmetric in the variables a_i, b_i,
    S5 = 13*s
    """
    # cost
    # b=0
    k = 20
    d = 4
    e = k // d
    u0 = ZZ(u0)
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    m5 = 13*m # Montgomery formula
    s5 = 13*s # Montgomery formula
    f5 = 4*m
    m10 = 3*m5 # Karastuba in quadratic extensions
    s10 = 2*m5 # squaring in quadratic extensions
    m20 = 3*m10 # Karastuba in quadratic extensions
    s20 = 2*m10 # squaring in quadratic extensions
    s20_cyclo = 2*s10 # = 4*m5
    f20 = (k-2)*m # problem to check as p=3 mod 5, not p=1 mod 5
    i5 = 48*m + inv # Masson PhD thesis page ix
    i10 = 2*m5 + 2*s5 + i5
    i20 = 2*m10 + 2*s10 + i10
    me=m5; se=s5; mk = m20; sk=s20; sk_cyclo = s20_cyclo; fk = f20; ik = i20 # e = k/d with d=4

    # Costello Lange Naehrig, with d=4, b=0
    # Table 6 and 7 page 20 of Eurocrypt'22, El Housni Guillevic, eprint.iacr.org/2021/1359
    double_line_ate_cln = 2*me+8*se+(k//2)*m
    add_line_ate_cln    = 9*me+5*se+(k//2)*m
    sparse_dense = 8*me
    sparse_sparse = 6*me

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    hw_2u = sum((abs(2*u0)).digits(2))
    bits_2naf_2u0 = bits_2naf(abs(2*u0))
    hw2naf_2u = sum([1 for bi in bits_2naf_2u0 if bi != 0])

    cost_opt_ate_cln = ((2*u0).nbits()-1)*(double_line_ate_cln + sk) - sk + ((2*u0).nbits()-2 - (hw_2u-1))*sparse_dense + (hw_2u-1)*(add_line_ate_cln + sparse_sparse + mk)
    cost_opt_ate_cln_2naf = (len(bits_2naf_2u0)-1)*(double_line_ate_cln + sk) - sk + (len(bits_2naf_2u0)-2-(hw2naf_2u-1))*sparse_dense + (hw2naf_2u-1)*(add_line_ate_cln + sparse_sparse + mk)

    adjust_line_cost = add_line_ate_cln + 2*f5 + sparse_dense
    cost_opt_ate_cln += adjust_line_cost
    cost_opt_ate_cln_2naf += adjust_line_cost
    min_cost_miller = min(cost_opt_ate_cln, cost_opt_ate_cln_2naf)

    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    #print("cost ate Miller = {}m".format(cost_ate))
    print("cost opt ate Miller = {}m (Costello Lange Naehrig)".format(cost_opt_ate_cln))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format((2*u0).nbits(), hw_2u, e))
    print("cost opt ate Miller = {}m (2-naf, Costello Lange Naehrig)".format(cost_opt_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format(len(bits_2naf_2u0), hw2naf_2u, e))

    # final exponentiation
    # k=20 (p^20-1)/r = (p^20-1)/Phi_20(u) * Phi_20(u)/r = (p^10-1)*(p^2+1)*(p^8-p^6+p^4-p^2+1)/r
    # easy part: m^((p^(k//2-1))*(p^2+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk

    # final exp: more than 11*exp(u) + 13*frob + 50*M
    fk_2 = 16*m
    fk_3 = fk
    fk_4 = fk_2
    fk_6 = fk_2

    hard_part = 13*exp_u + 19*m20 + 6*s20 + 7*f20
    hard_part_2naf = 13*exp_u_2naf+ 19*m20 + 6*s20 + 7*f20

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings, rough lower bound)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings, rough lower bound)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m\n".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

def cost_pairing_fst66_k20(u0):
    """
    The arithmetic cost over GF(p^5) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M5 = 13*m,
    M7 = 22*m, and because the formulas are symmetric in the variables a_i, b_i,
    S5 = 13*s
    S7 = 22*s
    """
    # cost
    # a=0
    print("u = {} = {:#x}".format(u0, u0))
    k = 20
    d = 2
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    m5 = 13*m # Montgomery formula
    s5 = 13*s # Montgomery formula
    f5 = 4*m
    m10 = 3*m5 # Karastuba in quadratic extensions
    s10 = 2*m5 # squaring in quadratic extensions
    f10 = 8*m
    m20 = 3*m10 # Karastuba in quadratic extensions
    s20 = 2*m10 # squaring in quadratic extensions
    s20_cyclo = 2*s10 # = 4*m5
    f20 = (k-2)*m
    i5 = 48*m + inv # Masson PhD thesis page ix
    i10 = 2*m5 + 2*s5 + i5
    i20 = 2*m10 + 2*s10 + i10
    me=m10; se=s10; mk = m20; sk=s20; sk_cyclo = s20_cyclo; fk = f20; ik = i20 # e = k/d with d=2
    # group operation on the curve
    # Costello Lange Naehrig formulas Sect. 5 Tab. 3
    # a=0, quadratic twist
    double_line_ate = 2*me+7*se+k*m
    add_line_ate    = 10*me+2*se+k*m

    u0 = ZZ(u0)
    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    # f_{u,Q}(P)
    cost_1 = (u0.nbits()-1)*double_line_ate + (u0.nbits()-2)*(mk+sk) + (hw_u-1)*(add_line_ate+mk)
    # f_{u,Q}^u * f_{u,[u]Q}(P)
    cost_2 = (u0.nbits()-1)*(double_line_ate + mk+sk) + (hw_u-1)*(add_line_ate+mk+mk)
    cost_3 = i10 + s10 + 3*m10 # computing uQ in affine coordinates
    cost_4 = 2*f10 + add_line_ate + f20 + 2*mk # pi_p([u]Q) + line + final accumulation
    cost_opt_ate = cost_1 + cost_2 + cost_3 + cost_4

    cost_1_2naf = (len(bits_2naf_u0)-1)*double_line_ate + (len(bits_2naf_u0)-2)*(mk+sk) + (hw2naf_u-1)*(add_line_ate + mk)
    cost_2_2naf = (len(bits_2naf_u0)-1)*(double_line_ate + mk+sk) + (hw2naf_u-1)*(add_line_ate + mk+mk)
    cost_opt_ate_2naf = cost_1_2naf + cost_2_2naf + cost_3 + cost_4

    min_cost_miller = min(cost_opt_ate, cost_opt_ate_2naf)
    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    print("cost opt ate Miller = {}m".format(cost_opt_ate))
    print("cost f_(u,Q)(P): ({0}-1)*(2*m{2}+7*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(10*m{2}+2*s{2}+k*m +mk)".format(u0.nbits(), hw_u, e))
    print("cost opt ate Miller = {}m (2-naf)".format(cost_opt_ate_2naf))
    print("cost f_(u,Q)(P): ({0}-1)*(2*m{2}+7*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(10*m{2}+2*s{2}+k*m+mk)".format(len(bits_2naf_u0), hw2naf_u, e))

    # final exponentiation
    # k=20 (p^20-1)/r = (p^20-1)/Phi_20(u) * Phi_20(u)/r = (p^10-1)*(p^2+1)*(p^8-p^6+p^4-p^2+1)/r
    # easy part: m^((p^(k//2-1))*(p^2+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk

    # 20*exp(|u|) + 25 M + 2 S + 5*frob + 2*frob(2) + frob(3) + 3*frob(4) + 2*frob(6)
    fk_2 = 16*m
    fk_3 = fk
    fk_4 = fk_2
    fk_6 = fk_2
    hard_part_aux = 25*mk + 2*sk_cyclo + 5*fk + 2*fk_2 + fk_3 + 3*fk_4 + 2*fk_6
    hard_part = 20*exp_u + hard_part_aux
    hard_part_2naf = 20*exp_u_2naf + hard_part_aux

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m\n".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

def cost_pairing_fst66_k22(u0, lower_bound_m11=False):
    """
    See the notes of cost_pairing_fst63_k22
    INPUT:
    - `u0`: curve seed
    - `lower_bound_m11`: boolean, choose between m11 = 45*m or m11 = 48*m
    The curve has the form y^2 = x^3 + b (a = 0, j = 0)
    pairing: u^2 - u*q^4 + q^8
    """
    print("u = {} = {:#x}".format(u0, u0))
    k = 22
    d = 2
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    if lower_bound_m11:
        m11 = 45*m # Karastuba lower bound
        s11 = 45*s # squaring with Karatsuba lower bound
    else:
        m11 = 48*m # Karastuba intermediate steps with 5-term and 6-term formulas
        s11 = 48*s # squaring with the same formulas
    f11 = 10*m
    m22 = 3*m11 # Karastuba in quadratic extensions
    s22 = 2*m11 # squaring in quadratic extensions
    s22_cyclo = 2*s11 # actually, does it really work?
    f22 = (k-2)*m
    i11 = 5*f11 + 4*m11 + 2*11*m + inv
    i22 = 2*m11 + 2*s11 + i11
    me=m11; se=s11; mk = m22; sk=s22; sk_cyclo = s22_cyclo; fk = f22; ik = i22 # e = k/d with d=2
    # curve arithmetic: a zero, b non-zero
    # generic formulas are not optimal
    # double_line_ate = 5*me+5*se+k*m # pairing.py l. 46
    # add_line_ate    = 10*me+3*se
    # add_line_ate_with_z = 14*me+3*se+k*m # pairing.py l. 189
    # pairing.py line 95, for any a
    # double_line_affine_ate = 3*me+4*se+k//2*m
    #double_line_ate_csb = 5*me+5*se+k*m # pairing.py l. 236
    #add_line_ate_csb = 10*me+3*se+k*m # pairing.py l. 280

    # Costello Lange Naehrig formulas Sect. 5 Tab. 3
    # a=0, quadratic twist
    double_line_ate_cln_a0 = 2*me+7*se+k*m #
    # mixed inputs affine projective
    add_line_ate_cln_a0 = 10*me + 2*se + k*m # CLN10 says
    # but so far I was able to get 11*me+2*se+k//2*m

    double_line_ate = double_line_ate_cln_a0
    add_line_ate = add_line_ate_cln_a0

    # formula: u^2 - u*q^4 + q^8 = 0 mod r
    u0 = ZZ(u0)
    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    # f_{u,Q}(P)
    cost_1 = (u0.nbits()-1)*double_line_ate + (u0.nbits()-2)*(mk+sk) + (hw_u-1)*(add_line_ate+mk)
    # f_{u,Q}^u * f_{u,[u]Q}(P)
    cost_2 = (u0.nbits()-1)*(double_line_ate + mk+sk) + (hw_u-1)*(add_line_ate+mk+mk)
    cost_3 = i11 + 2*m11 # computing uQ in affine coordinates
    cost_4 = 2*f11 + add_line_ate + f22 + 2*mk # pi_p4(-[u]Q) + line + final accumulation
    cost_opt_ate = cost_1 + cost_2 + cost_3 + cost_4

    cost_1_2naf = (len(bits_2naf_u0)-1)*double_line_ate + (len(bits_2naf_u0)-2)*(mk+sk) + (hw2naf_u-1)*(add_line_ate + mk)
    cost_2_2naf = (len(bits_2naf_u0)-1)*(double_line_ate + mk+sk) + (hw2naf_u-1)*(add_line_ate + mk+mk)
    cost_opt_ate_2naf = cost_1_2naf + cost_2_2naf + cost_3 + cost_4

    min_cost_miller = min(cost_opt_ate, cost_opt_ate_2naf)
    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    print("\nf_{u,Q}^u(P) * f_{u,[u]Q}(P)")
    print("cost opt ate Miller = {}m".format(cost_opt_ate))
    print("cost f_(u,Q)(P): ({0}-1)*(2*m{2}+7*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(11*m{2}+2*s{2} +mk)".format(u0.nbits(), hw_u, e))
    print("cost opt ate Miller = {}m (2-naf)".format(cost_opt_ate_2naf))
    print("cost f_(u,Q)(P): ({0}-1)*(2*m{2}+7*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(11*m{2}+2*s{2} +mk)".format(len(bits_2naf_u0), hw2naf_u, e))
    # final exponentiation
    # k=22 (p^22-1)/r = (p^22-1)/Phi_22(u) * Phi_22(u)/r = (p^11-1)*(p+1)*(p^10-p^9+p^8-p^7+p^6-p^5+p^4-p^3+p^2-p+1)/r
    # easy part: m^((p^(k//2-1))*(p+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk

    # 26 exp(u) + S + 11 M + 6 frob
    hard_part_aux = 11*mk + sk_cyclo + 6*fk
    hard_part = 26*exp_u + hard_part_aux
    hard_part_2naf = 26*exp_u_2naf + hard_part_aux

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m\n".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

def cost_pairing_fst63_k22(u0, lower_bound_m11=False):
    """
    The arithmetic cost over GF(p^11) can be estimated with Karatsuba ratio
    m_k >= k^(log_2(3))*m = 44.72*m
    M11 = 45*m,
    S11 = 45*s
    but it seems somehow under-estimated (the implementation would take hours and days).
    Write A = (A0 + A1*X^6), B = (B0 + B1*X^6) in GF(p^11), where A0, B0 are 6-terms:
    A0 = a0 + a1*X + ... + a5*X^5, B0 = b0 + b1*X + ... + b5 * X^5
    A1 = a6 + a7*X + ... + a10*X^4, B1 = b6 + b7*X + ... + b10*X^4
    Then A*B = (A0+A1*X^6)*(B0+B1^X^6) = A0*B0 + A1*B1*X^12 + ((A0+A1*X)*(B0+B1*X) - A0*B0 - A1*B1*X^2)*X^5
    with one 6-term mult, one 5-term mult, and one 6-term mult minus one mult (a0*b0).
    M11 = 18*m + 13*m + 17*m = 48*m with M6 = 18M
    M11 = 17*m + 13*m + 16*m = 46*m with M6 = 17M

    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    eq(6): M(11) <= M(5) + 2*M(6) - 1 where M(k) = cost of multiplying two k-term polynomials.
    M5 = 13*m, and because the formulas are symmetric in the variables a_i, b_i,
    S5 = 13*s
    Note that 5^(log_2(3)) = 12.81
    M6 = 17*m, and because the formulas are symmetric in the variables a_i, b_i,
    S6 = 17*s
    Note that 6^(log_2(3)) = 17.11
    With old Karatsuba-Ofman, M6 = M(2)*M(3) = 3*6 = 18M
    With Chung-Hasan formulas combined, S6 = 12 M
    M7 = 22*m and because the formulas are symmetric in the variables a_i, b_i,
    S7 = 22*s
    Note that 7^(log_2(3)) = 21.84

    Inversion in GF(p^11):
    a^(-1) = a^p*a^(p^2)*...*a^(p^10)/Norm(a)
           = a^(p*(1+p+p^2+...+p^9))/Morm(a)
           = a^(p*(p+1)*((1+p^2)*(1+p^4)+p^8))/Norm(a)
    numerator: 5 Frob + 4 M11
    denominator = a * numerator but it falls in Fp by definition,
    hence only the terms a_i * n_j where (i+j) = 0 mod 11: 11 terms
    finally, invert the norm then multiply by the numerator: 11 m
    total: 5 Frob + 4 M11 + 11m + inv + 11m
    """
    # cost
    # b=0
    print("u = {} = {:#x}".format(u0, u0))
    k = 22
    d = 2
    e = k // d
    u0 = ZZ(u0)
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    if lower_bound_m11:
        m11 = 45*m # Karastuba lower bound
        s11 = 45*s # squaring with Karatsuba lower bound
    else:
        m11 = 48*m # Karastuba intermediate steps with 5-term and 6-term formulas
        s11 = 48*s # squaring with the same formulas
    f11 = 10*m
    m22 = 3*m11 # Karastuba in quadratic extensions
    s22 = 2*m11 # squaring in quadratic extensions
    s22_cyclo = 2*s11 # actually, does it really work?
    f22 = (k-2)*m
    i11 = 5*f11 + 4*m11 + 2*11*m + inv
    i22 = 2*m11 + 2*s11 + i11
    me=m11; se=s11; mk = m22; sk=s22; sk_cyclo = s22_cyclo; fk = f22; ik = i22 # e = k/d with d=2
    double_line_ate = 2*me+8*se+k*m
    add_line_ate    = 9*me+5*se+k*m

    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    # f_{u,Q}(P)
    cost_1 = (u0.nbits()-1)*double_line_ate + (u0.nbits()-2)*(mk+sk) + (hw_u-1)*(add_line_ate+mk)
    # f_{u,Q}^u * f_{u,[u]Q}(P)
    cost_2 = (u0.nbits()-1)*(double_line_ate + mk+sk) + (hw_u-1)*(add_line_ate+mk+mk)
    cost_3 = i11 + s11 + 3*m11 # computing uQ in affine coordinates
    cost_4 = 2*f11 + add_line_ate + f22 + 2*mk # pi_p([u]Q) + line + final accumulation
    cost_opt_ate = cost_1 + cost_2 + cost_3 + cost_4

    cost_1_2naf = (len(bits_2naf_u0)-1)*double_line_ate + (len(bits_2naf_u0)-2)*(mk+sk) + (hw2naf_u-1)*(add_line_ate + mk)
    cost_2_2naf = (len(bits_2naf_u0)-1)*(double_line_ate + mk+sk) + (hw2naf_u-1)*(add_line_ate + mk+mk)
    cost_opt_ate_2naf = cost_1_2naf + cost_2_2naf + cost_3 + cost_4

    # f_{u^2,Q}(P)
    u2 = u0**2
    hw_u2 = sum((abs(u2)).digits(2))
    bits_2naf_u2 = bits_2naf(abs(u2))
    hw2naf_u2 = sum([1 for bi in bits_2naf_u2 if bi != 0])
    alt_cost_opt_ate = (u2.nbits()-1)*double_line_ate + (u2.nbits()-2)*(mk+sk) + (hw_u2-1)*(add_line_ate+mk)
    alt_cost_opt_ate_2naf = (len(bits_2naf_u2)-1)*double_line_ate + (len(bits_2naf_u2)-2)*(mk+sk) + (hw2naf_u2-1)*(add_line_ate + mk)

    min_cost_miller = min(cost_opt_ate, cost_opt_ate_2naf, alt_cost_opt_ate, alt_cost_opt_ate_2naf)
    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    print("\nf_{u,Q}^u(P) * f_{u,[u]Q}(P)")
    print("cost opt ate Miller = {}m".format(cost_opt_ate))
    print("cost f_(u,Q)(P): ({0}-1)*(2*m{2}+8*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(9*m{2}+5*s{2}+k*m +mk)".format(u0.nbits(), hw_u, e))
    print("cost opt ate Miller = {}m (2-naf)".format(cost_opt_ate_2naf))
    print("cost f_(u,Q)(P): ({0}-1)*(2*m{2}+8*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(9*m{2}+5*s{2}+k*m+mk)".format(len(bits_2naf_u0), hw2naf_u, e))

    print("\nf_{u^2,Q}(P)")
    print("cost opt ate Miller = {}m".format(alt_cost_opt_ate))
    print("cost f_(u^2,Q)(P): ({0}-1)*(2*m{2}+8*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(9*m{2}+5*s{2}+k*m +mk)".format(u2.nbits(), hw_u2, e))
    print("cost opt ate Miller = {}m (2-naf)".format(alt_cost_opt_ate_2naf))
    print("cost f_(u^2,Q)(P): ({0}-1)*(2*m{2}+8*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(9*m{2}+5*s{2}+k*m+mk)".format(len(bits_2naf_u2), hw2naf_u2, e))

    # final exponentiation
    # k=22 (p^22-1)/r = (p^22-1)/Phi_22(u) * Phi_22(u)/r = (p^11-1)*(p+1)*(p^10-p^9+p^8-p^7+p^6-p^5+p^4-p^3+p^2-p+1)/r
    # easy part: m^((p^(k//2-1))*(p+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk

    # 24 exp(u) + 2 S + 21 M + 9 frob
    hard_part_aux = 21*mk + 2*sk_cyclo + 9*fk
    hard_part = 24*exp_u + hard_part_aux
    hard_part_2naf = 24*exp_u_2naf + hard_part_aux

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m\n".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

def cost_pairing_kss22d7(u0, lower_bound_m11=False, a_3=False):
    """
    See the notes of cost_pairing_fst63_k22
    INPUT:
    - `u0`: curve seed
    - `lower_bound_m11`: boolean, choose between m11 = 45*m or m11 = 48*m
    - `a_3`: boolean, if the curve coefficient a is -3 or not (for arithmetic optimisation)
    """
    print("u = {} = {:#x}".format(u0, u0))
    k = 22
    d = 2
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    if lower_bound_m11:
        m11 = 45*m # Karastuba lower bound
        s11 = 45*s # squaring with Karatsuba lower bound
    else:
        m11 = 48*m # Karastuba intermediate steps with 5-term and 6-term formulas
        s11 = 48*s # squaring with the same formulas
    f11 = 11*10*m # there is no q=1 mod 11 so it is quite complicated
    m22 = 3*m11 # Karastuba in quadratic extensions
    s22 = 2*m11 # squaring in quadratic extensions
    s22_cyclo = 2*s11 # actually, does it really work?
    f22 = 21*11*m # again q!=1 mod 11 complicates the situation
    i11 = 5*f11 + 4*m11 + 2*11*m + inv
    # m^(q+q^2+...+q^10) = q(q^5+1)((q^2+1)(q+1)q+1) = q(q+1)((q^4+1)(q^2+1)q^2+1)
    i22 = 2*m11 + 2*s11 + i11
    me=m11; se=s11; mk = m22; sk=s22; sk_cyclo = s22_cyclo; fk = f22; ik = i22 # e = k/d with d=2
    # curve arithmetic: a non-zero, b non-zero
    double_line_affine_ate = 3*me+4*se+k//2*m
    if a_3:
        double_line_ate = 6*me+4*se+k*m
    else:
        double_line_ate = 5*me+6*se+k*m
    add_line_ate        = 10*me+3*se
    add_line_ate_with_z = 14*me+3*se+k*m

    # optimal ate pairing formula: u^2 - u*q + 2*q^2 = 0 mod r
    u0 = ZZ(u0)
    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    # f_{u,Q}(P)
    cost_1 = double_line_affine_ate + (u0.nbits()-2)*(double_line_ate+mk+sk) + (hw_u-1)*(add_line_ate+mk)
    # f_{u,Q}^u * f_{u,[u]Q}(P)
    cost_2 = double_line_affine_ate+mk+sk + (u0.nbits()-2)*(double_line_ate + mk+sk) + (hw_u-1)*(add_line_ate+mk+mk)
    cost_3 = i11 + s11 + 3*m11 # computing uQ in affine coordinates
    cost_4 = double_line_affine_ate # f_{2,Q}(P)
    cost_5 = 2*f11 + add_line_ate + 2*f22 + 3*mk # pi_p([-u]Q) + line l_{u^2Q, -upi(Q)} + final accumulation
    cost_opt_ate = cost_1 + cost_2 + cost_3 + cost_4 + cost_5

    cost_1_2naf = double_line_affine_ate + (len(bits_2naf_u0)-2)*(double_line_ate + mk+sk) + (hw2naf_u-1)*(add_line_ate + mk)
    cost_2_2naf = double_line_affine_ate +mk+sk + (len(bits_2naf_u0)-2)*(double_line_ate + mk+sk) + (hw2naf_u-1)*(add_line_ate + mk+mk)
    cost_opt_ate_2naf = cost_1_2naf + cost_2_2naf + cost_3 + cost_4 + cost_5

    min_cost_miller = min(cost_opt_ate, cost_opt_ate_2naf)
    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    print("\nf_{u,Q}^u(P) * f_{u,[u]Q}(P)")
    print("cost opt ate Miller = {}m".format(cost_opt_ate))
    if a_3:
        print("cost f_(u,Q)(P): ({0}-1)*(6*m{2}+4*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(10*m{2}+3*s{2} +mk)".format(u0.nbits(), hw_u, e))
    else:
        print("cost f_(u,Q)(P): ({0}-1)*(5*m{2}+6*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(10*m{2}+3*s{2} +mk)".format(u0.nbits(), hw_u, e))
    print("cost opt ate Miller = {}m (2-naf)".format(cost_opt_ate_2naf))
    if a_3:
        print("cost f_(u,Q)(P): ({0}-1)*(6*m{2}+4*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(10*m{2}+3*s{2} +mk)".format(len(bits_2naf_u0), hw2naf_u, e))
    else:
        print("cost f_(u,Q)(P): ({0}-1)*(5*m{2}+6*s{2}+k*m) + ({0}-2)*(mk+sk) + ({1}-1)*(10*m{2}+3*s{2} +mk)".format(len(bits_2naf_u0), hw2naf_u, e))

    # final exponentiation
    # k=22 (p^22-1)/r = (p^22-1)/Phi_22(u) * Phi_22(u)/r = (p^11-1)*(p+1)*(p^10-p^9+p^8-p^7+p^6-p^5+p^4-p^3+p^2-p+1)/r
    # easy part: m^((p^(k//2-1))*(p+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk

    # 22 exp(u) + 17 frob + 3 frob(9) + 41 M + 50 S
    hard_part_aux = 41*mk + 50*sk_cyclo + 20*fk
    hard_part = 22*exp_u + hard_part_aux
    hard_part_2naf = 22*exp_u_2naf + hard_part_aux

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m\n".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

def cost_pairing_fst64(u0, k):
    """
    The arithmetic cost over GF(p^5) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M5 = 13*m,
    M7 = 22*m, and because the formulas are symmetric in the variables a_i, b_i,
    S5 = 13*s
    S7 = 22*s
    """
    assert (k % 8) == 4
    assert k in [20, 28]
    # cost
    # b=0
    #k = 20
    d = 4
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    if k == 20:
        m5 = 13*m # Montgomery formula
        s5 = 13*s # Montgomery formula
        f5 = 4*m
        m10 = 3*m5 # Karastuba in quadratic extensions
        s10 = 2*m5 # squaring in quadratic extensions
        m20 = 3*m10 # Karastuba in quadratic extensions
        s20 = 2*m10 # squaring in quadratic extensions
        s20_cyclo = 2*s10 # = 4*m5
        f20 = (k-2)*m
        i5 = 48*m + inv # Masson PhD thesis page ix
        i10 = 2*m5 + 2*s5 + i5
        i20 = 2*m10 + 2*s10 + i10
        me=m5; se=s5; mk = m20; sk=s20; sk_cyclo = s20_cyclo; fk = f20; ik = i20 # e = k/d with d=4
    elif k == 28:
        m7 = 22*m
        s7 = 22*s
        f7 = 6*m
        m14 = 3*m7
        s14 = 2*m7
        m28 = 3*m14
        s28 = 2*m14
        s28_cyclo = 2*s14
        f28 = (k-2)*m
        i7 = 104*m + inv # Masson PhD thesis page ix
        i14 = 2*m7 + 2*s7 + i7
        i28 = 2*m14 + 2*s14 + i14
        me=m7; se=s7; mk = m28; sk=s28; sk_cyclo = s28_cyclo; fk = f28; ik = i28 # e = k/d with d=4
        print("m28 = {}m s28 = {}m, f28 = {}m, s28cyclo = {}m, i28={}m+i={}m".format(m28, s28, f28, s28_cyclo, i28, i28+inv))
    # Costello Lange Naehrig, with d=4, b=0
    # Table 6 and 7 page 20 of Eurocrypt'22, El Housni Guillevic, eprint.iacr.org/2021/1359
    double_line_ate_cln = 2*me+8*se+(k//2)*m
    add_line_ate_cln    = 9*me+5*se+(k//2)*m
    sparse_dense = 8*me
    sparse_sparse = 6*me

    u0 = ZZ(u0)
    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])

    cost_opt_ate_cln = (u0.nbits()-1)*(double_line_ate_cln + sk) - sk + (u0.nbits()-2 - (hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln + sparse_sparse + mk)
    cost_opt_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln + sk) - sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln + sparse_sparse + mk)
    min_cost_miller = min(cost_opt_ate_cln, cost_opt_ate_cln_2naf)

    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    #print("cost ate Miller = {}m".format(cost_ate))
    print("cost opt ate Miller = {}m (Costello Lange Naehrig)".format(cost_opt_ate_cln))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format(u0.nbits(), hw_u, e))
    print("cost opt ate Miller = {}m (2-naf, Costello Lange Naehrig)".format(cost_opt_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, e))

    # final exponentiation
    # k=20 (p^20-1)/r = (p^20-1)/Phi_20(u) * Phi_20(u)/r = (p^10-1)*(p^2+1)*(p^8-p^6+p^4-p^2+1)/r
    # k=28 (p^28-1)/r = (p^28-1)/Phi_28(u) * Phi_28(u)/r = (p^14-1)*(p^2+1)*(p^12-p^10+p^8-p^6+p^4-p^2+1)/r
    # easy part: m^((p^(k//2-1))*(p^2+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # exponentiation to the power (u-1)//2
    u1 = abs(u0-1)//2
    hw_u1 = sum(u1.digits(2))
    exp_u1 = (u1.nbits()-1)*sk_cyclo + (hw_u1-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk
    bits_2naf_u1 = bits_2naf(u1)
    hw2naf_u1 = sum([1 for bi in bits_2naf_u1 if bi != 0])
    exp_u1_2naf = (len(bits_2naf_u1)-1)*sk_cyclo + (hw2naf_u1-1)*mk

    if k == 20:
        #total cost 2*exp((u-1)//2) + 9*exp(|u|) + 8 M + frob + 2*frob(2) + frob(4) + 2 conj + 1 conj if u < 0
        hard_part = 2*exp_u1 + 9*exp_u + 8*mk + fk + 2*fk + fk
        hard_part_2naf = 2*exp_u1_2naf + 9*exp_u_2naf + 8*mk + fk + 2*fk + fk
    elif k == 28:
        #total cost 2*exp((u-1)//2) + 13*exp(|u|) + 13 M + frob + 5*frob(2) + conj (+ 1 conj if u < 0)
        #total cost 2*exp((u-1)//2) + 13*exp(|u|) + 12 M + frob + 2*frob(2)+frob(4)+2*frob(6) + 2conj (+ 1 conj if u < 0)
        # probably fk << mk so the second option will be chosen:
        hard_part = 2*exp_u1 + 13*exp_u + min(13*mk + fk + 5*fk, 12*mk + fk +2*fk + fk + 2*fk)
        hard_part_2naf = 2*exp_u1_2naf + 13*exp_u_2naf + min(13*mk + fk + 5*fk, 12*mk + fk +2*fk + fk + 2*fk)

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard:  {}m (with cyclotomic squarings)".format(hard_part))
    print("cost final exp hard:  {}m (2-naf with cyclotomic squarings)".format(hard_part_2naf))
    print("cost final exp:       {}m".format(easy_part + hard_part))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_2naf))
    print("\ncost pairing (total)  {}m".format(easy_part + min(hard_part, hard_part_2naf) + min_cost_miller))

def cost_pairing_fst64_k20(u0):
    cost_pairing_fst64(u0, 20)

def cost_pairing_fst64_k28(u0):
    cost_pairing_fst64(u0, 28)

def cost_pairing_gg28a(u0):
    """
    INPUT:
    - `u0`: curve seed

    The arithmetic cost over GF(p^7) is assumed with the formulas of
    Five, Six, and Seven-Term Karatsuba-Like Formulae, Peter L. Montgomery,
    IEEE Transactions on Computers, vol. 54, no. 3, March 2005
    M7 = 22*m, and because the formulas are symmetric in the variables a_i, b_i,
    S7 = 22*s

    optimal ate Miller loop, gg28a: u - q - 2*q^8
    optimal ate Miller loop, gg28a: 2 + u*q^6 - q^7
    Both cases have exactly the same Miller loop cost.

    optimized final exponentiation formula, two exponents where only signs change
    """
    # cost
    # b=0
    k = 28
    d = 4
    e = k // d
    m = 1
    s = 1
    inv = 25*m
    #
    # Granger Scott, Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions,
    # PKC 2010, pages 209-223.
    # http://www.iacr.org/archive/pkc2010/60560212/60560212.pdf
    m7 = 22*m # Montgomery formula
    s7 = 22*s # Montgomery formula
    f7 = 6*m
    m14 = 3*m7 # Karastuba in quadratic extensions
    s14 = 2*m7 # squaring in quadratic extensions
    m28 = 3*m14 # Karastuba in quadratic extensions
    s28 = 2*m14 # squaring in quadratic extensions
    s28_cyclo = 2*s14 # = 4*m7
    f28 = (k-2)*m # assuming p = 1 mod 7 and  p = 1 mod 4
    i7 = 104*m + inv # Masson PhD thesis page ix
    assert i7 == 4*f7 + 3*m7 + 14*m + inv
    # it means: inv(m) = m^p*m^(p^2)*m^(p^3)*m^(p^4)*m^(p^5)*m^(p^6)/Norm(m)
    # hence 6 Frobenius f7, 5 multiplications m7,
    # 7 multiplications m to compute Norm(m) from m^(p+p^2+p^3+p^4+p^5+p^6),
    # 7 multiplications to multiply inv(Norm(m)) by the numerator in Fp7.
    # improvement: m^(p+p^2+p^3+p^4+p^5+p^6) = m^(p*(p+1)*(p^4+p^2+1)) = ((m^p)^(p+1))^(p^4+p^2+1)
    # in 4 Frobenius f7, 3 multiplications
    # total 4 f7 + 3 m7 + 14 m + inv
    i14 = 2*m7 + 2*s7 + i7
    i28 = 2*m14 + 2*s14 + i14
    me=m7; se=s7; mk = m28; sk=s28; sk_cyclo = s28_cyclo; fk = f28; ik = i28 # e = k/d with d=4
    print("m28 = {}m s28 = {}m, f28 = {}m, s28cyclo = {}m, i28={}m+i={}m".format(m28, s28, f28, s28_cyclo, i28, i28+inv))

    # Costello Lange Naehrig, with d=4, b=0
    # Table 6 and 7 page 20 of Eurocrypt'22, El Housni Guillevic, eprint.iacr.org/2021/1359
    double_line_ate_cln = 2*me+8*se+(k//2)*m
    add_line_ate_cln    = 9*me+5*se+(k//2)*m
    sparse_dense = 8*me
    sparse_sparse = 6*me

    u0 = ZZ(u0)
    hw_u = sum((abs(u0)).digits(2))
    bits_2naf_u0 = bits_2naf(abs(u0))
    hw2naf_u = sum([1 for bi in bits_2naf_u0 if bi != 0])
    bits_2naf_u0_ = [bits_2naf_u0[i]*i for i in range(len(bits_2naf_u0)) if bits_2naf_u0[i] != 0]
    print("bits(u) = {} HW(u) = {}".format(u0.nbits(), hw_u))
    print("bits(u) = {} HW(u) = {} bits u = {} (2-NAF)".format(len(bits_2naf_u0), hw2naf_u, bits_2naf_u0_))
    u1 = u0-1
    hw_u1 = sum((abs(u1)).digits(2))
    bits_2naf_u1 = bits_2naf(abs(u1))
    hw2naf_u1 = sum([1 for bi in bits_2naf_u1 if bi != 0])
    bits_2naf_u1_ = [bits_2naf_u1[i]*i for i in range(len(bits_2naf_u1)) if bits_2naf_u1[i] != 0]
    print("bits(u-1) = {} HW(u-1) = {}".format(u1.nbits(), hw_u1))
    print("bits(u-1) = {} HW(u-1) = {} bits u-1 = {} (2-NAF)".format(len(bits_2naf_u1), hw2naf_u1, bits_2naf_u1_))

    cost_opt_ate_cln = (u0.nbits()-1)*(double_line_ate_cln + sk) - sk + (u0.nbits()-2 - (hw_u-1))*sparse_dense + (hw_u-1)*(add_line_ate_cln + sparse_sparse + mk)
    cost_opt_ate_cln_2naf = (len(bits_2naf_u0)-1)*(double_line_ate_cln + sk) - sk + (len(bits_2naf_u0)-2-(hw2naf_u-1))*sparse_dense + (hw2naf_u-1)*(add_line_ate_cln + sparse_sparse + mk)

    adjust_line_cost = 4*f7 + add_line_ate_cln + double_line_ate_cln + sparse_sparse + mk  # actually the doubling is in affine coordinates
    cost_opt_ate_cln += adjust_line_cost
    cost_opt_ate_cln_2naf += adjust_line_cost
    min_cost_miller = min(cost_opt_ate_cln, cost_opt_ate_cln_2naf)

    print("m{} = {}m s{} = {}m".format(k, mk, k, sk))
    print("m{} = {}m s{} = {}m".format(e, me, e, se))
    #print("cost ate Miller = {}m".format(cost_ate))
    print("cost opt ate Miller = {}m (Costello Lange Naehrig)".format(cost_opt_ate_cln))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format(u0.nbits(), hw_u, e))
    print("cost opt ate Miller = {}m (2-naf, Costello Lange Naehrig)".format(cost_opt_ate_cln_2naf))
    print("({0}-1)*(2*m{2}+8*s{2}+(k//2)*m + sk) -sk + ({0}-2-({1}-1))*(8*m{2}) + ({1}-1)*(9*m{2}+5*s{2}+(k//2)*m + 6*m{2}+mk)".format(len(bits_2naf_u0), hw2naf_u, e))

    # final exponentiation
    # k=28 (p^28-1)/r = (p^28-1)/Phi_28(u) * Phi_28(u)/r = (p^14-1)*(p^2+1)*(p^12-p^10+p^8-p^6+p^4-p^2+1)/r
    # easy part: m^((p^(k//2-1))*(p^2+1)) where m^(k//2) is a conjugation and costs nothing
    easy_part = ik + mk + fk + mk
    # exponentiation to the power u
    exp_u = (u0.nbits()-1)*sk_cyclo + (hw_u-1)*mk
    # 2-naf
    exp_u_2naf = (len(bits_2naf_u0)-1)*sk_cyclo + (hw2naf_u-1)*mk
    # exponentiation to the power u-1
    exp_u1 = (u1.nbits()-1)*sk_cyclo + (hw_u1-1)*mk
    # 2-naf
    exp_u1_2naf = (len(bits_2naf_u1)-1)*sk_cyclo + (hw2naf_u1-1)*mk

    # Frobenius powers fk_i = x^(q^i) for x in Fq28
    # maybe fk_7, fk_14, fk_21 are cheaper?
    fk_7 = 3*7*m # the formula could be (d-1)*k/d
    # final exp v1:
    # Cost: 2 exp(u-1) + 13 exp(u) +  83 S + 68 M + 12 frob(7) + 14 frob
    hard_part_aux_v1 = 68*mk + 83*sk_cyclo + 14*fk + 12*fk_7

    hard_part_main = 13*exp_u + 2*exp_u1
    hard_part_main_2naf = 13*exp_u_2naf + 2*exp_u1_2naf

    print("cost final exp easy:  {}m".format(easy_part))
    print("cost final exp hard v1:  {}m (with cyclotomic squarings)".format(hard_part_main + hard_part_aux_v1))
    print("cost final exp hard v1:  {}m (2-naf with cyclotomic squarings)".format(hard_part_main_2naf + hard_part_aux_v1))
    print("cost final exp:       {}m".format(easy_part + hard_part_main + hard_part_aux_v1))
    print("cost final exp 2-naf: {}m".format(easy_part + hard_part_main_2naf + hard_part_aux_v1))
    print("\ncost pairing (total)  {}m\n".format(easy_part + min(hard_part_main, hard_part_main_2naf) + hard_part_aux_v1 + min_cost_miller))
