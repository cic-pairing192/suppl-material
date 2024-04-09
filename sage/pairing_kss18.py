from pairing import *

def cofactor_clearing_g1(P, u, omega=None):
    """
    cofactor clearing with endomorphism on G1
    INPUT:
    -`P`: point on a KSS18 curve E
    -`u`: seed for the curve parameters

    The cofactor is c(x) = 7^2/3(x^2+5x+7) and note that with u=14 mod 21, then 7^3 | c
    The endomorphism is psi(P) = (xP*omega, yP) where omega is a primitive cube root of unity mod p
    It has eigenvalue x+2 mod c(x) -> (x+2)^2 + (x+2) + 1 = x^2 + 4x + 4 + x + 2 + 1 = x^2 + 5x + 7 = 0 mod cx
    The other eigenvalue is -x-3
    (x+2)*(-x-3) = -x^2-3x-2x-6 = -x^2 -5x -6 = -1 mod cx
    But actually this is mod (x^2+5x+7)/7 which is 3*cx/343

    A fast cofactor multiplication is then
    P -> Q := [343]P -> Q + [lambda+1] psi(Q)
    where lambda+1 is either u+2+1 = u+3 or (-u-3+1) = -u-2

    here it assumes that lambda = -u-3 and computes 343*(P + [-u-2]psi(P))
    see cofactor_clearing_g1_alt(P, u) for the other option
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((u**7 + 3*u**6 + 4*u**5 + 44*u**4 + 118*u**3 + 71*u**2 + 483*u + 1118)/24) # !!! this is a rational, not an integer, do not use // but use /
    P = 343*P
    # maybe P was of order 343, P could be 0 here... include the third coordinate P[2] that could be 0
    #if not P.is_zero():
    psiP = P.curve()(P[0]*omega, P[1], P[2])
    P = P + (-u-2)*psiP
    return P

def cofactor_clearing_g1_alt(P, u, omega=None):
    """
    cofactor clearing with endomorphism on G1
    INPUT:
    -`P`: point on a KSS18 curve E
    -`u`: seed for the curve parameters

    The cofactor is c(x) = 7^2/3(x^2+5x+7) and note that with u=14 mod 21, then 7^3 | c
    The endomorphism is psi(P) = (xP*omega, yP) where omega is a primitive cube root of unity mod p
    It has eigenvalue x+2 mod c(x) -> (x+2)^2 + (x+2) + 1 = x^2 + 5*x + 7 = 0 mod cx
    The other eigenvalue is -x-3
    (x+2)*(-x-3) = -x^2 -5x -6 = -1 mod cx
    But actually this is mod (x^2+5x+7)/7 which is 3*cx/343

    A fast cofactor multiplication is then
    P -> Q := [343]P -> Q + [lambda+1] psi(Q)
    where lambda+1 is either u+2+1 = u+3 or (-u-3+1) = -u-2

    here it assumes that lambda = u+2 and computes 343*(P + [u+3]psi(P))
    see cofactor_clearing_g1(P, u) for the other option
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((u**7 + 3*u**6 + 4*u**5 + 44*u**4 + 118*u**3 + 71*u**2 + 483*u + 1118)/24) # !!! this is a rational, not an integer, do not use // but use /
        omega = -omega-1
    P = 343*P
    # maybe P was of order 343, P could be 0 here... include the third coordinate P[2] that could be 0
    #if not P.is_zero():
    psiP = P.curve()(P[0]*omega, P[1], P[2])
    P = P + (u+3)*psiP
    return P

def cofactor_clearing_g2(P, u, Fq6, D_twist=True, case=0):
    """
    INPUT:
    - `P`: point on E'(Fp3) containing G2
    - `u`: seed of the KSS18 curve
    - `Fq6`: finite field extension of explicit degree 6 on top of Fq
    - `D_twist`: True/False (M_twist)

    cofactor clearing with endomorphism on G2
    G2 is supposed to be given in compressed representation over GF(p^3)
    That is, P.curve() is E'(Fp3) a sixth twist of E

    The endomorphism is
    psi(P) = twist o Frobenius o untwist (P)

    The eigenvalue is a root of the characteristic polynomial X^2 - t*X + p
    That is one of (t +/- y sqrt(-3))/2
    G2 has order p^3 + 1 - t3' where t3' is the trace of E', the appropriate sixth twist of E(Fp3)
    Let t be the trace of E(Fp), t2 = t^2-2*p and t3 = t*t2-p*t
    y3 = y * (p-t^2) where p = (t^2 + 3*y^2)/4
    Then #E'(Fp3) = p^3 + 1 - (3*y3+t3)/2 = r * c2
    c2 = (x^18 + 15*x^17 + 96*x^16 + 409*x^15 + 1791*x^14 + 7929*x^13 + 27539*x^12 + 81660*x^11 + 256908*x^10 + 757927*x^9 + 1803684*x^8 + 4055484*x^7 + 9658007*x^6 + 19465362*x^5 + 30860595*x^4 + 50075833*x^3 + 82554234*x^2 + 88845918*x + 40301641)/27
    3 | c2
    reduced matrix:
    [    2*x^2 + 3*x        -3*x - 1         x^2 + 2    -3*x^2 - 8*x        8*x + 19 x^3 + 2*x^2 - 1]
    [       -3*x - 1         x^2 + 2      -x^2 - 5*x        8*x + 19 x^3 + 2*x^2 - 1    -2*x^2 - 3*x]
    [        x^2 + 2      -x^2 - 5*x        5*x + 18 x^3 + 2*x^2 - 1    -2*x^2 - 3*x         3*x + 1]
    [     -x^2 - 5*x        5*x + 18 x^3 + 3*x^2 + 1    -2*x^2 - 3*x         3*x + 1        -x^2 - 2]
    [       5*x + 18 x^3 + 3*x^2 + 1    -3*x^2 - 8*x         3*x + 1        -x^2 - 2       x^2 + 5*x]
    [x^3 + 3*x^2 + 1    -3*x^2 - 8*x        8*x + 19        -x^2 - 2       x^2 + 5*x       -5*x - 18]
    for each row [l0 l1 l2 l3 l4 l5] of the matrix, l0 + l1*L + l2*L^2 + l3*L^3 + l4*L^4 + l5*L^5 is a multiple of c2, where L is the eigenvalue mod c2, such that L mod r = q mod r.
    """
    if P.is_zero():
        return P
    # note that all these mu values could be precomputed and stored
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    psi1P = endomorphism_g2_psi_p(P, None, mu, 6, 1, D_twist)
    # xi**((p^2-1)//6) = mu^(p+1)
    mu2 = mu.frobenius()*mu
    #assert mu2 == xi**((p**2-1)//6)
    psi2P = endomorphism_g2_psi_p(P, None, mu2, 6, 2, D_twist)
    # xi**((p^3-1)//6) = mu^(p^2+p+1)
    mu3 = mu.frobenius(2)*mu2
    #assert mu3 == xi**((p**3-1)//6)
    psi3P = endomorphism_g2_psi_p(P, None, mu3, 6, 3, D_twist)
    # xi**((p^4-1)//6) = mu^((p+1)*(p-1)*(p^2+1))
    mu4 = mu2.frobenius(2)*mu2
    #assert mu4 == xi**((p**4-1)//6)
    psi4P = endomorphism_g2_psi_p(P, None, mu4, 6, 4, D_twist)
    # xi**((p^5-1)//6) = mu^(1+p+p^2+p^3+p^4)
    mu5 = mu3 * mu2.frobenius(3)
    #assert mu5 == xi**((p**5-1)//6)
    psi5P = endomorphism_g2_psi_p(P, None, mu5, 6, 5, D_twist)
    if case == 0:
        return (2*u**2+3*u)*P - (3*u+1)*psi1P + (u**2+2)*psi2P - (3*u**2+8*u)*psi3P + (8*u+19)*psi4P + (u**3 + 2*u**2-1)*psi5P
    if case == 1:
        return -(3*u+1)*P + (u**2+2)*psi1P - (u**2+5*u)*psi2P + (8*u+19)*psi3P + (u**3+2*u**2-1)*psi4P - (2*u**2+3*u)*psi5P
    if case == 2:
        return (u**2+2)*P - (u**2+5*u)*psi1P + (5*u+18)*psi2P + (u**3+2*u**2-1)*psi3P - (2*u**2+3*u)*psi4P + (3*u+1)*psi5P
    if case == 3:
        return -(u**2+5*u)*P + (5*u+18)*psi1P + (u**3+3*u**2+1)*psi2P - (2*u**2+3*u)*psi3P + (3*u + 1)*psi4P - (u**2 + 2)*psi5P
    if case == 4:
        return (5*u+18)*P + (u**3+3*u**2+1)*psi1P - (3*u**2+8*u)*psi2P + (3*u+1)*psi3P - (u**2+2)*psi4P + (u**2+5*u)*psi5P
    if case == 5:
        return (u**3+3*u**2+1)*P - (3*u**2+8*u)*psi1P + (8*u+19)*psi2P - (u**2+2)*psi3P + (u**2+5*u)*psi4P - (5*u+18)*psi5P

def subgroup_membership_testing_g1(P, u, omega=None):
    """
    test if P belongs to G1 <=> P has order r
    INPUT:
    -`P`: point on an elliptic curve
    -`u`: seed for the curve parameters

    The order of G1 is r(x) = (x^6 + 37*x^3 + 343)/343 where x=14 mod 21
    The endomorphism is psi(P) = (xP*omega, yP) where omega is a primitive cube root of unity mod p
    It has eigenvalue lambda = x^3 + 18 mod r(x)
    A short formula is (a0, a1) = (19*(x/7)^3 + 1, (x/7)^3) s.t. a0 + a1*lambda == r (exact equality)
    (a0+a1*X).resultant(X^2+X+1) = a0^2 - a0*a1 + a1^2 == rx
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((u**7 + 3*u**6 + 4*u**5 + 44*u**4 + 118*u**3 + 71*u**2 + 483*u + 1118)/24) # !!! this is a rational, not an integer, do not use // but use /
        omega = -omega-1
    a1 = (u//7)**3
    P1 = a1*P
    psiP = P1.curve()(P1[0]*omega, P1[1], P1[2])
    Q = 19*P1 + P + psiP
    return Q.is_zero()

def subgroup_membership_testing_g2(Q, u, Fq6, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^e, e=k/d, a d-twist of E(Fqd)
    - `u`: curve seed
    - `Fq6`: Finite field extension of degree 6 on top of Fq = Fp3
    - `D_twist`: True/False

    Formula
    eq2 := 1 + x*(qx^2 mod rx) + 2*(qx^3 mod rx);
    Resultant(eq2, g2cx) eq 5^18 * 1277459803 / (3^3 * 7^27);
    eq2 div rx eq -35; // 5*7
    this is fine as g2cx has no roots modulo 5, resp. 7
    """
    # note that all these mu values could be precomputed and stored
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    # xi**((p^2-1)//6) = mu^(p+1)
    mu2 = mu.frobenius()*mu
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 6, 2, D_twist)
    # xi**((p^3-1)//6) = mu^(p^2+p+1)
    mu3 = mu.frobenius(2)*mu2
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 6, 3, D_twist)
    R = Q + u*psi2Q + 2*psi3Q
    return R.is_zero()

def subgroup_membership_testing_g2_alt(Q, u, Fq6, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^e, e=k/d, a d-twist of E(Fqd)
    - `u`: curve seed
    - `Fq6`: Finite field extension of degree 6 on top of Fq = Fp3
    - `D_twist`: True/False

    Formula:
    eq1 := -2 + 3*(qx^3 mod rx) + x*(qx^5 mod rx);
    Resultant(eq1, g2cx) eq 2^54 * 1277459803 / (3^3 * 7^27);
    eq1 div rx eq -56; // 8*7
    this is fine as g2cx has no roots modulo 2, resp. 7
    """
    # note that all these mu values could be precomputed and stored
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    # xi**((p^2-1)//6) = mu^(p+1)
    mu2 = mu.frobenius()*mu
    # xi**((p^3-1)//6) = mu^(p^2+p+1)
    mu3 = mu.frobenius(2)*mu2
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 6, 3, D_twist)
    # xi**((p^5-1)//6) = mu^(1+p+p^2+p^3+p^4)
    mu5 = mu3 * mu2.frobenius(3)
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 6, 5, D_twist)
    R = -2*Q + 3*psi3Q + u*psi5Q
    return R.is_zero()

def miller_loop_opt_ate_kss18(Q, P, u):
    """
    Miller loop f_{u,Q}(P) f_{3,Q}(P)^p l_{[u]Q,3\pi(Q)}(P)
    formula is u + 3*p - p^4 = 0 mod r

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters

    The curve coefficient a is zero.
    """
    m, uQ = miller_function_ate(Q, P, 0, u, m0=1)
    # it could be possible the first time of doubling to take into account that both P and Q are in affine coordinates, and also to store the first result to avoid re-computing 2*Q later.
    PP = (P[0], P[1])
    QQ = (Q[0], Q[1], 1, 1)
    l2, Q2 = double_line_j(QQ, PP, 0) # this is already computed in miller_function_ate(...) above
    QQ = (Q[0],Q[1])
    l3, Q3 = add_line_j(Q2, QQ, PP)

    piQ3 = [(Q3[0]).frobenius(), (Q3[1]).frobenius(), (Q3[2]).frobenius(), (Q3[3]).frobenius()]
    li, uQ_3piQ = add_line_j_with_z(uQ, piQ3, PP)

    return m * (l2*l3).frobenius() * li

def miller_loop_opt_ate_kss18_alt(Q, P, u):
    """
    Miller loop f_{u,Q}(P) f_{2,Q}(P)^p l_{[u]Q,2\pi(Q)}(P)
    formula is 1 + uq^2 + 2q^3 = 0 mod r

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters

    The curve coefficient a is zero.
    """
    m, uQ = miller_function_ate(Q, P, 0, u, m0=1)
    # it could be possible the first time of doubling to take into account that both P and Q are in affine coordinates, and also to store the first result to avoid re-computing 2*Q later.
    PP = (P[0], P[1])
    QQ = (Q[0], Q[1], 1, 1)
    l2, Q2 = double_line_j(QQ, PP, 0) # this is already computed in miller_function_ate(...) above

    piQ2 = [(Q2[0]).frobenius(), (Q2[1]).frobenius(), (Q2[2]).frobenius(), (Q2[3]).frobenius()]
    li, uQ_2piQ = add_line_j_with_z(uQ, piQ2, PP)

    return m * l2.frobenius() * li

def miller_loop_opt_ate_aklgl_kss18(Q, P, b_t, u, Fq6, map_Fq6_Fpk, D_twist=False, xi=None, check=False):
    """KSS18 optimal ate Miller loop f_{u,Q}(P) f_{3,Q}(P)^p l_{[u]Q,3\pi(Q)}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `b_t`: the curve coefficient of the twist curve
    - `u`: seed for curve parameters
    - `Fq6`: the extension compatible with the twist
    - `map_Fq6_Fpk`: map from Fq6 (with explicit degree 6) to absolute extension Fpk
    - `D_twist`: is it a D-twist of a M-twist

    The curve coefficient a is zero.
    """
    if xi is None:
        #xi = -Fq6.polynomial().constant_coefficient() # works only for absolute extensions on prime fields
        xi = -Fq6.modulus().constant_coefficient() # works with absolute and towering of extension
    m, uQ = miller_function_ate_aklgl(Q, P, b_t, u, Fq6, D_twist=D_twist)
    if check:
        uQ_test = u*Q
        uQ_aff = (uQ[0]/uQ[2], uQ[1]/uQ[2])
        assert uQ_aff[0] == uQ_test[0]
        assert uQ_aff[1] == uQ_test[1]
    # it could be possible the first time of doubling to take into account that both P and Q are in affine coordinates, and also to store the first result to avoid re-computing 2*Q later.
    PP = (P[0], P[1])
    QQ = (Q[0], Q[1], 1)
    l2, Q2 = double_line_h_a0_twist6_aklgl(QQ,PP,b_t,D_twist=D_twist)
    # this is already computed in miller_function_ate_aklgl(...) above
    QQ = (Q[0],Q[1])
    l3, Q3 = add_line_h_a0_twist6_aklgl(Q2,QQ,PP,D_twist=D_twist)
    # how to compute a frobenius 'before' the twist map?
    if check:
        p = Fq6.characteristic()
        E2 = Q.parent()
    if D_twist:
        # psi_sextic_d_twist(x,y) = (x*xi^2, y*xi^3)
        # in homogeneous coordinates: (X,Y,Z) ~ (X/Z,Y/Z,1) = (x,y)
        # a^6 = xi
        # pi(x*a^2, y*a^3) = (x.frobenius()*a^2.frobenius(), y.frobenius()*a^3.frobenius())
        # a^p = a^((p-1)/6 * 6)*a = xi^((p-1)/6) * a
        # a^2^p = xi^((p-1)/3) * a^2
        # a^3^p = xi^((p-1)/2) * a^3 = -a^3
        w = xi**((p-1)//6)
        piQ3 = [(Q3[0]).frobenius() * w**2, (Q3[1]).frobenius() * w**3, (Q3[2]).frobenius()]
    else:
        w = 1/xi**((p-1)//6)
        piQ3 = [(Q3[0]).frobenius() * w**2, (Q3[1]).frobenius() * w**3, (Q3[2]).frobenius()]
    li, uQ_3piQ = add_line_h_a0_twist6_aklgl_with_z(uQ, piQ3, PP, D_twist=D_twist)
    if D_twist:
        l2_l3 = sparse_sparse_mult_d6_twist(l2[0], l2[1], l2[3], l3[0], l3[1], l3[3], xi, Fq6)
        m_li = sparse_mult_d6_twist(li[0], li[1], li[3], m, xi, Fq6)
    else:
        l2_l3 = sparse_sparse_mult_m6_twist(l2[0], l2[2], l2[3], l3[0], l3[2], l3[3], xi, Fq6)
        m_li = sparse_mult_m6_twist(li[0], li[2], li[3], m, xi, Fq6)
    return map_Fq6_Fpk(m_li) * map_Fq6_Fpk(l2_l3).frobenius()

def final_exp_hard_kss18_v0(f, u):
    """
    formulas from Guide to pairing-based crypto book
    Algorithm 7.16 in chapter 16
    Cost: 6 Sq + 53 M + 29 Frobenius powers + 7 exponentiations to u + 8 Inversions with Frobenius power p^9
    """
    f_ = f.frobenius(9)
    A = f_.frobenius()    # 1
    t0 = A**2             # 2
    B = f_.frobenius(4)   # 3
    t0 = t0 * B           # 4
    fx = f**u
    fx_ = fx.frobenius(9)
    C = fx_.frobenius()   # 5
    t1 = t0 * C           # 6
    B = fx.frobenius(3)   # 7
    t0 = t1 * B           # 8
    fx2 = fx**u
    fx3 = fx2**u
    B = (fx2.frobenius() * fx3.frobenius(2)).frobenius(9) # 9
    t1 = t1 * B           # 10
    A = f.frobenius(2)    # 11
    B = fx_.frobenius(4)  # 12
    t6 = A * B            # 13
    t0 = t0 * B           # 14
    fx4 = fx3**u
    fx5 = fx4**u
    fx5_ = fx5.frobenius(9)
    A = fx5_.frobenius(4) * f.frobenius(5) # 15
    t4 = A * B            # 16
    B = fx                # 17
    t2 = t0 * B           # 18
    t0 = t0 * t1          # 19
    A = fx2.frobenius(3)  # 20
    t1 = A * C            # 21
    fx4_ = fx4.frobenius(9)
    B = fx4_.frobenius(2) # 22
    t3 = A * B            # 23
    t2 = t1 * t2          # 24
    B = fx4_.frobenius(4) # 25
    t5 = t1 * B           # 26
    fx2_ = fx2.frobenius(9)
    B = fx2_.frobenius(2) # 27
    t1 = t2 * B           # 28
    B = fx4.frobenius(3)  # 29
    t8 = t2 * B           # 30
    B = fx2               # 31
    t2 = t1 * B           # 32
    B = fx4_.frobenius()  # 33
    t1 = t1 * B           # 34
    t0 = t2 * t0          # 35
    B = fx5.frobenius(3)  # 36
    t7 = t2 * B           # 37
    t0 = t0**2            # 38
    B = fx2_.frobenius(4) # 39
    t2 = t0 * B           # 40
    fx3_ = fx3.frobenius(9)
    B = fx3_.frobenius() * fx3.frobenius(3) # 41
    t0 = t2 * B           # 42
    t2 = t2 * t8          # 43
    t1 = t0 * t1          # 44
    t0 = t0 * t7          # 45
    t3 = t1 * t3          # 46
    t1 = t1 * t6          # 47
    B = fx3 * fx3_.frobenius(4) # 48
    t6 = t3 * B           # 49
    fx6 = fx5**u
    A = fx6.frobenius(3)  # 50
    t3 = A * B            # 51
    t2 = t6 * t2          # 52
    fx6_ = fx6.frobenius(9)
    B = fx5 * fx5_.frobenius() * fx6_.frobenius(2) * fx3.frobenius(5) # 53
    t6 = t6 * B           # 54
    t2 = t2 * t5          # 55
    fx7_ = fx6_**u
    B = fx6 * fx7_.frobenius(2) * fx4.frobenius(5) # 56
    t5 = t5 * B           # 57
    t2 = t2**2            # 58
    B = fx4 * fx5_.frobenius(2) * fx2.frobenius(5) # 59
    t2 = t2 * B           # 60
    t0 = t0**2            # 61
    t0 = t0 * t6          # 62
    t1 = t2 * t1          # 63
    t2 = t2 * t5          # 64
    t1 = t1**2            # 65
    t1 = t1 * t4          # 66
    t1 = t1 * t0          # 67
    t0 = t0 * t3          # 68
    t0 = t0 * t1          # 69
    t1 = t1 * t2          # 70
    t0 = t0**2            # 71
    t0 = t0 * t1          # 72
    return t0             # 73

def final_exp_hard_kss18(m, u):
    """
    (p^6 - p^3 + 1)/r
    1. replace p by (r*c + t-1)
    2. expand the powers, simplify by r
    3. re-factor r*c into (p+1-t)
    There is a more systematic way to do it: https://eprint.iacr.org/2020/875

    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    px = (x**8 + 5*x**7 + 7*x**6 + 37*x**5 + 188*x**4 + 259*x**3 + 343*x**2 + 1763*x + 2401)/21
    rx = (x**6 + 37*x**3 + 343)/343 # 343 = 7^3
    cx = (x**2 + 5*x + 7)*49/3
    tx = (x**4 + 16*x + 7)/7

    Formula can be deduced from https://eprint.iacr.org/2020/875:
    B = px^5 + px^4*(tx-1) + px^3*(tx-1)^2 + px^2*((tx-1)^3-1) + px*((tx-1)^4 - tx + 1) + (tx-1)^5  - (tx-1)^2
    D = ((tx-1)^6 - (tx-1)^3 + 1) // rx
    cx*B + D == (px^6 - px^3 + 1) // rx

    Magma:
    px := (x^8 + 5*x^7 + 7*x^6 + 37*x^5 + 188*x^4 + 259*x^3 + 343*x^2 + 1763*x + 2401)/21;
    rx := (x^6 + 37*x^3 + 343)/343; // 343 = 7^3
    cx := (x^2 + 5*x + 7)*49/3;
    tx := (x^4 + 16*x + 7)/7;
    B := px^5 + px^4*(tx-1) + px^3*(tx-1)^2 + px^2*((tx-1)^3-1) + px*((tx-1)^4 - tx + 1) + (tx-1)^5  - (tx-1)^2;
    D := ((tx-1)^6 - (tx-1)^3 + 1) div rx;
    cx*B + D eq (px^6 - px^3 + 1) div rx;
    M := Matrix(QQx, 6, 6, [B,0,0,0,0,0, -px,1,0,0,0,0,  0,-px,1,0,0,0,  0,0,-px,1,0,0,  0,0,0,-px,1,0,  0,0,0,0,-px,1]);
    R := LLL(M);

    The 4th row of R corresponds to the formulas in https://link.springer.com/content/pdf/10.1007%2F978-3-642-28496-0_25.pdf
    Fuentes-Castaneda  -- Rodriguez-Henriquez SAC 2011 page 420.
    Claimed cost: 8 Sq + 52 M + Frobenius powers + 7 exponentiations to u
    But then it is possible to factor the leading term (of p^5)
    -> writing Euclidean division by (x^4 + 5*x^3 + 7*x^2 + 3) for each term in p^i, we obtain:

    l0 =      -u**6 - 5*u**5 - 7*u**4 - 21*u**3 - 108*u**2 - 147*u #= (-x^2) * (x^4 + 5*x^3 + 7*x^2 + 3) + 21 * (-x^3 - 5*x^2 - 7*x)
    l1 =        5*u**5 + 25*u**4 + 35*u**3 + 98*u**2 + 505*u + 686 #= (5*x) * (x^4 + 5*x^3 + 7*x^2 + 3) + 98 * (x^2 + 5*x + 7)
    l2 = u**7 + 5*u**6 + 7*u**5 + 19*u**4 + 98*u**3 + 133*u**2 - 6 #= (x^3 + 19) * (x^4 + 5*x^3 + 7*x^2 + 3) + 1 * (-63)
    l3 =  -2*u**6 - 10*u**5 - 14*u**4 - 35*u**3 - 181*u**2 - 245*u #= (-2*x^2) * (x^4 + 5*x^3 + 7*x^2 + 3) + 35 * (-x^3 - 5*x^2 - 7*x)
    l4 =        3*u**5 + 15*u**4 + 21*u**3 + 49*u**2 + 254*u + 343 #= (3*x) * (x^4 + 5*x^3 + 7*x^2 + 3) + 49 * (x^2 + 5*x + 7)
    l5 =                               -u**4 - 5*u**3 - 7*u**2 - 3 #= (-1) * (x^4 + 5*x^3 + 7*x^2 + 3) + 1 * (0)

    Then we write the Euclidean division by (x^2 + 5*x + 7) for each remainder. We obtain
    Our own formula: assuming easy inversion f^(-1) = f^(p^9)
    e4 eq (x^4 + 5*x^3 + 7*x^2 + 3)*(-px^5 + 3*x*px^4 -2*x^2*px^3 + (x^3+16 + 3)*px^2 + 5*x*px - x^2) + 7*((x^2 + 5*x + 7)*(7*(px^4 + 2*px) - x*(5*px^3 + 3)) - 9*px^2);
    e4 eq (x^4 + 5*x^3 + 7*x^2 + 3)*(-px^5 + x*(3*px^4 + 5*px) -x^2*(2*px^3 + 1) + x^3*px^2 + (16 + 3)*px^2) + 7*((x^2 + 5*x + 7)*(7*(px^4 + 2*px) - x*(5*px^3 + 3)) - 9*px^2);

    Cost: 7 exp(u) + 19 S + 26 M + 10 Frobenius powers + 6 Inversions with Frobenius power p^9

    """
    # 1. x^2 + 5*x + 7
    m1 = m**u
    m2 = m1**u
    m01 = m * m1 # m^(x+1)           # M
    f = m2 * ((m01**2 * m)**2 * m01) # 3M + 2S
    #assert f == m**(u**2 + 5*u + 7)
    f1 = f.frobenius(4) * f.frobenius()**2 # M + S
    fu = f**u #
    fu_ = fu.frobenius(9) # inv
    f2 = fu_.frobenius(3)
    f12 = f1 * f2                               # M
    f3 = (f12**2 * (f1 * fu_))**2 * (f12 * fu_) # 4M + 2S
    #f3 = f1**7 * f2**5 * fu_**3
    f9 = (m.frobenius(2)).frobenius(9)
    f9 = ((f9**2)**2)**2 * f9                  # 3 S + M
    f4 = f3 * f9                               # M
    f5 = f4.frobenius(9) * ((f4**2)**2)**2     # 3 S + M
    #i4 = 49 * (u**2 + 5*u + 7)
    #i3 = 35 * (-u**3 - 5*u**2 - 7*u)
    #i2 = -63
    #i1 = 98 * (u**2 + 5*u + 7)
    #i0 = 21 * (-u**3 - 5*u**2 - 7*u)
    # assert 7*((x^2 + 5*x + 7)*(7*(px^4 + 2*px) - x*(5*px^3 + 3)) - 9*px^2) == i0 + i1*px + i2 * px^2 + i3*px^3 + i4*px^4
    #assert f5 == m**i0 * m.frobenius()**i1 * m.frobenius(2)**i2 * m.frobenius(3)**i3 * m.frobenius(4)**i4
    g = fu**u * m**2 * m # m^(x^4 + 5*x^3 + 7*x^2 + 3) # 2M + S + exp(u)
    #assert g == m**(u**4 + 5*u**3 + 7*u**2 + 3)
    gu = g**u
    gu2 = gu**u
    gu3 = gu2**u
    g5 = (g.frobenius(5)).frobenius(9)
    #gx = gu.frobenius()**5 * gu.frobenius(4)**3
    gup = gu.frobenius()
    gup4 = gu.frobenius(4)
    gx = (gup**2 * gup4)**2 * gup * gup4 # 2 S + 3M
    gx2 = (gu2 * gu2.frobenius(3)**2).frobenius(9) #S + M
    gx3 = gu3.frobenius(2)
    #g2 = (g**19).frobenius(2)
    g4 = (g**2)**2                            # 2S
    g2 = ((g4)**2)**2 * g4 * g.frobenius(9)   # 2S + 2M
    #assert g2 == g**19
    g2 = g2.frobenius(2)
    h = (g5 * gx * gx2 * gx3 * g2) * f5
    #assert h == m.frobenius(5)**l5 * m.frobenius(4)**l4 * m.frobenius(3)**l3 * m.frobenius(2)**l2 * m.frobenius()**l1 * m**l0
    return h

def final_exp_hard_kss18_v1(m, u):
    """
    Final exponentiation, hard part 3/49*u**2 * (p^6 - p^3 + 1)/r

    From Faster Final Exponentiation on the KSS18 Curve,
    Shiping Cai, Zhi Hu, and Chang-An Zhao
    https://eprint.iacr.org/2021/1309
    7 exp(u) + 24 M + 11 S + 7 Frob(9) + 5 Frobenius
    """
    t0 = m**u
    t1 = m**2
    t4 = m * t1                     # m**3
    t2 = t1 * t4                    # m**5
    t1 = t1 * t2                    # m**7
    t2 = (t0 * t2)**u               # m**(5*u + u^2)
    c = t1 * t2                     # m**(7 + 5*u + u^2) = m**l6
    #l6 = (7 + 5*u + u**2); assert c == m**l6
    t0 = (c**2 * c)**2 * c          # m**(7*l6)
    t1 = t0**2                      # c**14 = m**(14*l6)
    t3 = (c**u).frobenius(9)        # c**(-u) = m**(-u*l6)
    c = (t3**u).frobenius(9) * t4   # c**(u^2) * m**3 = m**(u^2*l6 + 3) = m**l5
    #l5 = (u**2 * l6 + 3); assert c == m**l5
    t4 = c**u                       # m**(u*l5)
    t2 = t4.frobenius(9)            # m**(-u*l5)
    t41 = t4 * t1                   # m**(u*l5+14*l6)
    t1 = t41**2 * t41 * t0          # m**(3*u*l5 + 42*l6 + 7*l6) = m**(3*u*l5 + 49*l6)
    t2 = (t2**u).frobenius(9)       # m**(u**2*l5)
    t0 = t1.frobenius(9)            # m**(-3*u*l5 - 49*l6)
    #l4 = -3*u*l5 - 49*l6; assert t0 == m**l4
    t1 = t0**2 * t4   # m**(2*l4 + u*l5)
    #l1 = 2*l4 + u*l5; assert t1 == m**l1
    t1 = t1.frobenius()
    t4 = t1 * (c.frobenius() * t0).frobenius(4) # m**(l1*p + l4*p^4 + l5*p^5)
    #assert t4 == (m**l1).frobenius() * (m**l4).frobenius(4) * (m**l5).frobenius(5)
    t3_ = t3.frobenius(9)
    t3 = (t3_**2 * t3_)**2 * t3_  # m**(7*u*l6)
    t1 = t3**2                    # m**(14*u*l6)
    t0 = (t1 * t2)**2 * t3        # m**(2*u^2*l5 + 35*u*l6)
    #l3 = 2*u**2*l5 + 35*u*l6; assert t0 == m**l3
    t3 = t1 * t3                  # m**(21*u*l6)
    t1 = t2 * t3                  # m**(u**2*l5 + 21*u*l6)
    t4 = t1 * t4                  # m**(u**2*l5 + 21*u*l6 + l1*p + l4*p4 + l5*p5)
    t1 = (t1**u).frobenius(9)     # m**(-u**3*l5 - 21*u**2*l6)
    t2 = c**2                     # m**(2*l5)
    t1 = t1 * t2                  # m**(-u**3*l5 + 2*l5 - 21*u**2*l6)
    t0 = (t0.frobenius() * t1).frobenius(2)
    c = t4 * t0
    #l0 = 2*l3 + u*l4
    #l2 =-u*l0 + 2*l5
    return c

def final_exp_hard_kss18_v2(m, u):
    """
    Row 3 of LLL reduced matrix
    ee = (u^4 + 5*u^3 + 7*u^2 + 3)*(1 + 18*q^3 + u*q^2*(5 + 3*q^3) + u^2*q*(-1 - 2*q^3) + u^3 *q^3) \
         + (u^2 + 5*u + 7) * (7^2*q^2*(2 + q^3) + 7*u*q*(-3 - 5*q^3)) - 63*q^3

    ee == (9*u^3 + 147)/(49)*(q^6 - q^3 + 1)/r

    Row 4 of LLL reduced matrix

    ee = (u^4 + 5*u^3 + 7*u^2 + 3)*(q^2*(18 + 1 - q^3) + u*q*(5 + 3*q^3) + u^2*(-1 - 2*q^3) + u^3*q^2) \
    + (u^2 + 5*u + 7) * (7^2*q*(2 + q^3) + 7*u*(-3 - 5*q^3)) - 63*q^2

    ee == -3*u^2/49*(q^6 - q^3 + 1)/r

    u^2 + 5*u + 7 = (u+2)^2 + (u+2) + 1 = (u+1)^2 + 3*(u + 2) = (u+3)^2 - u - 2
    or, 5 = b101
        7 = b111

    Cost: 2 exp(u+2) + 5*exp(u) + 17 S + 23 M + 6 Frob(3) + 4 Frob
    """
    u2 = abs(u+2)
    mu = m**u2
    muu = mu**u2
    if u < 0:
        mu = mu.conjugate()
    ma = muu * mu * m
    #assert ma == m**(u**2 + 5*u + 7)
    #q = m.parent().characteristic()
    m2 = m**2
    m3 = m2 * m
    u_ = abs(u)
    mau = ma**u_
    mauu = mau**u_
    if u < 0:
        mau = mau.conjugate()
    mb = mauu * m3
    # 18 = 16 + 2 = b10010
    # 63 = 64 - 1 = b100000-
    mb18_m63 = (((((m2.conjugate()**2) * mb)**2)**2)**2 * mb)**2 * m
    mb18_m63 = mb18_m63.frobenius(3)
    #assert mb18_m63 == mb**(18*q**3) * m**(-63*q**3)

    mbu = mb**u_
    mbuu = mbu**u_
    mbuuu = mbuu**u_
    if u < 0:
        mbu = mbu.conjugate()
        mbuuu = mbuuu.conjugate()

    # mbu^(q^2*(5 + 3*q^3)) * mau^(-7*q*(5*q^3 + 3))
    mbu1 = mbu.frobenius(2)
    mau1 = mau.conjugate().frobenius()
    mau1 = ((mau1**2)**2)**2 * mau1.conjugate() # ^7
    f1 = mbu1 * mau1.frobenius(3)
    f2 = mbu1.frobenius(3) * mau1
    # f1^5 * f2^3
    mab1 = (f1**2 * f2)**2 * f1 * f2
    #assert mab1 == mb**(u*q**2*(5 + 3*q**3)) * ma**(-7*u*q*(5*q**3 + 3))

    # mb^(u^2*-q*(1 + 2*q^3)) * ma^(7^2*q^2*(2 + q^3))
    mbu2 = mbuu.frobenius().conjugate()
    # ^49 = 32 + 16 + 1
    ma2 = ((((ma**2 * ma)**2)**2)**2)**2 * ma
    #assert ma2 == ma**49
    ma2 = ma2.frobenius(2)
    f1 = mbu2 * ma2.frobenius(3)
    f2 = mbu2.frobenius(3) * ma2
    mab2 = f1 * f2**2
    #assert mab2 == mb**(-u**2*q*(1 + 2*q**3)) * ma**(7**2*q**2*(2 + q**3))

    #ee = (u**4 + 5*u**3 + 7*u**2 + 3)*(1 + 18*q**3 + u*q**2*(5 + 3*q**3) + u**2*q*(-1 - 2*q**3) + u**3 *q**3) \
    #     + (u**2 + 5*u + 7) * (7**2*q**2*(2 + q**3) + 7*u*q*(-3 - 5*q**3)) - 63*q**3

    r = mb18_m63 * mb * mbuuu.frobenius(3) * mab1 * mab2
    #assert r == m**ee
    return r
