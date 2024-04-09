"""
Tate, ate, optimal Tate, optimal ate pairings on BN curves
Date: 2023
From https://gitlab.inria.fr/zk-curves/snark-2-chains
+ Group operations: cofactor clearing and subgroup membership testing for G2
"""
from pairing import *

def cofactor_clearing_g2_bn(Q, u, Fq6, D_twist=True):
    """
    G2 cofactor h2 = 36*x^4 + 36*x^3 + 30*x^2 + 6*x + 1
    lambda mod h2 = (-48*x^3 - 30*x^2 - 20*x + 2)/5
    there is one choice of root of X^2-t*X+p that maps to p mod r, so there is one choice of eigenvalue for psi
    v = [6*x,  -1,   3,  -1]
    Q -> 6*u*Q -psi(Q) + 3*psi2(Q) - psi3(Q)
      =  3*(2*u*Q + psi2(Q)) -psi(Q + psi2(Q))
    """
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu

    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 6, 2, D_twist)
    u2Q = 3*(2*u*Q + psi2Q)
    psi1Q = endomorphism_g2_psi_p(Q + psi2Q, None, mu, 6, 1, D_twist)
    return u2Q - psi1Q

def membership_testing_g2_bn_ehgp(Q, u, Fq6, D_twist=True):
    """
    G2 membership testing from ePrint 2022/352 Y. El Housni, A. Guillevic, T. Piellard

    INPUT:
    - `Q`: point on compresed G2 in E'(p2)
    - `u`: curve seed

    formula that test if psi has eigenvalue 6*u^2
    [6*u^2] - psi(Q) =? 0
    no condition on u
    """
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    uQ = (6*u**2)*Q
    psiQ = endomorphism_g2_psi_p(Q, None, mu, 6, 1, D_twist)
    return (uQ - psiQ).is_zero()

def membership_testing_g2_bn(Q, u, Fq6, D_twist=True):
    """
    G2 membership testing from ePrint 2022/996

    INPUT:
    - `Q`: point on compresed G2 in E'(p2)
    - `u`: curve seed

    formula from alternative optimal ate pairing formula from Vercauteren' Optimal Pairing paper, 2009
    [x+1, x, x, -2*x]
    [x+1] Q + psi([x]Q) + psi2([x]Q) - psi3([2x]Q) =? 0
    condition: u != 5422 mod 21961 (BN-P446 example in ePrint 2022/348: Yu Dai, Kaizhan Lin, Chang-An Zhao, Zijian Zhou)
    """
    assert ((u - 5422) % 21961) != 0
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu
    uQ = u*Q
    psi2_uQ = endomorphism_g2_psi_p(uQ, None, mu2, 6, 2, D_twist)
    u1Q = uQ + Q
    psi2_2uQ = 2*psi2_uQ
    return (u1Q + psi2_uQ + endomorphism_g2_psi_p(uQ-psi2_2uQ, None, mu, 6, 1, D_twist)).is_zero()

def membership_testing_g2_bn_alt(Q, u, Fq6, D_twist=True):
    """
    G2 membership testing, technique from ePrint 2022/348

    INPUT:
    - `Q`: point on compressed G2 in E'(Fp2)
    - `u`: curve seed

    another formula similar to the other ones
    [x, 3*x+1, x+1, 0] (see miller_loop_opt_ate_bn_alt2)
    [x] Q + psi([3*x+1]Q) + psi2([x+1]Q) =? 0
    condition: u != -12 mod 241
    """
    assert ((u + 12) % 241) != 0
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu
    uQ = u*Q
    u1Q = uQ + Q
    u2Q = 2*uQ
    u3Q = u2Q + u1Q
    psi_u3Q = endomorphism_g2_psi_p(u3Q, None, mu, 6, 1, D_twist)
    psi2_u1Q = endomorphism_g2_psi_p(u1Q, None, mu2, 6, 2, D_twist)
    return (uQ + psi_u3Q + psi2_u1Q).is_zero()

def miller_loop_ate_bn(Q, P, u):
    """
    Return f_{6*u^2,Q}(P) where t(u)-1 = 6*u^2

    INPUT:
    - `Q`: r-torsion point on G2 not compressed, in E(Fpk) or E(Fqd)
    - `P`: r-torsion point on G1 in E(Fp)
    - `u`: seed for the curve coefficients

    Return a value m in the field of coefficients of the coordinates of Q
    """
    T = 6*u**2 # always positive
    return miller_function_ate(Q, P, 0, T)

def miller_loop_opt_ate_bn(Q, P, u):
    """
    Return f_{6*u+2,Q}(P) l_{[6u+2]Q,pi(Q)}(P) l_{[6u+2]Q+pi(Q), pi^2(-Q)}(P)

    INPUT:
    - `Q`: r-torsion point on G2 not compressed, in E(Fpk) with absolute extension Fpk allowing frobenius
    - `P`: r-torsion point on G1 in E(Fp)
    - `u`: seed for the curve coefficients

    The Frobenius map in Sage can be used only on absolute extensions.
    assume Q has coordinates in Fp12 as an absolute extension over Fp.

    Alternative formula with one more Frobenius on G2 instead to compute pi^3(Q):
    f_{6*u+2,Q}(P) l_{[6u+2]Q,pi(Q)}(P) l_{-pi^2(Q), pi^3(Q)}(P)
    """
    T = 6*u+2
    if T < 0:
        m, S = miller_function_ate((Q[0], -Q[1]), P, 0, -T)
    else:
        m, S = miller_function_ate(Q, P, 0, T)
    pQ = (Q[0].frobenius(), Q[1].frobenius())
    ln1, R1 = add_line_j(S, pQ, (P[0], P[1]))
    p2_Q = (Q[0].frobenius(2), -Q[1].frobenius(2))
    # alternative formula:
    # p3Q = (p2_Q[0].frobenius(), -p2_Q[1].frobenius())
    # ln2, R2 = add_line_affine_j(p2_Q, p3Q, (P[0],P[1]))
    # return m * ln1 * ln2
    ln2, R2 = add_line_j(R1, p2_Q, (P[0],P[1]))
    return m * ln1 * ln2

def miller_loop_opt_ate_bn_2naf(Q, P, u):
    """
    Return f_{6*u+2,Q}(P) l_{[6u+2]Q,pi(Q)}(P) l_{[6u+2]Q+pi(Q), pi^2(-Q)}(P)
    with the Miller loops in 2-naf form

    INPUT:
    - `Q`: r-torsion point on G2 not compressed, in E(Fpk) with absolute extension Fpk allowing frobenius
    - `P`: r-torsion point on G1 in E(Fp)
    - `u`: seed for the curve coefficients

    The Frobenius map in Sage can be used only on absolute extensions.
    assume Q has coordinates in Fp12 as an absolute extension over Fp.

    Alternative formula with one more Frobenius on G2 instead to compute pi^3(Q):
    f_{6*u+2,Q}(P) l_{[6u+2]Q,pi(Q)}(P) l_{-pi^2(Q), pi^3(Q)}(P)
    """
    T = 6*u+2
    if T < 0:
        m, S = miller_function_ate_2naf((Q[0], -Q[1]), P, 0, -T)
    else:
        m, S = miller_function_ate_2naf(Q, P, 0, T)
    pQ = (Q[0].frobenius(), Q[1].frobenius())
    ln1, R1 = add_line_j(S, pQ, (P[0], P[1]))
    p2_Q = (Q[0].frobenius(2), -Q[1].frobenius(2))
    # alternative formula:
    # p3Q = (p2_Q[0].frobenius(), -p2_Q[1].frobenius())
    # ln2, R2 = add_line_affine_j(p2_Q, p3Q, (P[0],P[1]))
    # return m * ln1 * ln2
    ln2, R2 = add_line_j(R1, p2_Q, (P[0], P[1]))
    return m * ln1 * ln2

def miller_loop_opt_ate_bn_alt1(Q, P, u):
    """
    alternative optimal ate pairing formula from Vercauteren' Optimal Pairing paper, 2009
    [x+1, x, x, -2*x]
    f_{x+1,Q}(P) * f_{x,Q}(P)^p * f_{x,Q}(P)^p^2 * f_{-2*x,Q}(P)^p^3
    * l_{[x+1]Q,pi2([x]Q)}(P) * l_{[x]Q,pi2([-2*x]Q)}(P)^p
    """
    l = 6*u**2
    assert (u+1 + u*l + u*l**2 - 2*u*l**3) % (36*u**4 + 36*u**3 + 18*u**2 + 6*u + 1) == 0
    if u < 0:
        f_u, S = miller_function_ate((Q[0], -Q[1]), P, 0, -u)
    else:
        f_u, S = miller_function_ate(Q, P, 0, u)
    # add line to get f_{u+1}
    l1, S1 = add_line_j(S, (Q[0], Q[1]), (P[0], P[1]))
    #f_u1 = f_u * l1
    p2S = (S[0].frobenius(2), S[1].frobenius(2), S[2].frobenius(2), S[3].frobenius(2))
    # double with -pi2(S) to get f_{-2u, pi2(Q)}
    l2, p2S2_ = double_line_j((p2S[0], -p2S[1], p2S[2], p2S[3]), (P[0], P[1]), 0)
    #f_{-2u, pi2(Q)} = (1/f_u**2).frobenius(2) * l2
    # to make the pairing bilinear, add term l_{[x+1]Q, pi2(uQ)}(P)
    l3, S3 = add_line_j_with_z(S1, p2S, (P[0], P[1]))
    # to make the pairing bilinear, add term (l_{[x]Q, -pi2(uQ)}(P)).frobenius()
    l5, S5 = add_line_j_with_z(S, p2S2_, (P[0], P[1]))
    # cost 5 M-full + 2 M-sparse-sparse + S + Frob(2) + Frob()
    f_u_p2 = f_u.frobenius(2)
    return f_u * f_u_p2 * (l1 * l3) * (f_u * (f_u_p2**2).conjugate() * (l2 * l5)).frobenius()

def miller_loop_opt_ate_bn_alt2(Q, P, u):
    """
    new alternative optimal ate pairing formula, Feb 28, 2023
    [x, 3*x+1, x+1, 0]
    f_{x,Q}(P) * f_{3*x+1,Q}(P)^p * f_{x+1,Q}(P)^p^2 * l_{[x]Q,pi2([x+1]Q)}(P)
    """
    l = 6*u**2
    assert (u + (3*u+1)*l + (u+1)*l**2) % (36*u**4 + 36*u**3 + 18*u**2 + 6*u + 1) == 0
    if u < 0:
        f_u, S = miller_function_ate((Q[0], -Q[1]), P, 0, -u)
    else:
        f_u, S = miller_function_ate(Q, P, 0, u)
    # add line to get f_{u+1}
    l1, S1 = add_line_j(S, (Q[0], Q[1]), (P[0], P[1]))
    # f_{u+1} = f_u * l1
    # double line to get f_{2u}
    l2, S2 = double_line_j(S, (P[0], P[1]), 0)
    # f_{2u} = f_u**2 * l2
    # add line [u+1]Q with [2u]Q to get f_{3u+1}
    l3, S3 = add_line_j_with_z(S2, S1, (P[0], P[1]))
    # f_{3u+1} = f_2u * f_{u+1} * l3 = f_u**2 * f_u * l1 * l2 * l3
    # l_{[x]Q, pi2([x+1]Q)}(P)
    p2S1 = (S1[0].frobenius(2), S1[1].frobenius(2), S1[2].frobenius(2), S1[3].frobenius(2))
    l5, S5 = add_line_j_with_z(S, p2S1, (P[0], P[1]))
    # cost 4 M-full + 1 M-sparse-sparse + 2 M-full-sparse + S + Frob(2) + Frob()
    f_u1 = f_u * l1
    return f_u * f_u1.frobenius(2) * (f_u**2 * f_u1 * l2 * l3).frobenius() * l5

def miller_loop_opt_tate_bn(P, Q, u):
    """
    Return f_{2*u+1,P}(Q) (f_{6*u^2+2*u, P}(Q))^(p^2)

    INPUT:
    - `P`: r-torsion point on G1 in E(Fp)
    - `Q`: r-torsion point on G2 not compressed, in E(Fpk) with absolute extension Fpk allowing frobenius
    - `u`: seed of the curve parameters

    The Frobenius map in Sage can be used only on absolute extensions.
    assume Q has coordinates in Fp12 as an absolute extension over Fp.

    Assuming that psi: (x,y) -> (omega*x, -y) has eigenvalue (tx-1)^2 mod r = -36*x^3-18*x^2-6*x-1
    it is the same as f_{2*u+1,P}(Q) f_{6*u^2+2*u, psi(P)}(Q)
    Computation can be improved as:
    m = f_{2*u, P}(Q); return m * l_{[2*u]P, P}(Q) ((m)_{3*u+1, [2*u]P}(Q))^(p^2)
    """
    if u < 0:
        m2u, P2u = miller_function_tate((P[0],-P[1]),Q,0,-2*u)
    else:
        m2u, P2u = miller_function_tate(P,Q,0,2*u)
    v = 3*u+1
    # affine coordinates for [2*u]*P
    z = 1/P2u[2]
    z2 = z**2
    z3 = z2 * z
    P2u = (P2u[0]*z2, P2u[1]*z3)
    ln, P2u1 = add_line_affine_j((P2u[0],P2u[1]),(P[0],P[1]),(Q[0],Q[1]))
    if v < 0:
        # invert m2u because m2u^v = m2u^(-|v|) = (1/m2u)^|v|
        mv, Pv = miller_function_tate((P2u[0],-P2u[1]),Q,0,-v, m0=m2u.frobenius(6))
    else:
        mv, Pv = miller_function_tate(P2u,Q,0,v, m0=m2u)
    return m2u * ln * mv.frobenius(2)

def miller_loop_opt_tate_bn_alt(P, Q, u):
    """
    Return f_{6*u^2+4*u+1,P}(Q) (f_{-2*u-1, psi(P)}(Q))^(p^2)

    INPUT:
    - `P`: r-torsion point on G1 in E(Fp)
    - `Q`: r-torsion point on G2 not compressed, in E(Fpk) with absolute extension Fpk allowing frobenius
    - `u`: seed of the curve parameters

    The Frobenius map in Sage can be used only on absolute extensions.
    assume Q has coordinates in Fp12 as an absolute extension over Fp.

    Assuming that psi: (x,y) -> (omega*x, -y) has eigenvalue (tx-1)^2 mod r = -36*x^3-18*x^2-6*x-1
    it is the same as f_{6*u^2+4*u+1,P}(Q) f_{-2*u-1, psi(P)}(Q)
    Computation can be improved as (with inversion as powering to p^6)
    m = f_{2*u, P}(Q); return (m * l_{[2*u]P, P})^(p^8) (m)_{3*u+2, [2*u]P}(Q) l_{[6u^2+4u]P, P}(Q)
    """
    if u < 0:
        m2u, P2u = miller_function_tate((P[0],-P[1]),Q,0,-2*u)
    else:
        m2u, P2u = miller_function_tate(P,Q,0,2*u)
    v = 3*u+2
    # affine coordinates for [2*u]*P
    z = 1/P2u[2]
    z2 = z**2
    z3 = z2 * z
    P2u = (P2u[0]*z2, P2u[1]*z3)
    ln, P2u1 = add_line_affine_j((P2u[0],P2u[1]),(P[0],P[1]),(Q[0],Q[1]))
    if v < 0:
        # invert m2u because m2u^v = m2u^(-|v|) = (1/m2u)^|v|
        mv, Pv = miller_function_tate((P2u[0],-P2u[1]),Q,0,-v, m0=m2u.frobenius(6))
    else:
        mv, Pv = miller_function_tate(P2u,Q,0,v, m0=m2u)
    ln2, Pv1 = add_line_j(Pv,(P[0],P[1]),(Q[0],Q[1]))
    return (m2u * ln).frobenius(8) * (mv * ln2)

def miller_loop_opt_tate_bn_aklgl_a0(P, Q, b, u, Fq6, map_Fq6_Fpk, D_twist=False):
    """
    INPUT:
    - `P`: on E (for G1)
    - `Q`: on E2 over Fp2 (the twist, for G2)
    - `b`: curve coefficient of E (to add and double P)
    - `u`: seed of the curve parameters
    - `Fq6`: degree 6 extension over Fq
    - `D_twist`: True/False (about E2)

    Assuming that psi: (x,y) -> (omega*x, -y) has eigenvalue (tx-1)^2 mod r = -36*x^3-18*x^2-6*x-1
    Return f_{2*u+1,P}(Q) f_{6*u^2+2*u, psi(P)}(Q)
    Alt formula: f_{6*u^2+4*u+1,P}(Q) f_{-2*u-1, psi(P)}(Q)

    can be improved as
    m = f_{2*u, P}(Q)
    Return m * l_{[2*u]P, P}(Q) ((m)_{3*u+1, [2*u]P}(Q))^(p^2)

    alt formula can be improved as (with inversion as powering to p^6)
    m = f_{2*u, P}(Q)
    Return (m * l_{[2*u]P, P})^(p^8) (m)_{3*u+2, [2*u]P}(Q) l_{[6u^2+4u]P, P}(Q)
    remember to swap the value D_twist for Tate (compared to ate)
    """
    if u < 0:
        m2u, P2u = miller_function_tate_aklgl((P[0],-P[1]),Q,b,-2*u,Fq6,D_twist=D_twist)
    else:
        m2u, P2u = miller_function_tate_aklgl(P,Q,b,2*u,Fq6,D_twist=D_twist)
    v = 3*u+1
    # affine coordinates for [2*u]*P from homogeneous coord
    z = 1/P2u[2]
    P2u = (P2u[0]*z, P2u[1]*z)
    ln, P2u1 = add_line_h_a0_twist6_aklgl((P2u[0],P2u[1],1), (P[0],P[1]), (Q[0],Q[1]), D_twist=not D_twist)
    if v < 0:
        # invert m2u because m2u^v = m2u^(-|v|) = (1/m2u)^|v|
        # m2u.frobenius(6) is not available because m2u is in a relative extension, Sage does not know how to do it
        coeffs_m2u = m2u.list() # a list of 6 coefficients, each coefficient is in Fq = Fp2 where Frobenius stands
        for i in range(1, len(coeffs_m2u), 2):
            coeffs_m2u[i] = -coeffs_m2u[i]
        m2u_p6 = Fq6(coeffs_m2u)
        #m2u_inv = 1/m2u
        mv, Pv = miller_function_tate_aklgl((P2u[0],-P2u[1]),Q,b,-v,Fq6,D_twist=D_twist,m0=m2u_p6)
    else:
        mv, Pv = miller_function_tate_aklgl(P2u,Q,b,v,Fq6,D_twist=D_twist,m0=m2u)
    xi = -Fq6.modulus().constant_coefficient()
    if not D_twist:
        m2u_ln = sparse_mult_d6_twist(ln[0],ln[1],ln[3], m2u, xi, Fq6)
    else:
        m2u_ln = sparse_mult_m6_twist(ln[0],ln[2],ln[3], m2u, xi, Fq6)
    return map_Fq6_Fpk(m2u_ln) * (map_Fq6_Fpk(mv)).frobenius(2)

def frobenius_map_G2(Q, xi_p13, xi_p12):
    """
    map (xQ,yQ) -> (xQ^p * xi^((p-1)/3), yQ^p * xi^((p-1)/2)) = (p % r)*Q
    INPUT:
    -`Q`: point on E'(Fq) (the compressed form of G2) of order r
    For D_twist:
    -`xi_p13`: xi^((p-1)/3)
    -`xi_p12`: xi^((p-1)/2)
    For M-twist:
    -`xi_p13`: 1/xi^((p-1)/3)
    -`xi_p12`: 1/xi^((p-1)/2)

    Return: a point pi(Q) on E'(Fq)
    """
    pQ = ((Q[0]).frobenius() * xi_p13, (Q[1]).frobenius() * xi_p12)
    return Q.curve()(pQ)

def miller_loop_opt_ate_bn_aklgl(Q,P,b_t,u,Fq6,D_twist=False,xi=None):
    """return f_{6u+2,Q}(P) * l_{[6u+2]Q,pi(Q)}(P) * l_{[6u+2]Q+pi(Q), pi^2(-Q)}(P)

    Optimized optimal ate Miller loop for BN curves and AKLGL formulas
    Q, P are r-torsion points in G2, G1, in affine coordinates,
    u is the seed (integer) of the curve coefficients

    If u < 0, then f_{|u|, -Q}(P) is computed thanks to the formula
    f_{ij,Q} = f_{i,Q}^j*f_{j,[i]Q} and with i=-1, j=|u|:
    f_{-|u|,Q} = f_{-1,Q}^u*f_{|u|,-Q} and since f_{-1,Q} is a vectical line,
    it is discarded: f_{-|u|,Q} = f_{|u|,-Q}.
    """
    if xi is None:
        xi = -Fq6.modulus().constant_coefficient() # works with absolute and towering of extension
    P_ = (P[0], P[1])
    T = 6*u + 2
    if T < 0:
        Q_ = (Q[0], -Q[1], 1)
        m_T, TQ = miller_function_ate_aklgl(Q_, P_, b_t, -T, Fq6, D_twist=D_twist)
    else:
        Q_ = (Q[0], Q[1], 1)
        m_T, TQ = miller_function_ate_aklgl(Q_, P_, b_t, T, Fq6, D_twist=D_twist)
    # pQ with Q in E(Fp2) (before applying the twist)
    # then the output is, with xi^((p-1)/3), xi^((p-1)/2)
    p = Fq6.characteristic()
    xi_p16 = xi**((p-1)//6)
    if not D_twist:
        xi_p16 = 1/xi_p16
    xi_p13 = xi_p16**2
    xi_p12 = xi_p13 * xi_p16
    pQ = ((Q[0]).frobenius() * xi_p13, (Q[1]).frobenius() * xi_p12)
    # xi^((p^2-1)/6) = xi^((p-1)/6)*xi^(p+1)
    xi_p216 = xi_p16.frobenius() * xi_p16
    xi_p213 = xi_p216**2
    xi_p212 = xi_p213 * xi_p216
    p2_Q = (Q[0].frobenius(2) * xi_p213, -Q[1].frobenius(2) * xi_p212)

    l1, TpQ = add_line_h_a0_twist6_aklgl(TQ, pQ, P_, D_twist=D_twist)
    l2, Tp_p2Q = add_line_h_a0_twist6_aklgl(TpQ, p2_Q, P_, D_twist=D_twist)
    if D_twist:
        l1l2 = sparse_sparse_mult_d6_twist(l1[0], l1[1], l1[3], l2[0], l2[1], l2[3], xi, Fq6)
    else:
        l1l2 = sparse_sparse_mult_m6_twist(l1[0], l1[2], l1[3], l2[0], l2[2], l2[3], xi, Fq6)
    return m_T * l1l2

def miller_loop_opt_ate_bn_aklgl_2naf(Q,P,b_t,u,Fq6,D_twist=False,xi=None):
    """return f_{6u+2,Q}(P) * l_{[6u+2]Q,pi(Q)}(P) * l_{[6u+2]Q+pi(Q), pi^2(-Q)}(P)

    Optimized optimal ate Miller loop for BN curves and AKLGL formulas, 2-NAF
    Q, P are r-torsion points in G2, G1, in affine coordinates,
    u is the seed (integer) of the curve coefficients

    If u < 0, then f_{|u|, -Q}(P) is computed thanks to the formula
    f_{ij,Q} = f_{i,Q}^j*f_{j,[i]Q} and with i=-1, j=|u|:
    f_{-|u|,Q} = f_{-1,Q}^u*f_{|u|,-Q} and since f_{-1,Q} is a vectical line,
    it is discarded: f_{-|u|,Q} = f_{|u|,-Q}.
    """
    if xi is None:
        xi = -Fq6.modulus().constant_coefficient() # works with absolute and towering of extension
    P_ = (P[0], P[1])
    T = 6*u + 2
    if T < 0:
        Q_ = (Q[0], -Q[1], 1)
        m_T, TQ = miller_function_ate_2naf_aklgl(Q_, P_, b_t, -T, Fq6, D_twist=D_twist)
    else:
        Q_ = (Q[0], Q[1], 1)
        m_T, TQ = miller_function_ate_2naf_aklgl(Q_, P_, b_t, T, Fq6, D_twist=D_twist)
    # pQ with Q in E(Fp2) (before applying the twist)
    # then the output is, with xi^((p-1)/3), xi^((p-1)/2)
    p = Fq6.characteristic()
    xi_p16 = xi**((p-1)//6)
    if not D_twist:
        xi_p16 = 1/xi_p16
    xi_p13 = xi_p16**2
    xi_p12 = xi_p13 * xi_p16
    pQ = ((Q[0]).frobenius() * xi_p13, (Q[1]).frobenius() * xi_p12)
    # xi^((p^2-1)/6) = xi^((p-1)/6)*xi^(p+1)
    xi_p216 = xi_p16.frobenius() * xi_p16
    xi_p213 = xi_p216**2
    xi_p212 = xi_p213 * xi_p216
    p2_Q = (Q[0].frobenius(2) * xi_p213, -Q[1].frobenius(2) * xi_p212)

    l1, TpQ = add_line_h_a0_twist6_aklgl(TQ, pQ, P_, D_twist=D_twist)
    l2, Tp_p2Q = add_line_h_a0_twist6_aklgl(TpQ, p2_Q, P_, D_twist=D_twist)
    if D_twist:
        l1l2 = sparse_sparse_mult_d6_twist(l1[0], l1[1], l1[3], l2[0], l2[1], l2[3], xi, Fq6)
    else:
        l1l2 = sparse_sparse_mult_m6_twist(l1[0], l1[2], l1[3], l2[0], l2[2], l2[3], xi, Fq6)
    return m_T * l1l2

def final_exp_hard_bn(m, u):
    """
    Final exponentiation, hard part: m^(h*(p^4-p^2+1)//r) where h(x) = 12*x^3 + 6*x^2 + 2*x

    INPUT:
    - `m`: in GF(p^12) as an absolute extension to allow for m.frobenius()
    - `u`: BN curve seed

    Formulas from Fuentes-Castaneda et al, SAC'2011
    l0 = 1+6*x + 12*x**2 + 12*x**3
    l1 = 4*x + 6*x**2 + 12*x**3
    l2 = 6*x + 6*x**2 + 12*x**3
    l3 = -1 + 4*x + 6*x**2 + 12*x**3

    l0 + l1*px + l2*px^2 + l3*px3 == (12*x^3 + 6*x^2 + 2*x) * (px^4 - px^2 + 1)//rx

    cost: 3 exp(u) + 3 S + 10 M + 3 frob
    """
    fx = m**u
    f2x = fx**2
    f4x = f2x**2
    f6x = f4x * f2x
    f6x2 = f6x**u
    f12x2 = f6x2**2
    f12x3 = f12x2**u
    a = f12x3 * f6x2 * f6x
    b = a * f2x.frobenius(6)
    res = (a * f6x2 * m) * b.frobenius() * a.frobenius(2) * (b * m.frobenius(6)).frobenius(3)
    return res
