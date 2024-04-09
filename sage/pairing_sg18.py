from pairing import *

def miller_loop_opt_ate_sg18(Q, P, u):
    """
    Miller loop f_{u,Q}(P) f_{u,Q}(P)^(p^3) l_{[u]Q,\pi_2(Q)}(P)
       where u can be positive or negative
    the formula is (x + x*qx^3 + qx^2) = 0 mod rx so the pairing equation is
    f_{u,Q}(P) f_{u,Q}(P)^(p^3) l_{\pi_3([u]Q),\pi_2(Q)}(P) l_{uQ, \pi_3([u]Q)+\pi_2(Q)}(P)
    --> it is not necessary to do the second line as it will be a vertical
    (it is possible to make a different choice of lines to implement)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters, non-zero integer in ZZ

    The curve coefficient a is zero.
    """
    m, uQ = miller_function_ate(Q, P, 0, u, m0=1)

    f = m.frobenius(3)
    f = m*f # costs one multiplication

    PP = (P[0], P[1])
    Q1 = (uQ[0], uQ[1], uQ[2], uQ[3])

    pi2Q = [(Q[0]).frobenius(2), (Q[1]).frobenius(2)]
    l3, Q3 = add_line_j(Q1, pi2Q, PP)

    f = f*l3 # can be done with a full-sparse multiplication

    return f

def final_exp_hard_sg18_v1(m, u):
    """
    Final exp with more factorization of the exponent
    \Phi_18(q)/r = (p^6-p^3+1)/r

    QQx = QQ['x']; (x,) = QQx._first_ngens(1)
    k = 18
    D = 3
    Phi_k = cyclotomic_polynomial(k)
    # SG18 polynomials
    rx = 27*x**6 + 9*x**3 + 1
    tx = 3*x**2 + 1
    cx = 9*x**4 - 6*x**2 + 1    # cofactor of curve order #E(Fp) = c(x)*r(x) = p(x) + 1 - t(x)
    px = cx*rx + tx - 1
    h1x = 9*x**4 - 6*x**2 + 1; assert h1x == cx # cx
    h2x = 27*x**6 - 9*x**3 + 1; assert h2x == Phi_k(tx-1) // rx
    ex = Phi_k(px) // rx
    ex == (3*x^2-1)^2 * (px^2 + 3*x^2*px + 9*x^4)*(27*x^6 + px^3 - 1) + 27*x^6 - 9*x^3 + 1 # ok, True
    # better version
    ex == (3*x^2-1)^2 * ((px^2 + 3*x^2*px + 9*x^4 + 3*x)*(1 - 3*x*px + px^3) - 3*px^2) + (1 - 3*x*px + px^3) # ok, True

    \Phi_18(q)/r = (3u^2-1)^2 ((q^2 + 3 q u^2 + 9 u^4 + 3 u)(1 - 3 u q + q^3) - 3 q^2) + (1 - 3 u q + q^3)

    step 1: (1 - 3uq + q^3) and -3q^2
    step 2: (q^2 + 3qu^2 + 9u^4 + 3u)(1 - 3uq + q^3) - 3q^2
    step 3: f^c where c = 9*u^4-6u^2+1 = (3*u^2-1)^2

    total cost 9 exp(|u|) + 14 M + 5 S + 5 f + 3 cj (+1 cj if u<0)
    """
    u_ = abs(u)
    # step 1: m1 = m^(1 - 3uq + q^3) and m0 = m^(-3q^2)
    m1 = m**2 * m              # ^3
    if u > 0:                  # 1-3uq+q^2 and -3q^2
        m1 = m1.conjugate()    # ^(-3)
        m0 = m1.frobenius(2)   # ^(-3q^2)
    else:                      # 1+3(-u)q+q^2 and -3q^2
        m0 = m1.frobenius(2)   # ^(3q^2)
        m0 = m0.conjugate()    # ^(-3q^2)
    m1 = m * (m1**u_ * m.frobenius(2)).frobenius() # 1-3uq+q^3
    # step 2: m2 = m1^(q^2 + 3qu^2 + 9u^4 + 3u)
    # q^2 + 3qu^2 + 9u^4 + 3u = q^2 + 3u(1 + u(3u^2 + q)) -> q^2 -3u(-1-u(3u^2+q)) if u<0
    m2 = (m1**u_)**u_
    m2 = m2**2 * m2 * m1.frobenius() # ^(3u^2 + q)
    m2 = m2**u_                      # ^|u|(3u^2+q)
    if u < 0:
        m2 = m1.conjugate() * m2     # ^(-1 +|u|(3u^2+q))
    else:
        m2 = m1 * m2                 # 1+u(3u^2+q)
    m2 = m2**u_
    m2 = m2**2 * m2                  # 3u(1 + u(3u^2 + q))
    m2 = m1.frobenius(2) * m2
    m2 = m2 * m0
    # step 3: m2 = m2^((3u^2-1)^2)
    m3 = m2**u_                 # m2^u
    m3 = m3**u_                # m2^(u^2)
    m3 = m3**2 * m3            # m2^(3*u^2)
    m2 = m3 * m2.conjugate()   # m2^(3*u^2-1) = m2
    m3 = m2**u_                # m2^u
    m3 = m3**u_                # m2^(u^2)
    m3 = m3**2 * m3            # m2^(3*u^2)
    m2 = m3 * m2.conjugate()   # m2^(3*u^2-1)
    # step 3: 4*exp(|u|) + 4M + 2S + 2 conj
    return m1 * m2

def final_exp_hard_sg18_v0(f, u):
    """
    Cost: 17 M + 5 S + 5 Frobenius powers + 9 exponentiations to u0 + 4 Inversions with Frobenius power p^9
    where u0 = |u|
    """
    u0 = abs(u)
    #####
    a1 = f**u0                 # f^u
    a2 = a1**u0                # f^(u^2)
    a3 = a2**2                 # f^(2*u^2)
    a4 = a2 * a3               # f^(3*u^2)
    a5 = a4**2                 # f^(6u^2)
    a6 = a4 * a5               # f^(9*u^2)
    a7 = a6**u0                # f^(9*u^3)
    a8 = a7**u0                # f^(9*u^4)
    a9 = a5.frobenius(9)       # f^(-6u^2)
    a10 = a8 * a9 * f          # f^(9*u^4-6u^2+1) = f^c
    # sub-total 4*exp(u) + 4M + 2S + 1 conj
    a11 = a10**u0              # f^(c*u)
    a12 = a11.frobenius(9)     # f^(-c*u)
    #####
    b1 = a11**u0               # f^(u^2*c)
    b2 = b1**u0                # f^(u^3*c)
    b3 = b2**2                 # f^(2*u^3*c)
    b4 = b2 * b3               # f^(3*u^3*c)
    #####
    c1 = b4**u0
    c2 = c1**2
    c3 = c1*c2
    c4 = c3**u0
    c5 = c4*a1
    #####
    d1 = c3*a12*f
    #####
    e1 = a10.frobenius(9)
    e2 = b4*e1
    #####
    g1 = b1**2
    g2 = b1*g1
    g3 = g2.frobenius(9)
    g4 = c5*g3
    #####
    f0 = a12
    f1 = g4.frobenius(1)
    f2 = e2.frobenius(2)
    f3 = d1.frobenius(3)
    f4 = c5.frobenius(4)
    f5 = b4.frobenius(5)
    #####
    t0 = f0*f1*f2*f3*f4*f5
    
    return t0

def cofactor_clearing_g1_sg18a(P, u):
    """
    cofactor clearing with Schoof criterion speed-up (rational c0-torsion where c = c0^2)
    INPUT:
    -`P`: point on a SG18a curve E, whose trace is t = 3*u^2 + 1
    -`u`: seed for the curve parameters

    The cofactor is c(x) = 9*x^4 - 6*x^2 + 1 = (3*x^2 - 1)^2
    Schoof criterion applies:
    let c0 = 3*x^2 - 1, then cx = c0^2, c0 | qx-1 and c0 | yx
    so that the c0-torsion is rational
    To multiply by cx, a multiplication by c0 is enough
    This is Rene Schoof Fq-rational l-torsion criterion from Proposition 3.7 in
    Schoof, R.: Nonsingular plane cubic curves over finite fields.
    Journal of Combinatorial Theory, Series A 46(2), 183–211 (1987).
    https://doi.org/10.1016/0097-3165(87)90003-3
    See also ePrint 2022/352

    A fast cofactor multiplication is then
    P -> (3*u^2-1)*P
    """
    P = (3*u**2-1)*P
    return P

def membership_testing_g1_sg18a(P, u, omega=None):
    """
    G1 membership testing, phi(P) = (omega*x, y) = [9*u^3+1]*P if P is in G1

    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed
    - `omega`: such that (omega*x, y) has eigenvalue 9*u^3+1

    P -> P + [1+lambda]phi(P) = P + [2+9*u^3]phi(P)
    But then, 1 + (1+lambda)*lambda = 1 + (2+9*u^3)*(1+9*u^3)
    = 81*x^6 + 27*x^3 + 3 = 3*(27*x^6 + 9*x^3 + 1) = 3*rx
    while cx = 9*x^4 - 6*x^2 + 1 so c = 1 mod 3 and this should be fine
    """
    if omega is None:
        Fp = P.curve().base_field()
        omega = Fp((486*u**9 + 243*u**8 - 486*u**7 - 81*u**6 + 297*u**5 - 54*u**4 - 72*u**3 + 45*u**2 + 6*u - 11)/7) # !!! this is a rational, not an integer, do not use // but use /
    phiP = P.curve()((P[0]*omega, P[1], P[2]))
    lphiP = (9*u**3+2)*phiP
    return (P + lphiP).is_zero()

def cofactor_clearing_g2_sg18a(Q, u, Fq6, D_twist=True, case=0):
    """
    Multiply Q by the cofactor of G2
    INPUT:
    - `Q`: point on E'(Fp3) containing (compressed) G2
    - `u`: seed of the SG18a curve
    - `Fq6`: finite field extension of explicit degree 6 on top of Fq
    - `D_twist`: True/False (M_twist)

    cofactor clearing with endomorphism on G2
    G2 is supposed to be given in compressed representation over GF(p^3)
    That is, P.curve() is E'(Fp3) a sixth twist of E

    The endomorphism is
    psi(P) = twist o Frobenius o untwist (P)

    The eigenvalue is a root of the characteristic polynomial X^2 - t*X + p
    That is one of (t +/- y sqrt(-3))/2 (the one that matches p on G2 mod r)
    G2 has order p^3 + 1 - t3' where t3' is the trace of E', the appropriate sixth twist of E(Fp3)
    Let t be the trace of E(Fp), t2 = t^2-2*p and t3 = t*t2-p*t = t^3-3*p*t
    y3 = y * (p-t^2) where p = (t^2 + 3*y^2)/4
    Then #E'(Fp3) = p^3 + 1 - (-3*y3+t3)/2 = r * c2
    G2 cofactor = 3*(177147*x^24 - 354294*x^22 + 118098*x^21 + 295245*x^20 - 236196*x^19 - 98415*x^18 + 196830*x^17 - 26244*x^16 - 83106*x^15 + 41553*x^14 + 15309*x^13 - 19440*x^12 + 1458*x^11 + 4860*x^10 - 1539*x^9 - 567*x^8 + 405*x^7 - 54*x^5 + 1)
    3 | c2
    reduced matrix:
    [       -3*x^2 + 1     3*x^3 - x - 1               2*x         3*x^2 - 1      -6*x^3 + 2*x 9*x^4 - 3*x^2 - x]
    [    3*x^3 - x - 1               2*x                 0      -6*x^3 + 2*x 9*x^4 - 3*x^2 - x         3*x^2 - 1]
    [              2*x                 0    -3*x^3 + x - 1 9*x^4 - 3*x^2 - x         3*x^2 - 1    -3*x^3 + x + 1]
    [                0    -3*x^3 + x - 1 9*x^4 - 3*x^2 + x         3*x^2 - 1    -3*x^3 + x + 1              -2*x]
    [   -3*x^3 + x - 1 9*x^4 - 3*x^2 + x         3*x^2 - 1    -3*x^3 + x + 1              -2*x                 0]
    [9*x^4 - 3*x^2 + x         3*x^2 - 1      -6*x^3 + 2*x              -2*x                 0     3*x^3 - x + 1]
    for each row [l0 l1 l2 l3 l4 l5] of the matrix, l0 + l1*L + l2*L^2 + l3*L^3 + l4*L^4 + l5*L^5 is a multiple of c2, where L is the eigenvalue mod c2, such that L mod r = q mod r.
    """
    if Q.is_zero():
        return Q
    # note that all these mu values could be precomputed and stored
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 6, 1, D_twist)
    # xi**((p^2-1)//6) = mu^(p+1)
    mu2 = mu.frobenius()*mu
    #assert mu2 == xi**((p**2-1)//6)
    psi2Q = endomorphism_g2_psi_p(Q, None, mu2, 6, 2, D_twist)
    # xi**((p^3-1)//6) = mu^(p^2+p+1)
    mu3 = mu.frobenius(2)*mu2
    #assert mu3 == xi**((p**3-1)//6)
    psi3Q = endomorphism_g2_psi_p(Q, None, mu3, 6, 3, D_twist)
    # xi**((p^4-1)//6) = mu^((p+1)*(p-1)*(p^2+1))
    mu4 = mu2.frobenius(2)*mu2
    #assert mu4 == xi**((p**4-1)//6)
    psi4Q = endomorphism_g2_psi_p(Q, None, mu4, 6, 4, D_twist)
    # xi**((p^5-1)//6) = mu^(1+p+p^2+p^3+p^4)
    mu5 = mu3 * mu2.frobenius(3)
    #assert mu5 == xi**((p**5-1)//6)
    psi5Q = endomorphism_g2_psi_p(Q, None, mu5, 6, 5, D_twist)

    if case == 0:
        return (-3*u**2+1)*Q + (3*u**3-u-1)*psi1Q + (2*u)*psi2Q + (3*u**2-1)*psi3Q + (-6*u**3+2*u)*psi4Q + (9*u**4-3*u**2-u)*psi5Q
    if case == 1:
        return (3*u**3-u-1)*Q + (2*u)*psi1Q + (-6*u**3+2*u)*psi3Q + (9*u**4-3*u**2-u)*psi4Q + (3*u**2-1)*psi5Q
    if case == 2:
        return (2*u)*Q + (-3*u**3+u-1)*psi2Q + (9*u**4-3*u**2-u)*psi3Q + (3*u**2-1)*psi4Q + (-3*u**3+u+1)*psi5Q
    if case == 3:
        return  (-3*u**3+u-1)*psi1Q + (9*u**4-3*u**2+u)*psi2Q + (3*u**2-1)*psi3Q + (-3*u**3+u+1)*psi4Q + (-2*u)*psi5Q
    if case == 4:
        return (-3*u**3+u-1)*Q + (9*u**4-3*u**2+u)*psi1Q + (3*u**2-1)*psi2Q + (-3*u**3+u+1)*psi3Q + (-2*u)*psi4Q
    if case == 5:
        return (9*u**4-3*u**2+u)*Q + (3*u**2-1)*psi1Q + (-6*u**3+2*u)*psi2Q + (-2*u)*psi3Q + (3*u**3-u+1)*psi5Q

def membership_testing_g2_sg18a(Q, u, Fq6, D_twist=True):
    """
    test if Q belongs to G2 <=> Q has order r
    INPUT:
    - `Q`: point on an Elliptic Curve E'(Fq), q=p^e, e=k/d, a d-twist of E(Fqd)
    - `u`: curve seed
    - `Fq6`: Finite field extension of degree 6 on top of Fq = Fp3
    - `D_twist`: True/False

    Formula
    eq2 := x + x*(qx^3 mod rx) + (qx^2 mod rx);
    eq2 eq 0;
    eq2 := x + x*qx^3 + qx^2;
    Resultant(eq2, g2cx) eq 3^361 * 10477 * 33107829276457963
    but the 3 in the resultant is due to the leading coefficients, there is no root mod 3
    For the formula x + qx^2 + x*qx^3, conditions on the seed u are:
    u != 232 mod 271 and u != 784561254737940 mod 1070240566457197
    """
    assert (u % 271) != 232
    assert (u % 1070240566457197) != 784561254737940
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
    R = u*(Q + psi3Q) + psi2Q
    return R.is_zero()
