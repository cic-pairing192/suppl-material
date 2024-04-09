"""
Pairing on new Gasnier curve k=22 D=7
Date: 2023, May 30

m = 161
assert ((x^2 -x*qx + 2*qx^2) % rx) == 0

super-optimal ate pairing formulas
assert ((x + qx*lambrx) % rx) == 0
assert ((-2*qx + x*lambrx - qx*lambrx) % rx) == 0

final exponentiation
"""
from pairing import *

def miller_loop_opt_ate_kss22d7_v0(Q, P, a, u):
    """Miller loop with formula u^2 -u*q + 2*q^2 = 0 mod r
    f_{u^2 - u*q + 2*q^2, Q}(P)
    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + a*x + b
    - `a`: curve coefficent, y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters
    """
    q = (P[0]).parent().characteristic()
    v = u**2 - u*q + 2*q**2
    m2, u2Q = miller_function_ate(Q, P, a, v, m0=1)
    
    return m2

def miller_loop_opt_ate_kss22d7_v1(Q, P, a, u):
    """Miller loop with formula u^2 - u*q + 2*q^2 = 0 mod r
    f_{u^2,Q}(P) * f_{u, pi(-Q)}(P) * l_{[u^2]Q, [u]pi(-Q)}(P) * f_{2, Q}(P)^q^2
    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + a*x + b
    - `a`: curve coefficent, y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters
    """
    m0, _2Q = miller_function_ate(Q, P, a, 2, m0=1)
    m2, u2Q = miller_function_ate(Q, P, a, u**2, m0=1)
    q_Q = (Q[0].frobenius(), -Q[1].frobenius())
    m1, u_2qQ = miller_function_ate(q_Q, P, a, u, m0=1)
    l3, S = add_line_j_with_z(u2Q, u_2qQ, (P[0], P[1]))
    
    return m2 * m1 * l3 * m0.frobenius(2)

def miller_loop_opt_ate_kss22d7(Q, P, a, u):
    """Miller loop with formula u^2 - u*q + 2*q^2 = 0 mod r
    f_{u,Q}(P)^u * f{u, [u]Q}(P) * f_{-u, Q}(P)^q * l_{[u^2]Q, [-u]pi(Q)}(P) * f_{2, Q}(P)^q^2
    where f_{2, Q}(P) = l_{Q,Q}(P)^2
    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + a*x + b
    - `a`: curve coefficent, y^2 = x^3 + a*x + b
    - `u`: seed for curve parameters

    TODO: it should be possible to share the costs of the first doubling of f_{u, Q}(P) and f_{2, Q}(P)
    """
    u0 = u
    m1, uQ = miller_function_ate(Q, P, a, u0, m0=1)
    Z = 1/uQ[2]
    Z2 = Z**2
    Z3 = Z2 * Z
    uQ = (uQ[0]*Z2, uQ[1]*Z3) # affine coordinates from Jacobian coordinates
    if u < 0:
        mu = m1.conjugate()
    else:
        mu = m1
    m2, u2Q = miller_function_ate(uQ, P, a, u0, m0=mu)
    u_qQ = (uQ[0].frobenius(), -uQ[1].frobenius())
    l3, S = add_line_j(u2Q, u_qQ, (P[0], P[1]))
    l2, _2Q = double_line_affine_j((Q[0], Q[1]), (P[0], P[1]), a)

    return m2 * m1.conjugate().frobenius() * l3 * l2.frobenius(2)

def final_exp_hard_kss22d7(m, u):
    """
    Hard part Phi_k(q)/r of the final exponentiation
    INPUT:
    - `m`: element in GF(p^k)
    - `u`: seed of the curve
    RETURN: m^s*Phi_k(q)/r
    where s = 322*(u^18 - 2*u^16 + 2*u^15 + 2*u^14 - 6*u^13 + 2*u^12 + 10*u^11 - 14*u^10 - 6*u^9 + 34*u^8)
    but with some change q^10 at some point hence
    s = 23*(u^41 - 2*u^40 + 2*u^39 + 2*u^38 - 6*u^37 + 2*u^36 + 10*u^35 - 14*u^34 - 6*u^33 + 34*u^32 - 22*u^31 + 89*u^30 - 19*u^29 + 111*u^28 - 73*u^27 - 149*u^26 + 295*u^25 + 3*u^24 - 593*u^23 + 587*u^22 + 599*u^21 - 1773*u^20 + 7179*u^19 + 7956*u^18 - 1700*u^17 - 14212*u^16 + 17612*u^15 + 10812*u^14 - 46036*u^13 + 24412*u^12 + 67660*u^11 - 116484*u^10 - 18836*u^9 + 391068*u^8)
    if r was adjusted to r -> r/23, then s should be adjusted to 23*s
    cost 22 exp(u) + 17 frob + 3 frob(9) + 41 M + 50 S
    """
    a = m**u
    a = a**u * a.conjugate() * m**2
    assert a == m**(u**2 - u + 2)
    f = a
    a = a**u
    f = (f**2).frobenius() * a
    a = a**u # u^4 -u^3 + 2*u^2
    f = (f**2).frobenius() * a.conjugate()
    a = a**u # u^5 -u^4 + 2*u^3
    f = (f**2).frobenius() * (a * a**2).conjugate() # a^3
    a = a**u # u^6 -u^5 + 2*u^4
    f = (f**2).frobenius() * a.conjugate()
    a = a**u # u^7 -u^6 + 2*u^5
    f = (f**2).frobenius() * ((a**2)**2 * a)        # a^5
    a = a**u # u^8 -u^7 + 2*u^6
    f = (f**2).frobenius() * (((a**2)**2)**2 * a.conjugate()) # a^7
    a = a**u # u^9 -u^8 + 2*u^7
    f = (f**2).frobenius() * (a**2 * a).conjugate() # a^3

    assert a == m**(u**9 - u**8 + 2*u**7)
    q = m.parent().characteristic()
    assert f**8 == m**(1024*(u**2 -u   + 2    )*q**7 +  512*(u**3 -u**2 + 2*u  )*q**6 -  256*(u**4 -u**3 + 2*u**2)*q**5 -3*128*(u**5 -u**4 + 2*u**3)*q**4 -   64*(u**6 -u**5 + 2*u**4)*q**3 + 5*32*(u**7 -u**6 + 2*u**5)*q**2  + 7*16*(u**8 -u**7 + 2*u**6)*q -  3*8*(u**9 -u**8 + 2*u**7) )

    a = a**u # u^10 -u^9 + 2*u^8
    g = ((((a**2)**2)**2)**2 * a).frobenius(9) # a^17
    a = a**u # u^11 -u^10 + 2*u^9
    f = (f**2 * g.frobenius())**2 * (((a**2)**2 * a)**2 * a).frobenius(9) # a^11
    f = f**2

    assert a == m**(u**11 -u**10 + 2*u**9)
    assert f == m**(17*4*(u**10-u**9 + 2*u**8)*q**10 + 11*2*(u**11-u**10+ 2*u**9)*q**9 + 1024*(u**2 -u   + 2    )*q**7 +  512*(u**3 -u**2 + 2*u  )*q**6 -  256*(u**4 -u**3 + 2*u**2)*q**5 -3*128*(u**5 -u**4 + 2*u**3)*q**4 -   64*(u**6 -u**5 + 2*u**4)*q**3 + 5*32*(u**7 -u**6 + 2*u**5)*q**2  + 7*16*(u**8 -u**7 + 2*u**6)*q -  3*8*(u**9 -u**8 + 2*u**7) )

    #a = a**u * m**161 # u^12 -u^11 + 2*u^10 + 161
    a = a**u * (((((((m**2)**2 * m)**2)**2)**2)**2)**2 * m)   # m^161
    g = ((((a**2 * a)**2)**2)**2 * a.conjugate()).conjugate() # a^-23
    a = a**u       # u^13 -u^12 + 2*u^11 + 161*u
    g = g.frobenius() * (((a**2)**2 * a)**2 * a)    # a^11
    a = a**u       # u^14 -u^13 + 2*u^12 + 161*u^2
    g = g.frobenius() * ((((a**2)**2)**2)**2 * a)   # a^17
    a = a**u       # u^15 -u^14 + 2*u^13 + 161*u^3
    g = g.frobenius() * (a**2 * a)                  # a^3
    a = a**u       # u^16 -u^15 + 2*u^14 + 161*u^4
    g = g.frobenius() * (((a**2)**2)**2 * a.conjugate()).conjugate() # a^-7
    a = a**u       # u^17 -u^16 + 2*u^15 + 161*u^5
    g = g.frobenius() * ((a**2)**2 * a).conjugate() # a^5
    a = a**u       # u^18 -u^17 + 2*u^16 + 161*u^6
    g = g.frobenius() * a
    a = a**u       # u^19 -u^18 + 2*u^17 + 161*u^7
    g = g.frobenius() * (a**2 * a)                  # a^3
    a = a**u       # u^20 -u^19 + 2*u^18 + 161*u^8
    g = g.frobenius() * a

    assert a == m**(u**20 -u**19 + 2*u**18 + 161*u**8)
    assert g == m**((-23*(u**12 -u**11 + 2*u**10 + 161    ))*q**8 + ( 11*(u**13 -u**12 + 2*u**11 + 161*u  ))*q**7 + ( 17*(u**14 -u**13 + 2*u**12 + 161*u**2))*q**6 + (  3*(u**15 -u**14 + 2*u**13 + 161*u**3))*q**5 + ( -7*(u**16 -u**15 + 2*u**14 + 161*u**4))*q**4 + ( -5*(u**17 -u**16 + 2*u**15 + 161*u**5))*q**3 + (    (u**18 -u**17 + 2*u**16 + 161*u**6))*q**2 + (  3*(u**19 -u**18 + 2*u**17 + 161*u**7))*q + (    (u**20 -u**19 + 2*u**18 + 161*u**8)))

    f = f * g

    a = a**u       # u^21 -u^20 + 2*u^19 + 161*u^9
    g = a
    a = a**u       # u^22 -u^21 + 2*u^20 + 161*u^10
    g = g.frobenius() * a

    g = g.frobenius(9)

    f = f * g

    eee = \
        + (    (u**21 -u**20 + 2*u**19 + 161*u**9) + 17*4*(u**10-u**9 + 2*u**8))*q**10 \
        + (    (u**22 -u**21 + 2*u**20 + 161*u**10)+ 11*2*(u**11-u**10+ 2*u**9))*q**9 \
        + (-23*(u**12 -u**11 + 2*u**10 + 161     )                             )*q**8 \
        + ( 11*(u**13 -u**12 + 2*u**11 + 161*u   ) + 1024*(u**2 -u    + 2     ))*q**7 \
        + ( 17*(u**14 -u**13 + 2*u**12 + 161*u**2) +  512*(u**3 -u**2 + 2*u   ))*q**6 \
        + (  3*(u**15 -u**14 + 2*u**13 + 161*u**3) -  256*(u**4 -u**3 + 2*u**2))*q**5 \
        + ( -7*(u**16 -u**15 + 2*u**14 + 161*u**4) -3*128*(u**5 -u**4 + 2*u**3))*q**4 \
        + ( -5*(u**17 -u**16 + 2*u**15 + 161*u**5) -   64*(u**6 -u**5 + 2*u**4))*q**3 \
        + (    (u**18 -u**17 + 2*u**16 + 161*u**6) + 5*32*(u**7 -u**6 + 2*u**5))*q**2 \
        + (  3*(u**19 -u**18 + 2*u**17 + 161*u**7) + 7*16*(u**8 -u**7 + 2*u**6))*q \
        + (    (u**20 -u**19 + 2*u**18 + 161*u**8) -  3*8*(u**9 -u**8 + 2*u**7))

    assert f == m**eee
    return f

