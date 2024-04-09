"""
Date April 2023

Pairing on Freeman-Scott-Teske curves, Construction 6.6, k=20 (D=3)
Only a quadratic twist is available
The curve equation is y^2 = x^3 + b (j=0)

k = 20
D = 3
rx = cyclotomic_polynomial(3*k)
tx = x**(k//2+1)-x+1
yx = (x**(k//2+1)+2*x**(k//2)+x-1)/3
px = ((x-1)**2*(x**k-x**(k//2)+1)+3*x**(k+1))/3
lambx = x**(k//2)-1
mux = -x**(k//2)

rx = x^16 + x^14 - x^10 - x^8 - x^6 + x^2 + 1
tx = x^11 - x + 1
qx = (x^22 + x^21 + x^20 - x^12 + 2*x^11 - x^10 + x^2 - 2*x + 1)/3
yx = (x**11 + 2*x**10 + x - 1)/3
lambx = x**10-1
mux = -x**10

# short vector [x^2 x 1 0 0 0 0 0]
assert ((x**2 + x*qx + qx**2) % rx) == 0

# with lambx = x**10-1:
# short vectors
# [ x  1  0  0  0  0  0  0  0  1  0  0  0  0  0  0]
# [ 0 -1  0  0  0  0  0  0  x  0  0  0  0  0  0  0]
assert ((x + qx + lambx*qx) % rx) == 0
assert ((x*lambx - qx) % rx) == 0

# with mux = -x**10:
# short vectors
# [ 0  1  0  0  0  0  0  0  x  1  0  0  0  0  0  0]
# [ x  0  0  0  0  0  0  0  0 -1  0  0  0  0  0  0]
assert ((qx + x*mux + mux*qx) % rx) == 0
assert ((x - mux*qx) % rx) == 0
"""
from pairing import *

def miller_loop_opt_ate_fst66_k20(Q, P, u):
    """Miller loop (f_{u,Q}^u f_{u,[u]Q} ell_{[u^2]Q, [u]pi(Q)} (f_{u,Q})^q

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + b
    - `u`: seed for curve parameters

    E has type FST 6.6, k = 2 mod 6, D=3
    Formula u^2 + u*q + q^2 = 0 mod r
    """
    m1, uQ = miller_function_ate(Q, P, 0, u, m0=1)
    Z = 1/uQ[2]
    Z2 = Z**2
    Z3 = Z2 * Z
    uQ = (uQ[0]*Z2, uQ[1]*Z3, 1, 1) # affine coordinates from Jacobian coordinates
    if u < 0:
        mu = m1.conjugate()
    else:
        mu = m1
    m2, u2Q = miller_function_ate(uQ, P, 0, u, m0=mu)
    piQ = (uQ[0].frobenius(), uQ[1].frobenius())
    l3, uqQ = add_line_j(u2Q, piQ, (P[0], P[1]))

    return m2 * m1.frobenius() * l3

def miller_loop_opt_ate_fst66_k20_cln_a0_quad_twist(Q, P, b_t, u, Fq2=None, D_twist=None):
    """Miller loop (f_{u,Q}^u f_{u,[u]Q} ell_{[u^2]Q, [u]pi(Q)} (f_{u,Q})^q
    f_{u^2, Q} * f_{u, [q]Q} * l_{[u^2]Q, [u][q]Q}
    u^2 + u*q + q^2 = 0 mod r

    INPUT:
    - `Q`: point on E'(Fq) of order r, the quadratic twist defined over Fq = Fp^10 = Fp^(k/2)
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + b
    - `b_t`: quadratic twist curve E' coefficient y^2 = x^3 + b_t
    - `u`: seed for curve parameters
    - `Fq2`: quadratic extension on top of Fq = Fp10
    - `D_twist`

    E has type FST 6.6, k = 2 mod 6, D=3
    Formula u^2 + u*q + q^2 = 0 mod r

    problem there is no conjugate function in SageMath over non-absolute extensions:
    use a map TODO
    """
    m1, uQ = miller_function_ate_cln_a0_quad_twist(Q, P, b_t, u, 1, Fq2, D_twist)
    Z = 1/uQ[2]
    uQ = (uQ[0]*Z, uQ[1]*Z, 1) # affine coordinates from projective coordinates
    if u < 0:
        mu = m1.conjugate() # TODO problem of map of finite fields
    else:
        mu = m1
    m2, u2Q = miller_function_ate_cln_a0_quad_twist(uQ, P, b_t, u, mu, Fq2, D_twist)
    piQ = (uQ[0].frobenius(), uQ[1].frobenius())
    l3, _ = add_line_cln_a0_quad_twist(u2Q, piQ, (P[0], P[1]), Fq2, D_twist)

    return m2 * m1.frobenius() * l3 # TODO problem of map of finite fields

def miller_loop_super_opt_ate_fst66_k20(Q, P, u, omega=None):
    """superoptimal pairing with Miller loop
    f_{u,Q}(P) * f_{u,Q}(phi^2(P))^lambda * (f_{u,Q}(phi(P))^mu
    eprint 2022/716 Corollary 1
    Emmanuel Fouotsa, Laurian Azebaze Guimagang, Raoul Ayissi

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + b
    - `u`: seed for curve parameters
    - `omega`: primitive cubic root of unity in Fp such that (omega*x, y) has eigenvalue x^10-1 on G1 and -x^10 on G2

    E has type FST 6.6, k = 2 mod 6, D=3
    two eigenvalues mod r, lambx = x^10-1, mux = -x^10
    1. x - mu*q = 0 mod r where mu = -x^10 is the eigenvalue of phi in G2, and lambda = x^10-1 is the eigenvalue in G1
    2. q + x*mu + mu*q = 0 mod r
    3. x + q + lambda*q = 0 mod r
    4. x*lambda - q = 0 mod r

    Note that x = mu*q mod r <=> mu = x/q mod r <=> mu = x*q^21
    and lambda = -mu-1 => lambda = -x*q^21-1
    """
    m1, uQ = miller_function_ate(Q, P, 0, u, m0=1)
    if omega is None:
        Fp = P[0].parent()
        omega = Fp(u**21 + u**20 + 2*u**19 + u**18 + 2*u**17 + u**16 + 2*u**15 + u**14 + 2*u**13 + u**12 + u**11 + 2*u**10 - u**9 + u**8 - u**7 + u**6 - u**5 + u**4 - u**3 + u**2 - 1)
        omega = -omega-1
    lambd = u**10-1
    mu = -u**10
    phiP = P.curve()(P[0]*omega, P[1])
    assert phiP == lambd*P
    phi2P = P.curve()(phiP[0]*omega, P[1])
    assert phi2P == mu*P
    m2, uQ = miller_function_ate(Q, phiP, 0, u, m0=1)
    m3, uQ = miller_function_ate(Q, phi2P, 0, u, m0=1)
    m = m1 * m3**lambd * m2**mu
    return m

def miller_loop_x_super_opt_ate_fst66_k20(Q, P, u, omega=None):
    """x-superoptimal pairing with Miller loop
    (f_{u,Q}(P) / f_{u,Q}(phi(P)))^x (f_{u,Q}(phi^2(P)) / f_{u,Q}(phi(P)))^q
    eprint 2022/716
    Emmanuel Fouotsa, Laurian Azebaze Guimagang, Raoul Ayissi

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + b
    - `u`: seed for curve parameters
    - `omega`: primitive cubic root of unity in Fp such that (omega*x, y) has eigenvalue x^10-1 on G1 and -x^10 on G2

    E has type FST 6.6, k = 2 mod 6, D=3
    two eigenvalues mod r, lambx = x^10-1, mux = -x^10
    1. x - mu*q = 0 mod r where mu = -x^10 is the eigenvalue of phi in G2, and lambda = x^10-1 is the eigenvalue in G1
    2. q + x*mu + mu*q = 0 mod r
    3. x + q + lambda*q = 0 mod r
    4. x*lambda - q = 0 mod r

    Note that x = mu*q mod r <=> mu = x/q mod r <=> mu = x*q^21
    and lambda = -mu-1 => lambda = -x*q^21-1
    """
    m1, uQ = miller_function_ate(Q, P, 0, u, m0=1)
    if omega is None:
        Fp = P[0].parent()
        omega = Fp(u**21 + u**20 + 2*u**19 + u**18 + 2*u**17 + u**16 + 2*u**15 + u**14 + 2*u**13 + u**12 + u**11 + 2*u**10 - u**9 + u**8 - u**7 + u**6 - u**5 + u**4 - u**3 + u**2 - 1)
        omega = -omega-1
    lambd = u**10-1
    mu = -u**10
    phiP = P.curve()(P[0]*omega, P[1])
    phi2P = P.curve()(phiP[0]*omega, P[1])
    assert phiP == lambd*P
    assert phi2P == mu*P
    m2, uQ = miller_function_ate(Q, phiP, 0, u, m0=1)
    m3, uQ = miller_function_ate(Q, phi2P, 0, u, m0=1)

    m = (m1 * m2.conjugate())**u * (m3 * m2.conjugate()).frobenius()
    return m

def final_exp_hard_fst66_k20(m, u):
    """
    Hard part Phi_k(q)/r of the final exponentiation
    INPUT:
    - `m`: element in GF(q^k)
    - `u`: seed of the curve
    RETURN: m^Phi_k(q)/r

    exp_hard = (p^8-p^6+p^4-p^2+1)/r
    c5 = -u^11 - u^10 - u^9 - u^5 - u^4 - u^3 - 3
    c2 = -u^8 - u^7 - u^6 - u^2 - u - 1

    ((- u^2*(u - q)*(u^3*(u^3 + q^3) + q^6 - 1) - q*(q^6 - q^4 - 1))*c5 \
    + (1 + u*q - q^2 + (u^2 - q^2)*q^4)*(-c2) \
    + a0*(u*(-1 + q^6) + q^3)*q + 3*(u^3 - u^2*q + q^3)) \
    == (-3*u^7 + 3*u^3 + 3*u) * exp_hard

    cost 20*exp(|u|) + 25 M + 2 S + 5*frob + 2*frob(2) + frob(3) + 3*frob(4) + 2*frob(6)
    """
    m0 = m
    m1 = m0**u
    m2 = m1**u
    m3 = m2**u
    m4 = m3**u
    m5 = m4**u
    m6 = m5**u
    f0 = m3 * (m2.conjugate() * m0.frobenius(2)).frobenius()
    f0 = f0**2 * f0
    # q = m.parent().characteristic()
    # e0 = 3*(u**3 + (-u**2 + q**2)*q)
    # assert f0 == m0**e0
    a0 = m6 * m5 * m1 * m0 * m3.conjugate()
    # A0 = u**6 + u**5 - u**3 + u + 1
    # assert a0 == m**A0
    a1 = a0**u
    f1 = (a1.frobenius(6) * a1.conjugate()).frobenius() * a0.frobenius(4)
    # assert f1 == a0**(-u*q + q**4 + u*q**7)
    a2 = a1**u * a0
    # c2 = -u**8 - u**7 - u**6 - u**2 - u - 1
    # assert m**(-c2) == a2
    a3 = a2**u
    a4 = a3**u
    a2_ = a2.frobenius(2).conjugate()
    f2 = a2 * a3.frobenius() * a2_ * (a4 * a2_).frobenius(4)
    a5 = (a4**u * m0**2 * m).conjugate()
    # c5 = -u**11 - u**10 - u**9 - u**5 - u**4 - u**3 - 3
    # assert a5 == m0**c5
    a6 = a5.frobenius(6) * a5.conjugate()
    a7 = (a6 * a5.frobenius(4).conjugate()).frobenius()
    # assert a7 == a5**(q*(q**6 - q**4 - 1))
    a8 = ((a5**u)**u)**u
    a8 = ((a8**u)**u)**u * a8.frobenius(3)
    a8 = a6 * a8
    a9 = a8**u * a8.frobenius().conjugate()
    a10 = ((a9**u)**u).conjugate()
    f10 = a10 * a7.conjugate()

    return f10 * f2 * f1 * f0

