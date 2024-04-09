"""
Date June 26, 2023

Pairing on Freeman-Scott-Teske curves, Construction 6.6, k=22 (D=3)
Only a quadratic twist is available
The curve equation is y^2 = x^3 + b (j=0)

k = 22
D = 3
rx = cyclotomic_polynomial(3*k)
tx = x**3+1
yx = (x**3-1)*(2*x**(k//2)-1)/3
px = ((x**3-1)**2*(x**k-x**(k//2)+1) + 3*x**3)/3
qx = px
lambx = x**(k//2)-1
mux = -x**(k//2)
cx = (x - 1)^2 * (x^2 - x + 1) * (x^2 + x + 1)^2/3
cx == (x^8 - x^7 + x^6 - 2*x^5 + 2*x^4 - 2*x^3 + x^2 - x + 1)/3

# short vector for optimal ate pairing computation

((x^2 - x*qx^4 + qx^8) % rx) == 0
((-1 + x^2*qx^3 - x*qx^7) % rx) == 0
(x - qx^4 + x^2*qx^7) % rx) == 0
"""
from pairing import *

def miller_loop_opt_ate_fst66_k22(Q, P, u):
    """Miller loop (f_{u,Q}^u f_{u,[u]Q} ell_{[u^2]Q, [-u]pi^4(Q)} (f_{u,Q})^(-q^4)
    f_{u^2, Q} * f_{u, -[q^4]Q} * l_{[u^2]Q, -[u][q^4]Q}

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + b
    - `u`: seed for curve parameters

    E has type FST 6.6, k = 4 mod 6, D=3
    Formula u^2 - u*q^4 + q^8 = 0 mod r
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
    pi4_Q = (uQ[0].frobenius(4), -uQ[1].frobenius(4))
    l3, _ = add_line_j(u2Q, pi4_Q, (P[0], P[1]))

    return m2 * m1.frobenius(4).conjugate() * l3

def miller_loop_opt_ate_fst66_k22_cln_a0_quad_twist(Q, P, b_t, u, Fq2=None, D_twist=None):
    """Miller loop (f_{u,Q}^u f_{u,[u]Q} ell_{[u^2]Q, [-u]pi^4(Q)} (f_{u,Q})^(-q^4)
    f_{u^2, Q} * f_{u, -[q^4]Q} * l_{[u^2]Q, -[u][q^4]Q}

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + b
    - `b_t`: quadratic twist curve E' coefficient y^2 = x^3 + b_t
    - `u`: seed for curve parameters
    - `Fq2`: quadratic extension on top of Fq = Fp11
    - `D_twist`

    E has type FST 6.6, k = 4 mod 6, D=3
    Formula u^2 - u*q^4 + q^8 = 0 mod r

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
    pi4_Q = (uQ[0].frobenius(4), -uQ[1].frobenius(4))
    l3, _ = add_line_cln_a0_quad_twist(u2Q, pi4_Q, (P[0], P[1]), Fq2, D_twist)

    return m2 * m1.frobenius(4).conjugate() * l3 # TODO problem of map of finite fields

def final_exp_hard_fst66_k22(m, u):
    """
    Hard part Phi_k(q)/r of the final exponentiation
    INPUT:
    - `m`: element in GF(q^k)
    - `u`: seed of the curve
    RETURN: m^Phi_k(q)/r

    exp_hard = (q^10 - q^9 + q^8 - q^7 + q^6 - q^5 + q^4 - q^3 + q^2 - q + 1)/r
             = cx * ex + 1
    there is no nice formula that simplifies like in
    ePrint 2020/875 by Hayashida--Hayasaka--Teruya

    new_exp eq (x^3 - 1)^2*((x^10*(x+qx^4) + x*qx^7-1)*(x^3 + qx)*(x^6 + qx^2) - x^10*qx^7) + 3*(x + qx^4);

    if u < 0:
    x_ := -x;
    new_exp eq (x_^3+ 1)^2*((x_^10*(x_-qx^4) + x_*qx^7+1)*(x_^3 - qx)*(x_^6 + qx^2) - x_^10*qx^7) + 3*(-x_ + qx^4);

    sx eq x^27 + x^26 - 3*x^24 - 3*x^23 + 4*x^21 + 4*x^20 - 4*x^18 - 4*x^17 - x^16 + 3*x^15 + 4*x^14 + 3*x^13 - x^12 - 4*x^11 - 4*x^10 + 4*x^8 + 4*x^7 - 3*x^5 - 3*x^4 + 4*x^2 + 4*x;
    Cost 26 exp(u) + 11 M + S + 6 frob
    """
    #q = m.parent().characteristic()
    f1 = m**u
    a = f1 * m.frobenius(4)
    a = a**2 * a
    #assert a == m**((u + q**4)*3)
    b = (f1**u)**u * m.conjugate()
    b = ((b**u)**u)**u * b.conjugate()
    #assert b == m**((u**3-1)**2)
    c = b**u
    d = ((((((((c**u)**u)**u)**u)**u)**u)**u)**u)**u
    #assert d == b**(u**10)
    e = b.conjugate() * c.frobenius(7) * (d**u * d.frobenius(4))
    #assert e == b**(u**10*(u+q**4) + u*q**7 - 1)
    e = ((e**u)**u)**u * e.frobenius()
    e = (((((e**u)**u)**u)**u)**u)**u * e.frobenius(2)
    e = e * d.frobenius(7).conjugate()
    return a * e
