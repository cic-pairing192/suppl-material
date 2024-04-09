"""
Date April 2023

Pairing on Freeman-Scott-Teske curves, Construction 6.3, k=22 (D=1)
Only a quadratic twist is available
The curve equation is y^2 = x^3 + a*x (j=1728)

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
lambx = x**(k//2)
mux = -x**(k//2)

rx = x^20 - x^18 + x^16 - x^14 + x^12 - x^10 + x^8 - x^6 + x^4 - x^2 + 1
tx = x^2 + 1
yx = x^13 - x^11
qx = (x^26 - 2*x^24 + x^22 + x^4 + 2*x^2 + 1)/4
cx = (x^2-1)^2*(x^2+1)/4
betax = (x^25 - 3*x^23 + 4*x^21 - 4*x^19 + 4*x^17 - 4*x^15 + 4*x^13 - 2*x^11 + x^3 + x)/2
lambx = x^11
mux = -x^11

assert ((x^2 - qx) % rx) == 0
with lambx = x^11:
assert ((x + lambx*qx^6) % rx) == 0
assert ((-qx^6 + x*lambx) % rx) == 0
assert ((x*qx^5 - lambx) % rx) == 0
assert ((1 + x*lambx*qx^5) % rx) == 0
"""
from pairing import *

def miller_loop_opt_ate_fst63_k22(Q, P, a, u):
    """Miller loop f_{u^2,Q}(P) = f_{u,Q}^u(P) f_{u,[u]Q}(P)

    INPUT:
    - `Q`: point on E(Fpk) of order r
    - `P`: point on E(Fp), E in short Weierstrass y^2 = x^3 + a*x
    - `a`: curve coefficent, y^2 = x^3 + a*x
    - `u`: seed for curve parameters

    E has type FST 6.3, k = 2 mod 4, D=1
    Formula u^2 - q^2 = 0 mod r
    """
    m1, uQ = miller_function_ate(Q, P, a, u, m0=1)
    Z = 1/uQ[2]
    Z2 = Z**2
    Z3 = Z2 * Z
    uQ = (uQ[0]*Z2, uQ[1]*Z3, 1, 1) # affine coordinates from Jacobian coordinates
    if u < 0:
        mu = m1.conjugate()
    else:
        mu = m1
    m2, u2Q = miller_function_ate(uQ, P, a, u, m0=mu)

    return m2

def final_exp_hard_fst63_k22(m, u):
    """
    Hard part Phi_k(q)/r of the final exponentiation
    INPUT:
    - `m`: element in GF(p^k)
    - `u`: seed of the curve
    RETURN: m^Phi_k(q)/r

    exp_hard = (q^10 - q^9 + q^8 - q^7 + q^6 - q^5 + q^4 - q^3 + q^2 - q + 1)/r
             = cx * ex + 1
    ex=(x^18 - x^16 + x^14 - x^12 + x^10 - x^8 + x^6 - x^4 + x^2 - 1)
    + (x^16 - x^14 + x^12 - x^10 + x^8 - x^6 + x^4 - x^2 + 1)*qx
    + (x^14 - x^12 + x^10 - x^8 + x^6 - x^4 + x^2 - 1)*qx^2
    + (x^12 - x^10 + x^8 - x^6 + x^4 - x^2 + 1)*qx^3
    + (x^10 - x^8 + x^6 - x^4 + x^2 - 1)*qx^4
    + (x^8 - x^6 + x^4 - x^2 + 1)*qx^5
    + (x^6 - x^4 + x^2 - 1)*qx^6
    + (x^4 - x^2 + 1)*qx^7
    + (x^2 - 1)*qx^8
    + qx^9

    cost 24 exp(u) + 2 S + 21 M + 9 frob
    """
    f = m
    m_ = m.conjugate()
    a = (m**u)**u * m_
    f = f.frobenius() * a
    a = (a**u)**u * m
    f = f.frobenius() * a
    a = (a**u)**u * m_
    f = f.frobenius() * a
    a = (a**u)**u * m
    f = f.frobenius() * a
    a = (a**u)**u * m_
    f = f.frobenius() * a
    a = (a**u)**u * m
    f = f.frobenius() * a
    a = (a**u)**u * m_
    f = f.frobenius() * a
    a = (a**u)**u * m
    f = f.frobenius() * a
    a = (a**u)**u * m_
    f = f.frobenius() * a
    # cx = (x^2-1)^2*(x^2+1)/4 = (x^4-1)*(x^2-1)/4
    f = (f**u)**u * f.conjugate()
    f = (((f**u)**u)**u)**u * f.conjugate()
    f = f * (m**2)**2
    return f
