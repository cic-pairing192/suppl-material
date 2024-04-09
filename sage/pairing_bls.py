"""
Group operations for BLS curves (BLS12, BLS24)
Date: March 29, 2023

ePrint 2021/1130: Michael Scott
ePrint 2022/348: Yu Dai, Kaizhan Lin, Chang-An Zhao, Zijian Zhou
ePrint 2022/352: El Housni, Guillevic, Piellard
"""

############ BLS12 ############
def cofactor_clearing_g1_bls12(P, u):
    """
    G1 cofactor h1 = (x-1)^2/3
    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed

    P -> (u-1)*P according to https://tches.iacr.org/index.php/TCHES/article/view/8348
    generic proof in ePrint 2022/352
    This is Rene Schoof Fq-rational l-torsion criterion from Proposition 3.7 in
    Schoof, R.: Nonsingular plane cubic curves over finite fields.
    Journal of Combinatorial Theory, Series A 46(2), 183–211 (1987).
    https://doi.org/10.1016/0097-3165(87)90003-3
    """
    return (u-1)*P

def cofactor_clearing_g2_bls12(Q, u, Fq6, D_twist=True):
    """
    Multiply Q by the cofactor of G2
    INPUT:
    - `Q`: point on compressed G2 in E'(Fp2)
    - `u`: curve seed
    - `Fq6`: explicit degree 6 extension on top of Fq = Fp2
    - `D_twist`: a Divide-twist or a Multiply-twist

    G2 cofactor h2 = 1/9*(x^8 - 4*x^7 + 5*x^6 - 4*x^4 + 6*x^3 - 4*x^2 - 4*x + 13)
    lambda mod h2 = 1/897*(-21*x^7 + 91*x^6 + 64*x^5 - 420*x^4 + 224*x^3 + 198*x^2 - 281*x + 676)
    v = (x^2 - x - 1       x - 1           2           0)
    Q -> (u*(u-1)-1)*Q + (u-1)*psi(Q) + 2*psi^2(Q)
    """
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu

    u_1Q = (u-1)*Q
    u2Q = u*u_1Q-Q
    psi1Q = endomorphism_g2_psi_p(u_1Q, None, mu, 6, 1, D_twist)
    psi2Q = endomorphism_g2_psi_p(2*Q, None, mu2, 6, 2, D_twist)
    return u2Q + psi1Q + psi2Q

def membership_testing_g1_bls12(P, u, omega):
    """
    G1 membership testing, phi(P) = (omega*x, y) = [-u^2]*P if P is in G1

    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed
    - `omega`: such that (omega*x, y) has eigenvalue -u^2
    """
    u2P = u**2*P
    phiP = P.curve()((P[0]*omega, P[1], P[2]))
    return (phiP + u2P).is_zero()

def membership_testing_g2_bls12(Q, u, Fq6, D_twist=True):
    """
    G2 membership testing from ePrint 2021/1130 Michael Scott
    https://eprint.iacr.org/2021/1130
    as soon as r = u^4-u^2+1 is prime, testing psi(Q) = u*Q is enough
    INPUT:
    - `Q`: point on compressed G2 in E'(Fp2)
    - `u`: curve seed
    - `Fq6`: explicit degree 6 extension on top of Fq = Fp2
    - `D_twist`: a Divide-twist or a Multiply-twist
    """
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)

    uQ = u*Q
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 6, 1, D_twist)
    return (psi1Q - uQ).is_zero()

############ BLS24 ############
def cofactor_clearing_g1_bls24(P, u):
    """
    G1 cofactor h1 = (x-1)^2/3
    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed

    P -> (u-1)*P according to https://tches.iacr.org/index.php/TCHES/article/view/8348
    generic proof in ePrint 2022/352
    This is Rene Schoof Fq-rational l-torsion criterion from Proposition 3.7 in
    Schoof, R.: Nonsingular plane cubic curves over finite fields.
    Journal of Combinatorial Theory, Series A 46(2), 183–211 (1987).
    https://doi.org/10.1016/0097-3165(87)90003-3
    """
    return (u-1)*P

def cofactor_clearing_g2_bls24(Q, u, Fq6, D_twist=True):
    """
    Multiply Q by the cofactor of G2
    INPUT:
    - `Q`: point on compressed G2 in E'(p4)
    - `u`: curve seed
    - `Fq6`: explicit degree 6 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist

    G2 cofactor h2 = 1/81*(x^32 - 8*x^31 + 28*x^30 - 56*x^29 + 67*x^28 - 32*x^27 - 56*x^26 + 160*x^25 - 203*x^24 + 132*x^23 + 12*x^22 - 132*x^21 + 170*x^20 - 124*x^19 + 44*x^18 - 4*x^17 + 2*x^16 + 20*x^15 - 46*x^14 + 20*x^13 + 5*x^12 + 24*x^11 - 42*x^10 + 48*x^9 - 101*x^8 + 100*x^7 + 70*x^6 - 128*x^5 + 70*x^4 - 56*x^3 - 44*x^2 + 40*x + 100)
    lambda mod h2 = a polynomial of degree 31
    v = [x^4-x^3-1, x^3-x^2, x^2-x, x-1, 2, 0, 0, 0]
    Q -> (u^3*(u-1)-1)*Q + u^2*(u-1)*psi(Q) + u*(u-1)*psi^2(Q) + (u-1)*psi^3(Q) + 2*psi^4(Q)
    """
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)
    mu2 = mu.frobenius()*mu

    Q2 = 2*Q
    u1Q = (u-1)*Q
    u2Q = u*u1Q   # u*(u-1)*Q
    u3Q = u*u2Q   # u^2*(u-1)*Q
    u4Q = u*u3Q-Q # (u^3*(u-1)-1)*Q

    psi3Q = endomorphism_g2_psi_p(u1Q, None, mu2, 6, 2, D_twist)
    psi1Q = endomorphism_g2_psi_p(u3Q + psi3Q, None, mu, 6, 1, D_twist)
    psi4Q = endomorphism_g2_psi_p(Q2, None, mu2, 6, 2, D_twist)
    psi2Q = endomorphism_g2_psi_p(u2Q+psi4Q, None, mu2, 6, 2, D_twist)

    return u4Q + psi1Q + psi2Q

def membership_testing_g1_bls24(P, u, omega):
    """
    G1 membership testing, phi(P) = (omega*x, y) = [-u^4]*P if P is in G1

    INPUT:
    - `P`: point on E(Fp)
    - `u`: curve seed
    - `omega`: such that (omega*x, y) has eigenvalue -u^4
    """
    u4P = u**4*P
    phiP = P.curve()((P[0]*omega, P[1], P[2]))
    return (phiP + u4P).is_zero()

def membership_testing_g2_bls24(Q, u, Fq6, D_twist=True):
    """
    same fonction as for BLS12
    G2 membership testing from ePrint 2021/1130 Michael Scott
    https://eprint.iacr.org/2021/1130
    as soon as r = u^8-u^4+1 is prime, testing psi(Q) = u*Q is enough
    INPUT:
    - `Q`: point on compressed G2 in E'(p4)
    - `u`: curve seed
    - `Fq6`: explicit degree 6 extension on top of Fq = Fp4
    - `D_twist`: a Divide-twist or a Multiply-twist
    """
    xi = -Fq6.modulus().constant_coefficient()
    p = Fq6.characteristic()
    mu = xi**((p-1)//6)

    uQ = u*Q
    psi1Q = endomorphism_g2_psi_p(Q, None, mu, 6, 1, D_twist)
    return (psi1Q - uQ).is_zero()
