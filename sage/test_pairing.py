from sage.rings.finite_rings.finite_field_constructor import GF
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from sage.arith.misc import primes, prime_divisors, prime_factors
from sage.arith.misc import euler_phi, divisors, gcd
from pairing import *

# this is much much faster with this statement:
# proof.arithmetic(False)
# from sage.structure.proof.all import arithmetic
# arithmetic(False) # in the 'main' part

def test_double_line_j(E, E2, Fqd, D_twist=False):
    """
    Testing double line function in Jacobian coordinates in Miller algorithm.

    INPUT:
    - `E`: elliptic curve defined over a prime field, of order r*c (c might be 1, r must be prime)
    - `E2`: elliptic curve defined over a field Fp^(k/d) of order c2*r
    - `Fqd` degree-d extension field, d in {2,4,6}
    - `D-twist`: flag
    """
    w = Fqd.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        S2 = 2*S
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a, a**2)
            for (T, str_T) in ((S,"S"), (-S2, "-2*S")):
                line, R = double_line_j(Sa, (T[0],T[1]), E.a4())
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_j(S, {}, a)".format(str_T))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_j(S, {}, a)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_j(P, Q, a): {}".format(ok))
    # 2. test with S in E2/Fqd
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a, a**2)
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiSa = psi_sextic_d_twist(Sa, w)
                psi2S = psi_sextic_d_twist(S2, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiSa = psi_sextic_m_twist(Sa, w)
                psi2S = psi_sextic_m_twist(S2, w)
            psiS = (psiS[0], psiS[1])
            psi_2S = (psi2S[0], -psi2S[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psi_2S, "-psi(2*S)")):
                line, R = double_line_j(psiSa, psiT, E.a4())
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == psi2S[0] and R_aff[1] == psi2S[1]
                if not ok:
                    print("Error double_line_j(psi(S), {}, a)".format(str_T))
                    print("2*psi(S): obtained {}\naffine {}\n expected {}".format(R, R_aff, psi2S))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_j(S, {}, a)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_j(Q, P, a): {}".format(ok))
    return ok

def test_double_line_j_no_twist(E, str_E=""):
    """
    Testing addition line function in Jacobian coordinates in Miller algorithm.

    INPUT:
    - `E`: elliptic curve defined over a field
    """
    E0 = E(0)
    list_a = [1, 2, 3, 11]
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        S2 = 2*S
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a, a**2)
            for (T, str_T) in ((S,"S"), (-S2, "-2*S")):
                line, R = double_line_j(Sa, (T[0],T[1]), E.a4())
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_j(S, {}, a) without twist{}".format(str_T, str_E))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_j(S, {}, a) without twist{}".format(str_T, str_E))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_j(P, Q, a) without twist{}: {}".format(str_E, ok))

def test_double_line_affine_j(E, E2, Fqd, D_twist=False):
    """
    Testing double line function with affine input and Jacobian ouput coordinates in Miller algorithm.

    INPUT:
    - `E`: elliptic curve defined over a prime field, of order r*c (c might be 1, r must be prime)
    - `E2`: elliptic curve defined over a field Fp^(k/d) of order c2*r
    - `Fqd` degree-d extension field, d in {2,4,6}
    - `D-twist`: flag
    """
    w = Fqd.gen(0)
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        S2 = 2*S
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        Sa = (S[0], S[1])
        for (T, str_T) in ((S,"S"), (-S2, "-2*S")):
            line, R = double_line_affine_j(Sa, (T[0],T[1]), E.a4())
            R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
            ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
            if not ok:
                print("Error double_line_affine_j(S, {}, a)".format(str_T))
                print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                return False
            ok = line == 0
            if not ok:
                print("Error double_line_affine_j(S, {}, a)".format(str_T))
                print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                return False
        i = i+1
    if not D_twist:
        print("test double_line_affine_j(P, Q, a) with M-twist: {}".format(ok))
    else:
        print("test double_line_affine_j(P, Q, a) with D-twist: {}".format(ok))
    # 2. test with S in E2/Fqd
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        Sa = (S[0], S[1])
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiSa = psi_sextic_d_twist(Sa, w)
            psi2S = psi_sextic_d_twist(S2, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiSa = psi_sextic_m_twist(Sa, w)
            psi2S = psi_sextic_m_twist(S2, w)
        psiS = (psiS[0], psiS[1])
        psi_2S = (psi2S[0], -psi2S[1])
        for (psiT, str_psiT) in ((psiS,"psi(S)"), (psi_2S, "-psi(2*S)")):
            line, R = double_line_affine_j(psiSa, psiT, E.a4())
            R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
            ok = R_aff[0] == psi2S[0] and R_aff[1] == psi2S[1]
            if not ok:
                print("Error double_line_affine_j(psi(S), {}, a)".format(str_T))
                print("2*psi(S): obtained {}\naffine {}\n expected {}".format(R, R_aff, psi2S))
                return False
            ok = line == 0
            if not ok:
                print("Error double_line_affine_j(S, {}, a)".format(str_T))
                print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                return False
        i = i+1
    if not D_twist:
        print("test double_line_affine_j(Q, P, a) with M-twist: {}".format(ok))
    else:
        print("test double_line_affine_j(Q, P, a) with D-twist: {}".format(ok))
    return ok

def test_add_line_j(E, E2, Fqd, D_twist=False):
    """
    Testing addition line function in Jacobian coordinates in Miller algorithm.

    INPUT:
    - `E`: elliptic curve defined over a prime field, of order r*c (c might be 1, r must be prime)
    - `E2`: elliptic curve defined over a field Fp^(k/d) of order c2*r
    - `Fqd` degree-d extension field, d in {2, 4, 6}
    - `D-twist`: flag
    """
    w = Fqd.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S, Q in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a, a**2)
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_j(Sa, (Q[0], Q[1]), (T[0],T[1]))
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_j(S, Q, {})".format(str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_j(S, Q, {})".format(str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    if not D_twist:
        print("test add_line_j(R, P, Q) with M-twist: {}".format(ok))
    else:
        print("test add_line_j(R, P, Q) with D-twist: {}".format(ok))
    # 2. test with S, Q in E2/Fqd
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a, a**2)
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiQ = psi_sextic_d_twist(Q, w)
                psiSa = psi_sextic_d_twist(Sa, w)
                psiSQ = psi_sextic_d_twist(SQ, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiQ = psi_sextic_m_twist(Q, w)
                psiSa = psi_sextic_m_twist(Sa, w)
                psiSQ = psi_sextic_m_twist(SQ, w)
            psiS = (psiS[0], psiS[1])
            psiQ = (psiQ[0], psiQ[1])
            psi_SQ = (psiSQ[0], -psiSQ[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
                line, R = add_line_j(psiSa, psiQ, psiT)
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == psiSQ[0] and R_aff[1] == psiSQ[1]
                if not ok:
                    print("Error add_line_j(psi(S), psi(Q), {})".format(str_T))
                    print("psi(S+Q): obtained {}\naffine {}\n expected {}".format(R, R_aff, psiSQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_j(psi(S), psi(Q), {})".format(str_T))
                    print("line through psi(S) and psi(Q) evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    if not D_twist:
        print("test add_line_j(S, Q, P) with M-twist: {}".format(ok))
    else:
        print("test add_line_j(S, Q, P) with D-twist: {}".format(ok))
    return ok

def test_add_line_j_no_twist(E, str_E=""):
    """
    Testing addition line function in Jacobian coordinates in Miller algorithm.

    INPUT:
    - `E`: elliptic curve defined over a field
    """
    list_a = [1, 2, 3, 11]
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a, a**2)
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_j(Sa, (Q[0], Q[1]), (T[0],T[1]))
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_j(S, Q, {}) without twist{}".format(str_T, str_E))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_j(S, Q, {}) without twist{}".format(str_T, str_E))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_j(R, P, Q) without twist{}: {}".format(str_E, ok))

def test_add_line_j_with_z_no_twist(E, str_E=""):
    """
    Testing addition line function in Jacobian coordinates in Miller algorithm.

    INPUT:
    - `E`: elliptic curve defined over a field
    """
    list_a = [1, 2, 3, 11]
    list_b = [1, 2, 3, 11]
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a, a**2)
            for b in list_a:
                Qb = (Q[0]*b**2, Q[1]*b**3, b, b**2)
                for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                    line, R = add_line_j_with_z(Sa, Qb, (T[0],T[1]))
                    R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                    ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                    if not ok:
                        print("Error add_line_j_with_z(S, Q, {}) without twist{}".format(str_T, str_E))
                        print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                        return False
                    ok = line == 0
                    if not ok:
                        print("Error add_line_j_with_z(S, Q, {}) without twist{}".format(str_T, str_E))
                        print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                        return False
        i = i+1
    print("test add_line_j_with_z(R, P, Q) without twist{}: {}".format(str_E, ok))

def test_add_line_affine_j(E, E2, Fqd, D_twist=False):
    """
    Testing addition line function with affine input and Jacobian ouput coordinates in Miller algorithm.

    INPUT:
    - `E`: elliptic curve defined over a prime field, of order r*c (c might be 1, r must be prime)
    - `E2`: elliptic curve defined over a field Fp^(k/d) of order c2*r
    - `Fqd` degree-d extension field, d in {2, 4, 6}
    - `D-twist`: flag
    """
    w = Fqd.gen(0)
    # 1. test with S, Q in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        Sa = (S[0], S[1])
        for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
            line, R = add_line_affine_j(Sa, (Q[0], Q[1]), (T[0],T[1]))
            R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
            ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
            if not ok:
                print("Error add_line_affine_j(S, Q, {})".format(str_T))
                print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                return False
            ok = line == 0
            if not ok:
                print("Error add_line_affine_j(S, Q, {})".format(str_T))
                print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                return False
        i = i+1
    if not D_twist:
        print("test add_line_affine_j(R, P, Q) with M-twist: {}".format(ok))
    else:
        print("test add_line_affine_j(R, P, Q) with D-twist: {}".format(ok))
    # 2. test with S, Q in E2/Fqd
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        # S in extended Jacobian coordinates, affine = (X/Z^2, Y/Z^3)
        # (X,Y,Z,Z^2) ~ (X*a^2, Y*a^3, Z*a, Z^2*a^2)
        Sa = (S[0], S[1])
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
            psiSQ = psi_sextic_d_twist(SQ, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
            psiSQ = psi_sextic_m_twist(SQ, w)
        psiS = (psiS[0], psiS[1])
        psiQ = (psiQ[0], psiQ[1])
        psi_SQ = (psiSQ[0], -psiSQ[1])
        for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
            line, R = add_line_affine_j(psiS, psiQ, psiT)
            R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
            ok = R_aff[0] == psiSQ[0] and R_aff[1] == psiSQ[1]
            if not ok:
                print("Error add_line_affine_j(psi(S), psi(Q), {})".format(str_T))
                print("psi(S+Q): obtained {}\naffine {}\n expected {}".format(R, R_aff, psiSQ))
                return False
            ok = line == 0
            if not ok:
                print("Error add_line_affine_j(psi(S), psi(Q), {})".format(str_T))
                print("line through psi(S) and psi(Q) evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                return False
        i = i+1
    if not D_twist:
        print("test add_line_affine_j(S, Q, P) with M-twist: {}".format(ok))
    else:
        print("test add_line_affine_j(S, Q, P) with D-twist: {}".format(ok))
    return ok

def test_double_line_j_csb(E, E2, Fqd, D_twist=False):
    """
    Testing double line function in Jacobian coordinates in Miller algorithm,
    with Chatterjee Sarkar Barua formulas
    Sanjit Chatterjee, Palash Sarkar, Rana Barua:
    Efficient Computation of Tate Pairing in Projective Coordinate over General
    Characteristic Fields. ICISC 2004: 168-181
    https://doi.org/10.1007/11496618_13
    https://www.researchgate.net/profile/Rana-Barua/publication/220833962_Efficient_Computation_of_Tate_Pairing_in_Projective_Coordinate_over_General_Characteristic_Fields/links/53cf450d0cf25dc05cfadfe0/Efficient-Computation-of-Tate-Pairing-in-Projective-Coordinate-over-General-Characteristic-Fields.pdf

    INPUT:
    - `E`: elliptic curve defined over a prime field, of order r*c (c might be 1, r must be prime)
    - `E2`: elliptic curve defined over a field Fp^(k/d) of order c2*r
    - `Fqd` degree-d extension field, d in {2,4,6}
    - `D-twist`: flag
    """
    w = Fqd.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        S2 = 2*S
        # S in Jacobian coordinates (X, Y, Z) ~ (a^2*X, a^3*Y, a*Z)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a)
            for (T, str_T) in ((S,"S"), (-S2, "-2*S")):
                line, R = double_line_j_csb(Sa, (T[0],T[1]), E.a4())
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_j_csb(S, {}, a)".format(str_T))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_j_csb(S, {}, a)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_j_csb(P, Q, a): {}".format(ok))
    # 2. test with S in E2/Fqd
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        # S in Jacobian coordinates (X, Y, Z) ~ (a^2*X, a^3*Y, a*Z)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a)
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiSa = psi_sextic_d_twist(Sa, w)
                psi2S = psi_sextic_d_twist(S2, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiSa = psi_sextic_m_twist(Sa, w)
                psi2S = psi_sextic_m_twist(S2, w)
            psiS = (psiS[0], psiS[1])
            psi_2S = (psi2S[0], -psi2S[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psi_2S, "-psi(2*S)")):
                line, R = double_line_j_csb(psiSa, psiT, E.a4())
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == psi2S[0] and R_aff[1] == psi2S[1]
                if not ok:
                    print("Error double_line_j_csb(psi(S), {}, a)".format(str_T))
                    print("2*psi(S): obtained {}\naffine {}\n expected {}".format(R, R_aff, psi2S))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_j_csb(S, {}, a)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_j_csb(Q, P, a): {}".format(ok))
    return ok

def test_add_line_j_csb(E, E2, Fqd, D_twist=False):
    """
    Testing addition line function in Jacobian coordinates in Miller algorithm,
    with Chatterjee Sarkar Barua formulas
    Sanjit Chatterjee, Palash Sarkar, Rana Barua:
    Efficient Computation of Tate Pairing in Projective Coordinate over General
    Characteristic Fields. ICISC 2004: 168-181
    https://doi.org/10.1007/11496618_13
    https://www.researchgate.net/profile/Rana-Barua/publication/220833962_Efficient_Computation_of_Tate_Pairing_in_Projective_Coordinate_over_General_Characteristic_Fields/links/53cf450d0cf25dc05cfadfe0/Efficient-Computation-of-Tate-Pairing-in-Projective-Coordinate-over-General-Characteristic-Fields.pdf

    INPUT:
    - `E`: elliptic curve defined over a prime field, of order r*c (c might be 1, r must be prime)
    - `E2`: elliptic curve defined over a field Fp^(k/d) of order c2*r
    - `Fqd` degree-d extension field, d in {2, 4, 6}
    - `D-twist`: flag
    """
    w = Fqd.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S, Q in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        # S in Jacobian coordinates (X, Y, Z) ~ (a^2*X, a^3*Y, a*Z)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a)
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_j_csb(Sa, (Q[0], Q[1]), (T[0],T[1]))
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_j_csb(S, Q, {})".format(str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_j_csb(S, Q, {})".format(str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_j_csb(P, Q, a): {}".format(ok))
    # 2. test with S, Q in E2/Fqd
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        # S in Jacobian coordinates (X, Y, Z) ~ (a^2*X, a^3*Y, a*Z)
        for a in list_a:
            Sa = (S[0]*a**2, S[1]*a**3, a)
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiQ = psi_sextic_d_twist(Q, w)
                psiSa = psi_sextic_d_twist(Sa, w)
                psiSQ = psi_sextic_d_twist(SQ, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiQ = psi_sextic_m_twist(Q, w)
                psiSa = psi_sextic_m_twist(Sa, w)
                psiSQ = psi_sextic_m_twist(SQ, w)
            psiS = (psiS[0], psiS[1])
            psiQ = (psiQ[0], psiQ[1])
            psi_SQ = (psiSQ[0], -psiSQ[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
                line, R = add_line_j_csb(psiSa, psiQ, psiT)
                R_aff = (R[0]/R[2]**2, R[1]/R[2]**3)
                ok = R_aff[0] == psiSQ[0] and R_aff[1] == psiSQ[1]
                if not ok:
                    print("Error add_line_j_csb(psi(S), psi(Q), {})".format(str_T))
                    print("psi(S+Q): obtained {}\naffine {}\n expected {}".format(R, R_aff, psiSQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_j_csb(psi(S), psi(Q), {})".format(str_T))
                    print("line through psi(S) and psi(Q) evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_j_csb(Q, P, a): {}".format(ok))
    return ok

def test_double_line_cln_b0(E, E2, Fq4, D_twist=False):
    """ Testing double_line_cln_b0 function

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fqd (the d-twist)
    - `Fq4`: the degree-4 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist
    """
    w = Fq4.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        S2 = 2*S
        for a in list_a: # (X/Z, Y/Z^2) ~ (X,Y,Z) so (X*a,Y*a^2, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a*a, a)
            for (T, str_T) in ((S,"S"), (-S2, "-2*S")):
                line, R = double_line_cln_b0(Sa, (T[0],T[1]), E.a4())
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_cln_b0(S, {}, a)".format(str_T))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_cln_b0(S, {}, a)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_cln_b0(P, Q, a): {}".format(ok))
    # 2. test with S in E2/Fq4
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        for a in list_a:
            Sa = (S[0]*a, S[1]*a*a, a)
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiSa = psi_sextic_d_twist(Sa, w)
                psi2S = psi_sextic_d_twist(S2, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiSa = psi_sextic_m_twist(Sa, w)
                psi2S = psi_sextic_m_twist(S2, w)
            psiS = (psiS[0], psiS[1])
            psi_2S = (psi2S[0], -psi2S[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psi_2S, "-psi(2*S)")):
                line, R = double_line_cln_b0(psiSa, psiT, E.a4())
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == psi2S[0] and R_aff[1] == psi2S[1]
                if not ok:
                    print("Error double_line_cln_b0(psi(S), {}, a)".format(str_T))
                    print("2*psi(S): obtained {}\naffine {}\n expected {}".format(R, R_aff, psi2S))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_cln_b0(S, {}, a)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_cln_b0(Q, P, a): {}".format(ok))
    return ok

def test_double_line_ate_cln_b0(E, E2, Fq4, D_twist=False):
    """ Testing double_line_ate_cln_b0 function with explicit quartic twist

    double_line_ate_cln_b0(S, P, a_t, D_twist=False)

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fqd (the d-twist)
    - `Fq4`: the degree-4 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist
    """
    w = Fq4.gen(0)
    xi = -Fq4.modulus().constant_coefficient()
    assert w**4 == xi
    list_a = [1, 2, 3, 11]
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        S2 = 2*S
        for a in list_a: # (X/Z, Y/Z^2) ~ (X,Y,Z) so (X*a,Y*a^2, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a*a, a)
            for (T, str_T) in ((S,"S"), (-S2, "-2*S")):
                line, R = double_line_ate_cln_b0(Sa, (T[0],T[1]), E.a4())
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_ate_cln_b0(S, {}, a)".format(str_T))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error double_line_ate_cln_b0(S, {}, a)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, sum(line)))
                    return False
        i = i+1
    print("test double_line_ate_cln_b0(P, Q, a): {}".format(ok))
    # 2. test with S in E2/Fq4
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        for a in list_a:
            Sa = (S[0]*a, S[1]*a*a, a)
            for (T, str_T) in (((S[0],S[1]),"S"), ((S2[0],-S2[1]), "-(2*S)")):
                line, R = double_line_ate_cln_b0(Sa, T, E2.a4(), D_twist=D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_ate_cln_b0(S, {}, a_t, D_twist={})".format(str_T, D_twist))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error double_line_ate_cln_b0(S, {}, a_t, D_twist={})".format(str_T, D_twist))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, Fq4(line)))
                    return False
        i = i+1
    print("test double_line_ate_cln_b0(Q, P, a_t, D_twist={}): {}".format(D_twist, ok))

    print("compare double_line_cln_b0 to double_line_ate_cln_b0")
    ok = True
    i = 0
    T = E.random_element()
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        for a in list_a:
            Sa = (S[0]*a, S[1]*a*a, a)
            line, R = double_line_ate_cln_b0(Sa, (T[0],T[1]), E2.a4(), D_twist=D_twist)
            line1 = Fq4(line)
            R_aff = (R[0]/R[2], R[1]/R[2]**2)
            if D_twist:
                psiSa = psi_sextic_d_twist(Sa, w)
            else:
                psiSa = psi_sextic_m_twist(Sa, w)
            line2, R2 = double_line_cln_b0(psiSa, (T[0],T[1]), E.a4())
            line2v = line2.list()
            R2_aff = (R2[0]/R2[2], R2[1]/R2[2]**2)
            if D_twist:# untwist
                RR = psi_sextic_m_twist(R2_aff, w)
                psiR = psi_sextic_d_twist(R_aff, w)
            else:
                RR = psi_sextic_d_twist(R2_aff, w)
                psiR = psi_sextic_m_twist(R_aff, w)
            ok = RR[0] == R_aff[0] and RR[1] == R_aff[1] and psiR[0] == R2_aff[0] and psiR[1] == R2_aff[1]
            if not ok:
                print("R and untwist(RR) match: {}".format(ok))
                print("R  = {}".format(R_aff))
                print("RR = {}".format(RR))
                return False
            if D_twist:
                s = 'D'
                ok = line1 == line2/w**3
            else:
                s = 'M'
                ok = line1 == line2*w**6
            if not ok:
                print("error {}-twist double_line_cln_b0(psi(S),P,a) and double_line_ate_cln_b0(S,P,a_t,D_twist={}) do not match".format(s, D_twist))
                return False
        i = i+1
    print("double_line_cln_b0 and double_line_ate_cln_b0 match: ok")
    return ok

def test_add_line_ate_cln_b0(E, E2, Fq4, D_twist=False):
    """ Testing add_line_ate_cln_b0 function

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fqd (the d-twist)
    - `Fq4`: the degree-4 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist
    """
    w = Fq4.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S, Q in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        for a in list_a: # (X/Z, Y/Z^2) ~ (X,Y,Z) so (X*a,Y*a^2, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a*a, a)
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_ate_cln_b0(Sa, (Q[0], Q[1]), (T[0],T[1]), D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_ate_cln_b0(S, Q, {})".format(str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error add_line_ate_cln_b0(S, Q, {})".format(str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, sum(line)))
                    return False
        i = i+1
    print("test add_line_ate_cln_b0(S, P, T), T in [P,S,-(P+S)]: {}".format(ok))
    # 2. test with S, Q in E2/Fq4
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        for a in list_a:
            Sa = (S[0]*a, S[1]*a*a, a)
            for (T, str_T) in (((S[0],S[1]),"S"), ((Q[0],Q[1]),"Q"), ((SQ[0],-SQ[1]), "-(S+Q)")):
                line, R = add_line_ate_cln_b0(Sa, (Q[0],Q[1]), T, D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_ate_cln_b0(S, Q, {})".format(str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error add_line_ate_cln_b0(S, Q, {})".format(str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, sum(line)))
                    return False
        i = i+1
    print("test add_line_ate_cln_b0(S, Q, T), T in [S,Q,-(S+Q)]: {}".format(ok))
    print("compare add_line_cln_b0 to add_line_ate_cln_b0")
    ok = True
    i = 0
    T = E.random_element()
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        for a in list_a:
            Sa = (S[0]*a, S[1]*a*a, a)
            line, R = add_line_ate_cln_b0(Sa, (Q[0],Q[1]), (T[0],T[1]), D_twist=D_twist)
            line1 = Fq4(line)
            R_aff = (R[0]/R[2], R[1]/R[2]**2)
            if D_twist:
                psiSa = psi_sextic_d_twist(Sa, w)
                psiQ =  psi_sextic_d_twist(Q, w)
            else:
                psiSa = psi_sextic_m_twist(Sa, w)
                psiQ =  psi_sextic_m_twist(Q, w)
            line2, R2 = add_line_cln_b0(psiSa, (psiQ[0],psiQ[1]), (T[0],T[1]))
            line2v = line2.list()
            R2_aff = (R2[0]/R2[2], R2[1]/R2[2]**2)
            if D_twist:# untwist
                RR = psi_sextic_m_twist(R2_aff, w)
                psiR = psi_sextic_d_twist(R_aff, w)
            else:
                RR = psi_sextic_d_twist(R2_aff, w)
                psiR = psi_sextic_m_twist(R_aff, w)
            ok = RR[0] == R_aff[0] and RR[1] == R_aff[1] and psiR[0] == R2_aff[0] and psiR[1] == R2_aff[1]
            if not ok:
                print("R and untwist(RR) match: {}".format(ok))
                print("R  = {}".format(R_aff))
                print("RR = {}".format(RR))
                return False
            if D_twist:
                s = 'D'
                ok = line1 == line2/w**2
            else:
                s = 'M'
                ok = line1 == line2*w**5
            if not ok:
                print("error {}-twist add_line_cln_b0(psi(S),P,a) and add_line_ate_cln_b0(S,P,a_t,D_twist={}) do not match".format(s, D_twist))
                return False
        i = i+1
    print("add_line_cln_b0 and add_line_ate_cln_b0 match: ok")
    return ok

def test_add_line_cln_b0(E, E2, Fq4, D_twist=False):
    """ Testing add_line_cln_b0 function

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fqd (the d-twist)
    - `Fq4`: the degree-4 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist
    """
    w = Fq4.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S, Q in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        for a in list_a: # (X/Z, Y/Z^2) ~ (X,Y,Z) so (X*a,Y*a^2, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a*a, a)
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_cln_b0(Sa, (Q[0], Q[1]), (T[0],T[1]))
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_b0(S, Q, {})".format(str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_b0(S, Q, {})".format(str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_cln_b0(S, P, T), T in [P,S,-(P+S)]: {}".format(ok))
    # 2. test with S, Q in E2/Fq4
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        for a in list_a:
            Sa = (S[0]*a, S[1]*a*a, a)
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiQ = psi_sextic_d_twist(Q, w)
                psiSa = psi_sextic_d_twist(Sa, w)
                psiSQ = psi_sextic_d_twist(SQ, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiQ = psi_sextic_m_twist(Q, w)
                psiSa = psi_sextic_m_twist(Sa, w)
                psiSQ = psi_sextic_m_twist(SQ, w)
            psiS = (psiS[0], psiS[1])
            psiQ = (psiQ[0], psiQ[1])
            psi_SQ = (psiSQ[0], -psiSQ[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
                line, R = add_line_cln_b0(psiSa, psiQ, psiT)
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == psiSQ[0] and R_aff[1] == psiSQ[1]
                if not ok:
                    print("Error add_line_cln_b0(psi(S), psi(Q), {})".format(str_T))
                    print("psi(S+Q): obtained {}\naffine {}\n expected {}".format(R, R_aff, psiSQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_b0(psi(S), psi(Q), {})".format(str_T))
                    print("line through psi(S) and psi(Q) evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_cln_b0(S, Q, T), T in [Q,S,-(Q+S)]: {}".format(ok))
    return ok

def test_add_line_cln_b0_with_z(E, E2, Fq4, D_twist=False):
    w = Fq4.gen(0)
    list_ab = [(1, 1), (1, 2), (1, 7), (3, 1), (3, 2), (3, 7), (11, 1), (11, 2), (11, 7)]
    ok = True
    i = 0
    while i < 10:
        # 1. test with S, Q in E/Fp
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        for (a,b) in list_ab: # (X/Z, Y/Z^2) ~ (X,Y,Z) so (X*a,Y*a^2, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a*a, a)
            Qb = (Q[0]*b, Q[1]*b*b, b)
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_cln_b0_with_z(Sa, Qb, (T[0],T[1]))
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_b0_with_z(S, Q, {})".format(str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_b0_with_z(S, Q, {})".format(str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    # 2. test with S, Q in E2/Fq4
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        for a,b in list_ab:
            Sa = (S[0]*a, S[1]*a*a, a)
            Qb = (Q[0]*b, Q[1]*b*b, b)
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiQ = psi_sextic_d_twist(Q, w)
                psiSa = psi_sextic_d_twist(Sa, w)
                psiQb = psi_sextic_d_twist(Qb, w)
                psiSQ = psi_sextic_d_twist(SQ, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiQ = psi_sextic_m_twist(Q, w)
                psiSa = psi_sextic_m_twist(Sa, w)
                psiQb = psi_sextic_m_twist(Qb, w)
                psiSQ = psi_sextic_m_twist(SQ, w)
            psiS = (psiS[0], psiS[1])
            psiQ = (psiQ[0], psiQ[1])
            psi_SQ = (psiSQ[0], -psiSQ[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
                line, R = add_line_cln_b0_with_z(psiSa, psiQb, psiT)
                R_aff = (R[0]/R[2], R[1]/R[2]**2)
                ok = R_aff[0] == psiSQ[0] and R_aff[1] == psiSQ[1]
                if not ok:
                    print("Error add_line_cln_b0_with_z(psi(S), psi(Q), {})".format(str_T))
                    print("psi(S+Q): obtained {}\naffine {}\n expected {}".format(R, R_aff, psiSQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_b0_with_z(psi(S), psi(Q), {})".format(str_T))
                    print("line through psi(S) and psi(Q) evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_cln_b0_with_z: {}".format(ok))
    return ok

### CLN projective coordinates a=0 quadratic twist

def test_double_line_cln_a0_quad_twist(E, E2, Fq2, D_twist=False):
    """ Testing double_line_cln_a0_quad_twist function with explicit quadratic twist

    double_line_cln_a0_quad_twist(S, P, b_t, Fq2, D_twist=False)

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fq2 (a quadratic twist)
    - `Fq2`: the degree-2 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist
    """
    w = Fq2.gen(0)
    xi = -Fq2.modulus().constant_coefficient()
    assert w**2 == xi
    list_a = [1, 2, 3, 11]
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while ok and i < 10:
        S = E.random_element()
        S2 = 2*S
        for a in list_a: # (X/Z, Y/Z) ~ (X,Y,Z) so (X*a,Y*a, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a, a)
            for (T, str_T) in ((S,"S"), (-S2, "-2*S")):
                # do not pass Fq2 nor D_twist as argument to avoid multiplication by w or xi
                line, R = double_line_cln_a0_quad_twist(Sa, (T[0],T[1]), E.a6())
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_cln_a0_quad_twist(S, {}, b)".format(str_T))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = line == 0
                if not ok:
                    print("Error double_line_cln_a0_quad_twist(S, {}, b)".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test double_line_cln_a0_quad_twist(P, Q, b, None, None): {}".format(ok))
    # 1bis test with untwisting P
    ok = True
    i = 0
    while ok and i < 10:
        S = E.random_element()
        S2 = 2*S
        # untwist(S), untwist(2S)
        if D_twist:
            psiS = psi_sextic_m_twist(S, w)
            psiS2 = psi_sextic_m_twist(S2, w)
        else:
            psiS = psi_sextic_d_twist(S, w)
            psiS2 = psi_sextic_d_twist(S2, w)
        for a in list_a: # (X/Z, Y/Z) ~ (X,Y,Z) so (X*a,Y*a, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a, a)
            for (T, str_T) in (((psiS[0],psiS[1]),"S"), ((psiS2[0],-psiS2[1]), "-(2*S)")):
                # evaluate at untwist(S), untwist(-2S)
                line, R = double_line_cln_a0_quad_twist(Sa, (T[0],T[1]), E.a6(), Fq2, not D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_cln_a0_quad_twist(S, {}, b, Fq2, {})".format(str_T, not D_twist))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error double_line_cln_a0_quad_twist(S, {}, b, Fq2, {})".format(str_T, not D_twist))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, sum(line)))
                    return False
        i = i+1
    print("test double_line_cln_a0_quad_twist(P, Q, b, Fq2, {}): {}".format(not D_twist, ok))
    # 2. test with S in E2/Fq2
    ok = True
    i = 0
    while ok and i < 10:
        S = E2.random_element()
        S2 = 2*S
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiS2 = psi_sextic_d_twist(S2, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiS2 = psi_sextic_m_twist(S2, w)
        for a in list_a:
            Sa = (S[0]*a, S[1]*a, a)
            for (T, str_T) in (((psiS[0],psiS[1]),"S"), ((psiS2[0],-psiS2[1]), "-(2*S)")):
                # evaluate at psi(S), psi(-2S) on E instead of S, -2S on E2
                line, R = double_line_cln_a0_quad_twist(Sa, T, E2.a6(), Fq2, D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
                if not ok:
                    print("Error double_line_cln_a0_quad_twist(S, {}, b_t, Fq2, D_twist={})".format(str_T, D_twist))
                    print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error double_line_cln_a0_quad_twist(S, {}, b_t, Fq2, D_twist={})".format(str_T, D_twist))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, Fq2(line)))
                    return False
        i = i+1
    print("test double_line_cln_a0_quad_twist(Q, P, b_t, Fq2, D_twist={}): {}".format(D_twist, ok))
    return ok

def test_add_line_cln_a0_quad_twist(E, E2, Fq2, D_twist=False):
    """ Testing add_line_cln_a0_quad_twist function with explicit quadratic twist

    add_line_cln_a0_quad_twist(S, Q, P, Fq2, D_twist=False)

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fq2 (a quadratic twist)
    - `Fq2`: the degree-2 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist
    """
    w = Fq2.gen(0)
    xi = -Fq2.modulus().constant_coefficient()
    assert w**2 == xi
    list_a = [1, 2, 3, 11]
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while ok and i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        for a in list_a: # (X/Z, Y/Z) ~ (X,Y,Z) so (X*a,Y*a, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a, a)
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                # do not pass Fq2 nor D_twist as argument to avoid multiplication by w or xi
                line, R = add_line_cln_a0_quad_twist(Sa, (Q[0], Q[1]), (T[0],T[1]))
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_a0_quad_twist(S, Q, {})".format(str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_a0_quad_twist(S, Q, {})".format(str_T))
                    print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_cln_a0_quad_twist(P, Q, None, None): {}".format(ok))
    # 1bis test with untwisting P
    ok = True
    i = 0
    while ok and i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        # untwist(S), untwist(2S)
        if D_twist:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
            psiSQ = psi_sextic_m_twist(SQ, w)
        else:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
            psiSQ = psi_sextic_d_twist(SQ, w)
        for a in list_a: # (X/Z, Y/Z) ~ (X,Y,Z) so (X*a,Y*a, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a, a)
            for (T, str_T) in (((psiS[0],psiS[1]),"S"), ((psiQ[0],psiQ[1]),"Q"), ((psiSQ[0],-psiSQ[1]), "-(S+Q)")):
                # evaluate at untwist(S), untwist(Q), untwist(-(S+Q))
                line, R = add_line_cln_a0_quad_twist(Sa, (Q[0],Q[1]), (T[0],T[1]), Fq2, not D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_a0_quad_twist(S, Q, {}, Fq2, {})".format(str_T, not D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    #return False
                ok = sum(line) == 0
                if not ok:
                    print("Error add_line_cln_a0_quad_twist(S, {}, Fq2, {})".format(str_T, not D_twist))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, sum(line)))
                    #return False
        i = i+1
    print("test add_line_cln_a0_quad_twist(P, Q, Fq2, {}): {}".format(not D_twist, ok))
    # 2. test with S in E2/Fq2
    ok = True
    i = 0
    while ok and i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
            psiSQ = psi_sextic_d_twist(SQ, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
            psiSQ = psi_sextic_m_twist(SQ, w)
        for a in list_a:
            Sa = (S[0]*a, S[1]*a, a)
            for (T, str_T) in (((psiS[0],psiS[1]),"S"), ((psiQ[0],psiQ[1]),"Q"), ((psiSQ[0],-psiSQ[1]), "-(S+Q)")):
                # evaluate at psi(S), psi(Q), psi(-(S+Q)) on E instead of S, Q, -(S+Q) on E2
                line, R = add_line_cln_a0_quad_twist(Sa, (Q[0], Q[1]), T, Fq2, D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_a0_quad_twist(S, Q, {}, Fq2, D_twist={})".format(str_T, D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error add_line_cln_a0_quad_twist(S, Q, {}, Fq2, D_twist={})".format(str_T, D_twist))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, Fq2(line)))
                    return False
        i = i+1
    print("test add_line_cln_a0_quad_twist(S, Q, P, Fq2, D_twist={}): {}".format(D_twist, ok))
    return ok

### CLN Projective coordinates a=0 cubic twist

def test_double_line_cln_a0_cubic_twist(E, E2, Fq3, D_twist=False):
    """ Testing double_line_cln_a0_cubic_twist function

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fq where q=p^(k/3) (3-twist)
    - `Fq3`: the degree-3 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist

    idea of the test: a tangent line at S vanishes at S and at -2*S
    test if l_{S,S}(S) is zero, l_{S,S}(-2S) is zero
    but because of the simplification of the formulas in [CLN],
    it does not vanish at -2S. Testing at S only.

    Third test: with explicit cubic twist
    """
    w = Fq3.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        S2 = 2*S
        for a in list_a: # (X/Z, Y/Z) ~ (X,Y,Z) so (X*a,Y*a, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a, a)
            (T, str_T) = (S,"S") # it does not work for (-S2, "-2*S")
            # because there were simplifications in the line formula, assuming it is not zero
            line, R = double_line_cln_a0_cubic_twist(Sa, (T[0],T[1],T[0]**2), E.a6())
            R_aff = (R[0]/R[2], R[1]/R[2])
            ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
            if not ok:
                print("Error double_line_cln_a0_cubic_twist(S, {}, b)".format(str_T))
                print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                return False
            ok = line == 0
            if not ok:
                print("Error double_line_cln_a0_cubic_twist(S, {}, b)".format(str_T))
                print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                return False
        i = i+1
    print("test double_line_cln_a0_cubic_twist(P, Q, b): {}".format(ok))
    # 2. test with S in E2/Fq3
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psi2S = psi_sextic_d_twist(S2, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psi2S = psi_sextic_m_twist(S2, w)
        psiS = (psiS[0], psiS[1], psiS[0]**2)
        psi_2S = (psi2S[0], -psi2S[1], psi2S[0]**2)
        for a in list_a:
            Sa = (S[0]*a, S[1]*a, a)
            if D_twist:
                psiSa = psi_sextic_d_twist(Sa, w)
            else:
                psiSa = psi_sextic_m_twist(Sa, w)
            psiT, str_psiT =(psiS,"psi(S)") # does not work with (psi_2S, "-psi(2*S)")
            line, R = double_line_cln_a0_cubic_twist(psiSa, psiT, E.a6())
            R_aff = (R[0]/R[2], R[1]/R[2])
            ok = R_aff[0] == psi2S[0] and R_aff[1] == psi2S[1]
            if not ok:
                print("Error double_line_cln_a0_cubic_twist(psi(S), {}, b)".format(str_psiT))
                print("2*psi(S): obtained {}\naffine {}\n expected {}".format(R, R_aff, psi2S))
                return False
            ok = line == 0
            if not ok:
                print("Error double_line_cln_a0_cubic_twist(psi(S), {}, b)".format(str_psiT))
                print("line tangent at psi(S) evaluated at {} should be 0, obtained\nline = {}".format(str_psiT, line))
                return False
        i = i+1
    print("test double_line_cln_a0_cubic_twist(Q, P, b): {}".format(ok))

    # 3. this time explicitly give the point S on the cubic twist
    w = Fq3.gen(0)
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        S2 = 2*S
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
        psiS = (psiS[0], psiS[1], psiS[0]**2)
        str_psiS = "psi(S)"
        for a in list_a:
            Sa = (S[0]*a, S[1]*a, a)
            line, R = double_line_cln_a0_cubic_twist(Sa, psiS, E2.a6(), Fq3, D_twist)
            R_aff = (R[0]/R[2], R[1]/R[2])
            ok = R_aff[0] == S2[0] and R_aff[1] == S2[1]
            if not ok:
                print("Error double_line_cln_a0_cubic_twist(S, {}, b_t, Fq3, D_twist={})".format(str_psiS, D_twist))
                print("2*S: obtained {}\naffine {}\n expected {}".format(R, R_aff, S2))
                return False
            ok = line == 0
            if not ok:
                print("Error double_line_cln_a0_cubic_twist(S, {}, b_t, Fq3, D_twist={})".format(str_psiS, D_twist))
                print("line tangent at S evaluated at {} should be 0, obtained\nline = {}".format(str_psiS, line))
                print("compare to double_line_cln_a0_cubic_twist(psiS, {}):".format(str_psiS))
                if D_twist:
                    psiSa = psi_sextic_d_twist(Sa, w)
                else:
                    psiSa = psi_sextic_m_twist(Sa, w)
                line2, R2 = double_line_cln_a0_cubic_twist(psiSa, psiS, E.a6())
                print("one obain line2 = {}".format(line2))
                for PP, strPP in [((0,0,0), "(0,0,0)"), ((1,0,0), "(1,0,0)"), ((0,1,0), "(0,1,0)"), ((0,0,1), "(0,0,1)")]:
                    print("double_line_cln_a0_cubic_twist(S, {}, Fq3, D_twist={})".format(strPP, D_twist))
                    line3, RR = double_line_cln_a0_cubic_twist(S, PP, E2.a6(), Fq3, D_twist)
                    line4, R4 = double_line_cln_a0_cubic_twist((psiS[0], psiS[1], 1), PP, E.a6())
                    print("line3: {} (with explicit cubic twist)".format(line3))
                    print("line4: {} (with psi(S), implicit cubic twist)".format(line4))
                    # with Sa instead of S
                    if a != 1:
                        print("double_line_cln_a0_cubic_twist(S{}, {}, Fq3, D_twist={})".format(a, strPP, D_twist))
                        line3, RR = double_line_cln_a0_cubic_twist(Sa, PP, E2.a6(), Fq3, D_twist)
                        line4, R4 = double_line_cln_a0_cubic_twist((psiSa[0], psiSa[1], 1), PP, E.a6())
                        print("line3: {} (with explicit cubic twist)".format(line3))
                        print("line4: {} (with psi(S{}), implicit cubic twist)".format(a ,line4))
                return False
        i = i+1
    print("test double_line_cln_a0_cubic_twist(Q, P, b_t, Fq3, D_twist={}): {}".format(D_twist, ok))
    return ok

def test_add_line_cln_a0_cubic_twist(E, E2, Fq3, D_twist=False):
    """ Testing add_line_cln_a0_cubic_twist function

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fq where q=p^(k/3) (3-twist)
    - `Fq3`: the degree-3 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist

    idea of the test: a line through S and Q vanishes at S, Q, and -(S+Q)
    test if l_{S,Q}(S) is zero, l_{S,Q}(Q) is zero
    but because of the simplification of the formulas in [CLN],
    it does not vanish at -(S+Q). Testing at S and Q only.

    Third test: with explicit cubic twist
    """
    w = Fq3.gen(0)
    list_a = [1, 2, 3, 11]
    # 1. test with S, Q in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        for a in list_a: # (X/Z, Y/Z) ~ (X,Y,Z) so (X*a,Y*a, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a, a)
            for (T, str_T) in [(S,"S"), (Q,"Q")]: #, (-SQ, "-(S+Q)")]:
                line, R = add_line_cln_a0_cubic_twist(Sa, (Q[0], Q[1]), (T[0], T[1], T[0]**2))
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist(S{}, Q, {})".format(a, str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist(S{}, Q, {})".format(a, str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_cln_a0_cubic_twist(S, Q, P) over Fp: {}".format(ok))
    # 2. test with S, Q in E2/Fq3
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
            psiSQ = psi_sextic_d_twist(SQ, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
            psiSQ = psi_sextic_m_twist(SQ, w)
        psiS = (psiS[0], psiS[1], psiS[0]**2)
        psiQ = (psiQ[0], psiQ[1], psiQ[0]**2)
        #psi_SQ = (psiSQ[0], -psiSQ[1], psiSQ[0]**2)
        for a in list_a:
            Sa = (S[0]*a, S[1]*a, a)
            if D_twist:
                psiSa = psi_sextic_d_twist(Sa, w)
            else:
                psiSa = psi_sextic_m_twist(Sa, w)
            for (psiT, str_psiT) in [(psiS,"psi(S)"), (psiQ,"psi(Q)")]: #, (psi_SQ, "-psi(S+Q)")]:
                line, R = add_line_cln_a0_cubic_twist(psiSa, (psiQ[0], psiQ[1]), psiT)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == psiSQ[0] and R_aff[1] == psiSQ[1]
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist(psi(S{}), psi(Q), {})".format(a, str_psiT))
                    print("psi(S+Q): obtained {}\naffine {}\n expected {}".format(R, R_aff, psiSQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist(psi(S{}), psi(Q), {})".format(a, str_psiT))
                    print("line through psi(S) and psi(Q) evaluated at {} should be 0, obtained\nline = {}".format(str_psiT, line))
                    return False
        i = i+1
    print("test add_line_cln_a0_cubic_twist(S, Q, P): {}".format(ok))
    # 3. with explicit cubic twist inside the line function
    w = Fq3.gen(0)
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
        psiS = (psiS[0], psiS[1], psiS[0]**2)
        psiQ = (psiQ[0], psiQ[1], psiQ[0]**2)
        for a in list_a:
            Sa = (S[0]*a, S[1]*a, a)
            for (psiT, str_psiT) in [(psiS,"psi(S)"), (psiQ,"psi(Q)")]:
                line, R = add_line_cln_a0_cubic_twist(Sa, (Q[0], Q[1]), psiT, Fq3, D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist(S{}, Q, {}, Fq3, D_twist={})".format(a, str_psiT, D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist(S{}, Q, {}, Fq3, D_twist={})".format(a, str_psiT, D_twist))
                    print("line through S, Q evaluated at {} should be 0, obtained\nline = {}".format(str_psiT, line))
                    print("compare to add_line_cln_a0_cubic_twist(psiS, psiQ, {}):".format(str_psiT))
                    if D_twist:
                        psiSa = psi_sextic_d_twist(Sa, w)
                    else:
                        psiSa = psi_sextic_m_twist(Sa, w)
                    line2, R2 = add_line_cln_a0_cubic_twist(psiSa, (psiQ[0], psiQ[1]), psiT)
                    print("one obain line2 = {}".format(line2))
                    for PP, strPP in [((0,0,0), "(0,0,0)"), ((1,0,0), "(1,0,0)"), ((0,1,0), "(0,1,0)"), ((0,0,1), "(0,0,1)")]:
                        print("add_line_cln_a0_cubic_twist(S, Q, {}, Fq3, D_twist={})".format(strPP, D_twist))
                        line3, RR = add_line_cln_a0_cubic_twist(S, (Q[0],Q[1]), PP, Fq3, D_twist)
                        line4, R4 = add_line_cln_a0_cubic_twist((psiS[0], psiS[1], 1), (psiQ[0], psiQ[1]), PP)
                        print("line3: {} (with explicit cubic twist)".format(line3))
                        print("line4: {} (with psi(S), psi(Q), implicit cubic twist)".format(line4))
                        if line4 != 0:
                            print("line3/line4 = {}".format(line3/line4))
                        # with Sa instead of S
                        if a != 1:
                            print("add_line_cln_a0_cubic_twist(S{}, Q, {}, Fq3, D_twist={})".format(a, strPP, D_twist))
                            line3, RR = add_line_cln_a0_cubic_twist(Sa, (Q[0],Q[1]), PP, Fq3, D_twist)
                            line4, R4 = add_line_cln_a0_cubic_twist((psiSa[0], psiSa[1], 1), (psiQ[0], psiQ[1]), PP)
                            print("line3: {} (with explicit cubic twist)".format(line3))
                            print("line4: {} (with psi(S{}), psi(Q), implicit cubic twist)".format(a, line4))
                            if line4 != 0:
                                print("line3/line4 = {}".format(line3/line4))
                    return False
        i = i+1
    print("test add_line_cln_a0_cubic_twist(S, Q, P, Fq3, D_twist={}): {}".format(D_twist, ok))
    return ok

def test_add_line_cln_a0_cubic_twist_with_z(E, E2, Fq3, D_twist=False):
    """ Testing add_line_cln_a0_cubic_twist_with_z function

    INPUT:
    - `E`: elliptic curve over Fp
    - `E2`: elliptic curve over Fq where q=p^(k/3) (3-twist)
    - `Fq3`: the degree-3 extension on top of Fq
    - `D_twist`: flag for D-twist or M-twist

    idea of the test: a line through S and Q vanishes at S, Q, and -(S+Q)
    test if l_{S,Q}(S) is zero, l_{S,Q}(Q) is zero
    but because of the simplification of the formulas in [CLN],
    it does not vanish at -(S+Q). Testing at S and Q only.

    Third test: with explicit cubic twist
    """
    w = Fq3.gen(0)
    list_ab = [(1, 1), (1, 2), (1, 7), (3, 1), (3, 2), (3, 7), (11, 1), (11, 2), (11, 7)]
    # 1. test with S, Q in E/Fp
    ok = True
    i = 0
    while i < 10:
        S = E.random_element()
        Q = E.random_element()
        SQ = S+Q
        for (a,b) in list_ab: # (X/Z, Y/Z^2) ~ (X,Y,Z) so (X*a,Y*a^2, Z*a) ~ (X,Y,Z)
            Sa = (S[0]*a, S[1]*a, a)
            Qb = (Q[0]*b, Q[1]*b, b)
            for (T, str_T) in [(S,"S"), (Q,"Q")]: #, (-SQ, "-(S+Q)")):
                line, R = add_line_cln_a0_cubic_twist_with_z(Sa, Qb, (T[0],T[1],T[0]**2))
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist_with_z(S{}, Q{}, {})".format(a, b, str_T))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist_with_z(S{}, Q{}, {})".format(a, b, str_T))
                    print("line through S and Q evaluated at {} should be 0, obtained\nline = {}".format(str_T, line))
                    return False
        i = i+1
    print("test add_line_cln_a0_cubic_twist_with_z(S, Q, P) over Fp: {}".format(ok))
    # 2. test with S, Q in E2/Fq3
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
            psiSQ = psi_sextic_d_twist(SQ, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
            psiSQ = psi_sextic_m_twist(SQ, w)
        psiS = (psiS[0], psiS[1], psiS[0]**2)
        psiQ = (psiQ[0], psiQ[1], psiQ[0]**2)
        #psi_SQ = (psiSQ[0], -psiSQ[1], psiSQ[0]**2)
        for a,b in list_ab:
            Sa = (S[0]*a, S[1]*a, a)
            Qb = (Q[0]*b, Q[1]*b, b)
            if D_twist:
                psiSa = psi_sextic_d_twist(Sa, w)
                psiQb = psi_sextic_d_twist(Qb, w)
            else:
                psiSa = psi_sextic_m_twist(Sa, w)
                psiQb = psi_sextic_m_twist(Qb, w)
            for (psiT, str_psiT) in [(psiS,"psi(S)"), (psiQ,"psi(Q)")]: #, (psi_SQ, "-psi(S+Q)")]:
                line, R = add_line_cln_a0_cubic_twist_with_z(psiSa, psiQb, psiT)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == psiSQ[0] and R_aff[1] == psiSQ[1]
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist_with_z(psi(S{}), psi(Q{}), {})".format(a, b, str_psiT))
                    print("psi(S+Q): obtained {}\naffine {}\n expected {}".format(R, R_aff, psiSQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist_with_z(psi(S{}), psi(Q{}), {})".format(a, b, str_psiT))
                    print("line through psi(S) and psi(Q) evaluated at {} should be 0, obtained\nline = {}".format(str_psiT, line))
                    return False
        i = i+1
    print("test add_line_cln_a0_cubic_twist_with_z(S, Q, P): {}".format(ok))
    # 3. with explicit cubic twist inside the line function
    w = Fq3.gen(0)
    ok = True
    i = 0
    while i < 10:
        S = E2.random_element()
        Q = E2.random_element()
        SQ = S+Q
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
        psiS = (psiS[0], psiS[1], psiS[0]**2)
        psiQ = (psiQ[0], psiQ[1], psiQ[0]**2)
        for a,b in list_ab:
            Sa = (S[0]*a, S[1]*a, a)
            Qb = (Q[0]*b, Q[1]*b, b)
            for (psiT, str_psiT) in [(psiS,"psi(S)"), (psiQ,"psi(Q)")]:
                line, R = add_line_cln_a0_cubic_twist_with_z(Sa, Qb, psiT, Fq3, D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist_with_z(S{}, Q{}, {}, Fq3, D_twist={})".format(a, b, str_psiT, D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_cln_a0_cubic_twist_with_z(S{}, Q{}, {}, Fq3, D_twist={})".format(a, b, str_psiT, D_twist))
                    print("line through S, Q evaluated at {} should be 0, obtained\nline = {}".format(str_psiT, line))
                    print("compare to add_line_cln_a0_cubic_twist_with_z(psiS, psiQ, {}):".format(str_psiT))
                    if D_twist:
                        psiSa = psi_sextic_d_twist(Sa, w)
                        psiQb = psi_sextic_d_twist(Qb, w)
                    else:
                        psiSa = psi_sextic_m_twist(Sa, w)
                        psiQb = psi_sextic_m_twist(Qb, w)
                    line2, R2 = add_line_cln_a0_cubic_twist_with_z(psiSa, psiQb, psiT)
                    print("one obain line2 = {}".format(line2))
                    for PP, strPP in [((0,0,0), "(0,0,0)"), ((1,0,0), "(1,0,0)"), ((0,1,0), "(0,1,0)"), ((0,0,1), "(0,0,1)")]:
                        print("add_line_cln_a0_cubic_twist_with_z(S, Q, {}, Fq3, D_twist={})".format(strPP, D_twist))
                        line3, RR = add_line_cln_a0_cubic_twist_with_z((S[0], S[1], 1), (Q[0],Q[1], 1), PP, Fq3, D_twist)
                        line4, R4 = add_line_cln_a0_cubic_twist_with_z((psiS[0], psiS[1], 1), (psiQ[0], psiQ[1], 1), PP)
                        print("line3: {} (with explicit cubic twist)".format(line3))
                        print("line4: {} (with psi(S), psi(Q), implicit cubic twist)".format(line4))
                        if line4 != 0:
                            print("line3/line4 = {}".format(line3/line4))
                        # with Sa, Qb instead of S, Q
                        if a != 1 or b != 1:
                            print("add_line_cln_a0_cubic_twist_with_z(S{}, Q{}, {}, Fq3, D_twist={})".format(a, b, strPP, D_twist))
                            line3, RR = add_line_cln_a0_cubic_twist_with_z(Sa, Qb, PP, Fq3, D_twist)
                            line4, R4 = add_line_cln_a0_cubic_twist_with_z(psiSa, psiQb, PP)
                            print("line3: {} (with explicit cubic twist)".format(line3))
                            print("line4: {} (with psi(S{}), psi(Q{}), implicit cubic twist)".format(a, b, line4))
                            if line4 != 0:
                                print("line3/line4 = {}".format(line3/line4))
                    return False
        i = i+1
    print("test add_line_cln_a0_cubic_twist_with_z(S, Q, P, Fq3, D_twist={}): {}".format(D_twist, ok))
    return ok

### AKLGL formulas

def test_double_line_h_a0_twist6_aklgl(E,E2,Fqk,r,c,c2,D_twist=False,verbose=False):
    E0 = E(0)
    E20 = E2(0)
    if verbose:
        print("test double_line_h_a0_twist6_aklgl")
    w = Fqk.gen(0)
    Q1 = c2*E2.random_element()
    while Q1 == E20 or not r*Q1 == E20:
        Q1 = c2*E2.random_element()
    P = c*E.random_element()
    while P == E0 or not r*P == E0:
        P = c*E.random_element()
    Pxy = (P[0],P[1])
    Q2 = 2*Q1
    Q3 = 3*Q1
    Q1xy = (Q1[0],Q1[1])
    ok = True
    sz = [1, 2, 3, 11]
    i=0
    while ok and i < len(sz):
        SZ = sz[i]
        Sxy = (SZ*Q1[0],SZ*Q1[1],SZ) # with Z=1 the first time
        ln, S2 = double_line_h_a0_twist6_aklgl(Sxy,Pxy,E2.a6(),D_twist=D_twist)
        ok0 = S2[0]/S2[2] == Q2[0] and S2[1]/S2[2] == Q2[1]
        lln,SS2,lxy = double_line_aklgl_test(Sxy,Pxy,E2.a6(),Fqk.gen(0),D_twist=D_twist)
        ok1 = SS2[0]/SS2[2] == Q2[0] and SS2[1]/SS2[2] == Q2[1]
        ok2 = Fqk(ln) == lln
        if verbose:
            print("S2 == 2*Q: {}".format(ok0))
            print("SS2== 2*Q: {}".format(ok1))
            print("test lines: {}".format(ok2))
        l0,lx,ly = lxy
        if D_twist:
            okl1 = l0 + lx*Q1[0]*w**2 + ly*Q1[1]*w**3 == 0
            okl2 = l0 + lx*Q2[0]*w**2 - ly*Q2[1]*w**3 == 0
        else:
            okl1 = l0 + lx*Q1[0]/w**2 + ly*Q1[1]/w**3 == 0
            okl2 = l0 + lx*Q2[0]/w**2 - ly*Q2[1]/w**3 == 0
        if verbose:
            print("l(xQ,yQ)   ==0: {}".format(okl1))
            print("l(x2Q,-y2Q)==0: {}".format(okl2))
        ok = ok0 and ok1 and ok2 and okl1 and okl2
        i = i+1
    print("test double_line_h_a0_twist6_aklgl: {}".format(ok))
    return ok

def test_double_line_h_a0_twist6_aklgl_no_div2(E,E2,Fqk,r,c,c2,D_twist=False,verbose=False):
    if verbose:
        print("test double_line_h_a0_twist6_aklgl_no_div2")
    w = Fqk.gen(0)
    Q1 = c2*E2.random_element()
    assert r*Q1 == E2(0)
    P = c*E.random_element()
    Pxy = (P[0],P[1])
    Q2 = 2*Q1
    Q3 = 3*Q1
    Q1xy = (Q1[0],Q1[1])
    ok = True
    sz = [1, 2, 3, 11]
    i=0
    while ok and i < len(sz):
        SZ = sz[i]
        Sxy = (SZ*Q1[0],SZ*Q1[1],SZ) # with Z=1
        ln, S2 = double_line_h_a0_twist6_aklgl_no_div2(Sxy,Pxy,E2.a6(),D_twist=D_twist)
        ok0 = S2[0]/S2[2] == Q2[0] and S2[1]/S2[2] == Q2[1]
        lln,SS2,lxy = double_line_aklgl_test(Sxy,Pxy,E2.a6(),Fqk.gen(0),D_twist=D_twist)
        ok1 = SS2[0]/SS2[2] == Q2[0] and SS2[1]/SS2[2] == Q2[1]
        ok2 = Fqk(ln) == lln
        if verbose:
            print("S2 == 2*Q: {}".format(ok0))
            print("SS2== 2*Q: {}".format(ok1))
            print("test lines: {}".format(ok2))
        l0,lx,ly = lxy
        if D_twist:
            okl1 = l0 + lx*Q1[0]*w**2 + ly*Q1[1]*w**3 == 0
            okl2 = l0 + lx*Q2[0]*w**2 - ly*Q2[1]*w**3 == 0
        else:
            okl1 = l0 + lx*Q1[0]/w**2 + ly*Q1[1]/w**3 == 0
            okl2 = l0 + lx*Q2[0]/w**2 - ly*Q2[1]/w**3 == 0
        if verbose:
            print("l(xQ,yQ)   ==0: {}".format(okl1))
            print("l(x2Q,-y2Q)==0: {}".format(okl2))
        ok = ok0 and ok1 and ok2 and okl1 and okl2
        i = i+1
    print("test double_line_h_a0_twist6_aklgl_no_div2: {}".format(ok))
    return ok

def test_add_line_h_a0_twist6_aklgl_test(E, E2, w, D_twist=False):
    list_a = [1, 2, 3, 11]
    # 1. if S and Q are in G1: line_{S,Q}(S) = line_{S,Q}(Q) = line_{S,Q}(-S-Q) = 0
    S = E.random_element()
    Q = E.random_element()
    SQ = S+Q
    QQ = (Q[0], Q[1])
    for a in list_a:
        SS = (S[0]*a, S[1]*a, a)
        for D_twist in [True, False]: # no notion of twist on E/Fp
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R, line_coeffs = add_line_h_a0_twist6_aklgl_test(SS, QQ, (T[0],T[1]), 1, D_twist=D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl_test(..., D_twist={})".format(D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl_test(..., D_twist={})".format(D_twist))
                    print("line through S, Q at {} should be 0, obtained\nline = {}\n sum = {}".format(str_T, line_coeffs, line))
                    return False
    # 2. if S and Q are in G2
    S = E2.random_element()
    Q = E2.random_element()
    SQ = S+Q
    QQ = (Q[0], Q[1])
    for a in list_a:
        SS = (S[0]*a, S[1]*a, a)
        for D_twist in [True, False]:
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiQ = psi_sextic_d_twist(Q, w)
                psiSQ = psi_sextic_d_twist(SQ, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiQ = psi_sextic_m_twist(Q, w)
                psiSQ = psi_sextic_m_twist(SQ, w)
            psiS = (psiS[0], psiS[1])
            psiQ = (psiQ[0], psiQ[1])
            psi_SQ = (psiSQ[0], -psiSQ[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
                line, R, line_coeffs = add_line_h_a0_twist6_aklgl_test(SS,QQ, psiT, w, D_twist=D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl_test(..., D_twist={})".format(D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = line == 0
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl_test(..., D_twist={}".format(D_twist))
                    print("line through S, Q at {} should be 0, obtained\nline = {}\n sum = {}".format(str_psiT, line_coeffs, line))
                    return False
    print("test add_line_h_a0_twist6_aklgl_test: {}".format(ok))
    return ok

def test_add_line_h_a0_twist6_aklgl(E, E2, w, D_twist=False):
    list_a = [1, 2, 3, 11]
    # 1. if S and Q are in G1: line_{S,Q}(S) = line_{S,Q}(Q) = line_{S,Q}(-S-Q) = 0
    S = E.random_element()
    Q = E.random_element()
    SQ = S+Q
    QQ = (Q[0], Q[1])
    for a in list_a:
        SS = (S[0]*a, S[1]*a, a)
        for D_twist in [True, False]: # no notion of twist on E/Fp
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_h_a0_twist6_aklgl(SS, QQ, (T[0],T[1]), D_twist=D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl(..., D_twist={})".format(D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl(..., D_twist={})".format(D_twist))
                    print("line through S, Q at {} should be 0, obtained\nline = {}\n sum = {}".format(str_T, line, sum(line)))
                    return False
    # 2. if S and Q are in G2
    S = E2.random_element()
    Q = E2.random_element()
    SQ = S+Q
    QQ = (Q[0], Q[1])
    for a in list_a:
        SS = (S[0]*a, S[1]*a, a)
        for D_twist in [True, False]:
            if D_twist:
                psiS = psi_sextic_d_twist(S, w)
                psiQ = psi_sextic_d_twist(Q, w)
                psiSQ = psi_sextic_d_twist(SQ, w)
            else:
                psiS = psi_sextic_m_twist(S, w)
                psiQ = psi_sextic_m_twist(Q, w)
                psiSQ = psi_sextic_m_twist(SQ, w)
            psiS = (psiS[0], psiS[1])
            psiQ = (psiQ[0], psiQ[1])
            psi_SQ = (psiSQ[0], -psiSQ[1])
            for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
                line, R = add_line_h_a0_twist6_aklgl(SS,QQ, psiT, D_twist=D_twist)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl(..., D_twist={})".format(D_twist))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                sum_line = sum([line[i]*w**i for i in range(len(line))])
                ok = sum_line == 0
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl(..., D_twist={}".format(D_twist))
                    print("line through S, Q at {} should be 0, obtained\nline = {}\n sum = {}".format(str_psiT, line, sum_line))
                    return False
    print("test add_line_h_a0_twist6_aklgl: {}".format(ok))

def test_add_line_h_a0_twist6_aklgl_with_z(E, E2, w, D_twist=False):
    list_ab = [(1, 1), (1, 2), (3, 1), (3,2)]
    # 1. if S and Q are in G1: line_{S,Q}(S) = line_{S,Q}(Q) = line_{S,Q}(-S-Q) = 0
    S = E.random_element()
    Q = E.random_element()
    SQ = S+Q
    for a,b in list_ab:
        SS = (S[0]*a, S[1]*a, a)
        QQ = (Q[0]*b, Q[1]*b, b)
        for D_twist_ in [True, False]: # no notion of twist on E/Fp
            for (T, str_T) in ((S,"S"), (Q,"Q"), (-SQ, "-(S+Q)")):
                line, R = add_line_h_a0_twist6_aklgl_with_z(SS, QQ, (T[0],T[1]), D_twist=D_twist_)
                R_aff = (R[0]/R[2], R[1]/R[2])
                ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl_with_z(..., D_twist={})".format(D_twist_))
                    print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                    return False
                ok = sum(line) == 0
                if not ok:
                    print("Error add_line_h_a0_twist6_aklgl_with_z(..., D_twist={})".format(D_twist_))
                    print("line through S, Q at {} should be 0, obtained\nline = {}\n sum = {}".format(str_T, line, sum(line)))
                    return False
    # 2. if S and Q are in G2
    S = E2.random_element()
    Q = E2.random_element()
    SQ = S+Q
    for a,b in list_ab:
        SS = (S[0]*a, S[1]*a, a)
        QQ = (Q[0]*b, Q[1]*b, b)
        if D_twist:
            psiS = psi_sextic_d_twist(S, w)
            psiQ = psi_sextic_d_twist(Q, w)
            psiSQ = psi_sextic_d_twist(SQ, w)
        else:
            psiS = psi_sextic_m_twist(S, w)
            psiQ = psi_sextic_m_twist(Q, w)
            psiSQ = psi_sextic_m_twist(SQ, w)
        psiS = (psiS[0], psiS[1])
        psiQ = (psiQ[0], psiQ[1])
        psi_SQ = (psiSQ[0], -psiSQ[1])
        for (psiT, str_psiT) in ((psiS,"psi(S)"), (psiQ,"psi(Q)"), (psi_SQ, "-psi(S+Q)")):
            line, R = add_line_h_a0_twist6_aklgl_with_z(SS,QQ, psiT, D_twist=D_twist)
            R_aff = (R[0]/R[2], R[1]/R[2])
            ok = R_aff[0] == SQ[0] and R_aff[1] == SQ[1]
            if not ok:
                print("Error add_line_h_a0_twist6_aklgl_with_z(..., D_twist={})".format(D_twist))
                print("S+Q: obtained {}\naffine {}\n expected {}".format(R, R_aff, SQ))
                return False
            sum_line = sum([line[i]*w**i for i in range(len(line))])
            ok = sum_line == 0
            if not ok:
                print("Error add_line_h_a0_twist6_aklgl_with_z(..., D_twist={}".format(D_twist))
                print("line through S, Q at {} should be 0, obtained\nline = {}\n sum = {}".format(str_psiT, line, sum_line))
                return False
    if D_twist:
        print("test add_line_h_a0_twist6_aklgl_with_z, D_twist: {}".format(ok))
    else:
        print("test add_line_h_a0_twist6_aklgl_with_z, M_twist: {}".format(ok))

def test_sparse_mult_m6_twist(Fq6):
    Fq = Fq6.base_ring()
    if Fq.degree() == 1:
        P = Fq6.polynomial()
    else:
        P = Fq6.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 6
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == coeffs[4] == coeffs[5] == 0
    assert coeffs[6] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        f = Fq6.random_element()
        l0 = Fq.random_element()
        l2 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq6([l0,0,l2,l3,0,0])
        expected_res = l*f
        res = sparse_mult_m6_twist(l0,l2,l3, f, xi, Fq6)
        ok = res == expected_res
        i = i+1
    print("test sparse_mult_m6_twist: {}".format(ok))
    return ok

def test_sparse_mult_d6_twist(Fq6):
    Fq = Fq6.base_ring()
    if Fq.degree() == 1:
        P = Fq6.polynomial()
    else:
        P = Fq6.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 6
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == coeffs[4] == coeffs[5] == 0
    assert coeffs[6] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        f = Fq6.random_element()
        l0 = Fq.random_element()
        l1 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq6([l0,l1,0,l3,0,0])
        expected_res = l*f
        res = sparse_mult_d6_twist(l0,l1,l3, f, xi, Fq6)
        ok = res == expected_res
        i = i+1
    print("test sparse_mult_d6_twist: {}".format(ok))
    return ok

def test_sparse_sparse_mult_m6_twist(Fq6):
    Fq = Fq6.base_ring()
    if Fq.degree() == 1:
        P = Fq6.polynomial()
    else:
        P = Fq6.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 6
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == coeffs[4] == coeffs[5] == 0
    assert coeffs[6] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        l0 = Fq.random_element()
        l2 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq6([l0,0,l2,l3,0,0])
        f0 = Fq.random_element()
        f2 = Fq.random_element()
        f3 = Fq.random_element()
        f = Fq6([f0,0,f2,f3,0,0])
        expected_res = l*f
        res = sparse_sparse_mult_m6_twist(l0, l2, l3, f0, f2, f3, xi, Fq6)
        ok = res == expected_res
        i = i+1
    print("test sparse_sparse_mult_m6_twist: {}".format(ok))
    return ok

def test_sparse_sparse_mult_d6_twist(Fq6):
    Fq = Fq6.base_ring()
    if Fq.degree() == 1:
        P = Fq6.polynomial()
    else:
        P = Fq6.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 6
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == coeffs[4] == coeffs[5] == 0
    assert coeffs[6] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        l0 = Fq.random_element()
        l1 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq6([l0,l1,0,l3,0,0])
        f0 = Fq.random_element()
        f1 = Fq.random_element()
        f3 = Fq.random_element()
        f = Fq6([f0,f1,0,f3,0,0])
        expected_res = l*f
        res = sparse_sparse_mult_d6_twist(l0, l1, l3, f0, f1, f3, xi, Fq6)
        ok = res == expected_res
        i = i+1
    print("test sparse_sparse_mult_d6_twist: {}".format(ok))
    return ok

def test_sparse_mult_m4_twist(Fq4):
    Fq = Fq4.base_ring()
    if Fq.degree() == 1:
        P = Fq4.polynomial()
    else:
        P = Fq4.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 4
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == 0
    assert coeffs[4] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        f = Fq4.random_element()
        l0 = Fq.random_element()
        l2 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq4([l0,0,l2,l3])
        expected_res = l*f
        res = sparse_mult_m4_twist(l0, l2, l3, f, xi, Fq4)
        ok = res == expected_res
        i = i+1
    print("test sparse_mult_m4_twist: {}".format(ok))
    return ok

def test_sparse_mult_d4_twist(Fq4):
    Fq = Fq4.base_ring()
    if Fq.degree() == 1:
        P = Fq4.polynomial()
    else:
        P = Fq4.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 4
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == 0
    assert coeffs[4] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        f = Fq4.random_element()
        l0 = Fq.random_element()
        l1 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq4([l0,l1,0,l3])
        expected_res = l*f
        res = sparse_mult_d4_twist(l0, l1, l3, f, xi, Fq4)
        ok = res == expected_res
        i = i+1
    print("test sparse_mult_d4_twist: {}".format(ok))
    return ok

def test_sparse_sparse_mult_m4_twist(Fq4):
    Fq = Fq4.base_ring() # .base_field() is not always defined, especially if Fq4 is composite
    if Fq.degree() == 1:
        P = Fq4.polynomial()
    else:
        P = Fq4.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 4
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == 0
    assert coeffs[4] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        a0 = Fq.random_element()
        a2 = Fq.random_element()
        a3 = Fq.random_element()
        a = Fq4([a0,0,a2,a3])
        l0 = Fq.random_element()
        l2 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq4([l0,0,l2,l3])
        expected_res = l*a
        res = sparse_sparse_mult_m4_twist(l0, l2, l3, a0, a2, a3, xi, Fq4)
        ok = res == expected_res
        i = i+1
    print("test sparse_sparse_mult_m4_twist: {}".format(ok))
    return ok

def test_sparse_sparse_mult_d4_twist(Fq4):
    Fq = Fq4.base_ring()
    if Fq.degree() == 1:
        P = Fq4.polynomial()
    else:
        P = Fq4.modulus()
    xi = -P.constant_coefficient()
    assert P.degree() == 4
    coeffs = P.list()
    assert coeffs[1] == coeffs[2] == coeffs[3] == 0
    assert coeffs[4] == 1
    assert coeffs[0] == -xi
    ok = True
    i = 0
    while ok and i < 10:
        a0 = Fq.random_element()
        a1 = Fq.random_element()
        a3 = Fq.random_element()
        a = Fq4([a0,a1,0,a3])
        l0 = Fq.random_element()
        l1 = Fq.random_element()
        l3 = Fq.random_element()
        l = Fq4([l0,l1,0,l3])
        expected_res = l*a
        res = sparse_sparse_mult_d4_twist(l0, l1, l3, a0, a1, a3, xi, Fq4)
        ok = res == expected_res
        i = i+1
    print("test sparse_sparse_mult_d4_twist: {}".format(ok))
    return ok

def test_bilinearity_miller_loop_ate(E, E_Fqd, E2, r, c, c2, t_1, D_twist=False, function_name=miller_function_ate):
    """
    Testing Miller loop of ate pairing e_{t-1}(Q, P) (or variant)

    Testing the function miller_function_ate(Q2, P, E.a4(), t-1) by default
    Compatible:
    miller_function_ate(Q2, P, a, t-1)
    miller_function_ate_2naf(Q2, P, a, t-1)

    miller_function_ate_csb(Q,P,a,t-1)

    miller_function_ate_cln_b0(Q, P, a, t-1)
    miller_function_ate_2naf_cln_b0(Q, P, a, t-1)

    where Q2 and P are both of order r and in E(Fqd) but in distinct subgroups
    To obtain valid Q2, first Q of order r is sampled from E2(Fq) then
    a map (D-twist or M-twist) is applied to Q to obtain Q2 in E_Fqd.
    Works with 6-twists (Fqd = Fq6)

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fqd`: elliptic curve over GF(q^d) where q = p^{k/d}
    - `E2`: d-twist over GF(q) where q = p^{k/d} of order r*c2
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `t_1`: the trace minus 1, usually t-1 = u0 the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0):
        Q = c2 * E2.random_element()
    Fqd = E_Fqd.base_field() # assume that the degree d extension is explicit
    w = Fqd.gen(0)
    exponent = (Fqd.cardinality()-1) // r # (q^d-1)//r = (p^k-1)//r
    if not D_twist:
        Q2 = psi_sextic_m_twist(Q, w)
    else:
        Q2 = psi_sextic_d_twist(Q, w)
    f, t_1Q = function_name(Q2, P, E.a4(), t_1)
    g = f**exponent
    ok = True
    aa = 1
    while ok and aa < 4:
        Pa = aa*P
        bb = 1
        while ok and bb < 4:
            Qb = bb*Q
            if not D_twist:
                Q2b = psi_sextic_m_twist(Qb, w)
            else:
                Q2b = psi_sextic_d_twist(Qb, w)
            fab, abQ = function_name(Q2b, Pa, E.a4(), t_1)
            gab = fab**exponent
            ok = ok and gab == g**(aa*bb)
            bb += 1
        aa += 1
    print("test bilinearity {}: {}".format(function_name.__name__, ok))
    return ok

def test_miller_function_ate(E, E_Fqd, E2, r, c, c2, t_1, D_twist=False):
    return test_bilinearity_miller_loop_ate(E, E_Fqd, E2, r, c, c2, t_1, D_twist=D_twist, function_name=miller_function_ate)

def test_miller_function_ate_csb(E, E_Fqd, E2, r, c, c2, t_1, D_twist=False):
    return test_bilinearity_miller_loop_ate(E, E_Fqd, E2, r, c, c2, t_1, D_twist=D_twist, function_name=miller_function_ate_csb)

def test_miller_function_ate_cln_b0(E, E_Fq4, E2, r, c, c2, t_1, D_twist=False):
    return test_bilinearity_miller_loop_ate(E, E_Fq4, E2, r, c, c2, t_1, D_twist=D_twist, function_name=miller_function_ate_cln_b0)

def test_miller_function_ate_2naf_cln_b0(E, E_Fq4, E2, r, c, c2, t_1, D_twist=False):
    return test_bilinearity_miller_loop_ate(E, E_Fq4, E2, r, c, c2, t_1, D_twist=D_twist, function_name=miller_function_ate_2naf_cln_b0)

def test_miller_function_ate_2naf(E, E_Fq6, E2, r, c, c2, t_1, D_twist=False):
    """Testing Miller function of ate pairing e_{t-1}(Q, P), t-1 in 2-naf

    Testing the function miller_function_ate_2naf(Q2, P, E.a4(), t-1)
    equivalent to miller_function_ate() but with t_1 in 2naf
    where Q2 and P are both of order r and in E(Fq6) but in distinct subgroups
    To obtain valid Q2, first Q of order r is sampled from E2(Fq) then
    a map (D-twist or M-twist) is applied to Q to obtain Q2 in E_Fq6.

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fq6`: elliptic curve over GF(q^6) where q = p^{k/6}
    - `E2`: sextic twist over GF(q) where q = p^{k/6} of order r*c2
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/6}
    - `t_1`: the trace minus 1, usually t-1 = u0 the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    return test_bilinearity_miller_loop_ate(E, E_Fq6, E2, r, c, c2, t_1, D_twist=D_twist, function_name=miller_function_ate_2naf)

def test_bilinearity_miller_loop_ate_absolute_extension(E, E2, Fqd, Fpk, map_Fqd_Fpk, r, c, c2, t_1, D_twist=False, function_name=miller_function_ate, curve_a_is_0=False):
    """Testing Miller loop, Fpk absolute extension (a.frobenius() allowed)

    Can test the function miller_loop_opt_ate_kss16(Q2, P, E.a4(), u)
    where Q2 and P are both of order r and in E(Fpk) but in distinct subgroups
    To obtain valid Q2, first Q of order r is sampled from E2(Fq) then
    a map (D-twist or M-twist) is applied to Q to obtain Q2 in E_Fqd, then finally in E_Fpk.

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fpk`: elliptic curve over GF(p^k) absolute extension
    - `E2`: d-twist over GF(q) where q = p^{k/d} of order r*c2, d=4,6
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `t_1`: the length of the loop (e.g. trace-1 for ate, seed u for optimal ate)
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)
    - `curve_a_is_0`: whether the short Weierstrass equation of the curve has a=0

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0):
        Q = c2 * E2.random_element()
    #Fqd = E_Fqd.base_field() # assume that the degree d extension is explicit
    w = Fqd.gen(0)
    exponent = (Fqd.cardinality()-1) // r # (q^d-1)//r = (p^k-1)//r
    if not D_twist:
        Q2 = psi_sextic_m_twist(Q, w)
    else:
        Q2 = psi_sextic_d_twist(Q, w)
    Q2 = (map_Fqd_Fpk(Q2[0]), map_Fqd_Fpk(Q2[1]))
    if curve_a_is_0:
        f = function_name(Q2, P, t_1)
    else:
        f = function_name(Q2, P, E.a4(), t_1)
    g = f**exponent
    ok = True
    aa = 1
    while ok and aa < 4:
        Pa = aa*P
        bb = 1
        while ok and bb < 4:
            Qb = bb*Q
            if not D_twist:
                Q2b = psi_sextic_m_twist(Qb, w)
            else:
                Q2b = psi_sextic_d_twist(Qb, w)
            Q2b = (map_Fqd_Fpk(Q2b[0]), map_Fqd_Fpk(Q2b[1]))
            if curve_a_is_0:
                fab = function_name(Q2b, Pa, t_1)
            else:
                fab = function_name(Q2b, Pa, E.a4(), t_1)
            gab = fab**exponent
            ok = ok and gab == g**(aa*bb)
            bb += 1
        aa += 1
    print("test bilinearity {}: {}".format(function_name.__name__, ok))
    return ok

def test_miller_function_ate_cln_b0_quartic_twist(function_name, E, E2, Fq4, r, c, c2, t_1, D_twist=False,verbose=False):
    """
    Testing Miller function of ate pairing e_{t-1}(Q, P) with Costello Lange Naehrig formulas

    Testing the functions
    miller_function_ate_cln_b0_quartic_twist(Q, P, E2.a4(), t-1, xi, D_twist, m0=1)
    miller_function_ate_cln_b0_quartic_twist_acc_line(Q, P, E2.a4(), t-1, xi, D_twist, m0=1)
    where Q and P are of order r, P in E(Fp), Q in E2(Fq) and q = p^{k/d}.
    The map from Q in E2(Fq) to Q2 in E(Fq^4) is done inside the tested function

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E2`: quartic twist over GF(q) where q = p^{k/4} of order r*c2
    - `Fq4`: field extension with an explicit degree 4 top extension
    - `xi`: element of Fq, Fq4 = Fq[x](x^4-xi)
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/4}
    - `t_1`: the trace minus 1, usually t-1 = u0 the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    assert ((Fq4.cardinality()-1) % r) == 0
    exponent = (Fq4.cardinality()-1) // r
    m, S = function_name(Q, P, E2.a4(), t_1, Fq4, D_twist=D_twist)
    S = [S[0]/S[2], S[1]/S[2]**2]
    t_1Q = t_1*Q
    if verbose:
        if S[0] == t_1Q[0] and S[1] == t_1Q[1]:
            print("S == t_1*Q: {}".format(True))
        elif S[0] == t_1Q[0] and S[1] ==-t_1Q[1]:
            print("S ==-t_1*Q: {}".format(True))
        else:
            print("S == t_1*Q: False, S ==-t_1*Q: False")
    g = m**exponent
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P
            mab, abQ = function_name(Qb, Pa, E2.a4(), t_1, Fq4, D_twist=D_twist)
            gab = mab**exponent
            gab_expected = g**(aa*bb)
            ok = gab == gab_expected
            S = [abQ[0]/abQ[2], abQ[1]/abQ[2]**2]
            t_1Qb = t_1*Qb
            if verbose:
                if S[0] == t_1Qb[0] and S[1] == t_1Qb[1]:
                    print("S == t_1*Qb: {}".format(True))
                elif S[0] == t_1Qb[0] and S[1] ==-t_1Qb[1]:
                    print("S ==-t_1*Qb: {}".format(True))
                else:
                    print("S == t_1*Qb: False, S ==-t_1*Qb: False")
                print("aa={} bb={} gab == gab_expected: {}".format(aa, bb, ok))
                if not ok:
                    print("gab     ={}\nexpected={}".format(gab, gab_expected))
                    print("gab = 1/g^ab: {}".format(gab_expected == 1/gab))
            aa += 1
        bb += 1
    print("{} (bilinear): {} ({} tests)".format(function_name.__name__,ok, (aa-1)*(bb-1)))
    return ok

def test_bilinearity_miller_loop_ate_cln_a0_cubic_twist(E, E_Fq3, E2, r, c, c2, t_1, D_twist=False, function_name=miller_function_ate_cln_a0_cubic_twist, Tate=False):
    """
    Testing Miller loop of ate pairing e_{t-1}(Q, P) (or variant)

    Testing the miller_function_ate_cln_a0_cubic_twist(Q2, P, E.a6(), t-1) by default
    Compatible:
    miller_function_ate_cln_a0_cubic_twist(Q, P, b, t-1)
    miller_function_ate_2naf_cln_a0_cubic_twist(Q, P, b, t-1)

    miller_function_tate_cln_a0_cubic_twist(P, Q, b, r)

    where Q2 and P are both of order r and in E(Fq3) but in distinct subgroups
    To obtain valid Q2, first Q of order r is sampled from E2(Fq) then
    a map (D-twist or M-twist) is applied to Q to obtain Q2 in E_Fq3.
    Works with 3-twists (Fqd = Fq3)

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fq3`: elliptic curve over GF(q^d) where q = p^{k/d}
    - `E2`: d-twist over GF(q) where q = p^{k/d} of order r*c2
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `t_1`: the trace minus 1, usually t-1 = u0 the seed of parameters (or r if Tate)
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)
    - `Tate`: check Tate pairing

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0):
        Q = c2 * E2.random_element()
    Fq3 = E_Fq3.base_field() # assume that the degree d extension is explicit
    w = Fq3.gen(0)
    exponent = (Fq3.cardinality()-1) // r # (q^d-1)//r = (p^k-1)//r
    if not D_twist:
        Q2 = psi_sextic_m_twist(Q, w)
    else:
        Q2 = psi_sextic_d_twist(Q, w)
    Q2 = E_Fq3(Q2)
    if Tate:
        f, t_1Q = function_name(P, Q2, E.a6(), t_1)
    else:
        f, t_1Q = function_name(Q2, P, E_Fq3.a6(), t_1)
    g = f**exponent
    ok = g != 0
    aa = 1
    while ok and aa < 4:
        Pa = aa*P
        bb = 1
        while ok and bb < 4:
            Qb = bb*Q
            if not D_twist:
                Q2b = psi_sextic_m_twist(Qb, w)
            else:
                Q2b = psi_sextic_d_twist(Qb, w)
            Q2b = E_Fq3(Q2b)
            if Tate:
                fab, abQ = function_name(Pa, Q2b, E.a6(), t_1)
            else:
                fab, abQ = function_name(Q2b, Pa, E_Fq3.a6(), t_1)
            gab = fab**exponent
            ok = gab != 0 and gab == g**(aa*bb)
            bb += 1
        aa += 1
    print("test bilinearity {}: {}".format(function_name.__name__, ok))
    return ok

def test_bilinearity_miller_loop_ate_cln_a0_cubic_twist_explicit(E, E_Fq3, E2, r, c, c2, t_1, D_twist=False, function_name=miller_function_ate_cln_a0_cubic_twist, Tate=False, opt=False):
    """
    Testing Miller loop of ate pairing e_{t-1}(Q, P) (or variant)

    Testing the miller_function_ate_cln_a0_cubic_twist(Q2, P, E2.a6(), t-1, Fq3, D_twist) by default
    Compatible:
    miller_function_ate_cln_a0_cubic_twist(Q, P, b_t, t-1, Fq3, D_twist)

    where Q and P are both of order r, P in E(Fq3), Q in E'(Fq) a cubic twist
    Works with 3-twists (Fqd = Fq3)

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fq3`: elliptic curve over GF(q^d) where q = p^{k/d}
    - `E2`: d-twist over GF(q) where q = p^{k/d} of order r*c2
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `t_1`: the trace minus 1, usually t-1 = u0 the seed of parameters (or r if Tate)
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)
    - `function_name`
    - `Tate`: check Tate pairing

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0):
        Q = c2 * E2.random_element()
    Fq3 = E_Fq3.base_field() # assume that the degree d extension is explicit
    w = Fq3.gen(0)
    exponent = (Fq3.cardinality()-1) // r # (q^d-1)//r = (p^k-1)//r
    if Tate:
        f, t_1Q = function_name(P, Q, E.a6(), t_1, 1, Fq3, D_twist)
    elif opt:
        f, t_1Q = function_name(Q, P, E2.a6(), t_1, Fq3, D_twist)
    else:
        f, t_1Q = function_name(Q, P, E2.a6(), t_1, 1, Fq3, D_twist)
    g = f**exponent
    ok = g != 0
    aa = 1
    while ok and aa < 4:
        Pa = aa*P
        bb = 1
        while ok and bb < 4:
            Qb = bb*Q
            if Tate:
                fab, abQ = function_name(Pa, Qb, E.a6(), t_1, 1, Fq3, D_twist)
            elif opt:
                fab, abQ = function_name(Qb, Pa, E2.a6(), t_1, Fq3, D_twist)
            else:
                fab, abQ = function_name(Qb, Pa, E2.a6(), t_1, 1, Fq3, D_twist)
            gab = fab**exponent
            ok = gab != 0 and gab == g**(aa*bb)
            bb += 1
        aa += 1
    print("test bilinearity {}: {}".format(function_name.__name__, ok))
    return ok

def test_miller_function_ate_aklgl(E, E2, Fq6, xi, r, c, c2, t_1, D_twist=False, verbose=False):
    """
    Testing Miller function of ate pairing e_{t-1}(Q, P) with AKLGL formulas

    Testing the function miller_function_ate_aklgl(Q, P, E2.a6(), t-1, Fq6, D_twist, m0=1, xi=None)
    where Q and P are of order r, P in E(Fp), Q in E2(Fq) and q = p^{k/d}.
    The map from Q in E2(Fq) to Q2 in E(Fq^6) is done inside the tested function
    miller_function_ate_aklgl().

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E2`: sextic twist over GF(q) where q = p^{k/6} of order r*c2
    - `Fq6`: field extension with an explicit degree 6 top extension
    - `xi`: element of Fq, Fq6 = Fq[x](x^6-xi)
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/6}
    - `t_1`: the trace minus 1, usually t-1 = u0 the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    #Fq6 = E_Fq6.base_field() # assume that the degree 6 extension is explicit
    w = Fq6.gen(0)
    assert w**6 == xi
    assert ((Fq6.cardinality()-1) % r) == 0
    exponent = (Fq6.cardinality()-1) // r
    m, S = miller_function_ate_aklgl(Q, P, E2.a6(), t_1, Fq6, D_twist=D_twist)
    S = [S[0]/S[2], S[1]/S[2]]
    t_1Q = t_1*Q
    if verbose:
        print("S == t_1*Q: {}".format(S[0] == t_1Q[0] and S[1] == t_1Q[1]))
        print("S ==-t_1*Q: {}".format(S[0] == t_1Q[0] and S[1] ==-t_1Q[1]))
    g = m**exponent
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P
            mab, abQ = miller_function_ate_aklgl(Qb, Pa, E2.a6(), t_1, Fq6, D_twist=D_twist)
            gab = mab**exponent
            gab_expected = g**(aa*bb)
            ok = gab == gab_expected
            S = [abQ[0]/abQ[2], abQ[1]/abQ[2]]
            t_1Qb = t_1*Qb
            if verbose:
                print("S == t_1*Qb: {}".format(S[0] == t_1Qb[0] and S[1] == t_1Qb[1]))
                print("S ==-t_1*Qb: {}".format(S[0] == t_1Qb[0] and S[1] ==-t_1Qb[1]))
                print("aa={} bb={} gab == gab_expected: {}".format(aa, bb, ok))
                if not ok:
                    print("gab     ={}\nexpected={}".format(gab, gab_expected))
                    print("gab = 1/g^ab: {}".format(gab_expected == 1/gab))
            aa += 1
        bb += 1
    print("test_miller_function_ate_aklgl (bilinear): {} ({} tests)".format(ok, (aa-1)*(bb-1)))
    return ok

def test_miller_function_ate_2naf_aklgl(E, E2, Fq6, xi, r, c, c2, t_1, D_twist=False, verbose=False):
    """
    Testing Miller function of ate pairing e_{t-1}(Q, P) with AKLGL formulas and 2-naf t-1

    Testing the function miller_function_ate_2naf_aklgl(Q, P, E2.a6(), t-1, Fq6, D_twist, m0=1, xi=None)
    where Q and P are of order r, P in E(Fp), Q in E2(Fq) and q = p^{k/d}.
    The map from Q in E2(Fq) to Q2 in E(Fq^6) is done inside the tested function
    miller_function_ate_2naf_aklgl().

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E2`: sextic twist over GF(q) where q = p^{k/6} of order r*c2
    - `Fq6`: field extension with an explicit degree 6 top extension
    - `xi`: element of Fq, Fq6 = Fq[x](x^6-xi)
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/6}
    - `t_1`: the trace minus 1, usually t-1 = u0 the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    #Fq6 = E_Fq6.base_field() # assume that the degree 6 extension is explicit
    w = Fq6.gen(0)
    assert w**6 == xi
    exponent = (Fq6.cardinality()-1) // r
    m, S = miller_function_ate_2naf_aklgl(Q, P, E2.a6(), t_1, Fq6, D_twist=D_twist)
    S = [S[0]/S[2], S[1]/S[2]]
    t_1Q = t_1*Q
    if verbose:
        print("S == t_1*Q: {}".format(S[0] == t_1Q[0] and S[1] == t_1Q[1]))
    g = m**exponent
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P
            mab, abQ = miller_function_ate_2naf_aklgl(Qb, Pa, E2.a6(), t_1, Fq6, D_twist=D_twist)
            gab = mab**exponent
            gab_expected = g**(aa*bb)
            ok = gab == gab_expected
            S = [abQ[0]/abQ[2], abQ[1]/abQ[2]]
            t_1Qb = t_1*Qb
            if verbose:
                print("S == t_1*Qb: {}".format(S[0] == t_1Qb[0] and S[1] == t_1Qb[1]))
                print("aa={} bb={} gab == gab_expected: {}".format(aa, bb, ok))
                if not ok:
                    print("gab     ={}\nexpected={}".format(gab, gab_expected))
                    print("gab = 1/g^ab: {}".format(gab_expected == 1/gab))
            aa += 1
        bb += 1
    print("test_miller_function_ate_2naf_aklgl (bilinear): {} ({} tests)".format(ok, (aa-1)*(bb-1)))
    return ok

def test_miller_loop_opt_ate_aklgl(miller_loop_opt_ate_aklgl, E, E2, Fq6, xi, map_Fq6_Fpk, r, c, c2, u, D_twist=False, verbose=False):
    """
    Testing optimal ate Miller loop e_{something}(Q, P) * (other terms) with AKLGL formulas

    For example
    miller_loop_opt_ate_aklgl_kss18(Q, P, E2.a6(), u, Fq6, map_Fq6_Fpk, D_twist)
    TODO:
    miller_loop_opt_ate_aklgl_kss16(Q, P, E2.a4(), u, Fq4, map_Fq4_Fpk, D_twist)
    miller_loop_opt_ate_aklgl_bw6_bls12_trace_0_mod_r_mod_u(Q, P, E2.a6(), u, Fq6, D_twist)
    miller_loop_opt_ate_aklgl_bw6_bls12_trace_3_mod_r_mod_u(Q, P, E2.a6(), u, Fq6, D_twist)
    miller_loop_opt_ate_aklgl_bw6_bls24_trace_0_mod_r_mod_u(Q, P, E2.a6(), u, Fq6, D_twist)
    miller_loop_opt_ate_aklgl_bw6_bls24_trace_3_mod_r_mod_u(Q, P, E2.a6(), u, Fq6, D_twist)

    where Q and P are of order r, P in E(Fp), Q in E2(Fq) and q = p^{k/d}.

    INPUT:
    - `function_opt_ate_aklgl`: a function
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E2`: sextic twist over GF(q) where q = p^{k/6} of order r*c2
    - `Fq6`: field extension with an explicit degree 6 top extension
    - `xi`: element of Fq, Fq6 = Fq[x](x^6-xi)
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/6}
    - `u`: the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    #Fq6 = E_Fq6.base_field() # assume that the degree 6 extension is explicit
    w = Fq6.gen(0)
    assert w**6 == xi
    exponent = (Fq6.cardinality()-1) // r
    m = miller_loop_opt_ate_aklgl(Q, P, E2.a6(), u, Fq6, map_Fq6_Fpk, D_twist=D_twist, xi=xi, check=True)
    g = m**exponent
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P
            mab = miller_loop_opt_ate_aklgl(Qb, Pa, E2.a6(), u, Fq6, map_Fq6_Fpk, D_twist=D_twist, xi=xi, check=True)
            gab = mab**exponent
            gab_expected = g**(aa*bb)
            ok = gab == gab_expected
            if verbose:
                print("aa={} bb={} gab == gab_expected: {}".format(aa, bb, ok))
                if not ok:
                    print("gab     ={}\nexpected={}".format(gab, gab_expected))
                    print("gab = 1/g^ab: {}".format(gab_expected == 1/gab))
            aa += 1
        bb += 1
    print("test {} (bilinear): {} ({} tests)".format(miller_loop_opt_ate_aklgl.__name__, ok, (aa-1)*(bb-1)))
    return ok

def test_miller_loop_opt_tate_aklgl(function_name, E, E2, Fqd, map_Fqd_Fpk, r, c, c2, u, xi, D_twist=False, verbose=False):
    """
    Testing optimal twisted ate (Tate) Miller loop with explicit twist (Q has compressed form in G2)

    For example
    miller_loop_opt_tate_bn_aklgl_a0

    where P and Q are of order r, P in E(Fp) (G1), Q in E2(Fq) (G2) and q = p^{k/d}.

    INPUT:
    - `function_name`: a function taking args (P, Q, curve_coeff, u, Fqd, map_Fqd_Fpk, D_twist)
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E2`: d-twist over GF(q) where q = p^{k/d} of order r*c2
    - `Fqd`: field extension with an explicit degree d top extension
    - `xi`: element of Fq, Fqd = Fq[x](x^d-xi)
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `u`: the seed of parameters
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    if verbose:
        print("arguments:")
        print("function_name = {}".format(function_name.__name__))
        print("E = {}\nE2 = {}\nFqd = {}".format(E, E2, Fqd))
        print("map_Fqd_Fpk = {}".format(map_Fqd_Fpk.__name__))
        print("r = {}\nc = {}\nc2 = {}\nu = {}\nxi = {}\nD_twist = {}".format(r, c, c2, u, xi, D_twist))
    if c == 1: # BN curves
        P = E.random_element()
        while P == E(0) or r*P != E(0):
            P = E.random_element()
    else:
        P = c*E.random_element()
        while P == E(0) or r*P != E(0):
            P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    #Fqd = E_Fqd.base_field() # assume that the degree d extension is explicit
    w = Fqd.gen(0)
    d = Fqd.degree()
    assert w**d == xi
    exponent = (Fqd.cardinality()-1) // r
    if d == 3 or d == 6:
        Eab = E.a6()
    else:
        Eab = E.a4()
    m = function_name(P, Q, Eab, u, Fqd, map_Fqd_Fpk, D_twist=D_twist)
    g = m**exponent
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P
            mab = function_name(Pa, Qb, Eab, u, Fqd, map_Fqd_Fpk, D_twist=D_twist)
            gab = mab**exponent
            gab_expected = g**(aa*bb)
            ok = gab == gab_expected
            if verbose:
                print("aa={} bb={} gab == gab_expected: {}".format(aa, bb, ok))
                if not ok:
                    print("gab     ={}\nexpected={}".format(gab, gab_expected))
                    print("gab = 1/g^ab: {}".format(gab_expected == 1/gab))
            aa += 1
        bb += 1
    print("test {} (bilinear): {} ({} tests)".format(function_name.__name__, ok, (aa-1)*(bb-1)))
    return ok

def test_order(E, order):
    """Test with 10 random points that the curve order corresponds

    INPUT:
    - `E`: elliptic curve (EllipticCurve class instance)
    - `order`: Integer

    RETURNS: True/False
    """
    ok = True
    i = 0
    while ok and i < 10:
        P = E.random_element()
        ok = order*P == E(0)
        i += 1
    print("test order of elliptic curve: {}".format(ok))
    return ok

def test_order_twist(E2, r, c2, D_twist=False):
    """Test with 5 random points that the curve order corresponds

    INPUT:
    - `E2`: elliptic curve (EllipticCurve class instance) over Fq absolute extension
    - `r`: prime integer
    - `c2`: cofactor, so that order (E2) == r*c2
    - `D_twist`: if E2 is a D-twist or M-twist, only for verbose printing

    RETURNS: True/False
    """
    i = 0
    ok = True
    order = c2*r
    while ok and i < 5:
        P = E2.random_element()
        ok = order*P == E2(0)
        i = i+1
    if not D_twist:
        print("test order EM: {}".format(ok))
    else:
        print("test order ED: {}".format(ok))
    return ok

def rene_schoof_criterion(c, ci, q, t, verbose=False):
    """
    Rene Schoof criterion: when is the l-torsion Fq-rational?
    if l^2 | c and l | (q-1) and (t**2-4*q) is a square mod l, then the l-torsion is Fq-rational, potentially the l^v-torsion
    the problem arises for BLS12-377 where 2^46 | p-1, 2^92 | c
    INPUT:
    - `c`: curve cofactor
    - `ci`: a divisor of c, one asks if there are points of order ci on E
    - `q`: base field characteristic
    - `t`: curve trace

    RETURN: if there are points of order ci on the curve, and the divisor to apply to c for that (c//prod_li instead of c//ci)

    the problematic li are those which divide c and q-1, for the rest, this is fine.
    So first, prod_li = ci//gcd(ci, q-1)
    """
    gcd_q = gcd(ci, q-1)
    prod_li = ci//gcd_q
    gcd_qi = gcd_q
    while gcd_qi > 1: # remove completely the factor li^vi of prod_li if li | q-1
        gcd_qi = gcd(prod_li, gcd_qi)
        prod_li = prod_li // gcd_qi
    for l in prime_factors(gcd_q): # only these l will be special
        # what if there is no point of order l^vi as there is some l^vi | ci, l^j|q-1...
        vi = ci.valuation(l)   # l^vi | ci -> c//l^vi or c//l^(vi+something)?
        v0 = c.valuation(l)
        v = min(v0//2, (q-1).valuation(l))
        is_square = (GF(l)(t**2-4*q)).is_square()
        if v > 0 and is_square and (v0-v) < vi:
            # there is rational l^v-torsion: points of order l^vi do not exist,
            # at most their order is c.valuation(l)-v -> if v0-v < vi, skip
            # there is no point of order ci on the curve
            return False, 0
        elif v > 0 and is_square:
            # I want a point of order l^vi*r where vi=ci.valuation(l), l^v0 | ci, and there is rational l^v-torsion
            prod_li *= l**(v+vi)  # v0-v >= vi <=> v0 >= v+vi, and v0 = c.valuation(l), ok
            if verbose:
                print("    l = {0}, val_{0}(c) = {1}, val_{0}(p-1)={2}, v = {3}".format(l, v0, (q-1).valuation(l), v))
        else:
            prod_li *= l**vi
    return True, prod_li

def get_point_exact_order(E, r, ci, c3):
    """
    Get a random point on E of exact order ci*r
    INPUT:
    - `E`: elliptic curve for G1 or G2
    - `r`: prime order of G1 and G2
    - `ci`: divisor of the cofactor c= #E / r
    - `c3`: rene_schoof_criterion output
    """
    Q_ok = False
    while not Q_ok:
        Q = E(0); rQ = E(0)
        while Q.is_zero() or rQ.is_zero():
            Q = c3 * E.random_element() # so that Q has expected order ci*r
            rQ = r*Q
        # check if Q has exactly order ci*r
        Q_ok = True
        if ci.nbits() <= 100: # check for each prime factor l of ci that r*ci/l*Q is not zero
            for l in prime_factors(ci):
                if ((ci//l)*rQ).is_zero():
                    Q_ok = False
                    continue
        else:
            for l in [li for li in primes(2**24) if (ci % li) == 0]:
                if ((ci//l)*rQ).is_zero():
                    Q_ok = False
                    continue
    return Q

def test_membership_testing_g1(E, r, c, u, t, omega, membership_testing_g1_name, verbose=True):
    """
    Testing membership_testing_g1_***()
    INPUT:
    - `E`: elliptic curve defined over GF(p)
    - `r`: (prime) order of G1
    - `c`: cofactor of G1, so that c*r = order(E)
    - `u`: curve seed
    - `t`: trace of E (for Schoof's criterion)
    - `omega`: primitive root in Fp for the endomorphism phi on E, could be None
    - `membership_testing_g1_name`: function name
    """
    # 1. check that input points P in G1 pass the function
    if c == 1:
        return True
    i = 0
    ok1 = True
    while i < 10 and ok1:
        P = E(0)
        while P.is_zero():
            P = c * E.random_element()
        ok1 = membership_testing_g1_name(P, u, omega)
        i = i+1
    print(" - test {} points in G1 pass: {}".format(membership_testing_g1_name.__name__, ok1))
    # 2. check that input points P not in G1 do not pass the test, for P of order ci*r with small integer ci
    q = E.base_field().order()
    if c.nbits() <= 100:
        iter_l = [ci for ci in divisors(c) if ci != 1]
    else:
        iter_l = [l**(j+1) for l in primes(2**24) for j in range(c.valuation(l)) if (c % l) == 0]
    if c not in iter_l: # e.g. if the curve is G1-subgroup secure
        iter_l.append(c)
    tested_l = "" # for printing: test possible (not skipped because of rational torsion)
    wrong_l = "" # test false for points of order l*r
    good_l = "" # test ok for points of order l*r
    bad_l = "" # points of that order do not exist because of rational l-torsion
    ok2 = True
    for ci in iter_l:
        if ci.nbits() <= 100:
            str_ci = "{}={}".format(ci, ci.factor())
        else:
            str_ci = str(ci)
        if verbose:
            print("    ci = {}".format(str_ci))
        ci_ok, prod_li = rene_schoof_criterion(c, ci, q, t, verbose)
        if not ci_ok:
            bad_l += " {},".format(str_ci)
            continue
        tested_l += " {},".format(str_ci)
        c3 = c//prod_li
        i = 0
        ok3 = True
        while i < 10 and ok3:
            P = get_point_exact_order(E, r, ci, c3)
            ok3 = not membership_testing_g1_name(P, u, omega)
            i = i+1
        if not ok3:
            wrong_l += " {},".format(str_ci)
            ok2 = False
        else:
            good_l += " {},".format(str_ci)
    if len(tested_l) > 0:
        print(" - test {} points not in G1, of order ci*r do not pass: {} for ci in [{}]".format(membership_testing_g1_name.__name__, ok2, tested_l))
        if not ok2:
            print("     wrong for points of order ci*r, ci in [{}]".format(wrong_l))
            print("     correct for points of order ci*r, ci in [{}]".format(good_l))
    if len(bad_l) > 20:
        print("    points of order ci*r do not exist, ci in list of {}".format(len(bad_l)))
    elif len(bad_l) > 0:
        print("    points of order ci*r do not exist, ci in [{}]".format(bad_l))
    print("test {}: {} {}".format(membership_testing_g1_name.__name__, ok1, ok2))
    return ok1 and ok2

def test_cofactor_clearing_g1(E, r, c, u, t, omega, cofactor_clearing_g1_name, verbose=True):
    """
    Testing cofactor_clearing_g1_***()
    INPUT:
    - `E`: elliptic curve defined over GF(p)
    - `r`: (prime) order of G1
    - `c`: cofactor of G1, so that c*r = order(E)
    - `u`: curve seed
    - `t`: trace of E (for Schoof's criterion)
    - `omega`: primitive root in Fp for the endomorphism phi on E (can be None)
    - `cofactor_clearing_g1_name`: function name
    """
    if c == 1:
        return True
    E0 = E(0)
    ok = True
    i = 0
    while i < 10 and ok:
        P = E0; rP = E0; cP = E0
        while P.is_zero() or rP.is_zero() or cP.is_zero():
            P = E.random_element()
            rP = r*P
            cP = c*P
        assert (c*rP).is_zero()
        if omega is None:
            cP = cofactor_clearing_g1_name(P, u)
            crP = cofactor_clearing_g1_name(rP, u)
        else:
            cP = cofactor_clearing_g1_name(P, u, omega)
            crP = cofactor_clearing_g1_name(rP, u, omega)
        ok = (not cP.is_zero()) and (r*cP).is_zero() and crP.is_zero()
        i = i+1
    print(" - test {} with random points: {}".format(cofactor_clearing_g1_name.__name__, ok))
    if not ok:
        return False
    # now refine the test: with points of order ci*r where ci is a small factor of c
    q = E.base_field().order()
    if c.nbits() <= 100 and not c.is_prime():
        iter_l = [ci for ci in divisors(c) if ci != 1 and ci != c]
    else:
        iter_l = [l**(j+1) for l in primes(2**24) for j in range(c.valuation(l)) if (c % l) == 0]
    # if iter_l is empty, there is no other test to make (c is prime or a large integer that cannot be factored)
    tested_l = "" # for printing: test possible (not skipped because of rational torsion)
    wrong_l = "" # test false for points of order l*r
    good_l = "" # test ok for points of order l*r
    bad_l = "" # points of that order do not exist because of rational l-torsion
    ok2 = True
    for ci in iter_l:
        if ci.nbits() <= 100:
            str_ci = "{}={}".format(ci, ci.factor())
        else:
            str_ci = str(ci)
        if verbose:
            print("    ci = {}".format(str_ci))
        ci_ok, prod_li = rene_schoof_criterion(c, ci, q, t, verbose)
        if not ci_ok:
            bad_l += " {},".format(str_ci)
            continue
        tested_l += " {},".format(str_ci)
        c3 = c//prod_li
        i = 0
        ok3 = True
        while i < 10 and ok3:
            P = get_point_exact_order(E, r, ci, c3)
            if omega is None:
                cP = cofactor_clearing_g1_name(P, u)
                crP = cofactor_clearing_g1_name(rP, u)
            else:
                cP = cofactor_clearing_g1_name(P, u, omega)
                crP = cofactor_clearing_g1_name(rP, u, omega)
            ok3 = (not cP.is_zero()) and (r*cP).is_zero() and crP.is_zero()
            i = i+1
        if not ok3:
            wrong_l += " {},".format(str_ci)
            ok2 = False
        else:
            good_l += " {},".format(str_ci)
    if len(tested_l) > 0:
        print(" - test {} for points of order ci*r: {} for ci in [{}]".format(cofactor_clearing_g1_name.__name__, ok2, tested_l))
        if not ok2:
            print("     wrong for points of order ci*r, ci in [{}]".format(wrong_l))
            print("     correct for points of order ci*r, ci in [{}]".format(good_l))
    if len(bad_l) > 20:
        print("    points of order ci*r do not exist, ci in list of {}".format(len(bad_l)))
    elif len(bad_l) > 0:
        print("    points of order ci*r do not exist, ci in [{}]".format(bad_l))
    print("test {}: {} {}".format(cofactor_clearing_g1_name.__name__, ok, ok2))
    return ok and ok2

def test_g2_frobenius_eigenvalue(E_FpkA, E2, Fqd, map_Fqd_FpkA, r, c2, D_twist=False):
    """Test that the Frobenius on points of G2 has eigenvalue p

    INPUT:
    -`E_FpkA`: elliptic curve defined over FpkA = Fp[x]/(poly(x)), Fp a prime finite field, k the embedding degree
    - `E2`: a curve defined over Fq an extension of Fp
    - `Fqd`: the extension of degree d above Fq so that Fqd and FpkA are isomorphic
    - `map_Fqd_FpkA`: an explicit map from Fqd to FpkA (absolute extension)
    - `r`: prime integer, order of subgroup of (E and) E2
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURNS: True/False

    The explicit map is needed to circumvent Sage missing tools
    implementation of tower extensions is not yet available in Sage
    documentation from Fp.extension? says:
    Extensions of non-prime finite fields by polynomials are not yet supported:
    we fall back to generic code:
      sage: k.extension(x^5 + x^2 + x - 1)
      Univariate Quotient Polynomial Ring in x over Finite Field in z4 of size 3^4 with modulus x^5 + x^2 + x + 2
    """
    ok = True
    Fpk = E_FpkA.base_field()
    w = Fqd.gen(0)
    a = Fpk.gen(0)
    q = Fpk.characteristic()
    i = 0
    while ok and i < 10:
        Q2 = c2 * E2.random_element()
        while Q2 == E2(0):
            Q2 = c2 * E2.random_element()
        assert r*Q2 == E2(0)
        if D_twist:
            Q0 = psi_sextic_d_twist(Q2, w)
        else:
            Q0 = psi_sextic_m_twist(Q2, w)
        Q = E_FpkA(map_Fqd_FpkA(Q0[0], a), map_Fqd_FpkA(Q0[1], a))
        piQ = E_FpkA([(Q[0]).frobenius(), (Q[1]).frobenius()])
        ok = piQ == q*Q
        i += 1
    print("test Frobenius(Q) == q*Q: {} ({} tests)".format(ok, i))
    return ok

def test_g2_frobenius_eigenvalue_alt(E_FpkA, E2, map_Fq_FpkA, r, c2, D_twist=False):
    """Test that the Frobenius on points of G2 has eigenvalue p

    INPUT:
    -`E_FpkA`: elliptic curve defined over FpkA = Fp[x]/(poly(x)), Fp a prime finite field, k the embedding degree
    - `E2`: a curve defined over Fq an extension of Fp
    - `map_Fq_FpkA`: an explicit map from Fq to FpkA (absolute extension)
    - `r`: prime integer, order of subgroup of (E and) E2
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/d}
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURNS: True/False

    The explicit map is needed to circumvent Sage missing tools
    implementation of tower extensions is not yet available in Sage
    documentation from Fp.extension? says:
    Extensions of non-prime finite fields by polynomials are not yet supported:
    we fall back to generic code:
      sage: k.extension(x^5 + x^2 + x - 1)
      Univariate Quotient Polynomial Ring in x over Finite Field in z4 of size 3^4 with modulus x^5 + x^2 + x + 2
    """
    ok = True
    Fpk = E_FpkA.base_field()
    w = Fpk.gen(0)
    q = Fpk.characteristic()
    i = 0
    while ok and i < 10:
        Q2 = c2 * E2.random_element()
        while Q2 == E2(0):
            Q2 = c2 * E2.random_element()
        assert r*Q2 == E2(0)
        Q2 = [map_Fq_FpkA(Q2[0]), map_Fq_FpkA(Q2[1])]
        if D_twist:
            Q0 = psi_sextic_d_twist(Q2, w)
        else:
            Q0 = psi_sextic_m_twist(Q2, w)
        Q = E_FpkA(Q0)
        piQ = E_FpkA([(Q[0]).frobenius(), (Q[1]).frobenius()])
        ok = piQ == q*Q
        i = i+1
    print("test Frobenius(Q) == q*Q: {}".format(ok))
    return ok

def test_cofactor_clearing_g2(E2, r, c2, u, t2, Fqd, cofactor_clearing_g2_name, D_twist=True, case=None, verbose=True):
    """
    Testing cofactor_clearing_g2_***()
    INPUT:
    - `E2`: d-twist curve defined over GF(p^e)
    - `r`: (prime) order of G2
    - `c2`: cofactor of G2, so that c2*r = order(E2)
    - `u`: curve seed
    - `t2`: trace of E2, for Schoof's criterion
    - `Fqd`: extension of degree d on top of Fq, q=p^e
    - `cofactor_clearing_g2_name`: function name
    - `D_twist`: True/False (Divide-twist or Multiply-twist)
    - `case`: for KSS18 function, optional
    """
    if c2 == 1:
        return True
    if case is not None:
        str_case = " case "+str(case)
    else:
        str_case = ""
    E0 = E2(0)
    ok = True
    i = 0
    while i < 10 and ok:
        Q = E0; rQ = E0; c2Q = E0
        while Q.is_zero() or rQ.is_zero() or c2Q.is_zero():
            Q = E2.random_element()
            rQ = r*Q
            c2Q = c2*Q
        assert (c2*rQ).is_zero()
        if case is not None:
            c2Q = cofactor_clearing_g2_name(Q, u, Fqd, D_twist, case)
            c2rQ = cofactor_clearing_g2_name(rQ, u, Fqd, D_twist, case)
        else:
            c2Q = cofactor_clearing_g2_name(Q, u, Fqd, D_twist)
            c2rQ = cofactor_clearing_g2_name(rQ, u, Fqd, D_twist)
        ok = (not c2Q.is_zero()) and (r*c2Q).is_zero() and c2rQ.is_zero()
        i = i+1
    print(" - test {}{} with random points: {}".format(cofactor_clearing_g2_name.__name__, str_case, ok))
    if not ok:
        return False
    # now refine the test: with points of order ci*r where ci is a small factor of c2
    q = E2.base_field().order()
    if c2.nbits() <= 100 and not c2.is_prime():
        iter_l = [ci for ci in divisors(c2) if ci != 1 and ci != c2]
    else:
        iter_l = [l**(j+1) for l in primes(2**24) for j in range(c2.valuation(l)) if (c2 % l) == 0]
    # if iter_l is empty, there is no other test to make (c2 is prime or is made of large primes only)
    tested_l = "" # for printing: test possible (not skipped because of rational torsion)
    wrong_l = "" # test false for points of order l*r
    good_l = "" # test ok for points of order l*r
    bad_l = "" # points of that order do not exist because of rational l-torsion
    ok2 = True
    for ci in iter_l:
        if ci.nbits() <= 100:
            str_ci = "{}={}".format(ci, ci.factor())
        else:
            str_ci = str(ci)
        if verbose:
            print("    ci = {}".format(str_ci))
        ci_ok, prod_li = rene_schoof_criterion(c2, ci, q, t2, verbose)
        if not ci_ok:
            bad_l += " {},".format(str_ci)
            continue
        tested_l += " {},".format(str_ci)
        c3 = c2//prod_li
        i = 0
        ok3 = True
        while i < 10 and ok3:
            Q = get_point_exact_order(E2, r, ci, c3)
            if case is not None:
                cQ = cofactor_clearing_g2_name(Q, u, Fqd, D_twist, case)
                crQ = cofactor_clearing_g2_name(rQ, u, Fqd, D_twist, case)
            else:
                cQ = cofactor_clearing_g2_name(Q, u, Fqd, D_twist)
                crQ = cofactor_clearing_g2_name(rQ, u, Fqd, D_twist)
            ok3 = (not cQ.is_zero()) and (r*cQ).is_zero() and crQ.is_zero()
            i = i+1
        if not ok3:
            wrong_l += " {},".format(str_ci)
            ok2 = False
        else:
            good_l += " {},".format(str_ci)
    if len(tested_l) > 0:
        print(" - test {}{} for points of order ci*r: {} for ci in [{}]".format(cofactor_clearing_g2_name.__name__, str_case, ok2, tested_l))
        if not ok2:
            print("     wrong for points of order ci*r, ci in [{}]".format(wrong_l))
            print("     correct for points of order ci*r, ci in [{}]".format(good_l))
    if len(bad_l) > 20:
        print("    points of order ci*r do not exist, ci in list of {}".format(len(bad_l)))
    elif len(bad_l) > 0:
        print("    points of order ci*r do not exist, ci in [{}]".format(bad_l))
    print("test {}{}: {} {}".format(cofactor_clearing_g2_name.__name__, str_case, ok, ok2))
    return ok and ok2

def test_membership_testing_g2(E2, r, c2, u, t2, Fqd, membership_testing_g2_name, D_twist=True, verbose=True):
    """
    Testing membership_testing_g2_***()
    INPUT:
    - `E2`: d-twist curve defined over GF(p^e)
    - `r`: (prime) order of G2
    - `c2`: cofactor of G2, so that c2*r = order(E2)
    - `u`: curve seed
    - `t2`: trace of E2, for Schoof's criterion
    - `Fqd`: extension of degree d on top of Fq, q=p^e
    - `membership_testing_g2_name`: function name
    - `D_twist`: True/False (Divide-twist or Multiply-twist)
    """
    # 1. check that input points Q in G2 pass the function
    i = 0
    ok1 = True
    while i < 10 and ok1:
        Q = E2(0)
        while Q.is_zero():
            Q = c2 * E2.random_element()
        ok1 = membership_testing_g2_name(Q, u, Fqd, D_twist)
        i = i+1
    print(" - test {} points in G2 pass: {}".format(membership_testing_g2_name.__name__, ok1))
    # 2. chech that input points Q not in G2 do not pass the test
    q = E2.base_field().order()
    if c2.nbits() <= 100:
        iter_l = [ci for ci in divisors(c2) if ci != 1]
    else:
        iter_l = [l**(j+1) for l in primes(2**24) for j in range(c2.valuation(l)) if (c2 % l) == 0]
    if c2 not in iter_l: # e.g. if the curve is G2-subgroup secure
        iter_l.append(c2)
    tested_l = "" # for printing: test possible (not skipped because of rational torsion)
    wrong_l = "" # test false for points of order l*r
    good_l = "" # test ok for points of order l*r
    bad_l = "" # points of that order do not exist because of rational l-torsion
    ok2 = True
    for ci in iter_l:
        if ci.nbits() <= 100:
            str_ci = "{}={}".format(ci, ci.factor())
        else:
            str_ci = str(ci)
        if verbose:
            print("    ci = {}".format(str_ci))
        ci_ok, prod_li = rene_schoof_criterion(c2, ci, q, t2, verbose)
        if not ci_ok:
            bad_l += " {},".format(str_ci)
            continue
        tested_l += " {},".format(str_ci)
        c3 = c2//prod_li
        i = 0
        ok3 = True
        while i < 10 and ok3:
            Q = get_point_exact_order(E2, r, ci, c3)
            ok3 = not membership_testing_g2_name(Q, u, Fqd, D_twist)
            i = i+1
        if not ok3:
            wrong_l += " {},".format(str_ci)
            ok2 = False
        else:
            good_l += " {},".format(str_ci)
    if len(tested_l) > 0:
        print(" - test {} points not in G2, of order ci*r do not pass: {} for ci in [{}]".format(membership_testing_g2_name.__name__, ok2, tested_l))
        if not ok2:
            print("     wrong for points of order ci*r, ci in [{}]".format(wrong_l))
            print("     correct for points of order ci*r, ci in [{}]".format(good_l))
    if len(bad_l) > 20:
        print("    points of order ci*r do not exist, ci in list of {}".format(len(bad_l)))
    elif len(bad_l) > 0:
        print("    points of order ci*r do not exist, ci in [{}]".format(bad_l))
    print("test {}: {} {}".format(membership_testing_g2_name.__name__, ok1, ok2))
    return ok1 and ok2

def test_miller_function_tate_option_2naf(E, E_Fq6, E2, r, c, c2, D_twist=False, function_name=miller_function_tate):
    """
    Testing Miller function of Tate pairing e_{r}(P, Q), r in binary or 2-naf form.

    Can be used for testing the functions
        miller_function_tate(P, Q2, E.a4(), r)
        miller_function_tate_2naf(P, Q2, E.a4(), r)
    where P and Q2 are both of order r and in E(Fq6) but in distinct subgroups.
    To obtain valid Q2, first Q of order r is sampled from E2(Fq) then
    a map (D-twist or M-twist) is applied to Q to obtain Q2 in E_Fq6.

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fq6`: elliptic curve over GF(q^6) where q = p^{k/6}
    - `E2`: sextic twist over GF(q) where q = p^{k/6} of order r*c2
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/6}
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)
    - `function_name`: either miller_function_tate or miller_function_tate_2naf

    RETURN: true or False
    """
    P = c*E.random_element()
    while P == E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0):
        Q = c2 * E2.random_element()
    Fq6 = E_Fq6.base_field() # assume that the degree 6 extension is explicit
    w = Fq6.gen(0)
    exponent = (Fq6.cardinality()-1) // r # (p^6-1)//r
    if not D_twist:
        Q2 = psi_sextic_m_twist(Q, w)
    else:
        Q2 = psi_sextic_d_twist(Q, w)
    f, rP = function_name(P, Q2, E.a4(), r)
    g = f**exponent
    Fq1 = g.parent()(1)
    ok = True
    ok_non_degenerate = True
    aa = 1
    while ok and aa < 4:
        Pa = aa*P
        bb = 1
        while ok and bb < 4:
            Qb = bb*Q
            if not D_twist:
                Q2b = psi_sextic_m_twist(Qb, w)
            else:
                Q2b = psi_sextic_d_twist(Qb, w)
            fab, abQ = function_name(Pa, Q2b, E.a4(), r)
            gab = fab**exponent
            ok = gab == g**(aa*bb)
            ok_non_degenerate = gab != Fq1
            bb += 1
        aa += 1
    print("test bilinearity {}: {}".format(function_name.__name__, ok))
    print("test non-degeneracy {}: {}".format(function_name.__name__, ok_non_degenerate))
    return ok, ok_non_degenerate

def test_miller_function_tate(E, E_Fq6, E2, r, c, c2, D_twist=False):
    """
    Testing Miller function of Tate pairing e_{r}(P, Q), r in binary form

    Testing the function miller_function_tate(P, Q2, E.a4(), r)

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fq6`: elliptic curve over GF(q^6) where q = p^{k/6}
    - `E2`: sextic twist over GF(q) where q = p^{k/6} of order r*c2
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/6}
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    ok, ok_non_degenerate = test_miller_function_tate_option_2naf(E, E_Fq6, E2, r, c, c2, D_twist=D_twist, function_name=miller_function_tate)
    return ok

def test_miller_function_tate_2naf(E, E_Fq6, E2, r, c, c2, D_twist=False):
    """
    Testing Miller function of Tate pairing e_{r}(P, Q), r in 2-naf form

    Testing the function miller_function_tate_2naf(P, Q2, E.a4(), r)

    INPUT:
    - `E`: elliptic curve over ground field GF(p) of order r*c
    - `E_Fq6`: elliptic curve over GF(q^6) where q = p^{k/6}
    - `E2`: sextic twist over GF(q) where q = p^{k/6} of order r*c2
    - `r`: prime integer, order of subgroup of E and E2
    - `c`: cofactor of E, so that # E(Fp) = r*c
    - `c2`: cofactor of E2, so that # E2(Fq) = r*c2, and q = p^{k/6}
    - `D_twist`: whether E2(Fq) is a D-twist or an M-twist of E(Fq)

    RETURN: true or False
    """
    ok, ok_non_degenerate = test_miller_function_tate_option_2naf(E, E_Fq6, E2, r, c, c2, D_twist=D_twist, function_name=miller_function_tate_2naf)
    return ok

### easy part of final exponentiation

def test_final_exp_easy_k6(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p3 = p**3
    exponent_easy = (p3-1)*(p+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k6(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p3 == 1/g
        i += 1
    print("test final_exp_easy_k6: {}".format(ok))
    print("test after final_exp_easy_k6, f^(p^3) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k9(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p3 = p**3
    p6 = p3**2
    exponent_easy = (p**3-1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k9(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p6 * g**p3 == 1/g
        i += 1
    print("test final_exp_easy_k9: {}".format(ok))
    print("test after final_exp_easy_k9, f^(p^6)*f^(p^3) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k12(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p2 = p**2
    p6 = p2**3
    exponent_easy = (p6-1)*(p2+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k12(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p6 == 1/g
        i += 1
    print("test final_exp_easy_k12: {}".format(ok))
    print("test after final_exp_easy_k12, f^(p^6) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k15(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p5 = p**5
    p10 = p5**2
    exponent_easy = (p5-1)*(p**2+p+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k15(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p10 * g**p5 == 1/g
        i += 1
    print("test final_exp_easy_k15: {}".format(ok))
    print("test after final_exp_easy_k15, f^(p^10)*f^(p^5) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k16(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p8 = p**8
    exponent_easy = (p8-1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k16(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p8 == 1/g
        i += 1
    print("test final_exp_easy_k16: {}".format(ok))
    print("test after final_exp_easy_k16, f^(p^8) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k18(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p3 = p**3
    p9 = p3**3
    exponent_easy = (p9-1)*(p3+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k18(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p9 == 1/g
        i += 1
    print("test final_exp_easy_k18: {}".format(ok))
    print("test after final_exp_easy_k18, f^(p^9) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k20(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p2 = p**2
    p10 = p2**5
    exponent_easy = (p10-1)*(p2+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k20(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p10 == 1/g
        i += 1
    print("test final_exp_easy_k20: {}".format(ok))
    print("test after final_exp_easy_k20, f^(p^10) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k21(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p2 = p**2
    p7 = p**7
    p14 = p7**2
    p_inv = p7 + p14
    exponent_easy = (p7-1)*(p2+p+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k21(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p_inv == 1/g
        i += 1
    print("test final_exp_easy_k21: {}".format(ok))
    print("test after final_exp_easy_k21, f^(p^14)*f^(p^7) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k22(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p11 = p**11
    exponent_easy = (p11-1)*(p+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k22(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p11 == 1/g
        i += 1
    print("test final_exp_easy_k22: {}".format(ok))
    print("test after final_exp_easy_k22, f^(p^11) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k24(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p4 = p**4
    p12 = p4**3
    exponent_easy = (p12-1)*(p4+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k24(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p12 == 1/g
        i += 1
    print("test final_exp_easy_k24: {}".format(ok))
    print("test after final_exp_easy_k24, f^(p^12) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k27(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p9 = p**9
    p18 = p9**2
    exponent_easy = (p9-1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k27(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p18 * g**p9 == 1/g
        i += 1
    print("test final_exp_easy_k27: {}".format(ok))
    print("test after final_exp_easy_k27, f^(p^18)*f^(p^9) == 1/f: {}".format(ok_easy_inv))
    return ok

def test_final_exp_easy_k28(Fqk):
    ok = True
    i = 0
    p = Fqk.characteristic()
    p2 = p**2
    p14 = p2**7
    exponent_easy = (p14-1)*(p2+1)
    ok_easy_inv = True
    while ok and ok_easy_inv and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k28(f)
        ok = f**exponent_easy == g
        ok_easy_inv = g**p14 == 1/g
        i += 1
    print("test final_exp_easy_k28: {}".format(ok))
    print("test after final_exp_easy_k28, f^(p^14) == 1/f: {}".format(ok_easy_inv))
    return ok

### hard part for specific curves

def test_final_exp_hard_bls9(Fqk, u, r, exponent_hard=None):
    p = Fqk.characteristic()
    if exponent_hard is None:
        exponent_hard = (p**6 + p**3 + 1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k9(f)
        h = final_exp_hard_bls9(g, u)
        ok = g**exponent_hard == h
        i += 1
    print("test final_exp_hard_bls9: {}".format(ok))
    return ok

def test_final_exp_bls12(Fqk, r, u, expected_exponent=None):
    # test that this is f^expo
    # with expo = (p^6-1)*(p^2+1)*3*(p^4-p^2+1)//r
    if expected_exponent is None:
        q = Fqk.characteristic()
        expected_exponent = (p**6-1)*(p**2+1)*3*(p**4-p**2+1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_bls12(f, u)
        ok = ok and g**r == Fqk(1)
        if expected_exponent is not None and expected_exponent != 0:
            ok = ok and g == f**expected_exponent
        i += 1
    print("test final_exp_bls12: {}".format(ok))
    return ok

def test_final_exp_2naf_bls12(Fqk, r, u, expected_exponent=None):
    # test that this is f^expo
    # with expo = (p^6-1)*(p^2+1)*3*(p^4-p^2+1)//r
    if expected_exponent is None:
        q = Fqk.characteristic()
        expected_exponent = (p**6-1)*(p**2+1)*3*(p**4-p**2+1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_2naf_bls12(f, u)
        ok = ok and g**r == Fqk(1)
        if expected_exponent is not None and expected_exponent != 0:
            ok = ok and g == f**expected_exponent
        i += 1
    print("test final_exp_2naf_bls12: {}".format(ok))
    return ok

def test_final_exp_hard_bls15(Fqk, u, r, exponent_hard=None, function_name=final_exp_hard_bls15):
    p = Fqk.characteristic()
    if exponent_hard is None:
        exponent_hard = (p**8 - p**7 + p**5 - p**4 + p**3 - p + 1)//r
    else:
        q = p
        assert exponent_hard == ((u-1)**2*(u**2+u+1)*(q*(q**6+q**3+q+1) + (u-1)*(q**6+u*q**5+u**2*q**4+(u**3+1)*q**3+u*(u**3+1)*q**2+(u**2*(u**3+1)+1)*q+u**3*(u**3+1)+u+1)) + 3)
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k15(f)
        h = function_name(g, u)
        ok = g**exponent_hard == h
        i += 1
    print("test {}: {}".format(function_name.__name__, ok))
    return ok

def test_final_exp_bls24_div3(Fqk, r, u, expected_exponent=None):
    # test that this is f^expo
    # with expo = (p^12-1)*(p^4+1)*(p^8-p^4+1)//r
    if expected_exponent is None:
        q = Fqk.characteristic()
        expected_exponent = (p**12-1)*(p**4+1)*(p**8-p**4+1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_bls24_div3(f, u)
        ok = ok and g**r == Fqk(1)
        if expected_exponent is not None and expected_exponent != 0:
            ok = ok and g == f**expected_exponent
        i += 1
    print("test final_exp_bls24_div3: {}".format(ok))
    return ok

def test_final_exp_bls24(Fqk, r, u, expected_exponent=None):
    # test that this is f^expo
    # with expo = (p^12-1)*(p^4+1)*3*(p^8-p^4+1)//r
    if expected_exponent is None:
        q = Fqk.characteristic()
        expected_exponent = (p**12-1)*(p**4+1)*3*(p**8-p**4+1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_bls24(f, u)
        ok = ok and g**r == Fqk(1)
        if expected_exponent is not None and expected_exponent != 0:
            ok = ok and g == f**expected_exponent
        i += 1
    print("test final_exp_bls24: {}".format(ok))
    return ok

def test_final_exp_2naf_bls24(Fqk, r, u, expected_exponent=None):
    # test that this is f^expo
    # with expo = (p^12-1)*(p^4+1)*3*(p^8-p^4+1)//r
    if expected_exponent is None:
        q = Fqk.characteristic()
        expected_exponent = (p**12-1)*(p**4+1)*3*(p**8-p**4+1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_2naf_bls24(f, u)
        ok = ok and g**r == Fqk(1)
        if expected_exponent is not None and expected_exponent != 0:
            ok = ok and g == f**expected_exponent
        i += 1
    print("test final_exp_2naf_bls24: {}".format(ok))
    return ok

def test_final_exp_hard_bls21_v1(Fqk, u, r, exponent_hard=None):
    p = Fqk.characteristic()
    if exponent_hard is None:
        exponent_hard = (p**12-p**11+p**9-p**8+p**6-p**4+p**3-p+1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k21(f)
        h = final_exp_hard_bls21_v1(g, u)
        ok = g**exponent_hard == h
        i += 1
    print("test final_exp_hard_bls21_v1: {}".format(ok))
    return ok

def test_final_exp_hard_bls21_v2(Fqk, u, r, exponent_hard=None):
    p = Fqk.characteristic()
    if exponent_hard is None:
        exponent_hard = 3*(p**12-p**11+p**9-p**8+p**6-p**4+p**3-p+1)//r
    ok = True
    i = 0
    while ok and i < 10:
        f = Fqk.random_element()
        g = final_exp_easy_k21(f)
        h = final_exp_hard_bls21_v2(g, u)
        ok = g**exponent_hard == h
        i += 1
    print("test final_exp_hard_bls21_v2: {}".format(ok))
    return ok

def test_final_exp_hard_bls27(Fqk, u, r, function_name=final_exp_hard_bls27, exponent_hard=None):
    p = Fqk.characteristic()
    if exponent_hard is None:
        exponent_hard = (p**18 + p**9 + 1)//r
    ok = True
    ok_exp = True
    ok_r = True
    ok_inv = True
    i = 0
    while (ok_r and ok_inv and ok_exp) and i < 10:
        f0 = Fqk.random_element()
        f = final_exp_easy_k27(f0)
        g = function_name(f, u)
        ok_r = g**r == Fqk(1)
        ok_exp = g == f**exponent_hard
        ok_inv = g.frobenius(9) * g.frobenius(18) == 1/g
        i += 1
    print("test {}: f^r == 1: {}, f == m^expected_exp: {}, f^(p^9)*f^(p^18) == 1/f: {}".format(function_name.__name__, ok_r, ok_exp, ok_inv))
    return ok_r and ok_exp and ok_inv

def test_final_exp_hard_k16(Fpk, r, u, function_name, expected_exponent):
    """
    testing a function final_exp_hard_k16(m, u)
    INPUT:
    - `Fpk`: absolute extension of degree 16 (where a.frobenius() is defined in SageMath)
    - `r`: prime integer, order of GT
    - `u`: curve seed
    - `function_name`: a final_exp_hard_k16 function (with k=16)
    - `expected_exponent`: an integer multiple of (p^8+1)//r

    Test if the function computes x -> x^expected_exponent and if the result has order r
    """
    p = Fpk.characteristic()
    assert expected_exponent % ((p**8 + 1)//r) == 0
    ok_exp = True
    ok_r = True
    ok_inv = True
    i = 0
    while (ok_r and ok_inv and ok_exp) and i < 10:
        f0 = Fpk.random_element()
        f = final_exp_easy_k16(f0)
        g = function_name(f, u)
        ok_r = g**r == Fpk(1)
        ok_exp = g == f**expected_exponent
        ok_inv = g.frobenius(8) == 1/g
        i = i+1
    print("test {}: f^r == 1: {}, f == m^expected_exp: {}, f^8 == 1/f: {}".format(function_name.__name__, ok_r, ok_exp, ok_inv))
    return ok_r and ok_exp and ok_inv

def test_final_exp_hard_k20(Fpk, u, r, function_name, expected_exponent=None):
    """
    Test the final exponentation, hard part, on curves of embedding degree 20

    INPUT:
    - `Fpk`: Finite field absolute extension of degree 20, where x.frobenius() is defined
    - `u`: seed, integer, can be positive or negative
    - `r`: prime subgroup order
    - `function_name`: e.g. final_exp_hard_fst66_k20, final_exp_hard_kss20_1st
    - `expected_exponent`: test if function_name computes f^expected_exponent
    """
    if expected_exponent is None:
        p = Fpk.characteristic()
        expected_exponent = (p**8 - p**6 + p**4 - p**2 + 1)//r
    ok = True
    ok_r = True
    i = 0
    while (ok or ok_r) and i < 10:
        f = Fpk.random_element()
        g = final_exp_easy_k20(f)
        h = function_name(g, u)
        ok_r = h**r == Fpk(1)
        ok = g**expected_exponent == h
        i += 1
    print("{}: {}, g^r = 1: {}".format(function_name.__name__, ok, ok_r))
    return ok

def test_final_exp_hard_k22(Fpk, u, r, function_name, expected_exponent=None):
    """
    Test the final exponentation, hard part, on curves of embedding degree 22

    INPUT:
    - `Fpk`: Finite field absolute extension of degree 22, where x.frobenius() is defined
    - `u`: seed, integer, can be positive or negative
    - `r`: prime subgroup order
    - `function_name`: e.g. final_exp_hard_fst63_k22, final_exp_hard_kss22_D7
    - `expected_exponent`: test if function_name computes f^expected_exponent
    """
    if expected_exponent is None:
        p = Fpk.characteristic()
        expected_exponent = (p**10 - p**9 + p**8 - p**7 + p**6 - p**5 + p**4 - p**3 + p**2 - p + 1)//r
    ok = True
    ok_r = True
    i = 0
    while (ok or ok_r) and i < 10:
        f = Fpk.random_element()
        g = final_exp_easy_k22(f)
        h = function_name(g, u)
        ok_r = h**r == Fpk(1)
        ok = g**expected_exponent == h
        i += 1
    print("{}: {}, g^r = 1: {}".format(function_name.__name__, ok, ok_r))
    return ok

def test_ate_pairing_bls12_aklgl(E, E2, r, c, c2, t_1, Fq6, map_Fp12_Fp12_A, D_twist=False):
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    f = ate_pairing_bls12_aklgl(Q, P, E2.a6(), t_1, Fq6, map_Fp12_Fp12_A, D_twist=D_twist)
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P 
            fab = ate_pairing_bls12_aklgl(Qb, Pa, E2.a6(), t_1, Fq6, map_Fp12_Fp12_A, D_twist=D_twist)
            fab_expected = f**(aa*bb)
            ok = fab == fab_expected
            aa += 1
        bb += 1
    print("test_ate_pairing_bls12_aklgl (bilinear): {} ({} tests)".format(ok, (aa-1)*(bb-1)))
    return ok

def test_ate_pairing_bls12_2naf_aklgl(E, E2, r, c, c2, t_1, Fq6, map_Fp12_Fp12_A, D_twist=False):
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    f = ate_pairing_bls12_2naf_aklgl(Q, P, E2.a6(), t_1, Fq6, map_Fp12_Fp12_A, D_twist=D_twist)
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P 
            fab = ate_pairing_bls12_2naf_aklgl(Qb, Pa, E2.a6(), t_1, Fq6, map_Fp12_Fp12_A, D_twist=D_twist)
            fab_expected = f**(aa*bb)
            ok = fab == fab_expected
            aa += 1
        bb += 1
    print("test_ate_pairing_bls12_2naf_aklgl (bilinear): {} ({} tests)".format(ok, (aa-1)*(bb-1)))
    return ok

def test_ate_pairing_bls24_aklgl(E, E2, r, c, c2, t_1, Fq6, map_Fp24_Fp24_A, D_twist=False):
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    f = ate_pairing_bls24_aklgl(Q, P, E2.a6(), t_1, Fq6, map_Fp24_Fp24_A, D_twist=D_twist)
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P 
            fab = ate_pairing_bls24_aklgl(Qb, Pa, E2.a6(), t_1, Fq6, map_Fp24_Fp24_A, D_twist=D_twist)
            fab_expected = f**(aa*bb)
            ok = fab == fab_expected
            aa += 1
        bb += 1
    print("test_ate_pairing_bls24_aklgl (bilinear): {} ({} tests)".format(ok, (aa-1)*(bb-1)))
    return ok

def test_ate_pairing_bls24_2naf_aklgl(E, E2, r, c, c2, t_1, Fq6, map_Fp24_Fp24_A, D_twist=False):
    P = c*E.random_element()
    while P == E(0) or r*P != E(0):
        P = c * E.random_element()
    Q = c2*E2.random_element()
    while Q == E2(0) or r*Q != E2(0):
        Q = c2 * E2.random_element()
    f = ate_pairing_bls24_2naf_aklgl(Q, P, E2.a6(), t_1, Fq6, map_Fp24_Fp24_A, D_twist=D_twist)
    ok = True
    bb = 1
    while ok and bb < 4:
        Qb = bb*Q
        aa = 1
        while ok and aa < 4:
            Pa = aa*P 
            fab = ate_pairing_bls24_2naf_aklgl(Qb, Pa, E2.a6(), t_1, Fq6, map_Fp24_Fp24_A, D_twist=D_twist)
            fab_expected = f**(aa*bb)
            ok = fab == fab_expected
            aa += 1
        bb += 1
    print("test_ate_pairing_bls24_2naf_aklgl (bilinear): {} ({} tests)".format(ok, (aa-1)*(bb-1)))
    return ok


def test_bw6_phi(E, r, c, omega):
    print("test bw6_phi(P, omega) (P in G1)")
    ok = True
    E0 = E(0)
    order =r*c
    i = 0
    while ok and i < 10:
        P = E.random_element()
        assert order*P == E0
        phiP = bw6_phi(P, omega)
        phi2P = bw6_phi(phiP, omega)
        ok = (phi2P + phiP + P == E0)
        i = i+1
    print("test bw6_phi(P, omega) (P in G1): {}".format(ok))
    return ok

def find_twist_curve_parameter_xi_ab(ab, Fq, r, g2c, d=6, D_twist=False, ba=None, find_mult_i=None, verbose=False):
    """
    Find the smallest non-zero curve coefficient atw or btw for the d-twist of
    E: y^2 = x^3 + b (3- or 6-twist) or E: y^2 = x^3 + a*x (4-twist)
    or E: y^2 = x^3 + a*x + b (quadratic twist d=2)

    INPUT:
    - `ab`: nonzero curve coefficient of E, d=3,6: b, d=2,4: a
    - `Fq`: field of definition of the d-twist
    - `r`: prime subgroup order
    - `g2c`: cofactor, so that the d-twist order is r*g2c over Fq
    - `d`: twist degree, can be 3, 4, 6 or 2
    - `D_twist`: is it a D-twist (divide: btw = b/xi) or a M-twist (multiply: btw=b*xi)
    - `ba`: the other curve parameter b for quadratic twists

    Cited in Benger-Scott
    Constructing Tower Extensions of Finite Fields for Implementation of
    Pairing-Based Cryptography
    Theorem 3.75 in Lidl Niederreiter
    Let d >= 2 be an integer and alpha in F_{p^m}^{*}. Then
    the binomial x^d - alpha is irreducible in Fpm[x] if and only if
    the following two conditions are satisfied:
    1. each prime factor of d divides the order e of alpha in Fpm*,
       but not (p-1)/e;
    2. If d = 0 mod 4 then p^m = 1 mod 4.

    if Fq is not Fp, then the irreducible binomial x^d - xi maybe should
    be such that xi in Fq but not in Fp (that is, xi = a0 + i).

    In practice, this function is not working very well, it sometimes runs infinity loops I don't know why.
    """
    if d not in [3, 6, 4, 2]:
        raise ValueError("Error the twist degree should be in [3, 6, 4, 2] but d={} given".format(d))
    m = Fq.degree()
    if m == 1:
        i = 0
    else:
        i = Fq.gen(0)
    k = m * d
    if find_mult_i is None:
        if m > 1 and ((d*m % 4) != 0 or (Fq.characteristic() % 4) == 1) and (d*m != 16) and (d*m != 18) and (d*m != 36) and (d*m != 27 or (Fq.characteristic() % 27) == 1):
            find_mult_i = True
        else:
            find_mult_i = False
    print("    p = {} mod {}, find_mult_i = {}".format(Fq.characteristic() % k, k, find_mult_i))
    Fqz_ = Fq['z_']; (z_,) = Fqz_._first_ngens(1)
    if m == 1 or find_mult_i:
        ii = 1
    else:
        ii = 0
    if find_mult_i:
        xi = ii*i
    else:
        xi = i + ii
    order_Etw = False
    while not order_Etw:
        while not (z_**d - xi).is_irreducible():
            if ii <= 0:
                ii = -ii + 1
            else:
                ii = -ii
            if find_mult_i:
                xi = ii*i
            else:
                xi = i + ii
            if verbose:
                print("xi = {}".format(xi))
        if D_twist:
            if d == 3:
                abtw = ab/xi**2
            elif d == 6 or d == 4:
                abtw = ab/xi
            else: # d == 2
                atw = ab/xi**2
                btw = ba/xi**3
        else:
            if d == 3:
                abtw = ab*xi**2
            elif d == 6 or d == 4:
                abtw = ab*xi
            else: # d == 2
                atw = ab*xi**2
                btw = ba*xi**3
        if d == 6 or d == 3:
            Etw = EllipticCurve([Fq(0), abtw])# cubic or sextic twist
        elif d == 4:
            Etw = EllipticCurve([abtw, Fq(0)])# quartic twist
        else:
            Etw = EllipticCurve([atw, btw])# quadratic twist
        P = Etw.random_element()
        if verbose:
            print("test order")
        order_Etw = (r*g2c) * P == Etw(0)
        if not order_Etw:
            if ii <= 0:
                ii = -ii + 1
            else:
                ii = -ii
            if find_mult_i:
                xi = ii*i
            else:
                xi = i + ii
    if (d==3) or (d==6) or (d==4):
        return xi, abtw
    return xi, atw, btw

def find_curve_parameter_a(Fq, r, c):
    """
    Find the smallest curve parameter a, assuming j(E) = 1728 (b=0)
    E: y^2 = x^3 + a*x

    INPUT:
    - `Fq`: finite field of definition of E
    - `r`: subgroup order of E
    - `c`: cofactor of the order

    The curve order should be r*c
    There are four possible orders: r*c, the quadratic twist, or one of the two quartic twists.
    This function iterates over a, starting at a=1, then -1, 2, -2 ...

    RETURN: a, E/Fq
    """
    order_E = False
    order = r*c
    a = 1
    while not order_E:
        E = EllipticCurve([Fq(a), Fq(0)])
        P = E.random_element()
        order_E = order*P == E(0)
        if not order_E:
            if a > 0:
                a = -a
            else:
                a = -a + 1
    return a, E

def find_curve_parameter_b(Fq, r, c):
    """
    Find the smallest curve parameter b, assuming j(E) = 0 (a=0)
    E: y^2 = x^3 + b

    INPUT:
    - `Fq`: finite field of definition of E
    - `r`: subgroup order of E
    - `c`: cofactor of the order

    The curve order should be r*c
    There are six possible orders: r*c, the quadratic twist,
    one of the two cubic twists, one of the two 6-th twists.
    This function iterates over b, starting at b=1, then -1, 2, -2 ...

    RETURN: b, E/Fq
    """
    order_E = False
    order = r*c
    b = 1
    while not order_E:
        E = EllipticCurve([Fq(0), Fq(b)])
        P = E.random_element()
        order_E = order*P == E(0)
        if not order_E:
            if b > 0:
                b = -b
            else:
                b = -b + 1
    return b, E

def get_g2_cofactor(k, d, px, rx, tx):
    """
    INPUT:
    -`k`:  embedding degree
    -`px`: characteristic
    -`tx`: trace
    -`rx`: subgoup order
    -`d`:  twist degree

    RETURN: c2x

    SOURCE: https://gitlab.inria.fr/tnfs-alpha/alpha
            file sage/tnfs/curve/pairing_friendly_curve.py
            function poly_cofactor_twist_g1_g2
    """
    k1 = k // d
    t1 = tx
    t2 = tx**2 - 2*px
    i = 3
    t_im1 = t2 # t_{i-1}
    t_im2 = t1 # t_{i-2}
    while i <= k1:
        t_i = t1*t_im1 - px*t_im2
        t_im2 = t_im1
        t_im1 = t_i
        i = i+1
    if k1 == 1:
        tx_k1 = t1
    elif k1 == 2:
        tx_k1 = t2
    else:
        tx_k1 = t_i
    px_k1 = px**k1
    if d == 3 or d == 6 or d == 4:
        # compute yx_k1 to be able to compute the d-th twist order
        if d == 4:
            yx_k1_square = (tx_k1**2 - 4*px_k1)/(-1)
        else:
            yx_k1_square = (tx_k1**2 - 4*px_k1)/(-3)
        lc = yx_k1_square.leading_coefficient()
        assert lc.is_square()
        yx_k1_square_monic = yx_k1_square / lc
        yx_k1_factors = yx_k1_square_monic.factor()
        yx_k1 = lc.sqrt()
        for fa, ee in yx_k1_factors:
            assert (ee % 2) == 0
            yx_k1 = yx_k1 * fa**(ee//2)
        assert yx_k1**2 == yx_k1_square
    else:
        # no complicated twist
        yx_k1 = 1
    if d == 3 or d == 6:
        if d == 6:
            E2_order = px_k1+1-(-3*yx_k1+tx_k1)/2
            E2_order_= px_k1+1-( 3*yx_k1+tx_k1)/2
            g2twx = px_k1+1+(-3*yx_k1+tx_k1)/2
            g2twx_= px_k1+1+( 3*yx_k1+tx_k1)/2
        elif d == 3:
            E2_order = px_k1+1-(-3*yx_k1-tx_k1)/2
            E2_order_= px_k1+1-( 3*yx_k1-tx_k1)/2
            g2twx = px_k1+1+(-3*yx_k1-tx_k1)/2
            g2twx_= px_k1+1+( 3*yx_k1-tx_k1)/2
        if (E2_order % rx) != 0 and (E2_order_ % rx) == 0:
            E2_order = E2_order_
            g2twx = g2twx_
    elif d == 4:
        E2_order = px_k1 + 1 + yx_k1
        g2twx = px_k1 + 1 - yx_k1 # quadratic twist of G2
        if (E2_order % rx) != 0 and (g2twx % rx) == 0:
            E2_order, g2twx = g2twx, E2_order
    elif d == 2:
        E2_order = px_k1 + 1 + tx_k1
        g2twx = px_k1 + 1 - tx_k1 # quadratic twist of G2
    else: # d==1
        assert d==1
        E2_order = px_k1 + 1 - tx_k1
        g2twx = px_k1 + 1 + tx_k1 # quadratic twist of G2

    assert (E2_order % rx) == 0
    g2cx = E2_order // rx
    return g2cx
