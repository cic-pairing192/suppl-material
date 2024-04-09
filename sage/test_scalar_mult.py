from sage.misc.prandom import randint, randrange
from sage.rings.integer_ring import ZZ

def test_glv_scalar_mult_g1_j0(E, lambda_mod_r, beta_mod_p, r, c):
    """Test GLV sclalar multiplication on G1

    INPUT:
    - `E`: elliptic curve over a prime field Fp, of order r*c, j=0
    - `lambda_mod_r`: the eigenvalue mod r
    - `beta_mod_p`: a primitive cube root of unity mod p
    - `r`: the prime subgroup order
    - `c`: the cofactor

    Check GLV scalar multiplication:
    Given a scalar s (integer) in [1,r], compute s*P as s0*P + s1*phi(P) 
    where phi is an endomorphism of eigenvalue lambda_mod_r, and 
    phi(x, y) = (beta_mod_p*x, y).
    The point P should be of order r.
    """
    ok = True
    i = 0
    while ok and i < 10:
        P = c*E.random_element()
        while P == E(0):
            P = c*E.random_element()
        Fp = E.base_field()
        beta_mod_p = Fp(beta_mod_p)
        phiP = E((P[0]*beta_mod_p, P[1]))
        if phiP != lambda_mod_r * P:
            beta_mod_p = -beta_mod_p-1
            print("test GLV on G1: adjusting beta_mod_p = -beta_mod_p-1")
            phiP = E((P[0]*beta_mod_p, P[1]))
            if phiP != lambda_mod_r * P:
                print("test GLV on G1: error eigenvalue")
                return False
        j = 0
        while ok and j < 10:
            s = ZZ(randint(1, r)) # or randrange(1, r+1)
            s1 = s // lambda_mod_r
            s0 = s % lambda_mod_r
            assert (s1 != 0) and (s0 + s1*lambda_mod_r) == s
            S = s*P
            T = s0*P + s1*phiP
            ok = (T == S) and (S != E(0)) and (r*S == E(0))
            j = j+1
        i = i+1
    print("test GLV on G1 (j=0): {}".format(ok))
    return ok

def test_glv_scalar_mult_g1_j1728(E, lambda_mod_r, beta_mod_p, r, c):
    """Test GLV sclalar multiplication on G1

    INPUT:
    - `E`: elliptic curve over a prime field Fp, of order r*c, j=1728
    - `lambda_mod_r`: the eigenvalue mod r
    - `beta_mod_p`: a primitive fourth root of unity mod p: sqrt(-1)
    - `r`: the prime subgroup order
    - `c`: the cofactor

    Check GLV scalar multiplication:
    Given a scalar s (integer) in [1,r], compute s*P as s0*P + s1*phi(P) 
    where phi is an endomorphism of eigenvalue lambda_mod_r, and
    phi(x, y) = (-x, beta_mod_p*y).
    The point P should be of order r.
    """
    ok = True
    i = 0
    while ok and i < 10:
        P = c*E.random_element()
        while P == E(0):
            P = c*E.random_element()
        Fp = E.base_field()
        beta_mod_p = Fp(beta_mod_p)
        phiP = E((-P[0], P[1]*beta_mod_p))
        if phiP != lambda_mod_r * P:
            beta_mod_p = -beta_mod_p
            print("test GLV on G1: adjusting beta_mod_p = -beta_mod_p")
            phiP = -phiP
            if phiP != lambda_mod_r * P:
                print("test GLV on G1: error eigenvalue")
                return False
        j = 0
        while ok and j < 10:
            s = ZZ(randint(1, r)) # or randrange(1, r+1)
            s1 = s // lambda_mod_r
            s0 = s % lambda_mod_r
            assert (s1 != 0) and (s0 + s1*lambda_mod_r) == s
            S = s*P
            T = s0*P + s1*phiP
            ok = (T == S) and (S != E(0)) and (r*S == E(0))
            j = j+1
        i = i+1
    print("test GLV on G1 (j=1728): {}".format(ok))
    return ok
