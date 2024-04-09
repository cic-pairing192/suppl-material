# Magma scripts to generate formulas

The file [`final_exp_hard.mag`](./final_exp_hard.mag) contains

-   functions that return the polynomials for a given family, for example
    `get_bls_polynomials(k)`, `get_kss16_polynomials()`
-   `final_exp_hard_HHT(k, rx, tx, qx)` to test Theorem 1 in 
	[ePrint 2020/875](https://eprint.iacr.org/2020/875)
	by Hayashida--Hayasaka--Teruya
-   `compute_lll_matrix_poly(dx, qx, max_degree_qx, QQx: verbose:=false)`
    the well-known formulas from (SAC'11) Faster Hashing to G2
	Laura Fuentes-Castaneda, Edward Knapp, Francisco Rodriguez-Henriquez
    https://doi.org/10.1007/978-3-642-28496-0_25
-   `optimal_ate_pairing_fc(k, qx, rx)`
    to compute the formulas for optimal ate pairing according to Vercauteren's
    formulas (with LLL on polynomials)
-   `exponentiation_hard_part(qx, rx, tx, k)` calls `compute_lll_matrix_poly`
    and prints the outputs.
-   `pretty_print_poly(f: with_sign:=false)` to print a polynomial with factored
    denominator and content of coefficients.
-   `get_eigenvalue_G2(t1, y1, te, ye, E2order, g2cx, rx)` compute the
    eigenvalue of the Frobenius endomorphism on the twisted curve, assuming
    there is only one choice so that when reduced mod r, it is equal to the
    characteristic (eigenvalue = q mod r by definition of G2 for optimal ate
    pairings).

The file
[`formulas_for_g1_g2_optimal_ate.mag`](./formulas_for_g1_g2_optimal_ate.mag)
computes the formulas for the eigenvalues,
the optimal ate pairing formula and deduces a formula for a small multiple of
the seed u in terms of Frobenius powers for fast G2 scalar decomposition.
It also contains the formulas for fast subgroup membership testing, fast
co-factor clearing.

The file [`script_final_exp_hard.mag`](./script_final_exp_hard.mag) runs
[`final_exp_hard.mag`](./final_exp_hard.mag) and obtain the formulas for optimal
ate pairing and optimized final exponentiation hard part.
