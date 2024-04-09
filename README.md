# Pairings at 192-bit security

This folder contains supplementary material for the paper "A short-list of pairing-friendly curves at the 192-bit security level".

It contains C+ASM implementations for all the curves benchmarked in the Experimental Results: BLS12-1150, FM16-765, KSS16-766, Fam16-766. FM18-768, SG18-638, KSS18-638 and BLS24-509.

For each of this curves, the binaries can be built by locating the `<preset>` file in the `presets` folder and run the following inside the RELIC root folder:

    mkdir -p relic-target
    cd relic-target
    ../presets/<preset>.sh ../
    make

The testing and benchmarking binaries for the pairing module can be found inside the `bin` folder, under names `test_pc` and `bench_pc` respectively.
We provide prebuilt statically-linked binaries to make the job easier, since the library is notoriously non-trivial to configure and build correctly.

The operations benchmarked are tagged:
- `g1_mul` and `g1_mul_sec` for scalar multiplication in G1, with the latter implemented in constant-time.
- `g2_mul` and `g2_mul_sec` for scalar multiplication in G2, with the latter implemented in constant-time.
- `gt_exp` and `gt_exp_sec` for exponentiation in GT, with the latter implemented in constant-time.
- `g1_map` and `g2_map` for hashing to groups G1 and G2, respectively.
- `g1_is_valid`, `g2_is_valid` and `gt_is_valid` for membership testing in groups G1, G2 and GT, respectively.
- `pc_map` and `pc_exp` for the pairing computation and final exponentiation, respectively.
