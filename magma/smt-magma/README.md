### Notice
Please make sure that the name of the  downloaded file does not contain "()", eg.<TCHES-paper29(1)>.
Otherwise, the code can not be complied at the "camke" step. 

### Algorithms

Based on the famous [RELIC cryptographic toolkit](https://github.com/relic-toolkit/relic) we implemented all building blocks related to pairing-based protocols on BW13-P310, including

 * pairing computation.
*  hashing to  $\mathbb{G}_1$ and $\mathbb{G}_2$.
*  group expontiations in  $\mathbb{G}_1$, $\mathbb{G}_2$ and  $\mathbb{G}_T$.
*  membership testings for $\mathbb{G}_1$, $\mathbb{G}_2$ and  $\mathbb{G}_T$.
### Requirements

The build process requires the [CMake](https://cmake.org/) cross-platform build system. The [GMP](https://gmplib.org/) library is also needed in our benchmarks.

### Build instructions

Instructions for building the library can be found in the [Wiki](https://github.com/relic-toolkit/relic/wiki/Building).


### Source code
  
The main source code of our algorithms are distributed in different folders.  The main functions are:
* pp_map_sup_oatep_k13(fp13_t r, ep_t p, ep13_t q): given $p\in  \mathbb{G}_1$ and $q\in \mathbb{G}_2$,  computing a single pairing.
* pp_map_sim_sup_oatep_k13(fp13_t r,  ep_t *p,   ep13_t *q, int m): computing a m-pairing products
* ep_map(ep_t p, const uint8_t *msg, int len) : hashing to $\mathbb{G}_1$
* ep13_map(ep13_t p, const uint8_t *msg, int len) : hashing to $\mathbb{G}_2$
* ep_mul(ep_t q, ep_t p, bn_t k) : given a random point $p\in \mathbb{G}_1$ and a random scalar $k$, computing $q=[k]p$
* ep13_mul(ep13_t q, ep13_t p, bn_t k) : given a random point $p\in \mathbb{G}_2$ and a random scalar $k$, computing $q=[k]p$
* fp13_exp_gt(fp13_t h1, fp13_t h0,  bn_t k) : given a random point $h0\in \mathbb{G}_T$ and a random exp $k$, computing $h1={h0}^k$
* g1_is_valid_bw13(ep_t p): Checking whether $p$ is a point of $\mathbb{G}_1$ or not.
* g2_is_valid_bw13(ep13_t q): Checking whether $q$ is a point of $\mathbb{G}_2$ or not.
* gt_is_valid_bw13(fp13_t h0): Checking whether $h0$ is a element of $\mathbb{G}_T$ or not.

### Testings, benckmarks and comparisons
* Testings and benckmarks: Function testings and benckmarking can be done by performing the following commands：

    1. mkdir build && cd build 
    2. ../preset/x64-pbc-bw310.sh ../
    3. make
    4. cd bin 
    5. ./test_bw13  (This is to check that our implementation is corrret)
    6. ./bench_pc_bw13 (This is to obtain clock cycles of involved operations on BW13-P310)
  
 * Comparisons: With the development of NFS, the parameters of curves have to upated to really reach the 128-bit security level. BW13-P310 is 128-bit secure curve that provides fast multiplication in  $\mathbb{G}_1$. BN-P446 and BLS12-P446 are two mainstream curves in BN and BLS12 families the 128-bit security level, respectievly. See [1](https://link.springer.com/chapter/10.1007/978-3-030-45388-6_19), [2](https://link.springer.com/article/10.1007/s00145-018-9280-5), [3](https://eprint.iacr.org/2019/485.pdf) for details. BLS24-P315 is another interesting curve at this security level that provides fast group exponentiation in $\mathbb{G}_1$. [RELIC cryptographic toolkit](https://github.com/relic-toolkit/relic) has provided high speed implementations for all building blocks related to pairing protocols on these curves. Timing results can be obtained by performing the following commands：
 
   1. mkdir build && cd build 
   2. ../preset/ < preset >.sh ../
   3. make
   4. cd bin 
   5. ./bench_pc

### Operation count for n-pairings products computation:
Notations:

 M, Mu, S, Su, R, f, e and A: Multiplication, multiplication without reduction, squaring, squaring without reduction, modular reduction, Frobenius, exponentiation by $-z$ and addition in $\mathbb{F}_{p^{13}}$.

m, mu, s, su, r, and a: Multiplication, multiplication without reduction, squaring, squaring without reduction, modular reduction and addition in $\mathbb{F}_{p}$.

    1.pp_add_k13_projc_lazyr():\src\pp\relic_pp_qpl_k13.c
    
       Line310-Line328, point additon, 6M+2Mu+3S+R+8A;
       
        Line 331-Line348 line function computation, 2M+3Mu+39m+2R+7A
        
        total cost: 8M+5Mu+39m+3S+3R+15A
    
    2.pp_dba_k13_projc_lazyr():\src\pp\relic_pp_qpl_k13.c
    
        Line 191- Line 205, point doubling,  2M+Mu+3S+Su+R+7A,
        
        Line 209-Line 228, point addition,  6M+2Mu+3S+R+8A;
        
        Line 232-Line 256,  line function computation, M+5Mu+39m+4R+11A
        
        total cost 9M+8Mu+6S+Su+39m+6R+26A
        
   3. pp_qpl_k13_projc_lazyr():\src\pp\relic_pp_qpl_k13.c
   
       Line 72- Line 104 the point quadrupling, 2*(2M+Mu+3S+Su+R+7A)
       
       Line 107-Line 136 line function computation, 4M+4Mu+S+26m+13mu+4R+14A
       
       total cost 8M+6Mu+7S+2Su+36m+13mu+6R+28A

   4. pp_mil_k13_sim():\src\pp\relic_pp_map_k13.c
   
      Line 68-Line 80,  initializing l1, l2, l3 and l4,
      
      Line 87-Line 100, the first nSQPL:
      
      6S+n*(pp_qpl_k13_projc_lazyr()+4M)
      
      =6S+n*(12M+6Mu+7S+2Su+26m+13mu+6R+28A)
      
      Line 105- Line 114, nSDBLADD:
      
      4S+n*(pp_dba_k13_projc_lazyr()+4M)
      
      =4S+(5M+5Mu+39m+4R+11A
      
      total cost 9M+8Mu+6S+Su+39m+6R+26A)
        
      Line 119- Line 133 the last 4 SQPL:
      
      8S+n*(pp_qpl_k13_projc_lazyr()+4M)
      
      =8S+n*(12M+6Mu+7S+2Su+26m+13mu+6R+28A)
      
      Line 137-Line 141: nSADD
      
      n*(4M+p_add_k13_projc_lazyr())
      
      =n*(12M+5Mu+39m+3S+3R+15A)

  5. pp_exp_bwk13(r, l1, l4): \src\pp\relic_pp_exp_k13.c

  6. pp_map_sim_sup_oatep_k13(): \src\pp\relic_pp_map_k13.c

    the cost of Miller loop: Line 310-356

        Line 301: the main cost of miller loop

        Line 307-356, the cost of function transformation

    Line 359, the cost of the final exponentiation.
