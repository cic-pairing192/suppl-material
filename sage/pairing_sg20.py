from pairing import *

def miller_loop_opt_ate_sg20_v0(Q, P, a, u):
    """Miller loop (f_{2u,Q}(P) l_{2uQ,pi_2(Q)}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x
    - `u`: seed for curve parameters

    """
    m, uQ = miller_function_ate(Q, P, a, 2*u, m0=1)
    Q1 = (uQ[0], uQ[1], uQ[2], uQ[3])
    PP = (P[0], P[1])
    
    pi2Q = ((Q[0]).frobenius(2), (Q[1]).frobenius(2))
    l, Q_ = add_line_j(Q1, pi2Q, PP)
    
    return m * l

def miller_loop_opt_ate_sg20_v1(Q, P, a, u):
    """
    Miller loop f_{u,Q}(P) f_{u,Q}(P)^(p^5) l_{[u]Q,\pi_2(Q)}(P)
       where u can be positive or negative
    the formula is (x - qx^2 + x*qx^5) = 0 mod rx so the pairing equation is
    f_{u,Q}(P) f_{u,Q}(P)^(p^5) l_{[u]Q,\pi_2(Q)}(P)
    
    INPUT:
    - `Q`: point on E(Fpk) or E(Fqd) of order r
    - `P`: point on E(Fp)
    - `u`: seed for curve parameters, non-zero integer in ZZ

    The curve coefficient a is zero.
    """
    m, uQ = miller_function_ate(Q, P, a, u, m0=1)

    f = m.frobenius(5)
    f = m*f # costs one multiplication

    PP = (P[0], P[1])
    Q1 = (uQ[0], uQ[1], uQ[2], uQ[3])

    pi2Q = [(Q[0]).frobenius(2), (Q[1]).frobenius(2)]
    l3, Q3 = add_line_j(Q1, pi2Q, PP)

    f = f*l3 # can be done with a full-sparse multiplication

    return f

def miller_loop_opt_ate_sg20_cln_b0(Q, P, a, u):
    """Miller loop f_{2u,Q}(P) l_{2uQ,pi_2(Q)}(P)

    INPUT:
    - `Q`: point on E(Fpk) or E(Fq4) of order r
    - `P`: point on E(Fp)
    - `a`: curve coefficient in short Weierstrass y^2 = x^3 + a*x
    - `u`: seed for curve parameters

    """
    m, uQ = miller_function_ate_cln_b0(Q, P, a, 2*u)
    pi2Q = ((Q[0]).frobenius(2), (Q[1]).frobenius(2))
    l, Q_ = add_line_ate_cln_b0(uQ, pi2Q, P)
    return m * l

def final_exp_hard_sg20(m, u):
    """
    l0 = -32*x**11 + 24*x**9 - 8*x**7 - 4*x**4 + 2*x**3
    l1 = -64*x**13 + 48*x**11 - 16*x**9 - 8*x**6 + 4*x**5
    l2 = -64*x**13 - 64*x**12 + 48*x**11 + 80*x**10 - 40*x**8 - 20*x**7 - 8*x**6 + 6*x**5 + 10*x**4 + 2*x**3 - 2*x**2 - x - 1
    l3 =  64*x**13 + 64*x**12 - 48*x**11 - 48*x**10 + 16*x**9 + 16*x**8 + 8*x**7 + 8*x**6 - 2*x**5 - 4*x**4 + 2*x**3 + 1
    l4 = -64*x**13 + 48*x**11 - 16*x**9 - 16*x**8 - 8*x**7 + 4*x**6 + 10*x**5 - 4*x**4 - 2*x**3 - 2*x
    l5 = -64*x**13 - 64*x**12 + 16*x**11 + 48*x**10 + 8*x**9 - 16*x**8 - 16*x**7 - 16*x**6 + 2*x**5 + 6*x**4 - 2*x**2 - 1
    l6 =   8*x**7 - 6*x**5 + 2*x**3 + 1
    l7 =  16*x**9 - 12*x**7 + 4*x**5 + 2*x**2 - x
    
    simplified li
    
    l6 = x*(8*x**6 - 6*x**4 + 2*x**2) + 1 = x*cx + 1
    y1 = 2*x*l6 - 1                     #helper value
    l7 = x*y1 = 2*x**2*l6 - x
    y2 = 2*x*l7 = 4*x**3*l6 - 2*x**2    #helper value
    l0 = -x*y2 = -4*x**4*l6 + 2*x**3
    y3 = -2*x*l0 = 8*x**5*l6 - 4*x**4   #helper value
    l1 = -x*y3 = -8*x**6*l6 + 4*x**5
    l4 = l1 - l6 - y1
    l3 = -l1 + l6 + y3
    l2 = l1 - l6 - y3 + y2 + l7 - h = -l3 + y2 + l7 - h
    l5 = l1 - l6 - y3 + l0 - h = -l3 + l0 - h
    
    total cost: 13 exp(|u|) + 19 M + 6 S + 7 f + 7 cj (+1 cj if u<0)
    *** maybe can be optimized a bit more *** 
    """
    
    u0 = abs(u)
    f = m

    #####                  # u = u0 > 0                     # oper.     # u = -u0 < 0                        # oper.
    fu1 = f**u0            # = f^u0                         # 1e_u0     # = f^u0                             # 1e_u0
    fu2 = fu1**u0          # = f^(u0^2)                     # 1e_u0     # = f^(u0^2)                         # 1e_u0
    g = f.frobenius(10)    # = f^(-1)                       # 1inv      # = f^(-1)                           # 1inv
    a1 = fu2*g             # = f^(u0^2 - 1)                 # 1m        # = f^(u0^2 - 1)                     # 1m
    a2 = a1**u0            # = f^(u0^3 - u0)                # 1e_u0     # = f^(u0^3 - u0)                    # 1e_u0
    a3 = a2**u0            # = f^(u0^4 - u0^2)              # 1e_u0     # = f^(u0^4 - u0^2)                  # 1e_u0
    a4 = a3**2             # = f^(2u0^4 - 2u0^2)            # 1s        # = f^(2u0^4 - 2u0^2)                # 1s
    a5 = a4**2             # = f^(4u0^4 - 4u0^2)            # 1s        # = f^(4u0^4 - 4u0^2)                # 1s
    a6 = a5*fu2            # = f^(4u0^4 - 3u0^2)            # 1m        # = f^(4u0^4 - 3u0^2)                # 1m
    a7 = a6*f              # = f^(4u0^4 - 3u0^2 + 1)        # 1m        # = f^(4u0^4 - 3u0^2 + 1)            # 1m
    a8 = a7**u0            # = f^(4u0^5 - 3u0^3 + u0)       # 1e_u0     # = f^(4u0^5 - 3u0^3 + u0)           # 1e_u0
    a9 = a8**u0            # = f^(4u0^6 - 3u0^4 + u0^2)     # 1e_u0     # = f^(4u0^6 - 3u0^4 + u0^2)         # 1e_u0
    fh = a9**2             # = f^h                          # 1m        # = f^h                              # 1m
    fl6 = fh**u0           # = f^(u0*h)                     # 1e_u0     # = f^(u0*h)                         # 1e_u0
    if u < 0:
        fl6 = fl6.frobenius(10)# -                          # -         # = f^(-u0*h)                        # 1inv
    fl6 = fl6*f            # = f^(u0*h + 1)                 # 1m        # = f^(-u0*h + 1)                    # 1m
    #####
    b1 = fl6**u0           # = f^(u0*l6)                    # 1e_u0     # = f^(u0*l6)                        # 1e_u0
    b2 = b1**2             # = f^(2u0*l6)                   # 1s        # = f^(2u0*l6)                       # 1s
    if u < 0:
        fy1 = b2*f                                                      # = f^(u0*l6 + 1)                    # 1m
    else:
        fy1 = b2*g         # = f^(u0*l6 - 1)                # 1m
    fl7 = fy1**u0          # = f^(2u0^2*l6 - u0)            # 1e_u0     # = f^(2u0^2*l6 + u0)                # 1e_u0
    #####
    fy2 = fl7**u0          # = f^(u0*l7)                    # 1e_u0     # = f^(u0*l7)                        # 1e_u0
    fy2 = fy2**2           # = f^(2u0*l7) = f^y2            # 1s        # = f^(2u0*l7) = f^y2                # 1s
    fl0 = fy2**u0          # = f^(2u0^2*l7) = f^(u0*y2)     # 1e_u0     # = f^(2u0^2*l7) = f^(u0*y2)         # 1e_u0
    fl0 = fl0.frobenius(10)# = f^(-u0*y2)                   # 1inv      # = f^(-u0*y2)                   # 1inv
    #####
    fy3 = fl0**u0          # = f^(u0*l0)                    # 1e_u0     # = f^(u0*l0)                    # 1e_u0
    fy3 = fy3**2           # = f^(2u0*l0)                   # 1s        # = f^(2u0*l0)                   # 1s
    fl1 = fy3**u0          # = f^(2u0^2*l0)                 # 1e_u0     # = f^(2u0^2*l0)                 # 1e_u0
    #####
    gl6 = fl6.frobenius(10)# = f^(-l6)                      # 1inv      # = f^(-l6)                      # 1inv
    if u > 0:
        fy1 = fy1.frobenius(10) # = f^(-y1)                 # 1inv      # -                              # -
    c1 = fl1*gl6           # = f^(l1 - l6)                  # 1m        # = f^(l1 - l6)                  # 1m
    fl4 = c1*fy1           # = f^(l1 - l6 - y1)             # 1m        # = f^(l1 - l6 + y1)             # 1m
    #####
    gc1 = c1.frobenius(10) # = f^(l6 - l1)                  # 1inv      # = f^(l6 - l1)                  # 1inv
    fl3 = gc1*fy3          # = f^(l6 - l1 + y3)             # 1m        # = f^(l6 - l1 + y3)             # 1m
    gl3 = fl3.frobenius(10)# = f^(l1 - l6 - y3)             # 1inv      # = f^(l1 - l6 - y3)             # 1inv
    #####
    gh = fh.frobenius(10)  # = f^(-h)                       # 1inv      # = f^(-h)                       # 1inv
    if u < 0:
        fy2 = fy2.frobenius(10) # -                         # -         # = f^(-y2)                      # 1inv
    c2 = gl3*gh            # = f^(l1 - l6 - y3 - h)         # 1m        # = f^(l1 - l6 - y3 - h)         # 1m
    fl2 = c2*fy2*fl7       # = f^(-l3 + y2 + l7 - h)        # 2m        # = f^(-l3 - y2 + l7 - h)        # 2m
    #####
    fl5 = c2*fl0           # = f^(-l3 - h + l0)             # 1m        # = f^(-l3 - h + l0)             # 1m
    
    fl1 = fl1.frobenius(1) # = f^(l1*p)                     # 1f        # = f^(l1*p)                     # 1f
    fl2 = fl2.frobenius(2) # = f^(l2*p^2)                   # 1f        # = f^(l2*p^2)                   # 1f
    fl3 = fl3.frobenius(3) # = f^(l3*p^3)                   # 1f        # = f^(l3*p^3)                   # 1f
    fl4 = fl4.frobenius(4) # = f^(l4*p^4)                   # 1f        # = f^(l4*p^4)                   # 1f
    fl5 = fl5.frobenius(5) # = f^(l5*p^5)                   # 1f        # = f^(l5*p^5)                   # 1f
    fl6 = fl6.frobenius(6) # = f^(l6*p^6)                   # 1f        # = f^(l6*p^6)                   # 1f
    fl7 = fl7.frobenius(7) # = f^(l7*p^7)                   # 1f        # = f^(l7*p^7)                   # 1f
    
    f = fl0*fl1*fl2*fl3*fl4*fl5*fl6*fl7 # = f^(l0 + l1*p + l2*p^2 + l3*p^3 + l4*p^4 + l5*p^5 + l6*p^6 + l7*p^7)     # 7m
    
    return f
