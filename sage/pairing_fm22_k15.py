def final_exp_hard_fm22_k15_v0(f, u, p, r):
    """
    k = 15
    D = 3
    px = (3*x**16 - 3*x**15 - 2*x**14 + 4*x**13 - 4*x**12 + 3*x**11 + 4*x**10 - 9*x**9 + 7*x**8 - 4*x**6 + 7*x**5 - 2*x**4 + 3*x**2 - 3*x + 3)/3
    rx = x**8 - x**7 + x**5 - x**4 + x**3 - x + 1
    tx = x**4 + 1 + rx
    cx = x**2 * (3*x**6 - 2*x**4 - x**3 - 2*x**2 + 3)/3

    ***Not claiming that this is the most efficient way to do the final expo***

    l0 =  3*u0 + 3*u0**2 + 3*u0**3 - 3*u0**4 + 3*u0**5 - 2*u0**7 + 4*u0**8 - u0**9 + 2*u0**11 - 5*u0**12 + 3*u0**14
    l1 = -3*u0 - 3*u0**2 - 3*u0**3 - 3*u0**7 - 3*u0**9 + 2*u0**11 + u0**12 + 2*u0**13 - 3*u0**15
    l2 = -3*u0**3 - 3*u0**5 + 2*u0**7 + u0**8 + 2*u0**9 - 3*u0**11
    l3 = -3 + 3*u0 + 3*u0**2 + 3*u0**3 + 5*u0**4 + u0**5 + 2*u0**7 - 5*u0**8 + 3*u0**9 + 3*u0**10 - 2*u0**11 - u0**12 - 2*u0**13 + 3*u0**15
    l4 = 6 - 3*u0**3 - 2*u0**4 + 2*u0**5 - 2*u0**6 + 3*u0**8 - 5*u0**9 - u0**10 + u0**12 + 5*u0**13 - 3*u0**15
    l5 = -3 - 3*u0**4 - 3*u0**6 + 2*u0**8 + u0**9 + 2*u0**10 - 3*u0**12
    l6 = -3 - 3*u0**2 + 2*u0**4 + u0**5 + 2*u0**6 - 3*u0**8
    l7 = 3 + 3*u0 + 3*u0**4 - 5*u0**5 + 2*u0**6 - u0**8 + 4*u0**9 - 2*u0**10 - 3*u0**11 + 3*u0**12

    l0+px*(l1+px*(l2+px*(l3 + px*(l4 + px*(l5 + px*(l6 + px*l7)))))) == exponent

    # total cost for hard part:     15 exp(|u|) + 37 M + 6 S + 11 f15 + 2 f15_5 + 2 i15_cyclo   (u > 0)
                                    15 exp(|u|) + 36 M + 6 S + 11 f15 + 2 f15_5 + 2 i15_cyclo   (u < 0)
    """
    
    u0 = abs(u)
    
    fu1 = f**u0
    fu2 = fu1**u0
    fu3 = fu2**u0
    fu4 = fu3**u0
    fu5 = fu4**u0
    fu6 = fu5**u0
    fu7 = fu6**u0
    fu8 = fu7**u0
    
    #
    f2 = f**2
    f3 = f2*f
    f2u1 = fu1**2
    f3u1 = f2u1*fu1
    f2u2 = fu2**2
    f3u2 = f2u2*fu2
    f2u3 = fu3**2
    f3u3 = f2u3*fu3
    f2u8 = fu8**2
    f3u8 = f2u8*fu8
    
    #
    y1 = f3*f3u2
    y2 = f3u1*f3u3
    y3 = y1*f3u8
    y4 = f3u3*f3u2
    
    #
    z1 = fu4*fu6
    z2 = z1**2

    if u > 0:
        w1 = z2*fu5
        w2 = y3
    else:
        w1 = z2
        w2 = y3*fu5

    gw2 = (w2.frobenius(10)) * (w2.frobenius(5))
    fl6 = w1*gw2
    
    f1l6 = fl6**u0
    f2l6 = f1l6**u0
    f3l6 = f2l6**u0
    f4l6 = f3l6**u0
    f5l6 = f4l6**u0
    f6l6 = f5l6**u0
    f7l6 = f6l6**u0

    #
    if u > 0:
        fp0 = f4l6 * f3u2 * f3u1
        gp0 = f3l6*f6l6
        fp1 = f7l6
        gp1 = y2*f3u2
        fp2 = f3l6
        fp3 = fl6*gp1
        gp3 = f2l6*f7l6
        fp4 = f7l6*f3
        gp4 = f5l6*fl6*y4
        fp5 = f4l6
        gp5 = f3
        fp6 = fl6
        fp7 = f3l6*f3
        gp7 = f1l6*f4l6
    else:
        fp0 = f4l6 * f3u2 * f3l6
        gp0 = f3u1*f6l6
        fp1 = y2
        gp1 = f7l6*f3u2
        gp2 = f3l6
        fp3 = fl6*gp1
        gp3 = f2l6*y2
        fp4 = f5l6*f3*f3u3
        gp4 = fp3
        fp5 = f4l6
        gp5 = f3
        fp6 = fl6
        fp7 = f1l6*f3
        gp7 = f4l6*f3l6

    fp1 = fp1.frobenius(1)
    fp3 = fp3.frobenius(3)
    fp4 = fp4.frobenius(4)
    fp5 = fp5.frobenius(5)
    fp6 = fp6.frobenius(6)
    fp7 = fp7.frobenius(7)

    gp1 = gp1.frobenius(1)
    gp3 = gp3.frobenius(3)
    gp4 = gp4.frobenius(4)
    gp5 = gp5.frobenius(5)
    gp7 = gp7.frobenius(7)

    if u > 0:
        fp2 = fp2.frobenius(2)
        gp2 = 1
    else:
        gp2 = gp2.frobenius(2)
        fp2 = 1

    A = fp0*fp1*fp2*fp3*fp4*fp5*fp6*fp7
    B = gp0*gp1*gp2*gp3*gp4*gp5*gp7
    C = (B.frobenius(10)) * (B.frobenius(5))

    t0 = A*C

    return t0
