"""Exact interval sign test of an SU(2) character coefficient at a proposed bare action."""
from fractions import Fraction
from math import factorial, lcm

beta_f, beta_a = Fraction(23, 10), Fraction(-19, 500)
order = 110
# Remove the positive scalar exp(beta_a/3). On the unit circle the
# nonconstant action is P(z)=(beta_f/2)(z+1/z)+(beta_a/3)(z^2+1/z^2).
weights = {1:beta_f/2, -1:beta_f/2, 2:beta_a/3, -2:beta_a/3}
scale = lcm(*(w.denominator for w in weights.values()))
integer = {k:int(scale*w) for k,w in weights.items()}
power, partial = {0:1}, {0:1}
denom = 1
for k in range(1,order+1):
    product = {}
    for n,coeff in power.items():
        for shift,weight in integer.items():
            m = n+shift
            product[m] = product.get(m,0) + coeff*weight
    factor = k*scale
    partial = {n:factor*partial.get(n,0) + product.get(n,0) for n in partial.keys() | product.keys()}
    power = product
    denom *= factor

radius = sum(abs(w) for w in weights.values())
tail = radius**(order+1)/factorial(order+1)/(1-radius/(order+2))
for n in range(2*order-1):
    # Haar sine squared times chi_n reduces to cos(n theta)-cos((n+2) theta).
    # Each omitted Laurent coefficient is bounded by the uniform exponential tail.
    value = Fraction(partial.get(n,0)-partial.get(n+2,0),denom)
    lo, hi = value-2*tail, value+2*tail
    if hi < 0:
        print("beta_F",beta_f,"beta_A",beta_a,"order",order)
        print("first negative SU(2) character coefficient after removing exp(beta_A/3)")
        print("n",n,"spin",Fraction(n,2),"lower",f"{float(lo):.12g}","upper",f"{float(hi):.12g}")
        print("rigorous arithmetic: upper < 0; all preceding lower bounds > 0")
        break
    if lo <= 0:
        raise ValueError(f"insufficient precision at n={n}")
else:
    raise ValueError("no certified negative character in range")
