"""Numerical check of QZ/Margin.lean (mpmath, 50 digits): the bound chain and the true margin at qB..qB+200."""
from mpmath import mp, log, mpf
mp.dps = 50
PhiB = mpf(-4005) / 1000
qB = 177
def margin(q):
    return mpf(133) / 60 + log(q * q - 4) / 4 - log(q) / 3 + mpf(4) / 3 * log(2) + PhiB - log(mpf(q) / qB) / 2
print("177^141 < 2^1053:", 177 ** 141 < 2 ** 1053)
print("closed-form bound 133/60 - 4.005 + (4/3 + 1053/846)*0.6931471808 =",
      mpf(133) / 60 - mpf(4005) / 1000 + (mpf(4) / 3 + mpf(1053) / 846) * mpf('0.6931471808'))
print("max margin over odd q in [177, 10^5]:", max(margin(q) for q in range(177, 100001, 2)))
print("margin(177) =", margin(177))
