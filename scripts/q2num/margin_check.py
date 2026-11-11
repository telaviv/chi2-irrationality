"""Numerical check of QZ/Margin.lean (mpmath, 50 digits): the bound chain and the true margin at qB..qB+200."""
from mpmath import mp, log, mpf
mp.dps = 50
PhiB = mpf(-4003) / 1000
qB = 175
def margin(q):
    return mpf(133) / 60 + log(q * q - 4) / 4 - log(q) / 3 + mpf(4) / 3 * log(2) + PhiB - log(mpf(q) / qB) / 2
print("175^104 < 2^775:", 175 ** 104 < 2 ** 775)
print("closed-form bound 133/60 - 4.003 + (4/3 + 775/624)*0.6931471808 =",
      mpf(133) / 60 - mpf(4003) / 1000 + (mpf(4) / 3 + mpf(775) / 624) * mpf('0.6931471808'))
print("max margin over odd q in [175, 10^5]:", max(margin(q) for q in range(175, 100001, 2)))
print("margin(175) =", margin(175))
