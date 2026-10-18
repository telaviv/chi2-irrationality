/-
# Arithmetic part: shared definitions

* `phi1`: the piecewise-linear `φ₁` (`∫_{2/5}^2 φ₁ = 17/12`);
* `lev K p = #{e ≥ 1 : p^e ≤ 2K − 1}`;
* the class bound for a prime `d` with `d² > 2K − 1` (one level): atoms `m < K` in classes mod `d`, rank
  `r_m = ⌊m/d⌋`, class size `clSize`, weights `wAtom d k = 2[d ≤ 2k+1] − [d ∣ 2k+1]`, running maximum `wMax`, and
  `classBd K d = Σ_{m<K} (2 r_m + 1 + M_m − n_m)₊` (`ℕ`-subtraction is the positive part).
-/
import Mathlib

namespace Chi2Irr

/-- `φ₁`, the per-prime exponent profile of the class bound. -/
noncomputable def phi1 (x : ℝ) : ℝ :=
  if x ≤ 2 / 5 then 2 else if x ≤ 1 / 2 then 3 - 5 * x / 2 else if x ≤ 2 / 3 then 2 - x / 2
  else if x ≤ 1 then 3 - 2 * x else if x ≤ 2 then 2 - x else 0

/-- `lev(p) = #{e ≥ 1 : p^e ≤ 2K − 1}`. -/
def lev (K p : ℕ) : ℕ := ((Finset.Icc 1 (2 * K)).filter (fun e => p ^ e ≤ 2 * K - 1)).card

/-- Atom weight `w_d(k) = 2[d ≤ 2k+1] − [d ∣ 2k+1]`. -/
def wAtom (d k : ℕ) : ℕ := (if d ≤ 2 * k + 1 then 2 else 0) - (if d ∣ 2 * k + 1 then 1 else 0)

/-- The size of the class of `m` modulo `d` in `[0, K)` (for `m < K`). -/
def clSize (K d m : ℕ) : ℕ := (K - 1 - m % d) / d + 1

/-- The maximal weight among the members of the class of `m` that are `≤ m`. -/
def wMax (d m : ℕ) : ℕ := (Finset.range (m / d + 1)).sup (fun j => wAtom d (m % d + j * d))

/-- **The class bound** `Σ_{m<K} (2⌊m/d⌋ + 1 + M_m − n_m)₊`. -/
def classBd (K d : ℕ) : ℕ := ∑ m ∈ Finset.range K, (2 * (m / d) + 1 + wMax d m - clSize K d m)

end Chi2Irr
