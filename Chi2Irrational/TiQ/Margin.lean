/-
# Theorem T: the margins `alphaCoreT q + c₂ + β < 0` (`pilot_ti2q/RESULT.md` §6)

Copy of the layout of `Q/Margin.lean` and `Q/Even/Margin.lean`. Elementary log bounds only:
`log(1 + x) ≤ x`, `log 2 < 0.6931471808`, `3¹⁷ < 2²⁷` (`log 3 < (27/17) log 2`), `7⁵ > 2¹⁴` (`log 7 > (14/5) log 2`).
* `q = 6` (direct certificate, `PhiT6 = −2.5671`): `log 37 ≤ log 36 + 1/36`; bound `−0.0025` (true margin `−0.0029`);
* odd `q ≥ 7` (`betaT`, the `q = 6` certificate shifted): `v₂(q² + 1) = 1`, so the sum is
  `133/60 + PhiT6 + ½ log 6 + ¼ log(q² + 1) − (5/6) log q ≤ C + 1/(4q²) − ⅓ log q`; bound `−0.095` at `q = 7`;
* even `q ≥ 8`: `q² + 1` odd, `c(e) ≤ c(1) = 2/33`; bound `−0.10` at `q = 8`.
Numerical check (Arb-free, mpmath to 30 digits, every `q < 20000`): `scripts/tiq/margin_check.py`.
-/
import Chi2Irrational.TiQ.Defs
import Chi2Irrational.Q.Margin
import Chi2Irrational.Q.Even.Margin

namespace Chi2Irr
namespace TiQ

lemma log3_lt : Real.log 3 < 27 / 17 * Real.log 2 := by
  have := Real.log_lt_log (by norm_num) (show (3 : ℝ) ^ 17 < 2 ^ 27 by norm_num)
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

lemma log7_gt : 14 / 5 * Real.log 2 < Real.log 7 := by
  have := Real.log_lt_log (by norm_num) (show (2 : ℝ) ^ 14 < 7 ^ 5 by norm_num)
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

lemma log6_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

/-- `log(q² + 1) ≤ 2 log q + 1/q²`. -/
lemma log_sq_add_one_le {q : ℕ} (hq : 1 ≤ q) :
    Real.log ((q : ℝ) ^ 2 + 1) ≤ 2 * Real.log q + 1 / (q : ℝ) ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h := Q.log_le_log_add (a := (q : ℝ) ^ 2 + 1) (b := (q : ℝ) ^ 2) (by positivity) (by positivity)
  rw [Real.log_pow] at h
  have e : ((q : ℝ) ^ 2 + 1) / (q : ℝ) ^ 2 - 1 = 1 / (q : ℝ) ^ 2 := by field_simp; ring
  rw [e] at h
  push_cast at h
  linarith

lemma cast_sq_add_one (q : ℕ) : ((q ^ 2 + 1 : ℕ) : ℝ) = (q : ℝ) ^ 2 + 1 := by push_cast; ring

/-- `c(e) ≤ c(1) = 2/33` for `e ≥ 1`. -/
lemma cE_le {e : ℕ} (he : 1 ≤ e) : Q.cE e ≤ 2 / 33 := by
  unfold Q.cE
  have he' : (1 : ℚ) ≤ e := by exact_mod_cast he
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Margin at `q = 6`** (the exact statement of `TiQ.margin_t6`). -/
theorem margin_t6_proof : alphaCoreT 6 + Q.c2EvenSharp 6 + (PhiT6 : ℝ) < 0 := by
  have h2 := Real.log_two_lt_d9
  have h3 := log3_lt
  have hv : padicValNat 2 6 = 1 := Q.padicValNat_two_pow_mul_odd 1 3 (by norm_num) (by norm_num)
  have ho1 : Q.oddPart (6 ^ 2 + 1) = 37 := Q.oddPart_of_not_dvd (by norm_num)
  have ho2 : Q.oddPart 6 = 3 := by simp [Q.oddPart, hv]
  have h36 : Real.log 36 = 2 * Real.log 2 + 2 * Real.log 3 := by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.log_pow, log6_eq]; push_cast; ring
  have hA := Q.log_le_log_add (a := 37) (b := 36) (by norm_num) (by norm_num)
  unfold alphaCoreT Q.c2EvenSharp
  rw [ho1, ho2, hv, show PhiT6 = -25671 / 10000 from rfl]
  simp only [Q.cE]
  push_cast
  rw [h36] at hA
  norm_num at hA h2 ⊢
  linarith

/-- **Margin at odd `q ≥ 7`** (the exact statement of `TiQ.margin_t_odd`). -/
theorem margin_t_odd_proof (q : ℕ) (hq : 7 ≤ q) (ho : Odd q) : alphaCoreT q + c2TiOdd + betaT q < 0 := by
  have h2 := Real.log_two_lt_d9
  have h3 := log3_lt
  have h7 := log7_gt
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hv : padicValNat 2 q = 0 :=
    padicValNat.eq_zero_of_not_dvd (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr ho)
  have hoq : Q.oddPart q = q := by simp [Q.oddPart, hv]
  -- `v₂(q² + 1) ≥ 1`
  have hdvd : 2 ∣ q ^ 2 + 1 := by
    obtain ⟨k, rfl⟩ := ho
    have : (2 * k + 1) ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by ring
    rw [this]; exact dvd_mul_right _ _
  have hv1 : 1 ≤ padicValNat 2 (q ^ 2 + 1) := one_le_padicValNat_of_dvd (by positivity) hdvd
  have hL := Q.log_eq_padicVal_add_log_oddPart (n := q ^ 2 + 1) (by positivity)
  rw [cast_sq_add_one] at hL
  have hv1' : (1 : ℝ) ≤ padicValNat 2 (q ^ 2 + 1) := by exact_mod_cast hv1
  have hlq := log_sq_add_one_le (q := q) (by omega)
  have hq7 : Real.log 7 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hinv : 1 / (q : ℝ) ^ 2 ≤ 1 / 49 := by
    have : (49 : ℝ) ≤ (q : ℝ) ^ 2 := by
      have : (7 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    exact one_div_le_one_div_of_le (by norm_num) this
  have hdiv : Real.log ((q : ℝ) / 6) = Real.log q - Real.log 6 := Real.log_div (by positivity) (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpl : (padicValNat 2 (q ^ 2 + 1) : ℝ) * Real.log 2 ≥ Real.log 2 := by nlinarith
  unfold alphaCoreT c2TiOdd betaT
  rw [hoq, hdiv, log6_eq, show PhiT6 = -25671 / 10000 from rfl]
  push_cast
  norm_num at h2 ⊢
  nlinarith

/-- **Margin at even `q ≥ 8`** (the exact statement of `TiQ.margin_t_even`). -/
theorem margin_t_even_proof (q : ℕ) (hq : 8 ≤ q) (he : Even q) :
    alphaCoreT q + Q.c2EvenSharp q + betaT q < 0 := by
  have h2 := Real.log_two_lt_d9
  have h3 := log3_lt
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hodd : ¬ 2 ∣ q ^ 2 + 1 := by
    obtain ⟨k, rfl⟩ := he
    intro h
    have : (k + k) ^ 2 + 1 = 2 * (2 * k ^ 2) + 1 := by ring
    rw [this] at h
    omega
  have ho1 : Q.oddPart (q ^ 2 + 1) = q ^ 2 + 1 := Q.oddPart_of_not_dvd hodd
  have hQ := Q.log_eq_padicVal_add_log_oddPart (n := q) (by omega)
  have he1 : 1 ≤ padicValNat 2 q := one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp he)
  have hc : ((Q.cE (padicValNat 2 q) : ℚ) : ℝ) ≤ 2 / 33 := by
    have := cE_le he1
    have h' : ((Q.cE (padicValNat 2 q) : ℚ) : ℝ) ≤ ((2 / 33 : ℚ) : ℝ) := Rat.cast_le.mpr this
    simpa using h'
  have hlq := log_sq_add_one_le (q := q) (by omega)
  have hq8 : 3 * Real.log 2 ≤ Real.log q := by
    have := Real.log_le_log (by norm_num) (show (8 : ℝ) ≤ q by exact_mod_cast hq)
    rwa [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at this
  have hinv : 1 / (q : ℝ) ^ 2 ≤ 1 / 64 := by
    have : (64 : ℝ) ≤ (q : ℝ) ^ 2 := by
      have : (8 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    exact one_div_le_one_div_of_le (by norm_num) this
  have hdiv : Real.log ((q : ℝ) / 6) = Real.log q - Real.log 6 := Real.log_div (by positivity) (by norm_num)
  unfold alphaCoreT Q.c2EvenSharp betaT
  rw [ho1, cast_sq_add_one, hdiv, log6_eq, show PhiT6 = -25671 / 10000 from rfl]
  push_cast
  norm_num at h2 ⊢
  nlinarith

end TiQ
end Chi2Irr
