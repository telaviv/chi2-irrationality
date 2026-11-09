/-
# Lemma 10 at general `ν`: the 2-adic bound on the coefficients of `Δ_h` at odd `q` (RESULT §1)

Generalises `Arith/TwoAdic.lean` from `q₀ ∈ {3, 5}` to every odd `q ≥ 3`, `ν = nu q = v₂(q² − 1) ≥ 3`:
* `twoAdic_Delta`: `‖[X^k] Δ_h‖₂ ≤ 2^{(ν − 2) βp(h) + h (⌊log₂ h⌋ + 6)}` (same Leibniz argument as the `q₀ ∈ {3, 5}`
  file, with `ρ_i = 2^{i+1+(ν−2) rPot i+⌊log₂ h⌋+6−h}`, `κ_j = 2^{j+(ν−2) cPot j}`);
* `twoAdic_odd_proof`: the stub `Q.twoAdic_odd` of `Q/Interface.lean`, from `4 βp(h) ≤ h² + 2h` (`betaP_le`) and
  `30h + 6h log h = o(h²)` (`eventually_rem_le`).
-/
import Chi2Irrational.Q.TwoAdicEntries
import Chi2Irrational.Arith.TwoAdic
import Chi2Irrational.Arith.Assembly

namespace Chi2Irr
namespace Q

open Polynomial Finset Filter

/-- **Lemma 10, general `ν`.** Every coefficient of `Δ_h` has `‖·‖₂ ≤ 2^{(ν−2) βp(h) + h (⌊log₂ h⌋ + 6)}` at odd
`q ≥ 3`. -/
theorem twoAdic_Delta {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (h k : ℕ) :
    padicNorm 2 ((Delta q h).coeff k) ≤
      (2 : ℚ) ^ ((nu q - 2) * betaP h + h * (Nat.log 2 h + 6)) := by
  set L := Nat.log 2 h with hL
  set m := nu q - 2 with hm
  set ρ : Fin h → ℚ := fun i => (2 : ℚ) ^ ((i : ℕ) + 1 + m * rPot h i + L + 6) / (2 : ℚ) ^ h with hρ
  set κ : Fin h → ℚ := fun j => (2 : ℚ) ^ ((j : ℕ) + m * cPot h j) with hκ
  have hentry : ∀ i j : Fin h, PN (ρ i * κ j) (LamP q h (aB i * bB h j)) := by
    intro i j
    have hv := V2_entry hq ho i.isLt j.isLt
    have hle : (2 : ℚ) ^ (-eTA m h i j) ≤ ρ i * κ j := by
      have e : ρ i * κ j =
          (2 : ℚ) ^ ((((i : ℕ) + 1 + m * rPot h i + L + 6 + ((j : ℕ) + m * cPot h j) : ℕ) : ℤ) - h) := by
        rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, pow_add]
        simp only [hρ, hκ]
        ring
      rw [e]
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      have hπ : i + j + 1 - h ≤ rPot h i + cPot h j := by unfold rPot cPot; omega
      have hmπ : (m : ℤ) * ((i + j + 1 - h : ℕ) : ℤ) ≤ (m : ℤ) * (rPot h i : ℤ) + (m : ℤ) * (cPot h j : ℤ) := by
        rw [← mul_add]; exact_mod_cast Nat.mul_le_mul_left m hπ
      unfold eTA
      push_cast
      linarith
    rw [LamP_apply]
    exact PN_entry (hv.1.trans hle) (hv.2.trans hle) (by positivity)
  have hdet : PN ((∏ i, ρ i) * ∏ i, κ i) (Matrix.of (fun i j : Fin h => LamP q h (aB i * bB h j))).det :=
    det_PN _ ρ κ (fun i => by positivity) (fun j => by positivity) hentry
  rw [Delta_eq_anchored]
  refine (hdet k).trans (le_of_eq ?_)
  simp only [hρ, hκ]
  rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum,
    prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i + 1 + m * rPot h i + L + 6) h,
    Fin.sum_univ_eq_sum_range (fun j => j + m * cPot h j) h, ← pow_mul, div_mul_eq_mul_div,
    ← pow_add, div_eq_iff (by positivity), ← pow_add]
  congr 1
  have h1 := sum_succ_add_sum h
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum] at h1 ⊢
  unfold betaP
  nlinarith

/-- The size of the 2-adic exponent: `((ν−2) βp(h) + h (⌊log₂ h⌋ + 6)) log 2 ≤ (c2Odd q + ε) h²` eventually. -/
theorem eventually_n2_le {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    ((((nu q - 2) * betaP h + h * (Nat.log 2 h + 6) : ℕ) : ℤ) : ℝ) * Real.log 2 ≤
      (c2Odd q + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  have hν := three_le_nu hq ho
  set ν' : ℝ := (nu q : ℝ) - 2 with hν'
  have hν'1 : 1 ≤ ν' := by
    have : (3 : ℝ) ≤ nu q := by exact_mod_cast hν
    linarith
  have hc : c2Odd q = ν' / 4 * Real.log 2 := by unfold c2Odd; rfl
  have hK : 0 < ν' + 6 := by linarith
  filter_upwards [eventually_rem_le (ε / (ν' + 6)) (by positivity), eventually_ge_atTop 1] with h hrem hh
  set H : ℝ := (h : ℝ) with hH
  have hH1 : 1 ≤ H := by rw [hH]; exact_mod_cast hh
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hβ : 4 * (betaP h : ℝ) ≤ H ^ 2 + 2 * H := by
    have := betaP_le h; rw [hH]; exact_mod_cast this
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log H := by
    have hp := Nat.pow_log_le_self 2 (by omega : h ≠ 0)
    have : ((2 : ℝ) ^ Nat.log 2 h) ≤ H := by rw [hH]; exact_mod_cast hp
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) this
  have hm : (((nu q - 2 : ℕ)) : ℝ) = ν' := by
    rw [hν']; push_cast [show 2 ≤ nu q by omega]; ring
  have hrem' : (ν' + 6) * (30 * H + 6 * H * Real.log H) ≤ ε * H ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hK] at hrem; linarith
  rw [hc]
  push_cast
  rw [hm, ← hH]
  have e1 : ν' * (betaP h : ℝ) * Real.log 2 ≤ ν' * ((H ^ 2 + 2 * H) / 4) * Real.log 2 := by
    gcongr; linarith
  have e2 : H * ((Nat.log 2 h : ℝ) * Real.log 2) ≤ H * Real.log H :=
    mul_le_mul_of_nonneg_left hL (by linarith)
  have e3 : ν' / 2 * H * Real.log 2 + 6 * H * Real.log 2 ≤ (ν' + 6) * (30 * H) := by
    have : ν' / 2 * H * Real.log 2 ≤ ν' / 2 * H := by
      have : 0 ≤ ν' / 2 * H := by positivity
      nlinarith
    have : 6 * H * Real.log 2 ≤ 6 * H := by nlinarith
    nlinarith
  have e4 : H * Real.log H ≤ (ν' + 6) * (6 * H * Real.log H) := by
    have : 0 ≤ H * Real.log H := by positivity
    nlinarith
  nlinarith

/-- **Lemma 10, general `ν`** (the stub `Q.twoAdic_odd`). -/
theorem twoAdic_odd_proof (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2Odd q + ε) * (h : ℝ) ^ 2 :=
  ⟨fun h => (((nu q - 2) * betaP h + h * (Nat.log 2 h + 6) : ℕ) : ℤ),
    fun h k => by rw [zpow_natCast]; exact twoAdic_Delta hq ho h k, eventually_n2_le hq ho⟩

end Q
end Chi2Irr
