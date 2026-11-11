/-
# Lemma 10″ (2-adic bound at `ζ = q/2`, `q` odd), part 2: potentials, Leibniz, the constant `4/3`

`pilot_chi2_2q/RESULT.md` §2. With the entry bound `v₂(G_ij) ≥ −c(i, j)` (`QZ/TwoAdicEntries.lean`), integer dual
potentials (discretising `u(x) = max(−x, x − 4/3)`, `v(y) = max(3 − 3y, y + 1/3)`, `a = ⌊(4h+2)/3⌋`)
  `U_i = −i` (`3i < 2h`), `i − a` (else);   `V_j = 3h − 3j` (`3j < 2h`), `j + 1 − h + a` (else)
satisfy `c(i, j) ≤ U_i + V_j` (`cZ_le_pot`, a four-case `omega` check). The Leibniz bound (`det_PN`) with
`ρ_i = 2^{U_i}`, `κ_j = 2^{V_j}` gives `n₂(h) = Σ_i (U_i + V_i) = 4hm − 3m² + 2m`, `m = ⌊(2h+2)/3⌋` (`n2Z_eq`), and
`3 n₂(h) ≤ 4h² + 4h + 4` (`three_n2Z_le`), i.e. `n₂(h) ≤ (4/3)h² + (4/3)h + 4/3`.
-/
import Chi2Irrational.QZ.TwoAdicEntries

namespace Chi2Irr
namespace QZ

open Polynomial Finset Filter

/-! ### Potentials -/

/-- `a = ⌊(4h + 2)/3⌋ = ⌈4h/3⌉`. -/
def aPot (h : ℕ) : ℕ := (4 * h + 2) / 3

/-- Row potential `U_i`. -/
def UZ (h i : ℕ) : ℤ := if 3 * i < 2 * h then -(i : ℤ) else (i : ℤ) - aPot h

/-- Column potential `V_j`. -/
def VZ (h j : ℕ) : ℤ := if 3 * j < 2 * h then 3 * (h : ℤ) - 3 * j else (j : ℤ) + 1 - h + aPot h

lemma cZ_le_pot {h i j : ℕ} (hi : i < h) (_hj : j < h) : cZ h i j ≤ UZ h i + VZ h j := by
  unfold cZ UZ VZ aPot
  split_ifs <;> omega

/-- The 2-adic exponent `n₂(h) = Σ_i U_i + Σ_j V_j`. -/
def n2Z (h : ℕ) : ℤ := ∑ i ∈ range h, (UZ h i + VZ h i)

lemma prod_two_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, (2 : ℚ) ^ (f i) = (2 : ℚ) ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, zpow_add₀ two_ne_zero]

/-! ### The Leibniz bound -/

/-- **Lemma 10″.** Every coefficient of `Δ_h(X; q/2)` has `‖·‖₂ ≤ 2^{n₂(h)}` for odd `q ≥ 3`. -/
theorem twoAdic_DeltaZ {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (h k : ℕ) :
    padicNorm 2 ((DeltaZ (zq q) h).coeff k) ≤ (2 : ℚ) ^ (n2Z h) := by
  set ρ : Fin h → ℚ := fun i => (2 : ℚ) ^ (UZ h i) with hρ
  set κ : Fin h → ℚ := fun j => (2 : ℚ) ^ (VZ h j) with hκ
  have hentry : ∀ i j : Fin h, PN (ρ i * κ j) (LamPZ (zq q) h (aB i * bB h j)) := by
    intro i j
    have hv := V2_entryZ hq ho i.isLt j.isLt
    have hle : (2 : ℚ) ^ (-(-cZ h i j)) ≤ ρ i * κ j := by
      simp only [hρ, hκ]
      rw [← zpow_add₀ two_ne_zero, neg_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (cZ_le_pot i.isLt j.isLt)
    rw [LamPZ_apply]
    exact PN_entry (hv.1.trans hle) (hv.2.trans hle) (by positivity)
  have hdet : PN ((∏ i, ρ i) * ∏ i, κ i)
      (Matrix.of (fun i j : Fin h => LamPZ (zq q) h (aB i * bB h j))).det :=
    det_PN _ ρ κ (fun i => by positivity) (fun j => by positivity) hentry
  rw [DeltaZ_eq_anchored]
  refine (hdet k).trans (le_of_eq ?_)
  simp only [hρ, hκ]
  rw [prod_two_zpow, prod_two_zpow, ← zpow_add₀ two_ne_zero, n2Z, sum_add_distrib,
    Fin.sum_univ_eq_sum_range (fun i => UZ h i) h, Fin.sum_univ_eq_sum_range (fun j => VZ h j) h]

/-! ### The size of `n₂(h)` -/

lemma sum_lin1 (h n : ℕ) : ∑ i ∈ range n, (3 * (h : ℤ) - 4 * i) = 3 * (h : ℤ) * n - 2 * (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_lin2 (h n : ℕ) : ∑ i ∈ range n, (2 * (i : ℤ) + 1 - h) = (n : ℤ) ^ 2 - (h : ℤ) * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `n₂(h) = 4hm − 3m² + 2m` with `m = ⌊(2h+2)/3⌋ = #{i < h : 3i < 2h}`. -/
lemma n2Z_eq (h : ℕ) :
    n2Z h = 4 * (h : ℤ) * (((2 * h + 2) / 3 : ℕ) : ℤ) - 3 * (((2 * h + 2) / 3 : ℕ) : ℤ) ^ 2 +
      2 * (((2 * h + 2) / 3 : ℕ) : ℤ) := by
  set m := (2 * h + 2) / 3 with hm
  have hmh : m ≤ h := by omega
  have e1 : ∑ i ∈ range m, (UZ h i + VZ h i) = ∑ i ∈ range m, (3 * (h : ℤ) - 4 * i) := by
    refine sum_congr rfl (fun i hi => ?_)
    have := mem_range.mp hi
    unfold UZ VZ
    simp only [show 3 * i < 2 * h by omega, ↓reduceIte]; ring
  have e2 : ∑ i ∈ Ico m h, (UZ h i + VZ h i) = ∑ i ∈ Ico m h, (2 * (i : ℤ) + 1 - h) := by
    refine sum_congr rfl (fun i hi => ?_)
    have := mem_Ico.mp hi
    unfold UZ VZ
    simp only [show ¬ 3 * i < 2 * h by omega, ↓reduceIte]; ring
  have e3 : ∑ i ∈ Ico m h, (2 * (i : ℤ) + 1 - h) =
      ∑ i ∈ range h, (2 * (i : ℤ) + 1 - h) - ∑ i ∈ range m, (2 * (i : ℤ) + 1 - h) := by
    rw [← sum_range_add_sum_Ico _ hmh]; ring
  rw [n2Z, ← sum_range_add_sum_Ico _ hmh, e1, e2, e3, sum_lin1, sum_lin2, sum_lin2]
  ring

/-- `3 n₂(h) ≤ 4h² + 4h + 4`. -/
lemma three_n2Z_le (h : ℕ) : 3 * n2Z h ≤ 4 * (h : ℤ) ^ 2 + 4 * h + 4 := by
  rw [n2Z_eq]
  set m := (2 * h + 2) / 3 with hm
  obtain ⟨r, hr, hr2⟩ : ∃ r : ℕ, 3 * m = 2 * h + r ∧ r ≤ 2 := ⟨3 * m - 2 * h, by omega, by omega⟩
  have hr' : (3 : ℤ) * m = 2 * h + r := by exact_mod_cast hr
  have hr2' : (r : ℤ) ≤ 2 := by exact_mod_cast hr2
  have key : 3 * (4 * (h : ℤ) * m - 3 * (m : ℤ) ^ 2 + 2 * m) = 4 * (h : ℤ) ^ 2 - (r : ℤ) ^ 2 + 4 * h + 2 * r := by
    linear_combination (2 - (r : ℤ) - 3 * m + 2 * h) * hr'
  rw [key]
  nlinarith [sq_nonneg ((r : ℤ) - 1)]

/-- `n₂(h) log 2 ≤ (c2Num + ε) h²` eventually. -/
theorem eventually_n2Z_le : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    (n2Z h : ℝ) * Real.log 2 ≤ (c2Num + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (⌈3 / ε⌉₊ + 1)] with h hh
  have hH : 3 / ε ≤ (h : ℝ) := by
    have h1 := Nat.le_ceil (3 / ε)
    have h2 : ((⌈3 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hh
    push_cast at h2
    linarith
  have hH0 : (0 : ℝ) ≤ h := by positivity
  have hb : 3 * (n2Z h : ℝ) ≤ 4 * (h : ℝ) ^ 2 + 4 * h + 4 := by exact_mod_cast three_n2Z_le h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have h3 : 3 ≤ ε * h := by rwa [div_le_iff₀ hε, mul_comm] at hH
  have hH1 : (1 : ℝ) ≤ h := by
    have : 1 ≤ h := by omega
    exact_mod_cast this
  have e1 : (n2Z h : ℝ) * Real.log 2 ≤ (4 * (h : ℝ) ^ 2 + 4 * h + 4) / 3 * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ hl2.le; linarith
  have e2 : (4 * (h : ℝ) + 4) * Real.log 2 ≤ 4 * (h : ℝ) + 4 :=
    by nlinarith
  have e3 : 3 * (h : ℝ) ≤ ε * h * h := by nlinarith
  unfold c2Num
  nlinarith

/-- **Lemma 10″** (the ingredient `QZ.twoAdic_num` of `QZ/Interface.lean`). -/
theorem twoAdic_num_proof (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaZ (zq q) h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2Num + ε) * (h : ℝ) ^ 2 :=
  ⟨n2Z, fun h k => twoAdic_DeltaZ hq ho h k, eventually_n2Z_le⟩

end QZ
end Chi2Irr
