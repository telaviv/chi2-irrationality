/-
# Theorem B at a real weight `W`, step 2: discrete weak duality (copy of `Analytic/Dual.lean`, `log_bN_le`)

Same statements as `Analytic/Dual.lean` with `bN q` replaced by `bW W` (`W > 0`):
`gDW`, `pattern_leW`, `zfW`, `abs_det_HTW_le_dual`, and the node-weight bound `log_bW_le` of `Analytic/Discrete.lean`.
The `q`-free parts (`Lk`, `Pm`, `Em`, `Cd`, `polya_Lk`, `quad_identity`, `card_fiber_le_two`, …) are reused.
-/
import Chi2Irrational.QZ.Nodes
import Chi2Irrational.Analytic.Discrete

namespace Chi2Irr
namespace QZ

open Finset Real

/-- The node weight function `g` at weight `W`. -/
noncomputable def gDW (W : ℝ) (h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) (s : ℕ) : ℝ :=
  Real.log (bW W h s) + 2 * Pm M m s - lam

/-- **Weak duality for one slot assignment**, weight `W`. -/
theorem pattern_leW {W : ℝ} (hW : 0 < W) {h T M : ℕ} (hh : 2 ≤ h) (hTM : T < M) (m : ℕ → ℝ)
    (hmsum : ∑ s ∈ range M, m s = h) (lam : ℝ) (f : Fin h → Fin T × Fin 3)
    (hinj : Function.Injective (fun i => xslot (f i))) :
    (∏ i, bW W h (tnode (f i))) * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 ≤
      Real.exp (Cd h M m lam + ∑ i, gDW W h M m lam (tnode (f i))) := by
  set t : Fin h → ℕ := fun i => tnode (f i)
  have ht : ∀ i, t i < M := fun i => by simp only [t, tnode]; have := (f i).1.isLt; omega
  have ht1 : ∀ i, 1 ≤ t i := fun i => by simp only [t, tnode]; omega
  set n : ℕ → ℝ := fun s => ((univ.filter (fun i => t i = s)).card : ℝ)
  have hn2 : ∀ s, n s ≤ 2 := fun s => by
    have := card_fiber_le_two f hinj s
    simp only [n, t]; exact_mod_cast this
  have hn0 : ∀ s, 0 ≤ n s := fun s => by positivity
  have hnsum : ∑ s ∈ range M, n s = h := by
    have := sum_fiber t ht (fun _ => (1 : ℝ))
    simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [← this]
  have hM : 1 ≤ M := by omega
  have hb : ∀ i, 0 < bW W h (t i) := fun i => bW_pos hW (ht1 i) (by omega)
  have hprod : (∏ i, bW W h (t i)) * ∏ i, ∏ j ∈ Ioi i, pairFactor (t i) (t j) ^ 2 =
      Real.exp (∑ i, Real.log (bW W h (t i)) + ∑ i, ∑ j, Lk (t i) (t j)) := by
    rw [Real.exp_add, Real.exp_sum, sum_pairs_symm (fun i j => Lk (t i) (t j))
      (fun i j => Lk_symm _ _) (fun i => by simp [Lk])]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => (Real.exp_log (hb i)).symm)
    · rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [pairFactor_eq_exp, ← Real.exp_nat_mul]
      push_cast; ring_nf
  have hpairs : ∑ i, ∑ j, Lk (t i) (t j) = ∑ s ∈ range M, ∑ s' ∈ range M, n s * n s' * Lk s s' :=
    sum_fiber2 t ht Lk
  have hwt : ∑ i, Real.log (bW W h (t i)) + 2 * ∑ s ∈ range M, n s * Pm M m s =
      ∑ i, gDW W h M m lam (t i) + lam * h := by
    have hP := sum_fiber t ht (fun s => Pm M m s)
    unfold gDW
    rw [← hP, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show ∑ i, (Real.log (bW W h (t i)) + 2 * Pm M m (t i) - lam) + lam * h =
      ∑ i, (Real.log (bW W h (t i)) + 2 * Pm M m (t i)) - lam * h + lam * h by
        rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring]
    ring
  have hν : ∑ s ∈ range M, (n s - m s) = 0 := by rw [Finset.sum_sub_distrib, hnsum, hmsum, sub_self]
  have hpol := polya_Lk hM (fun s => n s - m s) hν
  have hsq : ∑ s ∈ range M, (n s - m s) ^ 2 ≤ 4 * h + 2 * ∑ s ∈ range M, m s ^ 2 := by
    have : ∀ s ∈ range M, (n s - m s) ^ 2 ≤ 4 * n s + 2 * m s ^ 2 := by
      intro s _
      have := hn2 s; have := hn0 s
      nlinarith [sq_nonneg (n s + m s)]
    calc ∑ s ∈ range M, (n s - m s) ^ 2 ≤ ∑ s ∈ range M, (4 * n s + 2 * m s ^ 2) := Finset.sum_le_sum this
      _ = 4 * h + 2 * ∑ s ∈ range M, m s ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnsum]
  have hid := quad_identity M n m
  rw [hprod]
  refine Real.exp_le_exp.mpr ?_
  unfold Cd
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hsq hlog2]

/-! ### The sum over slot assignments -/

/-- The far-node weight at weight `W`: `1` for nodes `≤ S₀`, `e^{g(s)}` beyond. -/
noncomputable def zfW (W : ℝ) (h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) (S0 : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  if tnode k ≤ S0 then 1 else Real.exp (gDW W h M m lam (tnode k))

/-- Near/far split for an arbitrary node function `g`. -/
lemma split_near_far_gen {h T M : ℕ} (hTM : T < M) (g : ℕ → ℝ) (S0 : ℕ)
    (f : Fin h → Fin T × Fin 3) (hinj : Function.Injective (fun i => xslot (f i))) :
    ∑ i, g (tnode (f i)) ≤
      2 * ∑ s ∈ range (S0 + 1), max (g s) 0 +
        ∑ i, (if tnode (f i) ≤ S0 then 0 else g (tnode (f i))) := by
  set t : Fin h → ℕ := fun i => tnode (f i)
  have ht : ∀ i, t i < M := fun i => by simp only [t, tnode]; have := (f i).1.isLt; omega
  have hnear : ∑ i, (if t i ≤ S0 then max (g (t i)) 0 else 0) ≤
      2 * ∑ s ∈ range (S0 + 1), max (g s) 0 := by
    rw [sum_fiber t ht (fun s => if s ≤ S0 then max (g s) 0 else 0)]
    calc ∑ s ∈ range M, ((univ.filter (fun i => t i = s)).card : ℝ) * (if s ≤ S0 then max (g s) 0 else 0)
        ≤ ∑ s ∈ range M, 2 * (if s ≤ S0 then max (g s) 0 else 0) := by
          refine Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> simp))
          exact_mod_cast card_fiber_le_two f hinj s
      _ = 2 * ∑ s ∈ (range M).filter (fun s => s ≤ S0), max (g s) 0 := by
          rw [← Finset.mul_sum, Finset.sum_filter]
      _ ≤ 2 * ∑ s ∈ range (S0 + 1), max (g s) 0 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (by norm_num)
          · intro s hs; rw [mem_filter] at hs; rw [mem_range]; omega
          · intro s _ _; exact le_max_right _ _
  calc ∑ i, g (t i) ≤ ∑ i, ((if t i ≤ S0 then max (g (t i)) 0 else 0) +
        (if t i ≤ S0 then 0 else g (t i))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        split_ifs <;> simp [le_max_left]
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

/-- **The dual bound on the truncated determinant**, weight `W > 0`. -/
theorem abs_det_HTW_le_dual {W : ℝ} (hW : 0 < W) {h T M : ℕ} (hh : 2 ≤ h) (hTM : T < M) (m : ℕ → ℝ)
    (hmsum : ∑ s ∈ range M, m s = h) (lam : ℝ) (S0 : ℕ) :
    |(HTW W h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      (Real.exp (Cd h M m lam + 2 * ∑ s ∈ range (S0 + 1), max (gDW W h M m lam s) 0) *
        (∑ k : Fin T × Fin 3, zfW W h M m lam S0 k) ^ h) := by
  refine (abs_det_HTW_le hW hh).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg _))
  rw [Finset.sum_pow', Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun f _ => ?_)
  split_ifs with hinj
  · refine (pattern_leW hW hh hTM m hmsum lam f hinj).trans ?_
    have hsplit := split_near_far_gen hTM (gDW W h M m lam) S0 f hinj
    have hz : ∏ i, zfW W h M m lam S0 (f i) =
        Real.exp (∑ i, (if tnode (f i) ≤ S0 then 0 else gDW W h M m lam (tnode (f i)))) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      unfold zfW; split_ifs <;> simp
    rw [hz, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => by
      unfold zfW; split_ifs
      · norm_num
      · exact (Real.exp_pos _).le))

/-- **The node weight bound** at weight `W > 0`. -/
lemma log_bW_le {W : ℝ} (hW : 0 < W) {h s : ℕ} (hh : 1 ≤ h) (hs : 1 ≤ s) :
    Real.log (bW W h s) ≤ Real.log h + Real.log s - h * Real.log h + h * Vf W ((s : ℝ) / h) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hD := Dr_pos h hs0
  unfold bW phiR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hh0.ne',
    Real.log_div hs0.ne' hD.ne', Real.log_pow]
  have hDge := log_Dr_ge h hs0.le
  set x := (s : ℝ) / h with hx
  have e1 : (s : ℝ) + h = h * (x + 1) := by rw [hx]; field_simp
  have e2 : (s : ℝ) = h * x := by rw [hx]; field_simp
  have k1 : psiF ((s : ℝ) + h) = h * psiF (x + 1) + h * (x + 1) * Real.log h := by rw [e1, psiF_scale hh0]
  have k2 : psiF (s : ℝ) = h * psiF x + h * x * Real.log h := by rw [e2, psiF_scale hh0]
  have k3 : (s : ℝ) * Real.log W = h * (x * Real.log W) := by rw [e2]; ring
  unfold Vf
  rw [k1, k2] at hDge
  rw [k3]
  linarith

end QZ
end Chi2Irr
