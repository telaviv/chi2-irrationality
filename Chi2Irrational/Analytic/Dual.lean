/-
# Theorem B, step 2: discrete weak duality and the pattern sum

For a reference `m` (finitely supported on `[0, Sm]`, `Σ m = h`) and any `lam`:
  `g(s) = log b(s) + 2 P_m(s) − lam`,  `P_m(s) = Σ_{s′≠s} m_{s′} log|s − s′|`,
  `Cd = −E_m + lam h + log 2 (4h + 2 Σ m²)`,  `E_m = Σ_{s≠s′} m_s m_{s′} log|s − s′|`.
* `pattern_le`: for slot assignments `f` with distinct x-slots,
  `∏ b(s_i) ∏_{i<j} pf(s_i, s_j)² ≤ exp(Cd + Σ_i g(s_i))` (lattice inequality `polya_log` applied to `n − m`);
* `abs_det_HT_le_dual`: `|det HT| ≤ (h!)⁻¹ K² exp(Cd + 2 Σ_{1≤s≤S₀} g(s)₊) (3 S₀ + 3 Σ_{S₀<s≤T} e^{g(s)})^h`.
-/
import Chi2Irrational.Analytic.Nodes
import Chi2Irrational.Analytic.Polya

namespace Chi2Irr

open Finset Real

/-! ### Multiplicities -/

/-- Fiberwise sums: `Σ_i F(t_i) = Σ_{s<M} #{i : t_i = s} F(s)`. -/
lemma sum_fiber {n : Type*} [Fintype n] [DecidableEq n] (t : n → ℕ) {M : ℕ} (ht : ∀ i, t i < M) (F : ℕ → ℝ) :
    ∑ i, F (t i) = ∑ s ∈ range M, ((univ.filter (fun i => t i = s)).card : ℝ) * F s := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range M) (g := t) (fun i _ => mem_range.mpr (ht i))]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2]), Finset.sum_const, nsmul_eq_mul]

lemma sum_fiber2 {n : Type*} [Fintype n] [DecidableEq n] (t : n → ℕ) {M : ℕ} (ht : ∀ i, t i < M)
    (G : ℕ → ℕ → ℝ) :
    ∑ i, ∑ j, G (t i) (t j) = ∑ s ∈ range M, ∑ s' ∈ range M,
      ((univ.filter (fun i => t i = s)).card : ℝ) * ((univ.filter (fun i => t i = s')).card : ℝ) * G s s' := by
  rw [sum_fiber t ht (fun s => ∑ j, G s (t j))]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sum_fiber t ht (fun s' => G s s'), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s' _ => by ring)

/-! ### The lattice kernel and the duality identity -/

/-- `L(s, s′) = log|s − s′|` off the diagonal, `0` on it. -/
noncomputable def Lk (s s' : ℕ) : ℝ := if s = s' then 0 else Real.log |(s : ℝ) - s'|

lemma Lk_symm (s s' : ℕ) : Lk s s' = Lk s' s := by
  unfold Lk; split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [abs_sub_comm]

/-- `P_m(s) = Σ_{s′<M} m_{s′} L(s, s′)`. -/
noncomputable def Pm (M : ℕ) (m : ℕ → ℝ) (s : ℕ) : ℝ := ∑ s' ∈ range M, m s' * Lk s s'

/-- `E_m = Σ_{s, s′ < M} m_s m_{s′} L(s, s′)`. -/
noncomputable def Em (M : ℕ) (m : ℕ → ℝ) : ℝ := ∑ s ∈ range M, ∑ s' ∈ range M, m s * m s' * Lk s s'

lemma quad_identity (M : ℕ) (n m : ℕ → ℝ) :
    ∑ s ∈ range M, ∑ s' ∈ range M, n s * n s' * Lk s s' =
      -Em M m + 2 * ∑ s ∈ range M, n s * Pm M m s +
        ∑ s ∈ range M, ∑ s' ∈ range M, (n s - m s) * (n s' - m s') * Lk s s' := by
  have hsym : ∑ s ∈ range M, ∑ s' ∈ range M, m s * n s' * Lk s s' =
      ∑ s ∈ range M, n s * Pm M m s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    unfold Pm; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [Lk_symm]; ring
  have hP : ∑ s ∈ range M, n s * Pm M m s =
      ∑ s ∈ range M, ∑ s' ∈ range M, n s * m s' * Lk s s' := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    unfold Pm; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s' _ => by ring)
  have hexp : ∑ s ∈ range M, ∑ s' ∈ range M, (n s - m s) * (n s' - m s') * Lk s s' =
      ∑ s ∈ range M, ∑ s' ∈ range M, n s * n s' * Lk s s' -
        ∑ s ∈ range M, ∑ s' ∈ range M, n s * m s' * Lk s s' -
        ∑ s ∈ range M, ∑ s' ∈ range M, m s * n s' * Lk s s' + Em M m := by
    unfold Em
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => by ring))
  rw [hexp, hsym, ← hP]
  ring

/-- The lattice inequality in kernel form (`Σ ν = 0`). -/
lemma polya_Lk {M : ℕ} (hM : 1 ≤ M) (ν : ℕ → ℝ) (hν : ∑ s ∈ range M, ν s = 0) :
    ∑ s ∈ range M, ∑ s' ∈ range M, ν s * ν s' * Lk s s' ≤ Real.log 2 * ∑ s ∈ range M, ν s ^ 2 := by
  have h := polya_log hM ν
  rw [hν] at h
  have : ∑ s ∈ range M, ∑ s' ∈ range M, ν s * ν s' * Lk s s' =
      ∑ i ∈ range M, ∑ j ∈ (range M).erase i, ν i * ν j * Real.log |(i : ℝ) - j| := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.add_sum_erase _ _ hi]
    unfold Lk
    rw [ite_eq_left rfl, mul_zero, zero_add]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [ite_eq_right (Finset.ne_of_mem_erase hj).symm]
  rw [this]
  simpa using h

/-! ### One slot assignment -/

lemma pairFactor_eq_exp (a b : ℕ) : pairFactor a b = Real.exp (Lk a b) := by
  unfold pairFactor Lk
  split_ifs with h
  · simp
  · have : 0 < |(a : ℝ) - b| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast h))
    rw [Real.exp_log this]

lemma sum_pairs_symm {n : ℕ} (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 * ∑ i, ∑ j ∈ Ioi i, F i j := by
  have key : ∀ i j, F i j = (if i < j then F i j else 0) + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h.le), add_zero]
    · subst h; simp [hd]
    · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_left h, zero_add]
  have hIoi : ∀ i, ∑ j, (if i < j then F i j else 0) = ∑ j ∈ Ioi i, F i j := by
    intro i
    rw [← Finset.sum_filter]
    congr 1; ext j; simp
  calc ∑ i, ∑ j, F i j = ∑ i, ∑ j, (if i < j then F i j else 0) + ∑ i, ∑ j, (if j < i then F i j else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => key i j)
    _ = ∑ i, ∑ j, (if i < j then F i j else 0) + ∑ i, ∑ j, (if i < j then F i j else 0) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hF]
    _ = 2 * ∑ i, ∑ j ∈ Ioi i, F i j := by simp_rw [hIoi]; ring

/-- The node weight function `g`. -/
noncomputable def gD (q h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) (s : ℕ) : ℝ :=
  Real.log (bN q h s) + 2 * Pm M m s - lam

/-- The dual constant. -/
noncomputable def Cd (h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) : ℝ :=
  -Em M m + lam * h + Real.log 2 * (4 * h + 2 * ∑ s ∈ range M, m s ^ 2)

lemma card_fiber_le_two {h T : ℕ} (f : Fin h → Fin T × Fin 3)
    (hinj : Function.Injective (fun i => xslot (f i))) (s : ℕ) :
    (univ.filter (fun i => tnode (f i) = s)).card ≤ 2 := by
  have := Finset.card_le_card_of_injOn (s := univ.filter (fun i => tnode (f i) = s))
    (t := (univ : Finset Bool)) (fun i => (xslot (f i)).2) (fun _ _ => mem_univ _) (by
      intro i hi j hj hij
      apply hinj
      simp only [mem_filter, mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hi hj
      exact Prod.ext (by simp only [xslot]; rw [hi, hj]) hij)
  simpa using this

/-- **Weak duality for one slot assignment.** -/
theorem pattern_le {q h T M : ℕ} (hq : 2 ≤ q) (hh : 2 ≤ h) (hTM : T < M) (m : ℕ → ℝ)
    (hmsum : ∑ s ∈ range M, m s = h) (lam : ℝ) (f : Fin h → Fin T × Fin 3)
    (hinj : Function.Injective (fun i => xslot (f i))) :
    (∏ i, bN q h (tnode (f i))) * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 ≤
      Real.exp (Cd h M m lam + ∑ i, gD q h M m lam (tnode (f i))) := by
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
  -- the product as an exponential
  have hb : ∀ i, 0 < bN q h (t i) := fun i => bN_pos hq (ht1 i) (by omega)
  have hprod : (∏ i, bN q h (t i)) * ∏ i, ∏ j ∈ Ioi i, pairFactor (t i) (t j) ^ 2 =
      Real.exp (∑ i, Real.log (bN q h (t i)) + ∑ i, ∑ j, Lk (t i) (t j)) := by
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
  -- the pair sum through multiplicities
  have hpairs : ∑ i, ∑ j, Lk (t i) (t j) = ∑ s ∈ range M, ∑ s' ∈ range M, n s * n s' * Lk s s' :=
    sum_fiber2 t ht Lk
  -- the weight sum
  have hwt : ∑ i, Real.log (bN q h (t i)) + 2 * ∑ s ∈ range M, n s * Pm M m s =
      ∑ i, gD q h M m lam (t i) + lam * h := by
    have hP := sum_fiber t ht (fun s => Pm M m s)
    unfold gD
    rw [← hP, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show ∑ i, (Real.log (bN q h (t i)) + 2 * Pm M m (t i) - lam) + lam * h =
      ∑ i, (Real.log (bN q h (t i)) + 2 * Pm M m (t i)) - lam * h + lam * h by
        rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring]
    ring
  -- the lattice inequality
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

/-- The far-node weight: `1` for nodes `≤ S₀`, `e^{g(s)}` beyond. -/
noncomputable def zf (q h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) (S0 : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  if tnode k ≤ S0 then 1 else Real.exp (gD q h M m lam (tnode k))

lemma split_near_far {q h T M : ℕ} (hTM : T < M) (m : ℕ → ℝ) (lam : ℝ) (S0 : ℕ)
    (f : Fin h → Fin T × Fin 3) (hinj : Function.Injective (fun i => xslot (f i))) :
    ∑ i, gD q h M m lam (tnode (f i)) ≤
      2 * ∑ s ∈ range (S0 + 1), max (gD q h M m lam s) 0 +
        ∑ i, (if tnode (f i) ≤ S0 then 0 else gD q h M m lam (tnode (f i))) := by
  set g := gD q h M m lam
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

/-- **The dual bound on the truncated determinant.** -/
theorem abs_det_HT_le_dual {q h T M : ℕ} (hq : 2 ≤ q) (hh : 2 ≤ h) (hTM : T < M) (m : ℕ → ℝ)
    (hmsum : ∑ s ∈ range M, m s = h) (lam : ℝ) (S0 : ℕ) :
    |(HT q h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      (Real.exp (Cd h M m lam + 2 * ∑ s ∈ range (S0 + 1), max (gD q h M m lam s) 0) *
        (∑ k : Fin T × Fin 3, zf q h M m lam S0 k) ^ h) := by
  refine (abs_det_HT_le hq hh).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg _))
  rw [Finset.sum_pow', Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun f _ => ?_)
  split_ifs with hinj
  · refine (pattern_le hq hh hTM m hmsum lam f hinj).trans ?_
    have hsplit := split_near_far (q := q) hTM m lam S0 f hinj
    have hz : ∏ i, zf q h M m lam S0 (f i) =
        Real.exp (∑ i, (if tnode (f i) ≤ S0 then 0 else gD q h M m lam (tnode (f i)))) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      unfold zf; split_ifs <;> simp
    rw [hz, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => by
      unfold zf; split_ifs
      · norm_num
      · exact (Real.exp_pos _).le))

end Chi2Irr
