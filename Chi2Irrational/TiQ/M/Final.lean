/-
# Lemma M: the 2-adic bound `n₂(h) ≤ h²/8 + O(h log h)` for `Δ^Ti_h` at odd `q` (RESULT §1 steps 4–5)

`Δ^Ti_h = (Π_{i<h} i!)² det(Em + (X − θ) Aᵀ O A)` (`Gram.lean`) `= (Π i!)² det N` with the `3h × 3h` block matrix
`N = [[Em, Aᵀ, 0], [0, 1, −(X − θ) O], [−A, 0, 1]]` (`det_block`). One Leibniz bound with integer row/column potentials
(`det_PNz`) gives `‖coeff‖₂ ≤ 2^{SM(h) − 2 Σ_{i<h} v₂(i!)}`. The potentials, with `α = −⌊h/2⌋`, `γ = 2 − h + ⌊h/2⌋`,
`β = α − ⌊h/4⌋` (the crossover at `h/4` is RESULT's extremal quarter of node levels):
* rows: `Em`-rows `j ↦ max(j + α, 2j + β)`; middle rows `n ↦ max(2n + β, n)`; bottom rows `n ↦ −2n − β`;
* columns: `Em`-columns `j ↦ max(j + γ, 2j + β)`; middle columns `n ↦ −2n − β`; right columns `n ↦ max(2n + β, n)`.
Entry bounds: (A) `Em` (`boundA`, `2^{i+j+2−h}`), (C) `A` (`Am_bound`, `Am_zero`), (B) `O` (`Om_bound`) with `‖θ‖₂ ≤ 2`.
`2 SM(h) ≤ 9h²/4 + O(h)` and `Σ v₂(i!) ≥ h(h−1)/2 − h(log₂ h + 1)`, so the limit constant is `⅛ log 2`.
-/
import Chi2Irrational.TiQ.M.Gram
import Chi2Irrational.TiQ.M.BoundA
import Chi2Irrational.TiQ.M.BoundB

namespace Chi2Irr
namespace TiQ
namespace M

open Polynomial Finset Filter

lemma prod_two_zpow {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, (2 : ℚ) ^ (a i) = (2 : ℚ) ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [prod_insert hx, sum_insert hx, ih, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]

/-- **Leibniz bound with integer potentials** over any finite index type. -/
theorem det_PNz {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℚ[X]) (r c : ι → ℤ)
    (hN : ∀ i j, PN ((2 : ℚ) ^ (r i + c j)) (N i j)) :
    PN ((2 : ℚ) ^ (∑ i, r i + ∑ j, c j)) N.det := by
  have h0 : (0 : ℚ) ≤ (2 : ℚ) ^ (∑ i, r i + ∑ j, c j) := by positivity
  rw [Matrix.det_apply]
  refine PN_sum _ h0 _ (fun σ _ => ?_)
  have hprod : PN ((2 : ℚ) ^ (∑ i, r i + ∑ j, c j)) (∏ i, N (σ i) i) := by
    have := PN_prod univ (fun i => (2 : ℚ) ^ (r (σ i) + c i)) (fun i => by positivity) (fun i => N (σ i) i)
      (fun i _ => hN (σ i) i)
    rwa [prod_two_zpow, sum_add_distrib, Equiv.sum_comp σ r] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact PN_neg hprod

/-! ### The potentials -/

/-- `α = −⌊h/2⌋`. -/
def alp (h : ℕ) : ℤ := -((h / 2 : ℕ) : ℤ)

/-- `γ = 2 − h + ⌊h/2⌋`, so that `α + γ = 2 − h`. -/
def gam (h : ℕ) : ℤ := 2 - (h : ℤ) + ((h / 2 : ℕ) : ℤ)

/-- `β = α − ⌊h/4⌋`. -/
def bet (h : ℕ) : ℤ := alp h - ((h / 4 : ℕ) : ℤ)

/-- Row potentials (exponents of 2). -/
def rP (h : ℕ) : Fin h ⊕ (Fin h ⊕ Fin h) → ℤ
  | Sum.inl j => max ((j : ℤ) + alp h) (2 * (j : ℤ) + bet h)
  | Sum.inr (Sum.inl n) => max (2 * (n : ℤ) + bet h) n
  | Sum.inr (Sum.inr n) => -2 * (n : ℤ) - bet h

/-- Column potentials (exponents of 2). -/
def cP (h : ℕ) : Fin h ⊕ (Fin h ⊕ Fin h) → ℤ
  | Sum.inl j => max ((j : ℤ) + gam h) (2 * (j : ℤ) + bet h)
  | Sum.inr (Sum.inl n) => -2 * (n : ℤ) - bet h
  | Sum.inr (Sum.inr n) => max (2 * (n : ℤ) + bet h) n

/-- The sum of the potentials. -/
def SM (h : ℕ) : ℤ := ∑ i, rP h i + ∑ j, cP h j

/-- The 2-adic exponent of Lemma M. -/
def n2M (h : ℕ) : ℤ := SM h - 2 * ∑ i ∈ range h, (vf i : ℤ)

/-! ### Entry bounds of the block matrix -/

lemma PN_C' {a B : ℚ} (ha : padicNorm 2 a ≤ B) (hB : 0 ≤ B) : PN B (C a) := fun k => by
  rw [coeff_C]
  split_ifs
  · exact ha
  · simpa using hB

lemma two_zpow_le {a b : ℤ} (hab : a ≤ b) : (2 : ℚ) ^ a ≤ (2 : ℚ) ^ b :=
  zpow_le_zpow_right₀ (by norm_num) hab

lemma PN_Am_entry (h : ℕ) (n j : Fin h) {e : ℤ} (he : 2 * ((j : ℤ) - n) ≤ e) :
    PN ((2 : ℚ) ^ e) (C (Am h n j)) := by
  rcases lt_or_ge (j : ℕ) n with hjn | hjn
  · rw [Am_zero hjn, map_zero]; exact PN_zero (by positivity)
  · exact PN_C' ((Am_bound h n j).trans (two_zpow_le he)) (by positivity)

lemma PN_one_entry {e : ℤ} (he : 0 ≤ e) : PN ((2 : ℚ) ^ e) (1 : ℚ[X]) := by
  have : PN 1 (1 : ℚ[X]) := PN_one
  exact fun k => (this k).trans (by simpa using two_zpow_le he)

theorem Nblk_entry {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (h : ℕ) (i j : Fin h ⊕ (Fin h ⊕ Fin h)) :
    PN ((2 : ℚ) ^ (rP h i + cP h j))
      (Nblk ((Em q h).map C) ((Am h).map C) ((Om q h).map C) (X - C (theta q h)) i j) := by
  have hpos : ∀ e : ℤ, (0 : ℚ) ≤ (2 : ℚ) ^ e := fun e => by positivity
  have hag : alp h + gam h = 2 - h := by unfold alp gam; ring
  rcases i with j0 | n0 | n0 <;> rcases j with j1 | n1 | n1
  · -- `Em` block
    simp only [Nblk, Matrix.fromBlocks_apply₁₁, Matrix.map_apply]
    refine PN_C' ((boundA hq ho j0 j1).trans (two_zpow_le ?_)) (hpos _)
    simp only [rP, cP]
    have := le_max_left ((j0 : ℤ) + alp h) (2 * j0 + bet h)
    have := le_max_left ((j1 : ℤ) + gam h) (2 * j1 + bet h)
    omega
  · -- `Aᵀ` block
    simp only [Nblk, Matrix.fromBlocks_apply₁₂, Matrix.fromCols_apply_inl, Matrix.transpose_apply,
      Matrix.map_apply]
    refine PN_Am_entry h n1 j0 ?_
    simp only [rP, cP]
    have := le_max_right ((j0 : ℤ) + alp h) (2 * j0 + bet h)
    omega
  · simp only [Nblk, Matrix.fromBlocks_apply₁₂, Matrix.fromCols_apply_inr, Matrix.zero_apply]
    exact PN_zero (hpos _)
  · simp only [Nblk, Matrix.fromBlocks_apply₂₁, Matrix.fromRows_apply_inl, Matrix.zero_apply]
    exact PN_zero (hpos _)
  · -- identity block
    simp only [Nblk, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    split_ifs with hnn
    · subst hnn
      refine PN_one_entry ?_
      simp only [rP, cP]
      have := le_max_left (2 * (n0 : ℤ) + bet h) n0
      omega
    · exact PN_zero (hpos _)
  · -- `−(X − θ) O` block
    simp only [Nblk, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    have e : -((X - C (theta q h)) * C (Om q h n0 n1)) =
        C (theta q h * Om q h n0 n1) + X * C (-Om q h n0 n1) := by
      simp only [map_mul, map_neg]; ring
    rw [e]
    have hO := Om_bound ho h n0 n1
    have hθ := theta_bound hq ho h
    have hle : (2 : ℚ) ^ ((n0 : ℤ) + n1) ≤ (2 : ℚ) ^ (rP h (Sum.inr (Sum.inl n0)) + cP h (Sum.inr (Sum.inr n1))) := by
      refine two_zpow_le ?_
      simp only [rP, cP]
      have := le_max_right (2 * (n0 : ℤ) + bet h) n0
      have := le_max_right (2 * (n1 : ℤ) + bet h) n1
      omega
    have h2e : (2 : ℚ) ^ ((n0 : ℤ) + n1) = 2 * (2 : ℚ) ^ ((n0 : ℤ) + n1 - 1) := by
      rw [show ((n0 : ℤ) + n1) = 1 + ((n0 : ℤ) + n1 - 1) by ring, zpow_add₀ (by norm_num), zpow_one]
      ring_nf
    refine PN_entry ?_ ?_ (hpos _)
    · rw [padicNorm.mul]
      refine le_trans ?_ hle
      rw [h2e]
      exact mul_le_mul hθ hO (padicNorm.nonneg _) (by norm_num)
    · rw [padicNorm.neg]
      refine le_trans (hO.trans (two_zpow_le (by omega))) hle
  · simp only [Nblk, Matrix.fromBlocks_apply₂₁, Matrix.fromRows_apply_inr, Matrix.neg_apply, Matrix.map_apply]
    refine PN_neg (PN_Am_entry h n0 j1 ?_)
    simp only [rP, cP]
    have := le_max_right ((j1 : ℤ) + gam h) (2 * j1 + bet h)
    omega
  · simp only [Nblk, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    exact PN_zero (hpos _)
  · simp only [Nblk, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    split_ifs with hnn
    · subst hnn
      refine PN_one_entry ?_
      simp only [rP, cP]
      have := le_max_left (2 * (n0 : ℤ) + bet h) n0
      omega
    · exact PN_zero (hpos _)

/-! ### The bound -/

lemma padicNorm_factorial (n : ℕ) : padicNorm 2 ((n.factorial : ℕ) : ℚ) = (2 : ℚ) ^ (-(vf n : ℤ)) := by
  have hn : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [padicNorm.eq_zpow_of_nonzero hn, padicValRat.of_nat]
  rfl

lemma padicNorm_prod_factorial_sq (h : ℕ) :
    padicNorm 2 ((∏ i ∈ range h, ((i.factorial : ℕ) : ℚ)) ^ 2) =
      (2 : ℚ) ^ (-(2 * ∑ i ∈ range h, (vf i : ℤ))) := by
  rw [sq, padicNorm.mul]
  have : padicNorm 2 (∏ i ∈ range h, ((i.factorial : ℕ) : ℚ)) = (2 : ℚ) ^ (-(∑ i ∈ range h, (vf i : ℤ))) := by
    induction h with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, padicNorm.mul, ih, padicNorm_factorial, sum_range_succ, neg_add,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  rw [this, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  ring

/-- **Lemma M**, finite form. -/
theorem twoAdic_DeltaT_M {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (h k : ℕ) :
    padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2M h) := by
  have hdet : (HM q h).det =
      (Nblk ((Em q h).map C) ((Am h).map C) ((Om q h).map C) (X - C (theta q h))).det := by
    rw [det_block, HM_eq q h (theta q h)]
    congr 2
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hN := det_PNz _ (rP h) (cP h) (Nblk_entry hq ho h)
  rw [← hdet] at hN
  rw [DeltaT_eq_Cb, coeff_C_mul, padicNorm.mul, padicNorm_prod_factorial_sq]
  have e : n2M h = -(2 * ∑ i ∈ range h, (vf i : ℤ)) + SM h := by unfold n2M; ring
  rw [e, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  exact mul_le_mul_of_nonneg_left (hN k) (by positivity)

/-! ### The asymptotics -/

/-- `2 Σ_{j<h} max(0, T − j) ≤ T(T+1)` for `T ≥ 0`. -/
lemma sum_pos_part_le (T : ℤ) (hT : 0 ≤ T) (h : ℕ) :
    2 * ∑ j ∈ range h, max (0 : ℤ) (T - j) ≤ T * (T + 1) := by
  have key : ∀ m : ℕ, 2 * ∑ j ∈ range m, max (0 : ℤ) (T - j) +
      max (0 : ℤ) (T - m) * (max (0 : ℤ) (T - m) + 1) = T * (T + 1) := by
    intro m
    induction m with
    | zero => simp [max_eq_right hT]
    | succ n ih =>
      rw [sum_range_succ]
      push_cast
      rcases le_or_gt T n with hTn | hTn
      · rw [max_eq_left (by omega : T - (n : ℤ) ≤ 0), max_eq_left (by omega : T - ((n : ℤ) + 1) ≤ 0)] at *
        linarith
      · rw [max_eq_right (by omega : (0 : ℤ) ≤ T - n)] at ih ⊢
        rw [max_eq_right (by omega : (0 : ℤ) ≤ T - ((n : ℤ) + 1))]
        linarith
  have := key h
  have h1 : 0 ≤ max (0 : ℤ) (T - h) * (max (0 : ℤ) (T - h) + 1) := by
    have := le_max_left (0 : ℤ) (T - h); positivity
  linarith

lemma max_eq_add_pos (a b : ℤ) : max a b = b + max 0 (a - b) := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, max_eq_left (by omega)]; ring
  · rw [max_eq_left hab, max_eq_right (by omega)]; ring

lemma sum_range_cast_id (h : ℕ) : 2 * ∑ j ∈ range h, (j : ℤ) = (h : ℤ) * (h - 1) := by
  induction h with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

lemma sum_range_real_id (h : ℕ) : 2 * ∑ j ∈ range h, (j : ℝ) = (h : ℝ) * (h - 1) := by
  induction h with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

lemma sum_fin_eq_range (h : ℕ) (f : ℕ → ℤ) : ∑ j : Fin h, f j = ∑ j ∈ range h, f j :=
  Fin.sum_univ_eq_sum_range f h

/-- The potentials, summed. -/
lemma SM_eq (h : ℕ) :
    SM h = ∑ j ∈ range h, ((4 * (j : ℤ) + 2 * bet h) + max 0 (((h / 4 : ℕ) : ℤ) - j) +
        max 0 ((gam h - bet h) - j)) + ∑ n ∈ range h, 2 * max 0 (-bet h - n) := by
  unfold SM
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rP, cP]
  rw [sum_fin_eq_range h (fun j => max ((j : ℤ) + alp h) (2 * (j : ℤ) + bet h)),
    sum_fin_eq_range h (fun n => max (2 * (n : ℤ) + bet h) (n : ℤ)),
    sum_fin_eq_range h (fun n => -2 * (n : ℤ) - bet h),
    sum_fin_eq_range h (fun j => max ((j : ℤ) + gam h) (2 * (j : ℤ) + bet h))]
  have hab : alp h - bet h = ((h / 4 : ℕ) : ℤ) := by unfold bet; ring
  simp only [← sum_add_distrib]
  refine sum_congr rfl (fun j _ => ?_)
  rw [max_eq_add_pos ((j : ℤ) + alp h), max_eq_add_pos ((j : ℤ) + gam h), max_comm (2 * (j : ℤ) + bet h) (j : ℤ),
    max_eq_add_pos (j : ℤ)]
  rw [show (j : ℤ) + alp h - (2 * j + bet h) = ((h / 4 : ℕ) : ℤ) - j by rw [← hab]; ring,
    show (j : ℤ) + gam h - (2 * j + bet h) = gam h - bet h - j by ring,
    show (j : ℤ) - (2 * j + bet h) = -bet h - j by ring]
  ring

/-- `2 SM(h) ≤ 4h(h−1) + 4hβ + P(P+1) + P′(P′+1) + 2Q(Q+1)` with `Q = −β`, `P = ⌊h/4⌋`, `P′ = γ − β`. -/
lemma two_SM_le (h : ℕ) :
    2 * SM h ≤ 4 * ((h : ℤ) * (h - 1)) + 4 * h * bet h +
      ((h / 4 : ℕ) : ℤ) * ((h / 4 : ℕ) + 1) + (gam h - bet h) * (gam h - bet h + 1) +
      2 * (-bet h) * (-bet h + 1) := by
  have hP' : 0 ≤ gam h - bet h := by
    unfold gam bet alp; have := Nat.div_add_mod h 2; have := Nat.mod_lt h (by norm_num : 0 < 2); omega
  have hQ : 0 ≤ -bet h := by unfold bet alp; omega
  have s1 := sum_pos_part_le (((h / 4 : ℕ) : ℤ)) (by positivity) h
  have s2 := sum_pos_part_le (gam h - bet h) hP' h
  have s3 := sum_pos_part_le (-bet h) hQ h
  have s0 := sum_range_cast_id h
  rw [SM_eq, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, card_range, ← mul_sum]
  simp only [nsmul_eq_mul, ← mul_sum] at *
  nlinarith

theorem eventually_n2M_le : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    (n2M h : ℝ) * Real.log 2 ≤ (Real.log 2 / 8 + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [eventually_rem_le ε hε, eventually_ge_atTop 1] with h hrem hh
  set H : ℝ := (h : ℝ) with hH
  have hH1 : 1 ≤ H := by rw [hH]; exact_mod_cast hh
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log H := by
    have hp := Nat.pow_log_le_self 2 (by omega : h ≠ 0)
    have : ((2 : ℝ) ^ Nat.log 2 h) ≤ H := by rw [hH]; exact_mod_cast hp
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) this
  -- the potentials: `2 SM ≤ 9h²/4 + 13`
  have hSM : 2 * (SM h : ℝ) ≤ 9 / 4 * H ^ 2 + 13 := by
    have h1 := two_SM_le h
    have ha := Nat.div_add_mod h 2
    have ha' := Nat.mod_lt h (by norm_num : 0 < 2)
    have hb := Nat.div_add_mod h 4
    have hb' := Nat.mod_lt h (by norm_num : 0 < 4)
    unfold gam bet alp at h1
    set a : ℕ := h / 2
    set b : ℕ := h / 4
    have hA1 : (2 * (a : ℝ)) ≤ H := by rw [hH]; exact_mod_cast (show 2 * a ≤ h by omega)
    have hA2 : H ≤ 2 * (a : ℝ) + 1 := by rw [hH]; exact_mod_cast (show h ≤ 2 * a + 1 by omega)
    have hB1 : (4 * (b : ℝ)) ≤ H := by rw [hH]; exact_mod_cast (show 4 * b ≤ h by omega)
    have hB2 : H ≤ 4 * (b : ℝ) + 3 := by rw [hH]; exact_mod_cast (show h ≤ 4 * b + 3 by omega)
    have h1r : 2 * (SM h : ℝ) ≤ 4 * (H * (H - 1)) + 4 * H * (-(a : ℝ) - b) + b * (b + 1) +
        (2 - H + a - (-(a : ℝ) - b)) * (2 - H + a - (-(a : ℝ) - b) + 1) +
        2 * (-(-(a : ℝ) - b)) * (-(-(a : ℝ) - b) + 1) := by
      rw [hH]; exact_mod_cast h1
    nlinarith [mul_nonneg (sub_nonneg.2 hA1) (sub_nonneg.2 hA2), mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 hB2),
      mul_nonneg (sub_nonneg.2 hA1) (sub_nonneg.2 hB1), mul_nonneg (sub_nonneg.2 hA2) (sub_nonneg.2 hB2),
      mul_nonneg (sub_nonneg.2 hA1) (sub_nonneg.2 hB2), mul_nonneg (sub_nonneg.2 hA2) (sub_nonneg.2 hB1)]
  -- `Σ v₂(i!) ≥ h(h−1)/2 − h(log₂ h + 1)`
  have hvf : (H * (H - 1) / 2 - H * ((Nat.log 2 h : ℝ) + 1)) ≤ ((∑ i ∈ range h, (vf i : ℤ) : ℤ) : ℝ) := by
    have key : ∀ i ∈ range h, (i : ℝ) - ((Nat.log 2 h : ℝ) + 1) ≤ (vf i : ℝ) := by
      intro i hi
      have := vf_ge i
      have hl : Nat.log 2 i ≤ Nat.log 2 h := Nat.log_mono_right (mem_range.1 hi).le
      have : (i : ℝ) ≤ vf i + Nat.log 2 i + 1 := by exact_mod_cast this
      have : (Nat.log 2 i : ℝ) ≤ Nat.log 2 h := by exact_mod_cast hl
      linarith
    have hsum := sum_le_sum key
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
    have hg : (∑ i ∈ range h, (i : ℝ)) = H * (H - 1) / 2 := by
      have := sum_range_real_id h
      rw [← hH] at this
      linarith
    push_cast
    rw [hg] at hsum
    linarith
  have e2 : H * ((Nat.log 2 h : ℝ) * Real.log 2) ≤ H * Real.log H :=
    mul_le_mul_of_nonneg_left hL (by linarith)
  have e3 : H * Real.log 2 ≤ H := mul_le_of_le_one_right (by linarith) hl2'
  have hn : (n2M h : ℝ) ≤ H ^ 2 / 8 + 7 + 3 * H + 2 * H * (Nat.log 2 h : ℝ) := by
    unfold n2M; push_cast; push_cast at hvf; linarith
  have hn' := mul_le_mul_of_nonneg_right hn hl2.le
  have e4 : 7 * Real.log 2 ≤ 7 * H := by nlinarith
  nlinarith

/-- **Lemma M** (the ingredient for `TiQ.theoremT5`): at odd `q ≥ 3` the 2-adic constant is `⅛ log 2`. -/
theorem twoAdic_odd_M_proof (q : ℕ) (hq : 3 ≤ q) (ho : Odd q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((DeltaT q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (Real.log 2 / 8 + ε) * (h : ℝ) ^ 2 :=
  ⟨n2M, fun h k => twoAdic_DeltaT_M hq ho h k, eventually_n2M_le⟩

end M
end TiQ
end Chi2Irr
