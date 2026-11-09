/-
# Lemma 10₀: the 2-adic bound at even `q` (`pilot_q/RESULT.md` §4.1)

`twoAdic_even_proof`: for even `q ≥ 3`, every coefficient of `Δ_h = Delta q h` has
`‖·‖₂ ≤ 2^{E(h) − v₂(q)·aQ(h)}`, `E(h) = 4 Σ_{a<h} rPot h a = 2⌊h/2⌋(⌊h/2⌋ + 1) ≤ h²/2 + h`, so the limit constant is
`(½ − v₂(q)/3) log 2 = c2Even q`.

Proof (RESULT §4.1, steps (i) and (ii)):
* (ii) Gauss bound over the free ring `FR = ℚ[q, E]` (`GLeX_DeltaF_two`): in the anchored basis `a_i`, `b_j`
  (`TwoAdicEntries.lean`) the Gram matrix over `FR[X]` has determinant `Δ^F_h` (`DeltaF_eq_anchored`). Its entries have
  Gauss norm `‖·‖₂ ≤ 2^{|i+j+1−h|}`: (L) `i + j ≥ h`: `B = 0`, `A = μ(P X)` with `v₂(coeff_d(P X)) ≥ d − π`, and every
  `μ(u^d)` is an integer combination of the `Ω_b` (Gauss norm 1); (U) `i + j < h`: the polynomial part vanishes and each
  residue weight is `x_k/((−1)^l l! (N−l)!)`, `v₂ ≥ −1 − N`, against the factor `4`. Leibniz with row/column weights
  `rPot h i + rPot h (h−1−i)` gives `2^{E(h)}`. This is cruder than RESULT's `⌊h²/2⌋ − h` by `O(h)` only.
* (i) Clearing `E` and the `q`-adic divisibility (Lemma 4′(i), `qdeg_clearE_DeltaF`) are used through
  `padicNorm_Delta_clear` (`Arith/Special.lean`), which holds for every `q₀ ≥ 2`; at even `q₀`, `q₀² − 1` is odd, so
  `‖Δ coefficient‖₂ ≤ 2^{E(h)} · ‖q₀‖₂^{aQ h}`.
-/
import Chi2Irrational.Q.Defs
import Chi2Irrational.Arith.Special

namespace Chi2Irr
namespace Q

open Polynomial Finset Filter
open scoped Nat

/-! ### The anchored Gram identity over `FR` -/

theorem Gram2F_eq {h : ℕ} (a b : Fin h → ℚ[X]) (ha : ∀ i, (a i).natDegree < h)
    (hb : ∀ i, (b i).natDegree < h) :
    Matrix.of (fun i j => LamF h (a i * b j)) =
      (CoefM a).map (algebraMap ℚ FR[X]) * HF h * ((CoefM b).map (algebraMap ℚ FR[X])).transpose := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, HF_apply]
  rw [expand_fin a ha i, expand_fin b hb j, sum_mul_sum]
  change LamLinF h _ = _
  simp only [map_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  have : C (CoefM a i d) * X ^ (d : ℕ) * (C (CoefM b j e) * X ^ (e : ℕ)) =
      (CoefM a i d * CoefM b j e) • X ^ ((d : ℕ) + e) := by
    rw [smul_eq_C_mul, C_mul, pow_add]; ring
  rw [this, map_smul]
  change (CoefM a i d * CoefM b j e) • LamF h _ = _
  rw [Algebra.smul_def]
  simp only [map_mul]
  ring

/-- `Δ^F_h` is the determinant of the anchored Gram matrix over `FR[X]`. -/
theorem DeltaF_eq_anchored (h : ℕ) :
    DeltaF h = (Matrix.of (fun i j : Fin h => LamF h (aB i * bB h j))).det := by
  have hda : ∀ i : Fin h, (aB i).natDegree = i := fun i => by
    unfold aB; rw [natDegree_prod_pole, card_range]
  have hdb : ∀ j : Fin h, (bB h j).natDegree = j := fun j => by
    unfold bB; rw [natDegree_prod_pole, Nat.card_Ico]; have := j.isLt; omega
  have hC : ∀ M : Matrix (Fin h) (Fin h) ℚ,
      (M.map (algebraMap ℚ FR[X])).det = algebraMap ℚ FR[X] M.det := fun M =>
    (RingHom.map_det (algebraMap ℚ FR[X]) M).symm
  rw [Gram2F_eq (fun i => aB i) (fun j => bB h j) (fun i => by rw [hda]; exact i.isLt)
    (fun j => by rw [hdb]; exact j.isLt), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hC, hC,
    det_CoefM_monic _ hda (fun i => monic_prod_pole _), det_CoefM_monic _ hdb (fun j => monic_prod_pole _),
    map_one, one_mul, mul_one]
  rfl

/-! ### Gauss bounds for the pieces -/

lemma GLe_SpartF (k : ℕ) : GLe 2 1 (SpartF k) := by
  unfold SpartF
  refine GLe_sum _ zero_le_one _ (fun j _ => ?_)
  have h1 := GLe_pow (p := 2) zero_le_one GLe_qF (2 * (k - j))
  rw [one_pow] at h1
  have h2 : padicNorm 2 (1 / (2 * (j : ℚ) + 1) ^ 2) ≤ 1 := by
    have e : (2 * (j : ℚ) + 1) ^ 2 = (((2 * j + 1) ^ 2 : ℕ) : ℚ) := by push_cast; ring
    rw [e]
    have := V2_inv_odd (Odd.pow (odd_two_mul_add_one j) (n := 2))
    unfold V2 at this; simpa using this
  simpa using GLe_mul zero_le_one zero_le_one h1 (GLe_mono h2 (GLe_C _))

lemma GLe_qpow (n : ℕ) : GLe 2 1 (qF ^ n) := by
  have := GLe_pow (p := 2) zero_le_one GLe_qF n
  rwa [one_pow] at this

lemma GLe_muMonoF (d : ℕ) : GLe 2 1 (muMonoF d) := by
  unfold muMonoF
  refine GLe_sum _ zero_le_one _ (fun b _ => ?_)
  have hc : padicNorm 2 ((d : ℚ) * (dCoef (d - 1) b : ℚ)) ≤ 1 := by
    have e : ((d : ℚ) * (dCoef (d - 1) b : ℚ)) = (((d : ℤ) * dCoef (d - 1) b : ℤ) : ℚ) := by push_cast; ring
    rw [e]; exact padicNorm.of_int _
  simpa using GLe_mul zero_le_one zero_le_one (GLe_mono hc (GLe_C _)) (GLe_OmegaF b)

/-- `μ` of a `2`-integrally scaled polynomial `R = 2^{−n} H(2X)`: Gauss norm `≤ 2^n`. -/
lemma GLe_muF {n : ℕ} {R : ℚ[X]} (hR : IS n R) : GLe 2 ((2 : ℚ) ^ n) (muF R) := by
  rw [muF_eq_sum, Polynomial.sum_def]
  refine GLe_sum _ (by positivity) _ (fun d _ => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  have hc : padicNorm 2 (R.coeff d) ≤ (2 : ℚ) ^ n := by
    have := (hR d).1
    unfold V2 at this
    refine this.trans ?_
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  simpa using GLe_mul (by positivity) zero_le_one (GLe_mono hc (GLe_C _)) (GLe_muMonoF d)

/-! ### Case (L): `i + j ≥ h` -/

lemma AfunF_L {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    AfunF K (aB i * bB K j) = muF ((∏ m ∈ Ico (K - j) i, (X - C (pole m))) * X) := by
  have hz : ∑ k ∈ range K, MvPolynomial.C ((Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) *
      omega K k) * SpartF k = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; simp
  unfold AfunF
  rw [aB_mul_bB_L hi hj hij, mul_assoc, mul_divByMonic_cancel_left _ (Dpoly_monic K), hz, mul_zero, add_zero]

lemma BfunF_L {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    BfunF K (aB i * bB K j) = 0 := by
  have hz : ∑ k ∈ range K, MvPolynomial.C ((Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) *
      omega K k) * qF ^ (2 * k + 1) = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; simp
  unfold BfunF
  rw [aB_mul_bB_L hi hj hij, hz, mul_zero]

lemma GLe_A_L {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    GLe 2 ((2 : ℚ) ^ (i + j + 1 - K)) (AfunF K (aB i * bB K j)) := by
  rw [AfunF_L hi hj hij]
  have := IS_mul (IS_prod (Ico (K - j) i)) IS_X
  rw [Nat.card_Ico, show i - (K - j) + 1 = i + j + 1 - K by omega] at this
  exact GLe_muF this

/-! ### Case (U): `i + j < h` -/

lemma muF_U {K i j : ℕ} (hij : i + j < K) : muF ((aB i * bB K j * X) /ₘ Dpoly K) = 0 := by
  have hdeg : ((aB i * bB K j * X) /ₘ Dpoly K).natDegree = 0 := by
    rw [natDegree_divByMonic _ (Dpoly_monic K)]
    have h1 : (aB i * bB K j * X).natDegree ≤ i + j + 1 := by
      refine (natDegree_mul_le).trans ?_
      have := natDegree_mul_le (p := aB i) (q := bB K j)
      unfold aB bB at this ⊢
      rw [natDegree_prod_pole, natDegree_prod_pole, card_range, Nat.card_Ico] at this
      rw [natDegree_X]; omega
    have h2 : (Dpoly K).natDegree = K := by unfold Dpoly; rw [natDegree_prod_pole, card_range]
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, muF_eq_sum, sum_C_index (by simp)]
  simp [muMonoF]

/-- The residue weights in case (U): `v₂ ≥ −1 − N`, `N = K − 1 − i − j`. -/
lemma V2_coef_U {K i j k : ℕ} (hij : i + j < K) (hk : k < K) :
    V2 (-(((K - 1 - i - j : ℕ) : ℤ) + 1)) ((aB i * bB K j).eval (pole k) * omega K k) := by
  by_cases hkW : k ∈ Ico i (K - j)
  · rw [eval_omega_U hij hkW]
    have hk' := mem_Ico.mp hkW
    set N := K - 1 - i - j with hN
    obtain ⟨l, rfl⟩ : ∃ l, k = i + l := ⟨k - i, by omega⟩
    have hl : l ≤ N := by omega
    rw [show K - j = i + N + 1 by omega, prod_pole_erase i N l hl]
    have hpole : V2 (-1) (pole (i + l)) := by
      rw [pole_eq_odd]
      have := V2_div_of_norm (V2_natCast (2 * (i + l) + 1)) padicNorm_two_self
      simpa using V2_neg this
    have hsign : padicNorm 2 ((-1 : ℚ) ^ l) = 1 := by
      rcases neg_one_pow_eq_or ℚ l with h1 | h1 <;> rw [h1] <;> simp
    have hy : padicNorm 2 ((-1 : ℚ) ^ l * ((l ! : ℕ) : ℚ) * (((N - l) ! : ℕ) : ℚ)) =
        (2 : ℚ) ^ (-((vf l : ℤ) + vf (N - l))) := by
      rw [padicNorm.mul, padicNorm.mul, hsign, padicNorm_factorial, padicNorm_factorial, one_mul,
        ← zpow_add₀ two_ne_zero]
      ring_nf
    refine V2_mono ?_ (V2_div_of_norm hpole hy)
    have h1 := vf_le l
    have h2 := vf_le (N - l)
    omega
  · rw [eval_U_zero hij hk hkW, zero_mul]; exact V2_zero _

lemma GLe_of_V2 {e : ℤ} {r : ℚ} (hr : V2 e r) : GLe 2 ((2 : ℚ) ^ (-e)) (MvPolynomial.C r) :=
  GLe_mono hr (GLe_C r)

lemma GLe_four : GLe 2 ((2 : ℚ) ^ (-(2 : ℤ))) (4 : FR) := by
  have := GLe_of_V2 V2_four
  rwa [map_ofNat] at this

/-- The pole part `4 Σ_k c_k Y_k` in case (U). -/
lemma GLe_pole_U {K i j : ℕ} (hij : i + j < K) (Y : ℕ → FR) (hY : ∀ k, GLe 2 1 (Y k)) :
    GLe 2 ((2 : ℚ) ^ (K - 1 - i - j))
      (4 * ∑ k ∈ range K, MvPolynomial.C ((aB i * bB K j).eval (pole k) * omega K k) * Y k) := by
  set N := K - 1 - i - j
  have hs : GLe 2 ((2 : ℚ) ^ ((N : ℤ) + 1))
      (∑ k ∈ range K, MvPolynomial.C ((aB i * bB K j).eval (pole k) * omega K k) * Y k) := by
    refine GLe_sum _ (by positivity) _ (fun k hk => ?_)
    have := GLe_mul (by positivity) zero_le_one (GLe_of_V2 (V2_coef_U hij (mem_range.mp hk))) (hY k)
    simpa using this
  have h4 := GLe_mul (by positivity) (by positivity) GLe_four hs
  refine GLe_mono ?_ h4
  rw [← zpow_add₀ two_ne_zero, ← zpow_natCast]
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

lemma GLe_A_U {K i j : ℕ} (hij : i + j < K) :
    GLe 2 ((2 : ℚ) ^ (K - 1 - i - j)) (AfunF K (aB i * bB K j)) := by
  unfold AfunF
  rw [muF_U hij, zero_add]
  exact GLe_pole_U hij _ GLe_SpartF

lemma GLe_B_U {K i j : ℕ} (hij : i + j < K) :
    GLe 2 ((2 : ℚ) ^ (K - 1 - i - j)) (BfunF K (aB i * bB K j)) := by
  unfold BfunF
  rw [neg_mul]
  exact GLe_neg (GLe_pole_U hij _ (fun k => GLe_qpow (2 * k + 1)))

/-! ### The entries and the determinant -/

/-- `|i + j + 1 − h|`. -/
def dEnt (h i j : ℕ) : ℕ := (i + j + 1 - h) + (h - (i + j + 1))

lemma GLeX_entry {h i j : ℕ} (hi : i < h) (hj : j < h) :
    GLeX 2 ((2 : ℚ) ^ dEnt h i j) (LamF h (aB i * bB h j)) := by
  have key : GLe 2 ((2 : ℚ) ^ dEnt h i j) (AfunF h (aB i * bB h j)) ∧
      GLe 2 ((2 : ℚ) ^ dEnt h i j) (BfunF h (aB i * bB h j)) := by
    unfold dEnt
    rcases Nat.lt_or_ge (i + j) h with hij | hij
    · rw [show i + j + 1 - h = 0 by omega, show h - (i + j + 1) = h - 1 - i - j by omega, zero_add]
      exact ⟨GLe_A_U hij, GLe_B_U hij⟩
    · rw [show h - (i + j + 1) = 0 by omega, add_zero, BfunF_L hi.le hj.le hij]
      exact ⟨GLe_A_L hi.le hj.le hij, GLe_zero (by positivity)⟩
  unfold LamF
  exact GLeX_add (GLeX_C (by positivity) key.1) (GLeX_X_mul (by positivity) (GLeX_C (by positivity) key.2))

/-- The row/column weight `rPot h i + rPot h (h − 1 − i)` (`= ⌈|2i + 1 − h|/2⌉`). -/
def rr (h i : ℕ) : ℕ := rPot h i + rPot h (h - 1 - i)

lemma dEnt_le {h i j : ℕ} (hi : i < h) (hj : j < h) : dEnt h i j ≤ rr h i + rr h j := by
  unfold dEnt rr rPot; omega

/-- The exponent `E(h) = 4 Σ_{a<h} rPot h a`. -/
def Ebd (h : ℕ) : ℕ := 4 * ∑ a ∈ range h, rPot h a

lemma sum_rr (h : ℕ) : ∑ i : Fin h, rr h i = 2 * ∑ a ∈ range h, rPot h a := by
  rw [Fin.sum_univ_eq_sum_range (rr h) h]
  unfold rr
  rw [sum_add_distrib, sum_range_reflect (fun a => rPot h a) h]
  ring

/-- **Step (ii)**: the Gauss bound `‖Δ^F_h‖₂ ≤ 2^{E(h)}` over `ℚ[q, E]`. -/
theorem GLeX_DeltaF_two (h : ℕ) : GLeX 2 ((2 : ℚ) ^ Ebd h) (DeltaF h) := by
  rw [DeltaF_eq_anchored]
  have hdet := det_GLeX (p := 2) (Matrix.of (fun i j : Fin h => LamF h (aB i * bB h j))) (fun i => (2 : ℚ) ^ rr h i) (fun j => (2 : ℚ) ^ rr h j)
    (fun i => by positivity) (fun j => by positivity) (fun i j => by
      refine GLeX_mono ?_ (GLeX_entry i.isLt j.isLt)
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (dEnt_le i.isLt j.isLt))
  refine GLeX_mono (le_of_eq ?_) hdet
  rw [prod_pow_eq_pow_sum, ← pow_add, sum_rr]
  unfold Ebd
  ring_nf

/-! ### Specialisation at even `q` -/

lemma not_two_dvd_qsq {q : ℕ} (hq : 2 ≤ q) (he : Even q) : ¬ 2 ∣ q ^ 2 - 1 := by
  intro hd
  have h1 : 2 ∣ q ^ 2 := (Nat.even_pow.mpr ⟨he, two_ne_zero⟩).two_dvd
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 := Nat.dvd_sub h1 hd
  rw [show q ^ 2 - (q ^ 2 - 1) = 1 by omega] at h3
  omega

/-- **Lemma 10₀** for each coefficient. -/
theorem padicNorm_Delta_even {q : ℕ} (hq : 2 ≤ q) (he : Even q) (h k : ℕ) :
    padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ ((Ebd h : ℤ) - padicValNat 2 q * aQ h) := by
  have hcl := padicNorm_Delta_clear (p := 2) (by positivity) hq h k (aQ h) (GLeX_DeltaF_two h k)
    (fun m hm => qdeg_clearE_DeltaF h k m hm)
  have hqn : padicNorm 2 (q : ℚ) = (2 : ℚ) ^ (-(padicValNat 2 q : ℤ)) := by
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast (by omega : q ≠ 0)), padicValRat.of_nat]
    norm_num
  rw [padicNorm_qsq_unit hq (not_two_dvd_qsq hq he), one_pow, one_mul, hqn] at hcl
  refine hcl.trans (le_of_eq ?_)
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by norm_num)]
  push_cast
  ring_nf

/-! ### The limit constant -/

lemma Ebd_le (h : ℕ) : 2 * Ebd h ≤ h * h + 2 * h := by
  have h1 := two_mul_sum_sub h ((h + 1) / 2)
  unfold Ebd
  unfold rPot
  set f := h - (h + 1) / 2 with hf
  have e : h + 1 - (h + 1) / 2 = f + 1 := by omega
  have hf2 : 2 * f ≤ h := by omega
  rw [e] at h1
  nlinarith

lemma aQ_ge (h : ℕ) : h * h ≤ 3 * aQ h + 7 * h + 2 := by
  unfold aQ
  have e : h * (h - 1) = h * h - h := Nat.mul_sub_one h h
  rw [e]
  have := Nat.div_add_mod (h * h - h - 6 * h) 3
  have := Nat.mod_lt (h * h - h - 6 * h) (show 3 > 0 by norm_num)
  omega

/-- **Lemma 10₀** (RESULT §4.1): the exact statement of `Q.twoAdic_even`. -/
theorem twoAdic_even_proof (q : ℕ) (hq : 3 ≤ q) (he : Even q) :
    ∃ n2 : ℕ → ℤ, (∀ h k, padicNorm 2 ((Delta q h).coeff k) ≤ (2 : ℚ) ^ (n2 h)) ∧
      ∀ ε > 0, ∀ᶠ h : ℕ in atTop, (n2 h : ℝ) * Real.log 2 ≤ (c2Even q + ε) * (h : ℝ) ^ 2 := by
  refine ⟨fun h => (Ebd h : ℤ) - padicValNat 2 q * aQ h,
    fun h k => padicNorm_Delta_even (by omega) he h k, ?_⟩
  intro ε hε
  set v : ℝ := (padicValNat 2 q : ℝ) with hv
  have hv0 : 0 ≤ v := by positivity
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 + 3 * v) / ε)
  refine eventually_atTop.2 ⟨N + 1, fun h hh => ?_⟩
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hhN : (1 + 3 * v) / ε ≤ h := by
    have : (N : ℝ) ≤ h := by exact_mod_cast (show N ≤ h by omega)
    linarith
  have hE : 2 * (Ebd h : ℝ) ≤ (h : ℝ) ^ 2 + 2 * h := by
    have := Ebd_le h
    rw [sq]; exact_mod_cast this
  have hA : (h : ℝ) ^ 2 ≤ 3 * (aQ h : ℝ) + 7 * h + 2 := by
    have := aQ_ge h
    rw [sq]; exact_mod_cast this
  -- `n₂ ≤ (½ − v/3) h² + (1 + 3v) h`
  have hn : ((Ebd h : ℤ) - (padicValNat 2 q : ℤ) * aQ h : ℤ) ≤
      ((1 / 2 - v / 3) * (h : ℝ) ^ 2 + (1 + 3 * v) * h : ℝ) := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [← hv]
    nlinarith
  have hlin : (1 + 3 * v) * (h : ℝ) ≤ ε * (h : ℝ) ^ 2 := by
    have : 1 + 3 * v ≤ ε * h := by rw [div_le_iff₀ hε] at hhN; linarith
    nlinarith
  unfold c2Even
  rw [← hv]
  calc ((((Ebd h : ℤ) - (padicValNat 2 q : ℤ) * aQ h : ℤ) : ℝ)) * Real.log 2
      ≤ ((1 / 2 - v / 3) * (h : ℝ) ^ 2 + (1 + 3 * v) * h) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hn hL0.le
    _ ≤ ((1 / 2 - v / 3) * Real.log 2 + ε) * (h : ℝ) ^ 2 := by
        have h0 : 0 ≤ (1 + 3 * v) * (h : ℝ) := by positivity
        nlinarith

end Q
end Chi2Irr
