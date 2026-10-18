/-
# Gauss norms on the free ring and the change of basis

* `GLe p B f` (`f ∈ FR = ℚ[q, E]`): every coefficient has `‖·‖_p ≤ B`; closed under `+`, `·`, sums, products;
  `GLeX p B F` for `F ∈ FR[X]` (coefficientwise). `GLe_ev`: specializing `q, E` to `p`-integral rationals
  does not increase the norm.
* `det_GLeX`: a matrix over `FR[X]` with `‖M_ij‖ ≤ ρ_i κ_j` has `‖det M‖ ≤ ∏ρ ∏κ` (Leibniz).
* `LamF K g = A(g) + X B(g) ∈ FR[X]` is `ℚ`-linear in `g`; for a family `e_i` of degree `< h` with coefficient
  matrix `Ce`, the Gram matrix `GramF e = (Λ_X(e_i e_j))` satisfies `det GramF e = (det Ce)² Δ^F_h`.
* `det_Ce_mul_det_V`: if the evaluation matrix `e_m(x_k)` is lower triangular with diagonal `D′(x_m)`, then
  `det Ce · det V = ∏_m D′(x_m)` (`V_{dk} = x_k^d`).
-/
import Chi2Irrational.Arith.Free
import Chi2Irrational.NonVan.Gram

namespace Chi2Irr

open Polynomial Finset

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Gauss norms on `FR` -/

/-- `‖f‖_p ≤ B` for `f ∈ ℚ[q, E]`. -/
def GLe (B : ℚ) (f : FR) : Prop := ∀ m, padicNorm p (f.coeff m) ≤ B

variable {p}

lemma GLe_mono {B B' : ℚ} (h : B ≤ B') {f : FR} (hf : GLe p B f) : GLe p B' f := fun m => (hf m).trans h

lemma GLe_zero {B : ℚ} (hB : 0 ≤ B) : GLe p B 0 := fun m => by simp [hB]

lemma GLe_add {B : ℚ} {f g : FR} (hf : GLe p B f) (hg : GLe p B g) : GLe p B (f + g) := fun m => by
  rw [MvPolynomial.coeff_add]
  exact (padicNorm.nonarchimedean (p := p)).trans (max_le (hf m) (hg m))

lemma GLe_neg {B : ℚ} {f : FR} (hf : GLe p B f) : GLe p B (-f) := fun m => by
  rw [MvPolynomial.coeff_neg, padicNorm.neg]; exact hf m

lemma GLe_sub {B : ℚ} {f g : FR} (hf : GLe p B f) (hg : GLe p B g) : GLe p B (f - g) := by
  rw [sub_eq_add_neg]; exact GLe_add hf (GLe_neg hg)

lemma GLe_sum {ι : Type*} (s : Finset ι) {B : ℚ} (hB : 0 ≤ B) (f : ι → FR) (h : ∀ i ∈ s, GLe p B (f i)) :
    GLe p B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GLe_zero hB
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact GLe_add (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma GLe_mul {B C : ℚ} (hB : 0 ≤ B) (hC : 0 ≤ C) {f g : FR} (hf : GLe p B f) (hg : GLe p C g) :
    GLe p (B * C) (f * g) := fun m => by
  rw [MvPolynomial.coeff_mul]
  refine padicNorm.sum_le' (fun x _ => ?_) (by positivity)
  rw [padicNorm.mul]
  exact mul_le_mul (hf _) (hg _) (padicNorm.nonneg _) hB

lemma GLe_C (r : ℚ) : GLe p (padicNorm p r) (MvPolynomial.C r) := fun m => by
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact le_rfl
  · rw [padicNorm.zero]; exact padicNorm.nonneg _

lemma GLe_C_mul {B : ℚ} (hB : 0 ≤ B) (r : ℚ) {f : FR} (hf : GLe p B f) :
    GLe p (padicNorm p r * B) (MvPolynomial.C r * f) :=
  GLe_mul (padicNorm.nonneg _) hB (GLe_C r) hf

lemma GLe_one : GLe p 1 (1 : FR) := by simpa using GLe_C (p := p) 1

lemma GLe_X (i : Fin 2) : GLe p 1 (MvPolynomial.X i : FR) := fun m => by
  rw [MvPolynomial.coeff_X]
  split_ifs <;> simp

lemma GLe_pow {B : ℚ} (hB : 0 ≤ B) {f : FR} (hf : GLe p B f) (n : ℕ) : GLe p (B ^ n) (f ^ n) := by
  induction n with
  | zero => simpa using GLe_one
  | succ n ih => rw [pow_succ, pow_succ]; exact GLe_mul (by positivity) hB ih hf

lemma GLe_qF : GLe p 1 qF := GLe_X 0

lemma GLe_EF : GLe p 1 EF := GLe_X 1

lemma GLe_OmegaF (b : ℕ) : GLe p 1 (OmegaF b) := by
  unfold OmegaF
  split_ifs
  · exact GLe_EF
  · have h1 := GLe_pow (p := p) zero_le_one GLe_qF 2
    have h2 := GLe_pow (p := p) zero_le_one GLe_EF (b + 1)
    rw [one_pow] at h1 h2
    simpa using GLe_mul zero_le_one zero_le_one h1 h2

/-- Specialization does not increase the norm. -/
lemma GLe_ev {B : ℚ} {f : FR} (hf : GLe p B f) (hB : 0 ≤ B) (v : Fin 2 → ℚ) (hv : ∀ i, padicNorm p (v i) ≤ 1) :
    padicNorm p (MvPolynomial.aeval v f) ≤ B := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine padicNorm.sum_le' (fun m _ => ?_) hB
  rw [padicNorm.mul]
  have hprod : padicNorm p (∏ i ∈ m.support, v i ^ m i) ≤ 1 := by
    refine Finset.prod_induction _ (fun x => padicNorm p x ≤ 1) (fun a b ha hb => ?_) (by simp) (fun i _ => ?_)
    · rw [padicNorm.mul]; exact mul_le_one₀ ha (padicNorm.nonneg _) hb
    · induction m i with
      | zero => simp
      | succ n ih => rw [pow_succ, padicNorm.mul]; exact mul_le_one₀ ih (padicNorm.nonneg _) (hv i)
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  calc padicNorm p (f.coeff m) * padicNorm p (∏ i ∈ m.support, v i ^ m i) ≤ B * 1 :=
        mul_le_mul (hf m) hprod (padicNorm.nonneg _) hB
    _ = B := mul_one B


/-! ### Norms on `FR[X]` -/

variable (p) in
/-- `‖F‖_p ≤ B` for `F ∈ FR[X]` (all coefficients of all coefficients). -/
def GLeX (B : ℚ) (F : FR[X]) : Prop := ∀ k, GLe p B (F.coeff k)

lemma GLeX_zero {B : ℚ} (hB : 0 ≤ B) : GLeX p B 0 := fun k => by simpa using GLe_zero hB

lemma GLeX_add {B : ℚ} {F G : FR[X]} (hF : GLeX p B F) (hG : GLeX p B G) : GLeX p B (F + G) :=
  fun k => by rw [coeff_add]; exact GLe_add (hF k) (hG k)

lemma GLeX_neg {B : ℚ} {F : FR[X]} (hF : GLeX p B F) : GLeX p B (-F) :=
  fun k => by rw [coeff_neg]; exact GLe_neg (hF k)

lemma GLeX_sum {ι : Type*} (s : Finset ι) {B : ℚ} (hB : 0 ≤ B) (F : ι → FR[X]) (h : ∀ i ∈ s, GLeX p B (F i)) :
    GLeX p B (∑ i ∈ s, F i) := fun k => by
  rw [finset_sum_coeff]; exact GLe_sum s hB _ (fun i hi => h i hi k)

lemma GLeX_mul {B C : ℚ} (hB : 0 ≤ B) (hC : 0 ≤ C) {F G : FR[X]} (hF : GLeX p B F) (hG : GLeX p C G) :
    GLeX p (B * C) (F * G) := fun k => by
  rw [coeff_mul]
  exact GLe_sum _ (by positivity) _ (fun x _ => GLe_mul hB hC (hF _) (hG _))

lemma GLeX_C {B : ℚ} (hB : 0 ≤ B) {a : FR} (ha : GLe p B a) : GLeX p B (C a) := fun k => by
  rw [coeff_C]; split_ifs
  · exact ha
  · exact GLe_zero hB

lemma GLeX_X_mul {B : ℚ} {F : FR[X]} (hB : 0 ≤ B) (hF : GLeX p B F) : GLeX p B (X * F) := fun k => by
  cases k with
  | zero => rw [coeff_X_mul_zero]; exact GLe_zero hB
  | succ k => rw [coeff_X_mul]; exact hF k

lemma GLeX_mono {B B' : ℚ} (h : B ≤ B') {F : FR[X]} (hF : GLeX p B F) : GLeX p B' F :=
  fun k => GLe_mono h (hF k)

lemma GLeX_one : GLeX p 1 (1 : FR[X]) := by simpa using GLeX_C (p := p) zero_le_one GLe_one

lemma GLeX_prod {ι : Type*} (s : Finset ι) (B : ι → ℚ) (hB : ∀ i, 0 ≤ B i) (F : ι → FR[X])
    (h : ∀ i ∈ s, GLeX p (B i) (F i)) : GLeX p (∏ i ∈ s, B i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GLeX_one
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact GLeX_mul (hB a) (prod_nonneg (fun i _ => hB i)) (h a (mem_insert_self a s))
      (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- **Leibniz bound.** -/
theorem det_GLeX {n : ℕ} (M : Matrix (Fin n) (Fin n) FR[X]) (ρ κ : Fin n → ℚ) (hρ : ∀ i, 0 ≤ ρ i)
    (hκ : ∀ i, 0 ≤ κ i) (h : ∀ i j, GLeX p (ρ i * κ j) (M i j)) :
    GLeX p ((∏ i, ρ i) * ∏ i, κ i) M.det := by
  have h0 : 0 ≤ (∏ i, ρ i) * ∏ i, κ i := mul_nonneg (prod_nonneg (fun i _ => hρ i)) (prod_nonneg (fun i _ => hκ i))
  rw [Matrix.det_apply]
  refine GLeX_sum _ h0 _ (fun σ _ => ?_)
  have hprod : GLeX p ((∏ i, ρ i) * ∏ i, κ i) (∏ i, M (σ i) i) := by
    have := GLeX_prod univ (fun i => ρ (σ i) * κ i) (fun i => mul_nonneg (hρ _) (hκ _)) (fun i => M (σ i) i)
      (fun i _ => h (σ i) i)
    rwa [prod_mul_distrib, Equiv.prod_comp σ ρ] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact GLeX_neg hprod

/-! ### Linearity of `Λ_X` and the change of basis -/

/-- `Λ_X(g) = A(g) + X B(g)`. -/
noncomputable def LamF (K : ℕ) (g : ℚ[X]) : FR[X] := C (AfunF K g) + X * C (BfunF K g)

lemma muF_add (R S : ℚ[X]) : muF (R + S) = muF R + muF S := by simp [muF, map_add]

lemma muF_smul (c : ℚ) (R : ℚ[X]) : muF (c • R) = c • muF R := by simp [muF, map_smul]

lemma AfunF_add (K : ℕ) (g g' : ℚ[X]) : AfunF K (g + g') = AfunF K g + AfunF K g' := by
  unfold AfunF
  rw [add_mul, ← divByMonicHom_apply, map_add, divByMonicHom_apply, divByMonicHom_apply, muF_add]
  simp only [eval_add, add_mul, map_add, sum_add_distrib, mul_add]
  ring

lemma AfunF_smul (K : ℕ) (c : ℚ) (g : ℚ[X]) : AfunF K (c • g) = c • AfunF K g := by
  unfold AfunF
  rw [smul_mul_assoc, ← divByMonicHom_apply, map_smul, divByMonicHom_apply, muF_smul]
  simp only [eval_smul, smul_eq_mul, smul_add, mul_sum, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, map_mul]
  ring_nf

lemma BfunF_add (K : ℕ) (g g' : ℚ[X]) : BfunF K (g + g') = BfunF K g + BfunF K g' := by
  unfold BfunF
  simp only [eval_add, add_mul, map_add, sum_add_distrib, mul_add]

lemma BfunF_smul (K : ℕ) (c : ℚ) (g : ℚ[X]) : BfunF K (c • g) = c • BfunF K g := by
  unfold BfunF
  rw [MvPolynomial.smul_eq_C_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl (fun k _ => ?_)
  simp only [eval_smul, smul_eq_mul, map_mul]
  ring

/-- `Λ_X` as a `ℚ`-linear map. -/
noncomputable def LamLinF (K : ℕ) : ℚ[X] →ₗ[ℚ] FR[X] where
  toFun := LamF K
  map_add' g g' := by unfold LamF; rw [AfunF_add, BfunF_add]; simp only [map_add]; ring
  map_smul' c g := by
    unfold LamF
    rw [AfunF_smul, BfunF_smul, RingHom.id_apply]
    simp only [Algebra.smul_def, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]
    ring

/-- The Gram matrix of a family `e`. -/
noncomputable def GramF (h : ℕ) (e : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) FR[X] :=
  fun i j => LamF h (e i * e j)

/-- The coefficient matrix of a family `e`. -/
noncomputable def CoefM {h : ℕ} (e : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℚ := fun i d => (e i).coeff d

/-- The monomial Gram matrix. -/
noncomputable def HF (h : ℕ) : Matrix (Fin h) (Fin h) FR[X] := (X : FR[X]) • (BmatF h).map C + (AmatF h).map C

lemma HF_apply (h : ℕ) (d e : Fin h) : HF h d e = LamF h (X ^ ((d : ℕ) + e)) := by
  simp [HF, LamF, AmatF, BmatF, Matrix.add_apply, Matrix.smul_apply]; ring

lemma GramF_eq {h : ℕ} (e : Fin h → ℚ[X]) (he : ∀ i, (e i).natDegree < h) :
    GramF h e = (CoefM e).map (algebraMap ℚ FR[X]) * HF h * ((CoefM e).map (algebraMap ℚ FR[X])).transpose := by
  refine Matrix.ext fun i j => ?_
  have expand : ∀ k : Fin h, e k = ∑ d : Fin h, (CoefM e k d) • X ^ (d : ℕ) := by
    intro k
    simp_rw [smul_eq_C_mul]
    show e k = ∑ d : Fin h, C ((e k).coeff d) * X ^ (d : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun d => C ((e k).coeff d) * X ^ d) h]
    exact as_sum_range_C_mul_X_pow' _ (he k)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, HF_apply]
  unfold GramF
  rw [expand i, expand j, sum_mul_sum]
  show LamLinF h _ = _
  simp only [map_sum]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl (fun d' _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  rw [smul_mul_smul_comm, ← pow_add, map_smul]
  show (CoefM e i d * CoefM e j d') • LamF h _ = _
  rw [Algebra.smul_def]
  simp only [map_mul]
  ring

theorem det_GramF {h : ℕ} (e : Fin h → ℚ[X]) (he : ∀ i, (e i).natDegree < h) :
    (GramF h e).det = algebraMap ℚ FR[X] ((CoefM e).det) ^ 2 * DeltaF h := by
  have hC : ((CoefM e).map (algebraMap ℚ FR[X])).det = algebraMap ℚ FR[X] (CoefM e).det :=
    (RingHom.map_det (algebraMap ℚ FR[X]) (CoefM e)).symm
  rw [GramF_eq e he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hC]
  show _ * (HF h).det * _ = _ * DeltaF h
  unfold DeltaF HF
  ring


/-! ### The coefficient determinant -/

lemma padicNorm_prod' {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

lemma dPrime_fin (h : ℕ) (m : Fin h) :
    dPrime h m = ∏ k ∈ univ.erase m, (pole m - pole k) := by
  unfold dPrime
  rw [← Finset.filter_ne', Finset.prod_filter, ← Finset.filter_ne', Finset.prod_filter]
  rw [← Fin.prod_univ_eq_prod_range (fun k => if k ≠ (m : ℕ) then pole m - pole k else 1) h]
  refine prod_congr rfl (fun k _ => ?_)
  simp only [ne_eq, Fin.val_inj]

lemma prod_erase_swap {h : ℕ} {M : Type*} [CommMonoid M] (g : Fin h → Fin h → M) :
    ∏ m, ∏ k ∈ univ.erase m, g m k = ∏ m, ∏ k ∈ Ioi m, (g m k * g k m) := by
  have hsplit : ∀ m : Fin h, univ.erase m = Iio m ∪ Ioi m := fun m => by
    ext k; simp only [mem_erase, mem_univ, and_true, mem_union, mem_Iio, mem_Ioi]; omega
  have hdisj : ∀ m : Fin h, Disjoint (Iio m) (Ioi m) := fun m => by
    rw [Finset.disjoint_left]; intro k h1 h2; simp only [mem_Iio, mem_Ioi] at h1 h2; omega
  simp_rw [hsplit, prod_union (hdisj _), prod_mul_distrib]
  rw [mul_comm]
  congr 1
  exact Finset.prod_comm' (fun m k => by simp only [mem_univ, mem_Iio, mem_Ioi, true_and, and_true])

/-- **The coefficient determinant** of a family with triangular evaluation matrix. -/
theorem padicNorm_det_CoefM_sq {h : ℕ} (e : Fin h → ℚ[X]) (he : ∀ i, (e i).natDegree < h)
    (hlow : ∀ m k : Fin h, m < k → (e m).eval (pole k) = 0) (hdiag : ∀ m : Fin h, (e m).eval (pole m) = dPrime h m) :
    padicNorm p (CoefM e).det ^ 2 = ∏ m : Fin h, padicNorm p (dPrime h m) := by
  set v : Fin h → ℚ := fun k => pole k
  set V := Matrix.vandermonde v
  -- the evaluation matrix
  have hE : CoefM e * V.transpose = Matrix.of (fun (m k : Fin h) => (e m).eval (pole k)) := by
    refine Matrix.ext fun m k => ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply, Matrix.of_apply, CoefM, V, v]
    rw [eval_eq_sum_range' (he m), ← Fin.sum_univ_eq_sum_range (fun d => (e m).coeff d * pole k ^ d) h]
  have hdetE : (CoefM e).det * V.det = ∏ m : Fin h, dPrime h m := by
    rw [← Matrix.det_transpose V, ← Matrix.det_mul, hE, Matrix.det_of_lowerTriangular]
    · exact prod_congr rfl (fun m _ => by simp [hdiag])
    · intro m k hmk
      exact hlow m k hmk
  -- `∏ D′ = ± (det V)²`
  have hV : ∏ m : Fin h, padicNorm p (dPrime h m) = padicNorm p V.det ^ 2 := by
    rw [Matrix.det_vandermonde, padicNorm_prod', sq, ← prod_mul_distrib]
    simp_rw [dPrime_fin, padicNorm_prod']
    rw [prod_erase_swap (fun m k => padicNorm p (pole m - pole k))]
    refine prod_congr rfl (fun m _ => ?_)
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun k _ => ?_)
    simp only [v]
    rw [← padicNorm.neg (pole ↑m - pole ↑k), neg_sub]
  have hV0 : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    refine prod_ne_zero_iff.mpr (fun m _ => prod_ne_zero_iff.mpr (fun k hk => ?_))
    exact pole_sub_ne_zero (by have := mem_Ioi.mp hk; omega)
  have hn := congrArg (padicNorm p) hdetE
  rw [padicNorm.mul, padicNorm_prod'] at hn
  have hVpos : 0 < padicNorm p V.det := lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hV0).symm
  rw [hV] at hn
  have : padicNorm p (CoefM e).det = padicNorm p V.det := by
    have := hn; field_simp at this; nlinarith [padicNorm.nonneg (p := p) (CoefM e).det]
  rw [this, hV]

end Chi2Irr
