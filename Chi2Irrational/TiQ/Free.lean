/-
# The coefficient twist: `Δ^Ti_h` from the symbolic χ₂ determinant (RESULT §2, referee fix F2)

RESULT §2: `N^Ti(q, X) = (−1)^β N^χ(iq, −iX)`, and only monomials `qⁿ Xʲ` with `n + j` even occur, so every coefficient of
the Ti determinant is `±` a coefficient of the χ₂ determinant. In the free ring `FR = ℚ[q, E]` of `Arith/Free.lean`
(`E ↔ 1/(q² − 1)`) this reads (with `E ↦ −E`, since `1/((iq)² − 1) = −1/(q² + 1)`):
* `parity_DeltaF`: every monomial `q^{m₀} E^{m₁} Xʲ` of `DeltaF h` has `m₀ + j` even (the automorphism `q ↦ −q`, `X ↦ −X`
  fixes the symbolic matrix `A + XB`: `A` is even and `B` odd in `q`);
* `DeltaFT h`: `DeltaF h` with each monomial multiplied by `tw j m = (−1)^{m₁ + j + (m₀ + j)/2}`;
* `map_DeltaFT`: `q ↦ q₀`, `E ↦ 1/(q₀² + 1)` maps `DeltaFT h` to `DeltaT q₀ h` (`TiQ/Machine.lean`).
  Proof over `ℂ`: `q ↦ i q₀`, `E ↦ −1/(q₀² + 1)` maps the symbolic entries to the Ti entries (`B` up to the factor `−i`),
  so `DeltaF h` maps to `DeltaT q₀ h (−X)`-twisted; `(−i)^j (i q₀)^{m₀} (−E₀)^{m₁} = tw j m · q₀^{m₀} E₀^{m₁}` by parity.
* Clearing `E` (Lemma 5, Lemma 4′): `clearET β f` replaces `E^b` by `(q² + 1)^{β − b}`; its coefficients are `±` those of
  `clearE β f` (`coeff_clearET_twF`, via `q ↦ iq` over `ℂ`). So Gauss norms and `q`-degrees transfer.
-/
import Chi2Irrational.TiQ.PoleSeries
import Chi2Irrational.Arith.PoleOrder

namespace Chi2Irr
namespace TiQ

open Polynomial Finset

/-! ### Scaling substitutions on `FR` -/

lemma aeval_scale_monomial {R : Type*} [CommRing R] [Algebra ℚ R] (a : Fin 2 → R) (s : Fin 2 →₀ ℕ) (c : ℚ) :
    MvPolynomial.aeval (fun i => MvPolynomial.C (a i) * MvPolynomial.X i) (MvPolynomial.monomial s c) =
      MvPolynomial.monomial s (algebraMap ℚ R c * (a 0 ^ s 0 * a 1 ^ s 1)) := by
  rw [aeval_monomial_fin2, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two,
    MvPolynomial.algebraMap_apply]
  simp only [mul_pow, map_mul, map_pow]
  ring

lemma coeff_aeval_scale {R : Type*} [CommRing R] [Algebra ℚ R] (a : Fin 2 → R) (f : FR) (m : Fin 2 →₀ ℕ) :
    (MvPolynomial.aeval (fun i => MvPolynomial.C (a i) * MvPolynomial.X i) f).coeff m =
      algebraMap ℚ R (f.coeff m) * (a 0 ^ m 0 * a 1 ^ m 1) := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp only [aeval_scale_monomial, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm]; simp

/-! ### The sign and the twist -/

/-- The sign `(−1)^{m₁ + j + (m₀ + j)/2}` of the monomial `q^{m₀} E^{m₁} Xʲ`. -/
def tw (j : ℕ) (m : Fin 2 →₀ ℕ) : ℚ := (-1) ^ (m 1 + j + (m 0 + j) / 2)

lemma tw_ne_zero (j : ℕ) (m : Fin 2 →₀ ℕ) : tw j m ≠ 0 := by unfold tw; exact pow_ne_zero _ (by norm_num)

lemma padicNorm_neg_one_pow (p : ℕ) [Fact p.Prime] (n : ℕ) : padicNorm p ((-1 : ℚ) ^ n) = 1 := by
  rcases neg_one_pow_eq_or ℚ n with h | h <;> rw [h] <;> simp

lemma padicNorm_tw_mul (p : ℕ) [Fact p.Prime] (j : ℕ) (m : Fin 2 →₀ ℕ) (x : ℚ) :
    padicNorm p (tw j m * x) = padicNorm p x := by
  rw [padicNorm.mul, tw, padicNorm_neg_one_pow, one_mul]

/-- Multiply every monomial `q^{m₀} E^{m₁}` of `f` by `tw j m`. -/
noncomputable def twF (j : ℕ) (f : FR) : FR := ∑ m ∈ f.support, MvPolynomial.monomial m (tw j m * f.coeff m)

lemma coeff_twF (j : ℕ) (f : FR) (m : Fin 2 →₀ ℕ) : (twF j f).coeff m = tw j m * f.coeff m := by
  classical
  unfold twF
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]

lemma support_twF (j : ℕ) (f : FR) : (twF j f).support = f.support := by
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, coeff_twF]
  exact ⟨fun h h0 => h (by rw [h0, mul_zero]), fun h => mul_ne_zero (tw_ne_zero j m) h⟩

lemma twF_zero (j : ℕ) : twF j 0 = 0 := by simp [twF]

lemma GLe_twF {p : ℕ} [Fact p.Prime] {B : ℚ} {f : FR} (hf : GLe p B f) (j : ℕ) : GLe p B (twF j f) :=
  fun m => by rw [coeff_twF, padicNorm_tw_mul]; exact hf m

lemma EDeg_twF {d : ℕ} {f : FR} (hf : EDeg d f) (j : ℕ) : EDeg d (twF j f) := fun m hm => by
  rw [coeff_twF] at hm
  exact hf m (right_ne_zero_of_mul hm)

/-! ### The twisted symbolic determinant -/

lemma natDegree_DeltaF_le (h : ℕ) : (DeltaF h).natDegree ≤ h := by
  have := natDegree_det_X_add_C_le (BmatF h) (AmatF h)
  simpa [DeltaF] using this

/-- `DeltaF h` with the monomial `q^{m₀} E^{m₁} Xʲ` multiplied by `tw j m`. -/
noncomputable def DeltaFT (h : ℕ) : FR[X] := ∑ j ∈ range (h + 1), C (twF j ((DeltaF h).coeff j)) * X ^ j

lemma coeff_DeltaFT (h k : ℕ) : (DeltaFT h).coeff k = twF k ((DeltaF h).coeff k) := by
  unfold DeltaFT
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · have : (DeltaF h).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_DeltaF_le h) (by simpa using hk))
    rw [this, twF_zero]

lemma GLeX_DeltaFT {p : ℕ} [Fact p.Prime] {B : ℚ} {h : ℕ} (hf : GLeX p B (DeltaF h)) : GLeX p B (DeltaFT h) :=
  fun k => by rw [coeff_DeltaFT]; exact GLe_twF (hf k) k

/-! ### Parity -/

/-- `q ↦ −q`, `E ↦ E`. -/
noncomputable def negQ : FR →ₐ[ℚ] FR :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (![(-1 : ℚ), 1] i) * MvPolynomial.X i)

lemma negQ_qF : negQ qF = -qF := by
  simp [negQ, qF]

lemma negQ_EF : negQ EF = EF := by
  simp [negQ, EF]

lemma negQ_C (r : ℚ) : negQ (MvPolynomial.C r) = MvPolynomial.C r := MvPolynomial.aeval_C _ _

lemma coeff_negQ (f : FR) (m : Fin 2 →₀ ℕ) : (negQ f).coeff m = (-1) ^ (m 0) * f.coeff m := by
  unfold negQ
  rw [coeff_aeval_scale]
  simp [mul_comm]

lemma negQ_qpow_even (n : ℕ) : negQ (qF ^ (2 * n)) = qF ^ (2 * n) := by
  rw [map_pow, negQ_qF, pow_mul, pow_mul, neg_sq]

lemma negQ_qpow_odd (n : ℕ) : negQ (qF ^ (2 * n + 1)) = -qF ^ (2 * n + 1) := by
  rw [map_pow, negQ_qF, Odd.neg_pow ⟨n, rfl⟩]

lemma negQ_OmegaF (b : ℕ) : negQ (OmegaF b) = OmegaF b := by
  unfold OmegaF
  split_ifs
  · exact negQ_EF
  · rw [map_mul, map_pow, map_pow, negQ_qF, negQ_EF, neg_sq]

lemma negQ_muMonoF (d : ℕ) : negQ (muMonoF d) = muMonoF d := by
  unfold muMonoF
  simp only [map_sum, map_mul, negQ_C, negQ_OmegaF]

lemma negQ_muF (R : ℚ[X]) : negQ (muF R) = muF R := by
  rw [muF_eq_sum, Polynomial.sum_def, map_sum]
  exact sum_congr rfl (fun d _ => by rw [map_smul, negQ_muMonoF])

lemma negQ_SpartF (k : ℕ) : negQ (SpartF k) = SpartF k := by
  unfold SpartF
  simp only [map_sum, map_mul, negQ_C, negQ_qpow_even]

lemma negQ_AfunF (K : ℕ) (g : ℚ[X]) : negQ (AfunF K g) = AfunF K g := by
  unfold AfunF
  simp only [map_add, map_mul, map_sum, negQ_muF, negQ_C, negQ_SpartF, map_ofNat]

lemma negQ_BfunF (K : ℕ) (g : ℚ[X]) : negQ (BfunF K g) = -BfunF K g := by
  unfold BfunF
  simp only [map_mul, map_sum, map_neg, negQ_C, negQ_qpow_odd, map_ofNat]
  simp only [mul_neg, Finset.sum_neg_distrib]

/-- A ring hom applied to `det(X B + A)`. -/
lemma map_det_XBA {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) :
    (((X : R[X]) • B.map C + A.map C).det).map φ = ((X : S[X]) • (B.map φ).map C + (A.map φ).map C).det := by
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply]

/-- `det(X B + A)` at `cX`. -/
lemma comp_det_XBA {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (c : R) :
    (((X : R[X]) • B.map C + A.map C).det).comp (C c * X) =
      ((X : R[X]) • (B.map (fun x => c * x)).map C + A.map C).det := by
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Polynomial.coe_compRingHom_apply, add_comp, mul_comp, X_comp, C_comp, C_mul]
  ring

lemma map_negQ_DeltaF (h : ℕ) : (DeltaF h).map negQ.toRingHom = (DeltaF h).comp (C (-1) * X) := by
  unfold DeltaF
  rw [map_det_XBA, comp_det_XBA]
  have hA : (AmatF h).map negQ.toRingHom = AmatF h := Matrix.ext fun i j => negQ_AfunF h _
  have hB : (BmatF h).map negQ.toRingHom = (BmatF h).map (fun x => -1 * x) := Matrix.ext fun i j => by
    simp only [Matrix.map_apply]
    rw [neg_one_mul]; exact negQ_BfunF h _
  rw [hA, hB]

/-- **Parity.** Every monomial `q^{m₀} E^{m₁} Xʲ` of `DeltaF h` has `m₀ + j` even. -/
theorem parity_DeltaF (h j : ℕ) (m : Fin 2 →₀ ℕ) (hm : ((DeltaF h).coeff j).coeff m ≠ 0) : Even (m 0 + j) := by
  have e := congrArg (fun F : FR[X] => (F.coeff j).coeff m) (map_negQ_DeltaF h)
  simp only [Polynomial.coeff_map, comp_C_mul_X_coeff] at e
  erw [coeff_negQ] at e
  have hC : ((-1 : FR) ^ j) = MvPolynomial.C ((-1 : ℚ) ^ j) := by simp
  rw [hC, mul_comm ((DeltaF h).coeff j), MvPolynomial.coeff_C_mul] at e
  have e2 : ((-1 : ℚ) ^ (m 0) - (-1) ^ j) * ((DeltaF h).coeff j).coeff m = 0 := by
    rw [sub_mul, e, sub_self]
  have e3 : (-1 : ℚ) ^ (m 0) = (-1) ^ j := sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hm)
  have e4 : (-1 : ℚ) ^ (m 0 + j) = 1 := by
    rw [pow_add, e3, ← pow_add, ← two_mul, pow_mul]; norm_num
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp e4

/-! ### The specialisation over `ℂ` -/

/-- `q ↦ i q₀`, `E ↦ −1/(q₀² + 1)`. -/
noncomputable def psiC (q₀ : ℕ) : FR →ₐ[ℚ] ℂ :=
  MvPolynomial.aeval ![Complex.I * (q₀ : ℂ), -1 / ((q₀ : ℂ) ^ 2 + 1)]

/-- `q ↦ q₀`, `E ↦ 1/(q₀² + 1)`. -/
noncomputable def evT (q₀ : ℕ) : FR →ₐ[ℚ] ℚ := MvPolynomial.aeval ![(q₀ : ℚ), 1 / ((q₀ : ℚ) ^ 2 + 1)]

lemma qsq_add_one_ne_zero_C (q₀ : ℕ) : (q₀ : ℂ) ^ 2 + 1 ≠ 0 := by
  have : ((q₀ : ℝ) ^ 2 + 1 : ℝ) ≠ 0 := by positivity
  exact_mod_cast this

lemma psiC_qF (q₀ : ℕ) : psiC q₀ qF = Complex.I * q₀ := by simp [psiC, qF]

lemma psiC_EF (q₀ : ℕ) : psiC q₀ EF = -1 / ((q₀ : ℂ) ^ 2 + 1) := by simp [psiC, EF]

lemma psiC_C (q₀ : ℕ) (r : ℚ) : psiC q₀ (MvPolynomial.C r) = (r : ℂ) := by simp [psiC]

lemma psiC_OmegaF {q₀ : ℕ} (hq : 1 ≤ q₀) (b : ℕ) : psiC q₀ (OmegaF b) = ((OmQ (wT q₀) b : ℚ) : ℂ) := by
  have hq0 : (q₀ : ℂ) ≠ 0 := by exact_mod_cast (show q₀ ≠ 0 by omega)
  have h1 := qsq_add_one_ne_zero_C q₀
  have h1' : 1 + (q₀ : ℂ) ^ 2 ≠ 0 := by rwa [add_comm]
  have h3 : (1 : ℂ) - -1 / (q₀ : ℂ) ^ 2 = ((q₀ : ℂ) ^ 2 + 1) / (q₀ : ℂ) ^ 2 := by field_simp; ring
  unfold OmegaF OmQ wT
  split_ifs with hb
  · rw [psiC_EF]; push_cast; rw [h3]; field_simp
  · rw [map_mul, map_pow, map_pow, psiC_qF, psiC_EF]
    push_cast
    rw [h3, mul_pow, Complex.I_sq, div_pow, div_pow, div_pow]
    field_simp
    ring

lemma psiC_muMonoF {q₀ : ℕ} (hq : 2 ≤ q₀) (d : ℕ) : psiC q₀ (muMonoF d) = ((muMono (wT q₀) d : ℚ) : ℂ) := by
  rw [muMono_newtonQ (abs_wT_lt_one hq), muMonoF, map_sum]
  push_cast
  refine sum_congr rfl (fun b _ => ?_)
  rw [map_mul, psiC_C, psiC_OmegaF (by omega)]
  push_cast; ring

lemma psiC_muF {q₀ : ℕ} (hq : 2 ≤ q₀) (R : ℚ[X]) : psiC q₀ (muF R) = ((muPoly (wT q₀) R : ℚ) : ℂ) := by
  rw [muF_eq_sum, muPoly, Polynomial.sum_def, Polynomial.sum_def, map_sum]
  push_cast
  refine sum_congr rfl (fun d _ => ?_)
  rw [map_smul, psiC_muMonoF hq, Rat.smul_def]

lemma psiC_SpartF (q₀ k : ℕ) : psiC q₀ (SpartF k) = ((SpartT q₀ k : ℚ) : ℂ) := by
  unfold SpartF SpartT
  rw [map_sum]
  push_cast
  refine sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_pow, psiC_qF, psiC_C, mul_pow, pow_mul Complex.I, Complex.I_sq]
  push_cast; ring

lemma psiC_AfunF {q₀ : ℕ} (hq : 2 ≤ q₀) (K : ℕ) (g : ℚ[X]) :
    psiC q₀ (AfunF K g) = ((AfunT q₀ K g : ℚ) : ℂ) := by
  unfold AfunF AfunT
  simp only [map_add, map_mul, map_sum, psiC_muF hq, psiC_C, psiC_SpartF, map_ofNat]
  push_cast
  ring

lemma psiC_BfunF (q₀ K : ℕ) (g : ℚ[X]) :
    -Complex.I * psiC q₀ (BfunF K g) = ((BfunT q₀ K g : ℚ) : ℂ) := by
  unfold BfunF BfunT poleW
  have e4 : psiC q₀ (-4 : FR) = -4 := by rw [map_neg, map_ofNat]
  rw [map_mul, map_sum, e4, Rat.cast_mul, Rat.cast_sum, ← mul_assoc,
    show -Complex.I * -4 = ((-4 : ℚ) : ℂ) * (-Complex.I) by push_cast; ring, mul_assoc, mul_sum]
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  rw [map_mul, map_pow, psiC_C, psiC_qF, mul_pow, pow_succ Complex.I, pow_mul Complex.I, Complex.I_sq]
  push_cast
  linear_combination (-((g.eval (pole k) : ℚ) : ℂ) * ((omega K k : ℚ) : ℂ) * (-1) ^ k * (q₀ : ℂ) ^ (2 * k + 1)) *
    Complex.I_sq

lemma map_DeltaF_psiC {q₀ : ℕ} (hq : 2 ≤ q₀) (h : ℕ) :
    ((DeltaF h).map (psiC q₀).toRingHom).comp (C (-Complex.I) * X) = (DeltaT q₀ h).map (algebraMap ℚ ℂ) := by
  unfold DeltaF DeltaT
  rw [map_det_XBA, comp_det_XBA, map_det_XBA]
  have hA : (AmatF h).map (psiC q₀).toRingHom = (AmatT q₀ h).map (algebraMap ℚ ℂ) :=
    Matrix.ext fun i j => psiC_AfunF hq h _
  have hB : ((BmatF h).map (psiC q₀).toRingHom).map (fun x => -Complex.I * x) =
      (BmatT q₀ h).map (algebraMap ℚ ℂ) := Matrix.ext fun i j => psiC_BfunF q₀ h _
  rw [hA, hB]

/-- The sign identity behind the twist, for a coefficient with the parity of `DeltaF`. -/
lemma psiC_eq_evT_twF (q₀ k : ℕ) (f : FR) (hpar : ∀ m, f.coeff m ≠ 0 → Even (m 0 + k)) :
    (-Complex.I) ^ k * psiC q₀ f = ((evT q₀ (twF k f) : ℚ) : ℂ) := by
  have h1 : evT q₀ (twF k f) = ∑ m ∈ f.support,
      tw k m * f.coeff m * ((q₀ : ℚ) ^ m 0 * (1 / ((q₀ : ℚ) ^ 2 + 1)) ^ m 1) := by
    unfold evT twF
    rw [map_sum]
    exact sum_congr rfl (fun m _ => by rw [aeval_monomial_fin2]; simp)
  unfold psiC
  rw [aeval_eq_sum_support, h1, mul_sum]
  push_cast
  refine sum_congr rfl (fun m hm => ?_)
  obtain ⟨t, ht⟩ := hpar m (MvPolynomial.mem_support_iff.mp hm)
  have htw : tw k m = (-1) ^ (m 1 + k + t) := by
    unfold tw; congr 1; omega
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Algebra.algebraMap_eq_smul_one,
    Rat.smul_def, mul_one]
  rw [htw]
  push_cast
  have hI : (-Complex.I) ^ k * Complex.I ^ m 0 = (-1) ^ k * (-1) ^ t := by
    rw [neg_pow, mul_assoc, ← pow_add, show k + m 0 = 2 * t by omega, pow_mul, Complex.I_sq]
  have e : (-1 / ((q₀ : ℂ) ^ 2 + 1)) ^ m 1 = (-1) ^ m 1 * (1 / ((q₀ : ℂ) ^ 2 + 1)) ^ m 1 := by
    rw [← mul_pow, neg_div, neg_eq_neg_one_mul (1 / _)]
  rw [mul_pow, e]
  calc (-Complex.I) ^ k * ((f.coeff m : ℂ) * (Complex.I ^ m 0 * (q₀ : ℂ) ^ m 0 *
        ((-1) ^ m 1 * (1 / ((q₀ : ℂ) ^ 2 + 1)) ^ m 1)))
      = ((-Complex.I) ^ k * Complex.I ^ m 0) * (-1) ^ m 1 * (f.coeff m : ℂ) *
          ((q₀ : ℂ) ^ m 0 * (1 / ((q₀ : ℂ) ^ 2 + 1)) ^ m 1) := by ring
    _ = _ := by rw [hI, pow_add, pow_add]; ring

/-- **The twisted symbolic determinant specialises to the Ti machine.** -/
theorem map_DeltaFT {q₀ : ℕ} (hq : 2 ≤ q₀) (h : ℕ) : (DeltaFT h).map (evT q₀).toRingHom = DeltaT q₀ h := by
  apply Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  ext k
  rw [← map_DeltaF_psiC hq h, Polynomial.coeff_map, Polynomial.coeff_map, comp_C_mul_X_coeff,
    Polynomial.coeff_map, coeff_DeltaFT, mul_comm]
  exact (psiC_eq_evT_twF q₀ k _ (parity_DeltaF h k)).symm

/-- The coefficients of `Δ^Ti_h` as specialisations of twisted symbolic coefficients. -/
lemma coeff_DeltaT_eq {q₀ : ℕ} (hq : 2 ≤ q₀) (h k : ℕ) :
    (DeltaT q₀ h).coeff k = MvPolynomial.aeval ![(q₀ : ℚ), 1 / ((q₀ : ℚ) ^ 2 + 1)] (twF k ((DeltaF h).coeff k)) := by
  rw [← map_DeltaFT hq, Polynomial.coeff_map, coeff_DeltaFT]; rfl

/-! ### Clearing `E` for Ti: `E^b ↦ (q² + 1)^{β − b}` -/

/-- Replace `E^b` by `(q² + 1)^{β − b}`. -/
noncomputable def clearET (β : ℕ) (f : FR) : FR :=
  ∑ m ∈ f.support, MvPolynomial.C (f.coeff m) * qF ^ (m 0) * (qF ^ 2 + 1) ^ (β - m 1)

lemma aeval_clearET {R : Type*} [CommRing R] [Algebra ℚ R] (v : Fin 2 → R) (hv : v 1 * (v 0 ^ 2 + 1) = 1)
    {β : ℕ} {f : FR} (hf : EDeg β f) :
    MvPolynomial.aeval v (clearET β f) = (v 0 ^ 2 + 1) ^ β * MvPolynomial.aeval v f := by
  rw [aeval_eq_sum_support v f, mul_sum]
  unfold clearET
  rw [map_sum]
  refine sum_congr rfl (fun m hm => ?_)
  have hb : m 1 ≤ β := hf m (MvPolynomial.mem_support_iff.mp hm)
  simp only [map_mul, map_pow, map_add, map_one, MvPolynomial.aeval_C, qF, MvPolynomial.aeval_X]
  have key : (v 0 ^ 2 + 1) ^ β * v 1 ^ m 1 = (v 0 ^ 2 + 1) ^ (β - m 1) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hb
    rw [hd, Nat.add_sub_cancel_left, pow_add, mul_comm ((v 0 ^ 2 + 1) ^ m 1), mul_assoc, ← mul_pow,
      mul_comm (v 0 ^ 2 + 1), hv, one_pow, mul_one]
  rw [← key]; ring

lemma EDeg_clearET (β : ℕ) (f : FR) : EDeg 0 (clearET β f) := by
  unfold clearET
  refine EDeg_sum _ _ (fun m _ => ?_)
  have h1 : EDeg 0 (qF ^ 2 + 1) := EDeg_add (EDeg_qpow 2) (EDeg_C 1 |> fun h => by simpa using h)
  have := EDeg_mul (EDeg_mul (EDeg_C (f.coeff m)) (EDeg_qpow (m 0))) (EDeg_pow h1 (β - m 1))
  simpa using this

/-- `q ↦ i q` (over `ℂ`). -/
noncomputable def scI : FR →ₐ[ℚ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (![Complex.I, 1] i) * MvPolynomial.X i)

/-- The `ℚ`-to-`ℂ` coefficient map on `FR`. -/
noncomputable def toC : FR →ₐ[ℚ] MvPolynomial (Fin 2) ℂ := MvPolynomial.aeval (fun i => MvPolynomial.X i)

lemma coeff_toC (f : FR) (m : Fin 2 →₀ ℕ) : (toC f).coeff m = ((f.coeff m : ℚ) : ℂ) := by
  have := coeff_aeval_scale (R := ℂ) ![1, 1] f m
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, mul_one, map_one,
    one_mul] at this
  have e : (fun i : Fin 2 => MvPolynomial.C (![(1 : ℂ), 1] i) * MvPolynomial.X i) = fun i => MvPolynomial.X i := by
    funext i; fin_cases i <;> simp
  rw [e] at this
  rw [toC, this]; rfl

lemma coeff_scI (f : FR) (m : Fin 2 →₀ ℕ) : (scI f).coeff m = ((f.coeff m : ℚ) : ℂ) * Complex.I ^ m 0 := by
  rw [scI, coeff_aeval_scale]
  simp

lemma scI_qF : scI qF = MvPolynomial.C Complex.I * toC qF := by simp [scI, toC, qF]

lemma scI_C (r : ℚ) : scI (MvPolynomial.C r) = MvPolynomial.C (r : ℂ) := by
  simp [scI, MvPolynomial.algebraMap_apply]

lemma toC_C (r : ℚ) : toC (MvPolynomial.C r) = MvPolynomial.C (r : ℂ) := by
  simp [toC, MvPolynomial.algebraMap_apply]

/-- `scI (clearE β f) = i^k (−1)^β · clearET β (twF k f)` for `f` with the parity of the `k`-th coefficient. -/
lemma scI_clearE (k β : ℕ) (f : FR) (hE : EDeg β f) (hpar : ∀ m, f.coeff m ≠ 0 → Even (m 0 + k)) :
    scI (clearE β f) = MvPolynomial.C (Complex.I ^ k * (-1) ^ β) * toC (clearET β (twF k f)) := by
  unfold clearE clearET
  rw [support_twF, map_sum, map_sum, mul_sum]
  refine sum_congr rfl (fun m hm => ?_)
  have hm0 := MvPolynomial.mem_support_iff.mp hm
  obtain ⟨t, ht⟩ := hpar m hm0
  have hb : m 1 ≤ β := hE m hm0
  have htw : tw k m = (-1) ^ (m 1 + k + t) := by unfold tw; congr 1; omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hb
  have hsub : β - m 1 = n := by omega
  rw [coeff_twF, hsub]
  simp only [map_mul, map_pow, map_sub, map_add, map_one, scI_qF, scI_C, toC_C]
  set Q := toC qF
  have hI : Complex.I ^ m 0 = Complex.I ^ k * (-1) ^ (k + t) := by
    have h2 : Complex.I ^ m 0 * Complex.I ^ k = (-1) ^ t := by
      rw [← pow_add, show m 0 + k = 2 * t by omega, pow_mul, Complex.I_sq]
    have h4 : Complex.I ^ k * Complex.I ^ k = (-1) ^ k := by rw [← pow_add, ← two_mul, pow_mul, Complex.I_sq]
    have h5 : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc Complex.I ^ m 0 = Complex.I ^ m 0 * (Complex.I ^ k * Complex.I ^ k) * (-1) ^ k := by
          rw [h4, mul_assoc, h5, mul_one]
      _ = (Complex.I ^ m 0 * Complex.I ^ k) * Complex.I ^ k * (-1) ^ k := by ring
      _ = _ := by rw [h2, pow_add]; ring
  have hm1 : ((-1 : ℂ) ^ m 1) * ((-1 : ℂ) ^ m 1) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hs : ((f.coeff m : ℚ) : ℂ) * Complex.I ^ m 0 * (-1) ^ n =
      Complex.I ^ k * (-1) ^ β * (((tw k m * f.coeff m : ℚ)) : ℂ) := by
    rw [htw, hI, hn]
    push_cast
    rw [pow_add, pow_add, pow_add, pow_add]
    linear_combination (-((f.coeff m : ℚ) : ℂ) * Complex.I ^ k * (-1) ^ k * (-1) ^ t * (-1) ^ n) * hm1
  have e1 : (MvPolynomial.C Complex.I * Q) ^ 2 - 1 = -(Q ^ 2 + 1) := by
    rw [mul_pow, ← map_pow, Complex.I_sq, map_neg, map_one]; ring
  calc MvPolynomial.C ((f.coeff m : ℚ) : ℂ) * (MvPolynomial.C Complex.I * Q) ^ m 0 *
        ((MvPolynomial.C Complex.I * Q) ^ 2 - 1) ^ n
      = MvPolynomial.C (((f.coeff m : ℚ) : ℂ) * Complex.I ^ m 0 * (-1) ^ n) * (Q ^ m 0 * (Q ^ 2 + 1) ^ n) := by
        rw [e1, neg_pow]; simp only [map_mul, map_pow, map_neg, map_one, mul_pow]; ring
    _ = MvPolynomial.C (Complex.I ^ k * (-1) ^ β * (((tw k m * f.coeff m : ℚ)) : ℂ)) *
          (Q ^ m 0 * (Q ^ 2 + 1) ^ n) := by rw [hs]
    _ = _ := by simp only [map_mul, map_pow, Rat.cast_mul]; ring

lemma eq_or_eq_neg_of_I_pow {x y : ℚ} {a b : ℕ} (h : (x : ℂ) * Complex.I ^ a = (y : ℂ) * Complex.I ^ b) :
    x = y ∨ x = -y := by
  have hred : ∀ n : ℕ, Complex.I ^ n = Complex.I ^ (n % 4) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hred a, hred b] at h
  have ha : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 4) <;> interval_cases (b % 4) <;>
    simp [pow_succ, Complex.ext_iff] at h <;>
    (try obtain ⟨h1, h2⟩ := h) <;> norm_cast at * <;> first | (left; linarith) | (right; linarith)

/-- **The cleared Ti coefficients are `±` the cleared χ₂ coefficients.** -/
theorem coeff_clearET_twF (k β : ℕ) (f : FR) (hE : EDeg β f) (hpar : ∀ m, f.coeff m ≠ 0 → Even (m 0 + k))
    (m : Fin 2 →₀ ℕ) :
    (clearET β (twF k f)).coeff m = (clearE β f).coeff m ∨ (clearET β (twF k f)).coeff m = -(clearE β f).coeff m := by
  have e := congrArg (fun F : MvPolynomial (Fin 2) ℂ => F.coeff m) (scI_clearE k β f hE hpar)
  simp only [coeff_scI, MvPolynomial.coeff_C_mul, coeff_toC] at e
  have hβ : ((-1 : ℂ) ^ β) = ((((-1 : ℚ) ^ β : ℚ)) : ℂ) := by push_cast; rfl
  rw [hβ, mul_comm (Complex.I ^ k), mul_assoc, mul_comm (Complex.I ^ k), ← mul_assoc, ← Rat.cast_mul] at e
  rcases eq_or_eq_neg_of_I_pow e.symm with h1 | h1
  · rcases neg_one_pow_eq_or ℚ β with hb | hb <;> rw [hb] at h1
    · left; linarith
    · right; linarith
  · rcases neg_one_pow_eq_or ℚ β with hb | hb <;> rw [hb] at h1
    · right; linarith
    · left; linarith

lemma padicNorm_coeff_clearET {p : ℕ} [Fact p.Prime] (k β : ℕ) (f : FR) (hE : EDeg β f)
    (hpar : ∀ m, f.coeff m ≠ 0 → Even (m 0 + k)) (m : Fin 2 →₀ ℕ) :
    padicNorm p ((clearET β (twF k f)).coeff m) = padicNorm p ((clearE β f).coeff m) := by
  rcases coeff_clearET_twF k β f hE hpar m with h | h <;> rw [h]
  rw [padicNorm.neg]

lemma coeff_clearET_ne_zero {k β : ℕ} {f : FR} (hE : EDeg β f) (hpar : ∀ m, f.coeff m ≠ 0 → Even (m 0 + k))
    {m : Fin 2 →₀ ℕ} (hm : (clearET β (twF k f)).coeff m ≠ 0) : (clearE β f).coeff m ≠ 0 := by
  rcases coeff_clearET_twF k β f hE hpar m with h | h <;> rw [h] at hm
  · exact hm
  · exact neg_ne_zero.mp hm

/-! ### The common clearing step for the Ti machine -/

lemma qsq_add_one_pos (q₀ : ℕ) : (0 : ℚ) < (q₀ : ℚ) ^ 2 + 1 := by positivity

/-- Copy of `padicNorm_Delta_clear` (`Arith/Special.lean`) for `Δ^Ti`: the `p`-adic bound after clearing `(q₀² + 1)^β`,
from a Gauss bound and a `q`-degree bound on the cleared **χ₂** coefficient. -/
lemma padicNorm_DeltaT_clear {p q₀ : ℕ} [Fact p.Prime] {B : ℚ} (hB : 0 ≤ B) (hq : 2 ≤ q₀)
    (h k a : ℕ) (hf : GLe p B ((DeltaF h).coeff k))
    (ha : ∀ m, (clearE (betaP h) ((DeltaF h).coeff k)).coeff m ≠ 0 → a ≤ m 0) :
    padicNorm p ((q₀ : ℚ) ^ 2 + 1) ^ betaP h * padicNorm p ((DeltaT q₀ h).coeff k) ≤
      B * padicNorm p (q₀ : ℚ) ^ a := by
  set f := (DeltaF h).coeff k with hfdef
  set v : Fin 2 → ℚ := ![(q₀ : ℚ), 1 / ((q₀ : ℚ) ^ 2 + 1)]
  have hv : v 1 * (v 0 ^ 2 + 1) = 1 := by
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    field_simp [(qsq_add_one_pos q₀).ne']
  have hE : EDeg (betaP h) f := EDeg_DeltaF h k
  have hpar : ∀ m, f.coeff m ≠ 0 → Even (m 0 + k) := parity_DeltaF h k
  have hcl := aeval_clearET v hv (EDeg_twF hE k)
  have hG : GLe p B (clearET (betaP h) (twF k f)) := fun m => by
    rw [padicNorm_coeff_clearET k _ f hE hpar m]; exact GLe_clearE hB hf _ m
  have hb := padicNorm_aeval_le_of_qdeg hB hG (EDeg_clearET _ _) a
    (fun m hm => ha m (coeff_clearET_ne_zero hE hpar hm)) v
    (by simpa [v] using padicNorm.of_nat (p := p) q₀)
  rw [hcl, padicNorm.mul, padicNorm_pow (ℓ := p)] at hb
  rw [coeff_DeltaT_eq hq]
  simpa [v] using hb

end TiQ
end Chi2Irr
