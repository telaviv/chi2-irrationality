/-
# Lemma 5: the pole order at `q² = 1`, and clearing `E`

In the free ring `FR = ℚ[q, E]` (`E ↔ 1/(q²−1)`):
* `EDeg d f`: every monomial of `f` has `E`-degree `≤ d`; `EDegX` for `FR[X]`; a Leibniz bound `det_EDegX`.
* `EDeg_muF`: `μ(R)` has `E`-degree `≤ deg R` (Newton form: `Ω_b` has `E`-degree `b + 1`, `b < deg R`).
* `EDeg_DeltaF`: the monomial Gram entries have `E`-degree `≤ (i + j + 1 − h)₊ ≤ r_i + c_j`, so
  `Δ^F_h` has `E`-degree `≤ βp h = Σ_a (a + 1 − ⌈h/2⌉)₊ + Σ_b (b − ⌊h/2⌋)₊ ≤ (h² + 2h)/4`.
* `clearE β f` replaces `E^b` by `(q²−1)^{β−b}`: it has no `E`, does not increase Gauss norms, and
  `aeval v (clearE β f) = (v₀² − 1)^β · aeval v f` whenever `v₁ (v₀² − 1) = 1` (`aeval_clearE`).
-/
import Chi2Irrational.Arith.ClassBound

namespace Chi2Irr

open Polynomial Finset

/-! ### `E`-degree -/

/-- Every monomial of `f` has `E`-degree `≤ d`. -/
def EDeg (d : ℕ) (f : FR) : Prop := ∀ m, f.coeff m ≠ 0 → m 1 ≤ d

lemma EDeg_mono {d d' : ℕ} (h : d ≤ d') {f : FR} (hf : EDeg d f) : EDeg d' f := fun m hm => (hf m hm).trans h

lemma EDeg_zero (d : ℕ) : EDeg d 0 := fun m hm => by simp at hm

lemma EDeg_add {d : ℕ} {f g : FR} (hf : EDeg d f) (hg : EDeg d g) : EDeg d (f + g) := fun m hm => by
  rw [MvPolynomial.coeff_add] at hm
  by_cases h1 : f.coeff m = 0
  · rw [h1, zero_add] at hm; exact hg m hm
  · exact hf m h1

lemma EDeg_neg {d : ℕ} {f : FR} (hf : EDeg d f) : EDeg d (-f) := fun m hm => by
  rw [MvPolynomial.coeff_neg, neg_ne_zero] at hm; exact hf m hm

lemma EDeg_sub {d : ℕ} {f g : FR} (hf : EDeg d f) (hg : EDeg d g) : EDeg d (f - g) := by
  rw [sub_eq_add_neg]; exact EDeg_add hf (EDeg_neg hg)

lemma EDeg_sum {ι : Type*} (s : Finset ι) {d : ℕ} (f : ι → FR) (h : ∀ i ∈ s, EDeg d (f i)) :
    EDeg d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EDeg_zero d
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact EDeg_add (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma EDeg_mul {d₁ d₂ : ℕ} {f g : FR} (hf : EDeg d₁ f) (hg : EDeg d₂ g) : EDeg (d₁ + d₂) (f * g) := by
  classical
  intro m hm
  rw [MvPolynomial.coeff_mul] at hm
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  have h1 := hf x.1 (left_ne_zero_of_mul hne)
  have h2 := hg x.2 (right_ne_zero_of_mul hne)
  rw [← hx, Finsupp.add_apply]
  omega

lemma EDeg_C (r : ℚ) : EDeg 0 (MvPolynomial.C r) := fun m hm => by
  rw [MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · rw [← h]; rfl
  · exact absurd rfl hm

lemma EDeg_X0 : EDeg 0 qF := fun m hm => by
  unfold qF at hm
  rw [MvPolynomial.coeff_X'] at hm
  split_ifs at hm with h
  · rw [← h]; simp
  · exact absurd rfl hm

lemma EDeg_X1 : EDeg 1 EF := fun m hm => by
  unfold EF at hm
  rw [MvPolynomial.coeff_X'] at hm
  split_ifs at hm with h
  · rw [← h]; simp
  · exact absurd rfl hm

lemma EDeg_pow {d : ℕ} {f : FR} (hf : EDeg d f) (n : ℕ) : EDeg (d * n) (f ^ n) := by
  induction n with
  | zero => simpa using EDeg_C 1
  | succ n ih => rw [pow_succ, mul_add, mul_one]; exact EDeg_mul ih hf

lemma EDeg_qpow (n : ℕ) : EDeg 0 (qF ^ n) := by simpa using EDeg_pow EDeg_X0 n

lemma EDeg_OmegaF (b : ℕ) : EDeg (b + 1) (OmegaF b) := by
  unfold OmegaF
  split_ifs with hb
  · subst hb; simpa using EDeg_X1
  · have := EDeg_mul (EDeg_qpow 2) (EDeg_pow EDeg_X1 (b + 1))
    simpa using this

lemma EDeg_muMonoF (d : ℕ) : EDeg d (muMonoF d) := by
  unfold muMonoF
  refine EDeg_sum _ _ (fun b hb => ?_)
  have := EDeg_mul (EDeg_C ((d : ℚ) * (dCoef (d - 1) b : ℚ))) (EDeg_OmegaF b)
  exact EDeg_mono (by have := mem_range.mp hb; omega) this

lemma EDeg_muF (R : ℚ[X]) : EDeg R.natDegree (muF R) := by
  rw [muF_eq_sum, Polynomial.sum_def]
  refine EDeg_sum _ _ (fun d hd => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  have := EDeg_mul (EDeg_C (R.coeff d)) (EDeg_muMonoF d)
  exact EDeg_mono (by rw [zero_add]; exact le_natDegree_of_mem_supp d hd) this

lemma EDeg_SpartF (k : ℕ) : EDeg 0 (SpartF k) := by
  unfold SpartF
  exact EDeg_sum _ _ (fun j _ => by simpa using EDeg_mul (EDeg_qpow _) (EDeg_C _))

lemma EDeg_four : EDeg 0 (4 : FR) := by
  have : (4 : FR) = MvPolynomial.C 4 := (map_ofNat MvPolynomial.C 4).symm
  rw [this]; exact EDeg_C 4

lemma EDeg_AfunF (K : ℕ) (g : ℚ[X]) : EDeg ((g * X) /ₘ Dpoly K).natDegree (AfunF K g) := by
  unfold AfunF
  refine EDeg_add (EDeg_muF _) (EDeg_mono (Nat.zero_le _) ?_)
  have := EDeg_mul EDeg_four (EDeg_sum (range K) _ (fun k _ => by
    simpa using EDeg_mul (EDeg_C (g.eval (pole k) * omega K k)) (EDeg_SpartF k)))
  simpa using this

lemma EDeg_BfunF (K : ℕ) (g : ℚ[X]) : EDeg 0 (BfunF K g) := by
  unfold BfunF
  have h4 : EDeg 0 (-4 : FR) := EDeg_neg EDeg_four
  have := EDeg_mul h4 (EDeg_sum (range K) _ (fun k _ => by
    simpa using EDeg_mul (EDeg_C (g.eval (pole k) * omega K k)) (EDeg_qpow (2 * k + 1))))
  simpa using this

/-! ### `E`-degree on `FR[X]` and determinants -/

def EDegX (d : ℕ) (F : FR[X]) : Prop := ∀ k, EDeg d (F.coeff k)

lemma EDegX_add {d : ℕ} {F G : FR[X]} (hF : EDegX d F) (hG : EDegX d G) : EDegX d (F + G) :=
  fun k => by rw [coeff_add]; exact EDeg_add (hF k) (hG k)

lemma EDegX_neg {d : ℕ} {F : FR[X]} (hF : EDegX d F) : EDegX d (-F) :=
  fun k => by rw [coeff_neg]; exact EDeg_neg (hF k)

lemma EDegX_sum {ι : Type*} (s : Finset ι) {d : ℕ} (F : ι → FR[X]) (h : ∀ i ∈ s, EDegX d (F i)) :
    EDegX d (∑ i ∈ s, F i) := fun k => by
  rw [finset_sum_coeff]; exact EDeg_sum s _ (fun i hi => h i hi k)

lemma EDegX_mul {d₁ d₂ : ℕ} {F G : FR[X]} (hF : EDegX d₁ F) (hG : EDegX d₂ G) : EDegX (d₁ + d₂) (F * G) :=
  fun k => by
    rw [coeff_mul]; exact EDeg_sum _ _ (fun x _ => EDeg_mul (hF _) (hG _))

lemma EDegX_C {d : ℕ} {a : FR} (ha : EDeg d a) : EDegX d (C a) := fun k => by
  rw [coeff_C]; split_ifs
  · exact ha
  · exact EDeg_zero d

lemma EDegX_X_mul {d : ℕ} {F : FR[X]} (hF : EDegX d F) : EDegX d (X * F) := fun k => by
  cases k with
  | zero => rw [coeff_X_mul_zero]; exact EDeg_zero d
  | succ k => rw [coeff_X_mul]; exact hF k

lemma EDegX_mono {d d' : ℕ} (h : d ≤ d') {F : FR[X]} (hF : EDegX d F) : EDegX d' F :=
  fun k => EDeg_mono h (hF k)

lemma EDegX_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) (F : ι → FR[X]) (h : ∀ i ∈ s, EDegX (d i) (F i)) :
    EDegX (∑ i ∈ s, d i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EDegX_C (EDeg_C 1)
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact EDegX_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

theorem det_EDegX {n : ℕ} (M : Matrix (Fin n) (Fin n) FR[X]) (r c : Fin n → ℕ)
    (h : ∀ i j, EDegX (r i + c j) (M i j)) : EDegX (∑ i, r i + ∑ i, c i) M.det := by
  rw [Matrix.det_apply]
  refine EDegX_sum _ _ (fun σ _ => ?_)
  have hprod : EDegX (∑ i, r i + ∑ i, c i) (∏ i, M (σ i) i) := by
    have := EDegX_prod univ (fun i => r (σ i) + c i) (fun i => M (σ i) i) (fun i _ => h (σ i) i)
    rwa [sum_add_distrib, Equiv.sum_comp σ r] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact EDegX_neg hprod

/-! ### Lemma 5 -/

/-- Row potential `(a + 1 − ⌈h/2⌉)₊`. -/
def rPot (h a : ℕ) : ℕ := a + 1 - (h + 1) / 2

/-- Column potential `(b − ⌊h/2⌋)₊`. -/
def cPot (h b : ℕ) : ℕ := b - h / 2

/-- The clearing exponent `βp h ≈ h²/4`. -/
def betaP (h : ℕ) : ℕ := ∑ a ∈ range h, rPot h a + ∑ b ∈ range h, cPot h b

lemma two_mul_sum_sub (h c : ℕ) : 2 * ∑ a ∈ range h, (a + 1 - c) = (h - c) * (h + 1 - c) := by
  induction h with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    rcases Nat.lt_or_ge n c with hlt | hge
    · rw [Nat.sub_eq_zero_of_le hlt.le, Nat.sub_eq_zero_of_le (by omega : n + 1 ≤ c)]
      simp
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
      have e1 : c + d - c = d := by omega
      have e2 : c + d + 1 - c = d + 1 := by omega
      have e3 : c + d + 1 + 1 - c = d + 2 := by omega
      rw [e1, e2, e3]; ring

lemma two_mul_sum_sub' (h c : ℕ) : 2 * ∑ b ∈ range h, (b - c) ≤ (h - c) * (h - c) := by
  induction h with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add]
    rcases Nat.lt_or_ge n c with hlt | hge
    · rw [Nat.sub_eq_zero_of_le hlt.le, mul_zero, add_zero]
      exact ih.trans (Nat.mul_le_mul (by omega) (by omega))
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
      have e1 : c + d - c = d := by omega
      have e2 : c + d + 1 - c = d + 1 := by omega
      rw [e1] at ih ⊢; rw [e2]
      nlinarith

lemma betaP_le (h : ℕ) : 4 * betaP h ≤ h ^ 2 + 2 * h := by
  unfold betaP rPot cPot
  have h1 := two_mul_sum_sub h ((h + 1) / 2)
  have h2 := two_mul_sum_sub' h (h / 2)
  rcases Nat.even_or_odd h with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have a1 : (s + s + 1) / 2 = s := by omega
    have a2 : (s + s) / 2 = s := by omega
    rw [a1] at h1 ⊢; rw [a2] at h2 ⊢
    have b1 : s + s - s = s := by omega
    have b2 : s + s + 1 - s = s + 1 := by omega
    rw [b1, b2] at h1; rw [b1] at h2
    nlinarith
  · have a1 : (2 * s + 1 + 1) / 2 = s + 1 := by omega
    have a2 : (2 * s + 1) / 2 = s := by omega
    rw [a1] at h1 ⊢; rw [a2] at h2 ⊢
    have b1 : 2 * s + 1 - (s + 1) = s := by omega
    have b2 : 2 * s + 1 + 1 - (s + 1) = s + 1 := by omega
    have b3 : 2 * s + 1 - s = s + 1 := by omega
    rw [b1, b2] at h1; rw [b3] at h2
    nlinarith

lemma natDegree_powX_divByMonic (h n : ℕ) : ((X : ℚ[X]) ^ n * X /ₘ Dpoly h).natDegree ≤ n + 1 - h := by
  rw [natDegree_divByMonic _ (Dpoly_monic h), ← pow_succ, natDegree_X_pow]
  have : (Dpoly h).natDegree = h := by
    unfold Dpoly
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
    simp
  rw [this]

/-- **Lemma 5.** `Δ^F_h` has `E`-degree `≤ βp h`. -/
theorem EDeg_DeltaF (h : ℕ) : EDegX (betaP h) (DeltaF h) := by
  unfold DeltaF betaP
  rw [Fin.sum_univ_eq_sum_range (rPot h) h |>.symm, Fin.sum_univ_eq_sum_range (cPot h) h |>.symm]
  refine det_EDegX _ (fun i => rPot h i) (fun j => cPot h j) (fun i j => ?_)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, AmatF, BmatF]
  have hA := EDeg_AfunF h (X ^ ((i : ℕ) + j))
  have hdeg := natDegree_powX_divByMonic h ((i : ℕ) + j)
  have hle : (i : ℕ) + j + 1 - h ≤ rPot h i + cPot h j := by unfold rPot cPot; omega
  refine EDegX_add (EDegX_X_mul (EDegX_mono (Nat.zero_le _) (EDegX_C (EDeg_BfunF h _))))
    (EDegX_C (EDeg_mono ((hdeg.trans hle)) hA))


/-! ### Clearing `E` -/

/-- Replace `E^b` by `(q² − 1)^{β − b}`. -/
noncomputable def clearE (β : ℕ) (f : FR) : FR :=
  ∑ m ∈ f.support, MvPolynomial.C (f.coeff m) * qF ^ (m 0) * (qF ^ 2 - 1) ^ (β - m 1)

lemma aeval_monomial_fin2 {R : Type*} [CommRing R] [Algebra ℚ R] (v : Fin 2 → R) (m : Fin 2 →₀ ℕ) (c : ℚ) :
    MvPolynomial.aeval v (MvPolynomial.monomial m c) = algebraMap ℚ R c * (v 0 ^ m 0 * v 1 ^ m 1) := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]

lemma aeval_eq_sum_support {R : Type*} [CommRing R] [Algebra ℚ R] (v : Fin 2 → R) (f : FR) :
    MvPolynomial.aeval v f = ∑ m ∈ f.support, algebraMap ℚ R (f.coeff m) * (v 0 ^ m 0 * v 1 ^ m 1) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  exact sum_congr rfl (fun m _ => aeval_monomial_fin2 v m _)

lemma aeval_clearE {R : Type*} [CommRing R] [Algebra ℚ R] (v : Fin 2 → R) (hv : v 1 * (v 0 ^ 2 - 1) = 1)
    {β : ℕ} {f : FR} (hf : EDeg β f) :
    MvPolynomial.aeval v (clearE β f) = (v 0 ^ 2 - 1) ^ β * MvPolynomial.aeval v f := by
  rw [aeval_eq_sum_support v f, mul_sum]
  unfold clearE
  rw [map_sum]
  refine sum_congr rfl (fun m hm => ?_)
  have hb : m 1 ≤ β := hf m (MvPolynomial.mem_support_iff.mp hm)
  simp only [map_mul, map_pow, map_sub, map_one, MvPolynomial.aeval_C, qF, MvPolynomial.aeval_X]
  have key : (v 0 ^ 2 - 1) ^ β * v 1 ^ m 1 = (v 0 ^ 2 - 1) ^ (β - m 1) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hb
    rw [hd, Nat.add_sub_cancel_left, pow_add, mul_comm ((v 0 ^ 2 - 1) ^ m 1), mul_assoc, ← mul_pow,
      mul_comm (v 0 ^ 2 - 1), hv, one_pow, mul_one]
  rw [← key]; ring

lemma EDeg_clearE (β : ℕ) (f : FR) : EDeg 0 (clearE β f) := by
  unfold clearE
  refine EDeg_sum _ _ (fun m _ => ?_)
  have h1 : EDeg 0 (qF ^ 2 - 1) := EDeg_sub (EDeg_qpow 2) (EDeg_C 1 |> fun h => by simpa using h)
  have := EDeg_mul (EDeg_mul (EDeg_C (f.coeff m)) (EDeg_qpow (m 0))) (EDeg_pow h1 (β - m 1))
  simpa using this

lemma GLe_qsq_sub_one {p : ℕ} [Fact p.Prime] : GLe p 1 (qF ^ 2 - 1) := by
  have h : GLe p (1 ^ 2) (qF ^ 2) := GLe_pow zero_le_one GLe_qF 2
  rw [one_pow] at h
  exact GLe_sub h GLe_one

lemma GLe_clearE {p : ℕ} [Fact p.Prime] {B : ℚ} (hB : 0 ≤ B) {f : FR} (hf : GLe p B f) (β : ℕ) :
    GLe p B (clearE β f) := by
  unfold clearE
  refine GLe_sum _ hB _ (fun m _ => ?_)
  have h2 : GLe p (1 ^ (β - m 1)) ((qF ^ 2 - 1) ^ (β - m 1)) := GLe_pow zero_le_one GLe_qsq_sub_one _
  have h3 : GLe p (1 ^ m 0) (qF ^ m 0) := GLe_pow zero_le_one GLe_qF _
  rw [one_pow] at h2 h3
  have h4 : GLe p (padicNorm p (f.coeff m) * 1) (MvPolynomial.C (f.coeff m) * qF ^ m 0) :=
    GLe_mul (padicNorm.nonneg _) zero_le_one (GLe_C (f.coeff m)) h3
  rw [mul_one] at h4
  have h5 : GLe p (padicNorm p (f.coeff m) * 1) (MvPolynomial.C (f.coeff m) * qF ^ m 0 * (qF ^ 2 - 1) ^ (β - m 1)) :=
    GLe_mul (padicNorm.nonneg _) zero_le_one h4 h2
  rw [mul_one] at h5
  exact GLe_mono (hf m) h5

/-- Evaluating an `E`-free polynomial at `q₀`: the norm is at most `B |q₀|^a` if all `q`-degrees are `≥ a`. -/
lemma padicNorm_aeval_le_of_qdeg {p : ℕ} [Fact p.Prime] {B : ℚ} (hB : 0 ≤ B) {f : FR} (hf : GLe p B f)
    (hE : EDeg 0 f) (a : ℕ) (hq : ∀ m, f.coeff m ≠ 0 → a ≤ m 0) (v : Fin 2 → ℚ)
    (hv : padicNorm p (v 0) ≤ 1) : padicNorm p (MvPolynomial.aeval v f) ≤ B * padicNorm p (v 0) ^ a := by
  rw [aeval_eq_sum_support]
  refine padicNorm.sum_le' (fun m hm => ?_) (mul_nonneg hB (pow_nonneg (padicNorm.nonneg _) _))
  have hm0 := MvPolynomial.mem_support_iff.mp hm
  have h1 : m 1 = 0 := Nat.le_zero.mp (hE m hm0)
  rw [h1, pow_zero, mul_one, Algebra.algebraMap_self, RingHom.id_apply, padicNorm.mul, padicNorm_pow (ℓ := p)]
  have hq' := hq m hm0
  have : padicNorm p (v 0) ^ m 0 ≤ padicNorm p (v 0) ^ a :=
    pow_le_pow_of_le_one (padicNorm.nonneg _) hv hq'
  exact mul_le_mul (hf m) this (pow_nonneg (padicNorm.nonneg _) _) hB

end Chi2Irr
