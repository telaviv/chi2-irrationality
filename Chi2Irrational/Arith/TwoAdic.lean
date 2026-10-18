/-
# Lemma 10: the 2-adic bound on the coefficients of `Δ_h`

`twoAdic_Delta`: for `q₀ ∈ {3, 5}` and every `k`, `‖[X^k] Δ_h‖₂ ≤ 2^{βp(h) + h (⌊log₂ h⌋ + 6)}`.
* Gram identity for two families (`Gram2_eq`): `(Λ_X(a_i b_j)) = C_a H C_bᵀ` with `H = (Λ_X(X^{d+e}))`,
  `Λ_X(g) = A(g) + X B(g)`; for the anchored basis `C_a`, `C_b` are unitriangular, so the determinant is `Δ_h`.
* Leibniz over `ℚ[X]` (`det_PN`): `‖M_ij‖₂ ≤ ρ_i κ_j` coefficientwise implies `‖det M‖₂ ≤ ∏ρ ∏κ`.
* Entries (`V2_entry`): `v₂ ≥ K − (i+j+1) − (i+j+1−K)₊ − ⌊log₂ K⌋ − 6`, and `(i+j+1−K)₊ ≤ rPot i + cPot j`,
  so `ρ_i = 2^{i+1+rPot i+⌊log₂ h⌋+6−h}`, `κ_j = 2^{j+cPot j}` and `Σ(i+1) + Σ j = h²`.
-/
import Chi2Irrational.Arith.TwoAdicEntries
import Chi2Irrational.Arith.Gauss

namespace Chi2Irr

open Polynomial Finset
open scoped Nat

/-! ### `2`-adic norms on `ℚ[X]` and the Leibniz bound -/

/-- Every coefficient of `F` has `‖·‖₂ ≤ B`. -/
def PN (B : ℚ) (F : ℚ[X]) : Prop := ∀ k, padicNorm 2 (F.coeff k) ≤ B

lemma PN_zero {B : ℚ} (hB : 0 ≤ B) : PN B 0 := fun k => by simp [hB]

lemma PN_add {B : ℚ} {F G : ℚ[X]} (hF : PN B F) (hG : PN B G) : PN B (F + G) := fun k => by
  rw [coeff_add]; exact (padicNorm.nonarchimedean (p := 2)).trans (max_le (hF k) (hG k))

lemma PN_neg {B : ℚ} {F : ℚ[X]} (hF : PN B F) : PN B (-F) := fun k => by
  rw [coeff_neg, padicNorm.neg]; exact hF k

lemma PN_sum {ι : Type*} (s : Finset ι) {B : ℚ} (hB : 0 ≤ B) (F : ι → ℚ[X]) (h : ∀ i ∈ s, PN B (F i)) :
    PN B (∑ i ∈ s, F i) := fun k => by
  rw [finset_sum_coeff]; exact padicNorm.sum_le' (fun i hi => h i hi k) hB

lemma PN_mul {B C' : ℚ} (hB : 0 ≤ B) (hC : 0 ≤ C') {F G : ℚ[X]} (hF : PN B F) (hG : PN C' G) :
    PN (B * C') (F * G) := fun k => by
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun x _ => ?_) (by positivity)
  rw [padicNorm.mul]
  exact mul_le_mul (hF _) (hG _) (padicNorm.nonneg _) hB

lemma PN_one : PN 1 (1 : ℚ[X]) := fun k => by
  rw [coeff_one]; split_ifs <;> simp

lemma PN_prod {ι : Type*} (s : Finset ι) (B : ι → ℚ) (hB : ∀ i, 0 ≤ B i) (F : ι → ℚ[X])
    (h : ∀ i ∈ s, PN (B i) (F i)) : PN (∏ i ∈ s, B i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PN_one
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact PN_mul (hB a) (prod_nonneg (fun i _ => hB i)) (h a (mem_insert_self a s))
      (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- **Leibniz bound** over `ℚ[X]`. -/
theorem det_PN {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ[X]) (ρ κ : Fin n → ℚ) (hρ : ∀ i, 0 ≤ ρ i)
    (hκ : ∀ i, 0 ≤ κ i) (h : ∀ i j, PN (ρ i * κ j) (M i j)) :
    PN ((∏ i, ρ i) * ∏ i, κ i) M.det := by
  have h0 : 0 ≤ (∏ i, ρ i) * ∏ i, κ i :=
    mul_nonneg (prod_nonneg (fun i _ => hρ i)) (prod_nonneg (fun i _ => hκ i))
  rw [Matrix.det_apply]
  refine PN_sum _ h0 _ (fun σ _ => ?_)
  have hprod : PN ((∏ i, ρ i) * ∏ i, κ i) (∏ i, M (σ i) i) := by
    have := PN_prod univ (fun i => ρ (σ i) * κ i) (fun i => mul_nonneg (hρ _) (hκ _)) (fun i => M (σ i) i)
      (fun i _ => h (σ i) i)
    rwa [prod_mul_distrib, Equiv.prod_comp σ ρ] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact PN_neg hprod

lemma PN_entry {a b B : ℚ} (ha : padicNorm 2 a ≤ B) (hb : padicNorm 2 b ≤ B) (hB : 0 ≤ B) :
    PN B (C a + X * C b) := fun k => by
  rw [coeff_add, mul_comm, coeff_C_mul_X, coeff_C]
  refine (padicNorm.nonarchimedean (p := 2)).trans (max_le ?_ ?_)
  · split_ifs
    · exact ha
    · simpa using hB
  · split_ifs
    · exact hb
    · simpa using hB

/-! ### Linearity of `Λ_X` and the Gram identity for two families -/

lemma Afun_add' (q K : ℕ) (f g : ℚ[X]) : Afun q K (f + g) = Afun q K f + Afun q K g := by
  have := (LamLin q K 0).map_add f g
  simpa only [LamLin_apply, zero_mul, add_zero] using this

lemma Afun_smul' (q K : ℕ) (c : ℚ) (f : ℚ[X]) : Afun q K (c • f) = c * Afun q K f := by
  have := (LamLin q K 0).map_smul c f
  simpa only [LamLin_apply, zero_mul, add_zero, smul_eq_mul] using this

lemma Bfun_eq_LamLin (q K : ℕ) (g : ℚ[X]) : Bfun q K g = LamLin q K 1 g - LamLin q K 0 g := by
  simp only [LamLin_apply]; ring

lemma Bfun_add' (q K : ℕ) (f g : ℚ[X]) : Bfun q K (f + g) = Bfun q K f + Bfun q K g := by
  simp only [Bfun_eq_LamLin, map_add]; ring

lemma Bfun_smul' (q K : ℕ) (c : ℚ) (f : ℚ[X]) : Bfun q K (c • f) = c * Bfun q K f := by
  simp only [Bfun_eq_LamLin, map_smul, smul_eq_mul]; ring

/-- `Λ_X(g) = A(g) + X B(g)` as a `ℚ`-linear map `ℚ[X] → ℚ[X]`. -/
noncomputable def LamP (q K : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun g := C (Afun q K g) + X * C (Bfun q K g)
  map_add' f g := by simp only [Afun_add', Bfun_add', map_add]; ring
  map_smul' c f := by
    rw [Afun_smul', Bfun_smul', RingHom.id_apply, smul_eq_C_mul, map_mul, map_mul]; ring

lemma LamP_apply (q K : ℕ) (g : ℚ[X]) : LamP q K g = C (Afun q K g) + X * C (Bfun q K g) := rfl

/-- The monomial matrix `H_{de} = Λ_X(X^{d+e})`. -/
noncomputable def HPm (q h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] := fun d e => LamP q h (X ^ ((d : ℕ) + e))

lemma HPm_eq (q h : ℕ) : HPm q h = (X : ℚ[X]) • (Bmat q h).map C + (Amat q h).map C := by
  ext d e
  simp only [HPm, LamP_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Amat, Bmat]
  ring

lemma expand_fin {h : ℕ} (e : Fin h → ℚ[X]) (he : ∀ i, (e i).natDegree < h) (k : Fin h) :
    e k = ∑ d : Fin h, C (CoefM e k d) * X ^ (d : ℕ) := by
  show e k = ∑ d : Fin h, C ((e k).coeff d) * X ^ (d : ℕ)
  rw [Fin.sum_univ_eq_sum_range (fun d => C ((e k).coeff d) * X ^ d) h]
  exact as_sum_range_C_mul_X_pow' _ (he k)

theorem Gram2_eq (q : ℕ) {h : ℕ} (a b : Fin h → ℚ[X]) (ha : ∀ i, (a i).natDegree < h)
    (hb : ∀ i, (b i).natDegree < h) :
    Matrix.of (fun i j => LamP q h (a i * b j)) =
      (CoefM a).map C * HPm q h * ((CoefM b).map C).transpose := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [expand_fin a ha i, expand_fin b hb j, sum_mul_sum]
  simp only [map_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  have : C (CoefM a i d) * X ^ (d : ℕ) * (C (CoefM b j e) * X ^ (e : ℕ)) =
      (CoefM a i d * CoefM b j e) • X ^ ((d : ℕ) + e) := by
    rw [smul_eq_C_mul, C_mul, pow_add]; ring
  rw [this, map_smul, smul_eq_C_mul, C_mul]
  simp only [HPm]
  ring

lemma det_CoefM_monic {h : ℕ} (e : Fin h → ℚ[X]) (hdeg : ∀ i, (e i).natDegree = i)
    (hmon : ∀ i, (e i).Monic) : (CoefM e).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine prod_eq_one (fun i _ => ?_)
    have := (hmon i).coeff_natDegree
    rwa [hdeg i] at this
  · intro i d hid
    exact coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hid)

lemma det_map_C {h : ℕ} (M : Matrix (Fin h) (Fin h) ℚ) : (M.map C).det = C M.det :=
  (RingHom.map_det C M).symm

lemma monic_prod_pole (s : Finset ℕ) : (∏ m ∈ s, (X - C (pole m))).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/-- `Δ_h` is the determinant of the anchored Gram matrix. -/
theorem Delta_eq_anchored (q h : ℕ) :
    Delta q h = (Matrix.of (fun i j : Fin h => LamP q h (aB i * bB h j))).det := by
  have hda : ∀ i : Fin h, (aB i).natDegree = i := fun i => by
    unfold aB; rw [natDegree_prod_pole, card_range]
  have hdb : ∀ j : Fin h, (bB h j).natDegree = j := fun j => by
    unfold bB; rw [natDegree_prod_pole, Nat.card_Ico]; have := j.isLt; omega
  rw [Gram2_eq q (fun i => aB i) (fun j => bB h j) (fun i => by rw [hda]; exact i.isLt)
    (fun j => by rw [hdb]; exact j.isLt), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_map_C, det_map_C, det_CoefM_monic _ hda (fun i => monic_prod_pole _),
    det_CoefM_monic _ hdb (fun j => monic_prod_pole _), map_one, one_mul, mul_one, HPm_eq]
  rfl

/-! ### The final bound -/

lemma sum_succ_add_sum (h : ℕ) : ∑ i ∈ range h, (i + 1) + ∑ i ∈ range h, i = h * h := by
  induction h with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ]; nlinarith

lemma padicNorm_le_of_V2 {e : ℤ} {x : ℚ} (hx : V2 e x) {B : ℚ} (hB : (2 : ℚ) ^ (-e) ≤ B) :
    padicNorm 2 x ≤ B := hx.trans hB

/-- **Lemma 10.** Every coefficient of `Δ_h` has `‖·‖₂ ≤ 2^{βp(h) + h (⌊log₂ h⌋ + 6)}` for `q₀ ∈ {3, 5}`. -/
theorem twoAdic_Delta {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) (h k : ℕ) :
    padicNorm 2 ((Delta q₀ h).coeff k) ≤ (2 : ℚ) ^ (betaP h + h * (Nat.log 2 h + 6)) := by
  set L := Nat.log 2 h with hL
  set ρ : Fin h → ℚ := fun i => (2 : ℚ) ^ ((i : ℕ) + 1 + rPot h i + L + 6) / (2 : ℚ) ^ h with hρ
  set κ : Fin h → ℚ := fun j => (2 : ℚ) ^ ((j : ℕ) + cPot h j) with hκ
  have hentry : ∀ i j : Fin h, PN (ρ i * κ j) (LamP q₀ h (aB i * bB h j)) := by
    intro i j
    have hv := V2_entry hq i.isLt j.isLt
    have hle : (2 : ℚ) ^ (-eTA h i j) ≤ ρ i * κ j := by
      have e : ρ i * κ j =
          (2 : ℚ) ^ ((((i : ℕ) + 1 + rPot h i + L + 6 + ((j : ℕ) + cPot h j) : ℕ) : ℤ) - h) := by
        rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, pow_add]
        simp only [hρ, hκ]
        ring
      rw [e]
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      unfold eTA rPot cPot
      push_cast
      omega
    rw [LamP_apply]
    exact PN_entry (hv.1.trans hle) (hv.2.trans hle) (by positivity)
  have hdet : PN ((∏ i, ρ i) * ∏ i, κ i) (Matrix.of (fun i j : Fin h => LamP q₀ h (aB i * bB h j))).det :=
    det_PN _ ρ κ (fun i => by positivity) (fun j => by positivity) hentry
  rw [Delta_eq_anchored]
  refine (hdet k).trans (le_of_eq ?_)
  simp only [hρ, hκ]
  rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum,
    prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i + 1 + rPot h i + L + 6) h,
    Fin.sum_univ_eq_sum_range (fun j => j + cPot h j) h, ← pow_mul, div_mul_eq_mul_div,
    ← pow_add, div_eq_iff (by positivity), ← pow_add]
  congr 1
  have h1 := sum_succ_add_sum h
  simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul] at h1 ⊢
  unfold betaP
  nlinarith

end Chi2Irr
