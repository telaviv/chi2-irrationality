/-
# Lemma 10″ (2-adic bound at `ζ = q/2`, `q` odd), part 1: the anchored Gram matrix and its entries

`pilot_chi2_2q/RESULT.md` §2. `K = h`, anchored basis `a_i = ∏_{m<i} (X − x_m)`, `b_j = ∏_{h−j ≤ m < h} (X − x_m)`
(`aB`, `bB` of `Arith/TwoAdicEntries.lean`), `G_ij = Λ_X(a_i b_j) = A + X·B`.
* `DeltaZ_eq_anchored`: `Δ_h(X; ζ) = det G` (unitriangular change of basis, as `Delta_eq_anchored`).
* At `ζ = q/2`: `v₂(ζ) = −1`, `E = 1/(ζ² − 1) = 4/(q² − 4)` has `v₂(E) = 2`, so `v₂(Ω_b) ≥ 0` for every `b`.
* (L) `π = i + j + 1 − h ≥ 1`: `B = 0`, `v₂(A) ≥ −π` (`V2_A_LZ`; RESULT has `3 − π`, `−π` suffices).
* (U) `N = h − 1 − i − j ≥ 0`: `v₂(A), v₂(B) ≥ −2i − 3N` (`V2_A_UZ`, `V2_B_UZ`), by the naive expansion
  `(4/N!) Σ_{l≤N} (−1)^l C(N,l) x_{i+l} T(i+l)` with `v₂(x_k T(k)) ≥ −2k − 2` and `v₂(N!) ≤ N`
  (RESULT's sharper `−2i − 3N + s₂(N)` is not needed for the constant `4/3`).
-/
import Chi2Irrational.QZ.Defs
import Chi2Irrational.Arith.TwoAdic

namespace Chi2Irr
namespace QZ

open Polynomial Finset fwdDiff
open scoped Nat

/-! ### Linearity of `Λ_X` at `ζ` and the anchored Gram identity -/

/-- `Λ_r = A + r·B` at `ζ`, as a linear map. -/
noncomputable def LamLinZ (ζ : ℚ) (K : ℕ) (r : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (muLin (wtZ ζ)).comp ((divByMonicHom (Dpoly K)).comp (LinearMap.mulRight ℚ X)) +
    ∑ k ∈ range K, (4 * omega K k * SpartZ ζ k - 4 * r * omega K k * ζ ^ (2 * k + 1)) •
      Polynomial.leval (pole k)

lemma LamLinZ_apply (ζ : ℚ) (K : ℕ) (r : ℚ) (g : ℚ[X]) :
    LamLinZ ζ K r g = AfunZ ζ K g + r * BfunZ ζ K g := by
  unfold LamLinZ AfunZ BfunZ
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, divByMonicHom_apply, muLin_apply]
  simp only [LinearMap.smul_apply, Polynomial.leval_apply, smul_eq_mul]
  rw [add_assoc]
  congr 1
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  ring

lemma AfunZ_add (ζ : ℚ) (K : ℕ) (f g : ℚ[X]) : AfunZ ζ K (f + g) = AfunZ ζ K f + AfunZ ζ K g := by
  have := (LamLinZ ζ K 0).map_add f g
  simpa only [LamLinZ_apply, zero_mul, add_zero] using this

lemma AfunZ_smul (ζ : ℚ) (K : ℕ) (c : ℚ) (f : ℚ[X]) : AfunZ ζ K (c • f) = c * AfunZ ζ K f := by
  have := (LamLinZ ζ K 0).map_smul c f
  simpa only [LamLinZ_apply, zero_mul, add_zero, smul_eq_mul] using this

lemma BfunZ_eq_LamLin (ζ : ℚ) (K : ℕ) (g : ℚ[X]) : BfunZ ζ K g = LamLinZ ζ K 1 g - LamLinZ ζ K 0 g := by
  simp only [LamLinZ_apply]; ring

lemma BfunZ_add (ζ : ℚ) (K : ℕ) (f g : ℚ[X]) : BfunZ ζ K (f + g) = BfunZ ζ K f + BfunZ ζ K g := by
  simp only [BfunZ_eq_LamLin, map_add]; ring

lemma BfunZ_smul (ζ : ℚ) (K : ℕ) (c : ℚ) (f : ℚ[X]) : BfunZ ζ K (c • f) = c * BfunZ ζ K f := by
  simp only [BfunZ_eq_LamLin, map_smul, smul_eq_mul]; ring

/-- `Λ_X(g) = A(g) + X B(g)` at `ζ`, as a `ℚ`-linear map `ℚ[X] → ℚ[X]`. -/
noncomputable def LamPZ (ζ : ℚ) (K : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun g := C (AfunZ ζ K g) + X * C (BfunZ ζ K g)
  map_add' f g := by simp only [AfunZ_add, BfunZ_add, map_add]; ring
  map_smul' c f := by
    rw [AfunZ_smul, BfunZ_smul, RingHom.id_apply, smul_eq_C_mul, map_mul, map_mul]; ring

lemma LamPZ_apply (ζ : ℚ) (K : ℕ) (g : ℚ[X]) : LamPZ ζ K g = C (AfunZ ζ K g) + X * C (BfunZ ζ K g) := rfl

/-- The monomial matrix `H_{de} = Λ_X(X^{d+e})` at `ζ`. -/
noncomputable def HPmZ (ζ : ℚ) (h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] :=
  fun d e => LamPZ ζ h (X ^ ((d : ℕ) + e))

lemma HPmZ_eq (ζ : ℚ) (h : ℕ) : HPmZ ζ h = (X : ℚ[X]) • (BmatZ ζ h).map C + (AmatZ ζ h).map C := by
  ext d e
  simp only [HPmZ, LamPZ_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    AmatZ, BmatZ]
  ring_nf

theorem Gram2Z_eq (ζ : ℚ) {h : ℕ} (a b : Fin h → ℚ[X]) (ha : ∀ i, (a i).natDegree < h)
    (hb : ∀ i, (b i).natDegree < h) :
    Matrix.of (fun i j => LamPZ ζ h (a i * b j)) =
      (CoefM a).map C * HPmZ ζ h * ((CoefM b).map C).transpose := by
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
  simp only [HPmZ]
  ring

/-- `Δ_h(X; ζ)` is the determinant of the anchored Gram matrix. -/
theorem DeltaZ_eq_anchored (ζ : ℚ) (h : ℕ) :
    DeltaZ ζ h = (Matrix.of (fun i j : Fin h => LamPZ ζ h (aB i * bB h j))).det := by
  have hda : ∀ i : Fin h, (aB i).natDegree = i := fun i => by
    unfold aB; rw [natDegree_prod_pole, card_range]
  have hdb : ∀ j : Fin h, (bB h j).natDegree = j := fun j => by
    unfold bB; rw [natDegree_prod_pole, Nat.card_Ico]; have := j.isLt; omega
  rw [Gram2Z_eq ζ (fun i => aB i) (fun j => bB h j) (fun i => by rw [hda]; exact i.isLt)
    (fun j => by rw [hdb]; exact j.isLt), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_map_C, det_map_C, det_CoefM_monic _ hda (fun i => monic_prod_pole _),
    det_CoefM_monic _ hdb (fun j => monic_prod_pole _), map_one, one_mul, mul_one, HPmZ_eq]
  rfl

/-! ### Case (L): `i + j ≥ K` -/

lemma AfunZ_L {ζ : ℚ} {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    AfunZ ζ K (aB i * bB K j) = muPoly (wtZ ζ) ((∏ m ∈ Ico (K - j) i, (X - C (pole m))) * X) := by
  unfold AfunZ
  rw [aB_mul_bB_L hi hj hij, mul_assoc, mul_divByMonic_cancel_left _ (Dpoly_monic K)]
  have : ∑ k ∈ range K, (Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) * omega K k *
      SpartZ ζ k = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; ring
  rw [this, mul_zero, add_zero]

lemma BfunZ_L {ζ : ℚ} {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    BfunZ ζ K (aB i * bB K j) = 0 := by
  unfold BfunZ
  rw [aB_mul_bB_L hi hj hij]
  have : ∑ k ∈ range K, (Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) * omega K k *
      ζ ^ (2 * k + 1) = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; ring
  rw [this, mul_zero]

/-! ### Valuations at `ζ = q/2` -/

lemma one_lt_zq {q : ℕ} (hq : 3 ≤ q) : 1 < zq q := by
  unfold zq
  have : (3 : ℚ) ≤ q := by exact_mod_cast hq
  rw [lt_div_iff₀ (by norm_num)]; linarith

lemma V2_zq {q : ℕ} : V2 (-1) (zq q) := by
  unfold zq
  have := V2_div_of_norm (V2_natCast q) padicNorm_two_self
  simpa using this

lemma E_zq {q : ℕ} (hq : 3 ≤ q) : 1 / (zq q ^ 2 - 1) = 4 / (((q ^ 2 - 4 : ℕ)) : ℚ) := by
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  rw [Nat.cast_sub h4]
  unfold zq
  push_cast
  have e : ((q : ℚ) / 2) ^ 2 - 1 = ((q : ℚ) ^ 2 - 4) / 4 := by ring
  rw [e, one_div_div]

lemma odd_qsq_sub_four {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) : Odd (q ^ 2 - 4) :=
  Nat.Odd.sub_even (by nlinarith) (ho.pow) (by decide)

lemma V2_E {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) : V2 2 (1 / (zq q ^ 2 - 1)) := by
  rw [E_zq hq]; exact V2_div_odd V2_four (odd_qsq_sub_four hq ho)

lemma V2_OmegaZ {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (b : ℕ) : V2 0 (evZ (zq q) (OmegaF b)) := by
  unfold OmegaF
  split_ifs with hb
  · rw [evZ_E]; exact V2_mono (by norm_num) (V2_E hq ho)
  · rw [map_mul, map_pow, map_pow, evZ_q, evZ_E]
    refine V2_mul' (V2_pow V2_zq 2) (V2_pow (V2_E hq ho) (b + 1)) ?_
    push_cast; omega

/-- **(L) bound.** If `R = 2^{−n} H(2X)` with `H` 2-integral (`ℤ₍₂₎[X]`, the predicate `IS n R`) of degree `≤ n`, then `v₂(μ(R)) ≥ −n` at `ζ = q/2`. -/
theorem V2_muPolyZ {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {n : ℕ} {R : ℚ[X]} (hR : IS n R) :
    V2 (-(n : ℤ)) (muPoly (wtZ (zq q)) R) := by
  unfold muPoly
  rw [sum_over_range _ (fun d => by simp)]
  refine V2_sum _ _ (fun d _ => ?_)
  rcases Nat.lt_or_ge n d with hd | hd
  · rw [(hR d).2 hd, zero_mul]; exact V2_zero _
  rw [← evZ_muMonoF (one_lt_zq hq), muMonoF, map_sum, mul_sum]
  refine V2_sum _ _ (fun b _ => ?_)
  rw [map_mul, evZ_C]
  have hc : V2 0 ((d : ℚ) * (dCoef (d - 1) b : ℚ)) := by
    have := V2_mul (V2_natCast d) (V2_intCast (dCoef (d - 1) b)); simpa using this
  refine V2_mul' (hR d).1 (V2_mul hc (V2_OmegaZ hq ho b)) ?_
  omega

/-- The (L) entry `A`. -/
theorem V2_A_LZ {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K)
    (hij : K ≤ i + j) : V2 (-((i + j + 1 - K : ℕ) : ℤ)) (AfunZ (zq q) K (aB i * bB K j)) := by
  rw [AfunZ_L hi hj hij]
  have := IS_mul (IS_prod (Ico (K - j) i)) IS_X
  rw [Nat.card_Ico, show i - (K - j) + 1 = i + j + 1 - K by omega] at this
  exact V2_muPolyZ hq ho this

/-! ### Case (U): `i + j < K` -/

lemma muPoly_U_w (w : ℚ) {K i j : ℕ} (hij : i + j < K) :
    muPoly w ((aB i * bB K j * X) /ₘ Dpoly K) = 0 := by
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
  rw [eq_C_of_natDegree_eq_zero hdeg, muPoly, sum_C_index (by simp)]
  simp [muMono]

lemma AfunZ_U {ζ : ℚ} {K i j : ℕ} (hij : i + j < K) :
    AfunZ ζ K (aB i * bB K j) =
      4 * ∑ k ∈ range K, (aB i * bB K j).eval (pole k) * omega K k * SpartZ ζ k := by
  unfold AfunZ; rw [muPoly_U_w _ hij, zero_add]

lemma BfunZ_U {ζ : ℚ} {K i j : ℕ} (_hij : i + j < K) :
    BfunZ ζ K (aB i * bB K j) =
      -(4 * ∑ k ∈ range K, (aB i * bB K j).eval (pole k) * omega K k * ζ ^ (2 * k + 1)) := by
  unfold BfunZ; ring

/-- The pole part in case (U), by the naive expansion of `Δ^N`: if `v₂(x_{i+l} Y(i+l)) ≥ e − 2l`, then
`v₂(4 Σ_k (a_i b_j)(x_k) ω_k Y(k)) ≥ e + 2 − 3N`. -/
lemma V2_fourSum_U {K i j : ℕ} (hij : i + j < K) (Y : ℕ → ℚ) {e : ℤ}
    (hY : ∀ l : ℕ, V2 (e - 2 * l) (pole (i + l) * Y (i + l))) :
    V2 (e + 2 - 3 * ((K - 1 - i - j : ℕ) : ℤ))
      (4 * ∑ k ∈ range K, (aB i * bB K j).eval (pole k) * omega K k * Y k) := by
  set N := K - 1 - i - j with hN
  have key : 4 * ∑ k ∈ range K, (aB i * bB K j).eval (pole k) * omega K k * Y k =
      4 / ((N ! : ℕ) : ℚ) * ∑ l ∈ range (N + 1),
        (-1 : ℚ) ^ l * (N.choose l : ℚ) * (pole (i + l) * Y (i + l)) := by
    rw [sum_U hij Y, ← fd_sum_eq]; ring
  rw [key]
  have hs : V2 (e - 2 * N) (∑ l ∈ range (N + 1),
      (-1 : ℚ) ^ l * (N.choose l : ℚ) * (pole (i + l) * Y (i + l))) := by
    refine V2_sum _ _ (fun l hl => ?_)
    have hl' : l ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hl)
    have h1 : V2 0 ((-1 : ℚ) ^ l * (N.choose l : ℚ)) := by
      have := V2_mul (V2_pow (V2_neg V2_one) l) (V2_natCast (N.choose l)); simpa using this
    exact V2_mul' h1 (hY l) (by omega)
  have hv := vf_le N
  exact V2_mul' (V2_div_factorial V2_four N) hs (by omega)

lemma V2_pole (m : ℕ) : V2 (-1) (pole m) := by
  rw [pole_eq_odd]
  have := V2_neg (V2_div_of_norm (V2_natCast (2 * m + 1)) padicNorm_two_self)
  simpa using this

lemma V2_SpartZ {q : ℕ} (k : ℕ) : V2 (-2 * (k : ℤ)) (SpartZ (zq q) k) := by
  unfold SpartZ
  refine V2_sum _ _ (fun j hj => ?_)
  have hj' := mem_range.mp hj
  have : (2 * (j : ℚ) + 1) ^ 2 = (((2 * j + 1) ^ 2 : ℕ) : ℚ) := by push_cast; ring
  rw [this]
  refine V2_mono ?_ (V2_div_odd (V2_pow (V2_zq (q := q)) (2 * (k - j))) (Odd.pow (odd_two_mul_add_one j)))
  push_cast
  omega

/-- The (U) entry `A`: `v₂ ≥ −2i − 3N`. -/
theorem V2_A_UZ {q : ℕ} {K i j : ℕ} (hij : i + j < K) :
    V2 (-2 * (i : ℤ) - 3 * ((K - 1 - i - j : ℕ) : ℤ)) (AfunZ (zq q) K (aB i * bB K j)) := by
  rw [AfunZ_U hij]
  refine V2_mono (by omega) (V2_fourSum_U hij _ (e := -2 * (i : ℤ) - 2) (fun l => ?_))
  refine V2_mono ?_ (V2_mul (V2_pole (i + l)) (V2_SpartZ (q := q) (i + l)))
  push_cast; omega

/-- The (U) entry `B`: `v₂ ≥ −2i − 3N`. -/
theorem V2_B_UZ {q : ℕ} {K i j : ℕ} (hij : i + j < K) :
    V2 (-2 * (i : ℤ) - 3 * ((K - 1 - i - j : ℕ) : ℤ)) (BfunZ (zq q) K (aB i * bB K j)) := by
  rw [BfunZ_U hij]
  refine V2_neg (V2_mono (by omega) (V2_fourSum_U hij _ (e := -2 * (i : ℤ) - 2) (fun l => ?_)))
  refine V2_mono ?_ (V2_mul (V2_pole (i + l)) (V2_pow (V2_zq (q := q)) (2 * (i + l) + 1)))
  push_cast; omega

/-! ### All entries -/

/-- The cost `c(i, j)`: `2i + 3N` on (U), `π` on (L); `v₂(G_ij) ≥ −c(i, j)`. -/
def cZ (h i j : ℕ) : ℤ :=
  if i + j < h then 2 * (i : ℤ) + 3 * ((h - 1 - i - j : ℕ) : ℤ) else ((i + j + 1 - h : ℕ) : ℤ)

/-- **Entry bound (Lemma 10″).** -/
theorem V2_entryZ {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    V2 (-cZ h i j) (AfunZ (zq q) h (aB i * bB h j)) ∧ V2 (-cZ h i j) (BfunZ (zq q) h (aB i * bB h j)) := by
  unfold cZ
  split_ifs with hij
  · exact ⟨V2_mono (by omega) (V2_A_UZ hij), V2_mono (by omega) (V2_B_UZ hij)⟩
  · rw [not_lt] at hij
    exact ⟨V2_A_LZ hq ho hi.le hj.le hij, by rw [BfunZ_L hi.le hj.le hij]; exact V2_zero _⟩

end QZ
end Chi2Irr
