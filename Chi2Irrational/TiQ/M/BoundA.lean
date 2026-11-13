/-
# Lemma M, part 5: bound (A) on `Em = A + θ·B` (RESULT §1 step 3 (A), finite version)

For `g = Cb i · Cb j` (`i, j < h`, `K = h`):
`Em_ij = μ(R_g) + Σ_k g(x_k) ω_k D_k` with `D_k = 4 S♮_k − 4θ (−1)^k q^{2k+1}`
`      = MB(F) + Σ_k g(x_k) ω_k (D_k − MB(f_k′))`,  `F(t) = R_g′(t) + Σ_k g(x_k) ω_k f_k′(t) = (g u/D)′(t)`.
* The error sum: `‖g(x_k)‖₂ ≤ 2^{2(i+j)}` (`Cb_pole_bound`), `‖ω_k‖₂ ≤ 2^h`, and `err_bound`.
* `MB(F)`: termwise `‖Ω_b Δ^b F(0)‖₂ ≤ 2^{b+1} ‖Δ^b F(0)‖₂`, and `‖Δ^b F(0)‖₂ ≤ 2^{i+j+1−h−b}`. Write
  `u/D(u) = 2^h u/P(2u)`, `P(T) = Π_{k<h}(T + 2k + 1)`, `P(0)` odd; with `U = 1 − P/P(0) = T·V` and
  `S_M = (1/P(0)) Σ_{m<M} U^m` one has `P S_M = 1 − T^M V^M` (coefficients in `ℤ_(2)`). So
  `g u/D = 2^h g u S_M(2u) + 2^{h+M} g u^{M+1} V(2u)^M / P(2u)`: the polynomial part is
  `Σ_m 2^{h+m} σ_m u^{m+1} g` (`σ_m ∈ ℤ_(2)`), bounded by `fd_deriv_intval` with `d = m + 1 + i + j`; the tail, with
  `M = B + 2h`, has derivative values of size `≤ 2^{2h − h − M}` at the nodes (`P(2t)` odd).
-/
import Chi2Irrational.TiQ.M.Trunc

namespace Chi2Irr
namespace TiQ
namespace M

open Polynomial Finset

/-! ### Forward differences: linearity and a pointwise bound -/

lemma bA_fd_add (b : ℕ) (f g : ℕ → ℚ) : fd b (fun t => f t + g t) = fd b f + fd b g := by
  simp only [fd_eq_sum, mul_add, sum_add_distrib]

lemma bA_fd_smul (b : ℕ) (c : ℚ) (f : ℕ → ℚ) : fd b (fun t => c * f t) = c * fd b f := by
  simp only [fd_eq_sum, mul_sum]
  refine sum_congr rfl (fun _ _ => by ring)

lemma bA_fd_sum {ι : Type*} (s : Finset ι) (b : ℕ) (c : ι → ℚ) (f : ι → ℕ → ℚ) :
    fd b (fun t => ∑ k ∈ s, c k * f k t) = ∑ k ∈ s, c k * fd b (f k) := by
  simp only [fd_eq_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))

lemma bA_fd_V2 {e : ℤ} (b : ℕ) {f : ℕ → ℚ} (hf : ∀ t, V2 e (f t)) : V2 e (fd b f) := by
  rw [fd_eq_sum]
  refine V2_sum _ _ (fun t _ => ?_)
  have h0 : V2 0 ((-1 : ℚ) ^ (b - t) * (b.choose t : ℚ)) := by
    have := V2_mul (V2_pow (V2_neg V2_one) (b - t)) (V2_natCast (b.choose t))
    simpa using this
  simpa using V2_mul h0 (hf t)

/-! ### Polynomials with `v₂(coeff n) ≥ n` -/

/-- `v₂([X^n] Q) ≥ n` for all `n`, i.e. `Q(u) = H(2u)` with `H` 2-integral. -/
def bA_Z2 (Q : ℚ[X]) : Prop := ∀ n : ℕ, V2 n (Q.coeff n)

lemma bA_Z2_add {P Q : ℚ[X]} (hP : bA_Z2 P) (hQ : bA_Z2 Q) : bA_Z2 (P + Q) :=
  fun n => by rw [coeff_add]; exact V2_add (hP n) (hQ n)

lemma bA_Z2_sub {P Q : ℚ[X]} (hP : bA_Z2 P) (hQ : bA_Z2 Q) : bA_Z2 (P - Q) :=
  fun n => by rw [coeff_sub]; exact V2_sub (hP n) (hQ n)

lemma bA_Z2_zero : bA_Z2 0 := fun n => by rw [coeff_zero]; exact V2_zero _

lemma bA_Z2_C {a : ℚ} (ha : V2 0 a) : bA_Z2 (C a) := fun n => by
  rw [coeff_C]
  split_ifs with h
  · subst h; simpa using ha
  · exact V2_zero _

lemma bA_Z2_one : bA_Z2 1 := by rw [← C_1]; exact bA_Z2_C V2_one

lemma bA_Z2_mul {P Q : ℚ[X]} (hP : bA_Z2 P) (hQ : bA_Z2 Q) : bA_Z2 (P * Q) := fun n => by
  rw [coeff_mul]
  refine V2_sum _ _ (fun x hx => ?_)
  have := mem_antidiagonal.mp hx
  refine V2_mul' (hP x.1) (hQ x.2) ?_
  rw [← this]; push_cast; rfl

lemma bA_Z2_pow {P : ℚ[X]} (hP : bA_Z2 P) (m : ℕ) : bA_Z2 (P ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact bA_Z2_one
  | succ m ih => rw [pow_succ]; exact bA_Z2_mul ih hP

lemma bA_Z2_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (hf : ∀ i ∈ s, bA_Z2 (f i)) :
    bA_Z2 (∏ i ∈ s, f i) :=
  Finset.prod_induction _ bA_Z2 (fun _ _ => bA_Z2_mul) bA_Z2_one hf

lemma bA_Z2_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (hf : ∀ i ∈ s, bA_Z2 (f i)) :
    bA_Z2 (∑ i ∈ s, f i) :=
  Finset.sum_induction _ bA_Z2 (fun _ _ => bA_Z2_add) bA_Z2_zero hf

lemma bA_Z2_C_mul {a : ℚ} (ha : V2 0 a) {Q : ℚ[X]} (hQ : bA_Z2 Q) : bA_Z2 (C a * Q) :=
  bA_Z2_mul (bA_Z2_C ha) hQ

lemma bA_Z2_two_X_add {a : ℚ} (ha : V2 0 a) : bA_Z2 (C 2 * X + C a) := by
  refine bA_Z2_add (fun n => ?_) (bA_Z2_C ha)
  rw [coeff_C_mul_X]
  split_ifs with h
  · subst h; simpa using V2_two_pow 1
  · exact V2_zero _

lemma bA_Z2_derivative {Q : ℚ[X]} (hQ : bA_Z2 Q) (n : ℕ) : V2 0 ((derivative Q).coeff n) := by
  rw [coeff_derivative]
  have h1 : V2 0 ((n : ℚ) + 1) := by exact_mod_cast V2_natCast (n + 1)
  refine V2_mul' (hQ (n + 1)) h1 ?_
  push_cast; omega

lemma bA_eval_V2 {Q : ℚ[X]} {e : ℤ} (hQ : ∀ n, V2 e (Q.coeff n)) {x : ℚ} (hx : V2 0 x) :
    V2 e (Q.eval x) := by
  rw [eval_eq_sum_range]
  refine V2_sum _ _ (fun n _ => ?_)
  refine V2_mul' (hQ n) (V2_pow hx n) ?_
  simp

/-- The key derivative bound for `G · Q` with `G` integer-valued and `Q ∈ bA_Z2`. -/
lemma bA_fd_Z2 {G : ℚ[X]} {d : ℕ} (hd : G.natDegree ≤ d) (hint : ∀ n : ℕ, ∃ z : ℤ, G.eval (n : ℚ) = z)
    {Q : ℚ[X]} (hQ : bA_Z2 Q) (b : ℕ) :
    V2 ((b : ℤ) - d) (fd b (fun t => (derivative (G * Q)).eval (t : ℚ))) := by
  have hQs : G * Q = ∑ n ∈ range (Q.natDegree + 1), C (Q.coeff n) * (G * X ^ n) := by
    conv_lhs => rw [Q.as_sum_range_C_mul_X_pow, mul_sum]
    refine sum_congr rfl (fun _ _ => by ring)
  have hfun : (fun t : ℕ => (derivative (G * Q)).eval (t : ℚ)) =
      (fun t : ℕ => ∑ n ∈ range (Q.natDegree + 1), Q.coeff n * (derivative (G * X ^ n)).eval (t : ℚ)) := by
    funext t
    rw [hQs, derivative_sum, eval_finsetSum]
    refine sum_congr rfl (fun n _ => ?_)
    rw [derivative_C_mul, eval_mul, eval_C]
  rw [hfun, bA_fd_sum]
  refine V2_sum _ _ (fun n _ => ?_)
  have hdn : (G * X ^ n).natDegree ≤ d + n :=
    (natDegree_mul_le).trans (add_le_add hd (natDegree_X_pow_le n))
  have hintn : ∀ m : ℕ, ∃ z : ℤ, (G * X ^ n : ℚ[X]).eval (m : ℚ) = (z : ℚ) := fun m => by
    obtain ⟨z, hz⟩ := hint m
    refine ⟨z * (m : ℤ) ^ n, ?_⟩
    simp only [eval_mul, eval_pow, eval_X, hz]; push_cast; ring
  have h2 : V2 ((b : ℤ) - (d + n : ℕ)) (fd b (fun t => (derivative (G * X ^ n)).eval (t : ℚ))) := by
    unfold V2
    rw [neg_sub]
    exact fd_deriv_intval hdn hintn b
  refine V2_mul' (hQ n) h2 ?_
  push_cast; omega

/-! ### Derivatives of rational functions at a point -/

/-- `(N/P)′(t) = N′(t)/P(t) − N(t)P′(t)/P(t)²`. -/
noncomputable def bA_qd (N P : ℚ[X]) (t : ℚ) : ℚ :=
  (derivative N).eval t / P.eval t - N.eval t * (derivative P).eval t / (P.eval t) ^ 2

lemma bA_qd_mul_add (A P B : ℚ[X]) {t : ℚ} (hP : P.eval t ≠ 0) :
    bA_qd (A * P + B) P t = (derivative A).eval t + bA_qd B P t := by
  unfold bA_qd
  simp only [derivative_add, derivative_mul, eval_add, eval_mul]
  field_simp
  ring

lemma bA_qd_C_mul_both {a : ℚ} (ha : a ≠ 0) (N P : ℚ[X]) (t : ℚ) :
    bA_qd (C a * N) (C a * P) t = bA_qd N P t := by
  unfold bA_qd
  simp only [derivative_C_mul, eval_mul, eval_C]
  by_cases hP : P.eval t = 0
  · simp [hP]
  · field_simp

lemma bA_qd_C_mul (a : ℚ) (N P : ℚ[X]) (t : ℚ) : bA_qd (C a * N) P t = a * bA_qd N P t := by
  unfold bA_qd
  simp only [derivative_C_mul, eval_mul, eval_C]
  ring

lemma bA_qd_sum {ι : Type*} (s : Finset ι) (c : ι → ℚ) (N : ι → ℚ[X]) (P : ℚ[X]) (t : ℚ) :
    bA_qd (∑ k ∈ s, C (c k) * N k) P t = ∑ k ∈ s, c k * bA_qd (N k) P t := by
  unfold bA_qd
  simp only [derivative_sum, derivative_C_mul, eval_finsetSum, eval_mul, eval_C]
  rw [sum_div, sum_mul, sum_div, ← sum_sub_distrib]
  refine sum_congr rfl (fun _ _ => by ring)

lemma bA_sub_pole_pos (t m : ℕ) : 0 < (t : ℚ) - pole m := by
  unfold pole
  have h1 : (0 : ℚ) ≤ t := t.cast_nonneg
  have h2 : (0 : ℚ) ≤ m := m.cast_nonneg
  linarith

lemma bA_Dpoly_eval_ne (h t : ℕ) : (Dpoly h).eval (t : ℚ) ≠ 0 := by
  unfold Dpoly
  rw [eval_prod]
  refine prod_ne_zero_iff.mpr (fun m _ => ?_)
  rw [eval_sub, eval_X, eval_C]
  exact (bA_sub_pole_pos t m).ne'

lemma bA_fpoly_eval_ne (h k t : ℕ) : (fpoly h k).eval (t : ℚ) ≠ 0 := by
  unfold fpoly
  rw [eval_prod]
  refine prod_ne_zero_iff.mpr (fun m _ => ?_)
  rw [eval_sub, eval_X, eval_C]
  exact (bA_sub_pole_pos t m).ne'

lemma bA_qd_fpoly {h k : ℕ} (hk : k < h) (t : ℕ) : bA_qd (fpoly h k) (Dpoly h) t = fk k t := by
  rw [Dpoly_eq_mul_fpoly hk]
  unfold bA_qd fk
  have h1 := (bA_sub_pole_pos t k).ne'
  have h2 := bA_fpoly_eval_ne h k t
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_mul,
    eval_add, eval_sub, eval_X, eval_C]
  field_simp
  ring

/-! ### Partial fractions -/

lemma bA_Dpoly_pole {h k : ℕ} (hk : k < h) : (Dpoly h).eval (pole k) = 0 := by
  rw [Dpoly_eq_mul_fpoly hk, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]

lemma bA_lagrange (N : ℚ[X]) (h : ℕ) :
    N %ₘ Dpoly h = ∑ k ∈ range h, C (N.eval (pole k) / dPrime h k) * fpoly h k := by
  have hcard : #((range h).image pole) = h := by
    rw [card_image_of_injective _ pole_injective, card_range]
  have hD : (Dpoly h).degree = (h : WithBot ℕ) := by
    rw [degree_eq_natDegree (Dpoly_monic h).ne_zero, natDegree_Dpoly]
  apply eq_of_degrees_lt_of_eval_finset_eq ((range h).image pole)
  · rw [hcard, ← hD]
    exact degree_modByMonic_lt N (Dpoly_monic h)
  · rw [hcard]
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro k hk
    have := natDegree_C_mul_fpoly_lt (mem_range.mp hk) (N.eval (pole k) / dPrime h k)
    rwa [hD] at this
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    have hk' := mem_range.mp hk
    have e1 : (N %ₘ Dpoly h).eval (pole k) = N.eval (pole k) := by
      conv_rhs => rw [← modByMonic_add_div N (Dpoly h)]
      rw [eval_add, eval_mul, bA_Dpoly_pole hk', zero_mul, add_zero]
    rw [e1, eval_finsetSum, sum_eq_single k]
    · rw [eval_mul, eval_C, eval_fpoly h k k hk']
      simp only [↓reduceIte]
      rw [div_mul_cancel₀ _ (dPrime_ne_zero h k)]
    · intro m _ hmk
      simp [eval_fpoly h m k hk', Ne.symm hmk]
    · intro h0; exact absurd hk h0

lemma bA_partialFrac (N : ℚ[X]) (h t : ℕ) :
    bA_qd N (Dpoly h) t = (derivative (N /ₘ Dpoly h)).eval (t : ℚ) +
      ∑ k ∈ range h, (N.eval (pole k) / dPrime h k) * fk k t := by
  have e : N = (N /ₘ Dpoly h) * Dpoly h + N %ₘ Dpoly h := by
    conv_lhs => rw [← modByMonic_add_div N (Dpoly h)]
    ring
  conv_lhs => rw [e]
  rw [bA_qd_mul_add _ _ _ (bA_Dpoly_eval_ne h t), bA_lagrange, bA_qd_sum]
  congr 1
  refine sum_congr rfl (fun k hk => ?_)
  rw [bA_qd_fpoly (mem_range.mp hk)]

/-! ### `u/D(u) = 2^h u/P(2u)` and the geometric expansion of `1/P` -/

/-- `P(2u) = 2^h D(u) = ∏_{k<h} (2u + 2k + 1)`. -/
noncomputable def bA_Pu (h : ℕ) : ℚ[X] := C ((2 : ℚ) ^ h) * Dpoly h

lemma bA_Pu_eq (h : ℕ) : bA_Pu h = ∏ k ∈ range h, (C 2 * X + C (2 * (k : ℚ) + 1)) := by
  unfold bA_Pu Dpoly
  have e : C ((2 : ℚ) ^ h) = ∏ _k ∈ range h, C (2 : ℚ) := by rw [prod_const, card_range, C_pow]
  rw [e, ← prod_mul_distrib]
  refine prod_congr rfl (fun k _ => ?_)
  have e2 : (2 : ℚ) * pole k = -(2 * (k : ℚ) + 1) := by unfold pole; ring
  rw [mul_sub, ← C_mul, e2, C_neg, sub_neg_eq_add]

lemma bA_Pu_Z2 (h : ℕ) : bA_Z2 (bA_Pu h) := by
  rw [bA_Pu_eq]
  refine bA_Z2_prod _ _ (fun k _ => bA_Z2_two_X_add ?_)
  have := V2_natCast (2 * k + 1)
  push_cast at this
  exact this

lemma bA_Pu_eval_norm (h t : ℕ) : padicNorm 2 ((bA_Pu h).eval (t : ℚ)) = 1 := by
  rw [bA_Pu_eq, eval_prod, padicNorm_prod']
  refine prod_eq_one (fun k _ => ?_)
  simp only [eval_add, eval_mul, eval_C, eval_X]
  have := padicNorm_two_odd (n := 2 * t + 2 * k + 1) ⟨t + k, by ring⟩
  push_cast at this
  rw [← add_assoc]
  exact this

lemma bA_Pu_eval_ne (h t : ℕ) : (bA_Pu h).eval (t : ℚ) ≠ 0 := fun h0 => by
  have := bA_Pu_eval_norm h t
  rw [h0, padicNorm.zero] at this
  exact zero_ne_one this

/-- `P(0) = ∏ (2k+1)`, odd. -/
noncomputable def bA_cc (h : ℕ) : ℚ := (bA_Pu h).eval 0

lemma bA_cc_norm (h : ℕ) : padicNorm 2 (bA_cc h) = 1 := by
  have := bA_Pu_eval_norm h 0
  rwa [Nat.cast_zero] at this

lemma bA_cc_ne (h : ℕ) : bA_cc h ≠ 0 := by
  have := bA_Pu_eval_ne h 0
  rwa [Nat.cast_zero] at this

lemma bA_V2_div_unit {e : ℤ} {x y : ℚ} (hx : V2 e x) (hy : padicNorm 2 y = 1) : V2 e (x / y) := by
  have := V2_div_of_norm (k := 0) hx (by rw [hy]; simp)
  simpa using this

/-- `U = 1 − P/P(0)`. -/
noncomputable def bA_Uu (h : ℕ) : ℚ[X] := 1 - C (bA_cc h)⁻¹ * bA_Pu h

/-- `S_M = P(0)⁻¹ Σ_{m<M} U^m`. -/
noncomputable def bA_S (h M : ℕ) : ℚ[X] := C (bA_cc h)⁻¹ * ∑ m ∈ range M, bA_Uu h ^ m

lemma bA_cc_inv_V2 (h : ℕ) : V2 0 (bA_cc h)⁻¹ := by
  have := bA_V2_div_unit V2_one (bA_cc_norm h)
  simpa using this

lemma bA_Uu_Z2 (h : ℕ) : bA_Z2 (bA_Uu h) :=
  bA_Z2_sub bA_Z2_one (bA_Z2_C_mul (bA_cc_inv_V2 h) (bA_Pu_Z2 h))

lemma bA_S_Z2 (h M : ℕ) : bA_Z2 (bA_S h M) :=
  bA_Z2_C_mul (bA_cc_inv_V2 h) (bA_Z2_sum _ _ (fun m _ => bA_Z2_pow (bA_Uu_Z2 h) m))

lemma bA_Uu_coeff_zero (h : ℕ) : (bA_Uu h).coeff 0 = 0 := by
  unfold bA_Uu
  rw [coeff_sub, coeff_one_zero, coeff_C_mul, coeff_zero_eq_eval_zero]
  change 1 - (bA_cc h)⁻¹ * bA_cc h = 0
  rw [inv_mul_cancel₀ (bA_cc_ne h), sub_self]

lemma bA_Uu_V2_one (h n : ℕ) : V2 1 ((bA_Uu h).coeff n) := by
  rcases n with _ | n
  · rw [bA_Uu_coeff_zero]; exact V2_zero _
  · exact V2_mono (by push_cast; omega) (bA_Uu_Z2 h (n + 1))

lemma bA_Pu_mul_S (h M : ℕ) : bA_Pu h * bA_S h M = 1 - bA_Uu h ^ M := by
  have hcc := bA_cc_ne h
  have hP : bA_Pu h = C (bA_cc h) * (1 - bA_Uu h) := by
    unfold bA_Uu
    rw [sub_sub_cancel, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hcc, C_1, one_mul]
  unfold bA_S
  rw [hP]
  calc C (bA_cc h) * (1 - bA_Uu h) * (C (bA_cc h)⁻¹ * ∑ m ∈ range M, bA_Uu h ^ m)
      = C (bA_cc h * (bA_cc h)⁻¹) * ((1 - bA_Uu h) * ∑ m ∈ range M, bA_Uu h ^ m) := by
        rw [C_mul]; ring
    _ = 1 - bA_Uu h ^ M := by rw [mul_inv_cancel₀ hcc, C_1, one_mul, mul_neg_geom_sum]

/-! ### The tail `2^h G U^M / P(2u)` -/

lemma bA_tail_V2 {h M : ℕ} (hM : 1 ≤ M) {G : ℚ[X]} {t : ℕ} (hG0 : V2 0 (G.eval (t : ℚ)))
    (hG1 : V2 (-(2 * (h : ℤ))) ((derivative G).eval (t : ℚ))) :
    V2 ((M : ℤ) - 2 * h - 1) (bA_qd (G * bA_Uu h ^ M) (bA_Pu h) t) := by
  have hU : V2 1 ((bA_Uu h).eval (t : ℚ)) := bA_eval_V2 (bA_Uu_V2_one h) (V2_natCast t)
  have hU' : V2 0 ((derivative (bA_Uu h)).eval (t : ℚ)) :=
    bA_eval_V2 (bA_Z2_derivative (bA_Uu_Z2 h)) (V2_natCast t)
  have hP' : V2 0 ((derivative (bA_Pu h)).eval (t : ℚ)) :=
    bA_eval_V2 (bA_Z2_derivative (bA_Pu_Z2 h)) (V2_natCast t)
  have hPn := bA_Pu_eval_norm h t
  have hPn2 : padicNorm 2 (((bA_Pu h).eval (t : ℚ)) ^ 2) = 1 := by rw [sq, padicNorm.mul, hPn, one_mul]
  have hUM := V2_pow hU M
  have hUM1 := V2_pow hU (M - 1)
  unfold bA_qd
  simp only [derivative_mul, derivative_pow, eval_add, eval_mul, eval_pow, eval_C]
  refine V2_sub (bA_V2_div_unit (V2_add ?_ ?_) hPn) (bA_V2_div_unit ?_ hPn2)
  · exact V2_mul' hG1 hUM (by omega)
  · refine V2_mul' hG0 (V2_mul' (V2_mul' (V2_natCast M) hUM1 le_rfl) hU' le_rfl) ?_
    omega
  · exact V2_mul' (V2_mul' hG0 hUM le_rfl) hP' (by omega)

/-! ### `ω_k` -/

lemma bA_dPrime_eq {h k : ℕ} (hk : k < h) :
    dPrime h k = (-1 : ℚ) ^ k * ((k.factorial : ℕ) : ℚ) * (((h - 1 - k).factorial : ℕ) : ℚ) := by
  unfold dPrime
  have hsplit : (range h).erase k = range k ∪ Ico (k + 1) h := by
    ext m; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range k) (Ico (k + 1) h) := by
    rw [disjoint_left]; intro m h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
  have hp : ∀ m, pole k - pole m = (m : ℚ) - k := fun m => by unfold pole; ring
  rw [hsplit, prod_union hdisj]
  simp_rw [hp]
  have hL : ∏ m ∈ range k, ((m : ℚ) - k) = (-1 : ℚ) ^ k * ((k.factorial : ℕ) : ℚ) := by
    rw [← prod_range_reflect, ← prod_range_add_one_eq_factorial, Nat.cast_prod,
      show (-1 : ℚ) ^ k = ∏ _j ∈ range k, (-1 : ℚ) by rw [prod_const, card_range], ← prod_mul_distrib]
    refine prod_congr rfl (fun j hj => ?_)
    have := mem_range.mp hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hR : ∏ m ∈ Ico (k + 1) h, ((m : ℚ) - k) = (((h - 1 - k).factorial : ℕ) : ℚ) := by
    rw [prod_Ico_eq_prod_range, show h - (k + 1) = h - 1 - k by omega, ← prod_range_add_one_eq_factorial,
      Nat.cast_prod]
    refine prod_congr rfl (fun j _ => ?_)
    push_cast; ring
  rw [hL, hR]

lemma bA_omega_V2 {h k : ℕ} (hk : k < h) : V2 (-(h : ℤ)) (omega h k) := by
  unfold omega
  have hpole : V2 (-1) (pole k) := by
    have e : pole k = -(((2 * k + 1 : ℕ) : ℚ)) / 2 := by unfold pole; push_cast; ring
    rw [e]
    have := V2_div_of_norm (V2_neg (V2_natCast (2 * k + 1))) padicNorm_two_self
    simpa using this
  have hnorm : padicNorm 2 (dPrime h k) = (2 : ℚ) ^ (-((vf k + vf (h - 1 - k) : ℕ) : ℤ)) := by
    rw [bA_dPrime_eq hk, padicNorm.mul, padicNorm.mul, padicNorm_factorial, padicNorm_factorial]
    have h1 : padicNorm 2 ((-1 : ℚ) ^ k) = 1 := by
      rcases neg_one_pow_eq_or ℚ k with h | h <;> simp [h]
    rw [h1, one_mul, ← zpow_add₀ two_ne_zero]
    push_cast; ring_nf
  have := V2_div_of_norm hpole hnorm
  refine V2_mono ?_ this
  have h1 := vf_le k
  have h2 := vf_le (h - 1 - k)
  push_cast
  omega

/-! ### Linearity of `MB` -/

lemma bA_MB_lin (q B : ℕ) {ι : Type*} (s : Finset ι) (f : ℕ → ℚ) (c : ι → ℚ) (g : ι → ℕ → ℚ) :
    MB q B (fun t => f t + ∑ k ∈ s, c k * g k t) = MB q B f + ∑ k ∈ s, c k * MB q B (g k) := by
  unfold MB
  simp only [bA_fd_add, bA_fd_sum, mul_add, sum_add_distrib, mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))

/-! ### The derivative values `F(t) = (g u/D)′(t)`, split into polynomial part and tail -/

lemma bA_F_decomp (g : ℚ[X]) (h M t : ℕ) :
    (derivative ((g * X) /ₘ Dpoly h)).eval (t : ℚ) + ∑ k ∈ range h, (g.eval (pole k) * omega h k) * fk k t =
      (2 : ℚ) ^ h * (derivative (g * X * bA_S h M)).eval (t : ℚ) +
        (2 : ℚ) ^ h * bA_qd (g * X * bA_Uu h ^ M) (bA_Pu h) t := by
  have hsum : ∑ k ∈ range h, ((g * X).eval (pole k) / dPrime h k) * fk k t =
      ∑ k ∈ range h, (g.eval (pole k) * omega h k) * fk k t := by
    refine sum_congr rfl (fun k _ => ?_)
    rw [eval_mul, eval_X, omega, mul_div_assoc]
  rw [← hsum, ← bA_partialFrac (g * X) h t,
    ← bA_qd_C_mul_both (pow_ne_zero h (two_ne_zero : (2 : ℚ) ≠ 0)) (g * X) (Dpoly h) t]
  change bA_qd (C ((2 : ℚ) ^ h) * (g * X)) (bA_Pu h) t = _
  have hPS := bA_Pu_mul_S h M
  rw [show C ((2 : ℚ) ^ h) * (g * X) = (C ((2 : ℚ) ^ h) * (g * X * bA_S h M)) * bA_Pu h +
      C ((2 : ℚ) ^ h) * (g * X * bA_Uu h ^ M) by linear_combination (-(C ((2 : ℚ) ^ h) * (g * X))) * hPS]
  rw [bA_qd_mul_add _ _ _ (bA_Pu_eval_ne h t), bA_qd_C_mul, derivative_C_mul, eval_mul, eval_C]

/-- **Bound (A).** -/
theorem boundA {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {h : ℕ} (i j : Fin h) :
    padicNorm 2 (Em q h i j) ≤ (2 : ℚ) ^ ((i : ℤ) + j + 2 - h) := by
  have hi := i.2
  have hj := j.2
  set g : ℚ[X] := Cb i * Cb j with hg
  set B := Bt h with hB
  set M := Bt h + 2 * h + 1 with hM
  have hgint : ∀ n : ℕ, ∃ z : ℤ, g.eval (n : ℚ) = (z : ℚ) := fun n =>
    ⟨((n.choose i * n.choose j : ℕ) : ℤ), by rw [hg, eval_mul, Cb_eval_nat, Cb_eval_nat]; push_cast; ring⟩
  have hGint : ∀ n : ℕ, ∃ z : ℤ, (g * X).eval (n : ℚ) = (z : ℚ) := fun n => by
    obtain ⟨z, hz⟩ := hgint n
    exact ⟨z * n, by rw [eval_mul, eval_X, hz]; push_cast; ring⟩
  have hgdeg : g.natDegree ≤ (i : ℕ) + (j : ℕ) := natDegree_mul_le.trans (by rw [Cb_natDegree, Cb_natDegree])
  have hGdeg : (g * X).natDegree ≤ (i : ℕ) + (j : ℕ) + 1 := natDegree_mul_le.trans (add_le_add hgdeg natDegree_X_le)
  set c : ℕ → ℚ := fun k => g.eval (pole k) * omega h k with hc
  set R := (g * X) /ₘ Dpoly h with hR
  set F : ℕ → ℚ := fun t => (derivative R).eval (t : ℚ) + ∑ k ∈ range h, c k * fk k t with hF
  set e : ℕ → ℚ := fun k => 4 * SpartT q k - 4 * theta q h * poleW q k - MB q B (fk k) with he
  -- the decomposition `Em = MB(F) + Σ c_k e_k`
  have hEm : Em q h i j = MB q B F + ∑ k ∈ range h, c k * e k := by
    have hRdeg : R.natDegree ≤ B := by
      rw [hR, natDegree_divByMonic _ (Dpoly_monic h), hB, Bt]
      omega
    have h1 := MB_poly (q := q) (by omega) hRdeg
    show AfunT q h g + theta q h * BfunT q h g = _
    unfold AfunT BfunT
    rw [h1, hF, bA_MB_lin, add_assoc, add_assoc]
    congr 1
    simp only [hc, he, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    ring
  -- `Δ^b F(0)`
  have hfdF : ∀ b < B, V2 ((h : ℤ) + b - i - j - 1) (fd b F) := by
    intro b hb
    have hFeq : F = fun t : ℕ => (2 : ℚ) ^ h * (derivative (g * X * bA_S h M)).eval (t : ℚ) +
        (2 : ℚ) ^ h * bA_qd (g * X * bA_Uu h ^ M) (bA_Pu h) t := by
      funext t
      exact bA_F_decomp g h M t
    rw [hFeq, bA_fd_add, bA_fd_smul, bA_fd_smul]
    refine V2_add (V2_mul' (V2_two_pow h) (bA_fd_Z2 hGdeg hGint (bA_S_Z2 h M) b) ?_)
      (V2_mul' (V2_two_pow h) (bA_fd_V2 b (fun t => bA_tail_V2 (by omega) ?_ ?_)) ?_)
    · push_cast; omega
    · obtain ⟨z, hz⟩ := hGint t
      rw [hz]; exact V2_intCast z
    · have := deriv_intval_bound (d := 2 * h) (hGdeg.trans (by omega)) hGint t
      unfold V2; rw [neg_neg]
      exact_mod_cast this
    · rw [hB, Bt] at hb
      rw [hM, Bt]
      push_cast; omega
  have key : V2 ((h : ℤ) - i - j - 2) (Em q h i j) := by
    rw [hEm]
    refine V2_add ?_ ?_
    · unfold MB
      refine V2_sum _ _ (fun b hb => ?_)
      exact V2_mul' (V2_OmQT ho b) (hfdF b (mem_range.mp hb)) (by omega)
    · refine V2_sum _ _ (fun k hk => ?_)
      have hk' := mem_range.mp hk
      have hgk : V2 (-(2 * (i : ℤ) + 2 * j)) (g.eval (pole k)) := by
        rw [hg, eval_mul]
        refine V2_mul' (e := -(2 * (i : ℤ))) (f := -(2 * (j : ℤ))) ?_ ?_ (by omega)
        · unfold V2; rw [neg_neg]; exact Cb_pole_bound i k
        · unfold V2; rw [neg_neg]; exact Cb_pole_bound j k
      have hek : V2 (8 * (h : ℤ) + 8) (e k) := err_bound hq ho h k
      exact V2_mul' (V2_mul hgk (bA_omega_V2 hk')) hek (by omega)
  unfold V2 at key
  convert key using 2
  ring

end M
end TiQ
end Chi2Irr
