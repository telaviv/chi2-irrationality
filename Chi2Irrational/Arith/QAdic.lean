/-
# Lemma 4′: the `q`-adic order of the symbolic determinant

In `P = ℚ⟦q⟧` with `E = −(1 − q²)⁻¹` (`psiP : FR →ₐ[ℚ] P`):
* `coeff_psiP_OmegaF`: the coefficients of `Ω_b = q² E^{b+1}` (via the explicit series `Tser b = E^{b+1}`);
* `newton_back`: `f(−m) = Σ_b (−1)^b C(m+b−1, b) Δ^b f(0)` for polynomials (Newton backward);
* `coeff_psiP_muF`: the reflection `μ(R) = −Σ_m q^{2m} R′(−m)`;
* the slot decomposition of the Gram matrix modulo `q^{2M}` and Andreief give
  `ord_q Δ^P_h ≥ aQ h = (h(h−1) − 6h)/3` (`ord_DeltaP`).
-/
import Chi2Irrational.Arith.PoleOrder
import Chi2Irrational.Arith.Lemma9
import Chi2Irrational.Analytic.Andreief

namespace Chi2Irr

open Finset
open scoped Polynomial

/-! ### Power series -/

local notation "P" => PowerSeries ℚ

/-- `E^{b+1} = Σ_n [n even] (−1)^{b+1} C(n/2 + b, b) q^n`. -/
noncomputable def Tser (b : ℕ) : P :=
  PowerSeries.mk (fun n => if Even n then (-1 : ℚ) ^ (b + 1) * ((n / 2 + b).choose b : ℚ) else 0)

/-- `E = −(1 − q²)⁻¹`. -/
noncomputable def EP : P := Tser 0

lemma coeff_mul_q2_sub_one (F : P) (n : ℕ) :
    PowerSeries.coeff n (F * (PowerSeries.X ^ 2 - 1)) =
      (if 2 ≤ n then PowerSeries.coeff (n - 2) F else 0) - PowerSeries.coeff n F := by
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']

lemma coeff_Tser (b n : ℕ) : PowerSeries.coeff n (Tser b) =
    if Even n then (-1 : ℚ) ^ (b + 1) * ((n / 2 + b).choose b : ℚ) else 0 := by
  unfold Tser; rw [PowerSeries.coeff_mk]

lemma even_sub_two {n : ℕ} (hn : 2 ≤ n) : Even (n - 2) ↔ Even n := by
  constructor
  · intro h; have := h.add even_two; rwa [Nat.sub_add_cancel hn] at this
  · intro h; exact (Nat.even_sub hn).mpr (by simp [h])

lemma Tser_zero_mul : Tser 0 * (PowerSeries.X ^ 2 - 1) = 1 := by
  ext n
  rw [coeff_mul_q2_sub_one, PowerSeries.coeff_one]
  simp only [coeff_Tser, Nat.even_iff, zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one, mul_one]
  split_ifs <;> first | ring1 | (exfalso; omega)

lemma Tser_succ_mul (b : ℕ) : Tser (b + 1) * (PowerSeries.X ^ 2 - 1) = Tser b := by
  ext n
  rw [coeff_mul_q2_sub_one]
  simp only [coeff_Tser, Nat.even_iff]
  by_cases hn : 2 ≤ n
  · by_cases he : n % 2 = 0
    · have he2 : (n - 2) % 2 = 0 := by omega
      simp only [hn, he, he2, ite_true]
      obtain ⟨c, hc⟩ : ∃ c, n / 2 = c + 1 := ⟨n / 2 - 1, by omega⟩
      have hn2 : (n - 2) / 2 = c := by omega
      rw [hn2, hc]
      have pascal : ((c + 1 + (b + 1)).choose (b + 1) : ℚ) =
          ((c + (b + 1)).choose (b + 1) : ℚ) + ((c + 1 + b).choose b : ℚ) := by
        rw [show c + 1 + (b + 1) = (c + 1 + b) + 1 by ring, Nat.choose_succ_succ',
          add_comm ((c + 1 + b).choose b)]
        push_cast
        rw [show c + 1 + b = c + (b + 1) by ring]
      rw [pascal]
      ring
    · have he2 : ¬ (n - 2) % 2 = 0 := by omega
      simp only [hn, he, he2, ite_true, ite_false]; ring
  · simp only [hn, ite_false]
    interval_cases n
    · simp only [Nat.zero_mod, ite_true, Nat.zero_div, zero_add, Nat.choose_self, Nat.cast_one, mul_one]
      ring
    · simp

lemma Tser_mul_pow (b : ℕ) : Tser b * (PowerSeries.X ^ 2 - 1) ^ (b + 1) = 1 := by
  induction b with
  | zero => simpa using Tser_zero_mul
  | succ b ih => rw [pow_succ', ← mul_assoc, Tser_succ_mul, ih]

lemma EP_pow (b : ℕ) : EP ^ (b + 1) = Tser b := by
  have h1 : EP ^ (b + 1) * (PowerSeries.X ^ 2 - 1) ^ (b + 1) = 1 := by
    rw [← mul_pow]; unfold EP; rw [Tser_zero_mul, one_pow]
  have h2 := Tser_mul_pow b
  calc EP ^ (b + 1) = EP ^ (b + 1) * (Tser b * (PowerSeries.X ^ 2 - 1) ^ (b + 1)) := by rw [h2, mul_one]
    _ = (EP ^ (b + 1) * (PowerSeries.X ^ 2 - 1) ^ (b + 1)) * Tser b := by ring
    _ = Tser b := by rw [h1, one_mul]

lemma EP_mul : EP * (PowerSeries.X ^ 2 - 1) = 1 := Tser_zero_mul

/-- The specialization `q ↦ q`, `E ↦ −(1 − q²)⁻¹`. -/
noncomputable def psiP : FR →ₐ[ℚ] P := MvPolynomial.aeval ![PowerSeries.X, EP]

lemma psiP_q : psiP qF = PowerSeries.X := by simp [psiP, qF]

lemma psiP_E : psiP EF = EP := by simp [psiP, EF]

lemma coeff_psiP_OmegaF (b n : ℕ) :
    PowerSeries.coeff n (psiP (OmegaF b)) =
      if Even n then -(-1 : ℚ) ^ b * ((n / 2 + b - 1).choose b : ℚ) else 0 := by
  unfold OmegaF
  split_ifs with hb he he
  · subst hb; rw [psiP_E]; unfold EP Tser
    simp only [PowerSeries.coeff_mk, ite_eq_left he]; simp
  · subst hb; rw [psiP_E]; unfold EP Tser
    simp only [PowerSeries.coeff_mk, ite_eq_right he]
  · rw [map_mul, map_pow, map_pow, psiP_q, psiP_E, EP_pow, mul_comm, PowerSeries.coeff_mul_X_pow']
    unfold Tser
    simp only [PowerSeries.coeff_mk]
    split_ifs with h2 h3
    · have : (n - 2) / 2 + b = n / 2 + b - 1 := by obtain ⟨c, rfl⟩ := he; omega
      rw [this]; ring
    · exact absurd ((Nat.even_sub h2).mpr (by simp [he])) h3
    · have hn : n = 0 := by obtain ⟨c, rfl⟩ := he; omega
      subst hn
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rw [map_mul, map_pow, map_pow, psiP_q, psiP_E, EP_pow, mul_comm, PowerSeries.coeff_mul_X_pow']
    unfold Tser
    simp only [PowerSeries.coeff_mk]
    split_ifs with h2 h3
    · exact absurd (by have := h3.add even_two; rwa [Nat.sub_add_cancel h2] at this) he
    · rfl
    · rfl


/-! ### Newton backward differences -/

local notation "Δq" => fwdDiff (1 : ℚ)

lemma fwdDiff_iter_shift (F : ℚ → ℚ) (b : ℕ) (y : ℚ) :
    (Δq)^[b] F (y + 1) = (Δq)^[b] F y + (Δq)^[b + 1] F y := by
  rw [Function.iterate_succ_apply']
  simp only [fwdDiff]
  ring

/-- **Newton backward.** If `Δ^{n+1} F = 0` then `F(−m) = Σ_{b≤n} (−1)^b C(m+b−1, b) Δ^b F(0)`. -/
lemma newton_back (n : ℕ) : ∀ (m : ℕ) (F : ℚ → ℚ), (Δq)^[n + 1] F = 0 →
    F (-(m : ℚ)) = ∑ b ∈ range (n + 1), (-1 : ℚ) ^ b * ((m + b - 1).choose b : ℚ) * (Δq)^[b] F 0 := by
  intro m
  induction m with
  | zero =>
    intro F _
    rw [sum_range_succ']
    rw [sum_eq_zero (fun b _ => by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
    simp
  | succ m ih =>
    intro F hF
    set G : ℚ → ℚ := fun y => F (y + -1) with hG
    have hGF : ∀ y, F y = G (y + 1) := fun y => by simp [hG]
    have hGit : ∀ b y, (Δq)^[b] F y = (Δq)^[b] G (y + 1) := by
      intro b y
      have hFG : F = fun y => G (y + 1) := funext hGF
      rw [hFG, fwdDiff_iter_comp_add]
    have hGN : (Δq)^[n + 1] G = 0 := by
      funext y
      have := fwdDiff_iter_comp_add (h := (1 : ℚ)) F (-1) (n + 1) y
      simp only [hG]
      rw [this, hF]; rfl
    have hfirst : F (-((m + 1 : ℕ) : ℚ)) = G (-(m : ℚ)) := by
      rw [hGF]; congr 1; push_cast; ring
    rw [hfirst, ih G hGN]
    -- rewrite `Δ^b F(0) = Δ^b G(0) + Δ^{b+1} G(0)`
    have hsplit : ∀ b, (Δq)^[b] F 0 = (Δq)^[b] G 0 + (Δq)^[b + 1] G 0 := fun b => by
      rw [hGit, zero_add, ← fwdDiff_iter_shift G b 0, zero_add]
    simp_rw [hsplit, mul_add, sum_add_distrib]
    have hlast : (Δq)^[n + 1] G 0 = 0 := by rw [hGN]; rfl
    rw [sum_range_succ (fun b => (-1 : ℚ) ^ b * (((m + 1 + b - 1).choose b : ℕ) : ℚ) * (Δq)^[b + 1] G 0), hlast,
      mul_zero, add_zero, sum_range_succ' (fun b => (-1 : ℚ) ^ b * (((m + 1 + b - 1).choose b : ℕ) : ℚ) * (Δq)^[b] G 0),
      sum_range_succ' (fun b => (-1 : ℚ) ^ b * (((m + b - 1).choose b : ℕ) : ℚ) * (Δq)^[b] G 0)]
    have hpas : ∀ b : ℕ, (((m + 1 + (b + 1) - 1).choose (b + 1) : ℕ) : ℚ) =
        (((m + 1 + b - 1).choose b : ℕ) : ℚ) + (((m + (b + 1) - 1).choose (b + 1) : ℕ) : ℚ) := by
      intro b
      rw [show m + 1 + (b + 1) - 1 = (m + b) + 1 by omega, Nat.choose_succ_succ',
        show m + 1 + b - 1 = m + b by omega, show m + (b + 1) - 1 = m + b by omega]
      push_cast; ring
    simp only [hpas]
    have h0 : (((m + 1 + 0 - 1).choose 0 : ℕ) : ℚ) = (((m + 0 - 1).choose 0 : ℕ) : ℚ) := by simp
    rw [h0]
    have key : ∑ b ∈ range n, (-1 : ℚ) ^ (b + 1) * ((((m + 1 + b - 1).choose b : ℕ) : ℚ) +
        (((m + (b + 1) - 1).choose (b + 1) : ℕ) : ℚ)) * (Δq)^[b + 1] G 0 +
        ∑ b ∈ range n, (-1 : ℚ) ^ b * (((m + 1 + b - 1).choose b : ℕ) : ℚ) * (Δq)^[b + 1] G 0 =
        ∑ b ∈ range n, (-1 : ℚ) ^ (b + 1) * (((m + (b + 1) - 1).choose (b + 1) : ℕ) : ℚ) * (Δq)^[b + 1] G 0 := by
      rw [← sum_add_distrib]; exact sum_congr rfl (fun b _ => by ring)
    linarith [key]

/-- `ndF R b = Δ^b[R′](0)`. -/
lemma ndF_eq_fwdDiff (R : ℚ[X]) (b : ℕ) :
    ndF R b = (Δq)^[b] (fun x => (Polynomial.derivative R).eval x) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold ndF
  refine sum_congr rfl (fun k _ => ?_)
  rw [zsmul_eq_mul]
  simp

/-- **Reflection.** `μ(R) = −Σ_m q^{2m} R′(−m)` in `ℚ⟦q⟧`. -/
lemma coeff_psiP_muF (R : ℚ[X]) (n : ℕ) :
    PowerSeries.coeff n (psiP (muF R)) =
      if Even n then -(Polynomial.derivative R).eval (-((n / 2 : ℕ) : ℚ)) else 0 := by
  rw [muF_newton R (Nat.lt_succ_self _), map_sum, map_sum]
  have hterm : ∀ b ∈ range (R.natDegree + 1), PowerSeries.coeff n (psiP (MvPolynomial.C (ndF R b) * OmegaF b)) =
      ndF R b * (if Even n then -(-1 : ℚ) ^ b * ((n / 2 + b - 1).choose b : ℚ) else 0) := by
    intro b _
    have hC : psiP (MvPolynomial.C (ndF R b)) = algebraMap ℚ P (ndF R b) := psiP.commutes _
    rw [map_mul, hC, ← Algebra.smul_def, PowerSeries.coeff_smul, coeff_psiP_OmegaF, smul_eq_mul]
  rw [sum_congr rfl hterm]
  split_ifs with he
  · have hdeg : (Polynomial.derivative R).natDegree < R.natDegree + 1 :=
      lt_of_le_of_lt ((Polynomial.natDegree_derivative_le R).trans (Nat.sub_le _ _)) (Nat.lt_succ_self _)
    have hz : (Δq)^[R.natDegree + 1] (fun x => (Polynomial.derivative R).eval x) = 0 :=
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg
    rw [newton_back R.natDegree (n / 2) _ hz, ← sum_neg_distrib]
    refine sum_congr rfl (fun b _ => ?_)
    rw [ndF_eq_fwdDiff]; ring
  · simp


/-! ### Partial fractions and the slot values -/

open Polynomial in
lemma natDegree_Dpoly (h : ℕ) : (Dpoly h).natDegree = h := by
  unfold Dpoly
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp

open Polynomial in
/-- `g X = D · ((gX) /ₘ D) + Σ_k g(x_k) ω_k f_k`. -/
lemma gX_partial (h : ℕ) (g : ℚ[X]) :
    g * X = Dpoly h * ((g * X) /ₘ Dpoly h) + ∑ k ∈ range h, C (g.eval (pole k) * omega h k) * fpoly h k := by
  have hdec := modByMonic_add_div (g * X) (Dpoly h)
  suffices hrem : (g * X) %ₘ Dpoly h = ∑ k ∈ range h, C (g.eval (pole k) * omega h k) * fpoly h k by
    rw [← hrem]; linear_combination -hdec
  have hcard : ((range h).image pole).card = h := by
    rw [card_image_of_injective _ pole_injective, card_range]
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((range h).image pole) ?_ ?_
  · rw [hcard]
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · have := degree_modByMonic_lt (g * X) (Dpoly_monic h)
      rwa [degree_eq_natDegree (Dpoly_monic h).ne_zero, natDegree_Dpoly] at this
    · refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr (fun k hk => ?_))
      refine (degree_mul_le _ _).trans_lt ?_
      have hf := natDegree_fpoly_lt (mem_range.mp hk)
      calc (C (g.eval (pole k) * omega h k)).degree + (fpoly h k).degree ≤ 0 + (fpoly h k).degree := by
            gcongr; exact degree_C_le
        _ = (fpoly h k).degree := zero_add _
        _ < h := by
            rcases eq_or_ne (fpoly h k) 0 with h0 | h0
            · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
            · rw [degree_eq_natDegree h0]; exact_mod_cast hf
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    have hk' := mem_range.mp hk
    have hroot : (Dpoly h).eval (pole k) = 0 := by
      unfold Dpoly; rw [eval_prod]; exact prod_eq_zero hk (by simp)
    have hmod : ((g * X) %ₘ Dpoly h).eval (pole k) = (g * X).eval (pole k) := by
      have := congrArg (fun F => F.eval (pole k)) hdec
      rw [eval_add, eval_mul (p := Dpoly h), hroot, zero_mul, add_zero] at this
      exact this
    rw [hmod, eval_finset_sum, sum_eq_single k]
    · rw [eval_mul, eval_mul, eval_C, eval_X, eval_fpoly h k k hk', ite_eq_left rfl, omega]
      field_simp [dPrime_ne_zero h k]
    · intro k' hk'' hne
      rw [eval_mul, eval_fpoly h k' k hk', ite_eq_right (Ne.symm hne), mul_zero]
    · intro h0; exact absurd hk h0

open Polynomial in
/-- **The slot values**: for `t` with `D(t) ≠ 0`,
`R′(t) − Σ_k g(x_k)ω_k/(t − x_k)² = g′(t) φ(t) + g(t) φ′(t)` (`φ = u/D`). -/
lemma slot_identity (h : ℕ) (g : ℚ[X]) {t : ℚ} (hD : (Dpoly h).eval t ≠ 0) :
    (derivative ((g * X) /ₘ Dpoly h)).eval t -
        ∑ k ∈ range h, g.eval (pole k) * omega h k / (t - pole k) ^ 2 =
      (derivative g).eval t * (t / (Dpoly h).eval t) +
        g.eval t * (((Dpoly h).eval t - t * (derivative (Dpoly h)).eval t) / (Dpoly h).eval t ^ 2) := by
  set R := (g * X) /ₘ Dpoly h
  set D := (Dpoly h).eval t
  set D' := (derivative (Dpoly h)).eval t
  set c : ℕ → ℚ := fun k => g.eval (pole k) * omega h k
  have hpf := gX_partial h g
  have htk : ∀ k ∈ range h, t - pole k ≠ 0 := by
    intro k hk e
    apply hD
    unfold D Dpoly; rw [eval_prod]; exact prod_eq_zero hk (by simp [show t = pole k by linarith])
  have hfk : ∀ k ∈ range h, (fpoly h k).eval t = D / (t - pole k) := by
    intro k hk
    have := congrArg (fun F => F.eval t) (Dpoly_eq_mul_fpoly (mem_range.mp hk))
    simp only [eval_mul, eval_sub, eval_X, eval_C] at this
    field_simp [htk k hk]; linarith
  have hfk' : ∀ k ∈ range h, (derivative (fpoly h k)).eval t = (D' - D / (t - pole k)) / (t - pole k) := by
    intro k hk
    have := congrArg (fun F => (derivative F).eval t) (Dpoly_eq_mul_fpoly (mem_range.mp hk))
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
      eval_mul, eval_sub, eval_X, eval_C] at this
    rw [hfk k hk] at this
    rw [eq_div_iff (htk k hk)]
    unfold D'; linarith
  -- evaluate the partial fractions and their derivative at `t`
  have e0 := congrArg (fun F => F.eval t) hpf
  have e1 := congrArg (fun F => (derivative F).eval t) hpf
  simp only [eval_mul, eval_X, eval_add, eval_finset_sum, eval_C] at e0
  simp only [derivative_mul, derivative_X, mul_one, derivative_add, derivative_sum, derivative_C, zero_mul,
    zero_add, eval_add, eval_mul, eval_X, eval_finset_sum, eval_C] at e1
  rw [sum_congr rfl (fun k hk => by rw [hfk k hk])] at e0
  rw [sum_congr rfl (fun k hk => by rw [hfk' k hk])] at e1
  set Sv := ∑ k ∈ range h, c k / (t - pole k)
  set Sd := ∑ k ∈ range h, c k / (t - pole k) ^ 2
  have hSv : ∑ k ∈ range h, c k * (D / (t - pole k)) = D * Sv := by
    rw [mul_sum]; exact sum_congr rfl (fun k _ => by ring)
  have hSd : ∑ k ∈ range h, c k * ((D' - D / (t - pole k)) / (t - pole k)) = D' * Sv - D * Sd := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun k hk => ?_)
    field_simp [htk k hk]
  have e0' : g.eval t * t = D * R.eval t + D * Sv := by rw [← hSv]; exact e0
  have e1' : (derivative g).eval t * t + g.eval t = D' * R.eval t + D * (derivative R).eval t + (D' * Sv - D * Sd) := by
    rw [← hSd]; linarith [e1]
  have key : (derivative R).eval t - Sd =
      ((derivative g).eval t * t + g.eval t - D' * (R.eval t + Sv)) / D := by
    rw [eq_div_iff hD]; linarith [e1']
  have key2 : R.eval t + Sv = g.eval t * t / D := by rw [eq_div_iff hD]; linarith [e0']
  rw [key, key2]
  field_simp
  ring


/-! ### The Gram entries as power series -/

/-- The node `t = −m`. -/
def tN (m : ℕ) : ℚ := -(m : ℚ)

open Polynomial in
lemma Dpoly_eval_tN_ne (h m : ℕ) : (Dpoly h).eval (tN m) ≠ 0 := by
  unfold Dpoly tN
  rw [eval_prod]
  refine prod_ne_zero_iff.mpr (fun k _ => ?_)
  simp only [eval_sub, eval_X, eval_C, pole]
  intro e
  have : (2 * (k : ℚ) + 1) = 2 * m := by linarith
  have h2 : ((2 * k + 1 : ℕ) : ℚ) = ((2 * m : ℕ) : ℚ) := by push_cast; linarith
  have := Nat.cast_injective h2
  omega

/-- `φ(t) = t/D(t)` and `φ′(t) = (D(t) − tD′(t))/D(t)²` at `t = −m`. -/
noncomputable def phv (h m : ℕ) : ℚ := tN m / (Dpoly h).eval (tN m)

noncomputable def phd (h m : ℕ) : ℚ :=
  ((Dpoly h).eval (tN m) - tN m * (Polynomial.derivative (Dpoly h)).eval (tN m)) / (Dpoly h).eval (tN m) ^ 2

/-- The slot value `(u^{i+j} φ)′(−m)` as a bilinear form of rank `≤ 2`. -/
noncomputable def svij (h m i j : ℕ) : ℚ :=
  phd h m * (tN m ^ i * tN m ^ j) +
    phv h m * ((i : ℚ) * tN m ^ (i - 1) * tN m ^ j + tN m ^ i * ((j : ℚ) * tN m ^ (j - 1)))

/-- The pole coefficient `c_k = x_k^{n} ω_k`. -/
noncomputable def cPole (h n k : ℕ) : ℚ := pole k ^ n * omega h k

open Polynomial in
lemma svij_eq (h m i j : ℕ) :
    svij h m i j = (derivative ((X ^ (i + j) * X : ℚ[X]) /ₘ Dpoly h)).eval (tN m) -
      ∑ k ∈ range h, cPole h (i + j) k / (tN m - pole k) ^ 2 := by
  have := slot_identity h (X ^ (i + j)) (Dpoly_eval_tN_ne h m)
  simp only [eval_pow, eval_X] at this
  unfold cPole
  rw [this]
  unfold svij phv phd
  rw [derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X]
  have hsplit : (i : ℚ) * tN m ^ (i - 1) * tN m ^ j + tN m ^ i * ((j : ℚ) * tN m ^ (j - 1)) =
      ((i + j : ℕ) : ℚ) * tN m ^ (i + j - 1) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp
    have e1 : tN m ^ (i - 1) * tN m ^ j = tN m ^ (i + j - 1) := by rw [← pow_add]; congr 1; omega
    have e2 : tN m ^ i * tN m ^ (j - 1) = tN m ^ (i + j - 1) := by rw [← pow_add]; congr 1; omega
    rw [mul_assoc, e1, mul_left_comm, e2]; push_cast; ring
  rw [hsplit, ← pow_add]
  ring

/-- `χ₂(q) = Σ_{s odd} q^s/s²`. -/
noncomputable def chiS : P := PowerSeries.mk (fun n => if Even n then 0 else 1 / (n : ℚ) ^ 2)

/-- The slot series `Σ_m −(u^{i+j}φ)′(−m) q^{2m}`. -/
noncomputable def SlotSer (h i j : ℕ) : P :=
  PowerSeries.mk (fun n => if Even n then -svij h (n / 2) i j else 0)

lemma coeff_X_pow_mul_alg (a n : ℕ) (r : ℚ) :
    PowerSeries.coeff n ((PowerSeries.X : P) ^ a * algebraMap ℚ P r) = if n = a then r else 0 := by
  rw [mul_comm, PowerSeries.coeff_mul_X_pow', Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_smul,
    PowerSeries.coeff_one, smul_eq_mul]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

lemma psiP_C (r : ℚ) : psiP (MvPolynomial.C r) = algebraMap ℚ P r := psiP.commutes r

lemma coeff_psiP_SpartF (k n : ℕ) :
    PowerSeries.coeff n (psiP (SpartF k)) =
      if Even n ∧ n / 2 ≤ k then 1 / (2 * ((k - n / 2 : ℕ) : ℚ) + 1) ^ 2 else 0 := by
  unfold SpartF
  rw [map_sum, map_sum]
  simp only [map_mul, map_pow, psiP_q, psiP_C, coeff_X_pow_mul_alg]
  split_ifs with hc
  · rw [sum_eq_single (k - n / 2)]
    · rw [ite_eq_left (by obtain ⟨⟨c, hc1⟩, hc2⟩ := hc; omega)]
    · intro j hj hne
      have hj' := mem_range.mp hj
      rw [ite_eq_right (by intro e; apply hne; obtain ⟨⟨c, hc1⟩, hc2⟩ := hc; omega)]
    · intro hn; exact absurd (mem_range.mpr (by omega)) hn
  · refine sum_eq_zero (fun j hj => ?_)
    rw [ite_eq_right]
    intro e; apply hc
    have := mem_range.mp hj
    exact ⟨⟨k - j, by omega⟩, by omega⟩


lemma psiP_four : psiP (4 : FR) = 4 := map_ofNat psiP 4

open Polynomial in
lemma psiP_B_eq (h i j : ℕ) :
    psiP (BfunF h (X ^ (i + j))) =
      -(4 * ∑ k ∈ range h, algebraMap ℚ P (cPole h (i + j) k) * PowerSeries.X ^ (2 * k + 1)) := by
  unfold BfunF cPole
  simp only [map_mul, map_neg, map_sum, map_pow, psiP_C, psiP_q, psiP_four, eval_pow, eval_X]
  ring

lemma coeff_X_pow_mul_chiS (k n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : P) ^ (2 * k + 1) * chiS) =
      if Even n ∧ k < n / 2 then 1 / ((n - 2 * k - 1 : ℕ) : ℚ) ^ 2 else 0 := by
  rw [mul_comm, PowerSeries.coeff_mul_X_pow']
  unfold chiS
  rw [PowerSeries.coeff_mk]
  by_cases hn : 2 * k + 1 ≤ n
  · rw [ite_eq_left hn]
    by_cases he : Even n
    · have hodd : ¬ Even (n - (2 * k + 1)) := by
        rw [Nat.not_even_iff_odd]; obtain ⟨c, rfl⟩ := he; exact ⟨c - k - 1, by omega⟩
      rw [ite_eq_right hodd, ite_eq_left ⟨he, by obtain ⟨c, rfl⟩ := he; omega⟩]
      congr 2 <;> omega
    · have hev : Even (n - (2 * k + 1)) := by
        rw [Nat.not_even_iff_odd] at he; obtain ⟨c, rfl⟩ := he; exact ⟨c - k, by omega⟩
      rw [ite_eq_left hev, ite_eq_right (fun h => he h.1)]
  · rw [ite_eq_right hn, ite_eq_right]
    rintro ⟨⟨c, rfl⟩, h2⟩; omega

open Polynomial in
/-- **The `A`-entries.** `ψ(A(u^{i+j})) = Σ_m −(u^{i+j}φ)′(−m) q^{2m} − 4 Σ_k c_k q^{2k+1} χ₂(q)`. -/
lemma psiP_A_eq (h i j : ℕ) :
    psiP (AfunF h (X ^ (i + j))) =
      SlotSer h i j - 4 * ∑ k ∈ range h, algebraMap ℚ P (cPole h (i + j) k) * PowerSeries.X ^ (2 * k + 1) * chiS := by
  have hA : psiP (AfunF h (X ^ (i + j))) = psiP (muF ((X ^ (i + j) * X) /ₘ Dpoly h)) +
      ∑ k ∈ range h, (4 * cPole h (i + j) k) • psiP (SpartF k) := by
    unfold AfunF
    rw [map_add, map_mul, psiP_four, map_sum, mul_sum]
    congr 1
    refine sum_congr rfl (fun k _ => ?_)
    rw [Algebra.smul_def]
    unfold cPole
    simp only [map_mul, psiP_C, eval_pow, eval_X, map_pow, map_ofNat]
    ring
  have hX : (4 : P) * ∑ k ∈ range h, algebraMap ℚ P (cPole h (i + j) k) * PowerSeries.X ^ (2 * k + 1) * chiS =
      ∑ k ∈ range h, (4 * cPole h (i + j) k) • ((PowerSeries.X : P) ^ (2 * k + 1) * chiS) := by
    rw [mul_sum]
    refine sum_congr rfl (fun k _ => ?_)
    rw [Algebra.smul_def, map_mul, show algebraMap ℚ P 4 = 4 from map_ofNat _ 4]; ring
  rw [hA, hX]
  ext n
  rw [map_add, map_sub, coeff_psiP_muF, map_sum, map_sum]
  simp only [PowerSeries.coeff_smul, smul_eq_mul, coeff_psiP_SpartF, coeff_X_pow_mul_chiS]
  unfold SlotSer
  rw [PowerSeries.coeff_mk]
  split_ifs with he
  · rw [svij_eq]
    have key : ∑ k ∈ range h, 4 * cPole h (i + j) k *
        (if Even n ∧ n / 2 ≤ k then 1 / (2 * ((k - n / 2 : ℕ) : ℚ) + 1) ^ 2 else 0) =
        ∑ k ∈ range h, (cPole h (i + j) k / (tN (n / 2) - pole k) ^ 2 -
          4 * cPole h (i + j) k * (if Even n ∧ k < n / 2 then 1 / ((n - 2 * k - 1 : ℕ) : ℚ) ^ 2 else 0)) := by
      refine sum_congr rfl (fun k _ => ?_)
      set m := n / 2 with hm
      have hn2 : n = 2 * m := by obtain ⟨c, hc⟩ := he; omega
      have htk : tN m - pole k = ((k : ℚ) - m) + 1 / 2 := by unfold tN pole; ring
      rw [htk]
      rcases Nat.lt_or_ge k m with hkm | hkm
      · rw [ite_eq_right (by omega), ite_eq_left ⟨he, hkm⟩]
        have e : ((n - 2 * k - 1 : ℕ) : ℚ) = 2 * (m : ℚ) - 2 * k - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hn2]; push_cast; ring
        rw [e]
        have hkm' : (k : ℚ) + 1 ≤ m := by exact_mod_cast hkm
        have hne1 : (2 * (m : ℚ) - 2 * k - 1) ≠ 0 := by intro h'; linarith
        have hne2 : ((k : ℚ) - m + 1 / 2) ≠ 0 := by intro h'; linarith
        field_simp
        ring
      · rw [ite_eq_left ⟨he, hkm⟩, ite_eq_right (by omega)]
        rw [Nat.cast_sub hkm]
        have hkm' : (m : ℚ) ≤ k := by exact_mod_cast hkm
        have hne1 : (2 * ((k : ℚ) - m) + 1) ≠ 0 := by intro h'; linarith
        have hne2 : ((k : ℚ) - m + 1 / 2) ≠ 0 := by intro h'; linarith
        field_simp
        ring
    rw [key, sum_sub_distrib]
    unfold tN
    ring
  · simp only [neg_zero, zero_sub, zero_add]
    rw [sum_eq_zero (fun k _ => by rw [ite_eq_right (fun h => he h.1), mul_zero]),
      sum_eq_zero (fun k _ => by rw [ite_eq_right (fun h => he h.1), mul_zero])]
    simp


/-! ### The determinant: truncation, Andreief, prices -/

local notation "PY" => Polynomial P

/-- The `q`-adic target `aQ h = (h(h−1) − 6h)/3`. -/
def aQ (h : ℕ) : ℕ := (h * (h - 1) - 6 * h) / 3

/-- The ideal of `P[Y]` of polynomials whose coefficients are divisible by `q^N`. -/
noncomputable def Jq (N : ℕ) : Ideal PY := Ideal.span {Polynomial.C ((PowerSeries.X : P) ^ N)}

lemma mem_Jq_of_eq {N : ℕ} {F G : PY} (h : F = Polynomial.C ((PowerSeries.X : P) ^ N) * G) : F ∈ Jq N := by
  rw [h]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

lemma Jq_mono {N N' : ℕ} (h : N ≤ N') : Jq N' ≤ Jq N := by
  unfold Jq
  rw [Ideal.span_le]
  rintro x rfl
  refine mem_Jq_of_eq (G := Polynomial.C ((PowerSeries.X : P) ^ (N' - N))) ?_
  rw [← map_mul, ← pow_add, Nat.add_sub_cancel' h]

lemma coeff_dvd_of_mem_Jq {N : ℕ} {F : PY} (hF : F ∈ Jq N) (k : ℕ) : (PowerSeries.X : P) ^ N ∣ F.coeff k := by
  obtain ⟨G, rfl⟩ := Ideal.mem_span_singleton'.mp hF
  rw [mul_comm, Polynomial.coeff_C_mul]
  exact dvd_mul_right _ _

/-- A power series with vanishing low coefficients, put in `P[Y]` as a constant, lies in `Jq`. -/
lemma C_mem_Jq_of_coeff {N : ℕ} {F : P} (hF : ∀ n < N, PowerSeries.coeff n F = 0) :
    Polynomial.C F ∈ Jq N := by
  have : (PowerSeries.X : P) ^ N ∣ F := (PowerSeries.X_pow_dvd_iff).mpr hF
  obtain ⟨G, rfl⟩ := this
  exact mem_Jq_of_eq (G := Polynomial.C G) (by rw [map_mul])

/-- Sums of `h` distinct naturals are `≥ h(h−1)/2`. -/
lemma card_mul_le_two_sum (S : Finset ℕ) : S.card * (S.card - 1) ≤ 2 * ∑ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s has ih =>
    have hna : a ∉ s := fun h' => lt_irrefl a (has a h')
    rw [card_insert_of_notMem hna, sum_insert hna]
    have hcs : s.card ≤ a := by
      have : s ⊆ range a := fun x hx => mem_range.mpr (has x hx)
      simpa using card_le_card this
    rcases Nat.eq_zero_or_pos s.card with h0 | h0
    · rw [h0]; simp
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h0
      rw [hc] at ih hcs ⊢
      simp only [zero_add, Nat.add_sub_cancel] at ih ⊢
      nlinarith

lemma sum_inj_ge {h : ℕ} (g : Fin h → ℕ) (hg : Function.Injective g) : h * (h - 1) ≤ 2 * ∑ i, g i := by
  have := card_mul_le_two_sum (univ.image g)
  rwa [card_image_of_injective _ hg, card_univ, Fintype.card_fin, sum_image (fun a _ b _ e => hg e)] at this

/-- Slot keys: `(m, deriv?)` for node `−m`, or a pole. -/
abbrev SKey (M h : ℕ) := (Fin M × Bool) ⊕ Fin h

/-- The `q`-price of a slot key. -/
def price {M h : ℕ} : SKey M h → ℕ
  | Sum.inl (m, _) => 2 * m
  | Sum.inr k => 2 * k + 1

/-- An injection into `ℕ` with `3·price + 6 ≥ 2·κ`. -/
def kappa {M h : ℕ} : SKey M h → ℕ
  | Sum.inl (m, b) => 3 * m + (if b then 2 else 0)
  | Sum.inr k => 3 * k + 1

lemma kappa_injective {M h : ℕ} : Function.Injective (kappa (M := M) (h := h)) := by
  rintro (⟨m, b⟩ | k) (⟨m', b'⟩ | k') e <;> simp only [kappa] at e
  · have hm : (m : ℕ) = m' := by split_ifs at e <;> omega
    have hb : b = b' := by cases b <;> cases b' <;> simp at e ⊢ <;> omega
    rw [Fin.ext hm, hb]
  · split_ifs at e <;> omega
  · split_ifs at e <;> omega
  · rw [Fin.ext (by omega : (k : ℕ) = k')]

lemma kappa_le {M h : ℕ} (s : SKey M h) : 2 * kappa s ≤ 3 * price s + 6 := by
  rcases s with ⟨m, b⟩ | k <;> simp only [kappa, price] <;> (try split_ifs) <;> omega

/-- **Price bound.** -/
lemma price_sum_ge {M h : ℕ} (g : Fin h → SKey M h) (hg : Function.Injective g) : aQ h ≤ ∑ i, price (g i) := by
  have h1 := sum_inj_ge (fun i => kappa (g i)) (kappa_injective.comp hg)
  have h2 : 2 * ∑ i, kappa (g i) ≤ 3 * ∑ i, price (g i) + 6 * h := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => kappa_le (g i))
    rw [← Finset.mul_sum, sum_add_distrib, ← Finset.mul_sum, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at this
    linarith
  unfold aQ
  rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]
  omega


/-- Slot indices: `(m, τ)` (node `−m`, `τ ∈ {val·val, der·val, val·der}`) or a pole. -/
abbrev SIdx (M h : ℕ) := (Fin M × Fin 3) ⊕ Fin h

/-- The key of a slot: its row vector depends only on the key. -/
def skey {M h : ℕ} : SIdx M h → SKey M h
  | Sum.inl (m, τ) => Sum.inl (m, decide ((τ : ℕ) = 1))
  | Sum.inr k => Sum.inr k

/-- Rank-one coefficients. -/
noncomputable def ccS (M h : ℕ) : SIdx M h → PY
  | Sum.inl (m, τ) => Polynomial.C (algebraMap ℚ P (-(if (τ : ℕ) = 0 then phd h m else phv h m)) *
      (PowerSeries.X : P) ^ (2 * (m : ℕ)))
  | Sum.inr k => Polynomial.C (algebraMap ℚ P (-4 * omega h k) * (PowerSeries.X : P) ^ (2 * (k : ℕ) + 1)) *
      (Polynomial.C chiS + Polynomial.X)

/-- Row vectors. -/
noncomputable def xS (M h : ℕ) : SIdx M h → Fin h → PY
  | Sum.inl (m, τ) => fun i => Polynomial.C (algebraMap ℚ P
      (if (τ : ℕ) = 1 then (i : ℚ) * tN m ^ ((i : ℕ) - 1) else tN m ^ (i : ℕ)))
  | Sum.inr k => fun i => Polynomial.C (algebraMap ℚ P (pole k ^ (i : ℕ)))

/-- Column vectors. -/
noncomputable def yS (M h : ℕ) : SIdx M h → Fin h → PY
  | Sum.inl (m, τ) => fun j => Polynomial.C (algebraMap ℚ P
      (if (τ : ℕ) = 2 then (j : ℚ) * tN m ^ ((j : ℕ) - 1) else tN m ^ (j : ℕ)))
  | Sum.inr k => fun j => Polynomial.C (algebraMap ℚ P (pole k ^ (j : ℕ)))

lemma xS_eq_of_skey {M h : ℕ} {a b : SIdx M h} (hab : skey a = skey b) : xS M h a = xS M h b := by
  rcases a with ⟨m, τ⟩ | k <;> rcases b with ⟨m', τ'⟩ | k' <;> simp only [skey, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq, Prod.mk.injEq] at hab
  · obtain ⟨rfl, hτ⟩ := hab
    simp only [xS]
    have : ((τ : ℕ) = 1) ↔ ((τ' : ℕ) = 1) := by simpa using hτ
    funext i; simp only [this]
  · rw [hab]

lemma ccS_eq {M h : ℕ} (a : SIdx M h) :
    ∃ d : PY, ccS M h a = Polynomial.C ((PowerSeries.X : P) ^ price (skey a)) * d := by
  rcases a with ⟨m, τ⟩ | k
  · exact ⟨Polynomial.C (algebraMap ℚ P (-(if (τ : ℕ) = 0 then phd h m else phv h m))), by
      simp only [ccS, skey, price, ← map_mul]; ring_nf⟩
  · exact ⟨Polynomial.C (algebraMap ℚ P (-4 * omega h k)) * (Polynomial.C chiS + Polynomial.X), by
      simp only [ccS, skey, price, map_mul]; ring⟩

/-- The truncated rank-one matrix. -/
noncomputable def Mdec (M h : ℕ) : Matrix (Fin h) (Fin h) PY :=
  Matrix.of fun i j => ∑ a, ccS M h a * xS M h a i * yS M h a j

lemma Mdec_apply (M h : ℕ) (i j : Fin h) :
    Mdec M h i j = Polynomial.C (∑ m ∈ range M, algebraMap ℚ P (-svij h m i j) * (PowerSeries.X : P) ^ (2 * m)) +
      ∑ k ∈ range h, Polynomial.C (algebraMap ℚ P (-4 * cPole h (i + j) k) * (PowerSeries.X : P) ^ (2 * k + 1)) *
        (Polynomial.C chiS + Polynomial.X) := by
  unfold Mdec
  rw [Matrix.of_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun m => Polynomial.C (algebraMap ℚ P (-svij h m i j) *
      (PowerSeries.X : P) ^ (2 * m))) M]
    refine sum_congr rfl (fun m _ => ?_)
    rw [Fin.sum_univ_three]
    simp only [ccS, xS, yS, Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((0 : ℕ) = 1) = False by decide, show ((0 : ℕ) = 2) = False by decide,
      show ((1 : ℕ) = 0) = False by decide, show ((1 : ℕ) = 2) = False by decide,
      show ((2 : ℕ) = 0) = False by decide, show ((2 : ℕ) = 1) = False by decide, ite_false, ite_true]
    unfold svij
    simp only [map_mul, map_neg, map_add, map_pow, map_natCast]
    ring
  · rw [← Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (algebraMap ℚ P (-4 * cPole h (i + j) k) *
      (PowerSeries.X : P) ^ (2 * k + 1)) * (Polynomial.C chiS + Polynomial.X)) h]
    refine sum_congr rfl (fun k _ => ?_)
    simp only [ccS, xS, yS, cPole, map_mul, map_neg, map_pow]
    ring

/-- The Gram matrix over `P[Y]`. -/
noncomputable def HPser (h : ℕ) : Matrix (Fin h) (Fin h) PY := (Polynomial.mapRingHom psiP).mapMatrix (HF h)

lemma HPm_apply (h : ℕ) (i j : Fin h) :
    HPser h i j = Polynomial.C (SlotSer h i j) +
      ∑ k ∈ range h, Polynomial.C (algebraMap ℚ P (-4 * cPole h (i + j) k) * (PowerSeries.X : P) ^ (2 * k + 1)) *
        (Polynomial.C chiS + Polynomial.X) := by
  unfold HPser
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, HF_apply]
  unfold LamF
  rw [Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_C]
  erw [psiP_A_eq, psiP_B_eq]
  have e1 : SlotSer h i j - 4 * ∑ k ∈ range h, algebraMap ℚ P (cPole h (i + j) k) *
      (PowerSeries.X : P) ^ (2 * k + 1) * chiS = SlotSer h i j + ∑ k ∈ range h,
      algebraMap ℚ P (-4 * cPole h (i + j) k) * (PowerSeries.X : P) ^ (2 * k + 1) * chiS := by
    rw [mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl (fun k _ => ?_)
    simp only [map_mul, map_neg, map_ofNat]; ring
  have e2 : -(4 * ∑ k ∈ range h, algebraMap ℚ P (cPole h (i + j) k) * (PowerSeries.X : P) ^ (2 * k + 1)) =
      ∑ k ∈ range h, algebraMap ℚ P (-4 * cPole h (i + j) k) * (PowerSeries.X : P) ^ (2 * k + 1) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    simp only [map_mul, map_neg, map_ofNat]; ring
  rw [e1, e2, map_add, map_sum, map_sum, mul_sum, add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  rw [map_mul]; ring

lemma HPm_sub_Mdec_mem (M h : ℕ) (i j : Fin h) : HPser h i j - Mdec M h i j ∈ Jq (2 * M) := by
  rw [HPm_apply, Mdec_apply, add_sub_add_right_eq_sub, ← map_sub]
  refine C_mem_Jq_of_coeff (fun n hn => ?_)
  rw [map_sub, map_sum]
  unfold SlotSer
  rw [PowerSeries.coeff_mk]
  simp only [PowerSeries.coeff_mul_X_pow', Algebra.algebraMap_eq_smul_one,
    PowerSeries.coeff_smul, PowerSeries.coeff_one, smul_eq_mul]
  split_ifs with he
  · rw [sum_eq_single (n / 2)]
    · rw [ite_eq_left (by obtain ⟨c, rfl⟩ := he; omega), ite_eq_left (by obtain ⟨c, rfl⟩ := he; omega)]; ring
    · intro m _ hm
      split_ifs with h1 h2 <;> first | ring1 | (exfalso; obtain ⟨c, rfl⟩ := he; omega)
    · intro hm; exact absurd (mem_range.mpr (by omega)) hm
  · rw [sum_eq_zero]; · ring
    intro m _
    split_ifs with h1 h2 <;> first | ring1 | (exfalso; exact he ⟨m, by omega⟩)

/-- The determinant of the truncated rank-one matrix has `q`-order `≥ aQ h`. -/
lemma det_Mdec_mem (M h : ℕ) : (Mdec M h).det ∈ Jq (aQ h) := by
  have hA := factorial_smul_det_sum_rankOne (ccS M h) (xS M h) (yS M h)
  rw [Fintype.card_fin] at hA
  have hterm : ∀ f : Fin h → SIdx M h, (∏ i, ccS M h (f i)) * (Matrix.of fun i j => xS M h (f i) j).det *
      (Matrix.of fun i j => yS M h (f i) j).det ∈ Jq (aQ h) := by
    intro f
    by_cases hinj : Function.Injective (fun i => skey (f i))
    · refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
      choose d hd using fun i => ccS_eq (f i)
      rw [prod_congr rfl (fun i _ => hd i), prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
      have hle := price_sum_ge _ hinj
      refine mem_Jq_of_eq (G := Polynomial.C ((PowerSeries.X : P) ^ (∑ i, price (skey (f i)) - aQ h)) * ∏ i, d i) ?_
      rw [← mul_assoc, ← map_mul, ← pow_add, Nat.add_sub_cancel' hle]
    · obtain ⟨i, i', he, hne⟩ : ∃ i i', skey (f i) = skey (f i') ∧ i ≠ i' := by
        obtain ⟨a, b, e, hab⟩ := Function.not_injective_iff.mp hinj; exact ⟨a, b, e, hab⟩
      have h0 : (Matrix.of fun i j => xS M h (f i) j).det = 0 :=
        Matrix.det_zero_of_row_eq hne (by funext j; simp only [Matrix.of_apply, xS_eq_of_skey he])
      rw [h0, mul_zero, zero_mul]; exact Ideal.zero_mem _
  have hsum : (h.factorial) • (Mdec M h).det ∈ Jq (aQ h) := by
    unfold Mdec; rw [hA]; exact Ideal.sum_mem _ (fun f _ => hterm f)
  have hfac : ((h.factorial : ℚ))⁻¹ • ((h.factorial) • (Mdec M h).det) = (Mdec M h).det := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero h), one_smul]
  rw [← hfac, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ hsum

/-- **Lemma 4′ (i).** Every coefficient of `Δ_h` over `ℚ⟦q⟧` is divisible by `q^{aQ h}`. -/
theorem ord_DeltaP (h k : ℕ) :
    (PowerSeries.X : P) ^ aQ h ∣ ((DeltaF h).map psiP.toRingHom).coeff k := by
  set M := aQ h + 1
  have hdet : (DeltaF h).map psiP.toRingHom = (HPser h).det := by
    unfold DeltaF HPser
    rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
    rfl
  have hdiff : (HPser h).det - (Mdec M h).det ∈ Jq (2 * M) := by
    rw [← Ideal.Quotient.eq, RingHom.map_det (S := PY ⧸ Jq (2 * M)) (Ideal.Quotient.mk _) (HPser h),
      RingHom.map_det (S := PY ⧸ Jq (2 * M)) (Ideal.Quotient.mk _) (Mdec M h)]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (HPm_sub_Mdec_mem M h i j)
  have hmem : (HPser h).det ∈ Jq (aQ h) := by
    have h1 := Jq_mono (by omega : aQ h ≤ 2 * M) hdiff
    have h2 := det_Mdec_mem M h
    have := Ideal.add_mem _ h1 h2
    rwa [sub_add_cancel] at this
  rw [hdet]
  exact coeff_dvd_of_mem_Jq hmem k


/-! ### The cleared coefficients have `q`-degree `≥ aQ h` -/

/-- For `g` free of `E`, the `q^{m 0}` coefficient of `ψ(g)` is the coefficient of the monomial `m`. -/
lemma coeff_psiP_of_EDeg0 {g : FR} (hg : EDeg 0 g) (m : Fin 2 →₀ ℕ) (hm : g.coeff m ≠ 0) :
    PowerSeries.coeff (m 0) (psiP g) = g.coeff m := by
  have hm1 : m 1 = 0 := Nat.le_zero.mp (hg m hm)
  unfold psiP
  rw [aeval_eq_sum_support, map_sum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [sum_eq_single m]
  · rw [hm1, pow_zero, mul_one, mul_comm, coeff_X_pow_mul_alg, ite_eq_left rfl]
  · intro m' hm' hne
    have hm'1 : m' 1 = 0 := Nat.le_zero.mp (hg m' (MvPolynomial.mem_support_iff.mp hm'))
    rw [hm'1, pow_zero, mul_one, mul_comm, coeff_X_pow_mul_alg, ite_eq_right]
    intro e; apply hne
    ext i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · exact e.symm
    · rw [hm1, hm'1]
  · intro hm'; exact absurd (MvPolynomial.mem_support_iff.mpr hm) hm'

/-- **Lemma 4′ (ii).** After clearing `E` (multiplying by `(q²−1)^β`), every monomial of every
coefficient of `Δ_h` has `q`-degree `≥ aQ h`. -/
theorem qdeg_clearE_DeltaF (h k : ℕ) (m : Fin 2 →₀ ℕ)
    (hm : (clearE (betaP h) ((DeltaF h).coeff k)).coeff m ≠ 0) : aQ h ≤ m 0 := by
  have hdvd : (PowerSeries.X : P) ^ aQ h ∣ psiP (clearE (betaP h) ((DeltaF h).coeff k)) := by
    have e : psiP (clearE (betaP h) ((DeltaF h).coeff k)) =
        (PowerSeries.X ^ 2 - 1) ^ betaP h * psiP ((DeltaF h).coeff k) := by
      unfold psiP
      refine aeval_clearE _ ?_ (EDeg_DeltaF h k)
      simpa using EP_mul
    rw [e]
    refine Dvd.dvd.mul_left ?_ _
    have := ord_DeltaP h k
    rw [Polynomial.coeff_map] at this
    exact this
  rcases Nat.lt_or_ge (m 0) (aQ h) with hlt | hge
  · exfalso
    have h0 := PowerSeries.X_pow_dvd_iff.mp hdvd (m 0) hlt
    rw [coeff_psiP_of_EDeg0 (EDeg_clearE _ _) m hm] at h0
    exact hm h0
  · exact hge

end Chi2Irr
