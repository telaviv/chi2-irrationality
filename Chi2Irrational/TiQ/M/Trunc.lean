/-
# Lemma M, part 4: the truncated Mahler functional and the rational `θ` (RESULT §1 step 1, made finite)

* `MB_poly`: on a polynomial `R` of degree `≤ B`, `MB q B (R′) = μ(R)` (the Newton form of `μ`, `muMono_newtonQ`).
* Shift rule, truncated: `f_{k+1}(t) = f_k(t + 1)`, so `Δ^b f_{k+1}′(0) = Δ^b f_k′(0) + Δ^{b+1} f_k′(0)`; with
  `Ω_{b−1} = (w⁻¹ − 1) Ω_b` (`b ≥ 2`), `Ω_0 = (w⁻¹ − 1) Ω_1 − 1` this gives
  `MB(f_{k+1}′) = −q² MB(f_k′) + 4/(2k+3)² + (−q² − 1) Ω_B Δ^B f_k′(0)`.
  The archimedean pole values `D_k = 4 S♮_k − 4θ (−1)^k q^{2k+1}` satisfy the same recursion without the last term, and
  `D_0 = MB(f_0′)` by the choice of `θ`. The error has `v₂ ≥ 1 − (B+1) + (B + 2 + v₂(B!)) ≥ 2 + B/2`
  (`v₂(Δ^B f_k′(0)) ≥ B + 2 + v₂(B!)`, `Arith/TwoAdicBasis.lean`'s `gS` bound).
* `theta_bound`: `‖θ‖₂ ≤ 2` (`v₂(MB(f_0′)) ≥ 1`).
-/
import Chi2Irrational.TiQ.M.Binom

namespace Chi2Irr
namespace TiQ
namespace M

open Polynomial Finset

/-! ### Helpers -/

lemma tr_fd_lin {ι : Type*} (s : Finset ι) (a : ι → ℚ) (g : ι → ℕ → ℚ) (b : ℕ) :
    fd b (fun i => ∑ d ∈ s, a d * g d i) = ∑ d ∈ s, a d * fd b (g d) := by
  simp only [fd, fwdDiff_iter_eq_sum_shift, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))

lemma tr_muMono {w : ℚ} (h1 : |w| < 1) {d B : ℕ} (hd : d ≤ B) :
    muMono w d = ∑ b ∈ range B, ((d : ℚ) * (dCoef (d - 1) b : ℚ)) * OmQ w b := by
  rw [muMono_newtonQ h1]
  refine sum_subset (range_mono hd) (fun b _ hb => ?_)
  have hb' : d ≤ b := by simpa using hb
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0; simp
  · rw [dCoef_eq_zero (by omega)]; simp

/-- **Newton form**: `μ(R) = Σ_{b<B} Ω_b Δ^b R′(0)` once `B ≥ deg R`. -/
theorem MB_poly {q : ℕ} (hq : 2 ≤ q) {B : ℕ} {R : ℚ[X]} (hR : R.natDegree ≤ B) :
    muPoly (wT q) R = MB q B (fun i => (derivative R).eval (i : ℚ)) := by
  have hlt : R.natDegree < B + 1 := by omega
  unfold muPoly MB
  rw [sum_over_range' R (fun n => by simp) (B + 1) hlt]
  have hder : (fun i : ℕ => (derivative R).eval (i : ℚ)) =
      fun i : ℕ => ∑ d ∈ range (B + 1), (R.coeff d * (d : ℚ)) * (fun j : ℕ => (j : ℚ) ^ (d - 1)) i := by
    funext i
    rw [derivative_eval, sum_over_range' R (fun n => by simp) (B + 1) hlt]
  rw [hder]
  simp_rw [tr_fd_lin]
  have hmu : ∀ d ∈ range (B + 1), R.coeff d * muMono (wT q) d =
      ∑ b ∈ range B, R.coeff d * (((d : ℚ) * (dCoef (d - 1) b : ℚ)) * OmQ (wT q) b) := by
    intro d hd
    rw [tr_muMono (abs_wT_lt_one hq) (by simpa [Nat.lt_succ_iff] using hd), mul_sum]
  rw [sum_congr rfl hmu, sum_comm]
  refine sum_congr rfl (fun b _ => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun d _ => ?_)
  rw [fd, ← dCoef_eq_fd]
  ring

lemma tr_OmQ_rel {w : ℚ} (hw0 : w ≠ 0) (hw1 : 1 - w ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    OmQ w n = (w⁻¹ - 1) * OmQ w (n + 1) := by
  have h1 : n ≠ 0 := by omega
  unfold OmQ
  simp only [h1, Nat.add_one_ne_zero, ↓reduceIte]
  field_simp
  ring

lemma tr_shift_sum {w : ℚ} (hw0 : w ≠ 0) (hw1 : 1 - w ≠ 0) (x : ℕ → ℚ) {B : ℕ} (hB : 1 ≤ B) :
    ∑ b ∈ range B, OmQ w b * (x b + x (b + 1)) =
      w⁻¹ * ∑ b ∈ range B, OmQ w b * x b - (x 0 + x 1) + (w⁻¹ - 1) * OmQ w B * x B := by
  induction B, hB using Nat.le_induction with
  | base =>
    simp only [sum_range_one, OmQ, one_ne_zero, ↓reduceIte, zero_add, pow_one]
    field_simp
    ring
  | succ n hn ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    linear_combination (x (n + 1)) * tr_OmQ_rel hw0 hw1 hn

lemma tr_fk_shift (k : ℕ) : (fun r : ℕ => fk k (r + 1)) = fk (k + 1) := by
  funext r
  unfold fk
  rw [show (((r + 1 : ℕ) : ℚ) - pole k) = (r : ℚ) - pole (k + 1) by unfold pole; push_cast; ring]

lemma tr_fd_fk_succ (k b : ℕ) : fd b (fk (k + 1)) = fd b (fk k) + fd (b + 1) (fk k) := by
  unfold fd
  rw [fd_succ, fd_shift _ b 0 1, tr_fk_shift]
  ring

lemma tr_wT_ne {q : ℕ} (hq : 2 ≤ q) : wT q ≠ 0 ∧ 1 - wT q ≠ 0 := by
  have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq' : (q : ℚ) ≠ 0 := by linarith
  have hpos : (0 : ℚ) < (q : ℚ) ^ 2 := by positivity
  have hneg : -1 / (q : ℚ) ^ 2 < 0 := div_neg_of_neg_of_pos (by norm_num) hpos
  refine ⟨?_, ?_⟩
  · unfold wT; exact hneg.ne
  · unfold wT
    have : 0 < 1 - -1 / (q : ℚ) ^ 2 := by linarith
    exact this.ne'

lemma tr_wT_inv (q : ℕ) : (wT q)⁻¹ = -(q : ℚ) ^ 2 := by
  unfold wT
  rw [neg_div, inv_neg, inv_div, div_one]

lemma tr_MB_succ {q : ℕ} (hq : 2 ≤ q) {B : ℕ} (hB : 1 ≤ B) (k : ℕ) :
    MB q B (fk (k + 1)) = (wT q)⁻¹ * MB q B (fk k) - fk k 1 +
      ((wT q)⁻¹ - 1) * OmQ (wT q) B * fd B (fk k) := by
  obtain ⟨hw0, hw1⟩ := tr_wT_ne hq
  unfold MB
  simp_rw [tr_fd_fk_succ]
  rw [tr_shift_sum hw0 hw1 (fun b => fd b (fk k)) hB]
  have e0 : fd 0 (fk k) + fd 1 (fk k) = fk k 1 := by
    simp only [fd, Function.iterate_zero, id_eq, Function.iterate_one, fwdDiff]
    norm_num
  rw [e0]

lemma tr_SpartT_succ (q k : ℕ) :
    SpartT q (k + 1) = -(q : ℚ) ^ 2 * SpartT q k + 1 / (2 * ((k : ℚ) + 1) + 1) ^ 2 := by
  unfold SpartT
  rw [sum_range_succ, mul_sum]
  have hs : ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (k + 1 - j) * (q : ℚ) ^ (2 * (k + 1 - j)) / (2 * (j : ℚ) + 1) ^ 2 =
      ∑ j ∈ range (k + 1), -(q : ℚ) ^ 2 *
        ((-1 : ℚ) ^ (k - j) * (q : ℚ) ^ (2 * (k - j)) / (2 * (j : ℚ) + 1) ^ 2) := by
    refine sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [show k + 1 - j = (k - j) + 1 by omega]
    generalize k - j = t
    ring
  rw [hs, Nat.sub_self]
  push_cast
  ring

lemma tr_poleW_succ (q k : ℕ) : poleW q (k + 1) = -(q : ℚ) ^ 2 * poleW q k := by
  unfold poleW; ring

lemma tr_fk_one (k : ℕ) : fk k 1 = -4 / (2 * ((k : ℚ) + 1) + 1) ^ 2 := by
  unfold fk
  rw [show ((1 : ℕ) : ℚ) - pole k = (2 * ((k : ℚ) + 1) + 1) / 2 by unfold pole; push_cast; ring]
  have : (2 * ((k : ℚ) + 1) + 1) ≠ 0 := by positivity
  rw [div_pow]
  field_simp
  ring

lemma tr_fk_eq (k : ℕ) : fk k = (-4 : ℚ) • gS (2 * k + 1) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul]
  unfold fk gS
  rw [show (i : ℚ) - pole k = (((2 * k + 1 : ℕ) : ℚ) + 2 * (i : ℚ)) / 2 by unfold pole; push_cast; ring]
  have : (((2 * k + 1 : ℕ) : ℚ) + 2 * (i : ℚ)) ≠ 0 := by positivity
  rw [div_pow]
  field_simp
  ring

lemma tr_V2_fd_fk (k b : ℕ) : V2 (2 + (b : ℤ) + vf b) (fd b (fk k)) := by
  have e : fd b (fk k) = -4 * (fwdDiff 1)^[b] (gS (2 * k + 1)) 0 := by
    unfold fd
    rw [tr_fk_eq, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul]
  rw [e]
  have := V2_mul (V2_neg V2_four) (V2_fd_gS (odd_two_mul_add_one k) b)
  convert this using 1
  ring

lemma tr_vf_Bt (h : ℕ) : 8 * h + 8 ≤ vf (Bt h) := by
  unfold vf Bt
  rw [show 16 * h + 16 = 2 * (8 * h + 8) by ring, padicValNat_factorial_mul]
  omega

/-- **The pole values match the truncated functional** up to `2^{−(8h+8)}`. -/
theorem err_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (h k : ℕ) :
    padicNorm 2 (4 * SpartT q k - 4 * theta q h * poleW q k - MB q (Bt h) (fk k)) ≤
      (2 : ℚ) ^ (-(8 * (h : ℤ) + 8)) := by
  have hq2 : 2 ≤ q := by omega
  have hB : 1 ≤ Bt h := by unfold Bt; omega
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  show V2 (8 * (h : ℤ) + 8) _
  induction k with
  | zero =>
    have e : 4 * SpartT q 0 - 4 * theta q h * poleW q 0 - MB q (Bt h) (fk 0) = 0 := by
      simp only [SpartT, poleW, theta]
      simp
      field_simp
      ring
    rw [e]; exact V2_zero _
  | succ k ih =>
    have e : 4 * SpartT q (k + 1) - 4 * theta q h * poleW q (k + 1) - MB q (Bt h) (fk (k + 1)) =
        ((q ^ 2 : ℕ) : ℚ) * -(4 * SpartT q k - 4 * theta q h * poleW q k - MB q (Bt h) (fk k)) -
          ((-(q : ℚ) ^ 2 - 1) * OmQ (wT q) (Bt h) * fd (Bt h) (fk k)) := by
      rw [tr_SpartT_succ, tr_poleW_succ, tr_MB_succ hq2 hB, tr_wT_inv, tr_fk_one]
      push_cast
      ring
    rw [e]
    refine V2_sub ?_ ?_
    · have := V2_mul (V2_natCast (q ^ 2)) (V2_neg ih)
      simpa using this
    · have h1 := V2_mul (V2_mul (V2_qsqT ho) (V2_OmQT ho (Bt h))) (tr_V2_fd_fk k (Bt h))
      refine V2_mono ?_ h1
      have := tr_vf_Bt h
      have hBt : Bt h = 16 * h + 16 := rfl
      omega

theorem theta_bound {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) (h : ℕ) : padicNorm 2 (theta q h) ≤ 2 := by
  have hMB : V2 1 (MB q (Bt h) (fk 0)) := by
    unfold MB
    refine V2_sum _ _ (fun b _ => ?_)
    refine V2_mul' (V2_OmQT ho b) (tr_V2_fd_fk 0 b) ?_
    omega
  have hnum : V2 1 (4 - MB q (Bt h) (fk 0)) := V2_sub (V2_mono (by norm_num) V2_four) hMB
  have hden : padicNorm 2 (4 * (q : ℚ)) = (2 : ℚ) ^ (-(2 : ℤ)) := by
    rw [padicNorm.mul, padicNorm_two_odd ho, show (4 : ℚ) = 2 * 2 by norm_num, padicNorm.mul,
      padicNorm_two_self]
    norm_num
  have := V2_div_of_norm hnum hden
  unfold theta
  unfold V2 at this
  rw [show -((1 : ℤ) - 2) = 1 by norm_num, zpow_one] at this
  exact this

end M
end TiQ
end Chi2Irr
