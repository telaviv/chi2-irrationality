/-
# The series behind Lemma 1 for the signed weight `w = −q⁻²`

Copy of `PoleSeries.lean` and of the Newton-form part of `Arith/Free.lean`, for `|w| < 1` in place of `0 ≤ w < 1`:
* `powSum_eq_tsum'`: `powSum w n = Σ_{t≥1} t^n w^t` for `|w| < 1`;
* `powSum_newton'`, `powSum_newtonQ`, `muMono_newtonQ`: the Newton form `powSum w n = Σ_{b≤n} Δ^b[x^n](0) Ω_b(w)`,
  `Ω_0 = w/(1−w)`, `Ω_b = w^b/(1−w)^{b+1}`, for `|w| < 1` (as reals and as rationals);
* `pole_seriesT`: `Σ_{t≥1} w^t · (−1/(t − x_k)²) = −4 ((−1)^k q^{2k+1} Ti₂(1/q) − S♮_k)` for `w = −q⁻²` (RESULT §1:
  put `s = 2t + 2k + 1`, then `(−1)^t = (−1)^k χ₄(s)`).
-/
import Chi2Irrational.TiQ.Defs
import Chi2Irrational.TiQ.Machine
import Chi2Irrational.Arith.Free

namespace Chi2Irr
namespace TiQ

open Finset

lemma summable_powW' (n : ℕ) {W : ℝ} (h1 : |W| < 1) :
    Summable (fun t : ℕ => ((t : ℝ) + 1) ^ n * W ^ (t + 1)) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one n (r := W) (by rwa [Real.norm_eq_abs])
  have := (summable_nat_add_iff 1).mpr hs
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- **Power sums.** `powSum w n = ∑_{t≥1} t^n w^t` for `|w| < 1`. -/
theorem powSum_eq_tsum' {w : ℚ} (h1 : |w| < 1) (n : ℕ) :
    ((powSum w n : ℚ) : ℝ) = ∑' t : ℕ, ((t : ℝ) + 1) ^ n * (w : ℝ) ^ (t + 1) := by
  have hW1 : |(w : ℝ)| < 1 := by rw [← Rat.cast_abs]; exact_mod_cast h1
  have hne : (1 : ℝ) - w ≠ 0 := by
    intro h0
    have : (w : ℝ) = 1 := by linarith
    rw [this, abs_one] at hW1
    exact lt_irrefl _ hW1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  cases n with
  | zero =>
    rw [powSum]
    push_cast
    simp only [pow_zero, one_mul, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hW1]
    field_simp
  | succ n =>
    rw [powSum]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j => ((n + 1).choose j : ℝ) * (-1) ^ (n - j) * ((powSum w j : ℚ) : ℝ)) (n + 1)]
    rw [div_eq_iff hne]
    set S := ∑' t : ℕ, ((t : ℝ) + 1) ^ (n + 1) * (w : ℝ) ^ (t + 1) with hS
    set f : ℕ → ℝ := fun t => (t : ℝ) ^ (n + 1) * (w : ℝ) ^ (t + 1) with hf
    have hgshift : Summable (fun t : ℕ => f (t + 1)) := by
      have hc : ∀ t : ℕ, (w : ℝ) * (((t : ℝ) + 1) ^ (n + 1) * (w : ℝ) ^ (t + 1)) = f (t + 1) := by
        intro t
        simp only [hf]
        push_cast
        ring
      exact ((summable_powW' (n + 1) hW1).mul_left (w : ℝ)).congr hc
    have hsum0 : Summable f := (summable_nat_add_iff 1).mp hgshift
    have hshift : (w : ℝ) * S = ∑' t : ℕ, f t := by
      rw [tsum_eq_zero_add' (f := f) hgshift]
      have hf0 : f 0 = 0 := by simp [hf]
      rw [hf0, zero_add, hS, ← tsum_mul_left]
      congr 1
      ext t
      simp only [hf]
      push_cast
      ring
    have hdiff : S * (1 - w) = ∑' t : ℕ,
        ∑ j ∈ range (n + 1), ((n + 1).choose j : ℝ) * (-1) ^ (n - j) *
          (((t : ℝ) + 1) ^ j * (w : ℝ) ^ (t + 1)) := by
      rw [mul_sub, mul_one, mul_comm S, hshift, hS,
        ← (summable_powW' (n + 1) hW1).tsum_sub hsum0]
      congr 1
      ext t
      simp only [hf]
      rw [← sub_mul, succ_pow_sub_pow, sum_mul]
      refine sum_congr rfl (fun j _ => by ring)
    rw [hdiff, Summable.tsum_finsetSum (fun j _ =>
      (summable_powW' j hW1).mul_left (((n + 1).choose j : ℝ) * (-1) ^ (n - j)))]
    refine sum_congr rfl (fun j hj => ?_)
    rw [tsum_mul_left, ih j (mem_range.mp hj)]

lemma hasSum_choose_shift' {w : ℝ} (h1 : |w| < 1) (b : ℕ) :
    HasSum (fun t : ℕ => ((t + 1).choose b : ℝ) * w ^ (t + 1)) (OmR w b) := by
  have hn : ‖w‖ < 1 := by rwa [Real.norm_eq_abs]
  have hne : (1 : ℝ) - w ≠ 0 := by
    intro h0
    have : w = 1 := by linarith
    rw [this, abs_one] at h1
    exact lt_irrefl _ h1
  unfold OmR
  split_ifs with hb
  · subst hb
    have := (hasSum_geometric_of_abs_lt_one h1).mul_left w
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    convert this using 1
    · ext t; ring
    · field_simp
  · have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) b hn).mul_left (w ^ b)
    have hf : HasSum (fun s : ℕ => (s.choose b : ℝ) * w ^ s) (w ^ b / (1 - w) ^ (b + 1)) := by
      rw [← hasSum_nat_add_iff' b]
      have hz : ∑ i ∈ range b, (i.choose b : ℝ) * w ^ i = 0 :=
        Finset.sum_eq_zero (fun i hi => by rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]; simp)
      rw [hz, sub_zero]
      convert hs using 1
      · ext n; rw [pow_add]; ring
      · ring
    have := (hasSum_nat_add_iff' 1).mpr hf
    have hz : ∑ i ∈ range 1, (i.choose b : ℝ) * w ^ i = 0 := by
      simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)]
    rw [hz, sub_zero] at this
    exact this

/-- `Σ_{t≥1} t^n w^t = Σ_{b≤n} Δ^b[x^n](0) Ω_b(w)` for `|w| < 1`. -/
lemma powSum_newton' {w : ℚ} (h1 : |w| < 1) (n : ℕ) :
    ((powSum w n : ℚ) : ℝ) = ∑ b ∈ range (n + 1), ((dCoef n b : ℤ) : ℝ) * OmR w b := by
  have hW1 : |(w : ℝ)| < 1 := by rw [← Rat.cast_abs]; exact_mod_cast h1
  rw [powSum_eq_tsum' h1]
  have hterm : ∀ t : ℕ, ((t : ℝ) + 1) ^ n * (w : ℝ) ^ (t + 1) =
      ∑ b ∈ range (n + 1), ((dCoef n b : ℤ) : ℝ) * (((t + 1).choose b : ℝ) * (w : ℝ) ^ (t + 1)) := by
    intro t
    have := newton_pow (R := ℝ) n (t + 1)
    push_cast at this
    rw [this, Finset.sum_mul]
    exact sum_congr rfl (fun b _ => by ring)
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun b _ => ((hasSum_choose_shift' hW1 b).mul_left _).summable)]
  exact sum_congr rfl (fun b _ => by rw [tsum_mul_left, (hasSum_choose_shift' hW1 b).tsum_eq])

/-- `Ω_b(w)` as a rational: `Ω_0 = w/(1−w)`, `Ω_b = w^b/(1−w)^{b+1}`. -/
def OmQ (w : ℚ) (b : ℕ) : ℚ := if b = 0 then w / (1 - w) else w ^ b / (1 - w) ^ (b + 1)

lemma OmQ_cast (w : ℚ) (b : ℕ) : ((OmQ w b : ℚ) : ℝ) = OmR w b := by
  unfold OmQ OmR; split_ifs <;> push_cast <;> rfl

/-- **Newton form of the power sums**, rationally: `powSum w n = Σ_{b≤n} Δ^b[x^n](0) Ω_b(w)` for `|w| < 1`. -/
theorem powSum_newtonQ {w : ℚ} (h1 : |w| < 1) (n : ℕ) :
    powSum w n = ∑ b ∈ range (n + 1), (dCoef n b : ℚ) * OmQ w b := by
  apply Rat.cast_injective (α := ℝ)
  rw [powSum_newton' h1]
  push_cast
  exact sum_congr rfl (fun b _ => by rw [OmQ_cast])

/-- **Newton form of `μ(u^d)`**: `μ(u^d) = Σ_{b<d} d Δ^b[x^{d−1}](0) Ω_b(w)` for `|w| < 1`. -/
theorem muMono_newtonQ {w : ℚ} (h1 : |w| < 1) (d : ℕ) :
    muMono w d = ∑ b ∈ range d, ((d : ℚ) * (dCoef (d - 1) b : ℚ)) * OmQ w b := by
  cases d with
  | zero => simp [muMono]
  | succ n =>
    rw [muMono, powSum_newtonQ h1, mul_sum, Nat.add_sub_cancel]
    push_cast
    exact sum_congr rfl (fun b _ => by ring)

lemma abs_wT_lt_one {q : ℕ} (hq : 2 ≤ q) : |wT q| < 1 := by
  unfold wT
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℚ) < (q : ℚ) ^ 2 := by positivity
  rw [neg_div, abs_neg, abs_of_pos (by positivity), div_lt_one hq2]
  nlinarith

/-- **The pole series for Ti₂.** For `q ≥ 2`, `w = −q⁻²`:
`∑_{t≥1} w^t · (−1/(t − x_k)²) = −4 ((−1)^k q^{2k+1} Ti₂(1/q) − S♮_k)`. -/
theorem pole_seriesT {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    ∑' t : ℕ, ((wT q : ℚ) : ℝ) ^ (t + 1) * (-(1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2)) =
      -4 * ((poleW q k : ℝ) * ti2 (1 / (q : ℝ)) - (SpartT q k : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hz : |1 / (q : ℝ)| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    rw [div_le_one hq0]
    exact_mod_cast (by omega : 1 ≤ q)
  set z : ℝ := 1 / (q : ℝ) with hzdef
  have hzq : (q : ℝ) * z = 1 := by rw [hzdef]; field_simp
  have hsplit := (summable_ti2Term hz).sum_add_tsum_nat_add (k + 1)
  -- `(−1)^k q^{2k+1} · (first k+1 terms) = S♮_k`
  have hhead : (poleW q k : ℝ) * ∑ i ∈ range (k + 1), ti2Term z i = (SpartT q k : ℝ) := by
    unfold SpartT ti2Term poleW
    push_cast
    rw [mul_sum]
    refine sum_congr rfl (fun j hj => ?_)
    have hj : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have : (q : ℝ) ^ (2 * k + 1) * z ^ (2 * j + 1) = (q : ℝ) ^ (2 * (k - j)) := by
      rw [show 2 * k + 1 = 2 * (k - j) + (2 * j + 1) by omega, pow_add, mul_assoc, ← mul_pow, hzq,
        one_pow, mul_one]
    have hs : (-1 : ℝ) ^ k * (-1) ^ j = (-1) ^ (k - j) := by
      rw [← pow_add, show k + j = (k - j) + 2 * j by omega, pow_add, pow_mul]; simp
    rw [← this, ← hs]
    ring
  -- the tail, term by term
  have htail : ∀ t : ℕ, (poleW q k : ℝ) * ti2Term z (t + (k + 1)) =
      ((wT q : ℚ) : ℝ) ^ (t + 1) * (1 / 4) * (1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2) := by
    intro t
    unfold ti2Term wT pole poleW
    push_cast
    have hw : (-1 / (q : ℝ) ^ 2) ^ (t + 1) = (-1) ^ (t + 1) * z ^ (2 * t + 2) := by
      rw [neg_div, neg_eq_neg_one_mul, mul_pow, hzdef, ← one_div_pow, ← pow_mul]
      ring_nf
    rw [hw]
    have hpow : (q : ℝ) ^ (2 * k + 1) * z ^ (2 * (t + (k + 1)) + 1) = z ^ (2 * t + 2) := by
      rw [show 2 * (t + (k + 1)) + 1 = (2 * k + 1) + (2 * t + 2) by ring, pow_add z, ← mul_assoc,
        ← mul_pow, hzq, one_pow, one_mul]
    have hsgn : (-1 : ℝ) ^ k * (-1) ^ (t + (k + 1)) = (-1) ^ (t + 1) := by
      rw [← pow_add, show k + (t + (k + 1)) = (t + 1) + 2 * k by ring, pow_add, pow_mul]; simp
    have hden : (2 * ((t : ℝ) + ((k : ℝ) + 1)) + 1) ^ 2 =
        4 * ((t : ℝ) + 1 - -((k : ℝ) + 1 / 2)) ^ 2 := by
      ring
    have hne : ((t : ℝ) + 1 - -((k : ℝ) + 1 / 2)) ≠ 0 := by
      have : (0 : ℝ) ≤ t := t.cast_nonneg
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      intro h0
      linarith
    calc (-1 : ℝ) ^ k * (q : ℝ) ^ (2 * k + 1) *
          ((-1) ^ (t + (k + 1)) * z ^ (2 * (t + (k + 1)) + 1) / (2 * ((t : ℝ) + ((k : ℝ) + 1)) + 1) ^ 2)
        = ((-1 : ℝ) ^ k * (-1) ^ (t + (k + 1))) * ((q : ℝ) ^ (2 * k + 1) * z ^ (2 * (t + (k + 1)) + 1)) /
            (2 * ((t : ℝ) + ((k : ℝ) + 1)) + 1) ^ 2 := by ring
      _ = _ := by
          rw [hsgn, hpow, hden]
          field_simp
  have hts : Summable (fun t => ti2Term z (t + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).mpr (summable_ti2Term hz)
  have key : (poleW q k : ℝ) * ti2 z - (SpartT q k : ℝ) =
      ∑' t : ℕ, ((wT q : ℚ) : ℝ) ^ (t + 1) * (1 / 4) *
        (1 / (((t : ℝ) + 1) - (pole k : ℝ)) ^ 2) := by
    rw [ti2, ← hsplit, mul_add, hhead, add_sub_cancel_left, ← tsum_mul_left]
    exact tsum_congr htail
  rw [key, ← tsum_mul_left]
  refine tsum_congr (fun t => ?_)
  ring

end TiQ
end Chi2Irr
