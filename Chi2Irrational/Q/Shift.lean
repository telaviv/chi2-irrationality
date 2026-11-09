/-
# Theorem Q: the shift lemma (RESULT §2) in the certificate format of `Analytic/TheoremB.lean`

`DualCert.shift`: from a dual certificate `C : DualCert q₀`, `1 ≤ q₀ ≤ q` and `δ > 0`, a dual certificate
`C' : DualCert q` with `Φ(C') ≤ Φ(C) − ½ log(q/q₀) + δ`.

Construction (RESULT §2, discretised): `DualCert q` depends on `q` only through `W = Wr q = q⁻²`. With
`ℓ = log Wr q₀ − log Wr q = 2 log(q/q₀) ≥ 0`, `V_{W'}(x) = V_W(x) − ℓx` (`Vf_shift`). Keep `μ`, `X`, `N`; `λ' = λ − ℓ/2`;
refine the grid by the factor `2r` (`L' = 2rL = 2m`, `m = rL`) and put `S'_{k'} = S_{⌊k'/2r⌋} − ℓk'/L'`: on
`[k'/L', (k'+1)/L'] ⊆ [k/L, (k+1)/L]` (`k = ⌊k'/2r⌋`) the term `−ℓx` is at most its left-endpoint value. Tails:
`log Wr q ≤ log Wr q₀`, and the second tail changes by `−(X − ½)ℓ ≤ 0`. Excess:
`(S_k − λ − ℓk'/L' + ℓ/2)₊ ≤ (S_k − λ)₊ + (ℓ/2)(1 − k'/m)₊`, `Σ_{k' < XL'} (1 − k'/m)₊ = (m + 1)/2` (`sum_hinge`), and
each `k` is repeated `2r` times (`sum_range_mul_div`); so `Φ' ≤ Φ − ℓ/4 + ℓ/(4m)`, and `r` is chosen with `ℓ/r ≤ δ`.
Departure from RESULT §2: the continuous shift is exact there; here the left-endpoint Riemann sum costs `ℓ/(4m)`,
absorbed by `δ`. (Model: `lean_chi2u/Chi2U/V/Shift.lean`, density cap 1 there, 2 here.)
-/
import Chi2Irrational.Analytic.TheoremB

namespace Chi2Irr
namespace Q

open Finset

/-! ## Elementary sums -/

lemma sum_range_cast_id (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `Σ_{k < M} (1 − k/m)₊ = (m + 1)/2` for `M ≥ m + 1`. -/
lemma sum_hinge (m M : ℕ) (hm : 1 ≤ m) (hM : m + 1 ≤ M) :
    ∑ k ∈ range M, max (1 - (k : ℝ) / m) 0 = ((m : ℝ) + 1) / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← sum_range_add_sum_Ico _ hM]
  have h2 : ∑ k ∈ Ico (m + 1) M, max (1 - (k : ℝ) / m) 0 = 0 := by
    apply sum_eq_zero
    intro k hk
    have hk' : (m : ℝ) + 1 ≤ k := by exact_mod_cast (mem_Ico.mp hk).1
    apply max_eq_right
    rw [sub_nonpos, le_div_iff₀ hm']
    linarith
  have h1 : ∑ k ∈ range (m + 1), max (1 - (k : ℝ) / m) 0 = ∑ k ∈ range (m + 1), (1 - (k : ℝ) / m) := by
    apply sum_congr rfl
    intro k hk
    have hk' : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    apply max_eq_left
    rw [sub_nonneg, div_le_one hm']
    exact hk'
  rw [h2, add_zero, h1, sum_sub_distrib, ← sum_div, sum_range_cast_id]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast
  field_simp
  ring

/-- `Σ_{k < rn} g(⌊k/r⌋) = r Σ_{k < n} g(k)`. -/
lemma sum_range_mul_div (g : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (n : ℕ) :
    ∑ k ∈ range (r * n), g (k / r) = r * ∑ k ∈ range n, g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show r * (n + 1) = r * n + r by ring, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    have : ∀ x ∈ range r, g ((r * n + x) / r) = g n := by
      intro x hx
      rw [show r * n + x = x + r * n by ring, Nat.add_mul_div_left _ _ hr,
        Nat.div_eq_of_lt (mem_range.mp hx), zero_add]
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]

/-! ## The external field -/

lemma log_Wr (q : ℕ) : Real.log (Wr q) = -2 * Real.log q := by
  unfold Wr wt
  push_cast
  rw [one_div, Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- `V_{W'}(x) = V_W(x) − (log W − log W')·x`. -/
lemma Vf_shift (W W' x : ℝ) : Vf W' x = Vf W x - (Real.log W - Real.log W') * x := by
  unfold Vf; ring

/-! ## The shift lemma -/

/-- **Shift lemma** (RESULT §2): a certificate at `q₀` moves to every `q ≥ q₀`, gaining `½ log(q/q₀)` up to `δ`. -/
theorem DualCert.shift {q₀ : ℕ} (C : DualCert q₀) (hq₀ : 1 ≤ q₀) (q : ℕ) (hq : q₀ ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : DualCert q, C'.Phi ≤ C.Phi - Real.log ((q : ℝ) / q₀) / 2 + δ := by
  set ℓ := Real.log (Wr q₀) - Real.log (Wr q) with hℓ
  have hq₀' : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have hqq : (q₀ : ℝ) ≤ q := by exact_mod_cast hq
  have hℓe : ℓ = 2 * (Real.log q - Real.log q₀) := by rw [hℓ, log_Wr, log_Wr]; ring
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓe]; have := Real.log_le_log hq₀' hqq; linarith
  have hlogq : Real.log ((q : ℝ) / q₀) / 2 = ℓ / 4 := by
    rw [Real.log_div (by linarith) hq₀'.ne', hℓe]; ring
  -- the refinement factor
  set r : ℕ := ⌈ℓ / δ⌉₊ + 1 with hr
  have hr0 : 0 < r := Nat.succ_pos _
  have hrδ : ℓ / δ ≤ r := by
    have := Nat.le_ceil (ℓ / δ)
    rw [hr]; push_cast; linarith
  have hL1 := C.hL
  set m : ℕ := r * C.L with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr0.ne' (by omega))
  have hmr : (m : ℝ) = r * C.L := by rw [hm]; push_cast; ring
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  set r2 : ℕ := 2 * r with hr2
  have hr20 : 0 < r2 := by omega
  set L' : ℕ := r2 * C.L with hL'
  have hL'1 : 1 ≤ L' := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr20.ne' (by omega))
  have hL'r : (L' : ℝ) = r2 * C.L := by rw [hL']; push_cast; ring
  have hL'm : (L' : ℝ) = 2 * m := by rw [hL', hm, hr2]; push_cast; ring
  have hLpos : (0 : ℝ) < C.L := by exact_mod_cast (show 0 < C.L by omega)
  have hr20' : (0 : ℝ) < r2 := by exact_mod_cast hr20
  have hX1 : (1 : ℝ) ≤ C.X := by exact_mod_cast C.hX
  refine ⟨{
    μ := C.μ
    lam := C.lam - ℓ / 2
    L := L'
    X := C.X
    N := C.N
    Sk := fun k => C.Sk (k / r2) - ℓ * (k : ℝ) / L'
    hL := hL'1
    hN := C.hN
    hXN := C.hXN
    hX := C.hX
    hF := ?_
    htail1 := by have := C.htail1; linarith
    htail2 := ?_ }, ?_⟩
  · -- the cell bounds
    intro k hk x hx0 hx1 hx2
    have hk' : k / r2 < C.X * C.L := by
      rw [Nat.div_lt_iff_lt_mul hr20]
      calc k < C.X * L' := hk
        _ = C.X * C.L * r2 := by rw [hL']; ring
    have hlo : ((k / r2 : ℕ) : ℝ) / C.L ≤ x := by
      have h1 : ((k / r2 : ℕ) : ℝ) * r2 ≤ k := by exact_mod_cast Nat.div_mul_le_self k r2
      refine le_trans ?_ hx1
      rw [hL'r, div_le_div_iff₀ hLpos (by positivity)]
      nlinarith
    have hhi : x ≤ (((k / r2 : ℕ) : ℝ) + 1) / C.L := by
      have h1 : k + 1 ≤ k / r2 * r2 + r2 := Nat.lt_div_mul_add hr20
      have h1' : (k : ℝ) + 1 ≤ ((k / r2 : ℕ) : ℝ) * r2 + r2 := by exact_mod_cast h1
      refine le_trans hx2 ?_
      rw [hL'r, div_le_div_iff₀ (by positivity) hLpos]
      nlinarith
    have hF := C.hF (k / r2) hk' x hx0 hlo hhi
    have hmul : ℓ * ((k : ℝ) / L') ≤ ℓ * x := mul_le_mul_of_nonneg_left hx1 hℓ0
    rw [Vf_shift (Wr q₀) (Wr q) x, ← hℓ]
    change 2 * C.μ.U x + (Vf (Wr q₀) x - ℓ * x) ≤ C.Sk (k / r2) - ℓ * (k : ℝ) / L'
    rw [mul_div_assoc]
    linarith
  · -- the second tail: it changes by `−(X − ½)ℓ ≤ 0`
    have h2 := C.htail2
    have hXL : 0 ≤ ((C.X : ℝ) - 1 / 2) * ℓ := mul_nonneg (by linarith) hℓ0
    have e : (C.X : ℝ) * Real.log (Wr q) = C.X * Real.log (Wr q₀) - C.X * ℓ := by rw [hℓ]; ring
    change Real.log C.X + C.X * Real.log (Wr q) - (C.lam - ℓ / 2) < 0
    rw [e]
    nlinarith
  · -- the exponent
    unfold DualCert.Phi DualCert.σ
    dsimp only
    have hterm : ∀ k ∈ range (C.X * L'), max (C.Sk (k / r2) - ℓ * (k : ℝ) / L' - (C.lam - ℓ / 2)) 0 ≤
        max (C.Sk (k / r2) - C.lam) 0 + ℓ / 2 * max (1 - (k : ℝ) / m) 0 := by
      intro k _
      have a1 := le_max_left (C.Sk (k / r2) - C.lam) 0
      have a2 := le_max_right (C.Sk (k / r2) - C.lam) 0
      have hℓ2 : 0 ≤ ℓ / 2 := by linarith
      have b1 := mul_le_mul_of_nonneg_left (le_max_left (1 - (k : ℝ) / m) 0) hℓ2
      have b2 := mul_nonneg hℓ2 (le_max_right (1 - (k : ℝ) / m) 0)
      apply max_le
      · have : ℓ / 2 * (1 - (k : ℝ) / m) = ℓ / 2 - ℓ * (k : ℝ) / L' := by
          rw [hL'm]; field_simp
        linarith
      · linarith
    have hsum := sum_le_sum hterm
    have hMm : m + 1 ≤ C.X * L' := by
      have : L' = 2 * m := by rw [hL', hm, hr2]; ring
      rw [this]; have := C.hX; nlinarith
    rw [sum_add_distrib, ← mul_sum, sum_hinge m (C.X * L') hm1 hMm] at hsum
    have hrep : ∑ k ∈ range (C.X * L'), max (C.Sk (k / r2) - C.lam) 0 =
        r2 * ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0 := by
      rw [show C.X * L' = r2 * (C.X * C.L) by rw [hL']; ring]
      exact sum_range_mul_div (fun k => max (C.Sk k - C.lam) 0) r2 hr20 _
    rw [hrep] at hsum
    set σ := ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0 with hσ
    set S' := ∑ k ∈ range (C.X * L'), max (C.Sk (k / r2) - ℓ * (k : ℝ) / L' - (C.lam - ℓ / 2)) 0
    -- `(2/L') S' ≤ (2/L) σ + ℓ/4 + ℓ/(4m)` and `ℓ/(4m) ≤ ℓ/(4r) ≤ δ`
    have h1 : 2 / (L' : ℝ) * S' ≤ 2 / C.L * σ + ℓ / 4 + ℓ / (4 * m) := by
      have : 2 / (L' : ℝ) * S' ≤ 2 / (L' : ℝ) * (r2 * σ + ℓ / 2 * (((m : ℝ) + 1) / 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      refine this.trans (le_of_eq ?_)
      have e1 : 2 / (L' : ℝ) * (r2 * σ) = 2 / C.L * σ := by
        rw [hL'r]; field_simp
      have e2 : 2 / (L' : ℝ) * (ℓ / 2 * (((m : ℝ) + 1) / 2)) = ℓ / 4 + ℓ / (4 * m) := by
        rw [hL'm]; field_simp; ring
      rw [mul_add, e1, e2]; ring
    have h2 : ℓ / (4 * m) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      have hrm : (r : ℝ) ≤ m := by
        have : (1 : ℝ) ≤ C.L := by exact_mod_cast hL1
        have : (0 : ℝ) ≤ r := by positivity
        rw [hmr]; nlinarith
      have : ℓ ≤ δ * r := by rwa [div_le_iff₀ hδ, mul_comm] at hrδ
      nlinarith
    rw [hlogq]
    linarith

end Q
end Chi2Irr
