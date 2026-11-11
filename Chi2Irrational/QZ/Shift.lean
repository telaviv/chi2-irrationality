/-
# The shift lemma at a real weight (copy of `Q/Shift.lean` for `DualCertW`)

`DualCertW.shift`: from `C : DualCertW W₀`, `0 < W ≤ W₀` and `δ > 0`, a certificate `C' : DualCertW W` with
`Φ(C') ≤ Φ(C) − ℓ/4 + δ`, `ℓ = log W₀ − log W`. Same construction as `Q/Shift.lean` (keep `μ`, `X`, `N`;
`λ' = λ − ℓ/2`; refine the grid by `2r`, `S'_{k'} = S_{⌊k'/2r⌋} − ℓk'/L'`), which used `W = Wr q` only through
`ℓ ≥ 0`. At `W = ζ⁻²`: `ℓ = 2 log(ζ/ζ₀)`, gain `½ log(ζ/ζ₀)` (`DualCertZ.shift`).
-/
import Chi2Irrational.QZ.TheoremB
import Chi2Irrational.Q.Shift

namespace Chi2Irr
namespace QZ

open Finset

/-- **Shift lemma** at a real weight: a certificate at `W₀` moves to every `W ∈ (0, W₀]`, gaining
`(log W₀ − log W)/4` up to `δ`. -/
theorem DualCertW.shift {W₀ : ℝ} (C : DualCertW W₀) {W : ℝ} (hW : 0 < W) (hWW : W ≤ W₀) {δ : ℝ}
    (hδ : 0 < δ) : ∃ C' : DualCertW W, C'.Phi ≤ C.Phi - (Real.log W₀ - Real.log W) / 4 + δ := by
  set ℓ := Real.log W₀ - Real.log W with hℓ
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓ]; have := Real.log_le_log hW hWW; linarith
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
    rw [Q.Vf_shift W₀ W x, ← hℓ]
    change 2 * C.μ.U x + (Vf W₀ x - ℓ * x) ≤ C.Sk (k / r2) - ℓ * (k : ℝ) / L'
    rw [mul_div_assoc]
    linarith
  · -- the second tail: it changes by `−(X − ½)ℓ ≤ 0`
    have h2 := C.htail2
    have hXL : 0 ≤ ((C.X : ℝ) - 1 / 2) * ℓ := mul_nonneg (by linarith) hℓ0
    have e : (C.X : ℝ) * Real.log W = C.X * Real.log W₀ - C.X * ℓ := by rw [hℓ]; ring
    change Real.log C.X + C.X * Real.log W - (C.lam - ℓ / 2) < 0
    rw [e]
    nlinarith
  · -- the exponent
    unfold DualCertW.Phi DualCertW.σ
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
    rw [sum_add_distrib, ← mul_sum, Q.sum_hinge m (C.X * L') hm1 hMm] at hsum
    have hrep : ∑ k ∈ range (C.X * L'), max (C.Sk (k / r2) - C.lam) 0 =
        r2 * ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0 := by
      rw [show C.X * L' = r2 * (C.X * C.L) by rw [hL']; ring]
      exact Q.sum_range_mul_div (fun k => max (C.Sk k - C.lam) 0) r2 hr20 _
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

    linarith

end QZ
end Chi2Irr
