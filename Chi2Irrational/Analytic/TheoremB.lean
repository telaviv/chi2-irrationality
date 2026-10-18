/-
# Theorem B: the analytic bound from a dual certificate

A `DualCert q` is a step density `μ` (support `[0, N]`), a threshold `λ`, a grid `[k/L, (k+1)/L]` on `[0, X]`,
and bounds `F(x) = 2U^μ(x) + V(x) ≤ S_k` on the grid cells, together with the tail conditions
`1/X + log W < 0` and `log X + X log W < λ`. `DualCert.analytic` proves
`|Δ_h(χ₂(1/q))| ≤ exp((Φ + ε) h²)` eventually, for
`Φ = −E(μ) + λ + (2/L) Σ_k (S_k − λ)₊`.

Proof: the dual bound of `Dual.lean` with the cell averages `m = h ∫_cell μ` and the threshold `hλ + h log h`;
the discretization bounds of `Discrete.lean`; near nodes counted per grid cell (`near_count`); far nodes summed
geometrically (`F(x) − λ ≤ −δx` beyond `X`); all remainders are `O(h log h)` (`eventually_small`).
-/
import Chi2Irrational.Analytic.Helpers

namespace Chi2Irr

open Finset Real Filter Topology Polynomial

/-- A dual certificate for Theorem B. -/
structure DualCert (q : ℕ) where
  μ : StepData
  lam : ℝ
  L : ℕ
  X : ℕ
  N : ℕ
  Sk : ℕ → ℝ
  hL : 1 ≤ L
  hN : μ.a μ.K ≤ N
  hXN : N ≤ X
  hX : 1 ≤ X
  hF : ∀ k < X * L, ∀ x : ℝ, 0 < x → (k : ℝ) / L ≤ x → x ≤ ((k : ℝ) + 1) / L →
    2 * μ.U x + Vf (Wr q) x ≤ Sk k
  htail1 : 1 / (X : ℝ) + Real.log (Wr q) < 0
  htail2 : Real.log X + X * Real.log (Wr q) - lam < 0

namespace DualCert

variable {q : ℕ} (C : DualCert q)

/-- The excess `Σ_k (S_k − λ)₊`. -/
noncomputable def σ : ℝ := ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0

/-- **The certified exponent** `Φ = −E(μ) + λ + (2/L) Σ_k (S_k − λ)₊`. -/
noncomputable def Phi : ℝ := -C.μ.E + C.lam + 2 / C.L * C.σ

/-- The decay rate beyond `X`. -/
noncomputable def δ : ℝ :=
  -max (1 / (C.X : ℝ) + Real.log (Wr q)) ((Real.log C.X + C.X * Real.log (Wr q) - C.lam) / C.X)

lemma X_pos : (0 : ℝ) < C.X := by exact_mod_cast (by have := C.hX; omega : 0 < C.X)

lemma δ_pos : 0 < C.δ := by
  unfold δ
  have h2 : (Real.log C.X + C.X * Real.log (Wr q) - C.lam) / C.X < 0 := div_neg_of_neg_of_pos C.htail2 C.X_pos
  have := max_lt C.htail1 h2
  linarith

lemma σ_nonneg : 0 ≤ C.σ := Finset.sum_nonneg (fun k _ => le_max_right _ _)

/-- **The tail:** `F(x) − λ ≤ −δx` for `x ≥ X`. -/
lemma tail {x : ℝ} (hx : (C.X : ℝ) ≤ x) : 2 * C.μ.U x + Vf (Wr q) x - C.lam ≤ -C.δ * x := by
  have hX0 := C.X_pos
  have hx0 : 0 < x := by linarith
  have hNX : C.μ.a C.μ.K ≤ x := C.hN.trans ((by exact_mod_cast C.hXN : (C.N : ℝ) ≤ C.X).trans hx)
  have hU := C.μ.U_le_log hNX hx0
  have hV := Vf_le_tail (Wr q) hx0
  have hlog : Real.log x ≤ Real.log C.X + x / C.X - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hX0)
    rw [Real.log_div hx0.ne' hX0.ne'] at this
    linarith
  set c1 := 1 / (C.X : ℝ) + Real.log (Wr q)
  set c2 := (Real.log C.X + C.X * Real.log (Wr q) - C.lam) / C.X
  have hδ : -C.δ = max c1 c2 := by unfold δ; ring
  have e1 : c1 * x = x / C.X + x * Real.log (Wr q) := by simp only [c1]; ring
  have e2 : (C.X : ℝ) * (c2 - c1) = Real.log C.X - C.lam - 1 := by
    simp only [c1, c2]; field_simp; ring
  have hG : 2 * C.μ.U x + Vf (Wr q) x - C.lam ≤ C.X * (c2 - c1) + c1 * x := by
    rw [e1, e2]; linarith
  rw [hδ]
  rcases le_total c1 c2 with h | h
  · rw [max_eq_right h]
    have : (C.X : ℝ) * (c2 - c1) ≤ x * (c2 - c1) := mul_le_mul_of_nonneg_right hx (by linarith)
    nlinarith
  · rw [max_eq_left h]
    have : (C.X : ℝ) * (c2 - c1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hX0.le (by linarith)
    linarith

/-! ### The node weights -/

/-- The cell-average error `8K(1 + log h) + 2 log(Nh + 1)`. -/
noncomputable def errB (h : ℕ) : ℝ := 8 * C.μ.K * (1 + Real.log h) + 2 * Real.log (C.N * h + 1)

lemma errB_nonneg {h : ℕ} (hh : 1 ≤ h) : 0 ≤ C.errB h := by
  unfold errB
  have : 0 ≤ Real.log h := Real.log_nonneg (by exact_mod_cast hh)
  have : 0 ≤ Real.log ((C.N : ℝ) * h + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ C.N * h := by positivity
    linarith)
  positivity

lemma hS {h : ℕ} (hh : 1 ≤ h) : C.μ.a C.μ.K ≤ ((C.N * h : ℕ) : ℝ) / h := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  push_cast; rw [mul_div_assoc, div_self hh0, mul_one]; exact C.hN

/-- The node weight function of the certificate. -/
noncomputable def g (h M s : ℕ) : ℝ := gD q h M (C.μ.mref h) (h * C.lam + h * Real.log h) s

lemma g_le (hq : 2 ≤ q) {h M : ℕ} (hh : 1 ≤ h) (hM : C.N * h + 1 ≤ M) {s : ℕ} (hs : 1 ≤ s) :
    C.g h M s ≤ h * (2 * C.μ.U ((s : ℝ) / h) + Vf (Wr q) ((s : ℝ) / h) - C.lam) + Real.log h +
      Real.log s + 2 * C.errB h := by
  unfold g gD errB
  have h1 := log_bN_le hq hh hs
  have h2 := C.μ.Pm_le hh (C.hS hh) hM s
  push_cast at h2 ⊢
  linarith

lemma g_zero_le {h M : ℕ} (hh : 1 ≤ h) (hM : C.N * h + 1 ≤ M) :
    C.g h M 0 ≤ h * (2 * C.μ.U 0 - C.lam) + h * Real.log h + 2 * C.errB h := by
  unfold g gD errB
  have h1 : Real.log (bN q h 0) = 0 := by simp [bN, phiR]
  have h2 := C.μ.Pm_le hh (C.hS hh) hM 0
  push_cast at h2 ⊢
  rw [zero_div] at h2
  rw [h1]
  linarith

/-! ### Near nodes -/

lemma near_le (hq : 2 ≤ q) {h M : ℕ} (hh : 1 ≤ h) (hM : C.N * h + 1 ≤ M) :
    ∑ s ∈ range (C.X * h + 1), max (C.g h M s) 0 ≤
      (h * |2 * C.μ.U 0 - C.lam| + h * Real.log h + 2 * C.errB h) + h * (((h : ℝ) / C.L + 1) * C.σ) +
        (C.X * h : ℕ) * (Real.log h + Real.log ((C.X * h : ℕ) : ℝ) + 2 * C.errB h) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (by exact_mod_cast hh)
  have herr := C.errB_nonneg hh
  rw [Finset.sum_range_succ']
  -- the node `0`
  have h0 : max (C.g h M 0) 0 ≤ h * |2 * C.μ.U 0 - C.lam| + h * Real.log h + 2 * C.errB h := by
    have := C.g_zero_le hh hM
    have : (h : ℝ) * (2 * C.μ.U 0 - C.lam) ≤ h * |2 * C.μ.U 0 - C.lam| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hh0.le
    have : 0 ≤ (h : ℝ) * |2 * C.μ.U 0 - C.lam| := by positivity
    exact max_le (by linarith) (by nlinarith)
  -- the nodes `1, …, Xh`
  set Fx : ℕ → ℝ := fun s => max (2 * C.μ.U ((s : ℝ) / h) + Vf (Wr q) ((s : ℝ) / h) - C.lam) 0 with hFx
  have hnode : ∀ s ∈ range (C.X * h), max (C.g h M (s + 1)) 0 ≤
      h * Fx (s + 1) + (Real.log h + Real.log ((C.X * h : ℕ) : ℝ) + 2 * C.errB h) := by
    intro s hs
    have hs' := mem_range.mp hs
    have hg := C.g_le hq hh hM (s := s + 1) (by omega)
    have hlogs : Real.log ((s + 1 : ℕ) : ℝ) ≤ Real.log ((C.X * h : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (by omega : s + 1 ≤ C.X * h))
    have hlogs0 : 0 ≤ Real.log ((s + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ s + 1))
    have hmax : (h : ℝ) * (2 * C.μ.U (((s + 1 : ℕ) : ℝ) / h) + Vf (Wr q) (((s + 1 : ℕ) : ℝ) / h) - C.lam) ≤
        h * Fx (s + 1) := mul_le_mul_of_nonneg_left (le_max_left _ _) hh0.le
    have hFx0 : 0 ≤ (h : ℝ) * Fx (s + 1) := mul_nonneg hh0.le (le_max_right _ _)
    exact max_le (by linarith) (by linarith)
  have hcount := near_count (h := h) (L := C.L) (X := C.X) hh C.hL (fun k => max (C.Sk k - C.lam) 0)
    (fun k => le_max_right _ _) Fx (fun s hs1 hsX k hk hlo hhi => by
      simp only [hFx]
      refine max_le_max ?_ le_rfl
      have hpos : (0 : ℝ) < (s : ℝ) / h := div_pos (by exact_mod_cast (by omega : 0 < s)) hh0
      have := C.hF k hk ((s : ℝ) / h) hpos hlo hhi
      linarith)
  have hsum := Finset.sum_le_sum hnode
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul] at hsum
  have := mul_le_mul_of_nonneg_left hcount hh0.le
  unfold σ
  push_cast at hsum this ⊢
  linarith

/-! ### Far nodes -/

/-- The far-node constant `(2/δ)/(1 − e^{−δ/2})`. -/
noncomputable def Cf : ℝ := 2 / C.δ / (1 - Real.exp (-(C.δ / 2)))

lemma Cf_pos : 0 < C.Cf := by
  unfold Cf
  have := C.δ_pos
  have : Real.exp (-(C.δ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have : 0 < 1 - Real.exp (-(C.δ / 2)) := by linarith
  positivity

lemma far_node (hq : 2 ≤ q) {h M : ℕ} (hh : 1 ≤ h) (hM : C.N * h + 1 ≤ M) {s : ℕ} (hs : C.X * h < s) :
    Real.exp (C.g h M s) ≤ 2 / C.δ * h * Real.exp (2 * C.errB h) * Real.exp (-(C.δ / 2)) ^ s := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hδ := C.δ_pos
  have hs1 : 1 ≤ s := by have := C.hX; nlinarith
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hg := C.g_le hq hh hM hs1
  -- the tail of `F`
  have hx : (C.X : ℝ) ≤ (s : ℝ) / h := by
    rw [le_div_iff₀ hh0]; exact_mod_cast hs.le
  have ht := C.tail hx
  have ht' : (h : ℝ) * (2 * C.μ.U ((s : ℝ) / h) + Vf (Wr q) ((s : ℝ) / h) - C.lam) ≤ -C.δ * s := by
    have := mul_le_mul_of_nonneg_left ht hh0.le
    have e : (h : ℝ) * (-C.δ * ((s : ℝ) / h)) = -C.δ * s := by field_simp
    linarith
  -- `log s ≤ δs/2 + log(2/δ)`
  have hlogs : Real.log s ≤ C.δ / 2 * s + Real.log (2 / C.δ) := by
    have := Real.log_le_sub_one_of_pos (show 0 < C.δ / 2 * s by positivity)
    rw [Real.log_mul (by positivity) hs0.ne'] at this
    have e : Real.log (2 / C.δ) = -Real.log (C.δ / 2) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have hg' : C.g h M s ≤ Real.log (2 / C.δ) + Real.log h + 2 * C.errB h + -(C.δ / 2) * s := by linarith
  calc Real.exp (C.g h M s) ≤ Real.exp (Real.log (2 / C.δ) + Real.log h + 2 * C.errB h + -(C.δ / 2) * s) :=
        Real.exp_le_exp.mpr hg'
    _ = 2 / C.δ * h * Real.exp (2 * C.errB h) * Real.exp (-(C.δ / 2)) ^ s := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_log hh0,
          ← Real.exp_nat_mul]
        ring_nf

lemma far_le (hq : 2 ≤ q) {h T : ℕ} (hh : 1 ≤ h) :
    ∑ k : Fin T × Fin 3, zf q h (T + C.N * h + 1) (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k ≤
      3 * ((C.X * h : ℕ) + C.Cf * h * Real.exp (2 * C.errB h)) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hδ := C.δ_pos
  set M := T + C.N * h + 1
  have hM : C.N * h + 1 ≤ M := by omega
  set r := Real.exp (-(C.δ / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set Cg := 2 / C.δ * h * Real.exp (2 * C.errB h) with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  set f : ℕ → ℝ := fun t => if t + 1 ≤ C.X * h then 1 else Real.exp (C.g h M (t + 1)) with hf
  have hzf : ∀ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k = f k.1 := by
    intro k; simp only [zf, tnode, hf]; rfl
  rw [Fintype.sum_prod_type]
  simp_rw [hzf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun t => f t) T]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hbound : ∀ t ∈ range T, f t ≤ (if t + 1 ≤ C.X * h then 1 else 0) + Cg * r ^ (t + 1) := by
    intro t _
    simp only [hf]
    split_ifs with ht
    · have : 0 ≤ Cg * r ^ (t + 1) := by positivity
      linarith
    · rw [zero_add, hCg]
      exact C.far_node hq hh hM (by omega)
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (((range T).filter (fun t => t + 1 ≤ C.X * h)).card : ℝ) ≤ (C.X : ℝ) * h := by
    have : ((range T).filter (fun t => t + 1 ≤ C.X * h)).card ≤ C.X * h := by
      refine (Finset.card_le_card (t := range (C.X * h)) (fun t ht => ?_)).trans (card_range _).le
      simp only [mem_filter, mem_range] at ht ⊢; omega
    exact_mod_cast this
  have hgeo := sum_geom_succ_le hr0 hr1 T
  have : Cg * ∑ t ∈ range T, r ^ (t + 1) ≤ Cg * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeo hCg0
  have e : Cg * (1 / (1 - r)) = C.Cf * h * Real.exp (2 * C.errB h) := by
    simp only [hCg, Cf, hr]; ring
  linarith

/-! ### The dual constant -/

lemma Cd_le {h M : ℕ} (hh : 1 ≤ h) (hM : C.N * h + 1 ≤ M) :
    Cd h M (C.μ.mref h) (h * C.lam + h * Real.log h) ≤
      (h : ℝ) ^ 2 * (C.lam - C.μ.E) + 4 * h * Real.log (C.N * h + 1) + 8 * h * Real.log 2 := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hE := C.μ.Em_ge hh (C.hS hh) hM
  have hmsum : ∑ s ∈ range M, C.μ.mref h s = h := by
    rw [sum_range_support hM (C.μ.mref h) (C.μ.mref_zero h) (fun n hn => C.μ.mref_supp hh (C.hS hh) n hn)]
    exact C.μ.sum_mref_cells hh (C.hS hh)
  have hsq : ∑ s ∈ range M, C.μ.mref h s ^ 2 ≤ 2 * h := by
    calc ∑ s ∈ range M, C.μ.mref h s ^ 2 ≤ ∑ s ∈ range M, 2 * C.μ.mref h s :=
          Finset.sum_le_sum (fun s _ => by
            have := C.μ.mref_nonneg (h := h) (by omega) s
            have := C.μ.mref_le_two (h := h) (by omega) s
            nlinarith)
      _ = 2 * h := by rw [← Finset.mul_sum, hmsum]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold Cd
  push_cast at hE ⊢
  nlinarith

/-! ### Assembly -/

/-- The far-node bound `Z(h) = 3(Xh + C_f h e^{2·err})`. -/
noncomputable def Zb (h : ℕ) : ℝ := 3 * ((C.X * h : ℕ) + C.Cf * h * Real.exp (2 * C.errB h))

/-- The remainder (all `O(h log h)`). -/
noncomputable def Rem (h : ℕ) : ℝ :=
  2 * h * Real.log h + 4 * h + 4 * h * Real.log (C.N * h + 1) + 8 * h * Real.log 2 +
    2 * ((h * |2 * C.μ.U 0 - C.lam| + h * Real.log h + 2 * C.errB h) + h * C.σ +
      (C.X * h : ℕ) * (Real.log h + Real.log ((C.X * h : ℕ) : ℝ) + 2 * C.errB h)) + h * Real.log (C.Zb h)

lemma Zb_pos {h : ℕ} (hh : 1 ≤ h) : 0 < C.Zb h := by
  unfold Zb
  have := C.Cf_pos
  have : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  positivity

/-- **The truncated determinants, uniformly in `T`.** -/
theorem det_bound (hq : 2 ≤ q) {h : ℕ} (hh : 2 ≤ h) (T : ℕ) :
    |(HT q h T).det| ≤ Real.exp (C.Phi * (h : ℝ) ^ 2 + C.Rem h) := by
  have hh1 : 1 ≤ h := by omega
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  set M := T + C.N * h + 1 with hMdef
  have hM : C.N * h + 1 ≤ M := by omega
  have hTM : T < M := by omega
  have hmsum : ∑ s ∈ range M, C.μ.mref h s = h := by
    rw [sum_range_support hM (C.μ.mref h) (C.μ.mref_zero h) (fun n hn => C.μ.mref_supp hh1 (C.hS hh1) n hn)]
    exact C.μ.sum_mref_cells hh1 (C.hS hh1)
  have hdual := abs_det_HT_le_dual hq hh hTM (C.μ.mref h) hmsum (h * C.lam + h * Real.log h) (C.X * h)
  -- the pieces
  have hfar := C.far_le hq (T := T) hh1
  have hnear := C.near_le hq hh1 hM
  have hCd := C.Cd_le hh1 hM
  have hK := log_Kslot_sq_le hh1
  have hZ := C.Zb_pos hh1
  have hKpos : 0 < Kslot h ^ 2 := by unfold Kslot; positivity
  have hfac1 : (1 : ℝ) ≤ h.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero h)
  have hfac : ((h.factorial : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hfac1
  have hzf0 : 0 ≤ ∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k :=
    Finset.sum_nonneg (fun k _ => by unfold zf; split_ifs <;> positivity)
  have hpow : (∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k) ^ h ≤
      C.Zb h ^ h := pow_le_pow_left₀ hzf0 hfar h
  refine hdual.trans ?_
  generalize hE1 : Cd h M (C.μ.mref h) (h * C.lam + h * Real.log h) +
    2 * ∑ s ∈ range (C.X * h + 1), max (gD q h M (C.μ.mref h) (h * C.lam + h * Real.log h) s) 0 = E1
  have hstep : ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 * (Real.exp E1 *
      (∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k) ^ h) ≤
      Real.exp (Real.log (Kslot h ^ 2) + E1 + h * Real.log (C.Zb h)) := by
    calc ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 * (Real.exp E1 *
          (∑ k : Fin T × Fin 3, zf q h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * h) k) ^ h)
        ≤ 1 * Kslot h ^ 2 * (Real.exp E1 * C.Zb h ^ h) := by gcongr
      _ = _ := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hKpos, Real.exp_nat_mul, Real.exp_log hZ]; ring
  refine hstep.trans (Real.exp_le_exp.mpr ?_)
  -- the exponent
  have hnear' : ∑ s ∈ range (C.X * h + 1), max (gD q h M (C.μ.mref h) (h * C.lam + h * Real.log h) s) 0 ≤
      (h * |2 * C.μ.U 0 - C.lam| + h * Real.log h + 2 * C.errB h) + h * (((h : ℝ) / C.L + 1) * C.σ) +
        (C.X * h : ℕ) * (Real.log h + Real.log ((C.X * h : ℕ) : ℝ) + 2 * C.errB h) := hnear
  have hL0 : (0 : ℝ) < C.L := by exact_mod_cast (by have := C.hL; omega : 0 < C.L)
  have eΦ : C.Phi * (h : ℝ) ^ 2 = (h : ℝ) ^ 2 * (C.lam - C.μ.E) + 2 * h * ((h : ℝ) / C.L * C.σ) := by
    unfold Phi; field_simp; ring
  unfold Rem
  rw [← hE1, eΦ]
  nlinarith

/-- The remainder is `O(h log h)`. -/
lemma Rem_le : ∃ a b c : ℝ, ∀ h : ℕ, 1 ≤ h → C.Rem h ≤ a * h * Real.log h + b * h + c := by
  set cN := Real.log ((C.N : ℝ) + 1)
  set cX := Real.log (C.X : ℝ)
  set cZ := Real.log (3 * ((C.X : ℝ) + C.Cf))
  set u0 := |2 * C.μ.U 0 - C.lam|
  set e0 := 8 * (C.μ.K : ℝ) + 2 * cN
  set e1 := 8 * (C.μ.K : ℝ) + 2
  refine ⟨9 + 4 * C.X + 4 * C.X * e1 + 6 * e1,
    4 + 4 * cN + 8 * Real.log 2 + 2 * u0 + 2 * C.σ + 2 * C.X * cX + 4 * C.X * e0 + cZ + 2 * e0, 4 * e0,
    fun h hh => ?_⟩
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hX0 := C.X_pos
  have hCf := C.Cf_pos
  set Lg := Real.log (h : ℝ) with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg hh1
  have hK0 : (0 : ℝ) ≤ C.μ.K := Nat.cast_nonneg _
  have he1 : 0 ≤ e1 := by positivity
  -- `log(Nh + 1) ≤ log(N+1) + log h`
  have F1 : Real.log ((C.N : ℝ) * h + 1) ≤ cN + Lg := by
    rw [hLg, ← Real.log_mul (by positivity) hh0.ne']
    exact Real.log_le_log (by positivity) (by nlinarith [(Nat.cast_nonneg C.N : (0 : ℝ) ≤ C.N)])
  have F2 : C.errB h ≤ e0 + e1 * Lg := by unfold errB; linarith
  have herr := C.errB_nonneg hh
  have F3 : Real.log (((C.X * h : ℕ) : ℝ)) = cX + Lg := by
    push_cast; rw [Real.log_mul hX0.ne' hh0.ne']
  have F4 : Real.log (C.Zb h) ≤ cZ + Lg + 2 * C.errB h := by
    have hE : 1 ≤ Real.exp (2 * C.errB h) := Real.one_le_exp (by linarith)
    have hle : C.Zb h ≤ 3 * ((C.X : ℝ) + C.Cf) * h * Real.exp (2 * C.errB h) := by
      unfold Zb; push_cast
      have : (C.X : ℝ) * h ≤ C.X * h * Real.exp (2 * C.errB h) := by
        have := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ C.X * h)
        linarith
      nlinarith
    calc Real.log (C.Zb h) ≤ Real.log (3 * ((C.X : ℝ) + C.Cf) * h * Real.exp (2 * C.errB h)) :=
          Real.log_le_log (C.Zb_pos hh) hle
      _ = cZ + Lg + 2 * C.errB h := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hh0.ne',
            Real.log_exp]
  have P1 := mul_le_mul_of_nonneg_left F1 hh0.le
  have P3 := mul_le_mul_of_nonneg_left F2 (by positivity : (0 : ℝ) ≤ C.X * h)
  have P4 := mul_le_mul_of_nonneg_left F4 hh0.le
  have P4' := mul_le_mul_of_nonneg_left F2 hh0.le
  have P5 : e1 * Lg ≤ e1 * (h * Lg) := mul_le_mul_of_nonneg_left (by nlinarith) he1
  unfold Rem
  rw [F3]
  push_cast
  nlinarith

/-- **Theorem B** (from a dual certificate). -/
theorem analytic (hq : 2 ≤ q) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    |aeval (chi2 (1 / (q : ℝ))) (Delta q h)| ≤ Real.exp ((C.Phi + ε) * (h : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨a, b, c, hR⟩ := C.Rem_le
  filter_upwards [eventually_small a b c ε hε, eventually_ge_atTop 2] with h hsmall hh
  refine abs_Delta_le_of hq h (fun T => (C.det_bound hq hh T).trans (Real.exp_le_exp.mpr ?_))
  have := hR h (by omega)
  nlinarith

end DualCert

end Chi2Irr
