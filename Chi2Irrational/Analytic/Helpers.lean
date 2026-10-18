/-
# Theorem B, helpers: counting, tails and absorbing `O(h log h)`

* `eventually_small`: `a h log h + b h + c ≤ ε h²` eventually;
* `near_count`: a sum over the nodes `s = 1, …, Xh` of a function bounded on the grid cells `[k/L, (k+1)/L]` by `φ_k`
  is at most `(h/L + 1) Σ_k φ_k` (each cell holds at most `h/L + 1` nodes);
* `sum_geom_succ_le`: `Σ_{t<T} r^{t+1} ≤ 1/(1 − r)`;
* `log_Kslot_sq_le`: `log K² ≤ 2h log h + 4h`;
* `StepData.U_le_log`, `Vf_le_tail`: beyond the support, `U^μ(x) ≤ log x` and `V(x) ≤ x log W − log x`.
-/
import Chi2Irrational.Analytic.Discrete

namespace Chi2Irr

open Finset Real Filter Topology

/-- `a h log h + b h + c = o(h²)`. -/
lemma eventually_small (a b c ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, a * h * Real.log h + b * h + c ≤ ε * (h : ℝ) ^ 2 := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hpos : (0 : ℝ) < ε / (3 * (|a| + 1)) := by positivity
  have h2 := (h1.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hpos)
  filter_upwards [h2, eventually_ge_atTop (⌈3 * (|b| + |c| + 1) / ε⌉₊ + 1)] with h hlog hbig
  simp only [Function.comp] at hlog
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (by omega : 1 ≤ h)
  have hh0 : (0 : ℝ) < h := by linarith
  have hbig' : 3 * (|b| + |c| + 1) / ε ≤ h := by
    have := Nat.le_ceil (3 * (|b| + |c| + 1) / ε)
    have : ((⌈3 * (|b| + |c| + 1) / ε⌉₊ + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hbig
    push_cast at this; linarith
  have hlog0 : 0 ≤ Real.log h := Real.log_nonneg hh1
  -- the `h log h` part
  have ha : a * h * Real.log h ≤ ε / 3 * (h : ℝ) ^ 2 := by
    have e : Real.log h = (Real.log h / h) * h := by field_simp
    have hq : Real.log h / h * |a| ≤ ε / 3 := by
      have : Real.log h / h ≤ ε / (3 * (|a| + 1)) := hlog.le
      have hdiv : ε / (3 * (|a| + 1)) * |a| ≤ ε / 3 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg a]
      calc Real.log h / h * |a| ≤ ε / (3 * (|a| + 1)) * |a| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg a)
        _ ≤ ε / 3 := hdiv
    calc a * h * Real.log h ≤ |a| * h * Real.log h := by
          have := le_abs_self a
          have := mul_nonneg hh0.le hlog0
          nlinarith
      _ = (Real.log h / h * |a|) * h ^ 2 := by rw [e]; field_simp
      _ ≤ ε / 3 * (h : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hq (by positivity)
  -- the linear part
  have hb : b * h + c ≤ ε / 3 * (h : ℝ) ^ 2 := by
    have h3 : 3 * (|b| + |c| + 1) ≤ ε * h := by
      rw [div_le_iff₀ hε] at hbig'; linarith
    have := le_abs_self b
    have := le_abs_self c
    have : b * h ≤ |b| * h := by nlinarith
    have : c ≤ |c| * h := by nlinarith [abs_nonneg c]
    nlinarith
  nlinarith [sq_nonneg (h : ℝ)]

/-- **Nodes per grid cell.** -/
lemma near_count {h L X : ℕ} (hh : 1 ≤ h) (hL : 1 ≤ L) (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k) (G : ℕ → ℝ)
    (hG : ∀ s, 1 ≤ s → s ≤ X * h → ∀ k, k < X * L → (k : ℝ) / L ≤ (s : ℝ) / h →
      (s : ℝ) / h ≤ ((k : ℝ) + 1) / L → G s ≤ φ k) :
    ∑ s ∈ range (X * h), G (s + 1) ≤ ((h : ℝ) / L + 1) * ∑ k ∈ range (X * L), φ k := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set κ : ℕ → ℕ := fun s => ((s + 1) * L - 1) / h with hκ
  have hpos : ∀ s, 1 ≤ (s + 1) * L := fun s => Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the cell of each node
  have hlo : ∀ s, κ s * h + 1 ≤ (s + 1) * L := fun s => by
    have := Nat.div_mul_le_self ((s + 1) * L - 1) h
    have := hpos s
    simp only [hκ]; omega
  have hhi : ∀ s, (s + 1) * L ≤ (κ s + 1) * h := fun s => by
    have h1 := Nat.lt_div_mul_add (a := (s + 1) * L - 1) (show 0 < h by omega)
    have h2 := hpos s
    have e : (κ s + 1) * h = ((s + 1) * L - 1) / h * h + h := by simp only [hκ]; ring
    rw [e]; omega
  have hmaps : ∀ s ∈ range (X * h), κ s ∈ range (X * L) := by
    intro s hs
    rw [mem_range] at hs ⊢
    simp only [hκ]
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : (s + 1) * L ≤ X * h * L := Nat.mul_le_mul_right L (by omega)
    have := hpos s
    calc (s + 1) * L - 1 < X * h * L := by omega
      _ = X * L * h := by ring
  have hreal_lo : ∀ s, (κ s : ℝ) / L ≤ ((s + 1 : ℕ) : ℝ) / h := fun s => by
    rw [div_le_div_iff₀ hL0 hh0]
    have : ((κ s * h + 1 : ℕ) : ℝ) ≤ ((s + 1) * L : ℕ) := by exact_mod_cast hlo s
    push_cast at this ⊢; linarith
  have hreal_hi : ∀ s, ((s + 1 : ℕ) : ℝ) / h ≤ ((κ s : ℝ) + 1) / L := fun s => by
    rw [div_le_div_iff₀ hh0 hL0]
    have : (((s + 1) * L : ℕ) : ℝ) ≤ ((κ s + 1) * h : ℕ) := by exact_mod_cast hhi s
    push_cast at this ⊢; linarith
  -- each node is bounded by its cell
  have hstep : ∑ s ∈ range (X * h), G (s + 1) ≤ ∑ s ∈ range (X * h), φ (κ s) :=
    Finset.sum_le_sum (fun s hs => hG (s + 1) (by omega) (by have := mem_range.mp hs; omega) (κ s)
      (mem_range.mp (hmaps s hs)) (hreal_lo s) (hreal_hi s))
  -- fibers
  have hfib : ∀ k, (((range (X * h)).filter (fun s => κ s = k)).card : ℝ) ≤ (h : ℝ) / L + 1 := by
    intro k
    set lo := (k * h + L) / L with hlo_def
    set hi := (k + 1) * h / L with hhi_def
    have hsub : ((range (X * h)).filter (fun s => κ s = k)).card ≤ (Icc lo hi).card := by
      refine Finset.card_le_card_of_injOn (fun s => s + 1) (fun s hs => ?_) (fun a _ b _ e => by
        simpa using e)
      simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hs
      simp only [coe_Icc, Set.mem_Icc]
      have h1 := hlo s
      have h2 := hhi s
      rw [hs.2] at h1 h2
      constructor
      · rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
        have e1 : L * (s + 1) = (s + 1) * L := by ring
        omega
      · rw [Nat.le_div_iff_mul_le (by omega)]; exact h2
    have hcard : ((Icc lo hi).card : ℝ) ≤ (h : ℝ) / L + 1 := by
      rw [Nat.card_Icc]
      have hloL : k * h + 1 ≤ lo * L := by
        have := Nat.lt_div_mul_add (a := k * h + L) (show 0 < L by omega)
        rw [← hlo_def] at this
        omega
      have hhiL : hi * L ≤ (k + 1) * h := by rw [hhi_def]; exact Nat.div_mul_le_self _ _
      rcases le_or_gt lo (hi + 1) with hle | hgt
      · rw [Nat.cast_sub hle]
        have a1 : ((k * h + 1 : ℕ) : ℝ) ≤ ((lo * L : ℕ) : ℝ) := by exact_mod_cast hloL
        have a2 : ((hi * L : ℕ) : ℝ) ≤ (((k + 1) * h : ℕ) : ℝ) := by exact_mod_cast hhiL
        push_cast at a1 a2 ⊢
        have : ((hi : ℝ) + 1 - lo) * L ≤ h + L := by nlinarith
        rw [div_add_one hL0.ne', le_div_iff₀ hL0]
        linarith
      · rw [Nat.sub_eq_zero_of_le (by omega)]
        push_cast; positivity
    exact (by exact_mod_cast hsub : (((range (X * h)).filter (fun s => κ s = k)).card : ℝ) ≤
      ((Icc lo hi).card : ℝ)).trans hcard
  calc ∑ s ∈ range (X * h), G (s + 1) ≤ ∑ s ∈ range (X * h), φ (κ s) := hstep
    _ = ∑ k ∈ range (X * L), ∑ s ∈ (range (X * h)).filter (fun s => κ s = k), φ (κ s) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ range (X * L), (((range (X * h)).filter (fun s => κ s = k)).card : ℝ) * φ k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_congr rfl (fun s hs => by rw [(mem_filter.mp hs).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ k ∈ range (X * L), ((h : ℝ) / L + 1) * φ k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hfib k) (hφ k))
    _ = _ := by rw [Finset.mul_sum]

lemma sum_geom_succ_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (T : ℕ) :
    ∑ t ∈ range T, r ^ (t + 1) ≤ 1 / (1 - r) := by
  have := geom_sum_Ico_le_of_lt_one (m := 1) (n := T + 1) hr0 hr1
  rw [Finset.sum_Ico_eq_sum_range] at this
  simp only [add_tsub_cancel_right, pow_one] at this
  calc ∑ t ∈ range T, r ^ (t + 1) = ∑ k ∈ range T, r ^ (1 + k) :=
        Finset.sum_congr rfl (fun t _ => by rw [add_comm])
    _ ≤ r / (1 - r) := this
    _ ≤ 1 / (1 - r) := div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `log K² ≤ 2h log h + 4h`. -/
lemma log_Kslot_sq_le {h : ℕ} (hh : 1 ≤ h) :
    Real.log (Kslot h ^ 2) ≤ 2 * h * Real.log h + 4 * h := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have h1 : (0 : ℝ) < 1 + 2 / h := by positivity
  unfold Kslot
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have := Real.log_le_sub_one_of_pos h1
  have e : ((h ^ 2 : ℕ) : ℝ) * (2 / h) = 2 * h := by push_cast; field_simp
  have : ((h ^ 2 : ℕ) : ℝ) * Real.log (1 + 2 / h) ≤ ((h ^ 2 : ℕ) : ℝ) * (2 / h) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  push_cast at this e ⊢
  nlinarith

/-- Beyond the support the potential is at most `log x`. -/
lemma StepData.U_le_log (μ : StepData) {x : ℝ} (hx : μ.a μ.K ≤ x) (hx0 : 0 < x) :
    μ.U x ≤ Real.log x := by
  unfold StepData.U
  calc ∑ j ∈ range μ.K, μ.c j * Uint x (μ.a j) (μ.a (j + 1))
      ≤ ∑ j ∈ range μ.K, μ.c j * ((μ.a (j + 1) - μ.a j) * Real.log x) := by
        refine Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left ?_ (μ.c0 j))
        have hjK : μ.a (j + 1) ≤ μ.a μ.K := μ.a_mono (by have := mem_range.mp hj; omega)
        have := psiF_diff_le hx0 (by linarith [μ.amono j] : x - μ.a (j + 1) ≤ x - μ.a j)
          (by linarith [μ.a_nonneg (j + 1)]) (by linarith [μ.a_nonneg j]) (Or.inl (by linarith))
        unfold Uint
        convert this using 2; ring
    _ = (∑ j ∈ range μ.K, μ.c j * (μ.a (j + 1) - μ.a j)) * Real.log x := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = Real.log x := by rw [μ.mass, one_mul]

lemma Vf_le_tail (W : ℝ) {x : ℝ} (hx : 0 < x) : Vf W x ≤ x * Real.log W - Real.log x := by
  have := psiF_diff_ge_pos hx (le_refl x) (by linarith : x ≤ x + 1)
  unfold Vf
  have e : (x + 1 - x) * Real.log x = Real.log x := by ring
  rw [e] at this
  linarith

end Chi2Irr
