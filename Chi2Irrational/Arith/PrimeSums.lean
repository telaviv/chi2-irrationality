/- # Prime sums for the arithmetic part: the `φ₁` window and the `lev` tail

Two PNT consequences used in the arithmetic bound:
* `eventually_primeSum_phi1_le`: `∑_{2h/5 ≤ p < 2h} h φ₁(p/h) log p ≤ (17/12 + ε) h²` eventually, where
  `17/12 = ∫_{2/5}^2 φ₁` (`integral_phi1`). Proof: upper Riemann sums of the antitone `φ₁` on `M` equal cells
  (`phi1_riemann_le`, error `≤ 2·(8/5)/M`) fed into the step-function PNT bound `eventually_primeSum_step_le`.
* `eventually_primeSum_lev_le`: `∑_{p < 2h/5} 2h lev(p) log p ≤ (4/5 + ε) h²` eventually. Proof: `lev(p) ≤ 1` when
  `p² > 2h − 1`, and `lev(p) log p ≤ log(2h)` always, so the sum is `≤ 2h (θ(2h/5) + (√(2h) + 1) log(2h))`;
  then PNT (`θ(2h/5) ~ 2h/5`) and `√x log x = o(x)`.
Uses the prime number theorem of `Chi2Irrational.PNT`.
-/
import Chi2Irrational.PNT.PrimeSums
import Chi2Irrational.Arith.Defs

open Filter Topology Finset
open scoped Chebyshev

namespace Chi2Irr

open PNT

/-! ### `φ₁`: monotonicity, integral, Riemann sums -/

theorem phi1_nonneg (x : ℝ) : 0 ≤ phi1 x := by
  unfold phi1
  split_ifs <;> linarith

theorem phi1_antitone : Antitone phi1 := by
  intro x y hxy
  unfold phi1
  split_ifs <;> linarith

theorem integral_phi1 : ∫ x in (2/5 : ℝ)..2, phi1 x = 17 / 12 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable phi1 MeasureTheory.volume a b :=
    fun a b => phi1_antitone.intervalIntegrable
  have hs : ∫ x in (2/5 : ℝ)..2, phi1 x = (∫ x in (2/5 : ℝ)..(1/2), phi1 x) +
      (∫ x in (1/2 : ℝ)..(2/3), phi1 x) + (∫ x in (2/3 : ℝ)..1, phi1 x) +
      ∫ x in (1 : ℝ)..2, phi1 x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  rw [hs]
  have e1 : ∫ x in (2/5 : ℝ)..(1/2), phi1 x = ∫ x in (2/5 : ℝ)..(1/2), (3 - 5 / 2 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    unfold phi1
    split_ifs <;> linarith
  have e2 : ∫ x in (1/2 : ℝ)..(2/3), phi1 x = ∫ x in (1/2 : ℝ)..(2/3), (2 - 1 / 2 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    unfold phi1
    split_ifs <;> linarith
  have e3 : ∫ x in (2/3 : ℝ)..1, phi1 x = ∫ x in (2/3 : ℝ)..1, (3 - 2 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    unfold phi1
    split_ifs <;> linarith
  have e4 : ∫ x in (1 : ℝ)..2, phi1 x = ∫ x in (1 : ℝ)..2, (2 - 1 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    unfold phi1
    split_ifs <;> linarith
  rw [e1, e2, e3, e4]
  simp only [intervalIntegral.integral_sub intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_id).const_mul _), intervalIntegral.integral_const,
    smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_id, integral_id]
  norm_num

/-- Upper Riemann sum of an antitone function, cells `[b − (i+1)Δ, b − iΔ]`. -/
theorem antitone_riemann_le {f : ℝ → ℝ} (hf : Antitone f) (b Δ : ℝ) (hΔ : 0 ≤ Δ) (M : ℕ) :
    ∑ i ∈ range M, f (b - (i + 1) * Δ) * Δ ≤
      (∫ x in (b - M * Δ)..b, f x) + (f (b - M * Δ) - f b) * Δ := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hi : ∀ a c : ℝ, IntervalIntegrable f MeasureTheory.volume a c :=
      fun a c => hf.intervalIntegrable
    rw [sum_range_succ, ← intervalIntegral.integral_add_adjacent_intervals
      (hi (b - ((M + 1 : ℕ) : ℝ) * Δ) (b - M * Δ)) (hi _ b)]
    have hcell : (f (b - M * Δ)) * Δ ≤ ∫ x in (b - ((M + 1 : ℕ) : ℝ) * Δ)..(b - M * Δ), f x := by
      have hle : b - ((M + 1 : ℕ) : ℝ) * Δ ≤ b - M * Δ := by push_cast; nlinarith
      have := intervalIntegral.integral_mono_on hle intervalIntegrable_const (hi _ _)
        (fun x hx => hf hx.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      push_cast at this ⊢
      nlinarith
    push_cast at hcell ⊢
    nlinarith

theorem phi1_riemann_le (M : ℕ) (hM : 0 < M) :
    ∑ i ∈ range M, phi1 (2 - (i + 1) * (8 / 5 / M)) * (8 / 5 / M) ≤ 17 / 12 + 2 * (8 / 5 / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h := antitone_riemann_le phi1_antitone 2 (8 / 5 / M) (by positivity) M
  have e : (2 : ℝ) - M * (8 / 5 / M) = 2 / 5 := by field_simp; ring
  rw [e, integral_phi1] at h
  have h1 : phi1 (2 / 5) = 2 := by unfold phi1; norm_num
  have h2 : phi1 2 = 0 := by unfold phi1; norm_num
  rw [h1, h2] at h
  linarith


/-! ### The `φ₁` window -/

theorem eventually_primeSum_phi1_le (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h : ℕ in Filter.atTop,
    ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 2 * h ≤ 5 * p),
      (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p ≤ (17 / 12 + ε) * (h : ℝ) ^ 2 := by
  -- the number of cells
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 32 / (5 * ε) < M := exists_nat_gt _
  have hM0' : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM0 : 0 < M := by exact_mod_cast hM0'
  set Δ : ℝ := 8 / 5 / M with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hΔε : 2 * Δ ≤ ε / 2 := by
    have h1 : 32 < (M : ℝ) * (5 * ε) := by rwa [div_lt_iff₀ (by positivity)] at hM
    rw [hΔ, ← sub_nonneg]
    have e : ε / 2 - 2 * (8 / 5 / (M : ℝ)) = (ε * 5 * M - 32) / (10 * M) := by
      field_simp
      ring
    rw [e]
    exact div_nonneg (by nlinarith) (by positivity)
  have hMΔ : (M : ℝ) * Δ = 8 / 5 := by rw [hΔ]; field_simp
  set x : ℕ → ℝ := fun i => 1 / (2 - i * Δ) with hxdef
  set u : ℕ → ℝ := fun i => phi1 (2 - (i + 1) * Δ) with hudef
  have hpos : ∀ i ≤ M, 2 / 5 ≤ 2 - (i : ℝ) * Δ := by
    intro i hi
    have : (i : ℝ) ≤ M := by exact_mod_cast hi
    nlinarith
  have hx0 : 0 < x 0 := by simp [hxdef]
  have hx : ∀ i < M, x i < x (i + 1) := by
    intro i hi
    have h1 := hpos (i + 1) hi
    simp only [hxdef]
    push_cast at h1 ⊢
    apply one_div_lt_one_div_of_lt (by linarith)
    nlinarith
  have hinv : ∀ i ≤ M, 1 / x i = 2 - i * Δ := by
    intro i _
    simp [hxdef]
  have hh : ∀ i < M, ∀ y, x i < y → y < x (i + 1) → phi1 (1 / y) ≤ u i := by
    intro i hi y _ hy2
    have h1 := hpos (i + 1) hi
    have hy0 : 0 < y := lt_trans hx0 (lt_of_le_of_lt (PNT.le_of_chain hx i hi.le) (by
      have := hx i hi; linarith))
    have : 1 / x (i + 1) < 1 / y := one_div_lt_one_div_of_lt hy0 hy2
    rw [hinv (i + 1) hi] at this
    push_cast at this
    exact phi1_antitone this.le
  have hstep := eventually_primeSum_step_le (fun y => phi1 (1 / y)) x u M hx0 hx hh (half_pos hε)
  filter_upwards [hstep, eventually_ge_atTop 6] with h hs h6
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  -- the Riemann sum
  have hsum : ∑ i ∈ range M, u i * (1 / x i - 1 / x (i + 1)) ≤ 17 / 12 + ε / 2 := by
    have e : ∀ i ∈ range M, u i * (1 / x i - 1 / x (i + 1)) =
        phi1 (2 - (i + 1) * (8 / 5 / M)) * (8 / 5 / M) := by
      intro i hi
      rw [mem_range] at hi
      rw [hinv i hi.le, hinv (i + 1) hi]
      simp only [hudef, hΔ]
      push_cast
      ring
    rw [sum_congr rfl e]
    have := phi1_riemann_le M hM0
    rw [← hΔ] at this ⊢
    linarith
  have e0 : (h : ℝ) / x 0 = 2 * h := by simp [hxdef, mul_comm]
  have eM : (h : ℝ) / x M = 2 * h / 5 := by
    simp only [hxdef, hMΔ]
    field_simp
    ring
  rw [e0, eM] at hs
  -- the target is at most `h · primeSum`
  have hsub : ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 2 * h ≤ 5 * p),
      phi1 ((p : ℝ) / h) * Real.log p ≤
      primeSum (fun p => phi1 (1 / ((h : ℝ) / p))) (2 * h / 5) (2 * h) := by
    rw [primeSum_eq_sum_filter _ (by positivity) (range (2 * h + 1))]
    · have e : ∀ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 2 * h ≤ 5 * p),
          phi1 ((p : ℝ) / h) * Real.log p = phi1 (1 / ((h : ℝ) / p)) * Real.log p := by
        intro p _
        rw [one_div_div]
      rw [sum_congr rfl e]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [mem_filter, mem_range] at hp ⊢
        obtain ⟨hp1, hp2, hp3⟩ := hp
        have hne : 2 * h ≠ 5 * p := by
          intro heq
          have h2 : 2 ∣ p := by omega
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp2).mp h2
          omega
        have hlt : 2 * h < 5 * p := lt_of_le_of_ne hp3 hne
        refine ⟨by omega, hp2, ?_, ?_⟩
        · rw [div_lt_iff₀ (by norm_num)]
          exact_mod_cast (by omega : 2 * h < p * 5)
        · exact_mod_cast hp1.le
      · intro p _ _
        exact mul_nonneg (phi1_nonneg _) (Real.log_natCast_nonneg p)
    · intro p _ _ hpd
      rw [mem_range]
      have : p ≤ 2 * h := by exact_mod_cast hpd
      omega
  have e1 : ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 2 * h ≤ 5 * p),
      (h : ℝ) * phi1 ((p : ℝ) / h) * Real.log p = (h : ℝ) * ∑ p ∈ (Finset.range (2 * h)).filter
        (fun p => p.Prime ∧ 2 * h ≤ 5 * p), phi1 ((p : ℝ) / h) * Real.log p := by
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by ring
  rw [e1]
  have h3 : primeSum (fun p => phi1 (1 / ((h : ℝ) / p))) (2 * h / 5) (2 * h) ≤
      (h : ℝ) * (17 / 12 + ε / 2) + ε / 2 * h := by
    have := mul_le_mul_of_nonneg_left hsum hh0.le
    exact hs.trans (by linarith)
  calc (h : ℝ) * ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 2 * h ≤ 5 * p),
        phi1 ((p : ℝ) / h) * Real.log p
      ≤ (h : ℝ) * ((h : ℝ) * (17 / 12 + ε / 2) + ε / 2 * h) :=
        mul_le_mul_of_nonneg_left (hsub.trans h3) hh0.le
    _ = (17 / 12 + ε) * (h : ℝ) ^ 2 := by ring

/-! ### The `lev` tail -/

/-- `lev(p) ≤ 1` when `p² > 2K − 1`. -/
theorem lev_le_one {K p : ℕ} (hp : p.Prime) (hpp : 2 * K - 1 < p * p) : lev K p ≤ 1 := by
  unfold lev
  calc ((Finset.Icc 1 (2 * K)).filter (fun e => p ^ e ≤ 2 * K - 1)).card ≤ ({1} : Finset ℕ).card := by
        apply card_le_card
        intro e he
        simp only [mem_filter, mem_Icc] at he
        obtain ⟨⟨he1, _⟩, he2⟩ := he
        rw [mem_singleton]
        by_contra hne
        have h2 : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
        rw [pow_two] at h2
        omega
    _ = 1 := card_singleton 1

/-- `lev(p) · log p ≤ log(2K)` for a prime `p` and `K ≥ 1`. -/
theorem lev_mul_log_le {K p : ℕ} (hp : p.Prime) (hK : 1 ≤ K) :
    (lev K p : ℝ) * Real.log p ≤ Real.log (2 * K) := by
  set L := Nat.log p (2 * K - 1)
  have hlev : lev K p ≤ L := by
    unfold lev
    calc ((Finset.Icc 1 (2 * K)).filter (fun e => p ^ e ≤ 2 * K - 1)).card
        ≤ (Finset.Icc 1 L).card := by
          apply card_le_card
          intro e he
          simp only [mem_filter, mem_Icc] at he ⊢
          exact ⟨he.1.1, Nat.le_log_of_pow_le hp.one_lt he.2⟩
      _ = L := by simp
  have hpL : p ^ L ≤ 2 * K - 1 := Nat.pow_log_le_self p (by omega)
  have hpL' : ((p ^ L : ℕ) : ℝ) ≤ 2 * K := by
    have : ((2 * K - 1 : ℕ) : ℝ) ≤ 2 * K := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    exact (Nat.cast_le.mpr hpL).trans this
  have hp0 : (0 : ℝ) < ((p ^ L : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos L
  calc (lev K p : ℝ) * Real.log p ≤ (L : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlev) (Real.log_natCast_nonneg p)
    _ = Real.log ((p ^ L : ℕ) : ℝ) := by rw [Nat.cast_pow, Real.log_pow]
    _ ≤ Real.log (2 * K) := Real.log_le_log hp0 hpL'

/-- Finite form: `∑_{5p < 2K} lev(p) log p ≤ θ(2K/5) + (√(2K) + 1) log(2K)`. -/
theorem sum_lev_log_le (K : ℕ) (hK : 1 ≤ K) :
    ∑ p ∈ (Finset.range (2 * K)).filter (fun p => p.Prime ∧ 5 * p < 2 * K),
      (lev K p : ℝ) * Real.log p ≤
      θ (2 * K / 5) + (Real.sqrt (2 * K) + 1) * Real.log (2 * K) := by
  set F := (Finset.range (2 * K)).filter (fun p => p.Prime ∧ 5 * p < 2 * K) with hF
  have hlog2K : 0 ≤ Real.log (2 * K) :=
    Real.log_nonneg (by have : (1 : ℝ) ≤ K := by exact_mod_cast hK
                        linarith)
  -- pointwise split
  have hpt : ∀ p ∈ F, (lev K p : ℝ) * Real.log p ≤
      Real.log p + (if p * p ≤ 2 * K - 1 then Real.log (2 * K) else 0) := by
    intro p hp
    rw [hF, mem_filter] at hp
    have hp2 := hp.2.1
    split_ifs with hpp
    · have := lev_mul_log_le (K := K) hp2 hK
      have := Real.log_natCast_nonneg p
      linarith
    · have h1 : (lev K p : ℝ) ≤ 1 := by exact_mod_cast lev_le_one hp2 (by omega)
      have := Real.log_natCast_nonneg p
      nlinarith
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  gcongr
  · -- main term
    rw [← primeSum_one_zero, primeSum_eq_sum_filter _ (by positivity) (range (2 * K))]
    · simp only [one_mul]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [hF, mem_filter] at hp
        obtain ⟨hp1, hp2, hp3⟩ := hp
        refine mem_filter.mpr ⟨hp1, hp2, by exact_mod_cast hp2.pos, ?_⟩
        rw [le_div_iff₀ (by norm_num)]
        exact_mod_cast (by omega : p * 5 ≤ 2 * K)
      · intro p _ _
        exact Real.log_natCast_nonneg p
    · intro p _ _ hpd
      rw [mem_range]
      have : (p : ℝ) * 5 ≤ 2 * K := by rwa [le_div_iff₀ (by norm_num)] at hpd
      have : p * 5 ≤ 2 * K := by exact_mod_cast this
      omega
  · -- prime powers
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    gcongr
    have hcard : (F.filter (fun p => p * p ≤ 2 * K - 1)).card ≤ Nat.sqrt (2 * K) + 1 := by
      calc (F.filter (fun p => p * p ≤ 2 * K - 1)).card ≤ (range (Nat.sqrt (2 * K) + 1)).card := by
            apply card_le_card
            intro p hp
            rw [mem_filter] at hp
            rw [mem_range, Nat.lt_succ_iff]
            exact Nat.le_sqrt.mpr (by omega)
        _ = Nat.sqrt (2 * K) + 1 := card_range _
    calc ((F.filter (fun p => p * p ≤ 2 * K - 1)).card : ℝ) ≤ ((Nat.sqrt (2 * K) + 1 : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ ≤ Real.sqrt (2 * K) + 1 := by
          push_cast
          have := Real.nat_sqrt_le_real_sqrt (a := 2 * K)
          push_cast at this
          linarith

theorem eventually_primeSum_lev_le (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h : ℕ in Filter.atTop,
    ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 5 * p < 2 * h),
      2 * (h : ℝ) * (lev h p : ℝ) * Real.log p ≤ (4 / 5 + ε) * (h : ℝ) ^ 2 := by
  -- PNT: `θ(2h/5) ≤ (2/5 + ε/4) h`
  have hT := theta_nat_div_tendsto (c := 5 / 2) (by norm_num)
  have hlt : 1 / (5 / 2 : ℝ) < 2 / 5 + ε / 4 := by norm_num; linarith
  -- `√x log x = o(x)` and `log x = o(x)`, along `x = 2h`
  have h2h : Tendsto (fun h : ℕ => 2 * (h : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hA := h2h.eventually ((Port.isLittleO_sqrt_mul_log).bound (c := ε / 16) (by positivity))
  have hB := h2h.eventually (Real.isLittleO_log_id_atTop.bound (c := ε / 16) (by positivity))
  filter_upwards [hT.eventually (Iio_mem_nhds hlt), hA, hB, eventually_ge_atTop 1]
    with h hθ hA hB h1
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have h2h0 : (0 : ℝ) < 2 * h := by positivity
  simp only [id, Real.norm_eq_abs] at hA hB
  have hlog : 0 ≤ Real.log (2 * h) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ h := by exact_mod_cast h1
    linarith)
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlog), abs_of_pos h2h0] at hA
  rw [abs_of_nonneg hlog, abs_of_pos h2h0] at hB
  have hθ' : θ (2 * h / 5) ≤ (2 / 5 + ε / 4) * h := by
    have e : (2 * h / 5 : ℝ) = h / (5 / 2) := by ring
    rw [e]
    have := (div_lt_iff₀ hh0).mp hθ
    linarith
  have hfin := sum_lev_log_le h h1
  have hS : ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 5 * p < 2 * h),
      (lev h p : ℝ) * Real.log p ≤ (2 / 5 + ε / 2) * h := by
    have : (Real.sqrt (2 * h) + 1) * Real.log (2 * h) =
        Real.sqrt (2 * h) * Real.log (2 * h) + Real.log (2 * h) := by ring
    nlinarith
  have e1 : ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 5 * p < 2 * h),
      2 * (h : ℝ) * (lev h p : ℝ) * Real.log p = 2 * (h : ℝ) * ∑ p ∈ (Finset.range (2 * h)).filter
        (fun p => p.Prime ∧ 5 * p < 2 * h), (lev h p : ℝ) * Real.log p := by
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by ring
  rw [e1]
  calc 2 * (h : ℝ) * ∑ p ∈ (Finset.range (2 * h)).filter (fun p => p.Prime ∧ 5 * p < 2 * h),
        (lev h p : ℝ) * Real.log p
      ≤ 2 * (h : ℝ) * ((2 / 5 + ε / 2) * h) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (4 / 5 + ε) * (h : ℝ) ^ 2 := by ring

end Chi2Irr
