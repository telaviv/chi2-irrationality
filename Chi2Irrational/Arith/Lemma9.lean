/-
# Lemma 9: the general `p`-adic bound on `Δ^F_h`

For every odd prime `p` and every `h`: `‖Δ^F_h‖_p ≤ p^{2h·lev(p)}`, i.e. every rational coefficient of every
coefficient of `Δ^F_h ∈ ℚ[q, E][X]` has `v_p ≥ −2h·lev(p)` (`lev h p = #{e ∈ [1, 2h] : p^e ≤ 2h − 1}`).

Proof (Lagrange basis `f_i = ∏_{m≠i}(X − x_m)`, evaluation matrix diagonal `D′(x_i)`):
* `‖Δ‖ ≤ ‖det G‖ / ∏_i |D′(x_i)|_p` (`det_GramF`, `padicNorm_det_CoefM_sq`);
* **row claim** `entry_bound`: every entry `G_ij = Λ_X(f_i f_j)` has `‖·‖ ≤ |D′(x_i)|_p · p^{2 lev}`; then
  `det_GLeX` with `ρ_i = |D′(x_i)| p^{2lev}`, `κ_j = 1`.
* `μ` in Newton form (`muF_newton`): `μ(R) = Σ_b Δ^b[R′](0) Ω_b`, so `‖μ(R)‖ ≤ sup_{t∈ℕ} |R′(t)|_p`.
* Valuations by levels: `|n|_p ≤ p^{−ν(n)}`, `ν(n) = #{e ∈ L : p^e ∣ n}` (equality for `0 < |n| ≤ 2h − 1`), so
  `|D′(x_i)| = p^{−Σ_e N_e(i)}`; each term of `R′(t)` loses at most `2` per level (`level_L1`, `level_L2`: one
  residue class mod `p^e`, class sizes differ by `≤ 1`); the diagonal uses the ranked divided-difference formula
  `DD_prod_rank` with the ranking `rk` by decreasing `v_p(m − i)`.
-/
import Chi2Irrational.Arith.ClassBound

namespace Chi2Irr

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Levels and valuations -/

/-- The level set `L = {e ∈ [1, 2h] : p^e ≤ 2h − 1}`. -/
def levSet (h p : ℕ) : Finset ℕ := (Icc 1 (2 * h)).filter (fun e => p ^ e ≤ 2 * h - 1)

lemma card_levSet (h p : ℕ) : (levSet h p).card = lev h p := rfl

/-- `ν(n) = #{e ∈ L : p^e ∣ n}`. -/
def nuL (h p : ℕ) (n : ℤ) : ℕ := ((levSet h p).filter (fun e => ((p ^ e : ℕ) : ℤ) ∣ n)).card

lemma nuL_le (h : ℕ) (n : ℤ) : nuL h p n ≤ lev h p := card_filter_le _ _

lemma padicNorm_int_le (h : ℕ) (n : ℤ) : padicNorm p (n : ℚ) ≤ (p : ℚ)⁻¹ ^ nuL h p n := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  by_cases hn : n = 0
  · subst hn; simp only [Int.cast_zero, padicNorm.zero]; positivity
  · have hsub : (levSet h p).filter (fun e => ((p ^ e : ℕ) : ℤ) ∣ n) ⊆ Icc 1 (padicValInt p n) := by
      intro e he
      rw [mem_filter] at he
      obtain ⟨he1, hdvd⟩ := he
      have he1' := (mem_filter.mp he1).1
      rw [mem_Icc] at he1' ⊢
      push_cast at hdvd
      rcases (padicValInt_dvd_iff e n).mp hdvd with h0 | hle
      · exact absurd h0 hn
      · exact ⟨he1'.1, hle⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_int, inv_pow_eq_zpow]
    exact zpow_le_zpow_right₀ hp1 (by unfold nuL; omega)

lemma padicNorm_int_eq {h : ℕ} {n : ℤ} (hn : n ≠ 0) (hn' : n.natAbs ≤ 2 * h - 1) :
    padicNorm p (n : ℚ) = (p : ℚ)⁻¹ ^ nuL h p n := by
  have heq : (levSet h p).filter (fun e => ((p ^ e : ℕ) : ℤ) ∣ n) = Icc 1 (padicValInt p n) := by
    ext e
    simp only [levSet, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, -⟩, hdvd⟩
      push_cast at hdvd
      rcases (padicValInt_dvd_iff e n).mp hdvd with h0 | hle
      · exact absurd h0 hn
      · exact ⟨h1, hle⟩
    · rintro ⟨h1, hle⟩
      have hdvd : (p : ℤ) ^ e ∣ n := (padicValInt_dvd_iff e n).mpr (Or.inr hle)
      have hle2 : p ^ e ≤ 2 * h - 1 := by
        have := Int.natAbs_dvd_natAbs.mpr hdvd
        rw [Int.natAbs_pow, Int.natAbs_natCast] at this
        exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) this).trans hn'
      have hlt : e < p ^ e := Nat.lt_pow_self hp.out.one_lt
      exact ⟨⟨⟨h1, by omega⟩, hle2⟩, by push_cast; exact hdvd⟩
  rw [nuL, heq, Nat.card_Icc, Nat.add_sub_cancel, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
    padicValRat.of_int, inv_pow_eq_zpow]

/-- `Σ_r ν(g r) = Σ_{e∈L} #{r : p^e ∣ g r}`. -/
lemma sum_nuL (h : ℕ) (T : Finset ℕ) (g : ℕ → ℤ) :
    ∑ r ∈ T, nuL h p (g r) = ∑ e ∈ levSet h p, (T.filter (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ g r)).card := by
  simp only [nuL, card_filter]
  exact sum_comm

lemma padicNorm_prod_le_nuL (h : ℕ) (T : Finset ℕ) (f : ℕ → ℚ) (g : ℕ → ℤ)
    (hf : ∀ r ∈ T, padicNorm p (f r) ≤ (p : ℚ)⁻¹ ^ nuL h p (g r)) :
    padicNorm p (∏ r ∈ T, f r) ≤
      (p : ℚ)⁻¹ ^ ∑ e ∈ levSet h p, (T.filter (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ g r)).card := by
  rw [← sum_nuL, padicNorm_prod, ← prod_pow_eq_pow_sum]
  exact prod_le_prod₀ (fun r _ => padicNorm.nonneg _) hf

lemma padicNorm_sub_pole_le (hp2 : p ≠ 2) (h t r : ℕ) :
    padicNorm p ((t : ℚ) - pole r) ≤ (p : ℚ)⁻¹ ^ nuL h p (2 * (t : ℤ) + 2 * r + 1) := by
  have e : (t : ℚ) - pole r = ((2 * (t : ℤ) + 2 * r + 1 : ℤ) : ℚ) / 2 := by unfold pole; push_cast; ring
  rw [e, padicNorm.div, padicNorm_two hp2, div_one]
  exact padicNorm_int_le h _

lemma padicNorm_pole_sub_pole_le (h i r : ℕ) :
    padicNorm p (pole i - pole r) ≤ (p : ℚ)⁻¹ ^ nuL h p ((r : ℤ) - i) := by
  rw [pole_sub_pole]
  have := padicNorm_int_le (p := p) h ((r : ℤ) - i)
  push_cast at this
  exact this

/-- `N_e(i) = #{m < h, m ≠ i : d ∣ m − i}`. -/
def Aset (d h i : ℕ) : Finset ℕ := ((range h).erase i).filter (fun m : ℕ => (d : ℤ) ∣ (m : ℤ) - i)

/-- `V_i = Σ_{e∈L} N_e(i) = v_p(D′(x_i))`. -/
def Vexp (h p i : ℕ) : ℕ := ∑ e ∈ levSet h p, (Aset (p ^ e) h i).card

lemma padicNorm_dPrime_eq {h i : ℕ} (hi : i < h) : padicNorm p (dPrime h i) = (p : ℚ)⁻¹ ^ Vexp h p i := by
  unfold dPrime Vexp Aset
  rw [← sum_nuL h _ (fun m => (m : ℤ) - i), padicNorm_prod, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl (fun m hm => ?_)
  obtain ⟨hmi, hmh⟩ := mem_erase.mp hm
  rw [mem_range] at hmh
  rw [pole_sub_pole]
  have := padicNorm_int_eq (p := p) (h := h) (n := (m : ℤ) - i) (by omega) (by omega)
  push_cast at this
  exact this

lemma inv_pow_le_dPrime {h i : ℕ} (hi : i < h) {c : ℕ} (hc : Vexp h p i ≤ c + 2 * lev h p) :
    (p : ℚ)⁻¹ ^ c ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℚ) < p := by linarith
  rw [padicNorm_dPrime_eq hi, inv_pow_eq_zpow, inv_pow_eq_zpow, ← zpow_natCast (p : ℚ) (2 * lev h p),
    ← zpow_add₀ hp0.ne']
  exact zpow_le_zpow_right₀ hp1 (by push_cast; omega)

lemma pow_mod_two (hp2 : p ≠ 2) (e : ℕ) : p ^ e % 2 = 1 :=
  Nat.odd_iff.mp ((hp.out.odd_of_ne_two hp2).pow)

/-! ### One level: residue classes modulo an odd `d` -/

section Level

lemma dvd_of_dvd_two_mul {d : ℕ} (hd : d % 2 = 1) {x : ℤ} (hx : (d : ℤ) ∣ 2 * x) : (d : ℤ) ∣ x := by
  have e : (d : ℤ) * x - ((d / 2 : ℕ) : ℤ) * (2 * x) = x := by
    have : (d : ℤ) = 2 * ((d / 2 : ℕ) : ℤ) + 1 := by omega
    rw [this]; ring
  rw [← e]
  exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right hx _)

lemma card_filter_mod' {d : ℕ} (hd : 0 < d) {c : ℕ} (hc : c < d) (X : ℕ) :
    ((range X).filter (fun l => l % d = c)).card = (X + d - 1 - c) / d := by
  have himg : (range X).filter (fun l => l % d = c) = (range ((X + d - 1 - c) / d)).image (fun j => c + j * d) := by
    ext l
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hl, hlc⟩
      refine ⟨l / d, ?_, ?_⟩
      · rw [Nat.lt_div_iff_mul_lt hd]
        have := Nat.mod_add_div l d
        rw [hlc] at this
        have e : (l / d + 1) * d = l / d * d + d := by ring
        have e2 : d * (l / d) = l / d * d := by ring
        omega
      · have := Nat.mod_add_div l d
        rw [hlc] at this
        linarith [mul_comm d (l / d)]
    · rintro ⟨j, hj, rfl⟩
      rw [Nat.lt_div_iff_mul_lt hd] at hj
      refine ⟨?_, ?_⟩
      · have e : (j + 1) * d = j * d + d := by ring
        omega
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  rw [himg, card_image_of_injective _ (fun a b e => Nat.eq_of_mul_eq_mul_right hd (by omega)), card_range]

lemma card_mod_le {d : ℕ} (hd : 0 < d) {a b : ℕ} (ha : a < d) (hb : b < d) (X : ℕ) :
    ((range X).filter (fun l => l % d = a)).card ≤ ((range X).filter (fun l => l % d = b)).card + 1 := by
  rw [card_filter_mod' hd ha, card_filter_mod' hd hb]
  calc (X + d - 1 - a) / d ≤ (X + d - 1 - b + d) / d := Nat.div_le_div_right (by omega)
    _ = (X + d - 1 - b) / d + 1 := Nat.add_div_right _ hd

/-- The class of `i` in `[0, h)` modulo `d`. -/
def clsF (d h i : ℕ) : Finset ℕ := (range h).filter (fun m : ℕ => (d : ℤ) ∣ (m : ℤ) - i)

/-- The atoms `m < h` with `d ∣ 2t + 2m + 1`. -/
def ctF (d h t : ℕ) : Finset ℕ := (range h).filter (fun m : ℕ => (d : ℤ) ∣ 2 * (t : ℤ) + 2 * m + 1)

lemma clsF_eq (d h i : ℕ) : clsF d h i = (range h).filter (fun m => m % d = i % d) := by
  unfold clsF
  refine filter_congr (fun m _ => ?_)
  rw [← Nat.modEq_iff_dvd]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

lemma ctF_eq {d : ℕ} (hd : d % 2 = 1) (h t : ℕ) :
    ctF d h t = (range h).filter (fun m => m % d = ((d / 2) * (2 * t + 1)) % d) := by
  unfold ctF
  refine filter_congr (fun m _ => ?_)
  have hd' : (d : ℤ) = 2 * ((d / 2 : ℕ) : ℤ) + 1 := by omega
  have e : 2 * (t : ℤ) + 2 * m + 1 = 2 * ((m : ℤ) - ((d / 2 * (2 * t + 1) : ℕ) : ℤ)) + (d : ℤ) * (2 * t + 1) := by
    rw [hd']; push_cast; ring
  rw [e]
  constructor
  · intro h1
    have h2 : (d : ℤ) ∣ 2 * ((m : ℤ) - ((d / 2 * (2 * t + 1) : ℕ) : ℤ)) :=
      (dvd_add_left (dvd_mul_right _ _)).mp h1
    have h3 := dvd_of_dvd_two_mul hd h2
    rw [← Nat.modEq_iff_dvd] at h3
    exact h3.symm
  · intro h1
    have h3 : (d : ℤ) ∣ (m : ℤ) - ((d / 2 * (2 * t + 1) : ℕ) : ℤ) := (Nat.modEq_iff_dvd).mp h1.symm
    exact dvd_add (dvd_mul_of_dvd_right h3 _) (dvd_mul_right _ _)

lemma ctF_eq_clsF {d : ℕ} (hd : d % 2 = 1) {h t i : ℕ} (hti : (d : ℤ) ∣ 2 * (t : ℤ) + 2 * i + 1) :
    ctF d h t = clsF d h i := by
  unfold ctF clsF
  refine filter_congr (fun m _ => ?_)
  have e : 2 * (t : ℤ) + 2 * m + 1 = (2 * (t : ℤ) + 2 * i + 1) + 2 * ((m : ℤ) - i) := by ring
  rw [e]
  constructor
  · intro h1; exact dvd_of_dvd_two_mul hd ((dvd_add_right hti).mp h1)
  · intro h1; exact dvd_add hti (dvd_mul_of_dvd_right h1 _)

lemma not_dvd_of_mem_ctF {d : ℕ} {t i m : ℕ} (hti : ¬ (d : ℤ) ∣ 2 * (t : ℤ) + 2 * i + 1)
    (hm : (d : ℤ) ∣ 2 * (t : ℤ) + 2 * m + 1) : ¬ (d : ℤ) ∣ (m : ℤ) - i := by
  intro h1
  apply hti
  have e : 2 * (t : ℤ) + 2 * i + 1 = (2 * (t : ℤ) + 2 * m + 1) - 2 * ((m : ℤ) - i) := by ring
  rw [e]
  exact dvd_sub hm (dvd_mul_of_dvd_right h1 _)

lemma card_clsF_le {d : ℕ} (hd : d % 2 = 1) (h t i : ℕ) : (clsF d h i).card ≤ (ctF d h t).card + 1 := by
  have hd0 : 0 < d := by omega
  rw [clsF_eq, ctF_eq hd]
  exact card_mod_le hd0 (Nat.mod_lt _ hd0) (Nat.mod_lt _ hd0) h

lemma card_Aset {d h i : ℕ} (hi : i < h) : (Aset d h i).card + 1 = (clsF d h i).card := by
  unfold Aset clsF
  rw [filter_erase, card_erase_of_mem (mem_filter.mpr ⟨mem_range.mpr hi, by simp⟩)]
  have : 0 < ((range h).filter (fun m : ℕ => (d : ℤ) ∣ (m : ℤ) - i)).card :=
    card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, by simp⟩⟩
  omega

/-- **Level count, products over `[0,h) ∖ {i, j, s}`.** -/
lemma level_L1 {d : ℕ} (hd : d % 2 = 1) {h i : ℕ} (hi : i < h) (j s t : ℕ) (T : Finset ℕ)
    (hT : ∀ r < h, r ≠ i → r ≠ j → r ≠ s → r ∈ T) :
    (Aset d h i).card ≤ (T.filter (fun r : ℕ => (d : ℤ) ∣ 2 * (t : ℤ) + 2 * r + 1)).card + 2 := by
  have hA := card_Aset (d := d) hi
  have hsub : (((ctF d h t).erase i).erase j).erase s ⊆ T.filter (fun r : ℕ => (d : ℤ) ∣ 2 * (t : ℤ) + 2 * r + 1) := by
    intro r hr
    simp only [mem_erase, ctF, mem_filter, mem_range] at hr
    exact mem_filter.mpr ⟨hT r hr.2.2.2.1 hr.2.2.1 hr.2.1 hr.1, hr.2.2.2.2⟩
  have h1 := card_le_card hsub
  have e1 := pred_card_le_card_erase (s := ctF d h t) (a := i)
  have e2 := pred_card_le_card_erase (s := (ctF d h t).erase i) (a := j)
  have e3 := pred_card_le_card_erase (s := ((ctF d h t).erase i).erase j) (a := s)
  by_cases hdi : (d : ℤ) ∣ 2 * (t : ℤ) + 2 * i + 1
  · rw [ctF_eq_clsF hd hdi] at e1 h1 e2 e3
    omega
  · have hiC : i ∉ ctF d h t := fun hm => hdi (mem_filter.mp hm).2
    have e0 : ((ctF d h t).erase i).card = (ctF d h t).card := by rw [erase_eq_of_notMem hiC]
    have hK := card_clsF_le hd h t i
    omega

/-- **Level count, ranked divided-difference terms.** -/
lemma level_L2 {d : ℕ} (hd : d % 2 = 1) {h i : ℕ} (hi : i < h) (t l s : ℕ) (ρ : ℕ → ℕ)
    (hl : l ∈ (range h).erase i) (hinj : Set.InjOn ρ ((range h).erase i : Finset ℕ))
    (hρ : ∀ r ∈ (range h).erase i, ∀ r' ∈ (range h).erase i,
      (d : ℤ) ∣ (r : ℤ) - i → ¬ (d : ℤ) ∣ (r' : ℤ) - i → ρ r < ρ r') :
    (Aset d h i).card ≤
      ((((range h).erase i).filter (fun r => ρ r < ρ l)).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) - i)).card +
      (((((range h).erase i).filter (fun r => ρ l < ρ r)).erase s).filter
        (fun r : ℕ => (d : ℤ) ∣ 2 * (t : ℤ) + 2 * r + 1)).card + 2 := by
  by_cases hlA : (d : ℤ) ∣ (l : ℤ) - i
  · have hsplit : Aset d h i ⊆ insert l ((Aset d h i).filter (fun r => ρ r < ρ l) ∪
        (Aset d h i).filter (fun r => ρ l < ρ r)) := by
      intro r hr
      by_cases hrl : r = l
      · rw [hrl]; exact mem_insert_self _ _
      · have hne : ρ r ≠ ρ l := fun e => hrl (hinj (mem_coe.mpr (mem_filter.mp hr).1) (mem_coe.mpr hl) e)
        rcases lt_or_gt_of_ne hne with h1 | h1
        · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hr, h1⟩))
        · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hr, h1⟩))
    have hcA := (card_le_card hsplit).trans ((card_insert_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) 1))
    have hb : (Aset d h i).filter (fun r => ρ r < ρ l) ⊆
        (((range h).erase i).filter (fun r => ρ r < ρ l)).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) - i) := by
      intro r hr
      simp only [Aset, mem_filter] at hr ⊢
      exact ⟨⟨hr.1.1, hr.2⟩, hr.1.2⟩
    have hb' := card_le_card hb
    by_cases hti : (d : ℤ) ∣ 2 * (t : ℤ) + 2 * i + 1
    · have ha : ((Aset d h i).filter (fun r => ρ l < ρ r)).erase s ⊆
          ((((range h).erase i).filter (fun r => ρ l < ρ r)).erase s).filter
            (fun r : ℕ => (d : ℤ) ∣ 2 * (t : ℤ) + 2 * r + 1) := by
        intro r hr
        simp only [Aset, mem_erase, mem_filter] at hr
        refine mem_filter.mpr ⟨mem_erase.mpr ⟨hr.1, mem_filter.mpr ⟨mem_erase.mpr hr.2.1.1, hr.2.2⟩⟩, ?_⟩
        have e : 2 * (t : ℤ) + 2 * r + 1 = (2 * (t : ℤ) + 2 * i + 1) + 2 * ((r : ℤ) - i) := by ring
        rw [e]
        exact dvd_add hti (dvd_mul_of_dvd_right hr.2.1.2 _)
      have ha' := card_le_card ha
      have := pred_card_le_card_erase (s := (Aset d h i).filter (fun r => ρ l < ρ r)) (a := s)
      omega
    · have hC : (ctF d h t).erase s ⊆ ((((range h).erase i).filter (fun r => ρ l < ρ r)).erase s).filter
            (fun r : ℕ => (d : ℤ) ∣ 2 * (t : ℤ) + 2 * r + 1) := by
        intro r hr
        obtain ⟨hrs, hrC⟩ := mem_erase.mp hr
        have hrC' := mem_filter.mp hrC
        have hri : r ≠ i := fun e => hti (e ▸ hrC'.2)
        have hrM : r ∈ (range h).erase i := mem_erase.mpr ⟨hri, hrC'.1⟩
        have hrA := not_dvd_of_mem_ctF hti hrC'.2
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hrs, mem_filter.mpr ⟨hrM, hρ l hl r hrM hlA hrA⟩⟩, hrC'.2⟩
      have h1 := card_le_card hC
      have h2 := pred_card_le_card_erase (s := ctF d h t) (a := s)
      have hK := card_clsF_le hd h t i
      have hA := card_Aset (d := d) hi
      omega
  · have hsub : Aset d h i ⊆
        (((range h).erase i).filter (fun r => ρ r < ρ l)).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) - i) := by
      intro r hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hr'.1, hρ r hr'.1 l hl hr'.2 hlA⟩, hr'.2⟩
    have := card_le_card hsub
    omega

end Level

/-! ### The ranking by decreasing valuation -/

/-- `rk(m) = m + h (h − v_p(m − i))`: atoms with larger `v_p(m − i)` come first. -/
noncomputable def rk (p h i m : ℕ) : ℕ := m + h * (h - padicValInt p ((m : ℤ) - i))

lemma rk_injOn (h i : ℕ) : Set.InjOn (rk p h i) ((range h).erase i : Finset ℕ) := by
  intro r hr r' hr' e
  have hr1 : r < h := mem_range.mp (mem_of_mem_erase (mem_coe.mp hr))
  have hr1' : r' < h := mem_range.mp (mem_of_mem_erase (mem_coe.mp hr'))
  have := congrArg (· % h) e
  simp only [rk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr1'] at this
  exact this

lemma rk_lt {h i e : ℕ} (hi : i < h) {r r' : ℕ} (hr : r ∈ (range h).erase i) (hr' : r' ∈ (range h).erase i)
    (h1 : ((p ^ e : ℕ) : ℤ) ∣ (r : ℤ) - i) (h2 : ¬ ((p ^ e : ℕ) : ℤ) ∣ (r' : ℤ) - i) :
    rk p h i r < rk p h i r' := by
  obtain ⟨hri, hrh⟩ := mem_erase.mp hr
  obtain ⟨hri', hrh'⟩ := mem_erase.mp hr'
  rw [mem_range] at hrh hrh'
  push_cast at h1 h2
  have hne : (r : ℤ) - i ≠ 0 := by omega
  have hv1 : e ≤ padicValInt p ((r : ℤ) - i) := ((padicValInt_dvd_iff e _).mp h1).resolve_left hne
  have hv2 : padicValInt p ((r' : ℤ) - i) < e := by
    by_contra hc
    push_neg at hc
    exact h2 ((padicValInt_dvd_iff e _).mpr (Or.inr hc))
  have hv3 : padicValInt p ((r : ℤ) - i) < h := by
    have hd := padicValInt_dvd (p := p) ((r : ℤ) - i)
    have hd' := Int.natAbs_dvd_natAbs.mpr hd
    rw [Int.natAbs_pow, Int.natAbs_natCast] at hd'
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hd'
    have h4 := Nat.lt_pow_self (n := padicValInt p ((r : ℤ) - i)) hp.out.one_lt
    have h5 : ((r : ℤ) - i).natAbs < h := by omega
    omega
  unfold rk
  generalize padicValInt p ((r : ℤ) - i) = v at *
  generalize padicValInt p ((r' : ℤ) - i) = v' at *
  have hab : h - v + 1 ≤ h - v' := by omega
  have := Nat.mul_le_mul_left h hab
  rw [mul_add, mul_one] at this
  generalize h * (h - v) = A at *
  generalize h * (h - v') = B at *
  omega

lemma Bnn (x : ℚ) (n : ℕ) : 0 ≤ padicNorm p x * (p : ℚ) ^ n :=
  mul_nonneg (padicNorm.nonneg _) (pow_nonneg (Nat.cast_nonneg p) n)

/-! ### Ranked divided differences -/

lemma DD_X_sub_C (x a : ℚ) : DD x (X - C a) = 1 := by
  apply DD_eq_of_mul
  simp only [eval_sub, eval_X, eval_C, mul_one, map_sub]
  ring

lemma DD_X (x : ℚ) : DD x X = 1 := by
  apply DD_eq_of_mul
  simp

lemma DD_one (x : ℚ) : DD x 1 = 0 := by
  apply DD_eq_of_mul
  simp

/-- `DD_x ∏_{m∈M}(X − a_m) = Σ_ℓ ∏_{ρr<ρℓ}(x − a_r) · ∏_{ρℓ<ρr}(X − a_r)` for a ranking `ρ` injective on `M`. -/
lemma DD_prod_rank (x : ℚ) (a : ℕ → ℚ) (ρ : ℕ → ℕ) (M : Finset ℕ) (hρ : Set.InjOn ρ (M : Set ℕ)) :
    DD x (∏ m ∈ M, (X - C (a m))) = ∑ l ∈ M, C (∏ r ∈ M.filter (fun r => ρ r < ρ l), (x - a r)) *
      ∏ r ∈ M.filter (fun r => ρ l < ρ r), (X - C (a r)) := by
  revert hρ
  refine Finset.induction_on_min_value (motive := fun M => Set.InjOn ρ (M : Set ℕ) →
    DD x (∏ m ∈ M, (X - C (a m))) = ∑ l ∈ M, C (∏ r ∈ M.filter (fun r => ρ r < ρ l), (x - a r)) *
      ∏ r ∈ M.filter (fun r => ρ l < ρ r), (X - C (a r))) ρ M ?_ ?_
  · intro _
    simp [DD_one]
  · intro b s hb hmin ih hinj
    have hlt : ∀ y ∈ s, ρ b < ρ y := fun y hy => lt_of_le_of_ne (hmin y hy) (fun e => hb (by
      have := hinj (mem_coe.mpr (mem_insert_self b s)) (mem_coe.mpr (mem_insert_of_mem hy)) e
      rw [this]; exact hy))
    have ih' := ih (hinj.mono (coe_subset.mpr (subset_insert b s)))
    rw [prod_insert hb, DD_mul, DD_X_sub_C, one_mul, ih', sum_insert hb]
    have e1 : (insert b s).filter (fun r => ρ r < ρ b) = ∅ := by
      rw [filter_insert, ite_eq_right (lt_irrefl _), filter_eq_empty_iff]
      intro y hy
      exact not_lt.mpr (hmin y hy)
    have e2 : (insert b s).filter (fun r => ρ b < ρ r) = s := by
      rw [filter_insert, ite_eq_right (lt_irrefl _), filter_true_of_mem hlt]
    rw [e1, e2, prod_empty, map_one, one_mul, mul_sum]
    congr 1
    refine sum_congr rfl (fun l hl => ?_)
    rw [filter_insert, ite_eq_left (hlt l hl), filter_insert, ite_eq_right (not_lt.mpr (hmin l hl)),
      prod_insert (fun hm => hb (mem_filter.mp hm).1)]
    simp only [eval_sub, eval_X, eval_C, map_mul]
    ring

lemma Qpoly_eq' (h i : ℕ) : Qpoly h i = fpoly h i + C (pole i) * DD (pole i) (fpoly h i) := by
  rw [Qpoly_eq_DD, gpoly, DD_mul, DD_X, one_mul, eval_X]

/-! ### `μ` in Newton form -/

/-- `Δ^b[R′](0) = Σ_{k≤b} (−1)^{b−k} C(b,k) R′(k)`. -/
noncomputable def ndF (R : ℚ[X]) (b : ℕ) : ℚ :=
  ∑ k ∈ range (b + 1), (((-1 : ℤ) ^ (b - k) * (b.choose k : ℤ) : ℤ) : ℚ) * (derivative R).eval (k : ℚ)

lemma muF_newton (R : ℚ[X]) {N : ℕ} (hN : R.natDegree < N) :
    muF R = ∑ b ∈ range N, MvPolynomial.C (ndF R b) * OmegaF b := by
  rw [muF_eq_sum, sum_over_range' (f := fun d c => c • muMonoF d) _ (fun n => zero_smul ℚ _) N hN]
  have hext : ∀ d ∈ range N, R.coeff d • muMonoF d =
      ∑ b ∈ range N, MvPolynomial.C (R.coeff d * ((d : ℚ) * (dCoef (d - 1) b : ℚ))) * OmegaF b := by
    intro d hd
    unfold muMonoF
    rw [Finset.smul_sum]
    rw [sum_subset (range_subset_range.mpr (le_of_lt (mem_range.mp hd)))]
    · refine sum_congr rfl (fun b _ => ?_)
      rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    · intro b _ hbd
      rw [mem_range, not_lt] at hbd
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · subst h0; simp
      · rw [dCoef_eq_zero (by omega)]; simp
  rw [sum_congr rfl hext, sum_comm]
  refine sum_congr rfl (fun b _ => ?_)
  rw [← sum_mul, ← map_sum]
  congr 2
  have hder : ∀ k : ℕ, (derivative R).eval (k : ℚ) = ∑ d ∈ range N, R.coeff d * d * (k : ℚ) ^ (d - 1) :=
    fun k => by rw [derivative_eval, sum_over_range' _ (fun n => by simp) N hN]
  simp only [ndF, dCoef, hder]
  push_cast
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun d _ => sum_congr rfl (fun k _ => by ring))

/-- `‖μ(R)‖_p ≤ sup_{t∈ℕ} |R′(t)|_p`. -/
lemma GLe_muF_of_deriv {R : ℚ[X]} {B : ℚ} (hB : 0 ≤ B)
    (hR : ∀ t : ℕ, padicNorm p ((derivative R).eval (t : ℚ)) ≤ B) : GLe p B (muF R) := by
  rw [muF_newton R (Nat.lt_succ_self _)]
  refine GLe_sum _ hB _ (fun b _ => ?_)
  have hc : padicNorm p (ndF R b) ≤ B := by
    unfold ndF
    refine padicNorm.sum_le' (fun k _ => ?_) hB
    rw [padicNorm.mul]
    calc _ ≤ 1 * B := mul_le_mul (padicNorm.of_int _) (hR k) (padicNorm.nonneg _) zero_le_one
      _ = B := one_mul B
  simpa using GLe_mul hB zero_le_one (GLe_mono hc (GLe_C _)) (GLe_OmegaF b)

/-! ### Derivative bounds -/

section Deriv

variable (hp2 : p ≠ 2)
include hp2

/-- A product over `T ⊇ [0,h) ∖ {i, j, s}` at `t ∈ ℕ`. -/
lemma prod_T_le {h i : ℕ} (hi : i < h) (j s t : ℕ) (T : Finset ℕ)
    (hT : ∀ r < h, r ≠ i → r ≠ j → r ≠ s → r ∈ T) :
    padicNorm p (∏ r ∈ T, ((t : ℚ) - pole r)) ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := by
  refine (padicNorm_prod_le_nuL h T _ (fun r => 2 * (t : ℤ) + 2 * r + 1)
    (fun r _ => padicNorm_sub_pole_le hp2 h t r)).trans ?_
  refine inv_pow_le_dPrime hi ?_
  unfold Vexp
  calc ∑ e ∈ levSet h p, (Aset (p ^ e) h i).card
      ≤ ∑ e ∈ levSet h p, ((T.filter (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ 2 * (t : ℤ) + 2 * r + 1)).card + 2) :=
        sum_le_sum (fun e _ => level_L1 (pow_mod_two hp2 e) hi j s t T hT)
    _ = _ := by rw [sum_add_distrib, sum_const, card_levSet, smul_eq_mul]; ring

/-- A ranked divided-difference term. -/
lemma prod_DD_le {h i : ℕ} (hi : i < h) (t l s : ℕ) (hl : l ∈ (range h).erase i) :
    padicNorm p ((∏ r ∈ ((range h).erase i).filter (fun r => rk p h i r < rk p h i l), (pole i - pole r)) *
      ∏ r ∈ (((range h).erase i).filter (fun r => rk p h i l < rk p h i r)).erase s, ((t : ℚ) - pole r)) ≤
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := by
  rw [padicNorm.mul]
  have h1 := padicNorm_prod_le_nuL h (((range h).erase i).filter (fun r => rk p h i r < rk p h i l)) _
    (fun r => (r : ℤ) - i) (fun r _ => padicNorm_pole_sub_pole_le (p := p) h i r)
  have h2 := padicNorm_prod_le_nuL h ((((range h).erase i).filter (fun r => rk p h i l < rk p h i r)).erase s) _
    (fun r => 2 * (t : ℤ) + 2 * r + 1) (fun r _ => padicNorm_sub_pole_le hp2 h t r)
  refine (mul_le_mul h1 h2 (padicNorm.nonneg _) (by positivity)).trans ?_
  rw [← pow_add, ← sum_add_distrib]
  refine inv_pow_le_dPrime hi ?_
  unfold Vexp
  calc ∑ e ∈ levSet h p, (Aset (p ^ e) h i).card ≤ ∑ e ∈ levSet h p,
      (((((range h).erase i).filter (fun r => rk p h i r < rk p h i l)).filter
          (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ (r : ℤ) - i)).card +
        (((((range h).erase i).filter (fun r => rk p h i l < rk p h i r)).erase s).filter
          (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ 2 * (t : ℤ) + 2 * r + 1)).card + 2) :=
        sum_le_sum (fun e _ => level_L2 (pow_mod_two hp2 e) hi t l s (rk p h i) hl (rk_injOn h i)
          (fun r hr r' hr' h1 h2 => rk_lt hi hr hr' h1 h2))
    _ = _ := by rw [sum_add_distrib, sum_const, card_levSet, smul_eq_mul]; ring

lemma deriv_Fpoly_le {h i : ℕ} (hi : i < h) (j t : ℕ) :
    padicNorm p ((derivative (Fpoly h i j)).eval (t : ℚ)) ≤
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := by
  have hB : 0 ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := Bnn _ _
  unfold Fpoly
  rw [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X, eval_derivative_prod,
    eval_prod_X_sub_C]
  refine padicNorm.nonarchimedean.trans (max_le ?_ ?_)
  · exact prod_T_le hp2 hi j j t _ (fun r hr h1 h2 _ => by simp [mem_erase, *])
  · rw [padicNorm.mul]
    refine (mul_le_of_le_one_left (padicNorm.nonneg _) (padicNorm.of_nat t)).trans ?_
    exact padicNorm.sum_le' (fun s _ => prod_T_le hp2 hi j s t _
      (fun r hr h1 h2 h3 => by simp [mem_erase, *])) hB

lemma deriv_Qpoly_le {h i : ℕ} (hi : i < h) (t : ℕ) :
    padicNorm p ((derivative (Qpoly h i)).eval (t : ℚ)) ≤
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := by
  have hB : 0 ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := Bnn _ _
  rw [Qpoly_eq', derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C]
  refine padicNorm.nonarchimedean.trans (max_le ?_ ?_)
  · unfold fpoly
    rw [eval_derivative_prod]
    exact padicNorm.sum_le' (fun s _ => prod_T_le hp2 hi i s t _
      (fun r hr h1 _ h3 => by simp [mem_erase, *])) hB
  · rw [padicNorm.mul]
    refine (mul_le_of_le_one_left (padicNorm.nonneg _) (mem_Zl.mp (pole_mem_Zl hp2 i))).trans ?_
    unfold fpoly
    rw [DD_prod_rank (pole i) pole (rk p h i) _ (rk_injOn h i), derivative_sum, eval_finsetSum]
    refine padicNorm.sum_le' (fun l hl => ?_) hB
    rw [derivative_C_mul, eval_mul, eval_C, eval_derivative_prod, mul_sum]
    exact padicNorm.sum_le' (fun s _ => prod_DD_le hp2 hi t l s hl) hB

end Deriv

/-! ### The entries -/

lemma sum_pole_fpoly {h i : ℕ} (hi : i < h) (j : ℕ) (Y : ℕ → FR) :
    ∑ k ∈ range h, MvPolynomial.C ((fpoly h i * fpoly h j).eval (pole k) * omega h k) * Y k =
      MvPolynomial.C ((fpoly h i * fpoly h j).eval (pole i) * omega h i) * Y i := by
  rw [sum_eq_single i]
  · intro k hk hki
    rw [eval_mul, eval_fpoly h i k (mem_range.mp hk), ite_eq_right hki]
    simp
  · intro h'; exact absurd (mem_range.mpr hi) h'

lemma padicNorm_pole_coef (hp2 : p ≠ 2) {h i : ℕ} (hi : i < h) (j : ℕ) :
    padicNorm p ((fpoly h i * fpoly h j).eval (pole i) * omega h i) ≤ padicNorm p (dPrime h i) := by
  rw [eval_mul, eval_fpoly h i i hi, ite_eq_left rfl, eval_fpoly h j i hi]
  split_ifs with hij
  · subst hij
    unfold omega
    have hD := dPrime_ne_zero h i
    have e : dPrime h i * dPrime h i * (pole i / dPrime h i) = pole i * dPrime h i := by field_simp
    rw [e, padicNorm.mul]
    calc _ ≤ 1 * padicNorm p (dPrime h i) :=
          mul_le_mul_of_nonneg_right (mem_Zl.mp (pole_mem_Zl hp2 i)) (padicNorm.nonneg _)
      _ = _ := one_mul _
  · rw [mul_zero, zero_mul, padicNorm.zero]
    exact padicNorm.nonneg _

lemma GLe_four' : GLe p 1 (4 : FR) := by
  have : (4 : FR) = MvPolynomial.C 4 := (map_ofNat MvPolynomial.C 4).symm
  rw [this]
  exact GLe_mono (by exact_mod_cast padicNorm.of_nat 4) (GLe_C _)

lemma GLe_SpartF_lev {h k : ℕ} (hk : k < h) : GLe p ((p : ℚ) ^ (2 * lev h p)) (SpartF k) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hB : (0 : ℚ) ≤ (p : ℚ) ^ (2 * lev h p) := by positivity
  refine GLe_sum _ hB _ (fun j hj => ?_)
  have hj := mem_range.mp hj
  have hjn : padicNorm p (1 / (2 * (j : ℚ) + 1) ^ 2) ≤ (p : ℚ) ^ (2 * lev h p) := by
    have e : (2 * (j : ℚ) + 1) = ((2 * (j : ℤ) + 1 : ℤ) : ℚ) := by push_cast; ring
    rw [e, padicNorm.div, padicNorm.one, padicNorm_pow (ℓ := p),
      padicNorm_int_eq (h := h) (by omega) (by omega), ← pow_mul, one_div, inv_pow, inv_inv]
    exact pow_le_pow_right₀ hp1 (by have := nuL_le (p := p) h (2 * (j : ℤ) + 1); omega)
  have hC := GLe_mono hjn (GLe_C (p := p) (1 / (2 * (j : ℚ) + 1) ^ 2))
  have hq : GLe p 1 (qF ^ (2 * (k - j))) := by simpa using GLe_pow (p := p) zero_le_one GLe_qF (2 * (k - j))
  simpa using GLe_mul zero_le_one hB hq hC

/-- **Row claim.** `‖Λ_X(f_i f_j)‖_p ≤ |D′(x_i)|_p · p^{2 lev}`. -/
lemma entry_bound (hp2 : p ≠ 2) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    GLeX p (padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p)) (LamF h (fpoly h i * fpoly h j)) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hB : 0 ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p) := Bnn _ _
  have hBp : (1 : ℚ) ≤ (p : ℚ) ^ (2 * lev h p) := one_le_pow₀ hp1
  have hc := padicNorm_pole_coef hp2 hi j
  have hA : GLe p (padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p)) (AfunF h (fpoly h i * fpoly h j)) := by
    unfold AfunF
    rw [sum_pole_fpoly hi j SpartF]
    refine GLe_add ?_ ?_
    · refine GLe_muF_of_deriv hB (fun t => ?_)
      by_cases hij : i = j
      · subst hij
        rw [fpoly_sq_X_divByMonic hi]
        exact deriv_Qpoly_le hp2 hi t
      · rw [fpoly_mul_fpoly_X hi hj hij,
          mul_divByMonic_cancel_left _ (monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))]
        exact deriv_Fpoly_le hp2 hi j t
    · have h1 := GLe_mul (padicNorm.nonneg _) (by positivity) (GLe_C (p := p)
        ((fpoly h i * fpoly h j).eval (pole i) * omega h i)) (GLe_SpartF_lev (h := h) hi)
      have h2 := GLe_mul zero_le_one (Bnn _ _) GLe_four' h1
      refine GLe_mono ?_ h2
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hBB : GLe p (padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p)) (BfunF h (fpoly h i * fpoly h j)) := by
    unfold BfunF
    rw [sum_pole_fpoly hi j (fun k => qF ^ (2 * k + 1))]
    have hq : GLe p 1 (qF ^ (2 * i + 1)) := by simpa using GLe_pow (p := p) zero_le_one GLe_qF (2 * i + 1)
    have h1 := GLe_mul (padicNorm.nonneg _) zero_le_one (GLe_C (p := p)
      ((fpoly h i * fpoly h j).eval (pole i) * omega h i)) hq
    have h2 := GLe_mul zero_le_one (mul_nonneg (padicNorm.nonneg _) zero_le_one) (GLe_neg GLe_four') h1
    refine GLe_mono ?_ h2
    rw [one_mul, mul_one]
    exact hc.trans (le_mul_of_one_le_right (padicNorm.nonneg _) hBp)
  unfold LamF
  exact GLeX_add (GLeX_C hB hA) (GLeX_X_mul hB (GLeX_C hB hBB))

/-! ### Assembly -/

/-- **Lemma 9.** For every odd prime `p`: `‖Δ^F_h‖_p ≤ p^{2h·lev(p)}`. -/
theorem lemma9_DeltaF {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h : ℕ) :
    GLeX p ((p : ℚ) ^ (2 * h * lev h p)) (DeltaF h) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℚ) < p := by linarith
  set e : Fin h → ℚ[X] := fun i => fpoly h i
  have hdeg : ∀ i, (e i).natDegree < h := fun i => natDegree_fpoly_lt i.isLt
  have hG := det_GLeX (GramF h e) (fun i => padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * lev h p)) (fun _ => 1)
    (fun _ => Bnn _ _) (fun _ => zero_le_one) (fun i j => by
      rw [mul_one]; exact entry_bound hp2 i.isLt j.isLt)
  have hC2 := padicNorm_det_CoefM_sq (p := p) e hdeg
    (fun m k hmk => by
      show (fpoly h m).eval (pole k) = 0
      rw [eval_fpoly h m k k.isLt, ite_eq_right (fun hk => absurd hmk (by
        have : k = m := Fin.ext hk
        rw [this]; exact lt_irrefl _))])
    (fun m => by show (fpoly h m).eval (pole m) = _; rw [eval_fpoly h m m m.isLt, ite_eq_left rfl])
  have hpos : (0 : ℚ) < ∏ m : Fin h, padicNorm p (dPrime h m) :=
    prod_pos (fun m _ => lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero (dPrime_ne_zero h m)).symm)
  have hdetC : (CoefM e).det ≠ 0 := by
    intro h0
    rw [h0, padicNorm.zero] at hC2
    simp at hC2; linarith
  have hEq : DeltaF h = algebraMap ℚ FR[X] (((CoefM e).det)⁻¹ ^ 2) * (GramF h e).det := by
    rw [det_GramF e hdeg, ← mul_assoc, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hdetC),
      map_one, one_mul]
  rw [hEq]
  refine GLeX_mono (le_of_eq ?_) (GLeX_algebraMap_mul
    (mul_nonneg (prod_nonneg (fun i _ => Bnn _ _)) (prod_nonneg (fun _ _ => zero_le_one))) hG _)
  rw [inv_pow, ← one_div, padicNorm.div, padicNorm.one, padicNorm_pow (ℓ := p), hC2, prod_mul_distrib,
    prod_const, card_univ, Fintype.card_fin, prod_const_one, mul_one, ← mul_assoc, one_div,
    inv_mul_cancel₀ hpos.ne', one_mul, ← pow_mul]
  ring_nf

end Chi2Irr
