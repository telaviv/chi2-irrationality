/-
# Lemma 10_e, steps 4–7: `ν(f) ≥ R(h)` for every nonvanishing slot term

For `f : Fin h → SIdx M h` whose `X`-keys (`skey`) and `Y`-keys (`ykey`) are injective (otherwise a determinant
has two equal rows), with `I` node rows and `P = h − I` pole rows:
* prices (`price_nodes`, `price_poles`): `Σ_node 2m ≥ I(I−1)/2 − I + max(0, 2M_x − h)`, `Σ_pole (2k+1) ≥ P²`;
* differences (`sum_ccP_ge`): `Σ_{i,j} c ≥ (I² + P²)(1 − 2^{−L}) − 2LI − LP − 2IP`;
* derivative rows: at most `I`, each losing `⌊log₂ M_x⌋` (`large_node`);
* `final_arith` (the quadratic minimisation of RESULT §2 step 7):
  `ν(f) ≥ R(h) = m_e h² − h(3e/2 + 4⌊log₂ h⌋ + 4)`, `m_e = e − 2(e+1)²/(3e+8)`.
-/
import Chi2Irrational.Q.Even.Terms

namespace Chi2Irr
namespace Q

open Finset

variable {M h : ℕ}

/-- The `Y`-key of a slot. -/
def ykey : SIdx M h → SKey M h
  | Sum.inl (m, τ) => Sum.inl (m, decide ((τ : ℕ) = 2))
  | Sum.inr k => Sum.inr k

lemma yS_eq_of_ykey {a b : SIdx M h} (hab : ykey a = ykey b) : yS M h a = yS M h b := by
  rcases a with ⟨m, τ⟩ | k <;> rcases b with ⟨m', τ'⟩ | k' <;> simp only [ykey, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq, Prod.mk.injEq] at hab
  · obtain ⟨rfl, hτ⟩ := hab
    simp only [yS]
    have : ((τ : ℕ) = 2) ↔ ((τ' : ℕ) = 2) := by simpa using hτ
    funext j; simp only [this]
  · rw [hab]

def nodeM : SIdx M h → ℕ
  | Sum.inl (m, _) => (m : ℕ)
  | Sum.inr _ => 0

def poleK : SIdx M h → ℕ
  | Sum.inl _ => 0
  | Sum.inr k => (k : ℕ)

def xbool : SIdx M h → Bool
  | Sum.inl (_, τ) => decide ((τ : ℕ) = 1)
  | Sum.inr _ => false

/-- The `R(h)` of the plan: `m_e h² − h(3e/2 + 4⌊log₂ h⌋ + 4)`. -/
noncomputable def Rbd (e h : ℕ) : ℚ :=
  ((e : ℚ) - 2 * ((e : ℚ) + 1) ^ 2 / (3 * e + 8)) * (h : ℚ) ^ 2 -
    h * (3 * (e : ℚ) / 2 + 4 * (Nat.log 2 h : ℚ) + 4)

/-! ### Arithmetic -/

lemma quad_ge (e I P : ℚ) (he : 0 ≤ e) :
    (e - 2 * (e + 1) ^ 2 / (3 * e + 8)) * (I + P) ^ 2 ≤
      e * (I ^ 2 / 2 + P ^ 2) + (I + P) * (I - P) + (I - P) ^ 2 := by
  have hpos : 0 < 3 * e + 8 := by linarith
  have key : (3 * e + 8) * (e * (I ^ 2 / 2 + P ^ 2) + (I + P) * (I - P) + (I - P) ^ 2) -
      ((3 * e + 8) * e - 2 * (e + 1) ^ 2) * (I + P) ^ 2 = ((3 * e + 8) * I - (2 * e + 2) * (I + P)) ^ 2 / 2 := by
    ring
  have h1 : (e - 2 * (e + 1) ^ 2 / (3 * e + 8)) = ((3 * e + 8) * e - 2 * (e + 1) ^ 2) / (3 * e + 8) := by
    field_simp
  rw [h1, div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [sq_nonneg ((3 * e + 8) * I - (2 * e + 2) * (I + P))]

theorem final_arith (e h I P L t : ℕ) (he : 1 ≤ e) (hIP : I + P = h) (hL : L = t + 1)
    (ht : t = Nat.log 2 h) (hhL : (h : ℚ) < 2 ^ L) (Sn Sp Cc X Ld : ℚ)
    (hSn : (I : ℚ) * (I - 1) / 2 - I + X ≤ Sn) (hSp : (P : ℚ) ^ 2 ≤ Sp)
    (hCc : ((I : ℚ) ^ 2 + P ^ 2) * (1 - 1 / 2 ^ L) - 2 * L * I - L * P - 2 * I * P ≤ Cc)
    (hLd : Ld ≤ e * X + h * (2 * t + 1)) :
    Rbd e h ≤ h * I - h * P + e * (Sn + Sp) + Cc - Ld := by
  have he' : (1 : ℚ) ≤ e := by exact_mod_cast he
  have hIP' : (I : ℚ) + P = h := by exact_mod_cast hIP
  have hq := quad_ge e I P (by linarith)
  rw [hIP'] at hq
  have hD : (0 : ℚ) < 2 ^ L := by positivity
  have hI0 : (0 : ℚ) ≤ I := by positivity
  have hP0 : (0 : ℚ) ≤ P := by positivity
  have hh0 : (0 : ℚ) ≤ h := by positivity
  have hL' : (L : ℚ) = t + 1 := by rw [hL]; push_cast; ring
  -- `(I² + P²)/2^L ≤ h`
  have hsmall : ((I : ℚ) ^ 2 + P ^ 2) * (1 / 2 ^ L) ≤ h := by
    rw [mul_one_div, div_le_iff₀ hD]
    have : (I : ℚ) ^ 2 + P ^ 2 ≤ (h : ℚ) ^ 2 := by rw [← hIP']; nlinarith
    nlinarith
  unfold Rbd
  rw [← ht]
  have hIh : (I : ℚ) ≤ h := by linarith
  have hPh : (P : ℚ) ≤ h := by linarith
  have hLI : (L : ℚ) * I + L * P = L * h := by rw [← hIP']; ring
  nlinarith

/-! ### Facts about a nonvanishing term -/

section Valid

variable (f : Fin h → SIdx M h) (hx : Function.Injective (fun i => skey (f i)))
  (hy : Function.Injective (fun i => ykey (f i)))

/-- The node rows. -/
def Nrow : Finset (Fin h) := univ.filter (fun i => (f i).isLeft = true)

def Prow : Finset (Fin h) := univ.filter (fun i => ¬ (f i).isLeft = true)

lemma card_N_add_P : (Nrow f).card + (Prow f).card = h := by
  unfold Nrow Prow
  rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]

lemma posS_node {i : Fin h} (hi : i ∈ Nrow f) : posS (f i) = Sum.inl (nodeM (f i)) := by
  have := (mem_filter.mp hi).2
  rcases hfi : f i with ⟨m, τ⟩ | k
  · simp [posS, nodeM]
  · rw [hfi] at this; simp at this

lemma posS_pole {i : Fin h} (hi : i ∈ Prow f) : posS (f i) = Sum.inr (poleK (f i)) := by
  have := (mem_filter.mp hi).2
  rcases hfi : f i with ⟨m, τ⟩ | k
  · rw [hfi] at this; simp at this
  · simp [posS, poleK]

lemma skey_node {i : Fin h} (hi : i ∈ Nrow f) :
    ∃ m : Fin M, (m : ℕ) = nodeM (f i) ∧ skey (f i) = Sum.inl (m, xbool (f i)) := by
  have := (mem_filter.mp hi).2
  rcases hfi : f i with ⟨m, τ⟩ | k
  · exact ⟨m, by simp [nodeM], by simp [skey, xbool]⟩
  · rw [hfi] at this; simp at this

lemma skey_pole {i : Fin h} (hi : i ∈ Prow f) :
    ∃ k : Fin h, (k : ℕ) = poleK (f i) ∧ skey (f i) = Sum.inr k := by
  have := (mem_filter.mp hi).2
  rcases hfi : f i with ⟨m, τ⟩ | k
  · rw [hfi] at this; simp at this
  · exact ⟨k, by simp [poleK], by simp [skey]⟩

include hx in
lemma node_eq_of {i j : Fin h} (hi : i ∈ Nrow f) (hj : j ∈ Nrow f) (hm : nodeM (f i) = nodeM (f j))
    (hb : xbool (f i) = xbool (f j)) : i = j := by
  obtain ⟨m, hm1, hs⟩ := skey_node f hi
  obtain ⟨m', hm1', hs'⟩ := skey_node f hj
  refine hx ?_
  simp only
  rw [hs, hs', hb, Fin.ext (hm1.trans (hm.trans hm1'.symm))]

include hx in
lemma pole_eq_of {i j : Fin h} (hi : i ∈ Prow f) (hj : j ∈ Prow f) (hk : poleK (f i) = poleK (f j)) :
    i = j := by
  obtain ⟨k, hk1, hs⟩ := skey_pole f hi
  obtain ⟨k', hk1', hs'⟩ := skey_pole f hj
  refine hx ?_
  simp only
  rw [hs, hs', Fin.ext (hk1.trans (hk.trans hk1'.symm))]

include hx in
lemma node_fibre {i : Fin h} (hi : i ∈ Nrow f) :
    ((Nrow f).filter (fun j => nodeM (f j) = nodeM (f i))).card ≤ 2 := by
  have := card_le_card_of_injOn (fun j => xbool (f j)) (t := (univ : Finset Bool))
    (s := (Nrow f).filter (fun j => nodeM (f j) = nodeM (f i))) (fun j _ => mem_coe.mpr (mem_univ _))
    (fun a ha b hb hab => node_eq_of f hx (mem_filter.mp ha).1 (mem_filter.mp hb).1
      ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) hab)
  simpa using this

include hx in
lemma pole_fibre {i : Fin h} (hi : i ∈ Prow f) :
    ((Prow f).filter (fun j => poleK (f j) = poleK (f i))).card ≤ 1 := by
  refine card_le_one.mpr (fun a ha b hb => ?_)
  exact pole_eq_of f hx (mem_filter.mp ha).1 (mem_filter.mp hb).1
    ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)

/-! ### Prices -/

lemma card_mul_le_two_sum_q (S : Finset ℕ) : (S.card : ℚ) * (S.card - 1) ≤ 2 * ∑ x ∈ S, (x : ℚ) := by
  have := card_mul_le_two_sum S
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · rw [h0]; simp only [Nat.cast_zero, zero_mul]; positivity
  · have h2 : ((S.card * (S.card - 1) : ℕ) : ℚ) ≤ ((2 * ∑ x ∈ S, x : ℕ) : ℚ) := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub h0, Nat.cast_mul, Nat.cast_sum] at h2
    simpa using h2

include hy in
lemma price_poles : ((Prow f).card : ℚ) ^ 2 ≤ ∑ i ∈ Prow f, (2 * (poleK (f i) : ℚ) + 1) := by
  have hinj : Set.InjOn (fun i => poleK (f i)) (Prow f) := fun a ha b hb hab => by
    obtain ⟨k, hk1, hs⟩ := skey_pole f ha
    obtain ⟨k', hk1', hs'⟩ := skey_pole f hb
    refine hy ?_
    have ea : ykey (f a) = skey (f a) := by
      have := (mem_filter.mp (mem_coe.mp ha)).2
      rcases hfa : f a with ⟨m, τ⟩ | k <;> rw [hfa] at this <;> simp_all [ykey, skey]
    have eb : ykey (f b) = skey (f b) := by
      have := (mem_filter.mp (mem_coe.mp hb)).2
      rcases hfb : f b with ⟨m, τ⟩ | k <;> rw [hfb] at this <;> simp_all [ykey, skey]
    simp only
    rw [ea, eb, hs, hs', Fin.ext (hk1.trans (hab.trans hk1'.symm))]
  have h1 := card_mul_le_two_sum_q ((Prow f).image (fun i => poleK (f i)))
  rw [card_image_of_injOn hinj, sum_image hinj] at h1
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
  nlinarith

include hx in
lemma price_nodes :
    ((Nrow f).card : ℚ) * ((Nrow f).card - 1) / 2 - (Nrow f).card +
        max 0 (2 * ((univ.sup (fun i => nodeM (f i)) : ℕ) : ℚ) - h) ≤
      ∑ i ∈ Nrow f, 2 * (nodeM (f i) : ℚ) := by
  set Mx := univ.sup fun i => nodeM (f i) with hMx
  set κ : Fin h → ℕ := fun i => 2 * nodeM (f i) + (if xbool (f i) then 1 else 0) with hκ
  have hinj : Set.InjOn κ (Nrow f) := fun a ha b hb hab => by
    have hab' : 2 * nodeM (f a) + (if xbool (f a) then 1 else 0) =
        2 * nodeM (f b) + (if xbool (f b) then 1 else 0) := hab
    have hm : nodeM (f a) = nodeM (f b) := by split_ifs at hab' <;> omega
    have hb' : xbool (f a) = xbool (f b) := by
      cases h1 : xbool (f a) <;> cases h2 : xbool (f b) <;> rw [h1, h2] at hab' <;> simp at hab' <;> omega
    exact node_eq_of f hx ha hb hm hb'
  have hκle : ∀ i, (κ i : ℚ) ≤ 2 * (nodeM (f i) : ℚ) + 1 := fun i => by
    simp only [hκ]; push_cast; split_ifs <;> norm_num
  have hsum : ∑ i ∈ Nrow f, (κ i : ℚ) ≤ ∑ i ∈ Nrow f, 2 * (nodeM (f i) : ℚ) + (Nrow f).card := by
    calc ∑ i ∈ Nrow f, (κ i : ℚ) ≤ ∑ i ∈ Nrow f, (2 * (nodeM (f i) : ℚ) + 1) := sum_le_sum (fun i _ => hκle i)
      _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
  have h1 := card_mul_le_two_sum_q ((Nrow f).image κ)
  rw [card_image_of_injOn hinj, sum_image hinj] at h1
  have hIh : ((Nrow f).card : ℚ) ≤ h := by
    have := card_N_add_P f; have : (Nrow f).card ≤ h := by omega
    exact_mod_cast this
  rcases le_or_gt (2 * (Mx : ℚ) - h) 0 with hX | hX
  · rw [max_eq_left hX]; linarith
  · rw [max_eq_right hX.le]
    have hMpos : 0 < Mx := by
      by_contra h0
      have : Mx = 0 := by omega
      rw [this] at hX; push_cast at hX
      linarith [(by positivity : (0 : ℚ) ≤ h)]
    have hne : (univ : Finset (Fin h)).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      rw [hMx, hne, sup_empty] at hMpos; exact lt_irrefl _ hMpos
    obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_sup univ hne (fun i => nodeM (f i))
    have hi₀N : i₀ ∈ Nrow f := by
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rcases hfi : f i₀ with ⟨m, τ⟩ | k
      · rfl
      · exfalso
        rw [hfi] at hi₀
        have h0 : Mx = 0 := by rw [hMx]; exact hi₀
        omega
    have hinj' : Set.InjOn κ ((Nrow f).erase i₀) := hinj.mono (fun x hx => erase_subset _ _ (mem_coe.mp hx))
    have h2 := card_mul_le_two_sum_q (((Nrow f).erase i₀).image κ)
    rw [card_image_of_injOn hinj', sum_image hinj', card_erase_of_mem hi₀N] at h2
    have hI1 : 1 ≤ (Nrow f).card := card_pos.mpr ⟨i₀, hi₀N⟩
    have hc : (((Nrow f).card - 1 : ℕ) : ℚ) = ((Nrow f).card : ℚ) - 1 := by rw [Nat.cast_sub hI1]; simp
    rw [hc] at h2
    have hsplit := add_sum_erase (Nrow f) (fun i => (κ i : ℚ)) hi₀N
    have hκ0 : 2 * (Mx : ℚ) ≤ κ i₀ := by
      simp only [hκ]; push_cast; rw [← hi₀, ← hMx]; split_ifs <;> linarith
    nlinarith

/-! ### The difference sum -/

lemma ccP_nn {L : ℕ} {i j : Fin h} (hi : i ∈ Nrow f) (hj : j ∈ Nrow f) :
    (ccP L (posS (f i)) (posS (f j)) : ℚ) =
      ((if nodeM (f i) = nodeM (f j) then 0 else cntL L (nodeM (f i)) (nodeM (f j)) : ℕ) : ℚ) := by
  rw [posS_node f hi, posS_node f hj]; simp only [ccP]; split_ifs <;> simp

lemma ccP_pp {L : ℕ} {i j : Fin h} (hi : i ∈ Prow f) (hj : j ∈ Prow f) :
    (ccP L (posS (f i)) (posS (f j)) : ℚ) =
      ((if poleK (f i) = poleK (f j) then 0 else cntL L (poleK (f i)) (poleK (f j)) : ℕ) : ℚ) := by
  rw [posS_pole f hi, posS_pole f hj]; simp only [ccP]; split_ifs <;> simp

lemma ccP_np {L : ℕ} {i j : Fin h} (hi : i ∈ Nrow f) (hj : j ∈ Prow f) :
    (ccP L (posS (f i)) (posS (f j)) : ℚ) = -1 := by
  rw [posS_node f hi, posS_pole f hj]; simp [ccP]

lemma ccP_pn {L : ℕ} {i j : Fin h} (hi : i ∈ Prow f) (hj : j ∈ Nrow f) :
    (ccP L (posS (f i)) (posS (f j)) : ℚ) = -1 := by
  rw [posS_pole f hi, posS_node f hj]; simp [ccP]

lemma sum_split (G : Fin h → ℚ) : ∑ i, G i = ∑ i ∈ Nrow f, G i + ∑ i ∈ Prow f, G i :=
  (sum_filter_add_sum_filter_not univ (fun i => (f i).isLeft = true) G).symm

include hx in
lemma sum_ccP_ge (L : ℕ) :
    (((Nrow f).card : ℚ) ^ 2 + ((Prow f).card : ℚ) ^ 2) * (1 - 1 / 2 ^ L) - 2 * L * (Nrow f).card -
        L * (Prow f).card - 2 * (Nrow f).card * (Prow f).card ≤
      ∑ i, ∑ j, (ccP L (posS (f i)) (posS (f j)) : ℚ) := by
  rw [sum_split f]
  simp only [sum_split f (fun j => (ccP L (posS (f _)) (posS (f j)) : ℚ))]
  rw [sum_add_distrib, sum_add_distrib]
  have hA := sum_cntL_ge (Nrow f) (fun i => nodeM (f i)) 2 L (fun i hi => node_fibre f hx hi)
  have hB := sum_cntL_ge (Prow f) (fun i => poleK (f i)) 1 L (fun i hi => pole_fibre f hx hi)
  rw [sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => ccP_nn f hi hj))]
  rw [sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => ccP_np f hi hj))]
  rw [sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => ccP_pn f hi hj))]
  rw [sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => ccP_pp f hi hj))]
  simp only [sum_const, nsmul_eq_mul, mul_neg, mul_one, Nat.cast_ofNat, Nat.cast_one] at hA hB ⊢
  nlinarith

/-! ### Derivative rows -/

lemma card_Ux_Uy : (Ux f).card + (Uy f).card ≤ (Nrow f).card := by
  have hdisj : Disjoint (Ux f) (Uy f) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have h1 := (mem_filter.mp h1).2
    have h2 := (mem_filter.mp h2).2
    rcases hfi : f i with ⟨m, τ⟩ | k <;> rw [hfi] at h1 h2 <;> simp [dxS, dyS] at h1 h2
    omega
  have hsub : Ux f ∪ Uy f ⊆ Nrow f := by
    intro i hi
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rcases mem_union.mp hi with h1 | h1 <;> have h1 := (mem_filter.mp h1).2 <;>
      rcases hfi : f i with ⟨m, τ⟩ | k <;> rw [hfi] at h1 <;> simp_all [dxS, dyS]
  rw [← card_union_of_disjoint hdisj]
  exact card_le_card hsub

lemma hz_der (i : Fin h) (hi : dxS (f i) = true ∨ dyS (f i) = true) (j : Fin h)
    (hj : zP (posS (f j)) ≠ zP (posS (f i))) :
    (2 : ℚ) ^ (-(Nat.log 2 (univ.sup fun i => nodeM (f i)) : ℤ)) ≤
      padicNorm 2 (zP (posS (f i)) - zP (posS (f j))) := by
  set Mx := univ.sup fun i => nodeM (f i)
  have hMi : nodeM (f i) ≤ Mx := le_sup (f := fun i => nodeM (f i)) (mem_univ i)
  have hMj : nodeM (f j) ≤ Mx := le_sup (f := fun i => nodeM (f i)) (mem_univ j)
  have hle1 : (2 : ℚ) ^ (-(Nat.log 2 Mx : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  rcases hfi : f i with ⟨m, τ⟩ | k
  · try simp only [hfi] at hMi hj ⊢
    simp only [nodeM] at hMi
    rcases hfj : f j with ⟨m', τ'⟩ | k'
    · try simp only [hfj] at hMj hj ⊢
      simp only [nodeM] at hMj
      simp only [posS, zP] at hj ⊢
      have hmm : (m : ℕ) ≠ m' := fun e => hj (by rw [e])
      rw [tN_sub_tN]
      rcases lt_or_gt_of_ne hmm with hlt | hlt
      · have e : ((m' : ℕ) : ℚ) - (m : ℕ) = (((m' : ℕ) - m : ℕ) : ℚ) := by rw [Nat.cast_sub hlt.le]
        rw [e]; exact le_padicNorm_of_le (by omega) (by omega)
      · have e : ((m' : ℕ) : ℚ) - (m : ℕ) = -(((m : ℕ) - m' : ℕ) : ℚ) := by rw [Nat.cast_sub hlt.le]; ring
        rw [e, padicNorm.neg]; exact le_padicNorm_of_le (by omega) (by omega)
    · simp only [posS, zP]
      rw [padicNorm_tN_sub_pole]; linarith
  · rw [hfi] at hi; simp [dxS, dyS] at hi

/-! ### `ν(f) ≥ R(h)` -/

lemma wexp_node {e : ℕ} {i : Fin h} (hi : i ∈ Nrow f) :
    (wexp e h (f i) : ℚ) = h + e * (2 * (nodeM (f i) : ℚ)) := by
  have := (mem_filter.mp hi).2
  rcases hfi : f i with ⟨m, τ⟩ | k
  · simp [wexp, nodeM]
  · rw [hfi] at this; simp at this

lemma wexp_pole {e : ℕ} {i : Fin h} (hi : i ∈ Prow f) :
    (wexp e h (f i) : ℚ) = -(h : ℚ) + e * (2 * (poleK (f i) : ℚ) + 1) := by
  have := (mem_filter.mp hi).2
  rcases hfi : f i with ⟨m, τ⟩ | k
  · rw [hfi] at this; simp at this
  · simp [wexp, poleK]

include hx hy in
/-- **`ν(f) ≥ R(h)`** for a nonvanishing term. -/
theorem nu_ge (e : ℕ) (he : 1 ≤ e) :
    Rbd e h ≤ (nuF e (Nat.log 2 h + 1) (Nat.log 2 (univ.sup fun i => nodeM (f i))) f : ℚ) := by
  set Mx := univ.sup fun i => nodeM (f i) with hMx
  set I := (Nrow f).card
  set P := (Prow f).card
  have hIP : I + P = h := card_N_add_P f
  have hW : ∑ i, (wexp e h (f i) : ℚ) = h * I - h * P +
      e * (∑ i ∈ Nrow f, 2 * (nodeM (f i) : ℚ) + ∑ i ∈ Prow f, (2 * (poleK (f i) : ℚ) + 1)) := by
    rw [sum_split f, sum_congr rfl (fun i hi => wexp_node f hi), sum_congr rfl (fun i hi => wexp_pole f hi)]
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    ring
  have hd : (Ux f).card + (Uy f).card ≤ h := by have := card_Ux_Uy f; omega
  have hLd := large_node e h Mx ((Ux f).card + (Uy f).card) he hd
  have hLd' : ((Nat.log 2 Mx : ℕ) : ℚ) * (((Ux f).card + (Uy f).card : ℕ) : ℚ) ≤
      e * max 0 (2 * (Mx : ℚ) - h) + h * (2 * Nat.log 2 h + 1) := by
    have := (Int.cast_le (R := ℚ)).mpr hLd
    push_cast at this ⊢
    exact this
  have hhL : (h : ℚ) < 2 ^ (Nat.log 2 h + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) h
  have key := final_arith e h I P (Nat.log 2 h + 1) (Nat.log 2 h) he hIP rfl rfl hhL
    (∑ i ∈ Nrow f, 2 * (nodeM (f i) : ℚ)) (∑ i ∈ Prow f, (2 * (poleK (f i) : ℚ) + 1))
    (∑ i, ∑ j, (ccP (Nat.log 2 h + 1) (posS (f i)) (posS (f j)) : ℚ)) (max 0 (2 * (Mx : ℚ) - h))
    (((Nat.log 2 Mx : ℕ) : ℚ) * (((Ux f).card + (Uy f).card : ℕ) : ℚ))
    (price_nodes f hx) (price_poles f hy) (sum_ccP_ge f hx _) (by push_cast at hLd' ⊢; linarith)
  unfold nuF
  push_cast
  rw [hW]
  push_cast at key
  linarith

end Valid

end Q
end Chi2Irr
