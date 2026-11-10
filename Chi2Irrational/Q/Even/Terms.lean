/-
# Lemma 10_e, step 3: the slot terms of Lemma 4′'s expansion

For the truncated rank-one matrix `Mdec M h` of `Arith/QAdic.lean` (slots: nodes `−m` with three rank-one forms,
poles `x_k`), Andreief gives `h!·det Mdec = Σ_f (∏_i ccS(f i)) · det X_f · det Y_f`. Here:
* `WLe_ccS`: `‖ccS s‖_{v_e} ≤ 2^{−wexp s}`, `wexp(node m) = h + 2em`, `wexp(pole k) = −h + e(2k+1)`
  (`|φ′(−m)|₂, |φ(−m)|₂ ≤ 2^{−h}`, `|4ω_k|₂ ≤ 2^h`, `‖χ₂ + X‖_{v_e} ≤ 1`);
* `det_xS`, `det_yS`: `det X_f`, `det Y_f` are the determinants of `CoreDet.lean` at the points of `f`;
* `gz_le_ccP`: the point differences `|z_t − z_s|₂ ≤ 2^{−ccP s t}` (node–node and pole–pole by `cntL`,
  node–pole `= 2`).
-/
import Chi2Irrational.Arith.Special
import Chi2Irrational.Q.Even.WNorm
import Chi2Irrational.Q.Even.CoreDet
import Chi2Irrational.Q.Even.Count

namespace Chi2Irr
namespace Q

open Finset
open scoped Nat

/-! ### Factor bounds -/

lemma padicNorm_half_odd (n : ℤ) : padicNorm 2 ((n : ℚ) + 1 / 2) = 2 := by
  have e : (n : ℚ) + 1 / 2 = ((2 * n + 1 : ℤ) : ℚ) / 2 := by push_cast; ring
  have hodd : padicNorm 2 ((2 * n + 1 : ℤ) : ℚ) = 1 := by
    rw [padicNorm.int_eq_one_iff]
    intro hd
    have : (2 : ℤ) ∣ 1 := by
      have h2 : (2 : ℤ) ∣ 2 * n := dvd_mul_right 2 n
      have := (Int.dvd_add_right h2).mp (by exact_mod_cast hd)
      exact this
    omega
  rw [e, padicNorm.div, hodd]
  have : padicNorm 2 (2 : ℚ) = 1 / 2 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]; norm_num
  rw [this]; norm_num

lemma padicNorm_tN_sub_pole (m k : ℕ) : padicNorm 2 (tN m - pole k) = 2 := by
  have e : tN m - pole k = ((k : ℤ) - m : ℤ) + 1 / 2 := by unfold tN pole; push_cast; ring
  rw [e, padicNorm_half_odd]

lemma padicNorm_tN_le (m : ℕ) : padicNorm 2 (tN m) ≤ 1 := by
  unfold tN; rw [padicNorm.neg]; exact padicNorm.of_nat m

lemma padicNorm_Dpoly_tN (h m : ℕ) : padicNorm 2 ((Dpoly h).eval (tN m)) = 2 ^ h := by
  unfold Dpoly
  rw [Polynomial.eval_prod, CoreDet.padicNorm_prod_fin]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, padicNorm_tN_sub_pole]
  rw [prod_const, card_range]

lemma padicNorm_dDpoly_tN (h m : ℕ) : padicNorm 2 ((Polynomial.derivative (Dpoly h)).eval (tN m)) ≤ 2 ^ h := by
  unfold Dpoly
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  refine padicNorm.sum_le' (fun k hk => ?_) (by positivity)
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [CoreDet.padicNorm_prod_fin]
  simp only [padicNorm_tN_sub_pole]
  rw [prod_const, card_erase_of_mem hk, card_range]
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

lemma padicNorm_phv_le (h m : ℕ) : padicNorm 2 (phv h m) ≤ (2 : ℚ) ^ (-(h : ℤ)) := by
  unfold phv
  rw [padicNorm.div, padicNorm_Dpoly_tN, zpow_neg, zpow_natCast]
  rw [div_le_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
  exact padicNorm_tN_le m

lemma padicNorm_phd_le (h m : ℕ) : padicNorm 2 (phd h m) ≤ (2 : ℚ) ^ (-(h : ℤ)) := by
  unfold phd
  rw [padicNorm.div, sq, padicNorm.mul, padicNorm_Dpoly_tN]
  have hnum : padicNorm 2 ((Dpoly h).eval (tN m) - tN m * (Polynomial.derivative (Dpoly h)).eval (tN m)) ≤
      2 ^ h := by
    refine padicNorm.sub.trans (max_le (by rw [padicNorm_Dpoly_tN]) ?_)
    rw [padicNorm.mul]
    calc padicNorm 2 (tN m) * padicNorm 2 ((Polynomial.derivative (Dpoly h)).eval (tN m)) ≤ 1 * 2 ^ h :=
          mul_le_mul (padicNorm_tN_le m) (padicNorm_dDpoly_tN h m) (padicNorm.nonneg _) zero_le_one
      _ = 2 ^ h := one_mul _
  rw [zpow_neg, zpow_natCast, div_le_iff₀ (by positivity)]
  calc _ ≤ (2 : ℚ) ^ h := hnum
    _ = ((2 : ℚ) ^ h)⁻¹ * (2 ^ h * 2 ^ h) := by field_simp

lemma padicNorm_omega_le {h k : ℕ} (hk : k < h) : padicNorm 2 (omega h k) ≤ 2 ^ h := by
  have hd : dPrime h k = (-1) ^ k * ((k ! : ℕ) : ℚ) * (((h - 1 - k) ! : ℕ) : ℚ) := by
    unfold dPrime
    have := prod_pole_erase 0 (h - 1) k (by omega)
    rw [show 0 + (h - 1) + 1 = h by omega, zero_add, ← range_eq_Ico] at this
    exact this
  have hsign : padicNorm 2 ((-1 : ℚ) ^ k) = 1 := by
    rcases neg_one_pow_eq_or ℚ k with h1 | h1 <;> rw [h1] <;> simp
  have hpole : padicNorm 2 (pole k) = 2 := by
    have e : pole k = (((-(k : ℤ) - 1 : ℤ) : ℚ) + 1 / 2) := by unfold pole; push_cast; ring
    rw [e, padicNorm_half_odd]
  unfold omega
  rw [padicNorm.div, hd, padicNorm.mul, padicNorm.mul, hsign, one_mul, padicNorm_factorial, padicNorm_factorial,
    hpole, ← zpow_add₀ two_ne_zero, div_eq_mul_inv, ← zpow_neg]
  have h1 := vf_le k
  have h2 := vf_le (h - 1 - k)
  calc (2 : ℚ) * 2 ^ (-(-((vf k : ℕ) : ℤ) + -((vf (h - 1 - k) : ℕ) : ℤ))) =
      2 ^ ((1 : ℤ) + (vf k + vf (h - 1 - k) : ℕ)) := by
        rw [zpow_add₀ two_ne_zero, zpow_one]; push_cast; ring_nf
    _ ≤ 2 ^ ((h : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
    _ = 2 ^ h := zpow_natCast _ _

/-! ### Weighted norms of the rank-one coefficients -/

variable {M h : ℕ}

lemma WLeP_chiS (e : ℕ) : WLeP e 1 chiS := fun n => by
  unfold chiS
  rw [PowerSeries.coeff_mk]
  split_ifs with hn
  · rw [padicNorm.zero]; positivity
  · have ho : Odd n := Nat.not_even_iff_odd.mp hn
    have e1 : (n : ℚ) ^ 2 = ((n ^ 2 : ℕ) : ℚ) := by push_cast; ring
    rw [padicNorm.div, padicNorm.one, e1, padicNorm_two_odd (ho.pow), div_one, one_mul]
    exact one_le_pow₀ (by norm_num)

/-- The exponent of the weight of a slot: `h + 2em` at the node `−m`, `−h + e(2k+1)` at the pole `x_k`. -/
def wexp (e h : ℕ) {M : ℕ} : SIdx M h → ℤ
  | Sum.inl (m, _) => h + e * (2 * (m : ℕ))
  | Sum.inr k => -(h : ℤ) + e * (2 * (k : ℕ) + 1)

lemma two_zpow_split (a b : ℕ) : (2 : ℚ) ^ (-((a : ℤ) + b)) = (2 : ℚ) ^ (-(a : ℤ)) * ((2 : ℚ) ^ b)⁻¹ := by
  rw [neg_add, zpow_add₀ two_ne_zero, zpow_neg (2 : ℚ) (b : ℤ), zpow_natCast]

lemma WLe_ccS (e : ℕ) (s : SIdx M h) : WLe e ((2 : ℚ) ^ (-(wexp e h s))) (ccS M h s) := by
  rcases s with ⟨m, τ⟩ | k
  · have hr : padicNorm 2 (-(if (τ : ℕ) = 0 then phd h m else phv h m)) ≤ (2 : ℚ) ^ (-(h : ℤ)) := by
      rw [padicNorm.neg]; split_ifs
      · exact padicNorm_phd_le h m
      · exact padicNorm_phv_le h m
    refine WLe_mono ?_ (WLe_C (mul_nonneg (padicNorm.nonneg _) (by positivity))
      (WLeP_C_mul_X_pow (e := e) _ (2 * (m : ℕ))))
    simp only [wexp]
    rw [show ((e : ℤ) * (2 * ((m : ℕ) : ℤ))) = ((e * (2 * (m : ℕ)) : ℕ) : ℤ) by push_cast; ring,
      two_zpow_split]
    exact mul_le_mul_of_nonneg_right hr (by positivity)
  · have hr : padicNorm 2 (-4 * omega h k) ≤ (2 : ℚ) ^ h := by
      rw [padicNorm.mul, padicNorm.neg]
      have h4 : padicNorm 2 (4 : ℚ) ≤ 1 := by
        have := padicNorm.of_nat (p := 2) 4; simpa using this
      calc padicNorm 2 4 * padicNorm 2 (omega h k) ≤ 1 * 2 ^ h :=
            mul_le_mul h4 (padicNorm_omega_le k.isLt) (padicNorm.nonneg _) zero_le_one
        _ = 2 ^ h := one_mul _
    have h1 := WLe_C (e := e) (mul_nonneg (padicNorm.nonneg _) (by positivity))
      (WLeP_C_mul_X_pow (e := e) (-4 * omega h k) (2 * (k : ℕ) + 1))
    have h2 : WLe e 1 (Polynomial.C chiS + Polynomial.X) := WLe_add (WLe_C zero_le_one (WLeP_chiS e)) WLe_X
    have h3 := WLe_mul (mul_nonneg (padicNorm.nonneg _) (by positivity)) zero_le_one h1 h2
    rw [mul_one] at h3
    refine WLe_mono ?_ h3
    simp only [wexp]
    rw [show (-(-(h : ℤ) + (e : ℤ) * (2 * ((k : ℕ) : ℤ) + 1))) =
        (h : ℤ) + -((e * (2 * (k : ℕ) + 1) : ℕ) : ℤ) by push_cast; ring, zpow_add₀ two_ne_zero,
      zpow_neg (2 : ℚ) (((e * (2 * (k : ℕ) + 1)) : ℕ) : ℤ), zpow_natCast, zpow_natCast]
    exact mul_le_mul_of_nonneg_right hr (by positivity)

/-! ### Points and rows of a slot -/

/-- The position of a slot: `inl m` for the node `−m`, `inr k` for the pole `x_k`. -/
def posS : SIdx M h → ℕ ⊕ ℕ
  | Sum.inl (m, _) => Sum.inl (m : ℕ)
  | Sum.inr k => Sum.inr (k : ℕ)

/-- The point of a position. -/
def zP : ℕ ⊕ ℕ → ℚ
  | Sum.inl m => tN m
  | Sum.inr k => pole k

/-- A derivative row in `X` (`τ = 1`), in `Y` (`τ = 2`). -/
def dxS : SIdx M h → Bool
  | Sum.inl (_, τ) => decide ((τ : ℕ) = 1)
  | Sum.inr _ => false

def dyS : SIdx M h → Bool
  | Sum.inl (_, τ) => decide ((τ : ℕ) = 2)
  | Sum.inr _ => false

lemma xS_eq (s : SIdx M h) (j : Fin h) :
    xS M h s j = Polynomial.C (algebraMap ℚ (PowerSeries ℚ)
      (if dxS s then ((j : ℕ) : ℚ) * zP (posS s) ^ ((j : ℕ) - 1) else zP (posS s) ^ (j : ℕ))) := by
  rcases s with ⟨m, τ⟩ | k <;> simp [xS, dxS, zP, posS]

lemma yS_eq (s : SIdx M h) (j : Fin h) :
    yS M h s j = Polynomial.C (algebraMap ℚ (PowerSeries ℚ)
      (if dyS s then ((j : ℕ) : ℚ) * zP (posS s) ^ ((j : ℕ) - 1) else zP (posS s) ^ (j : ℕ))) := by
  rcases s with ⟨m, τ⟩ | k <;> simp [yS, dyS, zP, posS]

/-- The `ℚ`-matrix of `CoreDet.lean`. -/
def Rmat (z : Fin h → ℚ) (U : Finset (Fin h)) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun i j => if i ∈ U then ((j : ℕ) : ℚ) * z i ^ ((j : ℕ) - 1) else z i ^ (j : ℕ)

lemma det_C_alg (R : Matrix (Fin h) (Fin h) ℚ) :
    (R.map (fun r => Polynomial.C (algebraMap ℚ (PowerSeries ℚ) r))).det =
      Polynomial.C (algebraMap ℚ (PowerSeries ℚ) R.det) := by
  have := RingHom.map_det ((Polynomial.C).comp (algebraMap ℚ (PowerSeries ℚ))) R
  rw [RingHom.mapMatrix_apply] at this
  exact this.symm

lemma det_xS (f : Fin h → SIdx M h) :
    (Matrix.of fun i j => xS M h (f i) j).det = Polynomial.C (algebraMap ℚ (PowerSeries ℚ)
      (Rmat (fun i => zP (posS (f i))) (univ.filter (fun i => dxS (f i) = true))).det) := by
  rw [← det_C_alg]
  congr 1
  ext i j
  simp only [Matrix.of_apply, xS_eq, Rmat, Matrix.map_apply, mem_filter, mem_univ, true_and]

lemma det_yS (f : Fin h → SIdx M h) :
    (Matrix.of fun i j => yS M h (f i) j).det = Polynomial.C (algebraMap ℚ (PowerSeries ℚ)
      (Rmat (fun i => zP (posS (f i))) (univ.filter (fun i => dyS (f i) = true))).det) := by
  rw [← det_C_alg]
  congr 1
  ext i j
  simp only [Matrix.of_apply, yS_eq, Rmat, Matrix.map_apply, mem_filter, mem_univ, true_and]

/-! ### Point differences -/

/-- The exponent of a pair of positions. -/
def ccP (L : ℕ) : ℕ ⊕ ℕ → ℕ ⊕ ℕ → ℤ
  | Sum.inl a, Sum.inl b => if a = b then 0 else (cntL L a b : ℤ)
  | Sum.inr a, Sum.inr b => if a = b then 0 else (cntL L a b : ℤ)
  | _, _ => -1

lemma ccP_comm (L : ℕ) (s t : ℕ ⊕ ℕ) : ccP L s t = ccP L t s := by
  rcases s with a | a <;> rcases t with b | b <;> simp only [ccP]
  · by_cases hab : a = b
    · simp [hab]
    · rw [if_neg hab, if_neg (Ne.symm hab), cntL_comm]
  · by_cases hab : a = b
    · simp [hab]
    · rw [if_neg hab, if_neg (Ne.symm hab), cntL_comm]

lemma ccP_self (L : ℕ) (s : ℕ ⊕ ℕ) : ccP L s s = 0 := by rcases s with a | a <;> simp [ccP]

lemma tN_sub_tN (a b : ℕ) : tN b - tN a = (a : ℚ) - b := by unfold tN; ring

lemma gz_le_ccP (L : ℕ) (s t : ℕ ⊕ ℕ) :
    (if zP s ≠ zP t then padicNorm 2 (zP t - zP s) else 1) ≤ (2 : ℚ) ^ (-(ccP L s t)) := by
  split_ifs with hz
  · rcases s with a | a <;> rcases t with b | b <;> simp only [zP, ccP] at hz ⊢
    · have hab : a ≠ b := by rintro rfl; exact hz rfl
      rw [if_neg hab, tN_sub_tN]; exact padicNorm_sub_le_cntL hab
    · rw [← padicNorm.neg, neg_sub, padicNorm_tN_sub_pole]; norm_num
    · rw [padicNorm_tN_sub_pole]; norm_num
    · have hab : a ≠ b := by rintro rfl; exact hz rfl
      rw [if_neg hab, pole_sub_pole']; exact padicNorm_sub_le_cntL hab
  · push Not at hz
    rcases s with a | a <;> rcases t with b | b <;> simp only [zP, ccP] at hz ⊢
    · have : a = b := by unfold tN at hz; exact_mod_cast neg_injective hz
      subst this; simp
    · exfalso
      have := padicNorm_tN_sub_pole a b
      rw [hz, sub_self, padicNorm.zero] at this; norm_num at this
    · exfalso
      have := padicNorm_tN_sub_pole b a
      rw [hz, sub_self, padicNorm.zero] at this; norm_num at this
    · have : a = b := pole_injective hz
      subst this; simp

/-! ### The bound on one term -/

lemma prod_two_zpow {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, (2 : ℚ) ^ (a i) = (2 : ℚ) ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [prod_insert hx, sum_insert hx, ih, zpow_add₀ two_ne_zero]

lemma sum_sym_eq_two_mul (c : Fin h → Fin h → ℤ) (hc : ∀ i j, c i j = c j i) (hd : ∀ i, c i i = 0) :
    ∑ i, ∑ j, c i j = 2 * ∑ p ∈ CoreDet.Spr h, c p.1 p.2 := by
  have hsplit : ∀ i j, c i j = (if i < j then c i j else 0) + (if j < i then c i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, not_lt.mpr hij.le]
    · simp [hd]
    · simp [hij, not_lt.mpr hij.le]
  have h1 : ∑ p ∈ CoreDet.Spr h, c p.1 p.2 = ∑ i, ∑ j, (if i < j then c i j else 0) := by
    unfold CoreDet.Spr
    rw [sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ i, ∑ j, (if j < i then c i j else 0) = ∑ i, ∑ j, (if i < j then c i j else 0) := by
    rw [sum_comm]
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
    rw [hc]
  calc ∑ i, ∑ j, c i j = ∑ i, ∑ j, ((if i < j then c i j else 0) + (if j < i then c i j else 0)) :=
        sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => hsplit i j))
    _ = 2 * ∑ p ∈ CoreDet.Spr h, c p.1 p.2 := by
        simp only [sum_add_distrib]; rw [h2, ← h1]; ring

lemma prod_gz_le (L : ℕ) (g : Fin h → ℕ ⊕ ℕ) :
    ∏ p ∈ CoreDet.Spr h, CoreDet.gz (fun i => zP (g i)) p ≤
      (2 : ℚ) ^ (-(∑ p ∈ CoreDet.Spr h, ccP L (g p.1) (g p.2))) := by
  rw [← sum_neg_distrib, ← prod_two_zpow]
  exact prod_le_prod₀ (fun p _ => CoreDet.gz_nonneg _ p) (fun p _ => gz_le_ccP L (g p.1) (g p.2))

/-- The `X`- and `Y`-derivative rows of `f`. -/
def Ux (f : Fin h → SIdx M h) : Finset (Fin h) := univ.filter (fun i => dxS (f i) = true)

def Uy (f : Fin h → SIdx M h) : Finset (Fin h) := univ.filter (fun i => dyS (f i) = true)

/-- The exponent `ν(f)` of a term. -/
def nuF (e L Λ : ℕ) (f : Fin h → SIdx M h) : ℤ :=
  ∑ i, wexp e h (f i) + ∑ i, ∑ j, ccP L (posS (f i)) (posS (f j)) - Λ * ((Ux f).card + (Uy f).card)

/-- **One term**: `‖(∏ ccS) · det X_f · det Y_f‖_{v_e} ≤ 2^{−ν(f)}`. -/
theorem WLe_term (e L Λ : ℕ) (f : Fin h → SIdx M h)
    (hz : ∀ i, (dxS (f i) = true ∨ dyS (f i) = true) → ∀ j, zP (posS (f j)) ≠ zP (posS (f i)) →
      (2 : ℚ) ^ (-(Λ : ℤ)) ≤ padicNorm 2 (zP (posS (f i)) - zP (posS (f j)))) :
    WLe e ((2 : ℚ) ^ (-(nuF e L Λ f)))
      ((∏ i, ccS M h (f i)) * (Matrix.of fun i j => xS M h (f i) j).det *
        (Matrix.of fun i j => yS M h (f i) j).det) := by
  set z : Fin h → ℚ := fun i => zP (posS (f i)) with hzdef
  have h1 := WLe_prod univ (fun i => (2 : ℚ) ^ (-(wexp e h (f i)))) (fun i => by positivity)
    (fun i => ccS M h (f i)) (fun i _ => WLe_ccS e (f i))
  rw [det_xS, det_yS]
  have h2 := WLe_C (e := e) (padicNorm.nonneg _) (WLeP_algebraMap (e := e)
    (Rmat (fun i => zP (posS (f i))) (Ux f)).det)
  have h3 := WLe_C (e := e) (padicNorm.nonneg _) (WLeP_algebraMap (e := e)
    (Rmat (fun i => zP (posS (f i))) (Uy f)).det)
  refine WLe_mono ?_ (WLe_mul (mul_nonneg (prod_nonneg (fun i _ => by positivity)) (padicNorm.nonneg _))
    (padicNorm.nonneg _) (WLe_mul (prod_nonneg (fun i _ => by positivity)) (padicNorm.nonneg _) h1 h2) h3)
  -- the determinant bounds
  have hdx := CoreDet.padicNorm_detR_le (z := z) (Ux f) Λ (fun i hi j hj => hz i
    (Or.inl (mem_filter.mp hi).2) j hj)
  have hdy := CoreDet.padicNorm_detR_le (z := z) (Uy f) Λ (fun i hi j hj => hz i
    (Or.inr (mem_filter.mp hi).2) j hj)
  have hg := prod_gz_le L (fun i => posS (f i))
  set S := ∑ p ∈ CoreDet.Spr h, ccP L (posS (f p.1)) (posS (f p.2)) with hS
  have hsym := sum_sym_eq_two_mul (fun i j => ccP L (posS (f i)) (posS (f j)))
    (fun i j => ccP_comm L _ _) (fun i => ccP_self L _)
  have hx : padicNorm 2 (Rmat z (Ux f)).det ≤ (2 : ℚ) ^ (-S) * 2 ^ (Λ * (Ux f).card) :=
    hdx.trans (mul_le_mul_of_nonneg_right hg (by positivity))
  have hy : padicNorm 2 (Rmat z (Uy f)).det ≤ (2 : ℚ) ^ (-S) * 2 ^ (Λ * (Uy f).card) :=
    hdy.trans (mul_le_mul_of_nonneg_right hg (by positivity))
  rw [prod_two_zpow]
  calc (2 : ℚ) ^ (∑ i, -wexp e h (f i)) * padicNorm 2 (Rmat z (Ux f)).det * padicNorm 2 (Rmat z (Uy f)).det
      ≤ (2 : ℚ) ^ (∑ i, -wexp e h (f i)) * ((2 : ℚ) ^ (-S) * 2 ^ (Λ * (Ux f).card)) *
          ((2 : ℚ) ^ (-S) * 2 ^ (Λ * (Uy f).card)) := by
        gcongr
        exact padicNorm.nonneg _
    _ = (2 : ℚ) ^ (-(nuF e L Λ f)) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
          ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
        congr 1
        unfold nuF
        rw [hsym, sum_neg_distrib]
        push_cast
        ring

end Q
end Chi2Irr
