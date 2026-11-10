/-
# Lemma 10_e, step 1: the weighted Gauss valuation `v_e` on `ℚ⟦q⟧[X]`

`v_e(Σ c_{n,j} qⁿ Xʲ) = inf (v₂(c_{n,j}) + e n)` (`pilot_qeven/RESULT.md` §2, step 1). In norm form:
`WLe e B F :⇔ ∀ j n, |[qⁿ Xʲ] F|₂ ≤ B · 2^{e n}` (so `v_e(F) ≥ b ⇔ WLe e 2^{−b} F`), and `WLeP` on `ℚ⟦q⟧`.
Both are closed under `+`, `−`, finite sums, products (ultrametric inequality, `2^{e(n₁+n₂)} = 2^{en₁}2^{en₂}`).
-/
import Mathlib

namespace Chi2Irr
namespace Q

open Finset

/-- `‖f‖_{v_e} ≤ B` on `ℚ⟦q⟧`. -/
def WLeP (e : ℕ) (B : ℚ) (f : PowerSeries ℚ) : Prop :=
  ∀ n, padicNorm 2 (PowerSeries.coeff n f) ≤ B * (2 : ℚ) ^ (e * n)

/-- `‖F‖_{v_e} ≤ B` on `ℚ⟦q⟧[X]`, coefficientwise. -/
def WLe (e : ℕ) (B : ℚ) (F : Polynomial (PowerSeries ℚ)) : Prop := ∀ j, WLeP e B (F.coeff j)

variable {e : ℕ}

lemma WLeP_mono {B B' : ℚ} (h : B ≤ B') {f : PowerSeries ℚ} (hf : WLeP e B f) : WLeP e B' f := fun n =>
  (hf n).trans (mul_le_mul_of_nonneg_right h (by positivity))

lemma WLeP_zero {B : ℚ} (hB : 0 ≤ B) : WLeP e B 0 := fun n => by simp; positivity

lemma WLeP_add {B : ℚ} {f g : PowerSeries ℚ} (hf : WLeP e B f) (hg : WLeP e B g) : WLeP e B (f + g) :=
  fun n => by rw [map_add]; exact padicNorm.nonarchimedean.trans (max_le (hf n) (hg n))

lemma WLeP_neg {B : ℚ} {f : PowerSeries ℚ} (hf : WLeP e B f) : WLeP e B (-f) := fun n => by
  rw [map_neg, padicNorm.neg]; exact hf n

lemma WLeP_sum {ι : Type*} (s : Finset ι) {B : ℚ} (hB : 0 ≤ B) (f : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, WLeP e B (f i)) : WLeP e B (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]
  exact padicNorm.sum_le' (fun i hi => h i hi n) (by positivity)

lemma WLeP_mul {B B' : ℚ} (hB : 0 ≤ B) (hB' : 0 ≤ B') {f g : PowerSeries ℚ} (hf : WLeP e B f)
    (hg : WLeP e B' g) : WLeP e (B * B') (f * g) := fun n => by
  rw [PowerSeries.coeff_mul]
  refine padicNorm.sum_le' (fun x hx => ?_) (by positivity)
  rw [padicNorm.mul]
  have hx' : x.1 + x.2 = n := mem_antidiagonal.mp hx
  calc padicNorm 2 (PowerSeries.coeff x.1 f) * padicNorm 2 (PowerSeries.coeff x.2 g)
      ≤ (B * (2 : ℚ) ^ (e * x.1)) * (B' * (2 : ℚ) ^ (e * x.2)) :=
        mul_le_mul (hf _) (hg _) (padicNorm.nonneg _) (by positivity)
    _ = B * B' * (2 : ℚ) ^ (e * n) := by rw [← hx', mul_add, pow_add]; ring

lemma WLeP_one : WLeP e 1 1 := fun n => by
  rw [PowerSeries.coeff_one]
  split_ifs
  · rw [padicNorm.one, one_mul]; exact one_le_pow₀ (by norm_num)
  · rw [padicNorm.zero]; positivity

lemma WLeP_pow {B : ℚ} (hB : 0 ≤ B) {f : PowerSeries ℚ} (hf : WLeP e B f) (k : ℕ) : WLeP e (B ^ k) (f ^ k) := by
  induction k with
  | zero => simpa using WLeP_one
  | succ k ih => rw [pow_succ, pow_succ]; exact WLeP_mul (by positivity) hB ih hf

/-- `r qᵖ` has `‖·‖_{v_e} = |r|₂ 2^{−ep}`. -/
lemma WLeP_C_mul_X_pow (r : ℚ) (k : ℕ) :
    WLeP e (padicNorm 2 r * ((2 : ℚ) ^ (e * k))⁻¹) (algebraMap ℚ (PowerSeries ℚ) r * PowerSeries.X ^ k) :=
  fun n => by
  rw [PowerSeries.coeff_mul_X_pow', Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_smul,
    PowerSeries.coeff_one, smul_eq_mul]
  split_ifs with h1 h2
  · have : n = k := by omega
    subst this
    rw [mul_one, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  · rw [mul_zero, padicNorm.zero]
    exact mul_nonneg (mul_nonneg (padicNorm.nonneg _) (by positivity)) (by positivity)
  · rw [padicNorm.zero]
    exact mul_nonneg (mul_nonneg (padicNorm.nonneg _) (by positivity)) (by positivity)

lemma WLeP_algebraMap (r : ℚ) : WLeP e (padicNorm 2 r) (algebraMap ℚ (PowerSeries ℚ) r) := by
  have := WLeP_C_mul_X_pow (e := e) r 0
  simpa using this

/-! ### Polynomials over `ℚ⟦q⟧` -/

lemma WLe_mono {B B' : ℚ} (h : B ≤ B') {F : Polynomial (PowerSeries ℚ)} (hF : WLe e B F) : WLe e B' F :=
  fun j => WLeP_mono h (hF j)

lemma WLe_zero {B : ℚ} (hB : 0 ≤ B) : WLe e B 0 := fun j => by simpa using WLeP_zero hB

lemma WLe_add {B : ℚ} {F G : Polynomial (PowerSeries ℚ)} (hF : WLe e B F) (hG : WLe e B G) :
    WLe e B (F + G) := fun j => by rw [Polynomial.coeff_add]; exact WLeP_add (hF j) (hG j)

lemma WLe_neg {B : ℚ} {F : Polynomial (PowerSeries ℚ)} (hF : WLe e B F) : WLe e B (-F) := fun j => by
  rw [Polynomial.coeff_neg]; exact WLeP_neg (hF j)

lemma WLe_sum {ι : Type*} (s : Finset ι) {B : ℚ} (hB : 0 ≤ B) (F : ι → Polynomial (PowerSeries ℚ))
    (h : ∀ i ∈ s, WLe e B (F i)) : WLe e B (∑ i ∈ s, F i) := fun j => by
  rw [Polynomial.finsetSum_coeff]
  exact WLeP_sum s hB _ (fun i hi => h i hi j)

lemma WLe_mul {B B' : ℚ} (hB : 0 ≤ B) (hB' : 0 ≤ B') {F G : Polynomial (PowerSeries ℚ)} (hF : WLe e B F)
    (hG : WLe e B' G) : WLe e (B * B') (F * G) := fun j => by
  rw [Polynomial.coeff_mul]
  exact WLeP_sum _ (by positivity) _ (fun x _ => WLeP_mul hB hB' (hF _) (hG _))

lemma WLe_C {B : ℚ} (hB : 0 ≤ B) {f : PowerSeries ℚ} (hf : WLeP e B f) : WLe e B (Polynomial.C f) := fun j => by
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hf
  · exact WLeP_zero hB

lemma WLe_X : WLe e 1 (Polynomial.X : Polynomial (PowerSeries ℚ)) := fun j => by
  rw [Polynomial.coeff_X]
  split_ifs
  · exact WLeP_one
  · exact WLeP_zero zero_le_one

lemma WLe_one : WLe e 1 (1 : Polynomial (PowerSeries ℚ)) := by
  simpa using WLe_C zero_le_one (WLeP_one (e := e))

lemma WLe_prod {ι : Type*} (s : Finset ι) (B : ι → ℚ) (hB : ∀ i, 0 ≤ B i) (F : ι → Polynomial (PowerSeries ℚ))
    (h : ∀ i ∈ s, WLe e (B i) (F i)) : WLe e (∏ i ∈ s, B i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WLe_one
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact WLe_mul (hB a) (prod_nonneg (fun i _ => hB i)) (h a (mem_insert_self a s))
      (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma WLe_smul {B : ℚ} (r : ℚ) {F : Polynomial (PowerSeries ℚ)} (hF : WLe e B F) :
    WLe e (padicNorm 2 r * B) (algebraMap ℚ (Polynomial (PowerSeries ℚ)) r * F) := fun j n => by
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul, PowerSeries.coeff_smul, smul_eq_mul, padicNorm.mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hF j n) (padicNorm.nonneg _)

end Q
end Chi2Irr
