/-
# ℓ-adic toolkit

* `Zl ℓ`: the ℓ-integral rationals `{x : ℚ | ‖x‖_ℓ ≤ 1}` as a subring of `ℚ`;
* `red ℓ : ℚ → ZMod ℓ`: reduction mod `ℓ` (a ring hom on `Zl ℓ`, via `ℤ_[ℓ]` and `PadicInt.toZMod`; `0` off `Zl ℓ`);
* `red_det`: reduction commutes with determinants of ℓ-integral matrices;
* discreteness `‖x‖ < 1 → ‖x‖ ≤ ℓ⁻¹`, norms of powers of `ℓ`;
* `ZlPoly ℓ p`: polynomials with ℓ-integral coefficients (closed under the usual operations, divided differences).
Norms are `padicNorm ℓ : ℚ → ℚ`.
-/
import Mathlib

namespace Chi2Irr

open Polynomial

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- The ℓ-integral rationals. -/
def Zl : Subring ℚ where
  carrier := {x | padicNorm ℓ x ≤ 1}
  mul_mem' {a b} ha hb := by
    change padicNorm ℓ (a * b) ≤ 1
    rw [padicNorm.mul]
    calc padicNorm ℓ a * padicNorm ℓ b ≤ 1 * 1 :=
          mul_le_mul ha hb (padicNorm.nonneg b) zero_le_one
      _ = 1 := one_mul 1
  one_mem' := by simp
  add_mem' {a b} ha hb := le_trans padicNorm.nonarchimedean (max_le ha hb)
  zero_mem' := by simp [padicNorm.zero]
  neg_mem' {a} ha := by simpa [padicNorm.neg] using ha

variable {ℓ}

lemma mem_Zl {x : ℚ} : x ∈ Zl ℓ ↔ padicNorm ℓ x ≤ 1 := Iff.rfl

lemma intCast_mem_Zl (n : ℤ) : (n : ℚ) ∈ Zl ℓ := padicNorm.of_int n

lemma natCast_mem_Zl (n : ℕ) : (n : ℚ) ∈ Zl ℓ := padicNorm.of_nat n

variable (ℓ) in
/-- The inclusion `Zl ℓ → ℤ_[ℓ]`. -/
noncomputable def toZp : Zl ℓ →+* ℤ_[ℓ] where
  toFun x := ⟨((x : ℚ) : ℚ_[ℓ]), by
    rw [PadicInt.mem_subring_iff, Padic.eq_padicNorm]; exact_mod_cast x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; push_cast; rfl
  map_zero' := by ext; simp
  map_add' x y := by ext; push_cast; rfl

variable (ℓ) in
/-- Reduction mod `ℓ` on `Zl ℓ`. -/
noncomputable def redHom : Zl ℓ →+* ZMod ℓ := PadicInt.toZMod.comp (toZp ℓ)

lemma redHom_eq_zero_iff (x : Zl ℓ) : redHom ℓ x = 0 ↔ padicNorm ℓ (x : ℚ) < 1 := by
  unfold redHom
  rw [RingHom.comp_apply, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits, PadicInt.norm_def]
  change ‖((x : ℚ) : ℚ_[ℓ])‖ < 1 ↔ _
  rw [Padic.eq_padicNorm]
  exact_mod_cast Iff.rfl

variable (ℓ) in
open Classical in
/-- Reduction mod `ℓ` of a rational (`0` if it is not ℓ-integral). -/
noncomputable def red (x : ℚ) : ZMod ℓ := if h : x ∈ Zl ℓ then redHom ℓ ⟨x, h⟩ else 0

lemma red_of_mem {x : ℚ} (h : x ∈ Zl ℓ) : red ℓ x = redHom ℓ ⟨x, h⟩ := by
  unfold red
  simp [h]

lemma red_add {x y : ℚ} (hx : x ∈ Zl ℓ) (hy : y ∈ Zl ℓ) : red ℓ (x + y) = red ℓ x + red ℓ y := by
  rw [red_of_mem hx, red_of_mem hy, red_of_mem (add_mem hx hy), ← map_add]
  rfl

lemma red_mul {x y : ℚ} (hx : x ∈ Zl ℓ) (hy : y ∈ Zl ℓ) : red ℓ (x * y) = red ℓ x * red ℓ y := by
  rw [red_of_mem hx, red_of_mem hy, red_of_mem (mul_mem hx hy), ← map_mul]
  rfl

lemma red_neg {x : ℚ} (hx : x ∈ Zl ℓ) : red ℓ (-x) = -red ℓ x := by
  rw [red_of_mem hx, red_of_mem (neg_mem hx), ← map_neg]
  rfl

lemma red_sub {x y : ℚ} (hx : x ∈ Zl ℓ) (hy : y ∈ Zl ℓ) : red ℓ (x - y) = red ℓ x - red ℓ y := by
  rw [sub_eq_add_neg, red_add hx (neg_mem hy), red_neg hy, ← sub_eq_add_neg]

lemma red_intCast (n : ℤ) : red ℓ n = n := by
  rw [red_of_mem (intCast_mem_Zl n)]
  have : (⟨(n : ℚ), intCast_mem_Zl n⟩ : Zl ℓ) = (n : Zl ℓ) := by ext; simp
  rw [this, map_intCast]

lemma red_natCast (n : ℕ) : red ℓ n = n := by
  have := red_intCast (ℓ := ℓ) (n : ℤ)
  simpa using this

lemma red_zero : red ℓ 0 = 0 := by simpa using red_natCast (ℓ := ℓ) 0

lemma red_one : red ℓ 1 = 1 := by simpa using red_natCast (ℓ := ℓ) 1

lemma red_pow {x : ℚ} (hx : x ∈ Zl ℓ) (n : ℕ) : red ℓ (x ^ n) = red ℓ x ^ n := by
  induction n with
  | zero => simp [red_one]
  | succ n ih => rw [pow_succ, red_mul (pow_mem hx n) hx, ih, pow_succ]

lemma red_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, f i ∈ Zl ℓ) :
    red ℓ (∑ i ∈ s, f i) = ∑ i ∈ s, red ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [red_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      red_add (h a (Finset.mem_insert_self a s)) (sum_mem (fun i hi => h i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

lemma red_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, f i ∈ Zl ℓ) :
    red ℓ (∏ i ∈ s, f i) = ∏ i ∈ s, red ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [red_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      red_mul (h a (Finset.mem_insert_self a s)) (prod_mem (fun i hi => h i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

lemma red_eq_zero_iff {x : ℚ} (hx : x ∈ Zl ℓ) : red ℓ x = 0 ↔ padicNorm ℓ x < 1 := by
  rw [red_of_mem hx, redHom_eq_zero_iff]

/-- Discreteness of the ℓ-adic norm on `ℚ`. -/
lemma padicNorm_le_inv_of_lt_one {x : ℚ} (h : padicNorm ℓ x < 1) : padicNorm ℓ x ≤ (ℓ : ℚ)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [padicNorm.zero]
  obtain ⟨z, hz⟩ := padicNorm.values_discrete (p := ℓ) hx
  have hℓ1 : (1 : ℚ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  rw [hz] at h ⊢
  have hz1 : -z < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    have : (1 : ℚ) ≤ (ℓ : ℚ) ^ (-z) := one_le_zpow₀ hℓ1.le hcon
    linarith
  calc (ℓ : ℚ) ^ (-z) ≤ (ℓ : ℚ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hℓ1.le (by omega)
    _ = (ℓ : ℚ)⁻¹ := zpow_neg_one _

lemma red_eq_zero_iff' {x : ℚ} (hx : x ∈ Zl ℓ) : red ℓ x = 0 ↔ padicNorm ℓ x ≤ (ℓ : ℚ)⁻¹ := by
  rw [red_eq_zero_iff hx]
  constructor
  · exact padicNorm_le_inv_of_lt_one
  · intro h
    have : (ℓ : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt)
    linarith

lemma red_eq_of_sub {x y : ℚ} (hx : x ∈ Zl ℓ) (hy : y ∈ Zl ℓ) (h : padicNorm ℓ (x - y) < 1) :
    red ℓ x = red ℓ y := by
  have := (red_eq_zero_iff (sub_mem hx hy)).mpr h
  rw [red_sub hx hy, sub_eq_zero] at this
  exact this

lemma inv_mem_Zl {x : ℚ} (hx : padicNorm ℓ x = 1) : x⁻¹ ∈ Zl ℓ := by
  rw [mem_Zl, ← one_div, padicNorm.div, padicNorm.one, hx]; norm_num

lemma red_inv {x : ℚ} (hx : padicNorm ℓ x = 1) : red ℓ x⁻¹ = (red ℓ x)⁻¹ := by
  have hx0 : x ≠ 0 := by intro h; rw [h, padicNorm.zero] at hx; exact zero_ne_one hx
  have hxm : x ∈ Zl ℓ := le_of_eq hx
  have h1 : red ℓ x * red ℓ x⁻¹ = 1 := by
    rw [← red_mul hxm (inv_mem_Zl hx), mul_inv_cancel₀ hx0, red_one]
  exact (eq_inv_of_mul_eq_one_right h1)

lemma red_div {x y : ℚ} (hx : x ∈ Zl ℓ) (hy : padicNorm ℓ y = 1) :
    red ℓ (x / y) = red ℓ x / red ℓ y := by
  rw [div_eq_mul_inv, red_mul hx (inv_mem_Zl hy), red_inv hy, div_eq_mul_inv]

lemma red_ne_zero_of_norm_one {x : ℚ} (hx : padicNorm ℓ x = 1) : red ℓ x ≠ 0 := by
  rw [Ne, red_eq_zero_iff (le_of_eq hx), hx]
  exact lt_irrefl 1

/-- Reduction commutes with the determinant of an ℓ-integral matrix. -/
lemma red_det {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℚ) (h : ∀ i j, M i j ∈ Zl ℓ) :
    red ℓ M.det = (M.map (red ℓ)).det := by
  set M' : Matrix n n (Zl ℓ) := fun i j => ⟨M i j, h i j⟩
  have hM : M = M'.map (Zl ℓ).subtype := by ext i j; rfl
  have hdet : M.det = ((M'.det : Zl ℓ) : ℚ) := by
    rw [hM]
    exact ((Zl ℓ).subtype.map_det M').symm
  rw [hdet, red_of_mem (M'.det).2, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [red_of_mem (h i j)]

/-! ### Norms of powers of `ℓ` -/

lemma padicNorm_pow (x : ℚ) (n : ℕ) : padicNorm ℓ (x ^ n) = padicNorm ℓ x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma padicNorm_self : padicNorm ℓ (ℓ : ℚ) = (ℓ : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime

lemma padicNorm_ell_pow (n : ℕ) : padicNorm ℓ ((ℓ : ℚ) ^ n) = ((ℓ : ℚ)⁻¹) ^ n := by
  rw [padicNorm_pow, padicNorm_self]

lemma ell_pos : (0 : ℚ) < ℓ := by exact_mod_cast hℓ.out.pos

lemma ell_inv_le_one : (ℓ : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hℓ.out.one_lt.le)

lemma ell_inv_pos : (0 : ℚ) < (ℓ : ℚ)⁻¹ := inv_pos.mpr ell_pos

lemma padicNorm_natCast_eq_one {n : ℕ} (h : ¬ ℓ ∣ n) : padicNorm ℓ (n : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff n).mpr h

lemma padicNorm_intCast_eq_one {n : ℤ} (h : ¬ (ℓ : ℤ) ∣ n) : padicNorm ℓ (n : ℚ) = 1 :=
  (padicNorm.int_eq_one_iff n).mpr h

lemma padicNorm_intCast_le_inv {n : ℤ} (h : (ℓ : ℤ) ∣ n) : padicNorm ℓ (n : ℚ) ≤ (ℓ : ℚ)⁻¹ :=
  padicNorm_le_inv_of_lt_one ((padicNorm.int_lt_one_iff n).mpr h)

/-! ### Polynomials with ℓ-integral coefficients -/

variable (ℓ) in
/-- `p` has ℓ-integral coefficients. -/
def ZlPoly (p : ℚ[X]) : Prop := ∀ n, p.coeff n ∈ Zl ℓ

lemma zlPoly_C {c : ℚ} (hc : c ∈ Zl ℓ) : ZlPoly ℓ (C c) := by
  intro n; rw [coeff_C]; split_ifs <;> simp [hc, zero_mem]

lemma zlPoly_X : ZlPoly ℓ (X : ℚ[X]) := by
  intro n; rw [coeff_X]; split_ifs <;> simp [one_mem, zero_mem]

lemma zlPoly_add {p q : ℚ[X]} (hp : ZlPoly ℓ p) (hq : ZlPoly ℓ q) : ZlPoly ℓ (p + q) := by
  intro n; rw [coeff_add]; exact add_mem (hp n) (hq n)

lemma zlPoly_sub {p q : ℚ[X]} (hp : ZlPoly ℓ p) (hq : ZlPoly ℓ q) : ZlPoly ℓ (p - q) := by
  intro n; rw [coeff_sub]; exact sub_mem (hp n) (hq n)

lemma zlPoly_mul {p q : ℚ[X]} (hp : ZlPoly ℓ p) (hq : ZlPoly ℓ q) : ZlPoly ℓ (p * q) := by
  intro n; rw [coeff_mul]
  exact sum_mem (fun x _ => mul_mem (hp _) (hq _))

lemma zlPoly_one : ZlPoly ℓ (1 : ℚ[X]) := by simpa using zlPoly_C (ℓ := ℓ) (one_mem _)

lemma zlPoly_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, ZlPoly ℓ (f i)) :
    ZlPoly ℓ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zlPoly_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact zlPoly_mul (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma zlPoly_X_sub_C {c : ℚ} (hc : c ∈ Zl ℓ) : ZlPoly ℓ (X - C c) := zlPoly_sub zlPoly_X (zlPoly_C hc)

lemma zlPoly_derivative {p : ℚ[X]} (hp : ZlPoly ℓ p) : ZlPoly ℓ (derivative p) := by
  intro n; rw [coeff_derivative]
  exact mul_mem (hp _) (by exact_mod_cast natCast_mem_Zl (n + 1))

lemma eval_mem_Zl {p : ℚ[X]} (hp : ZlPoly ℓ p) {t : ℚ} (ht : t ∈ Zl ℓ) : p.eval t ∈ Zl ℓ := by
  rw [eval_eq_sum, Polynomial.sum_def]
  exact sum_mem (fun n _ => mul_mem (hp n) (pow_mem ht n))

lemma zlPoly_iff_lifts {p : ℚ[X]} : ZlPoly ℓ p ↔ p ∈ Polynomial.lifts (Zl ℓ).subtype := by
  rw [lifts_iff_coeff_lifts]
  refine forall_congr' (fun n => ?_)
  constructor
  · intro h; exact ⟨⟨_, h⟩, rfl⟩
  · rintro ⟨y, hy⟩; rw [← hy]; exact y.2

/-- Divided differences preserve ℓ-integrality: `(p − p(x))/(X − x)`. -/
lemma zlPoly_divDiff {p : ℚ[X]} (hp : ZlPoly ℓ p) {x : ℚ} (hx : x ∈ Zl ℓ) :
    ZlPoly ℓ ((p - C (p.eval x)) /ₘ (X - C x)) := by
  obtain ⟨p₀, hp₀⟩ := (mem_lifts p).mp (zlPoly_iff_lifts.mp hp)
  set x₀ : Zl ℓ := ⟨x, hx⟩
  have hx' : x = (Zl ℓ).subtype x₀ := rfl
  have hev : p.eval x = (Zl ℓ).subtype (p₀.eval x₀) := by
    rw [hx', ← hp₀, eval_map, eval₂_hom]
  have hmap : (p - C (p.eval x)) /ₘ (X - C x) =
      ((p₀ - C (p₀.eval x₀)) /ₘ (X - C x₀)).map (Zl ℓ).subtype := by
    rw [map_divByMonic _ (monic_X_sub_C x₀), Polynomial.map_sub, Polynomial.map_sub, map_X, map_C,
      map_C, hp₀, ← hev]
    rfl
  rw [hmap, zlPoly_iff_lifts]
  exact ⟨_, rfl⟩

end Chi2Irr
