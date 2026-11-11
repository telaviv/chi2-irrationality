/-
# Theorem Q4′: nonvanishing at `ζ = q/2` (Lemma P transferred; `pilot_chi2_2q/RESULT.md` §5)

RESULT §5 reads Lemma P (`NonVan/LemmaP.lean`) at the rational point `ζ₀ = q/2`, an `ℓ`-adic unit. Instead of re-running
the ~3000-line ℓ-adic proof with `ζ₀` in place of an integer, we transfer it:
1. `lemmaP_norm`: the proof of `lemmaP` gives more than `Δ_{3ℓ}(a/b) ≠ 0`: the rescaled Gram determinant is an ℓ-adic
   unit, i.e. `‖KP ℓ · Δ_{3ℓ}(a/b; q′)‖_ℓ = 1` with `KP ℓ = ∏α · ∏β · det(C)²` independent of the integer `q′`.
2. `ℓ`-adic continuity: every coefficient of `Δ_h(·; ζ)` is the specialisation of the same element of `ℚ[q, E]`
   (`DeltaF`), Gauss norm `≤ ℓ^{2h·lev}` (Lemma 9). For `q′ = q(ℓ^M + 1)/2` (so `2q′ ≡ q mod ℓ^M`),
   `‖Δ_h(r; q/2) − Δ_h(r; q′)‖_ℓ ≤ ℓ^{2h·lev − M}` for `ℓ`-integral `r`.
3. Lemma P's hypotheses at `q′` reduce mod `ℓ` to conditions at `ζ₀ = q/2`: `ℓ ∤ q(q² − 4)` and `ℓ` divides none of the
   numerators of `2^8 det M(S)`, `2^8 det M(L)`, `2^{10} det M(D)` at `q′` read through `2q′ ≡ q`, which are the
   integers `nS q, nL q, nD q` below (nonzero for `q ≥ 5`; RESULT §5: `B(S,3), B(L,3), B(D,3)` at `ζ₀`).
Taking `M` large, `‖KP · Δ_{3ℓ}(a/b; q/2)‖_ℓ = 1`, so `Δ_{3ℓ}(a/b; q/2) ≠ 0`, for every prime `ℓ` beyond an explicit
bound. Infinitely many such `ℓ` exist, so Lemma E's nonvanishing input holds along `h = 3ℓ`.
-/
import Chi2Irrational.QZ.Arith
import Chi2Irrational.Q.NonVan

namespace Chi2Irr
namespace QZ

open Polynomial Finset Filter

variable {q ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### 1. Lemma P with the exact valuation -/

/-- The `q`-free normaliser of the rescaled Gram determinant at `h = 3ℓ`. -/
noncomputable def KP (ℓ : ℕ) : ℚ :=
  (∏ i : Fin (3 * ℓ), (ℓ : ℚ) ^ 2 / dPrime (3 * ℓ) i) *
    (∏ j : Fin (3 * ℓ), (if (j : ℕ) % ℓ = kap ℓ then (ℓ : ℚ)⁻¹ else 1)) * (Cm (3 * ℓ)).det ^ 2

lemma det_mem_Zl {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℚ) (h : ∀ i j, M i j ∈ Zl ℓ) :
    M.det ∈ Zl ℓ := by
  set M' : Matrix n n (Zl ℓ) := fun i j => ⟨M i j, h i j⟩
  have hM : M = M'.map (Zl ℓ).subtype := by ext i j; rfl
  have hdet : M.det = ((M'.det : Zl ℓ) : ℚ) := by
    rw [hM]
    exact ((Zl ℓ).subtype.map_det M').symm
  rw [hdet]; exact (M'.det).2

/-- **Lemma P, valuation form.** Under the hypotheses of `lemmaP`, `‖KP ℓ · Δ_{3ℓ}(a/b)‖_ℓ = 1`. -/
theorem lemmaP_norm (g : Good q ℓ) (hS : padicNorm ℓ (MS q).det = 1)
    (hL : padicNorm ℓ (ML q).det = 1) (hD : padicNorm ℓ (MD q).det = 1)
    (a : ℤ) {b : ℕ} (_hb : 0 < b) (hℓb : ¬ ℓ ∣ b) :
    padicNorm ℓ (KP ℓ * (Delta q (3 * ℓ)).eval ((a : ℚ) / b)) = 1 := by
  have hℓ2 := g.ne_two
  set r₀ : ℚ := (a : ℚ) / b
  have hr₀ : r₀ ∈ Zl ℓ := by
    simp only [r₀]
    rw [div_eq_mul_inv]
    exact mul_mem (intCast_mem_Zl a) (inv_mem_Zl (padicNorm_natCast_eq_one hℓb))
  set α : Fin (3 * ℓ) → ℚ := fun i => (ℓ : ℚ) ^ 2 / dPrime (3 * ℓ) i
  set β : Fin (3 * ℓ) → ℚ := fun j => if (j : ℕ) % ℓ = kap ℓ then (ℓ : ℚ)⁻¹ else 1
  set N := Matrix.of fun i j : Fin (3 * ℓ) => α i * Gram q (3 * ℓ) r₀ i j * β j
  have hN : ∀ i j : Fin (3 * ℓ), N i j = E0 q ℓ i j +
      r₀ * (nu ℓ i j * Bfun q (3 * ℓ) (fpoly (3 * ℓ) i * fpoly (3 * ℓ) j)) := by
    intro i j
    simp only [N, Matrix.of_apply, α, β, Gram, LamLin_apply, E0]
    have hαβ : (ℓ : ℚ) ^ 2 / dPrime (3 * ℓ) i * (if (j : ℕ) % ℓ = kap ℓ then (ℓ : ℚ)⁻¹ else 1) =
        nu ℓ i j := by
      unfold nu
      split_ifs <;> field_simp [ell_pos.ne']
    rw [← hαβ]
    ring
  have hsmallB : ∀ i j : Fin (3 * ℓ),
      padicNorm ℓ (r₀ * (nu ℓ i j * Bfun q (3 * ℓ) (fpoly (3 * ℓ) i * fpoly (3 * ℓ) j))) ≤ (ℓ : ℚ)⁻¹ :=
    fun i j => pn_mul_le_left hr₀ (nu_Bfun_small g i.isLt)
  have hNmem : ∀ i j, N i j ∈ Zl ℓ := fun i j => by
    rw [hN]; exact add_mem (E0_mem g i.isLt j.isLt) ((hsmallB i j).trans ell_inv_le_one)
  have hNred : N.map (red ℓ) = Ebar q ℓ := by
    ext i j
    simp only [Matrix.map_apply, Ebar]
    refine red_eq_of_sub (hNmem i j) (E0_mem g i.isLt j.isLt) ?_
    rw [hN, add_sub_cancel_left]
    exact lt_of_le_of_lt (hsmallB i j) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt))
  have hred : red ℓ N.det ≠ 0 := by
    rw [red_det N hNmem, hNred]; exact det_Ebar_ne_zero g hS hL hD
  have h1 := padicNorm_eq_one_of_red_ne_zero (det_mem_Zl N hNmem) hred
  have e : N = Matrix.diagonal α * Gram q (3 * ℓ) r₀ * Matrix.diagonal β := by
    ext i j
    simp [N, Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply]
  rw [e, Matrix.det_mul, Matrix.det_mul, det_gram, Matrix.det_diagonal, Matrix.det_diagonal] at h1
  rw [← h1]
  unfold KP
  congr 1
  ring

/-! ### 2. ℓ-adic continuity of the machine in `ζ` -/

lemma padicNorm_pow_sub_pow_le {x y : ℚ} (hx : padicNorm ℓ x ≤ 1) (hy : padicNorm ℓ y ≤ 1) (n : ℕ) :
    padicNorm ℓ (x ^ n - y ^ n) ≤ padicNorm ℓ (x - y) := by
  induction n with
  | zero => simp [padicNorm.nonneg]
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [e]
    refine padicNorm.nonarchimedean.trans (max_le ?_ ?_)
    · rw [padicNorm.mul]
      calc padicNorm ℓ x * padicNorm ℓ (x ^ n - y ^ n) ≤ 1 * padicNorm ℓ (x - y) :=
            mul_le_mul hx ih (padicNorm.nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [padicNorm.mul, padicNorm_pow (ℓ := ℓ)]
      calc padicNorm ℓ (x - y) * padicNorm ℓ y ^ n ≤ padicNorm ℓ (x - y) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (padicNorm.nonneg _) hy) (padicNorm.nonneg _)
        _ = _ := mul_one _

/-- Two ℓ-integral evaluation points that are `δ`-close give `B δ`-close values of a polynomial of Gauss norm `≤ B`. -/
lemma padicNorm_aeval_sub_le {B : ℚ} (hB : 0 ≤ B) {f : FR} (hf : GLe ℓ B f) (v v' : Fin 2 → ℚ)
    (hv : ∀ i, padicNorm ℓ (v i) ≤ 1) (hv' : ∀ i, padicNorm ℓ (v' i) ≤ 1) {δ : ℚ}
    (hδ : ∀ i, padicNorm ℓ (v i - v' i) ≤ δ) :
    padicNorm ℓ (MvPolynomial.aeval v f - MvPolynomial.aeval v' f) ≤ B * δ := by
  have hδ0 : 0 ≤ δ := (padicNorm.nonneg _).trans (hδ 0)
  rw [aeval_eq_sum_support, aeval_eq_sum_support, ← sum_sub_distrib]
  refine padicNorm.sum_le' (fun m _ => ?_) (mul_nonneg hB hδ0)
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [← mul_sub, padicNorm.mul]
  refine mul_le_mul (hf m) ?_ (padicNorm.nonneg _) hB
  have e : v 0 ^ m 0 * v 1 ^ m 1 - v' 0 ^ m 0 * v' 1 ^ m 1 =
      (v 0 ^ m 0 - v' 0 ^ m 0) * v 1 ^ m 1 + v' 0 ^ m 0 * (v 1 ^ m 1 - v' 1 ^ m 1) := by ring
  rw [e]
  refine padicNorm.nonarchimedean.trans (max_le ?_ ?_)
  · rw [padicNorm.mul, padicNorm_pow (ℓ := ℓ)]
    calc padicNorm ℓ (v 0 ^ m 0 - v' 0 ^ m 0) * padicNorm ℓ (v 1) ^ m 1 ≤ δ * 1 :=
          mul_le_mul ((padicNorm_pow_sub_pow_le (hv 0) (hv' 0) _).trans (hδ 0))
            (pow_le_one₀ (padicNorm.nonneg _) (hv 1)) (pow_nonneg (padicNorm.nonneg _) _) hδ0
      _ = δ := mul_one δ
  · rw [padicNorm.mul, padicNorm_pow (ℓ := ℓ)]
    calc padicNorm ℓ (v' 0) ^ m 0 * padicNorm ℓ (v 1 ^ m 1 - v' 1 ^ m 1) ≤ 1 * δ :=
          mul_le_mul (pow_le_one₀ (padicNorm.nonneg _) (hv' 0))
            ((padicNorm_pow_sub_pow_le (hv 1) (hv' 1) _).trans (hδ 1)) (padicNorm.nonneg _) zero_le_one
      _ = δ := one_mul δ

/-- Two polynomials of degree `≤ h` with `B`-close coefficients have `B`-close values at an ℓ-integral point. -/
lemma padicNorm_eval_sub_le {P Q : ℚ[X]} {h : ℕ} (hP : P.natDegree ≤ h) (hQ : Q.natDegree ≤ h) {B : ℚ}
    (hB : 0 ≤ B) (hc : ∀ k, padicNorm ℓ (P.coeff k - Q.coeff k) ≤ B) {r : ℚ} (hr : padicNorm ℓ r ≤ 1) :
    padicNorm ℓ (P.eval r - Q.eval r) ≤ B := by
  have hd : (P - Q).natDegree < h + 1 := Nat.lt_succ_of_le ((natDegree_sub_le _ _).trans (max_le hP hQ))
  rw [← eval_sub, eval_eq_sum_range' hd]
  refine padicNorm.sum_le' (fun k _ => ?_) hB
  rw [padicNorm.mul, padicNorm_pow (ℓ := ℓ), coeff_sub]
  calc padicNorm ℓ (P.coeff k - Q.coeff k) * padicNorm ℓ r ^ k ≤ B * 1 :=
        mul_le_mul (hc k) (pow_le_one₀ (padicNorm.nonneg _) hr) (pow_nonneg (padicNorm.nonneg _) _) hB
    _ = B := mul_one B

/-! ### 3. The integers that must avoid `ℓ` -/

/-- `2^8 · (numerator of det M(S))` read at `2q′ = q`. -/
def nS (q : ℕ) : ℤ := 72 * (q : ℤ) ^ 8 + 32 * (q : ℤ) ^ 6

/-- `2^8 · (numerator of det M(L))` read at `2q′ = q`. -/
def nL (q : ℕ) : ℤ := 129600 * (q : ℤ) ^ 8 - 338400 * (q : ℤ) ^ 6 - 813056 * (q : ℤ) ^ 4 + 463360 * (q : ℤ) ^ 2

/-- `2^{10} · (numerator of det M(D))` read at `2q′ = q`. -/
def nD (q : ℕ) : ℤ := -16200 * (q : ℤ) ^ 10 + 204300 * (q : ℤ) ^ 8 - 456368 * (q : ℤ) ^ 6 - 26880 * (q : ℤ) ^ 4

lemma nS_ne {q : ℕ} (hq : 5 ≤ q) : nS q ≠ 0 := by
  have : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  unfold nS; positivity

lemma nL_ne {q : ℕ} (hq : 5 ≤ q) : nL q ≠ 0 := by
  have h5 : (5 : ℤ) ≤ q := by exact_mod_cast hq
  set y : ℤ := (q : ℤ) ^ 2 with hy
  have hy25 : 25 ≤ y := by rw [hy]; nlinarith
  have e : nL q = y * (129600 * y ^ 3 - 338400 * y ^ 2 - 813056 * y + 463360) := by
    unfold nL; rw [hy]; ring
  rw [e]
  have hpos : 0 < 129600 * y ^ 3 - 338400 * y ^ 2 - 813056 * y + 463360 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ y - 25) (by nlinarith : (0:ℤ) ≤ y ^ 2),
      mul_nonneg (by linarith : (0:ℤ) ≤ y - 25) (by linarith : (0:ℤ) ≤ y)]
  have : 0 < y * (129600 * y ^ 3 - 338400 * y ^ 2 - 813056 * y + 463360) := by positivity
  exact this.ne'

lemma nD_ne {q : ℕ} (hq : 5 ≤ q) : nD q ≠ 0 := by
  have h5 : (5 : ℤ) ≤ q := by exact_mod_cast hq
  set y : ℤ := (q : ℤ) ^ 2 with hy
  have hy25 : 25 ≤ y := by rw [hy]; nlinarith
  have e : nD q = -(y ^ 2 * (16200 * y ^ 3 - 204300 * y ^ 2 + 456368 * y + 26880)) := by
    unfold nD; rw [hy]; ring
  rw [e, neg_ne_zero]
  have hpos : 0 < 16200 * y ^ 3 - 204300 * y ^ 2 + 456368 * y + 26880 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ y - 25) (by nlinarith : (0:ℤ) ≤ y ^ 2)]
  have : 0 < y ^ 2 * (16200 * y ^ 3 - 204300 * y ^ 2 + 456368 * y + 26880) := by positivity
  exact this.ne'

/-- If `ℓ ∣ x − y` then `ℓ ∣ xⁿ − yⁿ`. -/
lemma dvd_pow_sub_pow_of {x y : ℤ} {d : ℤ} (h : d ∣ x - y) (n : ℕ) : d ∣ x ^ n - y ^ n :=
  h.trans (sub_dvd_pow_sub_pow x y n)

omit hℓ in
lemma not_dvd_of_natAbs_lt {n : ℤ} (hn : n ≠ 0) (hlt : n.natAbs < ℓ) : ¬ (ℓ : ℤ) ∣ n := by
  intro hd
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natCast_dvd.mp hd)
  omega

lemma padicNorm_frac_one {n : ℤ} {d : ℕ} (hn : ¬ (ℓ : ℤ) ∣ n) (hd : ¬ ℓ ∣ d) :
    padicNorm ℓ ((n : ℚ) / (d : ℚ)) = 1 := by
  rw [padicNorm.div, padicNorm_intCast_eq_one hn, padicNorm_natCast_eq_one hd, div_one]

/-! ### 4. Assembly -/

/-- **Nonvanishing at `ζ = q/2`** (the exact statement of `nonvan_z`, `QZ/Interface.lean`). -/
theorem nonvan_z_proof (q : ℕ) (hq : 5 ≤ q) (_ho : Odd q) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, (DeltaZ (zq q) h).eval ((a : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N0
  set Lb := N0 + (nS q).natAbs + (nL q).natAbs + (nD q).natAbs + q ^ 2 + b + 2026
  obtain ⟨ℓ, hℓL, hℓp⟩ := Nat.exists_infinite_primes Lb
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hq3 : 3 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq25 : 25 ≤ q ^ 2 := by nlinarith
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓodd : Odd ℓ := hℓp.odd_of_ne_two hℓ2
  have hℓq : ¬ ℓ ∣ q := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hℓq4 : ¬ ℓ ∣ q ^ 2 - 4 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hℓb : ¬ ℓ ∣ b := fun h => by have := Nat.le_of_dvd hb h; omega
  set h := 3 * ℓ with hh
  refine ⟨h, by omega, ?_⟩
  -- the precision `M`
  set e : ℤ := padicValRat ℓ (KP ℓ) with he
  set M : ℕ := 2 * h * lev h ℓ + e.natAbs + 1 with hM
  -- the integer point `q′ = q (ℓ^M + 1)/2`
  obtain ⟨u, hu⟩ : ∃ u : ℕ, ℓ ^ M + 1 = 2 * u := by
    obtain ⟨t, ht⟩ := hℓodd.pow (n := M)
    exact ⟨t + 1, by omega⟩
  set q' : ℕ := q * u with hq'
  have hu1 : 1 ≤ u := by have := Nat.one_le_pow M ℓ hℓp.pos; omega
  have hq'5 : 5 ≤ q' := by rw [hq']; nlinarith
  have h2q' : (2 * q' : ℤ) - q = (q : ℤ) * (ℓ : ℤ) ^ M := by
    rw [hq']; push_cast
    have : ((ℓ ^ M + 1 : ℕ) : ℤ) = ((2 * u : ℕ) : ℤ) := by rw [hu]
    push_cast at this
    linear_combination (q : ℤ) * this.symm
  have h2qQ : (2 * (q' : ℚ) - q) = (q : ℚ) * (ℓ : ℚ) ^ M := by exact_mod_cast h2q'
  have hℓ2q' : (ℓ : ℤ) ∣ (2 * q' : ℤ) - q := by
    rw [h2q']; exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
  -- `Good q′ ℓ`
  have hℓq' : ¬ ℓ ∣ q' := by
    intro hd
    have h1 : (ℓ : ℤ) ∣ (2 * q' : ℤ) := Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hd) _
    have h2 : (ℓ : ℤ) ∣ (q : ℤ) := by
      have := dvd_sub h1 hℓ2q'; simpa using this
    exact hℓq (Int.natCast_dvd_natCast.mp h2)
  have hq'sq : 1 ≤ q' ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hℓq'2 : ¬ ℓ ∣ q' ^ 2 - 1 := by
    intro hd
    have h1 : (ℓ : ℤ) ∣ 4 * ((q' : ℤ) ^ 2 - 1) := by
      refine Dvd.dvd.mul_left ?_ _
      have := Int.natCast_dvd_natCast.mpr hd
      push_cast [hq'sq] at this; exact this
    have h2 : (ℓ : ℤ) ∣ (2 * q' : ℤ) ^ 2 - (q : ℤ) ^ 2 := dvd_pow_sub_pow_of hℓ2q' 2
    have h3 : (ℓ : ℤ) ∣ (q : ℤ) ^ 2 - 4 := by
      have := dvd_sub h2 h1
      have e : (2 * q' : ℤ) ^ 2 - (q : ℤ) ^ 2 - 4 * ((q' : ℤ) ^ 2 - 1) = -((q : ℤ) ^ 2 - 4) := by ring
      rw [e, dvd_neg] at this; exact this
    have h4 : 4 ≤ q ^ 2 := by omega
    have : (ℓ : ℤ) ∣ ((q ^ 2 - 4 : ℕ) : ℤ) := by push_cast [h4]; exact h3
    exact hℓq4 (Int.natCast_dvd_natCast.mp this)
  have g : Good q' ℓ := ⟨by omega, by omega, hℓq', hℓq'2⟩
  -- the block determinants at `q′`
  have hdq : ¬ ℓ ∣ 9 * (q' ^ 2 - 1) := fun hd => by
    rcases (Nat.Prime.dvd_mul hℓp).mp hd with h9 | h9
    · have := Nat.le_of_dvd (by norm_num) h9; omega
    · exact hℓq'2 h9
  have hdL : ¬ ℓ ∣ 2025 * (q' ^ 2 - 1) := fun hd => by
    rcases (Nat.Prime.dvd_mul hℓp).mp hd with h9 | h9
    · have := Nat.le_of_dvd (by norm_num) h9; omega
    · exact hℓq'2 h9
  have hdD : ¬ ℓ ∣ 135 * (q' ^ 2 - 1) ^ 2 := fun hd => by
    rcases (Nat.Prime.dvd_mul hℓp).mp hd with h9 | h9
    · have := Nat.le_of_dvd (by norm_num) h9; omega
    · exact hℓq'2 (hℓp.dvd_of_dvd_pow h9)
  set x : ℤ := 2 * (q' : ℤ) with hx
  set y : ℤ := (q : ℤ) with hy
  have hxy : (ℓ : ℤ) ∣ x - y := hℓ2q'
  have hS : padicNorm ℓ (MS q').det = 1 := by
    rw [Q.det_MS_q (by omega)]
    refine padicNorm_frac_one ?_ hdq
    intro hd
    have h1 : (ℓ : ℤ) ∣ 2 ^ 8 * (72 * (q' : ℤ) ^ 8 + 8 * (q' : ℤ) ^ 6) := Dvd.dvd.mul_left hd _
    have h2 : (ℓ : ℤ) ∣ 72 * (x ^ 8 - y ^ 8) + 32 * (x ^ 6 - y ^ 6) :=
      dvd_add (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 8) _) (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 6) _)
    have h3 : (ℓ : ℤ) ∣ nS q := by
      have := dvd_sub h1 h2
      have e : 2 ^ 8 * (72 * (q' : ℤ) ^ 8 + 8 * (q' : ℤ) ^ 6) - (72 * (x ^ 8 - y ^ 8) + 32 * (x ^ 6 - y ^ 6)) =
          nS q := by rw [hx, hy]; unfold nS; ring
      rwa [e] at this
    exact not_dvd_of_natAbs_lt (nS_ne hq) (by omega) h3
  have hL : padicNorm ℓ (ML q').det = 1 := by
    rw [Q.det_ML_q (by omega)]
    refine padicNorm_frac_one ?_ hdL
    intro hd
    have h1 : (ℓ : ℤ) ∣ 2 ^ 8 * (129600 * (q' : ℤ) ^ 8 - 84600 * (q' : ℤ) ^ 6 - 50816 * (q' : ℤ) ^ 4 +
        7240 * (q' : ℤ) ^ 2) := Dvd.dvd.mul_left hd _
    have h2 : (ℓ : ℤ) ∣ 129600 * (x ^ 8 - y ^ 8) - 338400 * (x ^ 6 - y ^ 6) - 813056 * (x ^ 4 - y ^ 4) +
        463360 * (x ^ 2 - y ^ 2) :=
      dvd_add (dvd_sub (dvd_sub (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 8) _)
        (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 6) _)) (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 4) _))
        (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 2) _)
    have h3 : (ℓ : ℤ) ∣ nL q := by
      have := dvd_sub h1 h2
      have e : 2 ^ 8 * (129600 * (q' : ℤ) ^ 8 - 84600 * (q' : ℤ) ^ 6 - 50816 * (q' : ℤ) ^ 4 +
          7240 * (q' : ℤ) ^ 2) - (129600 * (x ^ 8 - y ^ 8) - 338400 * (x ^ 6 - y ^ 6) -
          813056 * (x ^ 4 - y ^ 4) + 463360 * (x ^ 2 - y ^ 2)) = nL q := by rw [hx, hy]; unfold nL; ring
      rwa [e] at this
    exact not_dvd_of_natAbs_lt (nL_ne hq) (by omega) h3
  have hD : padicNorm ℓ (MD q').det = 1 := by
    rw [Q.det_MD_q (by omega)]
    refine padicNorm_frac_one ?_ hdD
    intro hd
    have h1 : (ℓ : ℤ) ∣ 2 ^ 10 * (-16200 * (q' : ℤ) ^ 10 + 51075 * (q' : ℤ) ^ 8 - 28523 * (q' : ℤ) ^ 6 -
        420 * (q' : ℤ) ^ 4) := Dvd.dvd.mul_left hd _
    have h2 : (ℓ : ℤ) ∣ -16200 * (x ^ 10 - y ^ 10) + 204300 * (x ^ 8 - y ^ 8) - 456368 * (x ^ 6 - y ^ 6) -
        26880 * (x ^ 4 - y ^ 4) :=
      dvd_sub (dvd_sub (dvd_add (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 10) _)
        (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 8) _)) (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 6) _))
        (Dvd.dvd.mul_left (dvd_pow_sub_pow_of hxy 4) _)
    have h3 : (ℓ : ℤ) ∣ nD q := by
      have := dvd_sub h1 h2
      have e : 2 ^ 10 * (-16200 * (q' : ℤ) ^ 10 + 51075 * (q' : ℤ) ^ 8 - 28523 * (q' : ℤ) ^ 6 -
          420 * (q' : ℤ) ^ 4) - (-16200 * (x ^ 10 - y ^ 10) + 204300 * (x ^ 8 - y ^ 8) -
          456368 * (x ^ 6 - y ^ 6) - 26880 * (x ^ 4 - y ^ 4)) = nD q := by rw [hx, hy]; unfold nD; ring
      rwa [e] at this
    exact not_dvd_of_natAbs_lt (nD_ne hq) (by omega) h3
  -- Lemma P at `q′`, valuation form
  have hP := lemmaP_norm g hS hL hD a hb hℓb
  -- closeness of the evaluation points
  set r : ℚ := (a : ℚ) / b
  have hr : padicNorm ℓ r ≤ 1 := by
    simp only [r]; rw [div_eq_mul_inv]
    exact mul_mem (intCast_mem_Zl a) (inv_mem_Zl (padicNorm_natCast_eq_one hℓb))
  have hzq1 := one_lt_zq hq3
  set v : Fin 2 → ℚ := ![zq q, 1 / (zq q ^ 2 - 1)] with hv
  set v' : Fin 2 → ℚ := ![(q' : ℚ), 1 / ((q' : ℚ) ^ 2 - 1)] with hv'
  have hz2 : padicNorm ℓ (zq q ^ 2 - 1) = 1 := by
    rw [padicNorm_zq_sq hℓ2 hq3]; exact padicNorm_natCast_eq_one hℓq4
  have hq'2 : padicNorm ℓ ((q' : ℚ) ^ 2 - 1) = 1 := by
    have : ((q' : ℚ) ^ 2 - 1) = ((q' ^ 2 - 1 : ℕ) : ℚ) := by push_cast [hq'sq]; ring
    rw [this]; exact padicNorm_natCast_eq_one hℓq'2
  have hvi : ∀ i, padicNorm ℓ (v i) ≤ 1 := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simpa [hv, padicNorm_zq hℓ2] using padicNorm.of_nat (p := ℓ) q
    · simp only [hv, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [padicNorm.div, hz2, padicNorm.one, div_one]
  have hvi' : ∀ i, padicNorm ℓ (v' i) ≤ 1 := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simpa [hv'] using padicNorm.of_nat (p := ℓ) q'
    · simp only [hv', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [padicNorm.div, hq'2, padicNorm.one, div_one]
  have hdiff0 : padicNorm ℓ (zq q - q') ≤ (ℓ : ℚ)⁻¹ ^ M := by
    have e : zq q - q' = -((q : ℚ) * (ℓ : ℚ) ^ M) / 2 := by
      unfold zq; linear_combination (-1 / 2 : ℚ) * h2qQ
    rw [e, padicNorm.div, padicNorm_two_odd hℓ2, div_one, padicNorm.neg]
    rw [padicNorm.mul, padicNorm_pow (ℓ := ℓ), padicNorm.padicNorm_p_of_prime]
    calc padicNorm ℓ (q : ℚ) * (ℓ : ℚ)⁻¹ ^ M ≤ 1 * (ℓ : ℚ)⁻¹ ^ M :=
          mul_le_mul_of_nonneg_right (padicNorm.of_nat q) (by positivity)
      _ = _ := one_mul _
  have hδ : ∀ i, padicNorm ℓ (v i - v' i) ≤ (ℓ : ℚ)⁻¹ ^ M := by
    rw [Fin.forall_fin_two]
    refine ⟨by simpa [hv, hv'] using hdiff0, ?_⟩
    simp only [hv, hv', Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hz0 : zq q ^ 2 - 1 ≠ 0 := zsq_sub_one_ne_zero hzq1
    have hq0 : (q' : ℚ) ^ 2 - 1 ≠ 0 := by
      intro h0; rw [h0, padicNorm.zero] at hq'2; exact zero_ne_one hq'2
    have e : 1 / (zq q ^ 2 - 1) - 1 / ((q' : ℚ) ^ 2 - 1) =
        (zq q - q') * (-(zq q + q')) / ((zq q ^ 2 - 1) * ((q' : ℚ) ^ 2 - 1)) := by
      field_simp; ring
    rw [e, padicNorm.div, padicNorm.mul, padicNorm.mul, hz2, hq'2, padicNorm.neg, mul_one, div_one]
    have hs : padicNorm ℓ (zq q + q') ≤ 1 :=
      padicNorm.nonarchimedean.trans (max_le (hvi 0) (hvi' 0))
    calc padicNorm ℓ (zq q - q') * padicNorm ℓ (zq q + q') ≤ (ℓ : ℚ)⁻¹ ^ M * 1 :=
          mul_le_mul hdiff0 hs (padicNorm.nonneg _) (by positivity)
      _ = _ := mul_one _
  -- the coefficient comparison and the values
  set B : ℚ := (ℓ : ℚ) ^ (2 * h * lev h ℓ) with hB
  have hcoef : ∀ k, padicNorm ℓ ((DeltaZ (zq q) h).coeff k - (Delta q' h).coeff k) ≤ B * (ℓ : ℚ)⁻¹ ^ M := by
    intro k
    rw [coeff_DeltaZ_eq hzq1, coeff_Delta_eq (by omega)]
    exact padicNorm_aeval_sub_le (by positivity) (lemma9_DeltaF hℓ2 h k) v v' hvi hvi' hδ
  have hval := padicNorm_eval_sub_le (natDegree_DeltaZ_le (zq q) h) (natDegree_Delta_le q' h)
    (by positivity) hcoef hr
  -- conclusion
  intro h0
  have hK0 : KP ℓ ≠ 0 := by
    intro hk; rw [hk, zero_mul, padicNorm.zero] at hP; exact zero_ne_one hP
  have hKn : padicNorm ℓ (KP ℓ) = (ℓ : ℚ) ^ (-e) := padicNorm.eq_zpow_of_nonzero hK0
  have key : padicNorm ℓ (KP ℓ * (Delta q' h).eval r) ≤ (ℓ : ℚ)⁻¹ := by
    have e1 : KP ℓ * (Delta q' h).eval r = -(KP ℓ * ((DeltaZ (zq q) h).eval r - (Delta q' h).eval r)) := by
      rw [h0]; ring
    rw [e1, padicNorm.neg, padicNorm.mul, hKn]
    have hℓ1 : (1 : ℚ) < ℓ := by exact_mod_cast hℓp.one_lt
    have hℓ0 : (0 : ℚ) < ℓ := by linarith
    calc (ℓ : ℚ) ^ (-e) * padicNorm ℓ ((DeltaZ (zq q) h).eval r - (Delta q' h).eval r)
        ≤ (ℓ : ℚ) ^ (-e) * (B * (ℓ : ℚ)⁻¹ ^ M) := mul_le_mul_of_nonneg_left hval (by positivity)
      _ = (ℓ : ℚ) ^ (-e + ((2 * h * lev h ℓ : ℕ) : ℤ) - (M : ℤ)) := by
          rw [hB, inv_pow, zpow_sub₀ hℓ0.ne', zpow_add₀ hℓ0.ne', zpow_natCast, zpow_natCast]
          ring
      _ ≤ (ℓ : ℚ) ^ (-1 : ℤ) := by
          refine zpow_le_zpow_right₀ hℓ1.le ?_
          have hMz : (M : ℤ) = ((2 * h * lev h ℓ : ℕ) : ℤ) + (e.natAbs : ℤ) + 1 := by
            rw [hM]; push_cast; ring
          have h1 : -e ≤ (e.natAbs : ℤ) := by rw [← Int.natAbs_neg]; exact Int.le_natAbs
          rw [hMz]; linarith
      _ = (ℓ : ℚ)⁻¹ := zpow_neg_one _
  rw [hP] at key
  have hℓ1 : (1 : ℚ) < ℓ := by exact_mod_cast hℓp.one_lt
  have : (ℓ : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hℓ1
  linarith

end QZ
end Chi2Irr
