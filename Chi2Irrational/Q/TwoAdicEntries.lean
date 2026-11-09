/-
# Lemma 10 at general `ν` (RESULT §1, CHI2_IRRATIONALITY §4.3), part 2: the entries in the anchored basis

Generalises `Arith/TwoAdicEntries.lean` from `q₀ ∈ {3, 5}` (where `v₂(q₀² − 1) = 3`) to every odd `q ≥ 3`, with
`ν = nu q = v₂(q² − 1) ≥ 3`. The lemma names are those of the `q₀ ∈ {3, 5}` file (namespace `Chi2Irr.Q`); every
`q`-free lemma of that file (anchored basis, `IS`, `Afun_L`, `Bfun_L`, `Afun_U`, `Bfun_U`, …) is reused.
* (L) `π = i + j + 1 − K ≥ 1`: `v₂(Ω_b) = −ν(b + 1)`, so `v₂(A) ≥ −(ν − 1)π − 2 − ⌊log₂ π⌋`, `B = 0`;
* (U) unchanged: `V2_U` needs only `v₂(q² − 1) ≥ 2`;
* all entries: `v₂ ≥ K − (i+j+1) − (ν − 2)(i+j+1−K)₊ − ⌊log₂ K⌋ − 6` (`V2_entry`).
-/
import Chi2Irrational.Arith.TwoAdicEntries
import Chi2Irrational.Q.Defs

namespace Chi2Irr
namespace Q

open Polynomial Finset

/-- `ν = v₂(q² − 1)`. -/
def nu (q : ℕ) : ℕ := padicValNat 2 (q ^ 2 - 1)

lemma qsq_sub_one_ne_zero {q : ℕ} (hq : 3 ≤ q) : q ^ 2 - 1 ≠ 0 := by
  have : 9 ≤ q ^ 2 := by nlinarith
  omega

lemma eight_dvd_qsq {q : ℕ} (ho : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ := ho
  have e : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  rw [e]
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  rw [ht]
  exact ⟨t, by ring⟩

lemma three_le_nu {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) : 3 ≤ nu q := by
  unfold nu
  have h8 : 2 ^ 3 ∣ q ^ 2 - 1 := by simpa using eight_dvd_qsq ho
  exact (padicValNat_dvd_iff_le (qsq_sub_one_ne_zero hq)).mp h8

lemma cast_qsq {q : ℕ} (hq : 3 ≤ q) : ((q : ℚ) ^ 2 - 1) = ((q ^ 2 - 1 : ℕ) : ℚ) := by
  have : 1 ≤ q ^ 2 := by nlinarith
  push_cast [this]; ring

/-! ### `μ` at odd `q` in Newton form -/

lemma padicNorm_qsq {q : ℕ} (hq : 3 ≤ q) :
    padicNorm 2 ((q : ℚ) ^ 2 - 1) = (2 : ℚ) ^ (-(nu q : ℤ)) := by
  rw [cast_qsq hq, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast qsq_sub_one_ne_zero hq),
    padicValRat.of_nat]
  rfl

lemma V2_qsq {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) : V2 2 ((q : ℚ) ^ 2 - 1) := by
  unfold V2; rw [padicNorm_qsq hq]
  have := three_le_nu hq ho
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

lemma V2_Omega {q : ℕ} (hq : 3 ≤ q) (b : ℕ) :
    V2 (-(nu q : ℤ) * ((b : ℤ) + 1)) (evQ q (OmegaF b)) := by
  have hinv : V2 (-(nu q : ℤ)) (1 / ((q : ℚ) ^ 2 - 1)) := by
    have := V2_div_of_norm V2_one (padicNorm_qsq hq); simpa using this
  unfold OmegaF
  split_ifs with hb
  · subst hb; rw [evQ_E]; simpa using hinv
  · rw [map_mul, map_pow, map_pow, evQ_q, evQ_E]
    refine V2_mul' (V2_pow (V2_natCast q) 2) (V2_pow hinv (b + 1)) ?_
    push_cast; ring_nf; omega

/-- **(L) bound.** If `R = 2^{−n} H(2X)` with `H ∈ ℤ[X]` of degree `≤ n`, then
`v₂(μ(R)) ≥ −(ν − 1)n − 2 − ⌊log₂ n⌋` at odd `q ≥ 3`. -/
theorem V2_muPoly {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {n : ℕ} {R : ℚ[X]} (hR : IS n R) :
    V2 (-((nu q : ℤ) - 1) * n - 2 - Nat.log 2 n) (muPoly (wt q) R) := by
  have hν := three_le_nu hq ho
  unfold muPoly
  rw [sum_over_range _ (fun d => by simp)]
  refine V2_sum _ _ (fun d _ => ?_)
  rcases Nat.lt_or_ge n d with hd | hd
  · rw [(hR d).2 hd, zero_mul]; exact V2_zero _
  rw [← evQ_muMonoF (by omega : 2 ≤ q), muMonoF, map_sum]
  have hR' := (hR d).1
  rw [mul_sum]
  refine V2_sum _ _ (fun b hb => ?_)
  have hb' := mem_range.mp hb
  rw [map_mul, evQ_C]
  have hc : V2 (vf b) ((d : ℚ) * (dCoef (d - 1) b : ℚ)) := by
    have := V2_mul (V2_natCast d) (V2_factorial_dvd (factorial_dvd_dCoef (d - 1) b))
    simpa using this
  refine V2_mul' hR' (V2_mul hc (V2_Omega hq b)) ?_
  have h1 := vf_ge b
  have h2 := log_two_mono (show b ≤ n by omega)
  have p1 : ((nu q : ℤ) - 1) * b ≤ ((nu q : ℤ) - 1) * ((d : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  have p2 : ((nu q : ℤ) - 2) * d ≤ ((nu q : ℤ) - 2) * n :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  have h1' : (b : ℤ) ≤ (vf b : ℤ) + (Nat.log 2 b : ℤ) + 1 := by exact_mod_cast h1
  have h2' : (Nat.log 2 b : ℤ) ≤ (Nat.log 2 n : ℤ) := by exact_mod_cast h2
  nlinarith

/-- The (L) entry `A`. -/
theorem V2_A_L {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    V2 (-((nu q : ℤ) - 1) * ((i + j + 1 - K : ℕ) : ℤ) - 2 - Nat.log 2 (i + j + 1 - K))
      (Afun q K (aB i * bB K j)) := by
  rw [Afun_L hi hj hij]
  have := IS_mul (IS_prod (Ico (K - j) i)) IS_X
  rw [Nat.card_Ico, show i - (K - j) + 1 = i + j + 1 - K by omega] at this
  exact V2_muPoly hq ho this

/-! ### Case (U): `i + j < K` -/

theorem V2_A_U {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {K i j : ℕ} (hij : i + j < K) :
    V2 (((K - 1 - i - j : ℕ) : ℤ) - 1 - Nat.log 2 (K - 1 - i - j)) (Afun q K (aB i * bB K j)) := by
  rw [Afun_U hij]
  have hrec : ∀ l, (fun l => Spart q (i + l)) (l + 1) =
      (q : ℚ) ^ 2 * (fun l => Spart q (i + l)) l + 1 * gS (2 * i + 3) l := by
    intro l
    simp only
    rw [show i + (l + 1) = i + l + 1 by omega, Spart_succ, gS]
    push_cast; ring
  have hodd : Odd (2 * i + 3) := ⟨i + 1, by ring⟩
  have hU := V2_U (V2_qsq hq ho) V2_one hodd (T := fun l => Spart q (i + l))
    (by simpa using V2_Spart q i) hrec (c := 2 * i + 1) (odd_two_mul_add_one i) (K - 1 - i - j)
  have hF : (fun l => pole (i + l) * Spart q (i + l)) =
      (fun l : ℕ => (-(((2 * i + 1 : ℕ) : ℚ) / 2) - l) * (fun l => Spart q (i + l)) l) := by
    funext l; rw [pole_add]
  rw [hF]
  exact V2_mul' (V2_pow (V2_neg V2_one) _) hU (by simp)

theorem V2_B_U {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {K i j : ℕ} (hij : i + j < K) :
    V2 (((K - 1 - i - j : ℕ) : ℤ) - 1 - Nat.log 2 (K - 1 - i - j)) (Bfun q K (aB i * bB K j)) := by
  rw [Bfun_U hij]
  have hrec : ∀ l, (fun l => (q : ℚ) ^ (2 * (i + l) + 1)) (l + 1) =
      (q : ℚ) ^ 2 * (fun l => (q : ℚ) ^ (2 * (i + l) + 1)) l + 0 * gS (2 * i + 3) l := by
    intro l
    simp only
    rw [show 2 * (i + (l + 1)) + 1 = 2 + (2 * (i + l) + 1) by ring, pow_add]
    ring
  have hodd : Odd (2 * i + 3) := ⟨i + 1, by ring⟩
  have hU := V2_U (V2_qsq hq ho) (V2_zero 0) hodd (T := fun l => (q : ℚ) ^ (2 * (i + l) + 1))
    (by simpa using V2_pow (V2_natCast q) (2 * i + 1)) hrec (c := 2 * i + 1) (odd_two_mul_add_one i)
    (K - 1 - i - j)
  have hF : (fun l => pole (i + l) * (q : ℚ) ^ (2 * (i + l) + 1)) =
      (fun l : ℕ => (-(((2 * i + 1 : ℕ) : ℚ) / 2) - l) * (fun l => (q : ℚ) ^ (2 * (i + l) + 1)) l) := by
    funext l; rw [pole_add]
  rw [hF]
  exact V2_neg (V2_mul' (V2_pow (V2_neg V2_one) _) hU (by simp))

/-! ### All entries -/

/-- The exponent `K − (i+j+1) − m (i+j+1−K)₊ − ⌊log₂ K⌋ − 6` (`m = ν − 2`). -/
def eTA (m h i j : ℕ) : ℤ :=
  (h : ℤ) - (i + j + 1) - (m : ℤ) * ((i + j + 1 - h : ℕ) : ℤ) - Nat.log 2 h - 6

/-- **Entry bound (Lemma 10, general `ν`).** -/
theorem V2_entry {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    V2 (eTA (nu q - 2) h i j) (Afun q h (aB i * bB h j)) ∧
      V2 (eTA (nu q - 2) h i j) (Bfun q h (aB i * bB h j)) := by
  have hν := three_le_nu hq ho
  have hm : ((nu q - 2 : ℕ) : ℤ) = (nu q : ℤ) - 2 := by omega
  unfold eTA
  rw [hm]
  rcases Nat.lt_or_ge (i + j) h with hij | hij
  · have hl := log_two_mono (show h - 1 - i - j ≤ h by omega)
    have e : ((h - 1 - i - j : ℕ) : ℤ) = (h : ℤ) - 1 - i - j := by omega
    have e2 : i + j + 1 - h = 0 := by omega
    refine ⟨V2_mono ?_ (V2_A_U hq ho hij), V2_mono ?_ (V2_B_U hq ho hij)⟩ <;>
    · rw [e, e2]; push_cast; omega
  · have hl := log_two_mono (show i + j + 1 - h ≤ h by omega)
    refine ⟨V2_mono ?_ (V2_A_L hq ho hi.le hj.le hij), ?_⟩
    · have e : ((i + j + 1 - h : ℕ) : ℤ) = (i : ℤ) + j + 1 - h := by omega
      rw [e]
      have hl' : (Nat.log 2 (i + j + 1 - h) : ℤ) ≤ (Nat.log 2 h : ℤ) := by exact_mod_cast hl
      nlinarith
    · rw [Bfun_L hi.le hj.le hij]; exact V2_zero _

end Q
end Chi2Irr
