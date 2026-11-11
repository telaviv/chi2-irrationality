/-
# Lemma 10₁ (RESULT §3, `ν = v₂(q² + 1) = 1` at odd `q`), part 1: the entries in the anchored basis

Copy of `Arith/TwoAdicEntries.lean` and `Q/TwoAdicEntries.lean` for the Ti machine (`AfunT`, `BfunT`, `w = −q⁻²`).
Every machine-free lemma of those files (anchored basis `aB`, `bB`, `IS`, `aB_mul_bB_L`, `sum_U`, `pole_add`, …) and
of `Arith/TwoAdicBasis.lean` (`V2` calculus, `vf`, `fd_seq_formula`, `V2_fd_gS`) is reused by import.
Departures from the χ₂ files, all forced by `ν = 1`:
* (L) `π = i + j + 1 − K ≥ 1`: `μ` in Newton form at `w = −q⁻²` (`muMono_newtonQ`) with `v₂(Ω_b) = −(b + 1)`
  (`V2_OmQT`), so `v₂(A) ≥ −π − 2 − ⌊log₂ π⌋` (RESULT: `≥ −π`); `B = 0`;
* (U) `N = K − 1 − i − j ≥ 0`: `V2_fd_seq` / `V2_U` need `v₂(Q − 1) ≥ 2`; here `Q = −q²`, `v₂(Q − 1) = 1`, and the same
  recursion `Δ^m T(0) = (Q−1)^m T(0) + Σ_k (Q−1)^{m−1−k} Δ^k g(0)` gives `v₂(Δ^m T(0)) ≥ m − 1` (`V2_fd_seq1`), hence
  `v₂ ≥ 0` for the entry `(4/N!) Δ^N[(−c/2 − l) T(l)](0)` (`V2_U1`; RESULT: `≥ 1`);
* all entries: `v₂ ≥ −(i+j+1−K)₊ − ⌊log₂ K⌋ − 2` (`V2_entryT`).
Checked exactly in `scripts/tiq/twoadic_odd_check.py`.
-/
import Chi2Irrational.TiQ.PoleSeries
import Chi2Irrational.Arith.TwoAdicEntries

namespace Chi2Irr
namespace TiQ

open Polynomial Finset fwdDiff
open scoped Nat

/-! ### `ν = v₂(q² + 1) = 1` and `Ω_b` at `w = −q⁻²` -/

lemma padicNorm_qsq_add_one {q : ℕ} (ho : Odd q) :
    padicNorm 2 ((q : ℚ) ^ 2 + 1) = (2 : ℚ) ^ (-(1 : ℤ)) := by
  obtain ⟨m, rfl⟩ := ho
  have e : ((2 * m + 1 : ℕ) : ℚ) ^ 2 + 1 = 2 * ((2 * m * m + 2 * m + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [e, padicNorm.mul, padicNorm_two_self, padicNorm_two_odd ⟨m * m + m, by ring⟩, mul_one]

/-- `v₂(Q − 1) = 1` for `Q = −q²`. -/
lemma V2_qsqT {q : ℕ} (ho : Odd q) : V2 1 (-(q : ℚ) ^ 2 - 1) := by
  unfold V2
  rw [show -(q : ℚ) ^ 2 - 1 = -((q : ℚ) ^ 2 + 1) by ring, padicNorm.neg, padicNorm_qsq_add_one ho]

lemma V2_wT {q : ℕ} (ho : Odd q) : V2 0 (wT q) := by
  unfold wT
  have := V2_div_odd (V2_neg V2_one) (ho.pow (n := 2))
  rw [Nat.cast_pow] at this
  exact this

lemma V2_inv_one_sub_wT {q : ℕ} (ho : Odd q) : V2 (-1) (1 / (1 - wT q)) := by
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast ho.pos.ne'
  have h1 : (q : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  have h1' : 1 + (q : ℚ) ^ 2 ≠ 0 := by positivity
  have e2 : 1 - wT q = ((q : ℚ) ^ 2 + 1) / (q : ℚ) ^ 2 := by
    unfold wT
    field_simp
    ring
  have e : 1 / (1 - wT q) = ((q ^ 2 : ℕ) : ℚ) / ((q : ℚ) ^ 2 + 1) := by
    rw [e2, one_div_div, Nat.cast_pow]
  rw [e]
  have := V2_div_of_norm (k := 1) (V2_natCast (q ^ 2)) (padicNorm_qsq_add_one ho)
  rw [zero_sub] at this
  exact this

/-- `v₂(Ω_b(−q⁻²)) ≥ −(b + 1)` at odd `q`. -/
lemma V2_OmQT {q : ℕ} (ho : Odd q) (b : ℕ) : V2 (-((b : ℤ) + 1)) (OmQ (wT q) b) := by
  unfold OmQ
  split_ifs with hb
  · subst hb
    have := V2_mul (V2_wT ho) (V2_inv_one_sub_wT ho)
    rw [mul_one_div] at this
    simpa using this
  · have := V2_mul (V2_pow (V2_wT ho) b) (V2_pow (V2_inv_one_sub_wT ho) (b + 1))
    rw [one_div_pow, mul_one_div] at this
    convert this using 2
    push_cast; ring

/-- **(L) bound.** If `R = 2^{−n} H(2X)` with `H ∈ ℤ[X]` of degree `≤ n`, then `v₂(μ(R)) ≥ −n − 2 − ⌊log₂ n⌋` at
`w = −q⁻²`, odd `q ≥ 3`. -/
theorem V2_muPolyT {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {n : ℕ} {R : ℚ[X]} (hR : IS n R) :
    V2 (-(n : ℤ) - 2 - Nat.log 2 n) (muPoly (wT q) R) := by
  unfold muPoly
  rw [sum_over_range _ (fun d => by simp)]
  refine V2_sum _ _ (fun d _ => ?_)
  rcases Nat.lt_or_ge n d with hd | hd
  · rw [(hR d).2 hd, zero_mul]; exact V2_zero _
  rw [muMono_newtonQ (abs_wT_lt_one (by omega)), mul_sum]
  refine V2_sum _ _ (fun b hb => ?_)
  have hb' := mem_range.mp hb
  have hc : V2 (vf b) ((d : ℚ) * (dCoef (d - 1) b : ℚ)) := by
    have := V2_mul (V2_natCast d) (V2_factorial_dvd (factorial_dvd_dCoef (d - 1) b))
    simpa using this
  refine V2_mul' (hR d).1 (V2_mul hc (V2_OmQT ho b)) ?_
  have h1 := vf_ge b
  have h2 := log_two_mono (show b ≤ n by omega)
  omega

/-! ### Case (L): `i + j ≥ K` -/

lemma AfunT_L {q K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    AfunT q K (aB i * bB K j) = muPoly (wT q) ((∏ m ∈ Ico (K - j) i, (X - C (pole m))) * X) := by
  unfold AfunT
  rw [aB_mul_bB_L hi hj hij, mul_assoc, mul_divByMonic_cancel_left _ (Dpoly_monic K)]
  have : ∑ k ∈ range K, (Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) * omega K k *
      SpartT q k = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; ring
  rw [this, mul_zero, add_zero]

lemma BfunT_L {q K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    BfunT q K (aB i * bB K j) = 0 := by
  unfold BfunT
  rw [aB_mul_bB_L hi hj hij]
  have : ∑ k ∈ range K, (Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) * omega K k *
      poleW q k = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; ring
  rw [this, mul_zero]

/-- The (L) entry `A`. -/
theorem V2_A_LT {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    V2 (-((i + j + 1 - K : ℕ) : ℤ) - 2 - Nat.log 2 (i + j + 1 - K)) (AfunT q K (aB i * bB K j)) := by
  rw [AfunT_L hi hj hij]
  have := IS_mul (IS_prod (Ico (K - j) i)) IS_X
  rw [Nat.card_Ico, show i - (K - j) + 1 = i + j + 1 - K by omega] at this
  exact V2_muPolyT hq ho this

/-! ### The sequence bound at `ν = 1` -/

/-- If `T(l+1) = Q T(l) + e/(s+2l)²` with `v₂(Q − 1) ≥ 1`, then `v₂(Δ^m T(0)) ≥ m − 1`. -/
theorem V2_fd_seq1 {Q e : ℚ} (hη : V2 1 (Q - 1)) (he : V2 0 e) {s : ℕ} (hs : Odd s) {T : ℕ → ℚ}
    (hT0 : V2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * gS s l) (m : ℕ) :
    V2 ((m : ℤ) - 1) ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine V2_add (V2_mul' (V2_pow hη m) hT0 ?_) ?_
  · omega
  · refine V2_mul' (f := (m : ℤ) - 1) he (V2_sum _ _ (fun k hk => V2_mono ?_
      (V2_mul (V2_pow hη _) (V2_fd_gS hs k)))) (by simp)
    have hk := mem_range.mp hk
    omega

/-- **The (U) entry bound at `ν = 1`.** `v₂((4/N!) Δ^N[(−c/2 − l) T(l)](0)) ≥ 0`. -/
theorem V2_U1 {Q e : ℚ} (hη : V2 1 (Q - 1)) (he : V2 0 e) {s : ℕ} (hs : Odd s) {T : ℕ → ℚ}
    (hT0 : V2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * gS s l) {c : ℕ} (_hc : Odd c) (N : ℕ) :
    V2 0 (4 / (N ! : ℕ) * (Δ_[1])^[N] (fun l : ℕ => (-((c : ℚ) / 2) - l) * T l) 0) := by
  have hQ : V2 0 Q := by
    have := V2_add (V2_mono (by norm_num) hη) V2_one; simpa using this
  have hT1 : V2 0 (T 1) := by
    rw [hrec 0]
    exact V2_add (V2_mul' hQ hT0 (by norm_num)) (V2_mul' he (V2_gS hs 0) (by norm_num))
  have hsplit : (fun l : ℕ => (-((c : ℚ) / 2) - l) * T l) =
      (-((c : ℚ) / 2)) • T + (-1 : ℚ) • (fun l : ℕ => (l : ℚ) * T l) := by
    funext l; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hsplit, fwdDiff_iter_add, fwdDiff_iter_const_smul, fwdDiff_iter_const_smul, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, fd_mul_id_zero, mul_add]
  refine V2_add ?_ ?_
  · have hc2 : V2 (-1) ((c : ℚ) / 2) := by
      have := V2_div_of_norm (V2_natCast c) padicNorm_two_self; simpa using this
    refine V2_mul' (V2_div_factorial V2_four N)
      (V2_mul (V2_neg hc2) (V2_fd_seq1 hη he hs hT0 hrec N)) ?_
    have := vf_le N
    omega
  · cases N with
    | zero => simp only [Nat.cast_zero, zero_mul, mul_zero]; exact V2_zero _
    | succ n =>
      have hrec' : ∀ l, (fun r => T (r + 1)) (l + 1) = Q * (fun r => T (r + 1)) l + e * gS (s + 2) l := by
        intro l; simp only; rw [hrec (l + 1), gS_succ]
      have hb := V2_fd_seq1 hη he (hs.add_even even_two) (T := fun r => T (r + 1)) hT1 hrec' n
      have e1 : (4 : ℚ) / ((n + 1) ! : ℕ) * (-1 * (((n + 1 : ℕ) : ℚ) * (Δ_[1])^[n + 1 - 1] T 1)) =
          -(4 / (n ! : ℕ) * (Δ_[1])^[n] (fun r => T (r + 1)) 0) := by
        rw [show n + 1 - 1 = n by omega, ← fd_shift T n 0 1, zero_add, Nat.factorial_succ]
        push_cast
        field_simp
      rw [e1]
      refine V2_neg (V2_mul' (V2_div_factorial V2_four n) hb ?_)
      have := vf_le n
      omega

/-! ### Case (U): `i + j < K` -/

lemma muPoly_UT (w : ℚ) {K i j : ℕ} (hij : i + j < K) :
    muPoly w ((aB i * bB K j * X) /ₘ Dpoly K) = 0 := by
  have hdeg : ((aB i * bB K j * X) /ₘ Dpoly K).natDegree = 0 := by
    rw [natDegree_divByMonic _ (Dpoly_monic K)]
    have h1 : (aB i * bB K j * X).natDegree ≤ i + j + 1 := by
      refine (natDegree_mul_le).trans ?_
      have := natDegree_mul_le (p := aB i) (q := bB K j)
      unfold aB bB at this ⊢
      rw [natDegree_prod_pole, natDegree_prod_pole, card_range, Nat.card_Ico] at this
      rw [natDegree_X]; omega
    have h2 : (Dpoly K).natDegree = K := by unfold Dpoly; rw [natDegree_prod_pole, card_range]
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, muPoly, sum_C_index (by simp)]
  simp [muMono]

lemma AfunT_U {q K i j : ℕ} (hij : i + j < K) :
    AfunT q K (aB i * bB K j) = (-1) ^ (K - 1 - i - j) * (4 / (((K - 1 - i - j) ! : ℕ) : ℚ) *
      (Δ_[1])^[K - 1 - i - j] (fun l => pole (i + l) * SpartT q (i + l)) 0) := by
  unfold AfunT
  rw [muPoly_UT _ hij, zero_add, sum_U hij (SpartT q)]
  ring

lemma BfunT_U {q K i j : ℕ} (hij : i + j < K) :
    BfunT q K (aB i * bB K j) = -((-1) ^ (K - 1 - i - j) * (4 / (((K - 1 - i - j) ! : ℕ) : ℚ) *
      (Δ_[1])^[K - 1 - i - j] (fun l => pole (i + l) * poleW q (i + l)) 0)) := by
  unfold BfunT
  rw [sum_U hij (poleW q)]
  ring

/-- `S♮_{k+1} = −q² S♮_k + 1/(2k+3)²`. -/
lemma SpartT_succ (q k : ℕ) :
    SpartT q (k + 1) = -(q : ℚ) ^ 2 * SpartT q k + 1 / (2 * ((k + 1 : ℕ) : ℚ) + 1) ^ 2 := by
  unfold SpartT
  rw [sum_range_succ, mul_sum]
  simp only [Nat.sub_self, mul_zero, pow_zero, one_mul]
  congr 1
  refine sum_congr rfl (fun j hj => ?_)
  have hj' := mem_range.mp hj
  rw [show 2 * (k + 1 - j) = 2 + 2 * (k - j) by omega, show k + 1 - j = (k - j) + 1 by omega, pow_add,
    pow_succ]
  ring

lemma V2_SpartT (q k : ℕ) : V2 0 (SpartT q k) := by
  unfold SpartT
  refine V2_sum _ _ (fun j _ => ?_)
  have : (2 * (j : ℚ) + 1) ^ 2 = (((2 * j + 1) ^ 2 : ℕ) : ℚ) := by push_cast; ring
  rw [this]
  have := V2_div_odd (V2_mul (V2_pow (V2_neg V2_one) (k - j)) (V2_pow (V2_natCast q) (2 * (k - j))))
    (Odd.pow (odd_two_mul_add_one j) (n := 2))
  simpa using this

lemma V2_poleW (q k : ℕ) : V2 0 (poleW q k) := by
  unfold poleW
  have := V2_mul (V2_pow (V2_neg V2_one) k) (V2_pow (V2_natCast q) (2 * k + 1))
  simpa using this

theorem V2_A_UT {q : ℕ} (ho : Odd q) {K i j : ℕ} (hij : i + j < K) :
    V2 0 (AfunT q K (aB i * bB K j)) := by
  rw [AfunT_U hij]
  have hrec : ∀ l, (fun l => SpartT q (i + l)) (l + 1) =
      (-(q : ℚ) ^ 2) * (fun l => SpartT q (i + l)) l + 1 * gS (2 * i + 3) l := by
    intro l
    simp only
    rw [show i + (l + 1) = i + l + 1 by omega, SpartT_succ, gS]
    push_cast; ring
  have hodd : Odd (2 * i + 3) := ⟨i + 1, by ring⟩
  have hU := V2_U1 (V2_qsqT ho) V2_one hodd (T := fun l => SpartT q (i + l))
    (by simpa using V2_SpartT q i) hrec (c := 2 * i + 1) (odd_two_mul_add_one i) (K - 1 - i - j)
  have hF : (fun l => pole (i + l) * SpartT q (i + l)) =
      (fun l : ℕ => (-(((2 * i + 1 : ℕ) : ℚ) / 2) - l) * (fun l => SpartT q (i + l)) l) := by
    funext l; rw [pole_add]
  rw [hF]
  exact V2_mul' (V2_pow (V2_neg V2_one) _) hU (by simp)

theorem V2_B_UT {q : ℕ} (ho : Odd q) {K i j : ℕ} (hij : i + j < K) :
    V2 0 (BfunT q K (aB i * bB K j)) := by
  rw [BfunT_U hij]
  have hrec : ∀ l, (fun l => poleW q (i + l)) (l + 1) =
      (-(q : ℚ) ^ 2) * (fun l => poleW q (i + l)) l + 0 * gS (2 * i + 3) l := by
    intro l
    simp only
    unfold poleW
    rw [show i + (l + 1) = i + l + 1 by omega, pow_succ,
      show 2 * (i + l + 1) + 1 = 2 * (i + l) + 1 + 2 by ring, pow_add]
    ring
  have hodd : Odd (2 * i + 3) := ⟨i + 1, by ring⟩
  have hU := V2_U1 (V2_qsqT ho) (V2_zero 0) hodd (T := fun l => poleW q (i + l))
    (by simpa using V2_poleW q i) hrec (c := 2 * i + 1) (odd_two_mul_add_one i) (K - 1 - i - j)
  have hF : (fun l => pole (i + l) * poleW q (i + l)) =
      (fun l : ℕ => (-(((2 * i + 1 : ℕ) : ℚ) / 2) - l) * (fun l => poleW q (i + l)) l) := by
    funext l; rw [pole_add]
  rw [hF]
  exact V2_neg (V2_mul' (V2_pow (V2_neg V2_one) _) hU (by simp))

/-! ### All entries -/

/-- The exponent `−(i+j+1−K)₊ − ⌊log₂ K⌋ − 2`. -/
def eTA1 (h i j : ℕ) : ℤ := -((i + j + 1 - h : ℕ) : ℤ) - Nat.log 2 h - 2

/-- **Entry bound (Lemma 10₁).** -/
theorem V2_entryT {q : ℕ} (hq : 3 ≤ q) (ho : Odd q) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    V2 (eTA1 h i j) (AfunT q h (aB i * bB h j)) ∧ V2 (eTA1 h i j) (BfunT q h (aB i * bB h j)) := by
  unfold eTA1
  rcases Nat.lt_or_ge (i + j) h with hij | hij
  · have e2 : i + j + 1 - h = 0 := by omega
    rw [e2]
    exact ⟨V2_mono (by omega) (V2_A_UT ho hij), V2_mono (by omega) (V2_B_UT ho hij)⟩
  · have hl := log_two_mono (show i + j + 1 - h ≤ h by omega)
    refine ⟨V2_mono ?_ (V2_A_LT hq ho hi.le hj.le hij), ?_⟩
    · have hl' : (Nat.log 2 (i + j + 1 - h) : ℤ) ≤ (Nat.log 2 h : ℤ) := by exact_mod_cast hl
      omega
    · rw [BfunT_L hi.le hj.le hij]; exact V2_zero _

end TiQ
end Chi2Irr
