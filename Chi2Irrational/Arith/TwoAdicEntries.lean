/-
# Lemma 10 (2-adic bound), part 2: the entries in the anchored basis

Anchored basis (`K = h`): `a_i = ∏_{m<i} (X − x_m)`, `b_j = ∏_{K−j ≤ m < K} (X − x_m)`, both monic of degree `i`, `j`.
For `q₀ ∈ {3, 5}` (so `v₂(q₀² − 1) = 3`) and `i, j < K`, both `A(a_i b_j)` and `B(a_i b_j)` have
`v₂ ≥ K − (i+j+1) − (i+j+1−K)₊ − ⌊log₂ K⌋ − 6` (`V2_entry`):
* (L) `π = i + j + 1 − K ≥ 1`: `a_i b_j = D · P`, `B = 0`, `A = μ(P X)` with `P X = 2^{−π} H(2X)`, `H ∈ ℤ[X]`;
  Newton form of `μ` + `b! ∣ Δ^b[x^n](0)` give `v₂(A) ≥ −2π − 2 − ⌊log₂ π⌋`;
* (U) `N = K − 1 − i − j ≥ 0`: the polynomial part is a constant (`μ = 0`), and the pole part is
  `(4/N!) Σ_{l≤N} (−1)^l C(N,l) x_{i+l} T(i+l)` (`T = S` or `q^{2k+1}`), bounded by `V2_U`: `v₂ ≥ N − 1 − ⌊log₂ N⌋`.
-/
import Chi2Irrational.Arith.TwoAdicBasis
import Chi2Irrational.NonVan.Gram

namespace Chi2Irr

open Polynomial Finset fwdDiff
open scoped Nat

/-! ### The anchored basis -/

/-- `a_i = ∏_{m<i} (X − x_m)`. -/
noncomputable def aB (i : ℕ) : ℚ[X] := ∏ m ∈ range i, (X - C (pole m))

/-- `b_j = ∏_{K−j ≤ m < K} (X − x_m)`. -/
noncomputable def bB (K j : ℕ) : ℚ[X] := ∏ m ∈ Ico (K - j) K, (X - C (pole m))

lemma pole_sub_pole' (a b : ℕ) : pole a - pole b = (b : ℚ) - a := by unfold pole; ring

lemma pole_eq_odd (m : ℕ) : pole m = -(((2 * m + 1 : ℕ) : ℚ) / 2) := by unfold pole; push_cast; ring

lemma eval_prod_pole (s : Finset ℕ) (k : ℕ) :
    (∏ m ∈ s, (X - C (pole m))).eval (pole k) = ∏ m ∈ s, (pole k - pole m) := by
  rw [eval_prod]; simp only [eval_sub, eval_X, eval_C]

lemma eval_prod_pole_eq_zero {s : Finset ℕ} {k : ℕ} (hk : k ∈ s) :
    (∏ m ∈ s, (X - C (pole m))).eval (pole k) = 0 := by
  rw [eval_prod_pole]; exact prod_eq_zero hk (sub_self _)

/-! ### Case (L): `i + j ≥ K` -/

lemma aB_mul_bB_L {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    aB i * bB K j = Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m)) := by
  unfold aB bB Dpoly
  rw [← prod_range_mul_prod_Ico _ (show K - j ≤ i by omega),
    ← prod_range_mul_prod_Ico _ (show K - j ≤ K by omega)]
  ring

lemma Afun_L {q K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    Afun q K (aB i * bB K j) = muPoly (wt q) ((∏ m ∈ Ico (K - j) i, (X - C (pole m))) * X) := by
  unfold Afun
  rw [aB_mul_bB_L hi hj hij, mul_assoc, mul_divByMonic_cancel_left _ (Dpoly_monic K)]
  have : ∑ k ∈ range K, (Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) * omega K k *
      Spart q k = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; ring
  rw [this, mul_zero, add_zero]

lemma Bfun_L {q K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    Bfun q K (aB i * bB K j) = 0 := by
  unfold Bfun
  rw [aB_mul_bB_L hi hj hij]
  have : ∑ k ∈ range K, (Dpoly K * ∏ m ∈ Ico (K - j) i, (X - C (pole m))).eval (pole k) * omega K k *
      (q : ℚ) ^ (2 * k + 1) = 0 := by
    refine sum_eq_zero (fun k hk => ?_)
    rw [eval_mul]
    unfold Dpoly
    rw [eval_prod_pole_eq_zero hk]; ring
  rw [this, mul_zero]

/-! ### `2`-integral scaling: `R(t) = 2^{−n} H(2t)`, `H ∈ ℤ[t]`, `deg H ≤ n` -/

/-- `v₂(R_d) ≥ d − n`, and `R_d = 0` for `d > n`. -/
def IS (n : ℕ) (R : ℚ[X]) : Prop := ∀ d : ℕ, V2 ((d : ℤ) - n) (R.coeff d) ∧ (n < d → R.coeff d = 0)

lemma IS_one : IS 0 (1 : ℚ[X]) := fun d => by
  rw [coeff_one]
  split_ifs with h
  · subst h; exact ⟨by simpa using V2_one, fun h => absurd h (lt_irrefl 0)⟩
  · exact ⟨V2_zero _, fun _ => rfl⟩

lemma IS_X : IS 1 (X : ℚ[X]) := fun d => by
  rw [coeff_X]
  split_ifs with h
  · subst h; exact ⟨by simpa using V2_one, fun h => absurd h (lt_irrefl 1)⟩
  · exact ⟨V2_zero _, fun _ => rfl⟩

lemma IS_lin (m : ℕ) : IS 1 (X - C (pole m)) := fun d => by
  rw [coeff_sub, coeff_X, coeff_C]
  rcases Nat.lt_trichotomy d 1 with h | rfl | h
  · have : d = 0 := by omega
    subst this
    simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, zero_sub]
    refine ⟨?_, fun h => absurd h (by omega)⟩
    rw [pole_eq_odd, neg_neg]
    have := V2_div_of_norm (V2_natCast (2 * m + 1)) padicNorm_two_self
    simpa using this
  · simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, sub_zero]
    exact ⟨by simpa using V2_one, fun h => absurd h (lt_irrefl 1)⟩
  · simp only [show 1 ≠ d by omega, show d ≠ 0 by omega, ↓reduceIte, sub_zero]
    exact ⟨V2_zero _, fun _ => trivial⟩

lemma IS_mul {n m : ℕ} {R S : ℚ[X]} (hR : IS n R) (hS : IS m S) : IS (n + m) (R * S) := fun d => by
  rw [coeff_mul]
  constructor
  · refine V2_sum _ _ (fun x hx => ?_)
    have hx' := mem_antidiagonal.mp hx
    refine V2_mul' (hR x.1).1 (hS x.2).1 ?_
    push_cast; omega
  · intro hd
    refine sum_eq_zero (fun x hx => ?_)
    have hx' := mem_antidiagonal.mp hx
    rcases Nat.lt_or_ge n x.1 with h1 | h1
    · rw [(hR x.1).2 h1, zero_mul]
    · rw [(hS x.2).2 (by omega), mul_zero]

lemma IS_prod (s : Finset ℕ) : IS s.card (∏ m ∈ s, (X - C (pole m))) := by
  induction s using Finset.induction_on with
  | empty => simpa using IS_one
  | insert a s ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha, add_comm]
    exact IS_mul (IS_lin a) ih

/-! ### `μ` at `q₀ ∈ {3, 5}` in Newton form -/

lemma padicNorm_qsq {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) :
    padicNorm 2 ((q₀ : ℚ) ^ 2 - 1) = (2 : ℚ) ^ (-(3 : ℤ)) := by
  rcases hq with rfl | rfl
  · have : ((3 : ℕ) : ℚ) ^ 2 - 1 = ((2 ^ 3 : ℕ) : ℚ) := by norm_num
    rw [this, padicNorm.eq_zpow_of_nonzero (by norm_num), padicValRat.of_nat, padicValNat.prime_pow]
    norm_num
  · have : ((5 : ℕ) : ℚ) ^ 2 - 1 = ((2 ^ 3 * 3 : ℕ) : ℚ) := by norm_num
    rw [this, padicNorm.eq_zpow_of_nonzero (by norm_num), padicValRat.of_nat,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    norm_num

lemma V2_qsq {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) : V2 2 ((q₀ : ℚ) ^ 2 - 1) := by
  unfold V2; rw [padicNorm_qsq hq]
  exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)

lemma V2_Omega {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) (b : ℕ) :
    V2 (-3 * ((b : ℤ) + 1)) (evQ q₀ (OmegaF b)) := by
  have hinv : V2 (-3) (1 / ((q₀ : ℚ) ^ 2 - 1)) := by
    have := V2_div_of_norm V2_one (padicNorm_qsq hq); simpa using this
  unfold OmegaF
  split_ifs with hb
  · subst hb; rw [evQ_E]; simpa using hinv
  · rw [map_mul, map_pow, map_pow, evQ_q, evQ_E]
    refine V2_mul' (V2_pow (V2_natCast q₀) 2) (V2_pow hinv (b + 1)) ?_
    push_cast; ring_nf; omega

lemma two_le_q {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) : 2 ≤ q₀ := by rcases hq with rfl | rfl <;> norm_num

/-- **(L) bound.** If `R = 2^{−n} H(2X)` with `H ∈ ℤ[X]` of degree `≤ n`, `n ≥ 1`, then
`v₂(μ(R)) ≥ −2n − 2 − ⌊log₂ n⌋` at `q₀ ∈ {3, 5}`. -/
theorem V2_muPoly {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) {n : ℕ} {R : ℚ[X]} (hR : IS n R) :
    V2 (-2 * (n : ℤ) - 2 - Nat.log 2 n) (muPoly (wt q₀) R) := by
  unfold muPoly
  rw [sum_over_range _ (fun d => by simp)]
  refine V2_sum _ _ (fun d _ => ?_)
  rcases Nat.lt_or_ge n d with hd | hd
  · rw [(hR d).2 hd, zero_mul]; exact V2_zero _
  rw [← evQ_muMonoF (two_le_q hq), muMonoF, map_sum]
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
  push_cast
  omega

/-- The (L) entry `A`. -/
theorem V2_A_L {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) {K i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) (hij : K ≤ i + j) :
    V2 (-2 * ((i + j + 1 - K : ℕ) : ℤ) - 2 - Nat.log 2 (i + j + 1 - K)) (Afun q₀ K (aB i * bB K j)) := by
  rw [Afun_L hi hj hij]
  have := IS_mul (IS_prod (Ico (K - j) i)) IS_X
  rw [Nat.card_Ico, show i - (K - j) + 1 = i + j + 1 - K by omega] at this
  exact V2_muPoly hq this

/-! ### Case (U): `i + j < K` -/

lemma prod_range_add_one_q (n : ℕ) : ∏ t ∈ range n, ((t : ℚ) + 1) = ((n ! : ℕ) : ℚ) := by
  rw [← prod_range_add_one_eq_factorial]; push_cast; rfl

lemma prod_range_sub_q (l : ℕ) : ∏ t ∈ range l, ((t : ℚ) - l) = (-1) ^ l * ((l ! : ℕ) : ℚ) := by
  have e1 : (-1 : ℚ) ^ l * ((l ! : ℕ) : ℚ) = ∏ t ∈ range l, (-((t : ℚ) + 1)) := by
    rw [← prod_range_add_one_q, show (-1 : ℚ) ^ l = ∏ t ∈ range l, (-1 : ℚ) by simp, ← prod_mul_distrib]
    exact prod_congr rfl (fun t _ => by ring)
  rw [e1, ← prod_range_reflect (fun t => (t : ℚ) - l) l]
  refine prod_congr rfl (fun t ht => ?_)
  have ht' := mem_range.mp ht
  have e : ((l - 1 - t : ℕ) : ℚ) + t + 1 = l := by
    have : l - 1 - t + t + 1 = l := by omega
    exact_mod_cast this
  linarith

lemma prod_pole_erase (i N l : ℕ) (hl : l ≤ N) :
    ∏ m ∈ (Ico i (i + N + 1)).erase (i + l), (pole (i + l) - pole m) =
      (-1) ^ l * ((l ! : ℕ) : ℚ) * (((N - l) ! : ℕ) : ℚ) := by
  have hset : (Ico i (i + N + 1)).erase (i + l) = Ico i (i + l) ∪ Ico (i + l + 1) (i + N + 1) := by
    ext m; simp only [mem_erase, mem_Ico, mem_union]; omega
  have hdisj : Disjoint (Ico i (i + l)) (Ico (i + l + 1) (i + N + 1)) := by
    rw [Finset.disjoint_left]; intro m h1 h2; simp only [mem_Ico] at h1 h2; omega
  rw [hset, prod_union hdisj, prod_Ico_eq_prod_range, prod_Ico_eq_prod_range,
    show i + l - i = l by omega, show i + N + 1 - (i + l + 1) = N - l by omega,
    ← prod_range_sub_q, ← prod_range_add_one_q]
  congr 1
  · refine prod_congr rfl (fun t _ => ?_); rw [pole_sub_pole']; push_cast; ring
  · refine prod_congr rfl (fun t _ => ?_); rw [pole_sub_pole']; push_cast; ring

lemma aB_mul_bB_U {K i j : ℕ} (hij : i + j < K) :
    aB i * bB K j = ∏ m ∈ range i ∪ Ico (K - j) K, (X - C (pole m)) := by
  unfold aB bB
  rw [prod_union]
  rw [Finset.disjoint_left]; intro m h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega

lemma eval_omega_U {K i j k : ℕ} (hij : i + j < K) (hk : k ∈ Ico i (K - j)) :
    (aB i * bB K j).eval (pole k) * omega K k =
      pole k / ∏ m ∈ (Ico i (K - j)).erase k, (pole k - pole m) := by
  have hk' := mem_Ico.mp hk
  set Z := range i ∪ Ico (K - j) K with hZ
  have hset : (range K).erase k = Z ∪ (Ico i (K - j)).erase k := by
    ext m; simp only [hZ, mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint Z ((Ico i (K - j)).erase k) := by
    rw [Finset.disjoint_left]; intro m h1 h2
    simp only [hZ, mem_union, mem_range, mem_Ico, mem_erase] at h1 h2; omega
  have hE : ∏ m ∈ Z, (pole k - pole m) ≠ 0 := prod_ne_zero_iff.mpr (fun m hm => pole_sub_ne_zero (by
    intro e; subst e; simp only [hZ, mem_union, mem_range, mem_Ico] at hm; omega))
  have hP : ∏ m ∈ (Ico i (K - j)).erase k, (pole k - pole m) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun m hm => pole_sub_ne_zero (ne_of_mem_erase hm).symm)
  rw [aB_mul_bB_U hij, ← hZ, eval_prod_pole, omega, dPrime, hset, prod_union hdisj]
  field_simp

lemma eval_U_zero {K i j k : ℕ} (hij : i + j < K) (hk : k < K) (hkW : k ∉ Ico i (K - j)) :
    (aB i * bB K j).eval (pole k) = 0 := by
  rw [aB_mul_bB_U hij]
  refine eval_prod_pole_eq_zero ?_
  simp only [mem_Ico, not_and_or, not_le, not_lt] at hkW
  simp only [mem_union, mem_range, mem_Ico]; omega

lemma sum_U {K i j : ℕ} (hij : i + j < K) (Y : ℕ → ℚ) :
    ∑ k ∈ range K, (aB i * bB K j).eval (pole k) * omega K k * Y k =
      1 / (((K - 1 - i - j) ! : ℕ) : ℚ) *
        ((-1) ^ (K - 1 - i - j) * (Δ_[1])^[K - 1 - i - j] (fun l => pole (i + l) * Y (i + l)) 0) := by
  set N := K - 1 - i - j with hN
  have hsub : Ico i (K - j) ⊆ range K := fun k hk => by
    simp only [mem_Ico] at hk; simp only [mem_range]; omega
  rw [← sum_subset hsub (fun k hk hkW => by rw [eval_U_zero hij (mem_range.mp hk) hkW]; ring)]
  rw [sum_congr rfl (fun k hk => by rw [eval_omega_U hij hk])]
  rw [sum_Ico_eq_sum_range, show K - j - i = N + 1 by omega, show K - j = i + N + 1 by omega,
    ← fd_sum_eq, mul_sum]
  refine sum_congr rfl (fun l hl => ?_)
  have hl' : l ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hl)
  rw [prod_pole_erase i N l hl']
  have hc := Nat.choose_mul_factorial_mul_factorial hl'
  have hc' : ((N.choose l : ℕ) : ℚ) * ((l ! : ℕ) : ℚ) * (((N - l) ! : ℕ) : ℚ) = ((N ! : ℕ) : ℚ) := by
    exact_mod_cast hc
  have h1 : ((l ! : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : (((N - l) ! : ℕ) : ℚ) ≠ 0 := by positivity
  have hs : ((-1 : ℚ) ^ l) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [← hc']
  have h3 : ((-1 : ℚ) ^ l) ≠ 0 := by positivity
  have hC : ((N.choose l : ℕ) : ℚ) ≠ 0 := by have := Nat.choose_pos hl'; positivity
  field_simp
  rw [hs, mul_one]

lemma natDegree_prod_pole (s : Finset ℕ) : (∏ m ∈ s, (X - C (pole m))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ (fun m _ => monic_X_sub_C _)]
  simp

lemma muPoly_U {q K i j : ℕ} (hij : i + j < K) :
    muPoly (wt q) ((aB i * bB K j * X) /ₘ Dpoly K) = 0 := by
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

lemma Afun_U {q K i j : ℕ} (hij : i + j < K) :
    Afun q K (aB i * bB K j) = (-1) ^ (K - 1 - i - j) * (4 / (((K - 1 - i - j) ! : ℕ) : ℚ) *
      (Δ_[1])^[K - 1 - i - j] (fun l => pole (i + l) * Spart q (i + l)) 0) := by
  unfold Afun
  rw [muPoly_U hij, zero_add, sum_U hij (Spart q)]
  ring

lemma Bfun_U {q K i j : ℕ} (hij : i + j < K) :
    Bfun q K (aB i * bB K j) = -((-1) ^ (K - 1 - i - j) * (4 / (((K - 1 - i - j) ! : ℕ) : ℚ) *
      (Δ_[1])^[K - 1 - i - j] (fun l => pole (i + l) * (q : ℚ) ^ (2 * (i + l) + 1)) 0)) := by
  unfold Bfun
  rw [sum_U hij (fun k => (q : ℚ) ^ (2 * k + 1))]
  ring

lemma Spart_succ (q k : ℕ) :
    Spart q (k + 1) = (q : ℚ) ^ 2 * Spart q k + 1 / (2 * ((k + 1 : ℕ) : ℚ) + 1) ^ 2 := by
  unfold Spart
  rw [sum_range_succ, Nat.sub_self, mul_zero, pow_zero, mul_sum]
  congr 1
  refine sum_congr rfl (fun j hj => ?_)
  have hj' := mem_range.mp hj
  rw [show 2 * (k + 1 - j) = 2 + 2 * (k - j) by omega, pow_add]
  ring

lemma V2_Spart (q k : ℕ) : V2 0 (Spart q k) := by
  unfold Spart
  refine V2_sum _ _ (fun j _ => ?_)
  have : (2 * (j : ℚ) + 1) ^ 2 = (((2 * j + 1) ^ 2 : ℕ) : ℚ) := by push_cast; ring
  rw [this]
  have := V2_div_odd (V2_pow (V2_natCast q) (2 * (k - j))) (Odd.pow (odd_two_mul_add_one j) (n := 2))
  simpa using this

lemma pole_add (i l : ℕ) : pole (i + l) = -(((2 * i + 1 : ℕ) : ℚ) / 2) - l := by
  unfold pole; push_cast; ring

theorem V2_A_U {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) {K i j : ℕ} (hij : i + j < K) :
    V2 (((K - 1 - i - j : ℕ) : ℤ) - 1 - Nat.log 2 (K - 1 - i - j)) (Afun q₀ K (aB i * bB K j)) := by
  rw [Afun_U hij]
  have hrec : ∀ l, (fun l => Spart q₀ (i + l)) (l + 1) =
      (q₀ : ℚ) ^ 2 * (fun l => Spart q₀ (i + l)) l + 1 * gS (2 * i + 3) l := by
    intro l
    simp only
    rw [show i + (l + 1) = i + l + 1 by omega, Spart_succ, gS]
    push_cast; ring
  have hodd : Odd (2 * i + 3) := ⟨i + 1, by ring⟩
  have hU := V2_U (V2_qsq hq) V2_one hodd (T := fun l => Spart q₀ (i + l))
    (by simpa using V2_Spart q₀ i) hrec (c := 2 * i + 1) (odd_two_mul_add_one i) (K - 1 - i - j)
  have hF : (fun l => pole (i + l) * Spart q₀ (i + l)) =
      (fun l : ℕ => (-(((2 * i + 1 : ℕ) : ℚ) / 2) - l) * (fun l => Spart q₀ (i + l)) l) := by
    funext l; rw [pole_add]
  rw [hF]
  exact V2_mul' (V2_pow (V2_neg V2_one) _) hU (by simp)

theorem V2_B_U {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) {K i j : ℕ} (hij : i + j < K) :
    V2 (((K - 1 - i - j : ℕ) : ℤ) - 1 - Nat.log 2 (K - 1 - i - j)) (Bfun q₀ K (aB i * bB K j)) := by
  rw [Bfun_U hij]
  have hrec : ∀ l, (fun l => (q₀ : ℚ) ^ (2 * (i + l) + 1)) (l + 1) =
      (q₀ : ℚ) ^ 2 * (fun l => (q₀ : ℚ) ^ (2 * (i + l) + 1)) l + 0 * gS (2 * i + 3) l := by
    intro l
    simp only
    rw [show 2 * (i + (l + 1)) + 1 = 2 + (2 * (i + l) + 1) by ring, pow_add]
    ring
  have hodd : Odd (2 * i + 3) := ⟨i + 1, by ring⟩
  have hU := V2_U (V2_qsq hq) (V2_zero 0) hodd (T := fun l => (q₀ : ℚ) ^ (2 * (i + l) + 1))
    (by simpa using V2_pow (V2_natCast q₀) (2 * i + 1)) hrec (c := 2 * i + 1) (odd_two_mul_add_one i)
    (K - 1 - i - j)
  have hF : (fun l => pole (i + l) * (q₀ : ℚ) ^ (2 * (i + l) + 1)) =
      (fun l : ℕ => (-(((2 * i + 1 : ℕ) : ℚ) / 2) - l) * (fun l => (q₀ : ℚ) ^ (2 * (i + l) + 1)) l) := by
    funext l; rw [pole_add]
  rw [hF]
  exact V2_neg (V2_mul' (V2_pow (V2_neg V2_one) _) hU (by simp))

/-! ### All entries -/

/-- The exponent `K − (i+j+1) − (i+j+1−K)₊ − ⌊log₂ K⌋ − 6`. -/
def eTA (h i j : ℕ) : ℤ := (h : ℤ) - (i + j + 1) - ((i + j + 1 - h : ℕ) : ℤ) - Nat.log 2 h - 6

/-- **Entry bound (Lemma 10).** -/
theorem V2_entry {q₀ : ℕ} (hq : q₀ = 3 ∨ q₀ = 5) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    V2 (eTA h i j) (Afun q₀ h (aB i * bB h j)) ∧ V2 (eTA h i j) (Bfun q₀ h (aB i * bB h j)) := by
  unfold eTA
  rcases Nat.lt_or_ge (i + j) h with hij | hij
  · have hl := log_two_mono (show h - 1 - i - j ≤ h by omega)
    have e : ((h - 1 - i - j : ℕ) : ℤ) = (h : ℤ) - 1 - i - j := by omega
    have e2 : i + j + 1 - h = 0 := by omega
    refine ⟨V2_mono ?_ (V2_A_U hq hij), V2_mono ?_ (V2_B_U hq hij)⟩ <;>
    · rw [e, e2]; push_cast; omega
  · have hl := log_two_mono (show i + j + 1 - h ≤ h by omega)
    refine ⟨V2_mono ?_ (V2_A_L hq hi.le hj.le hij), ?_⟩
    · have e : ((i + j + 1 - h : ℕ) : ℤ) = (i : ℤ) + j + 1 - h := by omega
      rw [e]; omega
    · rw [Bfun_L hi.le hj.le hij]; exact V2_zero _

end Chi2Irr
