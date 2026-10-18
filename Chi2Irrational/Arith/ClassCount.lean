/-
# Arithmetic part: the one-level class count `classBd K d ≤ K φ₁(d/K)`

For odd `d` with `2K ≤ 5d` and `d < 2K` the class bound `classBd K d` (atoms `m < K` in classes mod `d`,
contribution `(2 r_m + 1 + M_m − n_m)₊`) is at most `K φ₁(d/K)`; for `d ≥ 2K` it vanishes.

Proof: with `d = 2κ + 1`, weights are `0` below `κ`, `≤ 1` at `κ`, `≤ 2` everywhere. Each atom's contribution
is bounded by an explicit constant on consecutive intervals of `[0, K)` (`cbTerm_le`), and the interval sums are
added up (`sum_Ico_le`). Four regions:
* (I)   `2K < 5d`, `2d ≤ K`:  breakpoints `0, κ+1, d, K−d, 2d, K`, bounds `0,1,2,3,4`; total `≤ 3K − 5d/2 − 1/2`;
* (II)  `K < 2d`, `3d ≤ 2K`:  breakpoints `0, κ+1, K−d, d, K`, bounds `0,1,2,3`;     total `≤ 2K − d/2 − 1/2`;
* (III) `2K < 3d`, `d ≤ K`:   breakpoints `0, κ, κ+1, d, K`, bounds `0,1,2,3`;       total `≤ 3K − 2d` (tight);
* (IV)  `K < d < 2K`:         breakpoints `0, κ, κ+1, K`, bounds `0,1,2`;            total `≤ 2K − d` (tight).

-/
import Chi2Irrational.Arith.Defs

namespace Chi2Irr

/-- The summand of `classBd`. -/
def cbTerm (K d m : ℕ) : ℕ := 2 * (m / d) + 1 + wMax d m - clSize K d m

lemma classBd_eq_sum (K d : ℕ) : classBd K d = ∑ m ∈ Finset.Ico 0 K, cbTerm K d m := by
  rw [← Finset.range_eq_Ico]; rfl

lemma wAtom_le_two (d k : ℕ) : wAtom d k ≤ 2 := by
  unfold wAtom; split_ifs <;> omega

lemma wAtom_eq_zero {d k : ℕ} (h : 2 * k + 1 < d) : wAtom d k = 0 := by
  unfold wAtom; rw [ite_eq_right (by omega), Nat.zero_sub]

lemma wAtom_le_one {d k : ℕ} (h : 2 * k + 1 ≤ d) : wAtom d k ≤ 1 := by
  unfold wAtom
  split_ifs with h1 h2
  · omega
  · exact absurd (show d ∣ 2 * k + 1 by rw [show 2 * k + 1 = d by omega]) h2
  · omega
  · omega

lemma wMax_le_two (d m : ℕ) : wMax d m ≤ 2 :=
  Finset.sup_le (fun _ _ => wAtom_le_two _ _)

lemma wMax_le_of_lt {d m B : ℕ} (hm : m < d) (h : wAtom d m ≤ B) : wMax d m ≤ B := by
  unfold wMax
  rw [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
  simpa using h

/-- Pointwise bound: if `m` has rank `r` (`r d ≤ m < r d + d`), its class has at least `t + 1` members, and the
running maximum weight is `≤ B`, then the contribution is `≤ 2r + 1 + B − (t+1)`. -/
lemma cbTerm_le {K d m r t B v : ℕ} (hd : 0 < d) (h1 : r * d ≤ m) (h2 : m < r * d + d)
    (hn : t * d + (m - r * d) + 1 ≤ K) (hB : wMax d m ≤ B) (hv : 2 * r + 1 + B ≤ v + (t + 1)) :
    cbTerm K d m ≤ v := by
  have hlo : r ≤ m / d := (Nat.le_div_iff_mul_le hd).2 h1
  have hhi : m / d < r + 1 := (Nat.div_lt_iff_lt_mul hd).2 (by rw [Nat.add_mul]; omega)
  have hdiv : m / d = r := by omega
  have hmod : m % d + r * d = m := by
    have := Nat.mod_add_div m d
    rw [hdiv, mul_comm] at this; exact this
  have ht : t ≤ (K - 1 - m % d) / d := (Nat.le_div_iff_mul_le hd).2 (by omega)
  have hc : t + 1 ≤ clSize K d m := by unfold clSize; omega
  unfold cbTerm; rw [hdiv]; omega

/-- Sum of a function bounded by `c` on `[a, b)`. -/
lemma sum_Ico_le (f : ℕ → ℕ) (a b c : ℕ) (h : ∀ m, a ≤ m → m < b → f m ≤ c) :
    ∑ m ∈ Finset.Ico a b, f m ≤ c * (b - a) := by
  calc ∑ m ∈ Finset.Ico a b, f m ≤ ∑ _m ∈ Finset.Ico a b, c :=
        Finset.sum_le_sum (fun m hm => by rw [Finset.mem_Ico] at hm; exact h m hm.1 hm.2)
    _ = c * (b - a) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_comm]

/-- **Vanishing** for `d ≥ 2K`: every atom has weight `0` and is alone in its class. -/
theorem classBd_eq_zero {K d : ℕ} (h : 2 * K ≤ d) : classBd K d = 0 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [classBd]
  rw [classBd_eq_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_Ico] at hm
  exact Nat.le_zero.1 (cbTerm_le (r := 0) (t := 0) (B := 0) (v := 0) (by omega) (by omega)
    (by omega) (by omega) (wMax_le_of_lt (by omega) (le_of_eq (wAtom_eq_zero (by omega)))) (by omega))

/-- Region (I): `2K < 5d`, `2d ≤ K`. -/
lemma classBd_regionI {K d κ : ℕ} (hκ : d = 2 * κ + 1) (h1 : 2 * K < 5 * d) (h2 : 2 * d ≤ K) :
    2 * classBd K d + 5 * d + 1 ≤ 6 * K := by
  have hd : 0 < d := by omega
  rw [classBd_eq_sum, ← Finset.sum_Ico_consecutive (cbTerm K d) (Nat.zero_le (κ + 1))
      (show κ + 1 ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show κ + 1 ≤ d by omega) (show d ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show d ≤ K - d by omega) (show K - d ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show K - d ≤ 2 * d by omega) (show 2 * d ≤ K by omega)]
  have pA := sum_Ico_le (cbTerm K d) 0 (κ + 1) 0 (fun m _ hb => cbTerm_le (r := 0) (t := 1) hd
    (by omega) (by omega) (by omega) (wMax_le_of_lt (by omega) (wAtom_le_one (by omega))) (by omega))
  have pB := sum_Ico_le (cbTerm K d) (κ + 1) d 1 (fun m _ hb => cbTerm_le (r := 0) (t := 1) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  have pC := sum_Ico_le (cbTerm K d) d (K - d) 2 (fun m ha hb => cbTerm_le (r := 1) (t := 2) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  have pD := sum_Ico_le (cbTerm K d) (K - d) (2 * d) 3 (fun m ha hb => cbTerm_le (r := 1) (t := 1) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  have pE := sum_Ico_le (cbTerm K d) (2 * d) K 4 (fun m ha hb => cbTerm_le (r := 2) (t := 2) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  omega

/-- Region (II): `K < 2d`, `3d ≤ 2K`. -/
lemma classBd_regionII {K d κ : ℕ} (hκ : d = 2 * κ + 1) (h1 : K < 2 * d) (h2 : 3 * d ≤ 2 * K) :
    2 * classBd K d + d + 1 ≤ 4 * K := by
  have hd : 0 < d := by omega
  rw [classBd_eq_sum, ← Finset.sum_Ico_consecutive (cbTerm K d) (Nat.zero_le (κ + 1))
      (show κ + 1 ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show κ + 1 ≤ K - d by omega) (show K - d ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show K - d ≤ d by omega) (show d ≤ K by omega)]
  have pA := sum_Ico_le (cbTerm K d) 0 (κ + 1) 0 (fun m _ hb => cbTerm_le (r := 0) (t := 1) hd
    (by omega) (by omega) (by omega) (wMax_le_of_lt (by omega) (wAtom_le_one (by omega))) (by omega))
  have pB := sum_Ico_le (cbTerm K d) (κ + 1) (K - d) 1 (fun m _ hb => cbTerm_le (r := 0) (t := 1) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  have pC := sum_Ico_le (cbTerm K d) (K - d) d 2 (fun m _ hb => cbTerm_le (r := 0) (t := 0) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  have pD := sum_Ico_le (cbTerm K d) d K 3 (fun m ha hb => cbTerm_le (r := 1) (t := 1) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  omega

/-- Region (III): `2K < 3d`, `d ≤ K` (tight). -/
lemma classBd_regionIII {K d κ : ℕ} (hκ : d = 2 * κ + 1) (h1 : 2 * K < 3 * d) (h2 : d ≤ K) :
    classBd K d + 2 * d ≤ 3 * K := by
  have hd : 0 < d := by omega
  rw [classBd_eq_sum, ← Finset.sum_Ico_consecutive (cbTerm K d) (Nat.zero_le κ)
      (show κ ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show κ ≤ κ + 1 by omega) (show κ + 1 ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show κ + 1 ≤ d by omega) (show d ≤ K by omega)]
  have pA := sum_Ico_le (cbTerm K d) 0 κ 0 (fun m _ hb => cbTerm_le (r := 0) (t := 0) hd
    (by omega) (by omega) (by omega) (wMax_le_of_lt (by omega) (le_of_eq (wAtom_eq_zero (by omega))))
    (by omega))
  have pB := sum_Ico_le (cbTerm K d) κ (κ + 1) 1 (fun m _ hb => cbTerm_le (r := 0) (t := 0) hd
    (by omega) (by omega) (by omega) (wMax_le_of_lt (by omega) (wAtom_le_one (by omega))) (by omega))
  have pC := sum_Ico_le (cbTerm K d) (κ + 1) d 2 (fun m _ hb => cbTerm_le (r := 0) (t := 0) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  have pD := sum_Ico_le (cbTerm K d) d K 3 (fun m ha hb => cbTerm_le (r := 1) (t := 1) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  omega

/-- Region (IV): `K < d < 2K` (tight). -/
lemma classBd_regionIV {K d κ : ℕ} (hκ : d = 2 * κ + 1) (h1 : K < d) (h2 : d < 2 * K) :
    classBd K d + d ≤ 2 * K := by
  have hd : 0 < d := by omega
  rw [classBd_eq_sum, ← Finset.sum_Ico_consecutive (cbTerm K d) (Nat.zero_le κ)
      (show κ ≤ K by omega),
    ← Finset.sum_Ico_consecutive (cbTerm K d) (show κ ≤ κ + 1 by omega) (show κ + 1 ≤ K by omega)]
  have pA := sum_Ico_le (cbTerm K d) 0 κ 0 (fun m _ hb => cbTerm_le (r := 0) (t := 0) hd
    (by omega) (by omega) (by omega) (wMax_le_of_lt (by omega) (le_of_eq (wAtom_eq_zero (by omega))))
    (by omega))
  have pB := sum_Ico_le (cbTerm K d) κ (κ + 1) 1 (fun m _ hb => cbTerm_le (r := 0) (t := 0) hd
    (by omega) (by omega) (by omega) (wMax_le_of_lt (by omega) (wAtom_le_one (by omega))) (by omega))
  have pC := sum_Ico_le (cbTerm K d) (κ + 1) K 2 (fun m _ hb => cbTerm_le (r := 0) (t := 0) hd
    (by omega) (by omega) (by omega) (wMax_le_two d m) (by omega))
  omega

/-- **The one-level class count** (Lemma 8A): for odd `d` with
`2K/5 ≤ d < 2K`, `classBd K d ≤ K φ₁(d/K)`. -/
theorem classBd_le_phi1 {K d : ℕ} (hK : 13 ≤ K) (hd : Odd d) (h1 : 2 * K ≤ 5 * d) (h2 : d < 2 * K) :
    (classBd K d : ℝ) ≤ K * phi1 ((d : ℝ) / K) := by
  obtain ⟨κ, hκ⟩ := hd
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have e : (K : ℝ) * ((d : ℝ) / K) = d := by field_simp
  have hd5 : (2 : ℝ) * K < 5 * d := by exact_mod_cast (by omega : 2 * K < 5 * d)
  have c1 : ¬ ((d : ℝ) / K ≤ 2 / 5) := by rw [div_le_iff₀ hK0]; intro h; linarith
  rcases le_or_gt (2 * d) K with hA | hA
  · -- region (I)
    have hn : ((2 * classBd K d + 5 * d + 1 : ℕ) : ℝ) ≤ ((6 * K : ℕ) : ℝ) := by
      exact_mod_cast classBd_regionI hκ (by omega) hA
    push_cast at hn
    have hA' : (2 : ℝ) * d ≤ K := by exact_mod_cast hA
    have c2 : (d : ℝ) / K ≤ 1 / 2 := by rw [div_le_iff₀ hK0]; linarith
    rw [phi1, ite_eq_right c1, ite_eq_left c2,
      show (K : ℝ) * (3 - 5 * ((d : ℝ) / K) / 2) = 3 * K - 5 / 2 * (K * ((d : ℝ) / K)) by ring, e]
    linarith
  have hA' : (K : ℝ) < 2 * d := by exact_mod_cast hA
  have c2 : ¬ ((d : ℝ) / K ≤ 1 / 2) := by rw [div_le_iff₀ hK0]; intro h; linarith
  rcases le_or_gt (3 * d) (2 * K) with hB | hB
  · -- region (II)
    have hn : ((2 * classBd K d + d + 1 : ℕ) : ℝ) ≤ ((4 * K : ℕ) : ℝ) := by
      exact_mod_cast classBd_regionII hκ hA hB
    push_cast at hn
    have hB' : (3 : ℝ) * d ≤ 2 * K := by exact_mod_cast hB
    have c3 : (d : ℝ) / K ≤ 2 / 3 := by rw [div_le_iff₀ hK0]; linarith
    rw [phi1, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3,
      show (K : ℝ) * (2 - (d : ℝ) / K / 2) = 2 * K - (K * ((d : ℝ) / K)) / 2 by ring, e]
    linarith
  have hB' : (2 : ℝ) * K < 3 * d := by exact_mod_cast hB
  have c3 : ¬ ((d : ℝ) / K ≤ 2 / 3) := by rw [div_le_iff₀ hK0]; intro h; linarith
  rcases le_or_gt d K with hC | hC
  · -- region (III)
    have hn : ((classBd K d + 2 * d : ℕ) : ℝ) ≤ ((3 * K : ℕ) : ℝ) := by
      exact_mod_cast classBd_regionIII hκ hB hC
    push_cast at hn
    have hC' : (d : ℝ) ≤ K := by exact_mod_cast hC
    have c4 : (d : ℝ) / K ≤ 1 := by rw [div_le_iff₀ hK0]; linarith
    rw [phi1, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_left c4,
      show (K : ℝ) * (3 - 2 * ((d : ℝ) / K)) = 3 * K - 2 * (K * ((d : ℝ) / K)) by ring, e]
    linarith
  · -- region (IV)
    have hn : ((classBd K d + d : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by
      exact_mod_cast classBd_regionIV hκ hC h2
    push_cast at hn
    have hC' : (K : ℝ) < d := by exact_mod_cast hC
    have h2' : (d : ℝ) < 2 * K := by exact_mod_cast h2
    have c4 : ¬ ((d : ℝ) / K ≤ 1) := by rw [div_le_iff₀ hK0]; intro h; linarith
    have c5 : (d : ℝ) / K ≤ 2 := by rw [div_le_iff₀ hK0]; linarith
    rw [phi1, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4, ite_eq_left c5,
      show (K : ℝ) * (2 - (d : ℝ) / K) = 2 * K - K * ((d : ℝ) / K) by ring, e]
    linarith

end Chi2Irr
