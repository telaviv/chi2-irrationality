/-
# Lemma M, part 3: bound (B) on `O_{nn′} = Σ_k β_k C(k,n) C(k,n′)` (RESULT §1 step 3 (B))

`β_k = 2(2k+1) q^{2k+1}/(k!(h−1−k)!) = (2q/N!) C(N,k)(2k+1) Q^k` (`N = h − 1`, `Q = q²`), and
`Σ_k β_k C(k,s) = (2q/N!) C(N,s) Q^s [(2s+1)(1+Q)^{N−s} + 2(N−s) Q (1+Q)^{N−s−1}]`. At odd `q`, `v₂(1 + Q) = 1`, so this has
`v₂ ≥ 1 − v₂(N!) + (N − s) ≥ 1 − s`. Expanding `C(k,n) C(k,n′) = Σ_{s ≤ n+n′} c_s C(k,s)` with `c_s ∈ ℤ` (the forward
differences of an integer-valued polynomial of degree `n + n′`) gives `v₂(O_{nn′}) ≥ 1 − n − n′`.
-/
import Chi2Irrational.TiQ.M.Binom

namespace Chi2Irr
namespace TiQ
namespace M

open Polynomial Finset

lemma bB_prod_neg (k : ℕ) : ∏ m ∈ range k, ((m : ℚ) - k) = (-1) ^ k * (k.factorial : ℚ) := by
  rw [← prod_range_reflect (fun m : ℕ => ((m : ℚ) - k)) k]
  have h1 : ∀ j ∈ range k, (((k - 1 - j : ℕ) : ℚ) - k) = (-1) * ((j : ℚ) + 1) := by
    intro j hj
    have := mem_range.mp hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_const, card_range]
  congr 1
  have := Finset.prod_range_add_one_eq_factorial k
  exact_mod_cast this

lemma bB_dPrime_aux (k d : ℕ) :
    dPrime (k + d + 1) k = (-1) ^ k * (k.factorial : ℚ) * (d.factorial : ℚ) := by
  induction d with
  | zero =>
    unfold dPrime
    rw [add_zero, range_add_one, erase_insert (by simp)]
    have : ∀ m ∈ range k, pole k - pole m = (m : ℚ) - k := by
      intro m _; unfold pole; ring
    rw [prod_congr rfl this, bB_prod_neg]; simp
  | succ d ih =>
    unfold dPrime at ih ⊢
    rw [show k + (d + 1) + 1 = (k + d + 1) + 1 by ring, range_add_one,
      erase_insert_of_ne (by omega), prod_insert (by simp), ih]
    have : pole k - pole (k + d + 1) = (d : ℚ) + 1 := by unfold pole; push_cast; ring
    rw [this, Nat.factorial_succ]; push_cast; ring

lemma bB_dPrime (N k : ℕ) (hk : k ≤ N) :
    dPrime (N + 1) k = (-1) ^ k * (k.factorial : ℚ) * ((N - k).factorial : ℚ) := by
  have := bB_dPrime_aux k (N - k)
  rwa [show k + (N - k) + 1 = N + 1 by omega] at this

lemma bB_betaK (q N k : ℕ) (hk : k ≤ N) :
    betaK q (N + 1) k = 2 * (q : ℚ) / (N.factorial : ℚ) *
      ((N.choose k : ℚ) * ((2 * k + 1) * ((q : ℚ) ^ 2) ^ k)) := by
  have hc : (N.choose k : ℚ) * (k.factorial : ℚ) * ((N - k).factorial : ℚ) = (N.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hC : (N.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hk1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have hk2 : ((N - k).factorial : ℚ) ≠ 0 := by positivity
  unfold betaK omega poleW
  rw [bB_dPrime N k hk, ← hc]
  unfold pole
  rcases Nat.even_or_odd k with he | he
  · rw [he.neg_one_pow]; field_simp; ring
  · rw [he.neg_one_pow]; field_simp; ring

lemma bB_S (Q : ℚ) (N s : ℕ) :
    ∑ k ∈ range (N + 1), (N.choose k : ℚ) * (k.choose s : ℚ) * Q ^ k =
      (N.choose s : ℚ) * Q ^ s * (1 + Q) ^ (N - s) := by
  by_cases hs : s ≤ N
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
    rw [show s + d + 1 = s + (d + 1) by ring, sum_range_add]
    rw [sum_eq_zero (fun k hk => by rw [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]; simp),
      zero_add, Nat.add_sub_cancel_left, add_comm 1 Q, add_pow, mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    have := Nat.choose_mul (n := s + d) (k := s + j) (s := s) (by omega)
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at this
    have h' : ((s + d).choose (s + j) : ℚ) * ((s + j).choose s : ℚ) =
        ((s + d).choose s : ℚ) * (d.choose j : ℚ) := by exact_mod_cast this
    rw [one_pow, mul_one, pow_add]
    linear_combination (Q ^ s * Q ^ j) * h'
  · rw [not_le] at hs
    rw [Nat.choose_eq_zero_of_lt hs]
    simp only [Nat.cast_zero, zero_mul]
    apply sum_eq_zero
    intro k hk
    have hk' := mem_range.mp hk
    rw [Nat.choose_eq_zero_of_lt (n := k) (k := s) (by omega)]
    simp

lemma bB_V2_S {q : ℕ} (ho : Odd q) (N s : ℕ) :
    V2 ((N : ℤ) - s) (∑ k ∈ range (N + 1), (N.choose k : ℚ) * (k.choose s : ℚ) * ((q : ℚ) ^ 2) ^ k) := by
  rw [bB_S]
  by_cases hs : s ≤ N
  · have h1 : V2 1 (1 + (q : ℚ) ^ 2) := by
      obtain ⟨m, rfl⟩ := ho
      have : (1 + ((2 * m + 1 : ℕ) : ℚ) ^ 2) = (((2 * (2 * m ^ 2 + 2 * m + 1) : ℤ)) : ℚ) := by
        push_cast; ring
      rw [this]
      exact V2_of_dvd (k := 1) (by simp)
    have hQ : V2 0 (((q : ℚ) ^ 2) ^ s) := by
      have := V2_natCast (q ^ (2 * s))
      push_cast at this
      rwa [← pow_mul]
    refine V2_mul' (V2_mul' (g := 0) (V2_natCast _) hQ (by simp)) (V2_pow h1 (N - s)) ?_
    omega
  · rw [not_le] at hs
    rw [Nat.choose_eq_zero_of_lt hs]
    simp only [Nat.cast_zero, zero_mul]
    exact V2_zero _

lemma bB_kchoose (k s : ℕ) : k * k.choose s = s * k.choose s + (s + 1) * k.choose (s + 1) := by
  have := Nat.choose_succ_right_eq k s
  rcases le_or_gt s k with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left] at this
    rw [mul_comm (s + 1), this]; ring
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma bB_V2_T {q : ℕ} (ho : Odd q) (N s : ℕ) :
    V2 (1 - (s : ℤ)) (∑ k ∈ range (N + 1), betaK q (N + 1) k * (k.choose s : ℚ)) := by
  have hT : ∑ k ∈ range (N + 1), betaK q (N + 1) k * (k.choose s : ℚ) =
      2 * (q : ℚ) / (N.factorial : ℚ) *
        ((2 * (s : ℚ) + 1) *
            ∑ k ∈ range (N + 1), (N.choose k : ℚ) * (k.choose s : ℚ) * ((q : ℚ) ^ 2) ^ k +
          2 * ((s : ℚ) + 1) *
            ∑ k ∈ range (N + 1), (N.choose k : ℚ) * (k.choose (s + 1) : ℚ) * ((q : ℚ) ^ 2) ^ k) := by
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun k hk => ?_)
    rw [bB_betaK q N k (by have := mem_range.mp hk; omega)]
    have h' : (k : ℚ) * (k.choose s : ℚ) = s * (k.choose s : ℚ) + (s + 1) * (k.choose (s + 1) : ℚ) := by
      exact_mod_cast bB_kchoose k s
    linear_combination (2 * (q : ℚ) / (N.factorial : ℚ) * (N.choose k : ℚ) * 2 * ((q : ℚ) ^ 2) ^ k) * h'
  rw [hT]
  have h2 : V2 1 (2 : ℚ) := by simpa using V2_two_pow 1
  have hA : V2 (1 - vf N) (2 * (q : ℚ) / (N.factorial : ℚ)) :=
    V2_div_factorial (V2_mul' h2 (V2_natCast q) (by simp)) N
  have hB1 : V2 0 (2 * (s : ℚ) + 1) := by
    have := V2_natCast (2 * s + 1); push_cast at this; exact this
  have hB2 : V2 1 (2 * ((s : ℚ) + 1)) := by
    have := V2_natCast (s + 1); push_cast at this
    exact V2_mul' h2 this (by simp)
  have hB : V2 ((N : ℤ) - s) ((2 * (s : ℚ) + 1) *
            ∑ k ∈ range (N + 1), (N.choose k : ℚ) * (k.choose s : ℚ) * ((q : ℚ) ^ 2) ^ k +
          2 * ((s : ℚ) + 1) *
            ∑ k ∈ range (N + 1), (N.choose k : ℚ) * (k.choose (s + 1) : ℚ) * ((q : ℚ) ^ 2) ^ k) :=
    V2_add (V2_mul' hB1 (bB_V2_S ho N s) (by simp))
      (V2_mul' hB2 (bB_V2_S ho N (s + 1)) (by push_cast; omega))
  have hv := vf_le N
  exact V2_mul' hA hB (by omega)

lemma bB_main {q : ℕ} (ho : Odd q) (N a b : ℕ) :
    V2 (1 - (a : ℤ) - b)
      (∑ k ∈ range (N + 1), betaK q (N + 1) k * (k.choose a : ℚ) * (k.choose b : ℚ)) := by
  have hnewton : ∀ k ≤ N, (k.choose a : ℚ) * (k.choose b : ℚ) =
      ∑ s ∈ range (N + 1), (k.choose s : ℚ) * (fwdDiff (1 : ℚ))^[s] (Cb a * Cb b).eval 0 := by
    intro k hk
    have := shift_eq_sum_fwdDiff_iter (1 : ℚ) (Cb a * Cb b).eval k 0
    have hk' : (Cb a * Cb b).eval (0 + k • (1 : ℚ)) = (k.choose a : ℚ) * (k.choose b : ℚ) := by
      rw [zero_add, nsmul_eq_mul, mul_one, eval_mul, Cb_eval_nat, Cb_eval_nat]
    rw [hk'] at this
    simp only [nsmul_eq_mul] at this
    rw [this]
    apply sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega)
    intro s _ hs
    rw [mem_range, not_lt] at hs
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hint : ∀ s, V2 0 ((fwdDiff (1 : ℚ))^[s] (Cb a * Cb b).eval 0) := by
    intro s
    rw [fwdDiff_iter_eq_sum_shift]
    apply V2_sum
    intro i _
    simp only [zero_add, nsmul_eq_mul, mul_one, eval_mul, Cb_eval_nat, zsmul_eq_mul]
    convert V2_intCast ((-1) ^ (s - i) * (s.choose i : ℤ) * (i.choose a : ℤ) * (i.choose b : ℤ))
      using 1
    push_cast; ring
  have hd : (Cb a * Cb b).natDegree ≤ a + b := by
    calc _ ≤ (Cb a).natDegree + (Cb b).natDegree := natDegree_mul_le
      _ = a + b := by rw [Cb_natDegree, Cb_natDegree]
  have hvan : ∀ s, a + b < s → (fwdDiff (1 : ℚ))^[s] (Cb a * Cb b).eval 0 = 0 := by
    intro s hs
    exact congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (lt_of_le_of_lt hd hs)) 0
  have h1 : ∑ k ∈ range (N + 1), betaK q (N + 1) k * (k.choose a : ℚ) * (k.choose b : ℚ) =
      ∑ k ∈ range (N + 1), betaK q (N + 1) k *
        ∑ s ∈ range (N + 1), (k.choose s : ℚ) * (fwdDiff (1 : ℚ))^[s] (Cb a * Cb b).eval 0 :=
    sum_congr rfl (fun k hk => by
      rw [mul_assoc, hnewton k (by have := mem_range.mp hk; omega)])
  have h2 : ∑ k ∈ range (N + 1), betaK q (N + 1) k * (k.choose a : ℚ) * (k.choose b : ℚ) =
      ∑ s ∈ range (N + 1), (fwdDiff (1 : ℚ))^[s] (Cb a * Cb b).eval 0 *
        ∑ k ∈ range (N + 1), betaK q (N + 1) k * (k.choose s : ℚ) := by
    rw [h1]
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))
  rw [h2]
  apply V2_sum
  intro s _
  by_cases hab : s ≤ a + b
  · exact V2_mul' (hint s) (bB_V2_T ho N s) (by omega)
  · rw [hvan s (by omega), zero_mul]; exact V2_zero _

/-- **Bound (B).** -/
theorem Om_bound {q : ℕ} (ho : Odd q) (h : ℕ) (n n' : Fin h) :
    padicNorm 2 (Om q h n n') ≤ (2 : ℚ) ^ ((n : ℤ) + n' - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N, h = N + 1 := ⟨h - 1, by have := n.isLt; omega⟩
  have := bB_main ho N n n'
  unfold V2 at this
  simp only [Om]
  calc _ ≤ _ := this
    _ = _ := by congr 1; ring

end M
end TiQ
end Chi2Irr
