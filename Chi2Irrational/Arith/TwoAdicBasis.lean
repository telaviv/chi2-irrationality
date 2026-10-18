/-
# Lemma 10 (2-adic bound), part 1: valuations, factorials, finite differences

* `V2 e x` : `v₂(x) ≥ e` (as `‖x‖₂ ≤ 2^{−e}`), closed under `+`, `·`, sums, powers;
* `vf n = v₂(n!)` with `n − ⌊log₂ n⌋ − 1 ≤ v₂(n!) ≤ n − 1` (`n ≥ 1`);
* forward differences on `ℕ → ℚ`: `fd_succ`, `fd_mul_id` (`Δ^{b+1}(x f)(y) = y Δ^{b+1} f(y) + (b+1) Δ^b f(y+1)`),
  `fd_sum_eq` (alternating binomial sums);
* `b! ∣ dCoef n b` (`factorial_dvd_dCoef`);
* `Δ^m [1/(s+2r)²](0) = (−2)^m m! H_m(s)/P_m(s)` (`fd_gS`), so `v₂ ≥ m + v₂(m!)` for odd `s`;
* `V2_fd_seq`: if `T(l+1) = Q T(l) + e/(s+2l)²` with `v₂(Q − 1) ≥ 2`, then `v₂(Δ^m T(0)) ≥ v₂(m!) + m − 2 − ⌊log₂ m⌋`;
* `V2_U`: the resulting bound `v₂((4/N!) Δ^N[(−c/2 − l) T(l)](0)) ≥ N − 1 − ⌊log₂ N⌋` (the (U) entries).
The S-part is handled through the exact recursion `Δ^{m+1}T = (Q−1) Δ^m T + Δ^m g`.
-/
import Chi2Irrational.Arith.PoleOrder

namespace Chi2Irr

open Polynomial Finset fwdDiff
open scoped Nat

/-! ### `V2 e x` : `v₂(x) ≥ e` -/

/-- `v₂(x) ≥ e`, i.e. `‖x‖₂ ≤ 2^{−e}` (true for `x = 0`). -/
def V2 (e : ℤ) (x : ℚ) : Prop := padicNorm 2 x ≤ (2 : ℚ) ^ (-e)

lemma V2_zero (e : ℤ) : V2 e 0 := by unfold V2; rw [padicNorm.zero]; positivity

lemma V2_mono {e e' : ℤ} (h : e' ≤ e) {x : ℚ} (hx : V2 e x) : V2 e' x :=
  hx.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))

lemma V2_add {e : ℤ} {x y : ℚ} (hx : V2 e x) (hy : V2 e y) : V2 e (x + y) :=
  (padicNorm.nonarchimedean (p := 2)).trans (max_le hx hy)

lemma V2_neg {e : ℤ} {x : ℚ} (hx : V2 e x) : V2 e (-x) := by unfold V2 at *; rwa [padicNorm.neg]

lemma V2_sub {e : ℤ} {x y : ℚ} (hx : V2 e x) (hy : V2 e y) : V2 e (x - y) := by
  rw [sub_eq_add_neg]; exact V2_add hx (V2_neg hy)

lemma V2_sum {ι : Type*} (s : Finset ι) {e : ℤ} (f : ι → ℚ) (h : ∀ i ∈ s, V2 e (f i)) :
    V2 e (∑ i ∈ s, f i) :=
  padicNorm.sum_le' h (by positivity)

lemma V2_mul {e f : ℤ} {x y : ℚ} (hx : V2 e x) (hy : V2 f y) : V2 (e + f) (x * y) := by
  unfold V2 at *
  rw [padicNorm.mul, neg_add, zpow_add₀ two_ne_zero]
  exact mul_le_mul hx hy (padicNorm.nonneg _) (by positivity)

lemma V2_mul' {e f g : ℤ} {x y : ℚ} (hx : V2 e x) (hy : V2 f y) (h : g ≤ e + f) : V2 g (x * y) :=
  V2_mono h (V2_mul hx hy)

lemma V2_one : V2 0 1 := by unfold V2; simp

lemma V2_pow {e : ℤ} {x : ℚ} (hx : V2 e x) (n : ℕ) : V2 (n * e) (x ^ n) := by
  induction n with
  | zero => simpa using V2_one
  | succ n ih =>
    rw [pow_succ]
    have := V2_mul ih hx
    convert this using 1
    push_cast; ring

lemma V2_natCast (n : ℕ) : V2 0 (n : ℚ) := by unfold V2; simpa using padicNorm.of_nat (p := 2) n

lemma V2_intCast (n : ℤ) : V2 0 (n : ℚ) := by unfold V2; simpa using padicNorm.of_int (p := 2) n

lemma V2_of_dvd {k : ℕ} {z : ℤ} (h : (2 : ℤ) ^ k ∣ z) : V2 k (z : ℚ) := by
  unfold V2
  have := (padicNorm.dvd_iff_norm_le (p := 2) (n := k) (z := z)).mp (by exact_mod_cast h)
  simpa using this

lemma V2_two_pow (n : ℕ) : V2 n ((2 : ℚ) ^ n) := by
  have := V2_of_dvd (k := n) (z := 2 ^ n) dvd_rfl
  simpa using this

lemma V2_div_of_norm {e k : ℤ} {x y : ℚ} (hx : V2 e x) (hy : padicNorm 2 y = (2 : ℚ) ^ (-k)) :
    V2 (e - k) (x / y) := by
  unfold V2 at *
  rw [padicNorm.div, hy, div_le_iff₀ (by positivity), ← zpow_add₀ two_ne_zero]
  convert hx using 2; ring

lemma padicNorm_two_odd {n : ℕ} (hn : Odd n) : padicNorm 2 (n : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff n).mpr (by obtain ⟨k, rfl⟩ := hn; omega)

lemma V2_div_odd {e : ℤ} {x : ℚ} (hx : V2 e x) {n : ℕ} (hn : Odd n) : V2 e (x / n) := by
  have := V2_div_of_norm (k := 0) hx (by rw [padicNorm_two_odd hn]; simp)
  simpa using this

lemma V2_inv_odd {n : ℕ} (hn : Odd n) : V2 0 (1 / (n : ℚ)) := V2_div_odd V2_one hn

/-! ### `v₂(n!)` -/

/-- `v₂(n!)`. -/
def vf (n : ℕ) : ℕ := padicValNat 2 n !

lemma vf_le (n : ℕ) : vf n ≤ n := by unfold vf; exact padicValNat_factorial_le 2 n

lemma vf_lt {n : ℕ} (hn : n ≠ 0) : vf n < n := by unfold vf; exact padicValNat_factorial_lt_of_ne_zero 2 hn

lemma vf_ge (n : ℕ) : n ≤ vf n + Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp [vf]
    · have e1 : vf n = vf (n / 2) + n / 2 := by
        unfold vf
        rw [← padicValNat_mul_div_factorial (p := 2) n, padicValNat_factorial_mul]
      have e2 := Nat.log_div_base 2 n
      have e3 : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) h
      have := ih (n / 2) (by omega)
      omega

lemma padicNorm_factorial (n : ℕ) : padicNorm 2 ((n ! : ℕ) : ℚ) = (2 : ℚ) ^ (-((vf n : ℕ) : ℤ)) := by
  unfold vf
  rw [padicNorm.eq_zpow_of_nonzero (by positivity), padicValRat.of_nat]
  norm_num

lemma V2_div_factorial {e : ℤ} {x : ℚ} (hx : V2 e x) (n : ℕ) : V2 (e - vf n) (x / (n ! : ℕ)) :=
  V2_div_of_norm hx (padicNorm_factorial n)

lemma V2_factorial_dvd {b : ℕ} {z : ℤ} (h : ((b ! : ℕ) : ℤ) ∣ z) : V2 (vf b) (z : ℚ) := by
  refine V2_of_dvd (dvd_trans ?_ h)
  exact_mod_cast (pow_padicValNat_dvd (p := 2) (n := b !))

lemma log_two_mono {a b : ℕ} (h : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right h

/-! ### Forward differences on `ℕ → ℚ` -/

lemma fd_succ (f : ℕ → ℚ) (b y : ℕ) :
    (Δ_[1])^[b + 1] f y = (Δ_[1])^[b] f (y + 1) - (Δ_[1])^[b] f y := by
  rw [Function.iterate_succ_apply']; rfl

lemma fd_shift (f : ℕ → ℚ) (b y m : ℕ) :
    (Δ_[1])^[b] f (y + m) = (Δ_[1])^[b] (fun r => f (r + m)) y :=
  (fwdDiff_iter_comp_add 1 f m b y).symm

lemma fd_mul_id (f : ℕ → ℚ) (b y : ℕ) :
    (Δ_[1])^[b + 1] (fun x : ℕ => (x : ℚ) * f x) y =
      y * (Δ_[1])^[b + 1] f y + (b + 1) * (Δ_[1])^[b] f (y + 1) := by
  induction b generalizing y with
  | zero =>
    simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq, fwdDiff, Nat.cast_zero]
    push_cast; ring
  | succ b ih =>
    have h1 := fd_succ f (b + 1) y
    have h2 := fd_succ f b (y + 1)
    rw [fd_succ _ (b + 1) y, ih, ih]
    push_cast
    linear_combination (-(y : ℚ)) * h1 - ((b : ℚ) + 1) * h2

lemma fd_mul_id_zero (f : ℕ → ℚ) (N : ℕ) :
    (Δ_[1])^[N] (fun x : ℕ => (x : ℚ) * f x) 0 = N * (Δ_[1])^[N - 1] f 1 := by
  cases N with
  | zero => simp
  | succ b => rw [fd_mul_id]; simp

lemma fd_sum_eq (f : ℕ → ℚ) (n : ℕ) :
    ∑ l ∈ range (n + 1), (-1 : ℚ) ^ l * (n.choose l : ℚ) * f l = (-1) ^ n * (Δ_[1])^[n] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift, mul_sum]
  refine sum_congr rfl (fun l hl => ?_)
  have hl' : l ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hl)
  rw [zsmul_eq_mul]
  push_cast
  simp only [zero_add, smul_eq_mul, mul_one]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl'
  rw [show l + d - l = d by omega, pow_add]
  have h : ((-1 : ℚ) ^ d) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-(-1 : ℚ) ^ l * ((l + d).choose l : ℚ) * f l) * h

/-! ### `b! ∣ Δ^b[x^n](0)` -/

lemma dCoef_eq_fd (n b : ℕ) : (dCoef n b : ℚ) = (Δ_[1])^[b] (fun x : ℕ => (x : ℚ) ^ n) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold dCoef
  push_cast
  refine sum_congr rfl (fun k _ => ?_)
  rw [zsmul_eq_mul]
  push_cast
  simp

lemma dCoef_succ (n b : ℕ) : dCoef (n + 1) (b + 1) = (b + 1) * (dCoef n b + dCoef n (b + 1)) := by
  have h := fd_mul_id (fun x : ℕ => (x : ℚ) ^ n) b 0
  have e : (fun x : ℕ => (x : ℚ) ^ (n + 1)) = fun x : ℕ => (x : ℚ) * (x : ℚ) ^ n := by funext x; ring
  have key : (dCoef (n + 1) (b + 1) : ℚ) = (b + 1) * (dCoef n b + dCoef n (b + 1)) := by
    rw [dCoef_eq_fd, dCoef_eq_fd, dCoef_eq_fd, e, h, fd_succ _ b 0]
    simp
  exact_mod_cast key

lemma factorial_dvd_dCoef (n b : ℕ) : ((b ! : ℕ) : ℤ) ∣ dCoef n b := by
  induction n generalizing b with
  | zero =>
    cases b with
    | zero => simp
    | succ b => rw [dCoef_eq_zero (by omega)]; exact dvd_zero _
  | succ n ih =>
    cases b with
    | zero => simp
    | succ b =>
      rw [dCoef_succ, Nat.factorial_succ]
      push_cast
      refine mul_dvd_mul_left _ (dvd_add (ih b) (dvd_trans ?_ (ih (b + 1))))
      exact_mod_cast Nat.factorial_dvd_factorial (Nat.le_succ b)

/-! ### `g_s(r) = 1/(s + 2r)²` -/

/-- `g_s(r) = 1/(s + 2r)²`. -/
def gS (s r : ℕ) : ℚ := 1 / ((s : ℚ) + 2 * r) ^ 2

/-- `P_m(s) = ∏_{a≤m} (s + 2a)`. -/
def PS (s m : ℕ) : ℚ := ∏ a ∈ range (m + 1), ((s : ℚ) + 2 * a)

/-- `H_m(s) = ∑_{a≤m} 1/(s + 2a)`. -/
def HS (s m : ℕ) : ℚ := ∑ a ∈ range (m + 1), 1 / ((s : ℚ) + 2 * a)

lemma PS_pos {s : ℕ} (hs : 0 < s) (m : ℕ) : 0 < PS s m :=
  prod_pos (fun a _ => by positivity)

lemma fd_gS (m : ℕ) : ∀ s : ℕ, 0 < s →
    (Δ_[1])^[m] (gS s) 0 = (-2) ^ m * (m ! : ℕ) * HS s m / PS s m := by
  induction m with
  | zero =>
    intro s hs
    have : (s : ℚ) ≠ 0 := by positivity
    simp [gS, HS, PS]
    field_simp
  | succ m ih =>
    intro s hs
    have hs0 : (s : ℚ) ≠ 0 := by positivity
    have hs1 : (s : ℚ) + 2 * ((m : ℚ) + 1) ≠ 0 := by positivity
    have hP : PS s (m + 1) ≠ 0 := (PS_pos hs _).ne'
    have hshift : (fun r => gS s (r + 1)) = gS (s + 2) := by
      funext r; unfold gS; push_cast; ring_nf
    have hP1 : PS (s + 2) m = PS s (m + 1) / s := by
      rw [eq_div_iff hs0]
      unfold PS
      rw [prod_range_succ' (fun a => (s : ℚ) + 2 * a)]
      push_cast
      simp only [mul_zero, add_zero]
      congr 1
      refine prod_congr rfl (fun a _ => by ring)
    have hP2 : PS s m = PS s (m + 1) / ((s : ℚ) + 2 * ((m : ℚ) + 1)) := by
      rw [eq_div_iff hs1]
      unfold PS
      rw [prod_range_succ _ (m + 1)]
      push_cast; ring
    have hH1 : HS (s + 2) m = HS s (m + 1) - 1 / s := by
      unfold HS
      rw [sum_range_succ' (fun a => 1 / ((s : ℚ) + 2 * a))]
      push_cast
      simp only [mul_zero, add_zero, add_sub_cancel_right]
      refine sum_congr rfl (fun a _ => by ring_nf)
    have hH2 : HS s m = HS s (m + 1) - 1 / ((s : ℚ) + 2 * ((m : ℚ) + 1)) := by
      unfold HS
      rw [sum_range_succ _ (m + 1)]
      push_cast; ring
    rw [fd_succ, zero_add, fd_shift _ _ 0 1, hshift, ih (s + 2) (by omega), ih s hs,
      hP1, hP2, hH1, hH2, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma padicNorm_PS {s : ℕ} (hs : Odd s) (m : ℕ) : padicNorm 2 (PS s m) = 1 := by
  unfold PS
  induction m with
  | zero =>
    simp only [zero_add, range_one, prod_singleton, Nat.cast_zero, mul_zero, add_zero]
    exact padicNorm_two_odd hs
  | succ m ih =>
    rw [prod_range_succ, padicNorm.mul, ih, one_mul]
    have : (s : ℚ) + 2 * ((m + 1 : ℕ) : ℚ) = ((s + 2 * (m + 1) : ℕ) : ℚ) := by push_cast; ring
    rw [this]
    exact padicNorm_two_odd (hs.add_even (even_two_mul _))

lemma V2_HS {s : ℕ} (hs : Odd s) (m : ℕ) : V2 0 (HS s m) := by
  unfold HS
  refine V2_sum _ _ (fun a _ => ?_)
  have : (s : ℚ) + 2 * (a : ℚ) = ((s + 2 * a : ℕ) : ℚ) := by push_cast; ring
  rw [this]
  exact V2_inv_odd (hs.add_even (even_two_mul _))

lemma V2_fd_gS {s : ℕ} (hs : Odd s) (m : ℕ) : V2 ((m : ℤ) + vf m) ((Δ_[1])^[m] (gS s) 0) := by
  rw [fd_gS m s hs.pos]
  have h1 : V2 m ((-2 : ℚ) ^ m) := by
    have := V2_pow (V2_neg (V2_two_pow 1)) m
    simpa using this
  have h2 : V2 (vf m) (((m ! : ℕ) : ℤ) : ℚ) := V2_factorial_dvd dvd_rfl
  push_cast at h2
  have := V2_div_of_norm (k := 0) (y := PS s m) (V2_mul (V2_mul h1 h2) (V2_HS hs m)) (by rw [padicNorm_PS hs]; simp)
  simpa using this

/-! ### The sequence bound -/

lemma fd_seq_formula {Q e : ℚ} {s : ℕ} {T : ℕ → ℚ} (hrec : ∀ l, T (l + 1) = Q * T l + e * gS s l)
    (m y : ℕ) :
    (Δ_[1])^[m] T y = (Q - 1) ^ m * T y +
      e * ∑ k ∈ range m, (Q - 1) ^ (m - 1 - k) * (Δ_[1])^[k] (gS s) y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [fd_succ, ih, ih, hrec, sum_range_succ']
    simp only [Function.iterate_zero, id, Nat.sub_zero]
    rw [show m + 1 - 1 = m by omega]
    have hs : ∑ k ∈ range m, (Q - 1) ^ (m - 1 - k) * (Δ_[1])^[k] (gS s) (y + 1) -
        ∑ k ∈ range m, (Q - 1) ^ (m - 1 - k) * (Δ_[1])^[k] (gS s) y =
        ∑ k ∈ range m, (Q - 1) ^ (m - (k + 1)) * (Δ_[1])^[k + 1] (gS s) y := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun k _ => ?_)
      rw [fd_succ, show m - (k + 1) = m - 1 - k by omega]
      ring
    linear_combination e * hs

theorem V2_fd_seq {Q e : ℚ} (hη : V2 2 (Q - 1)) (he : V2 0 e) {s : ℕ} (hs : Odd s) {T : ℕ → ℚ}
    (hT0 : V2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * gS s l) (m : ℕ) :
    V2 ((vf m : ℤ) + m - 2 - Nat.log 2 m) ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine V2_add (V2_mul' (V2_pow hη m) hT0 ?_) ?_
  · have := vf_le m; push_cast; omega
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [range_zero, sum_empty, mul_zero]; exact V2_zero _
    refine V2_mul' (f := (vf m : ℤ) + m - 2 - Nat.log 2 m) he (V2_sum _ _ (fun k hk => V2_mono ?_
      (V2_mul (V2_pow hη _) (V2_fd_gS hs k)))) (by simp)
    have hk := mem_range.mp hk
    have h1 := vf_ge k
    have h2 := vf_lt (Nat.pos_iff_ne_zero.mp hm)
    have h3 := log_two_mono hk.le
    push_cast
    omega

lemma padicNorm_two_self : padicNorm 2 (2 : ℚ) = (2 : ℚ) ^ (-(1 : ℤ)) := by
  rw [zpow_neg_one]; exact_mod_cast padicNorm.padicNorm_p_of_prime (p := 2)

lemma V2_four : V2 2 (4 : ℚ) := by
  have := V2_two_pow 2; norm_num at this; exact this

lemma V2_gS {s : ℕ} (hs : Odd s) (r : ℕ) : V2 0 (gS s r) := by
  unfold gS
  have : (s : ℚ) + 2 * r = ((s + 2 * r : ℕ) : ℚ) := by push_cast; ring
  rw [this, ← one_div_pow]
  simpa using V2_pow (V2_inv_odd (hs.add_even (even_two_mul r))) 2

lemma gS_succ (s r : ℕ) : gS s (r + 1) = gS (s + 2) r := by unfold gS; push_cast; ring_nf

/-- **The (U) entry bound.** `v₂((4/N!) Δ^N[(−c/2 − l) T(l)](0)) ≥ N − 1 − ⌊log₂ N⌋`. -/
theorem V2_U {Q e : ℚ} (hη : V2 2 (Q - 1)) (he : V2 0 e) {s : ℕ} (hs : Odd s) {T : ℕ → ℚ}
    (hT0 : V2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * gS s l) {c : ℕ} (hc : Odd c) (N : ℕ) :
    V2 ((N : ℤ) - 1 - Nat.log 2 N)
      (4 / (N ! : ℕ) * (Δ_[1])^[N] (fun l : ℕ => (-((c : ℚ) / 2) - l) * T l) 0) := by
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
      (V2_mul (V2_neg hc2) (V2_fd_seq hη he hs hT0 hrec N)) ?_
    omega
  · cases N with
    | zero => simp only [Nat.cast_zero, zero_mul, mul_zero]; exact V2_zero _
    | succ n =>
      have hrec' : ∀ l, (fun r => T (r + 1)) (l + 1) = Q * (fun r => T (r + 1)) l + e * gS (s + 2) l := by
        intro l; simp only; rw [hrec (l + 1), gS_succ]
      have hb := V2_fd_seq hη he (hs.add_even even_two) (T := fun r => T (r + 1)) hT1 hrec' n
      have e1 : (4 : ℚ) / ((n + 1) ! : ℕ) * (-1 * (((n + 1 : ℕ) : ℚ) * (Δ_[1])^[n + 1 - 1] T 1)) =
          -(4 / (n ! : ℕ) * (Δ_[1])^[n] (fun r => T (r + 1)) 0) := by
        rw [show n + 1 - 1 = n by omega, ← fd_shift T n 0 1, zero_add, Nat.factorial_succ]
        push_cast
        field_simp
      rw [e1]
      refine V2_neg (V2_mul' (V2_div_factorial V2_four n) hb ?_)
      have := log_two_mono (show n ≤ n + 1 by omega)
      push_cast
      omega

end Chi2Irr
