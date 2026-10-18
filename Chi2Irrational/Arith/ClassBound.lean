/-
# The class bound for one-level primes

For an odd prime `p` with `2h < p²` (so every difference of two atoms and every odd `s ≤ 2h − 1` has `v_p ≤ 1`):
  `‖Δ^F_h‖_p ≤ p^{classBd h p}`.
Basis: `e_m = s_m D/∏_{l ∈ seg m}(u − x_l)`, `seg m = {l ≤ m : l ≡ m (p)}`, `s_m = ∏_{l ∈ seg m, l < m}(x_m − x_l)`.
Its evaluation matrix is lower triangular with diagonal `D′(x_m)`, so `‖Δ‖ ≤ ‖det G^e‖/∏|D′(x_m)|`.
Entries: `e_m e_m′ φ = s s′ u ∏_{∉A∪B}/∏_{A∩B}`; the polynomial part is `s s′ ×` (p-integral), the residues at
`k ∈ A ∩ B` have `|·| = p^{−(n−1)}|2k+1|`, the pole factors `S_k` cost `p^{2[p ≤ 2k+1]}`.
-/
import Chi2Irrational.Arith.Gauss
import Chi2Irrational.Arith.Defs
import Chi2Irrational.NonVan.ClassData

namespace Chi2Irr

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Integral quotients -/

lemma zlPoly_divByMonic {P Q : ℚ[X]} (hP : ZlPoly p P) (hQ : ZlPoly p Q) (hm : Q.Monic) :
    ZlPoly p (P /ₘ Q) := by
  obtain ⟨P₀, hP₀⟩ := (mem_lifts P).mp (zlPoly_iff_lifts.mp hP)
  obtain ⟨Q₀, hQ₀, -, hQ₀m⟩ := lifts_and_natDegree_eq_and_monic (zlPoly_iff_lifts.mp hQ) hm
  rw [← hP₀, ← hQ₀, ← map_divByMonic _ hQ₀m, zlPoly_iff_lifts]
  exact ⟨_, rfl⟩

/-! ### Residue classes in `[0, X)` -/

lemma filter_mod_eq_image {c : ℕ} (hc : c < p) (X : ℕ) :
    (range X).filter (fun l => l % p = c) = (range ((X + p - 1 - c) / p)).image (fun j => c + j * p) := by
  have hp0 : 0 < p := hp.out.pos
  ext l
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hl, hlc⟩
    refine ⟨l / p, ?_, ?_⟩
    · rw [Nat.lt_div_iff_mul_lt hp0]
      have := Nat.mod_add_div l p
      rw [hlc] at this
      have e : (l / p + 1) * p = l / p * p + p := by ring
      have e2 : p * (l / p) = l / p * p := by ring
      omega
    · have := Nat.mod_add_div l p
      rw [hlc] at this
      linarith [mul_comm p (l / p)]
  · rintro ⟨j, hj, rfl⟩
    rw [Nat.lt_div_iff_mul_lt hp0] at hj
    refine ⟨?_, ?_⟩
    · have e : (j + 1) * p = j * p + p := by ring
      omega
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

lemma card_filter_mod {c : ℕ} (hc : c < p) (X : ℕ) :
    ((range X).filter (fun l => l % p = c)).card = (X + p - 1 - c) / p := by
  rw [filter_mod_eq_image hc, card_image_of_injective _ (fun a b e => by
    have hp0 : 0 < p := hp.out.pos
    exact Nat.eq_of_mul_eq_mul_right hp0 (by omega)), card_range]

/-- The segment `{l ≤ m : l ≡ m (p)}` (inside `[0, h)`). -/
def segF (p h m : ℕ) : Finset ℕ := (range h).filter (fun l => l ≤ m ∧ l % p = m % p)

lemma mem_segF {h m l : ℕ} : l ∈ segF p h m ↔ l < h ∧ l ≤ m ∧ l % p = m % p := by
  simp [segF]

lemma segF_subset (h m : ℕ) : segF p h m ⊆ range h := filter_subset _ _

lemma self_mem_segF {h m : ℕ} (hm : m < h) : m ∈ segF p h m := mem_segF.mpr ⟨hm, le_rfl, rfl⟩

lemma segF_eq {h m : ℕ} (hm : m < h) : segF p h m = (range (m + 1)).filter (fun l => l % p = m % p) := by
  ext l; simp only [mem_segF, mem_filter, mem_range]; omega

lemma card_segF {h m : ℕ} (hm : m < h) : (segF p h m).card = m / p + 1 := by
  have hp0 : 0 < p := hp.out.pos
  rw [segF_eq hm, card_filter_mod (Nat.mod_lt _ hp0)]
  have := Nat.mod_add_div m p
  have e : (m + 1 + p - 1 - m % p) = (m / p + 1) * p := by
    have : p * (m / p) = m / p * p := by ring
    have e2 : (m / p + 1) * p = m / p * p + p := by ring
    omega
  rw [e, Nat.mul_div_cancel _ hp0]

lemma card_class {h m : ℕ} (hm : m < h) :
    ((range h).filter (fun l => l % p = m % p)).card = clSize h p m := by
  have hp0 : 0 < p := hp.out.pos
  have hc := Nat.mod_lt m hp0
  rw [card_filter_mod hc, clSize]
  have hmc : m % p ≤ m := Nat.mod_le m p
  have e : h + p - 1 - m % p = (h - 1 - m % p) + p := by omega
  rw [e, Nat.add_div_right _ hp0]

/-! ### `p`-adic sizes (`p` odd, `2h < p²`) -/

section Sizes

variable {h : ℕ} (hp2 : p ≠ 2) (hph : 2 * h < p * p)
include hp2 hph

lemma padicNorm_pole_sub_same {a b : ℕ} (hab : a ≠ b) (ha : a < h) (hb : b < h) (hmod : a % p = b % p) :
    padicNorm p (pole a - pole b) = (p : ℚ)⁻¹ := by
  have hp0 : 0 < p := hp.out.pos
  rw [pole_sub_pole]
  have hdvd : (p : ℤ) ∣ (b : ℤ) - a := (Nat.modEq_iff_dvd).mp hmod
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by intro e; subst e; simp at hk; omega
  have hkp : ¬ (p : ℤ) ∣ k := by
    rintro ⟨j, rfl⟩
    have hj : j ≠ 0 := by rintro rfl; simp at hk0
    have : (p : ℤ) * p ≤ |(b : ℤ) - a| := by
      rw [hk, abs_mul, abs_mul, abs_of_pos (by exact_mod_cast hp0 : (0:ℤ) < p)]
      have : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
      nlinarith
    have : |(b : ℤ) - a| < h := by rw [abs_lt]; constructor <;> omega
    have : (p : ℤ) * p < 2 * h := by nlinarith
    have : ((p * p : ℕ) : ℤ) < ((2 * h : ℕ) : ℤ) := by push_cast; linarith
    omega
  have e : ((b : ℚ) - a) = (p : ℚ) * (k : ℚ) := by exact_mod_cast hk
  rw [e, padicNorm.mul, padicNorm_self, padicNorm_intCast_eq_one hkp, mul_one]

lemma padicNorm_pole_sub (a b : ℕ) (ha : a < h) (hb : b < h) (hab : a ≠ b) :
    padicNorm p (pole a - pole b) = if a % p = b % p then (p : ℚ)⁻¹ else 1 := by
  split_ifs with hm
  · exact padicNorm_pole_sub_same hp2 hph hab ha hb hm
  · exact padicNorm_pole_sub_of_mod_ne hm

/-- `|∏_{l∈S}(x_k − x_l)|_p = p^{−#(S ∩ class k)}`. -/
lemma padicNorm_prod_poles {S : Finset ℕ} {k : ℕ} (hS : S ⊆ range h) (hk : k < h) (hkS : k ∉ S) :
    padicNorm p (∏ l ∈ S, (pole k - pole l)) = ((p : ℚ)⁻¹) ^ (S.filter (fun l => l % p = k % p)).card := by
  rw [padicNorm_prod, ← prod_filter_mul_prod_filter_not S (fun l => l % p = k % p)]
  have h1 : ∀ l ∈ S.filter (fun l => l % p = k % p), padicNorm p (pole k - pole l) = (p : ℚ)⁻¹ := by
    intro l hl
    rw [mem_filter] at hl
    exact padicNorm_pole_sub_same hp2 hph (fun e => hkS (e ▸ hl.1)) hk (mem_range.mp (hS hl.1)) hl.2.symm
  have h2 : ∀ l ∈ S.filter (fun l => ¬ l % p = k % p), padicNorm p (pole k - pole l) = 1 := by
    intro l hl
    rw [mem_filter] at hl
    exact padicNorm_pole_sub_of_mod_ne (fun e => hl.2 e.symm)
  rw [prod_congr rfl h1, prod_congr rfl h2, prod_const, prod_const_one, mul_one]

lemma padicNorm_odd {s : ℕ} (hs : s < p * p) (hs0 : 0 < s) :
    padicNorm p (s : ℚ) = if p ∣ s then (p : ℚ)⁻¹ else 1 := by
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    have hk : ¬ p ∣ k := by
      rintro ⟨j, rfl⟩
      have : 0 < j := by rcases Nat.eq_zero_or_pos j with e | e
                         · subst e; simp at hs0
                         · exact e
      nlinarith
    push_cast
    rw [padicNorm.mul, padicNorm_self, padicNorm_natCast_eq_one hk, mul_one]
  · exact padicNorm_natCast_eq_one hd

lemma padicNorm_pole' {k : ℕ} (hk : k < h) :
    padicNorm p (pole k) = if p ∣ 2 * k + 1 then (p : ℚ)⁻¹ else 1 := by
  rw [pole_eq, padicNorm.neg, padicNorm.div, padicNorm_two hp2, div_one]
  exact padicNorm_odd hp2 hph (by omega) (by omega)

lemma GLe_SpartF {k : ℕ} (hk : k < h) :
    GLe p (if p ≤ 2 * k + 1 then (p : ℚ) ^ 2 else 1) (SpartF k) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hB : (0 : ℚ) ≤ (if p ≤ 2 * k + 1 then (p : ℚ) ^ 2 else 1) := by split_ifs <;> positivity
  refine GLe_sum _ hB _ (fun j hj => ?_)
  have hj := mem_range.mp hj
  have hjn : padicNorm p (1 / (2 * (j : ℚ) + 1) ^ 2) ≤ (if p ≤ 2 * k + 1 then (p : ℚ) ^ 2 else 1) := by
    have e : (2 * (j : ℚ) + 1) = ((2 * j + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [e, padicNorm.div, padicNorm.one, padicNorm_pow (ℓ := p), padicNorm_odd hp2 hph (by omega) (by omega)]
    split_ifs with h1 h2 h2
    · simp [inv_pow]
    · exfalso; have := Nat.le_of_dvd (by omega) h1; omega
    · simp only [one_pow, div_one]; nlinarith
    · simp
  have hC : GLe p (if p ≤ 2 * k + 1 then (p : ℚ) ^ 2 else 1) (MvPolynomial.C (1 / (2 * (j : ℚ) + 1) ^ 2)) :=
    GLe_mono hjn (GLe_C _)
  have hq : GLe p 1 (qF ^ (2 * (k - j))) := by simpa using GLe_pow (p := p) zero_le_one GLe_qF (2 * (k - j))
  simpa using GLe_mul zero_le_one hB hq hC

end Sizes


/-! ### The class family -/

/-- `s_m = ∏_{l ∈ seg m, l ≠ m} (x_m − x_l)`. -/
noncomputable def scF (p h m : ℕ) : ℚ := ∏ l ∈ (segF p h m).erase m, (pole m - pole l)

/-- `∏_{k ∈ S} (X − x_k)`. -/
noncomputable def prodS (S : Finset ℕ) : ℚ[X] := ∏ k ∈ S, (X - C (pole k))

lemma prodS_monic (S : Finset ℕ) : (prodS S).Monic := monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)

lemma natDegree_prodS (S : Finset ℕ) : (prodS S).natDegree = S.card := by
  unfold prodS
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp

lemma eval_prodS (S : Finset ℕ) (t : ℚ) : (prodS S).eval t = ∏ k ∈ S, (t - pole k) := by
  simp [prodS, eval_prod]

/-- The class-adapted family `e_m = s_m ∏_{k ∉ seg m} (X − x_k)`. -/
noncomputable def eCl (p h : ℕ) (m : Fin h) : ℚ[X] := C (scF p h m) * prodS (range h \ segF p h m)

lemma natDegree_eCl {h : ℕ} (m : Fin h) : (eCl p h m).natDegree < h := by
  unfold eCl
  refine (natDegree_C_mul_le _ _).trans_lt ?_
  rw [natDegree_prodS]
  have h1 := card_sdiff_add_card_eq_card (segF_subset (p := p) h m)
  have h2 := card_pos.mpr ⟨_, self_mem_segF (p := p) m.isLt⟩
  rw [card_range] at h1
  omega

lemma eval_eCl_of_not_mem {h : ℕ} (m : Fin h) {k : ℕ} (hk : k < h) (hkA : k ∉ segF p h m) :
    (eCl p h m).eval (pole k) = 0 := by
  unfold eCl
  rw [eval_mul, eval_prodS, prod_eq_zero (mem_sdiff.mpr ⟨mem_range.mpr hk, hkA⟩) (sub_self _), mul_zero]

lemma eval_eCl_self {h : ℕ} (m : Fin h) : (eCl p h m).eval (pole m) = dPrime h m := by
  unfold eCl dPrime scF
  rw [eval_mul, eval_C, eval_prodS]
  have hm : (m : ℕ) ∈ segF p h m := self_mem_segF m.isLt
  have hsplit : (range h).erase m = (segF p h m).erase m ∪ (range h \ segF p h m) := by
    ext l
    constructor
    · intro hl
      rw [mem_erase] at hl
      by_cases hA : l ∈ segF p h m
      · exact mem_union_left _ (mem_erase.mpr ⟨hl.1, hA⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hl.2, hA⟩)
    · intro hl
      rcases mem_union.mp hl with hl | hl
      · exact mem_erase.mpr ⟨(mem_erase.mp hl).1, segF_subset h m (mem_erase.mp hl).2⟩
      · obtain ⟨h1, h2⟩ := mem_sdiff.mp hl
        exact mem_erase.mpr ⟨fun e => h2 (e ▸ hm), h1⟩
  have hdisj : Disjoint ((segF p h m).erase m) (range h \ segF p h m) := by
    rw [disjoint_left]; intro l h1 h2; exact (mem_sdiff.mp h2).2 (mem_of_mem_erase h1)
  rw [hsplit, prod_union hdisj]

/-! ### The entries -/

lemma divByMonic_mul_cancel {P Q N : ℚ[X]} (hQ : Q.Monic) (hN : N.Monic) : (P * N) /ₘ (Q * N) = P /ₘ Q := by
  have hQN : (Q * N).Monic := hQ.mul hN
  refine (div_modByMonic_unique (P /ₘ Q) ((P %ₘ Q) * N) hQN ⟨?_, ?_⟩).1
  · have := modByMonic_add_div P Q
    calc P %ₘ Q * N + Q * N * (P /ₘ Q) = (P %ₘ Q + Q * (P /ₘ Q)) * N := by ring
      _ = P * N := by rw [this]
  · by_cases h0 : P %ₘ Q = 0
    · rw [h0, zero_mul, degree_zero]; exact bot_lt_iff_ne_bot.mpr (by
        rw [Ne, degree_eq_bot]; exact hQN.ne_zero)
    · rw [degree_mul, degree_mul]
      exact WithBot.add_lt_add_right (by rw [Ne, degree_eq_bot]; exact hN.ne_zero) (degree_modByMonic_lt _ hQ)

lemma C_mul_divByMonic (c : ℚ) (P Q : ℚ[X]) : (C c * P) /ₘ Q = C c * (P /ₘ Q) := by
  rw [← smul_eq_C_mul, ← divByMonicHom_apply, map_smul, divByMonicHom_apply, smul_eq_C_mul]

/-- The product of two family members. -/
lemma eCl_mul {h : ℕ} (m m' : Fin h) :
    eCl p h m * eCl p h m' = C (scF p h m * scF p h m') *
      (prodS (range h \ (segF p h m ∪ segF p h m')) * prodS (range h \ (segF p h m ∩ segF p h m'))) := by
  have key : prodS (range h \ segF p h m) * prodS (range h \ segF p h m') =
      prodS (range h \ (segF p h m ∪ segF p h m')) * prodS (range h \ (segF p h m ∩ segF p h m')) := by
    unfold prodS
    rw [sdiff_union_distrib, sdiff_inter_distrib_right, ← prod_union_inter, mul_comm]
  unfold eCl
  rw [C_mul, ← key]
  ring

/-- The polynomial part `(e_m e_m′ X) /ₘ D`. -/
lemma polyPart_eCl {h : ℕ} (m m' : Fin h) :
    (eCl p h m * eCl p h m' * X) /ₘ Dpoly h =
      C (scF p h m * scF p h m') * ((X * prodS (range h \ (segF p h m ∪ segF p h m'))) /ₘ
        prodS (segF p h m ∩ segF p h m')) := by
  set A := segF p h m
  set B := segF p h m'
  have hD : Dpoly h = prodS (A ∩ B) * prodS (range h \ (A ∩ B)) := by
    unfold Dpoly prodS
    rw [mul_comm, prod_sdiff ((inter_subset_left).trans (segF_subset h m))]
  rw [eCl_mul, hD]
  have e : C (scF p h m * scF p h m') * (prodS (range h \ (A ∪ B)) * prodS (range h \ (A ∩ B))) * X =
      (C (scF p h m * scF p h m') * (X * prodS (range h \ (A ∪ B)))) * prodS (range h \ (A ∩ B)) := by ring
  rw [e, divByMonic_mul_cancel (prodS_monic _) (prodS_monic _), C_mul_divByMonic]

lemma zlPoly_prodS (hp2 : p ≠ 2) (S : Finset ℕ) : ZlPoly p (prodS S) :=
  zlPoly_prod _ _ (fun k _ => zlPoly_X_sub_C (pole_mem_Zl hp2 k))

lemma zlPoly_polyPart (hp2 : p ≠ 2) {h : ℕ} (m m' : Fin h) :
    ZlPoly p ((X * prodS (range h \ (segF p h m ∪ segF p h m'))) /ₘ prodS (segF p h m ∩ segF p h m')) :=
  zlPoly_divByMonic (zlPoly_mul zlPoly_X (zlPoly_prodS hp2 _)) (zlPoly_prodS hp2 _) (prodS_monic _)

/-! ### `μ` of an integral polynomial -/

lemma GLe_muMonoF (d : ℕ) : GLe p 1 (muMonoF d) := by
  unfold muMonoF
  refine GLe_sum _ zero_le_one _ (fun b _ => ?_)
  have hc : padicNorm p ((d : ℚ) * (dCoef (d - 1) b : ℚ)) ≤ 1 := by
    have : ((d : ℚ) * (dCoef (d - 1) b : ℚ)) = (((d : ℤ) * dCoef (d - 1) b : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact padicNorm.of_int _
  simpa using GLe_mul zero_le_one zero_le_one (GLe_mono hc (GLe_C _)) (GLe_OmegaF b)

lemma GLe_muF_of_zlPoly {R : ℚ[X]} (hR : ZlPoly p R) : GLe p 1 (muF R) := by
  rw [muF_eq_sum, Polynomial.sum_def]
  refine GLe_sum _ zero_le_one _ (fun d _ => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  simpa using GLe_mul zero_le_one zero_le_one (GLe_mono (mem_Zl.mp (hR d)) (GLe_C _)) (GLe_muMonoF d)

lemma GLe_muF_C_mul {R : ℚ[X]} (hR : ZlPoly p R) (c : ℚ) : GLe p (padicNorm p c) (muF (C c * R)) := by
  rw [← smul_eq_C_mul, muF_smul, MvPolynomial.smul_eq_C_mul]
  simpa using GLe_mul (padicNorm.nonneg _) zero_le_one (GLe_C c) (GLe_muF_of_zlPoly hR)


/-! ### Exponents -/

/-- The class-bound summand of an atom. -/
def sCB (p h m : ℕ) : ℕ := 2 * (m / p) + 1 + wMax p m - clSize h p m

/-- Row and column exponents (`a_m + b_m = 2 r_m − s_m`). -/
def aE (p h m : ℕ) : ℤ := (m / p : ℕ) - (sCB p h m / 2 : ℕ)

def bE (p h m : ℕ) : ℤ := (m / p : ℕ) - ((sCB p h m + 1) / 2 : ℕ)

lemma zpow_prod_eq {ι : Type*} (s : Finset ι) {a : ℚ} (ha : a ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [prod_insert hx, sum_insert hx, ih, zpow_add₀ ha]

lemma inv_pow_eq_zpow {a : ℚ} (n : ℕ) : a⁻¹ ^ n = a ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_natCast, inv_pow]

lemma wAtom_le_wMax {m k : ℕ} (hk : k ≤ m) (hmod : k % p = m % p) : wAtom p k ≤ wMax p m := by
  unfold wMax
  have hp0 : 0 < p := hp.out.pos
  have hkdiv : k / p ≤ m / p := Nat.div_le_div_right hk
  have : k = m % p + k / p * p := by
    have := Nat.mod_add_div k p; rw [hmod] at this; linarith [mul_comm p (k / p)]
  rw [this]
  exact Finset.le_sup (f := fun j => wAtom p (m % p + j * p)) (mem_range.mpr (by omega))

section Entries

variable {h : ℕ} (hp2 : p ≠ 2) (hph : 2 * h < p * p)
include hp2 hph

lemma padicNorm_scF {m : ℕ} (hm : m < h) : padicNorm p (scF p h m) = (p : ℚ)⁻¹ ^ (m / p) := by
  unfold scF
  have hS : (segF p h m).erase m ⊆ range h := (erase_subset _ _).trans (segF_subset h m)
  rw [padicNorm_prod_poles hp2 hph hS hm (by simp)]
  congr 1
  rw [filter_true_of_mem (fun l hl => (mem_segF.mp (mem_of_mem_erase hl)).2.2), card_erase_of_mem
    (self_mem_segF hm), card_segF hm]
  generalize m / p = r
  omega

lemma padicNorm_dPrime_cl {m : ℕ} (hm : m < h) : padicNorm p (dPrime h m) = (p : ℚ)⁻¹ ^ (clSize h p m - 1) := by
  unfold dPrime
  rw [padicNorm_prod_poles hp2 hph (erase_subset _ _) hm (by simp)]
  congr 1
  have : ((range h).erase m).filter (fun l => l % p = m % p) = ((range h).filter (fun l => l % p = m % p)).erase m := by
    ext l; simp only [mem_filter, mem_erase]; tauto
  rw [this, card_erase_of_mem (s := (range h).filter (fun l => l % p = m % p))
    (mem_filter.mpr ⟨mem_range.mpr hm, rfl⟩), card_class hm]

/-- On its own segment, a family member has norm `p^{−(n−1)}`. -/
lemma padicNorm_eval_eCl (m : Fin h) {k : ℕ} (hk : k ∈ segF p h m) :
    padicNorm p ((eCl p h m).eval (pole k)) = (p : ℚ)⁻¹ ^ (clSize h p m - 1) := by
  obtain ⟨hkh, hkm, hkmod⟩ := mem_segF.mp hk
  unfold eCl
  rw [eval_mul, eval_C, eval_prodS, padicNorm.mul, padicNorm_scF hp2 hph m.isLt,
    padicNorm_prod_poles hp2 hph sdiff_subset hkh (fun e => (mem_sdiff.mp e).2 hk), ← pow_add]
  congr 1
  have hsub : segF p h m ⊆ (range h).filter (fun l => l % p = k % p) := by
    intro l hl; obtain ⟨h1, -, h3⟩ := mem_segF.mp hl
    exact mem_filter.mpr ⟨mem_range.mpr h1, h3.trans hkmod.symm⟩
  have : (range h \ segF p h m).filter (fun l => l % p = k % p) =
      (range h).filter (fun l => l % p = k % p) \ segF p h m := by
    ext l; simp only [mem_filter, mem_sdiff]; tauto
  rw [this, card_sdiff_of_subset hsub, hkmod, card_class m.isLt, card_segF m.isLt]
  have h1 : clSize h p m ≥ (segF p h m).card := by
    rw [← card_class m.isLt, ← hkmod]
    exact card_le_card hsub
  rw [card_segF m.isLt] at h1
  generalize (m : ℕ) / p = r at h1 ⊢
  generalize clSize h p m = n at h1 ⊢
  omega

lemma GLe_four : GLe p 1 (4 : FR) := by
  have : (4 : FR) = MvPolynomial.C 4 := (map_ofNat MvPolynomial.C 4).symm
  rw [this]
  exact GLe_mono (by exact_mod_cast padicNorm.of_nat 4) (GLe_C _)

/-- **Entry bound**, pole part. -/
lemma pole_term_le (m m' : Fin h) {k : ℕ} (hk : k < h) :
    padicNorm p (((eCl p h m) * (eCl p h m')).eval (pole k) * omega h k) * (if p ≤ 2 * k + 1 then (p : ℚ) ^ 2 else 1)
      ≤ (p : ℚ) ^ (-(aE p h m + bE p h m')) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℚ) < p := by linarith
  by_cases hkA : k ∈ segF p h m ∩ segF p h m'
  · obtain ⟨hA, hB⟩ := mem_inter.mp hkA
    obtain ⟨-, hkm, hkmod⟩ := mem_segF.mp hA
    obtain ⟨-, hkm', hkmod'⟩ := mem_segF.mp hB
    have hcl : clSize h p m' = clSize h p m := by
      rw [← card_class m'.isLt, ← card_class m.isLt, ← hkmod, ← hkmod']
    have hck : clSize h p k = clSize h p m := by
      rw [← card_class hk, ← card_class m.isLt, hkmod]
    have hn1 : 1 ≤ clSize h p m := by
      rw [← card_class m.isLt]; exact card_pos.mpr ⟨m, mem_filter.mpr ⟨mem_range.mpr m.isLt, rfl⟩⟩
    have hw1 := wAtom_le_wMax (p := p) hkm hkmod
    have hw2 := wAtom_le_wMax (p := p) hkm' hkmod'
    rw [eval_mul, omega, mul_assoc, padicNorm.mul, padicNorm.mul, padicNorm.div,
      padicNorm_eval_eCl hp2 hph m hA, padicNorm_eval_eCl hp2 hph m' hB, padicNorm_dPrime_cl hp2 hph hk,
      padicNorm_pole' hp2 hph hk, hcl, hck]
    have hne : ((p : ℚ)⁻¹ ^ (clSize h p m - 1)) ≠ 0 := by positivity
    have key2 : ∀ a c d : ℚ, a ≠ 0 → a * (a * (c / a)) * d = a * c * d := fun a c d ha => by field_simp
    rw [key2 _ _ _ hne, inv_pow_eq_zpow]
    have hinv : (p : ℚ)⁻¹ = (p : ℚ) ^ (-1 : ℤ) := (zpow_neg_one _).symm
    have hsq : (p : ℚ) ^ 2 = (p : ℚ) ^ (2 : ℤ) := (zpow_natCast _ 2).symm
    unfold aE bE sCB
    unfold wAtom at hw1 hw2
    generalize (m : ℕ) / p = r at *
    generalize (m' : ℕ) / p = r' at *
    generalize wMax p m = M at *
    generalize wMax p m' = M' at *
    generalize clSize h p m = n at *
    by_cases c1 : p ∣ 2 * k + 1 <;> by_cases c2 : p ≤ 2 * k + 1
    · rw [ite_eq_left c1, ite_eq_left c2] at *
      rw [hinv, hsq, ← zpow_add₀ hp0.ne', ← zpow_add₀ hp0.ne']
      exact zpow_le_zpow_right₀ hp1 (by push_cast; omega)
    · exact absurd (Nat.le_of_dvd (by omega) c1) c2
    · rw [ite_eq_right c1, ite_eq_left c2] at *
      rw [hsq, mul_one, ← zpow_add₀ hp0.ne']
      exact zpow_le_zpow_right₀ hp1 (by push_cast; omega)
    · rw [ite_eq_right c1, ite_eq_right c2] at *
      rw [mul_one, mul_one]
      exact zpow_le_zpow_right₀ hp1 (by push_cast; omega)
  · -- off the common segment the product vanishes
    have hz : ((eCl p h m) * (eCl p h m')).eval (pole k) = 0 := by
      rw [eval_mul]
      rcases not_and_or.mp (fun h' => hkA (mem_inter.mpr h')) with h1 | h1
      · rw [eval_eCl_of_not_mem m hk h1, zero_mul]
      · rw [eval_eCl_of_not_mem m' hk h1, mul_zero]
    rw [hz, zero_mul, padicNorm.zero, zero_mul]
    positivity

end Entries


/-! ### Assembly -/

lemma GLeX_algebraMap_mul {B : ℚ} (hB : 0 ≤ B) {F : FR[X]} (hF : GLeX p B F) (c : ℚ) :
    GLeX p (padicNorm p c * B) (algebraMap ℚ FR[X] c * F) := fun k => by
  rw [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, coeff_C_mul]
  exact GLe_C_mul hB c (hF k)

/-- `Σ_m (n_m − 1) = Σ_m 2⌊m/p⌋` (pairs in a class, counted from both ends). -/
lemma sum_clSize_sub_one (h : ℕ) :
    ∑ m ∈ range h, (clSize h p m - 1) = ∑ m ∈ range h, 2 * (m / p) := by
  have hsplit : ∀ m ∈ range h, clSize h p m - 1 = ((range h).filter (fun l => l < m ∧ l % p = m % p)).card +
      ((range h).filter (fun l => m < l ∧ l % p = m % p)).card := by
    intro m hm
    have hm' := mem_range.mp hm
    rw [← card_class hm', ← card_erase_of_mem (s := (range h).filter (fun l => l % p = m % p))
      (mem_filter.mpr ⟨hm, rfl⟩), ← card_union_of_disjoint]
    · congr 1; ext l; simp only [mem_erase, mem_filter, mem_union]
      constructor
      · rintro ⟨hne, hl, hmod⟩
        rcases lt_or_gt_of_ne hne with h1 | h1
        · exact Or.inl ⟨hl, h1, hmod⟩
        · exact Or.inr ⟨hl, h1, hmod⟩
      · rintro (⟨hl, h1, hmod⟩ | ⟨hl, h1, hmod⟩)
        · exact ⟨h1.ne, hl, hmod⟩
        · exact ⟨h1.ne', hl, hmod⟩
    · rw [disjoint_left]; intro l h1 h2; simp only [mem_filter] at h1 h2; omega
  have hlow : ∀ m ∈ range h, ((range h).filter (fun l => l < m ∧ l % p = m % p)).card = m / p := by
    intro m hm
    have hm' := mem_range.mp hm
    have : (range h).filter (fun l => l < m ∧ l % p = m % p) = (segF p h m).erase m := by
      ext l; simp only [mem_filter, mem_erase, mem_segF, mem_range]; omega
    rw [this, card_erase_of_mem (self_mem_segF hm'), card_segF hm']
    generalize m / p = r
    omega
  have hswap : ∑ m ∈ range h, ((range h).filter (fun l => m < l ∧ l % p = m % p)).card =
      ∑ m ∈ range h, ((range h).filter (fun l => l < m ∧ l % p = m % p)).card := by
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun m _ => sum_congr rfl (fun l _ => ?_))
    congr 1
    exact propext ⟨fun ⟨a, b⟩ => ⟨a, b.symm⟩, fun ⟨a, b⟩ => ⟨a, b.symm⟩⟩
  rw [sum_congr rfl hsplit, sum_add_distrib, hswap, ← sum_add_distrib]
  refine sum_congr rfl (fun m hm => ?_)
  rw [hlow m hm]; ring

section Final

variable {h : ℕ} (hp2 : p ≠ 2) (hph : 2 * h < p * p)
include hp2 hph

lemma entry_GLeX (m m' : Fin h) :
    GLeX p ((p : ℚ) ^ (-(aE p h m + bE p h m'))) (GramF h (eCl p h) m m') := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℚ) < p := by linarith
  set B := (p : ℚ) ^ (-(aE p h m + bE p h m'))
  have hB : 0 ≤ B := by positivity
  set g := eCl p h m * eCl p h m'
  -- `|s s′| ≤ B`
  have hss : padicNorm p (scF p h m * scF p h m') ≤ B := by
    rw [padicNorm.mul, padicNorm_scF hp2 hph m.isLt, padicNorm_scF hp2 hph m'.isLt, inv_pow_eq_zpow,
      inv_pow_eq_zpow, ← zpow_add₀ hp0.ne']
    refine zpow_le_zpow_right₀ hp1 ?_
    unfold aE bE; push_cast; omega
  have hpole : ∀ k ∈ range h, padicNorm p (g.eval (pole k) * omega h k) *
      (if p ≤ 2 * k + 1 then (p : ℚ) ^ 2 else 1) ≤ B :=
    fun k hk => pole_term_le hp2 hph m m' (mem_range.mp hk)
  have hif : ∀ k : ℕ, (1 : ℚ) ≤ (if p ≤ 2 * k + 1 then (p : ℚ) ^ 2 else 1) := fun k => by
    split_ifs
    · nlinarith
    · exact le_rfl
  have hA : GLe p B (AfunF h g) := by
    unfold AfunF
    refine GLe_add ?_ ?_
    · rw [polyPart_eCl]
      exact GLe_mono hss (GLe_muF_C_mul (zlPoly_polyPart hp2 m m') _)
    · have hs : GLe p B (∑ k ∈ range h, MvPolynomial.C (g.eval (pole k) * omega h k) * SpartF k) := by
        refine GLe_sum _ hB _ (fun k hk => ?_)
        exact GLe_mono (hpole k hk) (GLe_mul (padicNorm.nonneg _) (by split_ifs <;> positivity) (GLe_C _)
          (GLe_SpartF hp2 hph (mem_range.mp hk)))
      simpa using GLe_mul zero_le_one hB (GLe_four hp2 hph) hs
  have hBB : GLe p B (BfunF h g) := by
    unfold BfunF
    have hs : GLe p B (∑ k ∈ range h, MvPolynomial.C (g.eval (pole k) * omega h k) * qF ^ (2 * k + 1)) := by
      refine GLe_sum _ hB _ (fun k hk => ?_)
      have hq : GLe p 1 (qF ^ (2 * k + 1)) := by simpa using GLe_pow (p := p) zero_le_one GLe_qF (2 * k + 1)
      refine GLe_mono ?_ (GLe_mul (padicNorm.nonneg _) zero_le_one (GLe_C _) hq)
      rw [mul_one]
      exact (le_mul_of_one_le_right (padicNorm.nonneg _) (hif k)).trans (hpole k hk)
    have h4 : GLe p 1 (-4 : FR) := GLe_neg (GLe_four hp2 hph)
    simpa using GLe_mul zero_le_one hB h4 hs
  show GLeX p B (LamF h g)
  unfold LamF
  exact GLeX_add (GLeX_C hB hA) (GLeX_X_mul hB (GLeX_C hB hBB))

/-- **The class bound.** For an odd prime `p` with `2h < p²`: `‖Δ^F_h‖_p ≤ p^{classBd h p}`. -/
theorem classBound_DeltaF : GLeX p ((p : ℚ) ^ (classBd h p : ℤ)) (DeltaF h) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℚ) < p := by linarith
  set e := eCl p h
  have hdeg : ∀ i, (e i).natDegree < h := fun i => natDegree_eCl i
  -- the Gram determinant
  have hG := det_GLeX (GramF h e) (fun m => (p : ℚ) ^ (-aE p h m)) (fun m => (p : ℚ) ^ (-bE p h m))
    (fun _ => by positivity) (fun _ => by positivity) (fun m m' => by
      rw [← zpow_add₀ hp0.ne', ← neg_add]; exact entry_GLeX hp2 hph m m')
  -- the coefficient determinant
  have hC2 := padicNorm_det_CoefM_sq (p := p) e hdeg
    (fun m k hmk => eval_eCl_of_not_mem m k.isLt (fun hk => by
      have := (mem_segF.mp hk).2.1
      exact absurd hmk (not_lt.mpr (by exact_mod_cast this))))
    (fun m => eval_eCl_self m)
  have hD : ∀ m : Fin h, padicNorm p (dPrime h m) = (p : ℚ) ^ (-((clSize h p m - 1 : ℕ) : ℤ)) := fun m => by
    rw [padicNorm_dPrime_cl hp2 hph m.isLt, inv_pow_eq_zpow]
  have hdetC : (CoefM e).det ≠ 0 := by
    intro h0
    rw [h0, padicNorm.zero] at hC2
    have : (0 : ℚ) < ∏ m : Fin h, padicNorm p (dPrime h m) :=
      prod_pos (fun m _ => lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero (dPrime_ne_zero h m)).symm)
    simp at hC2; linarith
  -- `Δ = (det C)^{−2} det G`
  have hEq : DeltaF h = algebraMap ℚ FR[X] (((CoefM e).det)⁻¹ ^ 2) * (GramF h e).det := by
    rw [det_GramF e hdeg, ← mul_assoc, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hdetC),
      map_one, one_mul]
  rw [hEq]
  refine GLeX_mono ?_ (GLeX_algebraMap_mul (by positivity) hG _)
  -- the exponent count
  rw [inv_pow, ← one_div, padicNorm.div, padicNorm.one, padicNorm_pow (ℓ := p), hC2, prod_congr rfl (fun m _ => hD m), zpow_prod_eq _ hp0.ne',
    zpow_prod_eq _ hp0.ne', zpow_prod_eq _ hp0.ne', one_div, ← zpow_neg, ← zpow_add₀ hp0.ne', ← zpow_add₀ hp0.ne']
  refine zpow_le_zpow_right₀ hp1 ?_
  -- `Σ (n_m − 1) − Σ (a_m + b_m) = classBd`
  have hsum := sum_clSize_sub_one (p := p) h
  rw [← Fin.sum_univ_eq_sum_range (fun m => clSize h p m - 1) h,
    ← Fin.sum_univ_eq_sum_range (fun m => 2 * (m / p)) h] at hsum
  have hcb : (classBd h p : ℤ) = ∑ m : Fin h, ((sCB p h m : ℕ) : ℤ) := by
    unfold classBd
    rw [← Fin.sum_univ_eq_sum_range (fun m => 2 * (m / p) + 1 + wMax p m - clSize h p m) h]
    push_cast; rfl
  have hsumZ : ∑ m : Fin h, ((clSize h p m - 1 : ℕ) : ℤ) = ∑ m : Fin h, ((2 * ((m : ℕ) / p) : ℕ) : ℤ) := by
    exact_mod_cast hsum
  have key : -∑ m : Fin h, -((clSize h p m - 1 : ℕ) : ℤ) + (∑ m : Fin h, -aE p h m + ∑ m : Fin h, -bE p h m) =
      ∑ m : Fin h, ((sCB p h m : ℕ) : ℤ) := by
    rw [sum_neg_distrib, neg_neg, hsumZ, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun m _ => ?_)
    unfold aE bE
    push_cast
    omega
  rw [hcb, ← key]

end Final

end Chi2Irr
