# Lemma 10_e in Lean: plan (worker l10e)

Target: `twoAdic_even_sharp_proof` (exact statement of the stub in `Q/Even/Interface.lean`).
Source: `pilot_qeven/RESULT.md` §2 (Lemma 10_e), referee `REFEREE_QEVEN.md` #1–#5.
Numerical check of every inequality below on exact data: `l10e_check.py` → `l10e_check.txt` (0 violations).

Notation: `K = h`, `e = v₂(q₀) ≥ 1`, `P = ℚ⟦q⟧`, `PY = P[X]`, `m_e = e − 2(e+1)²/(3e+8)` (`= −(c(e) − e/3)`),
`t = Nat.log 2 h`, `L = t + 1` (so `2^L > h`), `R(h) = m_e h² − h(3e/2 + 4t + 4)`, `n2(h) = h − ⌈R(h)⌉`.

## Statement chain

1. **Weighted norm** (`Q/Even/WNorm.lean`). `WLe e B F :⇔ ∀ j n, |[qⁿXʲ]F|₂ ≤ B·2^{en}` on `PY` (and `WLeP` on `P`).
   Closed under `+`, `−`, finite sums, products (ultrametric + `2^{e(n₁+n₂)} = 2^{en₁}2^{en₂}`), ℚ-scalars.
   This is RESULT step 1's `v_e` (`v_e ≥ b ⇔ WLe e 2^{−b}`); no 2-adic analysis.
2. **Transfer** (`TwoAdicSharp.lean`, `padicNorm_Delta_of_WLe`). If `WLe e B ((DeltaF h).map psiP)`, `|q₀|₂ = 2^{−e}`
   and `q₀² − 1` odd, then `|coeff_k Δ_h(q₀)|₂ ≤ B`. Route: `clearE`/`aeval_clearE` and `coeff_psiP_of_EDeg0` as in
   `padicNorm_Delta_clear` / `qdeg_clearE_DeltaF` (Lemma 4′ files), with `WLeP 1 ((q²−1)^β)`.
3. **Truncation** (existing, `Arith/QAdic.lean`): `det HPser − det (Mdec M h) ∈ Jq (2M)` (proof of `ord_DeltaP`),
   so `WLe e B (Mdec M h).det` for all `M` gives `WLe e B (HPser h).det = (DeltaF h).map psiP`.
4. **Andreief** (existing `factorial_smul_det_sum_rankOne`, as in `det_Mdec_mem`):
   `h!·det Mdec = Σ_f (Π_i ccS(f i))·det X_f·det Y_f`, `f : Fin h → SIdx M h`. `|1/h!|₂ ≤ 2^h` (`vf_le`).
   If the x-keys or the y-keys of `f` repeat, a determinant vanishes (equal rows). Otherwise (`valid f`):
5. **Factor bounds** (RESULT step 3): `|phd h m|₂ ≤ 2^{−h}` (`|D(−m)| = 2^h`, `|D′(−m)| ≤ 2^{h−1}` by
   `derivative_prod`), `|phv h m|₂ ≤ 2^{−h}`, `|4ω_k|₂ ≤ 2^{h}` (`dPrime = ±k!(h−1−k)!`, `prod_pole_erase`, `vf_le`);
   `WLe 1 (C χ₂ + X)`. So `Π_i ccS(f i)` has `WLe (Π_i 2^{−ω(f i) − e·price(f i)})`, `ω(node) = h`, `ω(pole) = −h`.
6. **CoreDet** (`Q/Even/CoreDet.lean`; RESULT step 3's derivative-loss argument). For `z : Fin h → ℚ`, `U` (derivative
   rows) and `Λ ≥ 0` with `2^{−Λ} ≤ |z_i − z_j|₂` for `i ∈ U`, `z_j ≠ z_i`:
   `|det(if i∈U then j z_i^{j−1} else z_i^j)|₂ ≤ Π_{i<j, z_i≠z_j}|z_j − z_i|₂ · 2^{Λ|U|}`.
   Proof: `det = eval_z (∂_U V)`, `V = Π_{i<j}(X_j − X_i)` in `MvPolynomial (Fin h) ℚ` (`det_vandermonde`;
   `∂_a det W_U = det W_{U∪a}` since only row `a` involves `X_a`); by induction `∂_U V ∈ span_ℤ {Π_{p∉C} ℓ_p : C good}`
   (C = image of an injective choice `c : U → pairs`, `i ∈ c i`); evaluate each generator.
   (Confluent pairs are the zero factors, which must be in `C`; this is the confluent formula of step 2 without
   writing it out.)
7. **Point valuations**: node–node `|m − m′|₂ ≤ 2^{−cnt}`, `cnt = #{ℓ < L : 2^{ℓ+1} ∣ m − m′}`; node–pole `= 2`;
   pole–pole like node–node. Derivative rows sit at nodes; `Λ = Nat.log 2 Mx` (`Mx` = largest node) works.
   `(Π_{i<j})² = Π_{i≠j}`, so the exponent is `Σ_{i,j} c(i,j)` over ordered pairs.
8. **Counting** (`Q/Even/Count.lean`; RESULT step 4), for valid `f`, `I` node rows, `P = h − I` pole rows:
   (I2) `Σ_node 2m ≥ I(I−1)/2 − I + max(0, 2Mx − h)` (injection `2m + [τ=1]`), `Σ_pole (2k+1) ≥ P²`;
   (I3) `Σ_{i,j} c ≥ (I² + P²)(1 − 2^{−L}) − 2LI − LP − 2IP` (Cauchy–Schwarz on residues mod `2^{ℓ+1}`,
        `sq_sum_le_card_mul_sum_sq`; same-node pairs ≤ 2I);
   (I4) `e·max(0, 2Mx − h) − Λ·#der ≥ −h(2t+1)` (large nodes; RESULT step 5), `#der ≤ I`;
   (I5) `e(I²/2 + P²) + h(I − P) + (I − P)² − m_e h² = (3e/2+4)(I − x*h)² ≥ 0` (RESULT step 7).
   Sum: `ν(f) ≥ R(h)`, so each term has `WLe e 2^{−⌈R(h)⌉}` and `det Mdec` has `WLe e 2^{h − ⌈R(h)⌉}`.
9. **Limit**: `n2(h) log 2 ≤ (−m_e log 2 + ε)h²` eventually, and `−m_e log 2 = c2EvenSharp q` (algebra on `cE`).

## Departures from RESULT
* Cruder constants in the O(h log h) terms (pole weight `−h` instead of `2 − h + s₂(h−1)`, the `h!` of Andreief,
  `Λ = log₂(max node)` for every derivative). Leading constant unchanged: `c(e)`.
* The confluent Cauchy–Binet formula (step 2) is replaced by Andreief over ordered slot maps (already in Lean for
  Lemma 4′) plus CoreDet; same terms, no closed formula for the ∂-operator needed.

## Status (2026-11-09): done
`twoAdic_even_sharp_proof` in `Chi2Irrational/Q/Even/TwoAdicSharp.lean`; type equal to the stub (scratch
`example : type_of% @Chi2Irr.Q.twoAdic_even_sharp := @Chi2Irr.Q.twoAdic_even_sharp_proof`), axioms
`[propext, Classical.choice, Quot.sound]`. Files and the plan step they implement:
`Q/Even/WNorm.lean` (1), `Q/Even/CoreDet.lean` (6), `Q/Even/Count.lean` (8: `sum_cntL_ge`, `large_node`),
`Q/Even/Terms.lean` (5, 7, `WLe_term`), `Q/Even/NuBound.lean` (8: prices, `sum_ccP_ge`, `final_arith`, `nu_ge`),
`Q/Even/TwoAdicSharp.lean` (2, 3, 4, 9). The witness is exactly `n2(h) = h − ⌈R(h)⌉` (`n2E`), the function
tested in `l10e_check.py` §4.
