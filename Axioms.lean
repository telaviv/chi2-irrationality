import Chi2Irrational

/- # Axiom audit

Run `lake env lean Axioms.lean`. Every line should print `[propext, Classical.choice, Quot.sound]`. -/

-- The main theorems
#print axioms Chi2Irr.chi2_one_third_irrational
#print axioms Chi2Irr.chi2_one_fifth_irrational

-- Endgame: Lemma E and the conditional main theorem
#print axioms Chi2Irr.irrational_of_poly_approx
#print axioms Chi2Irr.irrational_of_bounds

-- The machine and Lemma 1 (pole expansion)
#print axioms Chi2Irr.natDegree_Delta_le
#print axioms Chi2Irr.eval_Delta
#print axioms Chi2Irr.powSum_eq_tsum
#print axioms Chi2Irr.pole_series
#print axioms Chi2Irr.Lam_eq
#print axioms Chi2Irr.aeval_chi2_Delta

-- The arithmetic bound
#print axioms Chi2Irr.classBound_DeltaF
#print axioms Chi2Irr.lemma9_DeltaF
#print axioms Chi2Irr.ord_DeltaP
#print axioms Chi2Irr.qdeg_clearE_DeltaF
#print axioms Chi2Irr.twoAdic_Delta
#print axioms Chi2Irr.denQ_int
#print axioms Chi2Irr.arith_denQ

-- Theorem B with the two dual certificates
#print axioms Chi2Irr.Cert.Q3.analytic
#print axioms Chi2Irr.Cert.Q5.analytic

-- Lemma P (nonvanishing)
#print axioms Chi2Irr.Delta_eval_ne_zero_of_det
#print axioms Chi2Irr.muPoly_split
#print axioms Chi2Irr.red_mul_muPoly
#print axioms Chi2Irr.resid_diag_D
#print axioms Chi2Irr.block_SL
#print axioms Chi2Irr.block_D
#print axioms Chi2Irr.lemmaP
#print axioms Chi2Irr.nonvan_three
#print axioms Chi2Irr.nonvan_five
#print axioms Chi2Irr.Q.theoremQ
#print axioms Chi2Irr.Q.arith_q
#print axioms Chi2Irr.Q.twoAdic_odd
#print axioms Chi2Irr.Q.twoAdic_even
#print axioms Chi2Irr.Q.nonvan_q
#print axioms Chi2Irr.Q.analytic_odd
#print axioms Chi2Irr.Q.analytic_even
#print axioms Chi2Irr.Q.margin_odd
#print axioms Chi2Irr.Q.margin_even
#print axioms Chi2Irr.Q.theoremQ4
#print axioms Chi2Irr.Q.twoAdic_even_sharp
#print axioms Chi2Irr.Q.cert_newQ
#print axioms Chi2Irr.Q.margin_newQ
-- Theorem Q4′ (numerator 2): χ₂(2/q) for odd q ≥ 175
#print axioms Chi2Irr.QZ.theoremQ4num
#print axioms Chi2Irr.QZ.map_DeltaF_Z
#print axioms Chi2Irr.QZ.irrational_of_boundsZ
#print axioms Chi2Irr.QZ.arith_z
#print axioms Chi2Irr.QZ.twoAdic_num
#print axioms Chi2Irr.QZ.nonvan_z
#print axioms Chi2Irr.QZ.lemmaP_norm
#print axioms Chi2Irr.QZ.analytic_z
#print axioms Chi2Irr.QZ.margin_z
-- Theorem T: Ti₂(1/q) ∉ ℚ for q ≥ 6
#print axioms Chi2Irr.TiQ.theoremT
#print axioms Chi2Irr.TiQ.arith_t
#print axioms Chi2Irr.TiQ.twoAdic_odd_t
#print axioms Chi2Irr.TiQ.twoAdic_even_t
#print axioms Chi2Irr.TiQ.nonvan_t
#print axioms Chi2Irr.TiQ.analytic_t
#print axioms Chi2Irr.TiQ.cert_t6
#print axioms Chi2Irr.TiQ.margin_t6
#print axioms Chi2Irr.TiQ.margin_t_odd
#print axioms Chi2Irr.TiQ.margin_t_even
#print axioms Chi2Irr.TiQ.map_DeltaFT
-- Theorem T₅: Ti₂(1/q) ∉ ℚ for q ≥ 5 (Lemma M at odd q, the q = 5 certificate)
#print axioms Chi2Irr.TiQ.theoremT5
#print axioms Chi2Irr.TiQ.twoAdic_odd_M
#print axioms Chi2Irr.TiQ.cert_t5
#print axioms Chi2Irr.TiQ.margin_t5
#print axioms Chi2Irr.TiQ.M.DeltaT_eq_Cb
#print axioms Chi2Irr.TiQ.M.det_block
#print axioms Chi2Irr.TiQ.M.boundA
#print axioms Chi2Irr.TiQ.M.Om_bound
#print axioms Chi2Irr.TiQ.M.Am_bound
#print axioms Chi2Irr.TiQ.M.err_bound
#print axioms Chi2Irr.TiQ.M.twoAdic_DeltaT_M
