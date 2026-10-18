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
