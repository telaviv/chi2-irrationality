/-
# χ₂(1/3) and χ₂(1/5) are irrational

The main theorems are `Chi2Irr.chi2_one_third_irrational` and `Chi2Irr.chi2_one_fifth_irrational`
(`Chi2Irrational/Arith/Assembly.lean`). See `README.md`.
-/
import Chi2Irrational.Analytic.Andreief
import Chi2Irrational.Analytic.Discrete
import Chi2Irrational.Analytic.Dual
import Chi2Irrational.Analytic.Helpers
import Chi2Irrational.Analytic.Nodes
import Chi2Irrational.Analytic.Polya
import Chi2Irrational.Analytic.PsiCalc
import Chi2Irrational.Analytic.SlotDet
import Chi2Irrational.Analytic.StepMu
import Chi2Irrational.Analytic.TheoremB
import Chi2Irrational.Arith.Assembly
import Chi2Irrational.Arith.ClassBound
import Chi2Irrational.Arith.ClassCount
import Chi2Irrational.Arith.Defs
import Chi2Irrational.Arith.Free
import Chi2Irrational.Arith.Gauss
import Chi2Irrational.Arith.Lemma9
import Chi2Irrational.Arith.PoleOrder
import Chi2Irrational.Arith.PrimeSums
import Chi2Irrational.Arith.QAdic
import Chi2Irrational.Arith.Special
import Chi2Irrational.Arith.TwoAdic
import Chi2Irrational.Arith.TwoAdicBasis
import Chi2Irrational.Arith.TwoAdicEntries
import Chi2Irrational.Cert.Core
import Chi2Irrational.Cert.DataQ3
import Chi2Irrational.Cert.DataQ5
import Chi2Irrational.Cert.Instance
import Chi2Irrational.Cert.Q3
import Chi2Irrational.Cert.Q5
import Chi2Irrational.Criterion
import Chi2Irrational.Defs
import Chi2Irrational.Interval.Basic
import Chi2Irrational.Interval.Log
import Chi2Irrational.Machine
import Chi2Irrational.MainCond
import Chi2Irrational.NonVan.BlockMat
import Chi2Irrational.NonVan.Blocks
import Chi2Irrational.NonVan.ClassData
import Chi2Irrational.NonVan.Counting
import Chi2Irrational.NonVan.EntryBounds
import Chi2Irrational.NonVan.Gram
import Chi2Irrational.NonVan.LAdic
import Chi2Irrational.NonVan.LemmaP
import Chi2Irrational.NonVan.NonVanQ
import Chi2Irrational.NonVan.PoleTerm
import Chi2Irrational.NonVan.ProgAdic
import Chi2Irrational.NonVan.Progression
import Chi2Irrational.NonVan.Residues
import Chi2Irrational.NonVan.Setup
import Chi2Irrational.NonVan.Sigma
import Chi2Irrational.PNT.Port.Consequences
import Chi2Irrational.PNT.Port.Fourier
import Chi2Irrational.PNT.Port.SmoothExistence
import Chi2Irrational.PNT.Port.Sobolev
import Chi2Irrational.PNT.Port.Wiener
import Chi2Irrational.PNT.PrimeSums
import Chi2Irrational.PNT.Theta
import Chi2Irrational.PoleExpansion
import Chi2Irrational.PoleSeries
import Chi2Irrational.Statement
