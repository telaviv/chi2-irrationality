/-
# The target statements

`χ₂(1/5) ∉ ℚ` and `χ₂(1/3) ∉ ℚ`, with `Irrational` from Mathlib.
-/
import Chi2Irrational.Defs

namespace Chi2Irr

/-- `χ₂(1/5)` is irrational. -/
def Chi2OneFifthIrrational : Prop := Irrational (chi2 (1 / 5))

/-- `χ₂(1/3)` is irrational. -/
def Chi2OneThirdIrrational : Prop := Irrational (chi2 (1 / 3))

end Chi2Irr
