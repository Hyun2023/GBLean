-- import GB.CFinsupp
import GB.Monomial
import GB.Polynomial
import GB.S_Poly
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division


section Reduction
variable
[DecidableEq (Monomial σ )]

-- Reduction Procedure, aka multivariate divison algorithm
def red [Field R] (f : MvPolynomial σ R) : MvPolynomial σ R := sorry
