import GB.Monomial
import GB.Polynomial
open Monomial

-- TODO
-- 1. Finish the definition of S-Polynomial.
-- 2. State and Prove some facts related to S Polynomial will be used in Buchberger or F4 alg


-- Definition of S-Polynomial
-- ((LCM (LM f) (LM g)) / (LT f)) * f - ((LCM (LM f) (LM g)) / (LT g)) * g
def Spol_help [CommRing R] (f g : MvPolynomial σ R) (f_NE : f ≠ 0) (g_NE : g ≠ 0) : MvPolynomial σ R :=
  sorry
-- def Spol [CommRing R] [DecidableEq R] (f g : MvPolynomial σ R) : MvPolynomial σ R :=
--   if f_NE : f = 0 then 0 else (if g_NE : g = 0 then 0 else Spol_help f g f_NE g_NE)
