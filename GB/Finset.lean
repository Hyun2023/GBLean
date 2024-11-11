import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max


def Finset.ToList [LinearOrder T] (A : Finset T) : List T :=
  match Finset.min A with
  | some m => m::(Finset.ToList (Finset.erase A m))
  | none => []
