import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.LinearAlgebra.LinearIndependent
variable [Field K] [AddCommGroup V] [Module K V]
example (f : V →ₗ[K] V)
  (μ ν : K) (hμν : μ ≠ ν)
  (x y : V) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
  (hx : f x = μ • x) (hy : f y = ν • y) :
  ∀ a b : K,
    a • x + b • y = 0 → a = 0 ∧ b = 0 := by
intro a b hab
have :=
calc (μ - ν) • a • x
    = (a • μ • x + b • ν • y) -
    ν • (a• x + b• y) := by module
  _= f (a • x + b • y) -
    ν • (a• x + b• y) := by simp [hx, hy]
  _= 0 := by simp [hab]
simp_all [sub_eq_zero]

variable [Field L_1]
