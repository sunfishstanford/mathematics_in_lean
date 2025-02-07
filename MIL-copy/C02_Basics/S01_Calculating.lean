import MIL.Common
import Mathlib.Data.Real.Basic

-- An example.
example (a b c d : ℝ) : a * b * c * d = b * d * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
  rw [mul_comm b ]
  rw [mul_assoc]
  rw [ mul_comm]

example (a b c d: ℝ): a * b *c*d = d*a*b*c := by
  rw [mul_comm d]

#check add_mul 1 2 3

-- Try these.
example (a b c : ℝ) : a * (b * c) = b * (c * a)
 := by
  rw [← mul_assoc]
  rw [mul_comm]
  rw [← mul_assoc]
  rw [mul_comm]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  #check mul_comm
  #check add_mul a b c
  rw [← mul_assoc]
  rw [mul_comm]
  rw [← mul_assoc]
  rw [mul_comm c]
  rw [mul_comm]


-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp']
  rw [mul_comm b]
  rw [sub_self]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c d: ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check (mul_assoc a b (c*d): (a*b)*(c*d) = a* (b*(c*d)))
#check add_mul
#check mul_add
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _=a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end

-- Try these. For the second, use the theorems listed underneath.
#check sub_self
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add]
  rw [←add_assoc (a*c+a*d)]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a*(c+d) + b*(c+d) := by
      rw[add_mul]
    _= a*c + a*d + (b*c+b*d) := by
      rw[mul_add a, mul_add b]
    _= a*c + a*d + b*c + b*d := by
      rw[← add_assoc (a*c+a*d)]


example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc
    (a + b) * (a - b) = a*(a-b)+ b*(a-b):= by
      rw [add_mul]
    _= a*a - a*b + (b*a - b*b) := by
      rw [mul_sub, mul_sub]
    _= a^2 - a*b + (b*a - b^2) := by
      rw [pow_two,pow_two]
    _= a^2 - a*b + b*a - b^2 := by
      rw [← add_sub ]
    _= a^2 + -(a*b) + b*a - b^2 := by
      rw [sub_eq_add_neg (a^2)]
    _= a^2 + -(a*b) + (a*b) - b^2 := by
      rw [mul_comm (b)]
    _= a^2 + (-(a*b) + (a*b)) - b^2 := by
      rw [add_assoc (a^2)]
    _= a^2 + (0) - b^2 := by
      rw [neg_add_cancel]
    _= a^2 - b^2 := by
      rw [add_zero]



#check mul_comm
#check neg_eq_neg_one_mul
#check sub_eq_add_neg
#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
#check one_mul
#check neg_add_cancel


end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]


def sameType {a b : Type} (x : a) (y : b) : Nat :=
  if h : a = b then 1 else 0

-- Examples of usage
#eval sameType 3 5       -- Both are Nat, so it returns 1
#eval sameType 3 "hello" -- Nat vs String, so it returns 0
#eval sameType true false -- Both are Bool, so it returns 1
