namespace LeanPlayground.GaussSum

/-- The sum `0 + 1 + ⋯ + n`, defined by recursion. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 10 -- 55

/-- Small concrete facts can be checked by computation. -/
example : sumTo 100 = 5050 := by decide

/-- Gauss's formula, proved by induction. -/
theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo, Nat.mul_add, ih]
    grind

end LeanPlayground.GaussSum
