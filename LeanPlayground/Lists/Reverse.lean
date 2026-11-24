namespace LeanPlayground.Lists

variable {α : Type}

/-- List reversal from scratch: quadratic, but easy to reason about. -/
def rev : List α → List α
  | [] => []
  | x :: xs => rev xs ++ [x]

#eval rev [1, 2, 3, 4] -- [4, 3, 2, 1]

theorem rev_append (xs ys : List α) : rev (xs ++ ys) = rev ys ++ rev xs := by
  induction xs with
  | nil => simp [rev]
  | cons x xs ih => simp [rev, ih]

theorem rev_rev (xs : List α) : rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, rev_append, ih]

theorem length_rev (xs : List α) : (rev xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, ih]

/-- A linear-time, tail-recursive version using an accumulator. -/
def revAcc : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

/-- The accumulator must be generalized for the induction hypothesis to apply. -/
theorem revAcc_eq (xs acc : List α) : revAcc xs acc = rev xs ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [revAcc, rev, ih]

theorem revAcc_nil (xs : List α) : revAcc xs [] = rev xs := by
  simp [revAcc_eq]

end LeanPlayground.Lists
