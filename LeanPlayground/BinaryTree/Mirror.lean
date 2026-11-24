import LeanPlayground.BinaryTree.Defs

namespace LeanPlayground.BinaryTree.Tree

variable {α : Type}

theorem mirror_mirror (t : Tree α) : t.mirror.mirror = t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr => simp [mirror, ihl, ihr]

theorem size_mirror (t : Tree α) : t.mirror.size = t.size := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    simp only [mirror, size, ihl, ihr]
    omega

/-- Mirroring a tree reverses its in-order traversal. -/
theorem toList_mirror (t : Tree α) : t.mirror.toList = t.toList.reverse := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr => simp [mirror, toList, ihl, ihr]

end LeanPlayground.BinaryTree.Tree
