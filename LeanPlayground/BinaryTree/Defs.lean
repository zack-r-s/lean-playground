namespace LeanPlayground.BinaryTree

/-- A binary tree with a value at each node. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr

namespace Tree

variable {α : Type}

def size : Tree α → Nat
  | leaf => 0
  | node l _ r => l.size + 1 + r.size

/-- In-order traversal. -/
def toList : Tree α → List α
  | leaf => []
  | node l x r => l.toList ++ [x] ++ r.toList

def mirror : Tree α → Tree α
  | leaf => leaf
  | node l x r => node r.mirror x l.mirror

def sample : Tree Nat :=
  node (node leaf 1 leaf) 2 (node leaf 3 leaf)

#eval sample.toList        -- [1, 2, 3]
#eval sample.mirror.toList -- [3, 2, 1]

end Tree

end LeanPlayground.BinaryTree
