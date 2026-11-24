namespace LeanPlayground.Logic

variable {p q r : Prop}

/-- Term mode: a proof is just a function that builds the conclusion. -/
theorem and_swap : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

/-- Tactic mode: the same style of fact, with case analysis on `∨`. -/
theorem or_swap : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem and_or_distrib : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · rintro ⟨hp, hq | hr⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

/-- This De Morgan law holds constructively... -/
theorem not_or_iff : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩

/-- ...but the forward direction of this one needs classical logic (`by_cases`). -/
theorem not_and_iff : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inr fun hq => h ⟨hp, hq⟩
    · exact Or.inl hp
  · rintro (hnp | hnq) ⟨hp, hq⟩
    · exact hnp hp
    · exact hnq hq

end LeanPlayground.Logic
