import Mathlib

theorem onlyfr_private_line_points {P L : Type*} [DecidableEq P] [DecidableEq L]
    (pts : L → Finset P) (lines : Finset L) (l : L) (hl : l ∈ lines)
    (uniqueLine : ∀ p r : P, p ≠ r → ∀ a b : L,
      p ∈ pts a → r ∈ pts a → p ∈ pts b → r ∈ pts b → a = b) :
    (pts l).card ≤ ((pts l).filter (fun p => ∀ a ∈ lines.erase l, p ∉ pts a)).card +
      (lines.card - 1) := by
  classical
  let shared := (lines.erase l).biUnion (fun a => pts l ∩ pts a)
  have hone (a : L) (ha : a ∈ lines.erase l) : (pts l ∩ pts a).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp r hr
    by_contra h
    have e := uniqueLine p r h l a (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hr).1
      (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hr).2
    exact (Finset.ne_of_mem_erase ha) e.symm
  have hs : shared.card ≤ (lines.erase l).card := by
    calc
      shared.card ≤ ∑ a ∈ lines.erase l, (pts l ∩ pts a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ lines.erase l, 1 := Finset.sum_le_sum hone
      _ = _ := by simp
  let priv := (pts l).filter (fun p => ∀ a ∈ lines.erase l, p ∉ pts a)
  have cover : pts l ⊆ priv ∪ shared := by
    intro p hp
    by_cases h : ∀ a ∈ lines.erase l, p ∉ pts a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
    · push_neg at h
      obtain ⟨a, ha, hpa⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_inter.mpr ⟨hp, hpa⟩⟩)
  calc
    (pts l).card ≤ (priv ∪ shared).card := Finset.card_le_card cover
    _ ≤ priv.card + shared.card := Finset.card_union_le _ _
    _ ≤ priv.card + (lines.card - 1) := Nat.add_le_add_left ((Finset.card_erase_of_mem hl) ▸ hs) _
