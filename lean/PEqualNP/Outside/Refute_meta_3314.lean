import Mathlib
import PEqualNP.Defs

theorem onlyfr_refute_L_meta_3314 : ¬ (∀ (x1 : (Fin (14 : ℕ) → Bool) → Prop),   ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),     PEqualNP.MetaComplexity.Monotone2 x2 ∧       x2.size ≤ (25 : ℕ) ∧         (14 : ℕ) ≤ x4 ∧           x4 < x5 ∧             x5 < (14 : ℕ) + x2.size ∧               (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))]) ∧                 have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;                 have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;                 have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;                 have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];                 x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false) := by
  classical
  intro h
  let a : Fin 14 → Bool := fun k => (129 : ℕ).testBit k.val
  obtain ⟨C, op, i, j, rows, _, _, _, _, _, ⟨hop, hrows⟩, hr⟩ := h (fun x => x ≠ a)
  subst op
  have hfirst : rows.1 = 129 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
    rcases hrows with h | h | h <;> simp [h]
  have hm : Maximal (fun x : Fin 14 → Bool => ¬ x ≠ a) a := by
    constructor
    · simp
    · intro b hb _
      have he : b = a := by simpa using hb
      exact le_of_eq he
  dsimp only at hr
  obtain ⟨hne, _, _, _, hmax⟩ := hr
  rw [hfirst] at hne
  rcases hmax a hm with ⟨he, _⟩ | hz
  · cases he
  · change (C.wires (List.ofFn a)).getD i false ≠ (C.wires (List.ofFn a)).getD j false at hne
    change PEqualNP.CircuitLowerBounds.GateOp.or.eval
      [(C.wires (List.ofFn a)).getD i false, (C.wires (List.ofFn a)).getD j false] = false at hz
    revert hne hz
    generalize (C.wires (List.ofFn a)).getD i false = u
    generalize (C.wires (List.ofFn a)).getD j false = v
    cases u <;> cases v <;> decide
