import PEqualNP.Outside.L_meta_693

theorem onlyfr_incidence_extension : ∀ (n : ℕ) (I : Fin n → Fin n → Prop) (D : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 D →
    (∀ p l : Fin n, I p l → PEqualNP.MetaComplexity.circuitFun (n+n) D (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) = true) →
    (∀ x : Fin (n+n) → Bool, (¬ ∃ p l : Fin n, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) → PEqualNP.MetaComplexity.circuitFun (n+n) D x = false) →
    (∀ x : Fin (n+n) → Bool, PEqualNP.MetaComplexity.circuitFun (n+n) D x = true ↔ ∃ p l : Fin n, l ∈ (Finset.univ : Finset (Fin n)) ∧ I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) := by
  classical
  intro n I D hm hp hz x
  constructor
  · intro h
    by_contra hn
    exact Bool.noConfusion (h.symm.trans (hz x (by simpa using hn)))
  · rintro ⟨p, l, _, hi, hx, hy⟩
    apply PEqualNP.Outside.L_meta_693.InputCircuit693.wires_mono D hm
      (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) x _ D.output (hp p l hi)
    intro z h
    rcases of_decide_eq_true h with he | he
    · simpa [he] using hx
    · simpa [he] using hy
