import PEqualNP.Outside.PrivateLinePoints

namespace Onlyfr.PrivateLineAudit

theorem lower_bound {P L : Type*} [DecidableEq P] [DecidableEq L]
    (pts : L → Finset P) (S : Finset L) (l : L) (hl : l ∈ S) (q : ℕ)
    (hdegree : (pts l).card = q + 1)
    (uniqueLine : ∀ p r : P, p ≠ r → ∀ a b : L,
      p ∈ pts a → r ∈ pts a → p ∈ pts b → r ∈ pts b → a = b) :
    q + 2 - S.card ≤ ((pts l).filter (fun p => ∀ a ∈ S.erase l, p ∉ pts a)).card := by
  have h := onlyfr_private_line_points pts S l hl uniqueLine
  have hs : 0 < S.card := Finset.card_pos.mpr ⟨l, hl⟩
  omega

theorem exists_other_line {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hsmall : ∀ l, Fintype.card {p : Fin n // I p l} < n)
    (hjoin : ∀ p r : Fin n, p ≠ r → ∃ a, I p a ∧ I r a)
    (l p : Fin n) (hp : I p l) : ∃ a, a ≠ l ∧ I p a := by
  classical
  have hout : ∃ r : Fin n, ¬ I r l := by
    by_contra h
    push_neg at h
    have hall : (Finset.univ.filter (fun r : Fin n => I r l)) = Finset.univ := by
      ext r
      simp [h r]
    have hc := hsmall l
    rw [Fintype.card_subtype, hall, Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨r, hr⟩ := hout
  have hpr : p ≠ r := by rintro rfl; exact hr hp
  obtain ⟨a, hpa, hra⟩ := hjoin p r hpr
  exact ⟨a, by rintro rfl; exact hr hra, hpa⟩

theorem no_private_full {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hsmall : ∀ l, Fintype.card {p : Fin n // I p l} < n)
    (hjoin : ∀ p r : Fin n, p ≠ r → ∃ a, I p a ∧ I r a)
    (l : Fin n) :
    (Finset.univ.filter (fun p : Fin n => I p l ∧
      ∀ a ∈ (Finset.univ : Finset (Fin n)).erase l, ¬ I p a)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨_, hpl, hprivate⟩ := Finset.mem_filter.mp hp
  obtain ⟨a, hal, hpa⟩ := exists_other_line I hsmall hjoin l p hpl
  exact hprivate a (Finset.mem_erase.mpr ⟨hal, Finset.mem_univ _⟩) hpa

theorem no_private_plane {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hq : 199 ≤ q) (hn : n = q ^ 2 + q + 1)
    (hdegree : ∀ l, Fintype.card {p : Fin n // I p l} = q + 1)
    (hjoin : ∀ p r : Fin n, p ≠ r → ∃! a, I p a ∧ I r a)
    (l : Fin n) :
    (Finset.univ.filter (fun p : Fin n => I p l ∧
      ∀ a ∈ (Finset.univ : Finset (Fin n)).erase l, ¬ I p a)) = ∅ := by
  apply no_private_full I
  · intro a
    rw [hdegree a, hn]
    have hpos : 0 < q ^ 2 := pow_pos (by omega : 0 < q) _
    omega
  · intro p r hpr
    exact (hjoin p r hpr).exists

end Onlyfr.PrivateLineAudit
