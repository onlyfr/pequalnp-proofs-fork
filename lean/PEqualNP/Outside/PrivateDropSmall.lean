import PEqualNP.Outside.PrivateIncidenceDrop

namespace Onlyfr.PrivateDropSmall

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateGateDrop Onlyfr.PrivateIncidenceDrop

theorem star_cost {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (S : Finset (Fin n)) (l : Fin n) (D : Circuit) (hl : l ∈ S)
    (hdegree : Fintype.card {p : Fin n // I p l} = q + 1)
    (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) : q ≤ D.size := by
  classical
  let pts : Finset (Fin n) := Finset.univ.filter (fun p => I p l)
  have hc : pts.card = q + 1 := by simpa [pts, Fintype.card_subtype] using hdegree
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < pts.card)
  have hrl : I r l := (Finset.mem_filter.mp hr).2
  let P := pts.erase r
  let Q := P.image (Fin.castAdd n)
  have hPcard : P.card = q := by
    have hh := Finset.card_erase_of_mem hr
    dsimp [P]
    omega
  have hQcard : Q.card = q := by
    rw [Finset.card_image_of_injective _ (Fin.castAdd_injective n n), hPcard]
  have nc (A : Finset (Fin (n+n))) (hA : A ⊆ Q) :
      ∃ x y, edgeFun I S (pin A x) ≠ edgeFun I S (pin A y) := by
    have hrA : Fin.castAdd n r ∉ A := by
      intro hh
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp (hA hh)
      have he' : p = r := Fin.castAdd_injective n n he
      subst p
      exact (Finset.mem_erase.mp hp).1 rfl
    have hlA : Fin.natAdd n l ∉ A := by
      intro hh
      obtain ⟨p, _, he⟩ := Finset.mem_image.mp (hA hh)
      exact left_ne_right p l he
    refine ⟨pairInput r l, fun _ => false, ?_⟩
    have ht : edgeFun I S (pin A (pairInput r l)) = true := by
      exact (edgeFun_true I S _).mpr ⟨r, l, hl, hrl,
        by simp [pin, hrA, pair_point], by rw [pin, if_neg hlA, pair_line]; simp⟩
    have hz : pin A (fun _ => false) = fun _ => false := by funext z; simp [pin]
    rw [ht, hz, edgeFun_zero]
    decide
  have deps (A : Finset (Fin (n+n))) (hA : A ⊆ Q) (i : Fin (n+n)) (hi : i ∈ Q \ A) :=
    point_deps I S l P hl (fun p hp => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2) A hA i hi
  obtain ⟨t, ht, _⟩ := many_inputs Q (edgeFun I S) D.size (mono_size_of_exact I S D hm hex) nc deps
  rw [hQcard] at ht
  omega

theorem empty_circuit (m : ℕ) :
    ∃ E : Circuit, Monotone2 E ∧ E.size = 0 ∧ ∀ x : Fin m → Bool, circuitFun m E x = false := by
  refine ⟨⟨[], m⟩, ?_, rfl, ?_⟩
  · intro g hg
    cases hg
  · intro x
    simp [circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_default]

theorem hdrop_small {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hdegree : ∀ a, Fintype.card {p : Fin n // I p a} = q + 1)
    (hjoin : ∀ p r : Fin n, p ≠ r → ∃! a, I p a ∧ I r a)
    (S : Finset (Fin n)) (D : Circuit) (hne : S.Nonempty)
    (hsmall : 100 * S.card + q ≤ 100 * (q + 2))
    (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) :
    ∃ removed ∈ S, ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase removed ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      100 * E.size + q ≤ 100 * D.size := by
  classical
  obtain ⟨l, hl⟩ := hne
  by_cases hsingle : S = {l}
  · have hcost := star_cost I S l D hl (hdegree l) hm hex
    obtain ⟨E, hE, hsize, hev⟩ := empty_circuit (n+n)
    refine ⟨l, hl, E, hE, ?_, ?_⟩
    · intro x
      rw [hev]
      simp [hsingle]
    · rw [hsize]
      omega
  · have hother : ∃ a ∈ S.erase l, ∃ r, I r a := by
      have hne' : (S.erase l).Nonempty := by
        by_contra hh
        have he := Finset.not_nonempty_iff_eq_empty.mp hh
        have hs : S = {l} := by
          ext a
          by_cases ha : a = l
          · subst a; simp [hl]
          · have hna : a ∉ S := by
              intro hmem
              have := Finset.mem_erase.mpr ⟨ha, hmem⟩
              rw [he] at this
              simpa using this
            simp [ha, hna]
        exact hsingle hs
      obtain ⟨a, ha⟩ := hne'
      have hc : 0 < (Finset.univ.filter (fun p : Fin n => I p a)).card := by
        have hh := hdegree a
        rw [Fintype.card_subtype] at hh
        omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp hc
      exact ⟨a, ha, r, (Finset.mem_filter.mp hr).2⟩
    let pts : Fin n → Finset (Fin n) := fun a => Finset.univ.filter (fun p => I p a)
    let P := (pts l).filter (fun p => ∀ a ∈ S.erase l, p ∉ pts a)
    have hpriv : ∀ p ∈ P, I p l ∧ ∀ a ∈ S.erase l, ¬ I p a := by
      intro p hp
      obtain ⟨hpl, hp⟩ := Finset.mem_filter.mp hp
      exact ⟨(Finset.mem_filter.mp hpl).2, fun a ha hpa => hp a ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩)⟩
    have hdeg : (pts l).card = q + 1 := by simpa [pts, Fintype.card_subtype] using hdegree l
    have hunique : ∀ p r : Fin n, p ≠ r → ∀ a b,
        p ∈ pts a → r ∈ pts a → p ∈ pts b → r ∈ pts b → a = b := by
      intro p r hpr a b hpa hra hpb hrb
      exact (hjoin p r hpr).unique
        ⟨(Finset.mem_filter.mp hpa).2, (Finset.mem_filter.mp hra).2⟩
        ⟨(Finset.mem_filter.mp hpb).2, (Finset.mem_filter.mp hrb).2⟩
    have hbound : q + 2 - S.card ≤ P.card := by
      convert Onlyfr.PrivateLineAudit.lower_bound pts S l hl q hdeg hunique using 1 <;>
        congr 1 <;> ext p <;> simp [P]
    obtain ⟨E, hE, hev, hsave⟩ := private_points_save I S l P D hl hpriv hother hm hex
    refine ⟨l, hl, E, hE, hev, ?_⟩
    omega

end Onlyfr.PrivateDropSmall

