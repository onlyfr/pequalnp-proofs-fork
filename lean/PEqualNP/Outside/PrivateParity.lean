import PEqualNP.Outside.PrivateDropSmall

namespace Onlyfr.PrivateParity

private theorem countSwap {A B : Type*} (U : Finset A) (V : Finset B)
    (R : A → B → Prop) [DecidableRel R] :
    ∑ a ∈ U, (V.filter (R a)).card = ∑ b ∈ V, (U.filter (fun a => R a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

private theorem exact_of_total {A : Type*} (U : Finset A) (f : A → ℕ) (k : ℕ)
    (hle : ∀ a ∈ U, f a ≤ k) (ht : U.card * k ≤ ∑ a ∈ U, f a) :
    ∀ a ∈ U, f a = k := by
  intro a ha
  by_contra! hh
  have hlt : f a < k := lt_of_le_of_ne (hle a ha) hh
  have h := Finset.sum_lt_sum hle ⟨a, ha, hlt⟩
  simp at h
  omega

private theorem one_of_total {A : Type*} (U : Finset A) (f : A → ℕ)
    (hle : ∀ a ∈ U, 1 ≤ f a) (ht : (∑ a ∈ U, f a) ≤ U.card) :
    ∀ a ∈ U, f a = 1 := by
  intro a ha
  by_contra! hh
  have hlt : 1 < f a := lt_of_le_of_ne (hle a ha) (Ne.symm hh)
  have h := Finset.sum_lt_sum hle ⟨a, ha, hlt⟩
  simp at h
  omega

section
variable {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
private abbrev pts (l : Fin n) := Finset.univ.filter (fun p => I p l)
private abbrev pencil (p : Fin n) := Finset.univ.filter (I p)

private theorem point_degree {q : ℕ} (hq : 0 < q) (hn : n = q^2+q+1)
    (hd : ∀ l, (pts I l).card = q+1)
    (hj : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (p : Fin n) :
    (pencil I p).card = q+1 := by
  classical
  let U := (Finset.univ : Finset (Fin n)).erase p
  have hrow (r) (hr : r ∈ U) : ((pencil I p).filter (I r)).card = 1 := by
    obtain ⟨a, ha, hu⟩ := hj p r (Finset.ne_of_mem_erase hr).symm
    have he : (pencil I p).filter (I r) = {a} := by
      ext b
      simp only [pencil, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨hu b, fun e => e ▸ ha⟩
    simp [he]
  have hcol (a) (ha : a ∈ pencil I p) : (U.filter (fun r => I r a)).card = q := by
    have he : U.filter (fun r => I r a) = (pts I a).erase p := by ext r; simp [U, pts, and_assoc]
    have hp : p ∈ pts I a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    rw [he, Finset.card_erase_of_mem hp, hd]
    omega
  have h := countSwap U (pencil I p) I
  rw [Finset.sum_const_nat hrow, Finset.sum_const_nat hcol] at h
  have hc : U.card = n-1 := by simp [U]
  rw [hc] at h
  have he : (q+1)*q = (pencil I p).card*q := by
    rw [← h, mul_one, show n-1 = q^2+q by omega]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hq he).symm

private theorem meet_le (hj : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    {a b : Fin n} (hab : a ≠ b) : ((pts I a).filter (fun p => I p b)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  by_contra h
  obtain ⟨hp, hpb⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr, hrb⟩ := Finset.mem_filter.mp hr
  exact hab ((hj p r h).unique ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hr).2⟩ ⟨hpb, hrb⟩)

private theorem meet_one {q : ℕ} (hq : 0 < q) (hn : n = q^2+q+1)
    (hd : ∀ l, (pts I l).card = q+1)
    (hj : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    {a b : Fin n} (hab : a ≠ b) : ((pts I a).filter (fun p => I p b)).card = 1 := by
  classical
  let V := (Finset.univ : Finset (Fin n)).erase a
  have hrow (p) (hp : p ∈ pts I a) : (V.filter (I p)).card = q := by
    have he : V.filter (I p) = (pencil I p).erase a := by ext t; simp [V, pencil, and_assoc]
    rw [he, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩),
      point_degree I hq hn hd hj]
    omega
  have h := countSwap (pts I a) V I
  rw [Finset.sum_const_nat hrow, hd] at h
  apply exact_of_total V _ 1 (fun t ht => meet_le I hj (Finset.ne_of_mem_erase ht).symm) _ b
  · exact Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
  · rw [← h]
    simp [V, hn, pow_two, Nat.add_mul]

end

/-- An odd order plane admits no set of q+2 lines without a private point. -/
theorem private_at_boundary {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (ho : Odd q) (hn : n = q^2+q+1)
    (hd : ∀ a, Fintype.card {p // I p a} = q+1)
    (hj : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (S : Finset (Fin n)) (hs : S.card = q+2) :
    ∃ l ∈ S, ∃ p, I p l ∧ ∀ a ∈ S.erase l, ¬ I p a := by
  classical
  have hd' (a) : (pts I a).card = q+1 := by simpa [pts, Fintype.card_subtype] using hd a
  by_contra! hnopriv
  have htwo (p : Fin n) (l : Fin n) (hl : l ∈ S) (hpl : I p l) :
      (S.filter (I p)).card = 2 := by
    let V := S.erase l
    have hpos (r) (hr : r ∈ pts I l) : 1 ≤ (V.filter (I r)).card := by
      obtain ⟨a, ha, hra⟩ := hnopriv l hl r (Finset.mem_filter.mp hr).2
      exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hra⟩⟩
    have h := countSwap (pts I l) V I
    have hcols (a) (ha : a ∈ V) := meet_one I (by omega : 0 < q) hn hd' hj (Finset.ne_of_mem_erase ha).symm
    rw [Finset.sum_const_nat hcols] at h
    have hvc : V.card = q+1 := by simp [V, Finset.card_erase_of_mem hl, hs]
    have hsum : (∑ r ∈ pts I l, (V.filter (I r)).card) ≤ (pts I l).card := by rw [h, hvc, hd']; simp
    have hone := one_of_total _ _ hpos hsum p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩)
    have he : V.filter (I p) = (S.filter (I p)).erase l := by ext t; simp [V, and_assoc, and_left_comm]
    rw [he, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hl, hpl⟩)] at hone
    omega
  have hout : ∃ b : Fin n, b ∉ S := by
    by_contra! hall
    have he : S = Finset.univ := Finset.eq_univ_of_forall hall
    rw [he, Finset.card_univ, Fintype.card_fin] at hs
    nlinarith
  obtain ⟨b, hb⟩ := hout
  have h := countSwap (pts I b) S I
  have hcols (a) (ha : a ∈ S) := meet_one I (by omega : 0 < q) hn hd' hj (show b ≠ a from fun e => hb (e ▸ ha))
  rw [Finset.sum_const_nat hcols, mul_one, hs] at h
  have heven : Even (∑ p ∈ pts I b, (S.filter (I p)).card) := by
    apply Finset.even_sum
    intro p _
    by_cases hh : (S.filter (I p)).Nonempty
    · obtain ⟨l, hl⟩ := hh
      rw [htwo p l (Finset.mem_filter.mp hl).1 (Finset.mem_filter.mp hl).2]
      decide
    · simp [Finset.not_nonempty_iff_eq_empty.mp hh]
  rw [h] at heven
  obtain ⟨u, hu⟩ := heven
  obtain ⟨v, hv⟩ := ho
  omega

/-- With q+3 active lines and no private points, triple points partition the lines into triples. -/
theorem private_at_next {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hn : n = q^2+q+1) (hmod : ¬ 3 ∣ q+3)
    (hd : ∀ a, Fintype.card {p // I p a} = q+1)
    (hj : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (S : Finset (Fin n)) (hs : S.card = q+3) :
    ∃ l ∈ S, ∃ p, I p l ∧ ∀ a ∈ S.erase l, ¬ I p a := by
  classical
  have hd' (a) : (pts I a).card = q+1 := by simpa [pts, Fintype.card_subtype] using hd a
  by_contra! hnopriv
  let d := fun p => (S.filter (I p)).card
  let T := Finset.univ.filter (fun p => d p = 3)
  have hone (l) (hl : l ∈ S) : (T.filter (fun p => I p l)).card = 1 := by
    let V := S.erase l
    let f := fun p => (V.filter (I p)).card
    have hpos (p) (hp : p ∈ pts I l) : 1 ≤ f p := by
      obtain ⟨a, ha, hpa⟩ := hnopriv l hl p (Finset.mem_filter.mp hp).2
      exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩⟩
    have h := countSwap (pts I l) V I
    have hc (a) (ha : a ∈ V) := meet_one I (by omega : 0 < q) hn hd' hj (Finset.ne_of_mem_erase ha).symm
    rw [Finset.sum_const_nat hc, mul_one, Finset.card_erase_of_mem hl, hs] at h
    have hsplit : (∑ p ∈ pts I l, f p) = ∑ p ∈ pts I l, (1 + (f p - 1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have := hpos p hp
      omega
    rw [Finset.sum_add_distrib] at hsplit
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hd'] at hsplit
    change (∑ p ∈ pts I l, f p) = _ at h
    have hexcess : (∑ p ∈ pts I l, (f p - 1)) = 1 := by omega
    have he : T.filter (fun p => I p l) = (pts I l).filter (fun p => d p = 3) := by
      ext p; simp [T, pts, and_comm]
    rw [he, Finset.card_filter, ← hexcess]
    apply Finset.sum_congr rfl
    intro p hp
    have hle := Finset.single_le_sum (f := fun p => f p - 1) (fun _ _ => Nat.zero_le _) hp
    rw [hexcess] at hle
    have hrel : f p = d p - 1 := by
      have he' : V.filter (I p) = (S.filter (I p)).erase l := by ext t; simp [V, and_assoc, and_left_comm]
      change (V.filter (I p)).card = (S.filter (I p)).card - 1
      rw [he', Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hl, (Finset.mem_filter.mp hp).2⟩)]
    have := hpos p hp
    split <;> omega
  have h := countSwap T S I
  have hthree (p) (hp : p ∈ T) : (S.filter (I p)).card = 3 := (Finset.mem_filter.mp hp).2
  rw [Finset.sum_const_nat hthree, Finset.sum_const_nat hone, mul_one, hs] at h
  exact hmod ⟨T.card, by omega⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Onlyfr.PrivateIncidenceDrop

theorem hdrop_199 {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hn : n = 199^2+199+1)
    (hd : ∀ a, Fintype.card {p // I p a} = 199+1)
    (hj : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (S : Finset (Fin n)) (D : Circuit) (hne : S.Nonempty) (hs : S.card ≤ 202)
    (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) :
    ∃ l ∈ S, ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase l ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      100 * E.size + 199 ≤ 100 * D.size := by
  classical
  by_cases h : S.card ≤ 200
  · exact Onlyfr.PrivateDropSmall.hdrop_small_succ I hd hj S D hne (by omega) hm hex
  obtain ⟨l, hl, p, hp, hpv⟩ : ∃ l ∈ S, ∃ p, I p l ∧ ∀ a ∈ S.erase l, ¬ I p a := by
    by_cases he : S.card = 201
    · exact private_at_boundary (q := 199) I (by decide) (by decide) hn hd hj S he
    · exact private_at_next (q := 199) I (by decide) hn (by decide) hd hj S (by omega)
  have hcard (a) : (pts I a).card = 200 := by simpa [pts, Fintype.card_subtype] using hd a
  have hk : ∃ r ∉ ({p} : Finset (Fin n)), I r l := by
    by_contra! hall
    have hsub : pts I l ⊆ {p} := by
      intro r hr
      by_contra hh
      exact hall r hh ((Finset.mem_filter.mp hr).2)
    have hc := Finset.card_le_card hsub
    simp [hcard] at hc
  have hother : ∃ a ∈ S.erase l, ∃ r, I r a := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (S.erase l).card by rw [Finset.card_erase_of_mem hl]; omega)
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < (pts I a).card by rw [hcard]; decide)
    exact ⟨a, ha, r, (Finset.mem_filter.mp hr).2⟩
  obtain ⟨E, hmE, hE, hsize⟩ := private_points_and_line_save I S l {p} D 1 (by decide)
    (fun _ => hk) hl (by simpa using And.intro hp hpv) hother hm hex
  simp only [Finset.card_singleton] at hsize
  exact ⟨l, hl, E, hmE, hE, by omega⟩

end Onlyfr.PrivateParity