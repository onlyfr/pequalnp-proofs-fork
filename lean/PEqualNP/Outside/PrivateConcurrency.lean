import PEqualNP.Outside.PrivateArcExact

namespace Onlyfr.PrivateConcurrency
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateArcExact

variable {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] (S : Finset (Fin n))
def pts (l : Fin n) := Finset.univ.filter (fun p => I p l)
def active := S.biUnion (pts I)
def sig (p : Fin n) := S.filter (I p)
def types := (active I S).image (sig I S)
def budget := (∑ l ∈ S, (pts I l).card) + S.card - ((active I S).card + (types I S).card)

private theorem mem_pts (p l : Fin n) : I p l ↔ p ∈ pts I l := by simp [pts]

/-- At most the support budget separates any circuit from the row upper bound. -/
theorem support_lower (ne : (active I S).Nonempty) {t : ℕ}
    (hf : HasMonoSize (n+n) (edgeFun I S) t) :
    (active I S).card + (types I S).card ≤ t+1 := by
  classical
  have ex (v) (hv : v ∈ types I S) : ∃ p ∈ active I S, sig I S p = v := Finset.mem_image.mp hv
  obtain ⟨p₀,h₀⟩ := ne
  let rep (v : Finset (Fin n)) := if h : v ∈ types I S then (ex v h).choose else p₀
  have spec (v) (h : v ∈ types I S) : rep v ∈ active I S ∧ sig I S (rep v) = v := by
    simpa only [rep,dif_pos h] using (ex v h).choose_spec
  let T := (types I S).image rep
  have tc : T.card = (types I S).card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv e
    simpa only [(spec u hu).2,(spec v hv).2] using congrArg (sig I S) e
  have sub : T ⊆ active I S := by
    intro p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    exact (spec v hv).1
  have hn : T.Nonempty := ⟨rep (sig I S p₀), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ h₀)⟩
  have h := encoded_lower (pts I) S (Equiv.refl _) (Function.Embedding.refl _) I
    (fun l _ p => mem_pts I p l) T sub hn (by
      intro p hp r hr hpr
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hr
      by_contra! agree
      have he : sig I S (rep u) = sig I S (rep v) := by
        ext l
        simp only [sig,Finset.mem_filter]
        exact and_congr_right fun hl => (mem_pts I _ l).trans ((agree l hl).trans (mem_pts I _ l).symm)
      rw [(spec u hu).2,(spec v hv).2] at he
      exact hpr (congrArg rep he)) (by simpa using hf)
  rw [tc] at h
  exact h

/-- Compute the support budget from the multiplicities in a linear incidence system. -/
theorem budget_eq
    (linear : ∀ p r a b, I p a → I r a → I p b → I r b → a ≠ b → p = r) :
    budget I S = (∑ p ∈ active I S, ((sig I S p).card - 2)) +
      (S.card - (S.filter (fun l => {l} ∈ types I S)).card) := by
  classical
  let A := active I S
  let B := A.filter (fun p => 2 ≤ (sig I S p).card)
  let V := S.filter (fun l => {l} ∈ types I S)
  let singles := V.image (fun l => ({l} : Finset (Fin n)))
  have pos (p) (hp : p ∈ A) : 0 < (sig I S p).card := by
    obtain ⟨l,hl,hi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.card_pos.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,(mem_pts I p l).mpr hi⟩⟩
  have inj : (↑B : Set (Fin n)).InjOn (sig I S) := by
    intro p hp r _ he
    have h := (Finset.mem_filter.mp hp).2
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (sig I S p).card)
    have ha' : a ∈ sig I S r := he ▸ ha
    have hb' : b ∈ sig I S r := he ▸ hb
    exact linear p r a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha').2
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hb').2 hab
  have eq : types I S = singles ∪ B.image (sig I S) := by
    ext U
    constructor
    · intro hu
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
      by_cases h : 2 ≤ (sig I S p).card
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,h⟩))
      · have := pos p hp
        obtain ⟨l,he⟩ := Finset.card_eq_one.mp (by omega : (sig I S p).card = 1)
        have hl : l ∈ sig I S p := by simp [he]
        have hv : l ∈ V := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).1,
          he ▸ Finset.mem_image_of_mem (sig I S) hp⟩
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l,hv,he.symm⟩)
    · intro h
      rcases Finset.mem_union.mp h with hs|hb
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hs
        exact (Finset.mem_filter.mp hl).2
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hp).1
  have dis : Disjoint singles (B.image (sig I S)) := by
    apply Finset.disjoint_left.mpr
    intro u hs hb
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hb
    have := (Finset.mem_filter.mp hp).2
    simp [he] at this
  have card : (types I S).card = V.card+B.card := by
    rw [eq,Finset.card_union_of_disjoint dis,Finset.card_image_of_injOn inj]
    congr 1
    exact Finset.card_image_of_injective _ (fun a b h => Finset.singleton_inj.mp h)
  have sumDeg : (∑ l ∈ S, (pts I l).card) = ∑ p ∈ A, (sig I S p).card := by
    have he (p) : Finset.univ.filter (fun j => j ∈ S ∧ p ∈ pts I j) = sig I S p := by
      ext j; simp [sig,pts]
    simpa only [he,A,active] using Finset.sum_card_eq_sum_biUnion_card (pts I) S
  have count : (∑ p ∈ A, (sig I S p).card) =
      A.card+B.card+(∑ p ∈ A, ((sig I S p).card-2)) := by
    calc
      _ = ∑ p ∈ A, (1 + (if 2 ≤ (sig I S p).card then 1 else 0) + ((sig I S p).card-2)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have := pos p hp
        split <;> omega
      _ = _ := by simp [B,Finset.sum_add_distrib,Finset.sum_boole]
  have hv : V.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  unfold budget
  rw [sumDeg,count,card]
  change _ + _ - (A.card + _) = (∑ p ∈ A, ((sig I S p).card-2)) + (S.card - V.card)
  omega

theorem hdrop_of_budget {q : ℕ} (hs : 2 ≤ S.card) (hd : ∀ l ∈ S, (pts I l).card = q+1)
    (small : 100 * budget I S + q ≤ 100*(q+2))
    {t : ℕ} (hf : HasMonoSize (n+n) (edgeFun I S) t) (l : Fin n) (hl : l ∈ S) :
    ∃ u, HasMonoSize (n+n) (edgeFun I (S.erase l)) u ∧ 100*u+q ≤ 100*t := by
  classical
  have hp (a) (ha : a ∈ S) : (pts I a).Nonempty := Finset.card_pos.mp (by rw [hd a ha]; omega)
  obtain ⟨p,hi⟩ := hp l hl
  have lb := support_lower I S ⟨p,Finset.mem_biUnion.mpr ⟨l,hl,hi⟩⟩ hf
  have hc := Finset.card_erase_of_mem hl
  have hn : (S.erase l).Nonempty := Finset.card_pos.mp (by omega)
  have ub := encoded_upper (pts I) (S.erase l) (Equiv.refl _) (Function.Embedding.refl _) I
    (fun a _ p => mem_pts I p a) hn (fun a ha => hp a (Finset.mem_of_mem_erase ha))
  refine ⟨_,by simpa using ub,?_⟩
  unfold budget at small
  rw [← Finset.add_sum_erase S (fun a => (pts I a).card) hl, hd l hl] at small
  have pos := Finset.card_pos.mpr hn
  omega

end Onlyfr.PrivateConcurrency
