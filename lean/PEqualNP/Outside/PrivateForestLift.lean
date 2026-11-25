import PEqualNP.Outside.PrivateGeneralDrop
import PEqualNP.MetaComplexity.Helpers.ForestBound

namespace Onlyfr.PrivateForestLift

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGateDrop Onlyfr.PrivateGeneralDrop

def graph {n : ℕ} (I : Fin n → Fin n → Prop) (S P : Finset (Fin n)) : SimpleGraph (Fin (n+n)) where
  Adj u v := ∃ p ∉ P, ∃ l ∈ S, I p l ∧
    ((u = Fin.castAdd n p ∧ v = Fin.natAdd n l) ∨ (v = Fin.castAdd n p ∧ u = Fin.natAdd n l))
  symm := ⟨by
    rintro u v ⟨p,hp,l,hl,hpl,h⟩
    exact ⟨p,hp,l,hl,hpl,h.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨p,_,l,_,_,h⟩
    rcases h with h|h <;> exact left_ne_right p l (h.1.symm.trans h.2)⟩

theorem lift_forest {n : ℕ} (I : Fin n → Fin n → Prop) (S P : Finset (Fin n))
    (hpin : ∀ p ∈ P, ∃ l ∈ S, I p l) (hne : S.Nonempty)
    (leaf : Fin n → Fin n) (hlf : ∀ l ∈ S, leaf l ∉ P ∧ I (leaf l) l)
    (hinj : (↑S : Set (Fin n)).InjOn leaf)
    (hforest : (graph I S P).IsAcyclic)
    (edges : Finset (Fin n × Fin n))
    (hedges : ∀ e ∈ edges, e.1 ∉ P ∧ e.2 ∈ S ∧ I e.1 e.2)
    {s : ℕ} (hf : HasMonoSize (n+n) (edgeFun I S) s) :
    edges.card + S.card + P.card ≤ s+1 := by
  classical
  let G := graph I S P
  have adj (p l : Fin n) (hp : p ∉ P) (hl : l ∈ S) (he : I p l) :
      G.Adj (Fin.castAdd n p) (Fin.natAdd n l) := ⟨p,hp,l,hl,he,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨l,hl⟩ := hne
  have keep := hlf l hl
  have covers (T : Finset (Fin (n+n))) (hc : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) : S.card ≤ T.card := by
    let pick (a : Fin n) := if Fin.natAdd n a ∈ T then Fin.natAdd n a else Fin.castAdd n (leaf a)
    apply Finset.card_le_card_of_injOn pick
    · intro a ha
      have h := hc _ _ (adj _ _ (hlf a ha).1 ha (hlf a ha).2)
      change pick a ∈ T
      by_cases hm : Fin.natAdd n a ∈ T
      · simp [pick, hm]
      · simpa [pick, hm] using h.resolve_right hm
    · intro a ha b hb he
      unfold pick at he
      split at he <;> split at he
      · exact Fin.natAdd_injective n n he
      · exact False.elim (left_ne_right _ _ he.symm)
      · exact False.elim (left_ne_right _ _ he)
      · exact hinj ha hb (Fin.castAdd_injective n n he)
  let edge (e : Fin n × Fin n) := s(Fin.castAdd n e.1, Fin.natAdd n e.2)
  have hsize : edges.card ≤ G.edgeFinset.card := by
    apply Finset.card_le_card_of_injOn edge
    · intro e he
      obtain ⟨hp,ha,hi⟩ := hedges e he
      exact SimpleGraph.mem_edgeFinset.mpr (adj _ _ hp ha hi)
    · intro e _ d _ he
      rcases Sym2.eq_iff.mp he with h|h
      · exact Prod.ext (Fin.castAdd_injective n n h.1) (Fin.natAdd_injective n n h.2)
      · exact False.elim (left_ne_right _ _ h.1)
  have eqf (x : Fin (n+n) → Bool) : edgeFun I S (pin (P.image (Fin.castAdd n)) x) =
      decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) := by
    apply Bool.eq_iff_iff.mpr
    rw [edgeFun_true,decide_eq_true_eq]
    have line (a : Fin n) : Fin.natAdd n a ∉ P.image (Fin.castAdd n) := by
      intro h
      obtain ⟨v,_,he⟩ := Finset.mem_image.mp h
      exact left_ne_right v a he
    constructor
    · rintro ⟨v,a,ha,hi,hp,hy⟩
      have hv : v ∉ P := by
        intro h
        rw [pin,if_pos (Finset.mem_image_of_mem _ h)] at hp
        contradiction
      have hw : Fin.castAdd n v ∉ P.image (Fin.castAdd n) := by simpa using hv
      rw [pin,if_neg hw] at hp
      rw [pin,if_neg (line a)] at hy
      exact ⟨_,_,adj _ _ hv ha hi,hp,hy⟩
    · rintro ⟨i,j,⟨v,hv,a,ha,hi,h⟩,hx,hy⟩
      have hw : Fin.castAdd n v ∉ P.image (Fin.castAdd n) := by simpa using hv
      refine ⟨v,a,ha,hi,?_,?_⟩
      · rw [pin,if_neg hw]
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
      · rw [pin,if_neg (line a)]
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
  have hcombined := lift_point_restriction I S P hpin ⟨leaf l,keep.1,l,hl,keep.2⟩ hf
    (L := edges.card + S.card - 1) (by
      intro t ht
      have heq := funext eqf
      rw [heq] at ht
      have hb := Helpers.Forest.forest_bound _ S.card t G hforest
        ⟨_,_,adj _ _ keep.1 hl keep.2⟩ covers ht.has
      omega)
  omega

end Onlyfr.PrivateForestLift
