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
      unfold pick
      split
      · assumption
      · exact h.resolve_right (by assumption)
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

/-- On an arc of lines, deleting arbitrary lines leaves exactly one shared
point per other surviving line. The private-point count is therefore exact. -/
theorem arc_private_card {A B : Type*} [DecidableEq A] [DecidableEq B]
    (pts : B → Finset A) (S : Finset B) (l : B) (hl : l ∈ S)
    (pair : ∀ a ∈ S.erase l, (pts l ∩ pts a).card = 1)
    (triple : ∀ a ∈ S.erase l, ∀ b ∈ S.erase l, a ≠ b →
      ∀ p ∈ pts l, p ∈ pts a → p ∉ pts b) :
    ((pts l) \ (S.erase l).biUnion (fun a => pts l ∩ pts a)).card
      + (S.card - 1) = (pts l).card := by
  classical
  let shared := (S.erase l).biUnion (fun a => pts l ∩ pts a)
  have count : shared.card = (S.erase l).card := by
    unfold shared
    rw [Finset.card_biUnion]
    · simp [Finset.sum_congr rfl pair]
    · intro a ha b hb hab
      apply Finset.disjoint_left.mpr
      intro p hp hq
      exact triple a ha b hb hab p (Finset.mem_inter.mp hp).1
        (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hq).2
  have sub : shared ⊆ pts l := by
    intro p hp
    obtain ⟨a, _, h⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp h).1
  change ((pts l) \ shared).card + _ = _
  rw [← Finset.card_erase_of_mem hl, ← count, Finset.card_sdiff_add_card_eq_card sub]

/-- In the affine chart the two tangents with parameters a and b meet at
(-(a+b), -a*b). Different b give different intersections on line a. -/
theorem tangent_pair {K : Type*} [Field K] {a b x y : K} (hab : a ≠ b) :
    y = a*x + a^2 ∧ y = b*x + b^2 ↔ x = -(a+b) ∧ y = -(a*b) := by
  constructor
  · rintro ⟨ha, hb⟩
    have h : (a-b)*(x+a+b) = 0 := by linear_combination hb - ha
    have hx := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hab)
    constructor
    · linear_combination hx
    · linear_combination ha + a*hx
  · rintro ⟨rfl, rfl⟩
    constructor <;> ring

theorem tangent_no_triple {K : Type*} [Field K] {a b c x y : K}
    (hab : a ≠ b) (hac : a ≠ c) (ha : y = a*x + a^2)
    (hb : y = b*x + b^2) (hc : y = c*x + c^2) : b = c := by
  have h₁ := ((tangent_pair hab).mp ⟨ha,hb⟩).1
  have h₂ := ((tangent_pair hac).mp ⟨ha,hc⟩).1
  linear_combination h₁ - h₂

/-- None indexes the line at infinity; a right-hand point is a direction,
with None reserved for the vertical direction. -/
def arcInc {K : Type*} [Field K] : Option K → (K × K) ⊕ Option K → Prop
  | some a, .inl (x,y) => y = a*x + a^2
  | some a, .inr d => d = some a
  | none, .inl _ => False
  | none, .inr _ => True

theorem arc_pair_unique {K : Type*} [Field K] {l m : Option K} (hne : l ≠ m) :
    ∃! p, arcInc l p ∧ arcInc m p := by
  cases l with
  | none =>
    cases m with
    | none => exact (hne rfl).elim
    | some b =>
      refine ⟨.inr (some b), ⟨trivial,rfl⟩, ?_⟩
      rintro (p|d) ⟨ha,hb⟩
      · exact False.elim ha
      · exact congrArg Sum.inr hb
  | some a =>
    cases m with
    | none =>
      refine ⟨.inr (some a), ⟨rfl,trivial⟩, ?_⟩
      rintro (p|d) ⟨ha,hb⟩
      · exact False.elim hb
      · exact congrArg Sum.inr ha
    | some b =>
      have hab : a ≠ b := fun h => hne (congrArg some h)
      refine ⟨.inl (-(a+b),-(a*b)), (tangent_pair hab).mpr ⟨rfl,rfl⟩, ?_⟩
      rintro (⟨x,y⟩|d) ⟨ha,hb⟩
      · have h := (tangent_pair hab).mp ⟨ha,hb⟩
        exact congrArg Sum.inl (Prod.ext h.1 h.2)
      · exact False.elim (hne (ha.symm.trans hb))

theorem arc_no_triple {K : Type*} [Field K] {l m r : Option K}
    (hlm : l ≠ m) (hlr : l ≠ r) (hmr : m ≠ r) (p : (K × K) ⊕ Option K) :
    arcInc l p → arcInc m p → ¬ arcInc r p := by
  cases p with
  | inl p =>
    obtain ⟨x,y⟩ := p
    cases l <;> cases m <;> cases r <;> simp only [arcInc, false_implies, not_false_eq_true, implies_true]
    intro ha hb hc
    exact hmr (congrArg some (tangent_no_triple (fun h => hlm (congrArg some h))
      (fun h => hlr (congrArg some h)) ha hb hc))
  | inr d =>
    cases l <;> cases m <;> cases r <;> simp_all [arcInc]

noncomputable def arcPts {K : Type*} [Field K] [Fintype K] (l : Option K) :
    Finset ((K × K) ⊕ Option K) := by
  classical
  exact Finset.univ.filter (arcInc l)

@[simp] theorem mem_arcPts {K : Type*} [Field K] [Fintype K]
    {l : Option K} {p : (K × K) ⊕ Option K} : p ∈ arcPts l ↔ arcInc l p := by
  classical
  simp [arcPts]

theorem projective_arc_private_card {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (S : Finset (Option K)) (l : Option K) (hl : l ∈ S) :
    ((arcPts l) \ (S.erase l).biUnion (fun a => arcPts l ∩ arcPts a)).card
      + (S.card - 1) = (arcPts l).card := by
  apply arc_private_card _ _ _ hl
  · intro a ha
    obtain ⟨p, hp, hu⟩ := arc_pair_unique (Finset.ne_of_mem_erase ha).symm
    apply Finset.card_eq_one.mpr
    refine ⟨p, ?_⟩
    ext v
    simp only [Finset.mem_inter, mem_arcPts, Finset.mem_singleton]
    exact ⟨hu v, fun h => h ▸ hp⟩
  · intro a ha b hb hab p hp hpa hpb
    exact arc_no_triple (Finset.ne_of_mem_erase ha).symm
      (Finset.ne_of_mem_erase hb).symm hab p (mem_arcPts.mp hp)
      (mem_arcPts.mp hpa) (mem_arcPts.mp hpb)

theorem arcPts_card {K : Type*} [Field K] [Fintype K] (l : Option K) :
    (arcPts l).card = Fintype.card K + 1 := by
  classical
  cases l with
  | none =>
    have h : arcPts (none : Option K) = Finset.univ.image
        (Sum.inr : Option K → (K × K) ⊕ Option K) := by
      ext p
      cases p <;> simp [arcInc]
    rw [h, Finset.card_image_of_injective _ Sum.inr_injective]
    simp
  | some a =>
    let f (x : K) : (K × K) ⊕ Option K := .inl (x,a*x+a^2)
    have hi : Function.Injective f := by
      intro x y h
      exact congrArg Prod.fst (Sum.inl.inj h)
    have h : arcPts (some a) = insert (.inr (some a)) (Finset.univ.image f) := by
      ext p
      cases p with
      | inl p =>
        obtain ⟨x,y⟩ := p
        simp [f, arcInc, eq_comm]
      | inr d => simp [f, arcInc]
    rw [h, Finset.card_insert_of_notMem (by simp [f]), Finset.card_image_of_injective _ hi]
    simp

end Onlyfr.PrivateForestLift
