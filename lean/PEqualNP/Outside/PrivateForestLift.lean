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

section Star

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Retain private points and all points on the chosen central line. -/
noncomputable def starRow (S : Finset (Option K)) (c l : Option K) :=
  ((arcPts l) \ (S.erase l).biUnion (fun a => arcPts l ∩ arcPts a)) ∪ (arcPts l ∩ arcPts c)

theorem starRow_center (S : Finset (Option K)) (c : Option K) :
    starRow S c c = arcPts c := by
  unfold starRow
  simp [Finset.union_eq_right.mpr (Finset.sdiff_subset : _ ⊆ arcPts c)]

theorem starRow_other (S : Finset (Option K)) {c l : Option K}
    (hc : c ∈ S) (hl : l ∈ S) (hne : l ≠ c) :
    (starRow S c l).card = (Fintype.card K + 2 - S.card) + 1 := by
  classical
  let shared := (S.erase l).biUnion (fun a => arcPts l ∩ arcPts a)
  have sub : arcPts l ∩ arcPts c ⊆ shared :=
    Finset.subset_biUnion_of_mem (fun a => arcPts l ∩ arcPts a) (Finset.mem_erase.mpr ⟨hne.symm,hc⟩)
  have dis : Disjoint (arcPts l \ shared) (arcPts l ∩ arcPts c) := by
    exact Finset.disjoint_left.mpr fun _ hp h => (Finset.mem_sdiff.mp hp).2 (sub h)
  obtain ⟨p, hp, hu⟩ := arc_pair_unique hne
  have one : (arcPts l ∩ arcPts c).card = 1 := by
    apply Finset.card_eq_one.mpr
    refine ⟨p, ?_⟩
    ext v
    simp only [Finset.mem_inter, mem_arcPts, Finset.mem_singleton]
    exact ⟨hu v, fun h => h ▸ hp⟩
  have count := projective_arc_private_card S l hl
  rw [arcPts_card] at count
  change (arcPts l \ shared).card + _ = _ at count
  have pos := Finset.card_pos.mpr ⟨l,hl⟩
  unfold starRow
  rw [Finset.card_union_of_disjoint dis, one]
  omega

/-- Each dependent pair records a line and one of its retained points. -/
theorem star_edges_card (S : Finset (Option K)) {c : Option K} (hc : c ∈ S) :
    (S.sigma (starRow S c)).card = Fintype.card K + 1 +
      (S.card - 1) * ((Fintype.card K + 2 - S.card) + 1) := by
  rw [Finset.card_sigma, ← Finset.add_sum_erase _ _ hc, starRow_center, arcPts_card]
  congr 1
  calc
    _ = ∑ _l ∈ S.erase c, ((Fintype.card K + 2 - S.card) + 1) := by
      apply Finset.sum_congr rfl
      intro l hl
      exact starRow_other S hc (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)
    _ = _ := by simp [Finset.card_erase_of_mem hc]

/-- At a vertex of maximal rank on a cycle both cycle neighbours would have
no greater rank. Uniqueness of such a neighbour therefore rules out cycles. -/
theorem acyclic_of_unique_lower {V : Type*} (G : SimpleGraph V) (rank : V → ℕ)
    (unique : ∀ v u w, G.Adj v u → G.Adj v w →
      rank u ≤ rank v → rank w ≤ rank v → u = w) : G.IsAcyclic := by
  classical
  apply SimpleGraph.isAcyclic_iff_free_cycleGraph.mpr
  intro n hn ⟨f⟩
  obtain ⟨t,rfl⟩ : ∃ t, n = t+3 := ⟨n-3, by omega⟩
  obtain ⟨v,_,hv⟩ := Finset.exists_max_image Finset.univ
    (fun i => rank (f i)) Finset.univ_nonempty
  have small : ((SimpleGraph.cycleGraph (t+3)).neighborFinset v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu w hw
    apply f.injective
    exact unique _ _ _ (f.toHom.map_rel (by simpa only [SimpleGraph.mem_neighborFinset] using hu))
      (f.toHom.map_rel (by simpa only [SimpleGraph.mem_neighborFinset] using hw))
      (hv u (by simp)) (hv w (by simp))
  change (SimpleGraph.cycleGraph (t+3)).degree v ≤ 1 at small
  rw [SimpleGraph.cycleGraph_degree_three_le] at small
  omega

def starGraph (S : Finset (Option K)) (c : Option K) :
    SimpleGraph ((Option K) ⊕ ((K × K) ⊕ Option K)) where
  Adj
    | .inl l, .inr p | .inr p, .inl l => l ∈ S ∧ p ∈ starRow S c l
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

theorem starGraph_acyclic (S : Finset (Option K)) {c : Option K} (hc : c ∈ S) :
    (starGraph S c).IsAcyclic := by
  classical
  let rank : Option K ⊕ ((K × K) ⊕ Option K) → ℕ
    | .inl l => if l = c then 0 else 2
    | .inr p => if p ∈ arcPts c then 1 else 3
  apply acyclic_of_unique_lower _ rank
  intro v u w hu hw hru hrw
  cases v <;> cases u <;> cases w <;> simp_all only [starGraph, Sum.inr.injEq, Sum.inl.injEq]
  case inl.inr.inr l p r =>
    by_cases h : l = c
    · subst l
      simp [rank] at hru
      split at hru <;> omega
    · have hp : p ∈ arcPts c := by by_contra hp; simp only [rank, if_neg hp, if_neg h] at hru <;> omega
      have hr : r ∈ arcPts c := by by_contra hr; simp only [rank, if_neg hr, if_neg h] at hrw <;> omega
      have onLine (z) (hz : z ∈ starRow S c l) : z ∈ arcPts l := by
        rcases Finset.mem_union.mp hz with hz|hz
        · exact (Finset.mem_sdiff.mp hz).1
        · exact (Finset.mem_inter.mp hz).1
      exact (arc_pair_unique h).unique ⟨mem_arcPts.mp (onLine p hu.2),mem_arcPts.mp hp⟩
        ⟨mem_arcPts.mp (onLine r hw.2),mem_arcPts.mp hr⟩
  case inr.inl.inl p l m =>
    by_cases hp : p ∈ arcPts c
    · by_contra h
      by_cases hl : l = c <;> by_cases hm : m = c <;> simp_all [rank]
    · by_contra h
      have priv : p ∈ (arcPts l) \ (S.erase l).biUnion (fun a => arcPts l ∩ arcPts a) := by
        rcases Finset.mem_union.mp hu.2 with h|h
        · exact h
        · exact (hp (Finset.mem_inter.mp h).2).elim
      have hm : p ∈ arcPts m := by
        rcases Finset.mem_union.mp hw.2 with h|h
        · exact (Finset.mem_sdiff.mp h).1
        · exact (Finset.mem_inter.mp h).1
      exact (Finset.mem_sdiff.mp priv).2 (Finset.mem_biUnion.mpr
        ⟨m,Finset.mem_erase.mpr ⟨Ne.symm h,hw.1⟩,Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp priv).1,hm⟩⟩)

/-- Points shared by a pair of noncentral active lines are exactly the
intersections removed by the star construction. -/
noncomputable def commonPts (U : Finset (Option K)) : Finset ((K × K) ⊕ Option K) := by
  classical
  exact Finset.univ.filter (fun p => ∀ l ∈ U, arcInc l p)

@[simp] theorem mem_commonPts {U : Finset (Option K)} {p} :
    p ∈ commonPts U ↔ ∀ l ∈ U, arcInc l p := by classical simp [commonPts]

noncomputable def starPinned (S : Finset (Option K)) (c : Option K) :=
  ((S.erase c).powersetCard 2).biUnion commonPts

theorem starPinned_card (S : Finset (Option K)) {c : Option K} (hc : c ∈ S) :
    (starPinned S c).card = (S.card - 1).choose 2 := by
  classical
  have one (U : Finset (Option K)) (hU : U.card = 2) : (commonPts U).card = 1 := by
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hU
    obtain ⟨p,hp,hu⟩ := arc_pair_unique hab
    apply Finset.card_eq_one.mpr
    refine ⟨p, ?_⟩
    ext z
    simp only [mem_commonPts, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨fun h => hu z h, fun h => h ▸ hp⟩
  unfold starPinned
  rw [Finset.card_biUnion]
  · calc
      _ = ∑ _ ∈ (S.erase c).powersetCard 2, 1 := by
        exact Finset.sum_congr rfl fun U hU => one U (Finset.mem_powersetCard.mp hU).2
      _ = _ := by simp [Finset.card_powersetCard, Finset.card_erase_of_mem hc]
  · intro U hU V hV huv
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have huc := (Finset.mem_powersetCard.mp hU).2
    have hvc := (Finset.mem_powersetCard.mp hV).2
    obtain ⟨a,b,hab,hpair⟩ := Finset.card_eq_two.mp huc
    have sub : V ⊆ U := by
      intro l hl
      by_contra hn
      have ha : a ∈ U := by simp [hpair]
      have hb : b ∈ U := by simp [hpair]
      exact arc_no_triple (r := l) hab (fun e => hn (e ▸ ha)) (fun e => hn (e ▸ hb)) p
        (mem_commonPts.mp hp a ha) (mem_commonPts.mp hp b hb) (mem_commonPts.mp hq l hl)
    exact huv (Finset.eq_of_subset_of_card_le sub (by omega)).symm

theorem star_counts_1009 (hK : Fintype.card K = 1009) (S : Finset (Option K))
    (hS : S.card = 1001) {c : Option K} (hc : c ∈ S) :
    (S.sigma (starRow S c)).card = 12010 ∧ (starPinned S c).card = 499500 := by
  rw [star_edges_card S hc, starPinned_card S hc, hS, hK]
  norm_num [Nat.choose_two_right]

theorem starRow_eq_restriction (S : Finset (Option K)) {c l : Option K} (hl : l ∈ S) :
    starRow S c l = arcPts l \ starPinned S c := by
  classical
  ext p
  have pin : p ∈ starPinned S c ↔ ∃ a ∈ S.erase c, ∃ b ∈ S.erase c,
      a ≠ b ∧ arcInc a p ∧ arcInc b p := by
    constructor
    · intro h
      obtain ⟨U,hU,hp⟩ := Finset.mem_biUnion.mp h
      obtain ⟨sub,card⟩ := Finset.mem_powersetCard.mp hU
      obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp card
      exact ⟨a,sub (by simp),b,sub (by simp),hab,
        mem_commonPts.mp hp _ (by simp),mem_commonPts.mp hp _ (by simp)⟩
    · rintro ⟨a,ha,b,hb,hab,hpa,hpb⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨{a,b}, Finset.mem_powersetCard.mpr ⟨by intro z hz; rcases Finset.mem_insert.mp hz with h|h; exact h.symm ▸ ha; exact (Finset.mem_singleton.mp h).symm ▸ hb, by simp [hab]⟩, ?_⟩
      simpa using And.intro hpa hpb
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨hp,hs⟩ := Finset.mem_sdiff.mp h
      refine Finset.mem_sdiff.mpr ⟨hp, ?_⟩
      intro hpin
      obtain ⟨a,ha,b,hb,hab,hpa,hpb⟩ := pin.mp hpin
      have noOther (m) (hm : m ∈ S.erase c) (hm' : m ≠ l) (hi : arcInc m p) : False :=
        hs (Finset.mem_biUnion.mpr ⟨m,Finset.mem_erase.mpr ⟨hm',Finset.mem_of_mem_erase hm⟩,
          Finset.mem_inter.mpr ⟨hp,mem_arcPts.mpr hi⟩⟩)
      by_cases e : a = l
      · exact noOther b hb (e ▸ hab.symm) hpb
      · exact noOther a ha e hpa
    · obtain ⟨hlp,hcp⟩ := Finset.mem_inter.mp h
      refine Finset.mem_sdiff.mpr ⟨hlp,?_⟩
      intro hpin
      obtain ⟨a,ha,b,hb,hab,hpa,hpb⟩ := pin.mp hpin
      exact arc_no_triple hab (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb) p
        hpa hpb (mem_arcPts.mp hcp)
  · intro h
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp h
    by_cases hc : p ∈ arcPts c
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp,hc⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      refine ⟨hp,?_⟩
      intro hshare
      obtain ⟨a,ha,hi⟩ := Finset.mem_biUnion.mp hshare
      have hal := Finset.ne_of_mem_erase ha
      have hpa := (Finset.mem_inter.mp hi).2
      have hlc : l ≠ c := fun e => hc (e ▸ hp)
      have hac : a ≠ c := fun e => hc (e ▸ hpa)
      exact hn (pin.mpr ⟨a,Finset.mem_erase.mpr ⟨hac,Finset.mem_of_mem_erase ha⟩,l,
        Finset.mem_erase.mpr ⟨hlc,hl⟩,hal,mem_arcPts.mp hpa,mem_arcPts.mp hp⟩)

/-- Pick one private representative per active line. Since every point on an
arc belongs to at most two lines, pinning the noncentral crossings preserves
all the chosen representatives. -/
theorem star_matching (S : Finset (Option K)) (c : Option K) :
    ∃ leaf : Option K → (K × K) ⊕ Option K,
      (∀ l ∈ S, leaf l ∈ starRow S c l) ∧ (↑S : Set (Option K)).InjOn leaf := by
  classical
  let priv (l : Option K) := arcPts l \ (S.erase l).biUnion (fun a => arcPts l ∩ arcPts a)
  have bound : S.card ≤ Fintype.card K + 1 := by simpa using S.card_le_univ
  have ex (l : Option K) (hl : l ∈ S) : (priv l).Nonempty := by
    apply Finset.card_pos.mp
    have h := projective_arc_private_card S l hl
    rw [arcPts_card] at h
    change (priv l).card + _ = _ at h
    omega
  let leaf (l : Option K) := if h : l ∈ S then (ex l h).choose else Sum.inr none
  have good (l : Option K) (h : l ∈ S) : leaf l ∈ priv l := by
    simpa only [leaf, dif_pos h] using (ex l h).choose_spec
  refine ⟨leaf,fun l hl => Finset.mem_union_left _ (good l hl), ?_⟩
  intro a ha b hb e
  by_contra hne
  have ha' := Finset.mem_sdiff.mp (good a ha)
  have hb' := Finset.mem_sdiff.mp (good b hb)
  exact ha'.2 (Finset.mem_biUnion.mpr ⟨b,Finset.mem_erase.mpr ⟨Ne.symm hne,hb⟩,
    Finset.mem_inter.mpr ⟨ha'.1,e ▸ hb'.1⟩⟩)

/-- Transport a forest along an injection, allowing unused circuit inputs as
additional isolated vertices. Only vertices on a cycle need an inverse. -/
theorem acyclic_of_encoded_edges {A B : Type*} [Nonempty A] (G : SimpleGraph A)
    (H : SimpleGraph B) (e : A ↪ B) (hg : G.IsAcyclic)
    (edges : ∀ u v, H.Adj u v → ∃ a b, e a = u ∧ e b = v ∧ G.Adj a b) :
    H.IsAcyclic := by
  classical
  apply SimpleGraph.isAcyclic_iff_free_cycleGraph.mpr
  intro n hn ⟨f⟩
  obtain ⟨t,rfl⟩ : ∃ t, n = t+3 := ⟨n-3,by omega⟩
  let inv := Function.invFun e
  have left : Function.LeftInverse inv e := Function.leftInverse_invFun e.injective
  have hit (i : Fin (t+3)) : e (inv (f i)) = f i := by
    have pos : 0 < ((SimpleGraph.cycleGraph (t+3)).neighborFinset i).card := by
      change 0 < (SimpleGraph.cycleGraph (t+3)).degree i
      rw [SimpleGraph.cycleGraph_degree_three_le]
      decide
    obtain ⟨j,hj⟩ := Finset.card_pos.mp pos
    obtain ⟨a,_,ha,_,_⟩ := edges _ _ (f.toHom.map_rel (by simpa only [SimpleGraph.mem_neighborFinset] using hj))
    change e a = f i at ha
    rw [← ha,left a]
  apply SimpleGraph.isAcyclic_iff_free_cycleGraph.mp hg _ hn
  refine ⟨⟨⟨fun i => inv (f i), ?_⟩, ?_⟩⟩
  · intro i j h
    obtain ⟨a,b,ha,hb,hadj⟩ := edges _ _ (f.toHom.map_rel h)
    change e a = f i at ha
    change e b = f j at hb
    rwa [← ha,← hb,left a,left b]
  · intro i j h
    apply f.injective
    exact (hit i).symm.trans ((congrArg e h).trans (hit j))

/-- A lower bound for any circuit on numbered inputs realizing the given arc
rows. The point numbering is arbitrary, and unused line inputs are allowed. -/
theorem arc_circuit_bound {n t : ℕ} (S : Finset (Option K)) {c : Option K} (hc : c ∈ S)
    (pt : ((K × K) ⊕ Option K) ≃ Fin n) (ln : Option K ↪ Fin n)
    (I : Fin n → Fin n → Prop)
    (rows : ∀ l ∈ S, ∀ p, I (pt p) (ln l) ↔ arcInc l p)
    (hf : HasMonoSize (n+n) (edgeFun I (S.map ln)) t) :
    (S.sigma (starRow S c)).card + S.card + (starPinned S c).card ≤ t+1 := by
  classical
  let P := (starPinned S c).map pt.toEmbedding
  have pins (p) : pt p ∈ P ↔ p ∈ starPinned S c := by simp [P]
  have retained (l) (hl : l ∈ S) (p) :
      p ∈ starRow S c l ↔ I (pt p) (ln l) ∧ pt p ∉ P := by
    rw [starRow_eq_restriction S hl, Finset.mem_sdiff,mem_arcPts,rows l hl,pins]
  have hpins : ∀ u ∈ P, ∃ v ∈ S.map ln, I u v := by
    intro u hu
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨U,hU,hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hs,hn⟩ := Finset.mem_powersetCard.mp hU
    obtain ⟨l,hl⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
    have hls := Finset.mem_of_mem_erase (hs hl)
    exact ⟨ln l,Finset.mem_map_of_mem _ hls,(rows l hls p).mpr (mem_commonPts.mp hi l hl)⟩
  obtain ⟨leaf,hLeaf,injLeaf⟩ := star_matching S c
  let decode := Function.invFun ln
  have left : Function.LeftInverse decode ln := Function.leftInverse_invFun ln.injective
  let pick (u : Fin n) := pt (leaf (decode u))
  have good : ∀ l ∈ S.map ln, pick l ∉ P ∧ I (pick l) l := by
    intro u hu
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hu
    simpa only [pick,left l] using ((retained l hl _).mp (hLeaf l hl)).symm
  have inj : (↑(S.map ln) : Set (Fin n)).InjOn pick := by
    intro u hu v hv h
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨m,hm,rfl⟩ := Finset.mem_map.mp hv
    simp only [pick,left l,left m,Equiv.apply_eq_iff_eq] at h
    exact congrArg ln (injLeaf hl hm h)
  let encode : Option K ⊕ ((K × K) ⊕ Option K) ↪ Fin (n+n) :=
    ⟨Sum.elim (fun l => Fin.natAdd n (ln l)) (fun p => Fin.castAdd n (pt p)), by
      intro u v h
      cases u with
      | inl l =>
        cases v with
        | inl m => exact congrArg Sum.inl (ln.injective (Fin.natAdd_injective n n h))
        | inr p => exact (left_ne_right _ _ h.symm).elim
      | inr p =>
        cases v with
        | inl l => exact (left_ne_right _ _ h).elim
        | inr q => exact congrArg Sum.inr (pt.injective (Fin.castAdd_injective n n h))⟩
  have forest : (graph I (S.map ln) P).IsAcyclic := by
    apply acyclic_of_encoded_edges (starGraph S c) _ encode (starGraph_acyclic S hc)
    rintro u v ⟨z,hz,w,hw,hzw,h⟩
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hw
    let p := pt.symm z
    have ep : pt p = z := pt.apply_symm_apply z
    have hadj : (starGraph S c).Adj (.inl l) (.inr p) :=
      ⟨hl,(retained l hl p).mpr (by rw [ep]; exact ⟨hzw,hz⟩)⟩
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨.inr p,.inl l,congrArg (Fin.castAdd n) ep,rfl,hadj.symm⟩
    · exact ⟨.inl l,.inr p,rfl,congrArg (Fin.castAdd n) ep,hadj⟩
  let pair : (Σ _ : Option K, (K × K) ⊕ Option K) ↪ Fin n × Fin n :=
    ⟨fun e => (pt e.2, ln e.1), by
      rintro ⟨l,p⟩ ⟨m,q⟩ h
      obtain rfl := ln.injective (congrArg Prod.snd h)
      obtain rfl := pt.injective (congrArg Prod.fst h)
      rfl⟩
  have bound := lift_forest I (S.map ln) P hpins ⟨ln c,Finset.mem_map_of_mem _ hc⟩ pick good inj
    forest ((S.sigma (starRow S c)).map pair) (by
      intro e he
      obtain ⟨⟨l,p⟩,hp,rfl⟩ := Finset.mem_map.mp he
      obtain ⟨hl,hr⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hi,hn⟩ := (retained l hl p).mp hr
      exact ⟨hn,Finset.mem_map_of_mem _ hl,hi⟩) hf
  simpa only [P,Finset.card_map] using bound

theorem arc_circuit_1009 {n t : ℕ} (hK : Fintype.card K = 1009)
    (S : Finset (Option K)) (hS : S.card = 1001)
    (pt : ((K × K) ⊕ Option K) ≃ Fin n) (ln : Option K ↪ Fin n)
    (I : Fin n → Fin n → Prop) (rows : ∀ l ∈ S, ∀ p, I (pt p) (ln l) ↔ arcInc l p)
    (hf : HasMonoSize (n+n) (edgeFun I (S.map ln)) t) : 512510 ≤ t := by
  obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have h := arc_circuit_bound S hc pt ln I rows hf
  obtain ⟨he,hp⟩ := star_counts_1009 hK S hS hc
  omega

theorem arc_full_circuit_1009 {n t : ℕ} (hK : Fintype.card K = 1009)
    (pt : ((K × K) ⊕ Option K) ≃ Fin n) (ln : Option K ↪ Fin n)
    (I : Fin n → Fin n → Prop) (rows : ∀ l p, I (pt p) (ln l) ↔ arcInc l p)
    (hf : HasMonoSize (n+n) (edgeFun I (Finset.univ.map ln)) t) : 512573 ≤ t := by
  have hc : (none : Option K) ∈ Finset.univ := Finset.mem_univ _
  have h := arc_circuit_bound Finset.univ hc pt ln I (fun l _ => rows l) hf
  rw [star_edges_card _ hc,starPinned_card _ hc] at h
  norm_num [Nat.choose_two_right,hK] at h
  omega

end Star

end Onlyfr.PrivateForestLift
