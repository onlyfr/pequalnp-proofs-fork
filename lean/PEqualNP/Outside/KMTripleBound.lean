import PEqualNP.Outside.PrivatePointPhase
import PEqualNP.Outside.ThreeEdgeProjection
import PEqualNP.Outside.ThreeEdgeTargets

namespace Onlyfr.KMTripleBound
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.Helpers
open Onlyfr.PrivateIncidenceDrop Onlyfr.ThreeEdgeProjection

variable {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] (S : Finset (Fin n))
variable (hj : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
def pts (l : Fin n) := Finset.univ.filter (fun p => I p l)
def active := S.biUnion (pts I)
def sig (p : Fin n) := S.filter (I p)

local notation "J" => (fun (l p : Fin n) => l ∈ S ∧ I p l)
include hj

theorem three_lower (T : Finset (Fin n)) (two : ∀ p ∈ T, (sig I S p).card = 2) (h3 : T.card = 3)
    (t : ℕ) (ht : HasMonoSize (n+n) (edgeFun J T) t) : 8 ≤ t := by
  classical
  let idx : T ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using h3)
  let p (i : Fin 3) : Fin n := (idx.symm i).val
  have pairs (i) := Finset.card_eq_two.mp (two (p i) (idx.symm i).property)
  choose a b ne eq using pairs
  let v : Fin 6 → Fin n := ![a 0,b 0,a 1,b 1,a 2,b 2]
  have ends_eq (i) : ends v i = (a i,b i) := by fin_cases i <;> rfl
  have mem (i l) : J l (p i) ↔ l = a i ∨ l = b i := by
    change l ∈ S ∧ I (p i) l ↔ _
    rw [← Finset.mem_filter]
    change l ∈ sig I S (p i) ↔ _
    rw [eq]
    simp
  have different (i j : Fin 3) (hij : i ≠ j) :
      ¬ (ends v i = ends v j ∨ ends v i = (ends v j).swap) := by
    simp only [ends_eq,Prod.swap,Prod.mk.injEq]
    intro h
    have both : J (a i) (p j) ∧ J (b i) (p j) := by
      rw [mem,mem]
      tauto
    have hpr : p i ≠ p j := fun e => hij (idx.symm.injective (Subtype.ext e))
    exact ne i ((hj _ _ hpr).unique
      ⟨((mem i _).mpr (Or.inl rfl)).2,both.1.2⟩ ⟨((mem i _).mpr (Or.inr rfl)).2,both.2.2⟩)
  obtain ⟨s,c,hc⟩ := colorable v (fun i => by simpa only [ends_eq] using ne i) different
  simp only [ends_eq,Prod.ext_iff] at hc
  let tag (u : Fin n) : Fin 7 := if hu : u ∈ T then mid (idx ⟨u,hu⟩) else 0
  have tag_p (i) : tag (p i) = mid i := by simp [tag,p,(idx.symm i).property]
  let π : Fin (n+n) → Fin 7 := Fin.addCases (fun l => vertex (c l)) tag
  have proj := PermInputs.relabel_size π _ _ ht.has
  apply target_lower s
  convert proj using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun_true]
  simp only [target,decide_eq_true_eq,Function.comp_apply,π,Fin.addCases_left,Fin.addCases_right]
  constructor
  · rintro ⟨i,hi,hy⟩
    have h := hc i
    have hc' : x (vertex (c (a i))) = true ∨ x (vertex (c (b i))) = true := by
      rcases h with ⟨ha,hb⟩|⟨hb,ha⟩ <;> rw [ha,hb] <;> tauto
    rcases hc' with ha|hb
    · exact ⟨a i,p i,(idx.symm i).property,(mem i _).mpr (Or.inl rfl),ha,by rwa [tag_p]⟩
    · exact ⟨b i,p i,(idx.symm i).property,(mem i _).mpr (Or.inr rfl),hb,by rwa [tag_p]⟩
  · rintro ⟨l,u,hu,hj,hx,hy⟩
    let i := idx ⟨u,hu⟩
    have e : p i = u := by simp [p,i]
    rw [← e,tag_p] at hy
    rw [← e] at hj
    have hj := (mem i l).mp hj
    refine ⟨i,hy,?_⟩
    rcases hj with rfl|rfl <;> rcases hc i with ⟨ha,hb⟩|⟨hb,ha⟩ <;> simp_all


/-- A support larger than two has a line which neither of the other two
points reads. Pinning that input to false
preserves the triple function and decreases the number of lines. -/
theorem wide_three (S : Finset (Fin n)) (T : Finset (Fin n)) (h3 : T.card = 3)
    (ge : ∀ p ∈ T, 2 ≤ (sig I S p).card)
    {t : ℕ} (ht : HasMonoSize (n+n) (edgeFun (fun l p => l ∈ S ∧ I p l) T) t) : 8 ≤ t := by
  classical
  by_cases allTwo : ∀ p ∈ T, (sig I S p).card = 2
  · exact three_lower I S hj T allTwo h3 t ht
  push Not at allTwo
  obtain ⟨p,hp,wide⟩ := allTwo
  let B := (T.erase p).biUnion (fun r => (sig I S p).filter (I r))
  have small : B.card ≤ 2 := by
    calc
      _ ≤ ∑ r ∈ T.erase p, ((sig I S p).filter (I r)).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ T.erase p, 1 := Finset.sum_le_sum (fun r hr => by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact (hj p r (Finset.ne_of_mem_erase hr).symm).unique
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2,(Finset.mem_filter.mp ha).2⟩
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2,(Finset.mem_filter.mp hb).2⟩)
      _ = 2 := by simp [Finset.card_erase_of_mem hp,h3]
  have pick : ∃ a ∈ sig I S p, a ∉ B := by
    by_contra! sub
    have := Finset.card_le_card sub
    have := ge p hp
    omega
  obtain ⟨a,ha,unique⟩ := pick
  have haS := (Finset.mem_filter.mp ha).1
  have hpa := (Finset.mem_filter.mp ha).2
  have owns (r) (hr : r ∈ T) (h : I r a) : r = p := by
    by_contra ne
    exact unique (Finset.mem_biUnion.mpr ⟨r,Finset.mem_erase.mpr ⟨ne,hr⟩,Finset.mem_filter.mpr ⟨ha,h⟩⟩)
  have eqsig (r) : sig I (S.erase a) r = (sig I S r).erase a := by
    ext b; simp [sig,and_comm,and_left_comm]
  have remains (r) (hr : r ∈ T) : 2 ≤ (sig I (S.erase a) r).card := by
    rw [eqsig]
    by_cases h : a ∈ sig I S r
    · have e := owns r hr (Finset.mem_filter.mp h).2
      subst r
      rw [Finset.card_erase_of_mem h]
      have := ge p hp
      omega
    · simpa [Finset.erase_eq_of_notMem h] using ge r hr
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (remains p hp))
  obtain ⟨hbS,hpb⟩ := Finset.mem_filter.mp hb
  let J' := fun (l r : Fin n) => l ∈ S.erase a ∧ I r l
  let idx := Fin.castAdd n a
  let f := edgeFun (fun l p => l ∈ S ∧ I p l) T
  have eqf (x : Fin (n+n) → Bool) : f (Function.update x idx false) = edgeFun J' T x := by
    apply Bool.eq_iff_iff.mpr
    change edgeFun (fun l p => l ∈ S ∧ I p l) T _ = true ↔ edgeFun J' T _ = true
    rw [edgeFun_true,edgeFun_true]
    constructor
    · rintro ⟨l,r,hr,⟨hl,hi⟩,hx,hy⟩
      by_cases e : l = a
      · subst l; simp [idx] at hx
      · exact ⟨l,r,hr,⟨Finset.mem_erase.mpr ⟨e,hl⟩,hi⟩,by rwa [Function.update_of_ne (show Fin.castAdd n l ≠ idx from fun h => e (Fin.castAdd_injective n n h))] at hx,
          by rwa [Function.update_of_ne (left_ne_right a r).symm] at hy⟩
    · rintro ⟨l,r,hr,⟨hl,hi⟩,hx,hy⟩
      exact ⟨l,r,hr,⟨Finset.mem_of_mem_erase hl,hi⟩,
        by rwa [Function.update_of_ne (show Fin.castAdd n l ≠ idx from fun h => Finset.ne_of_mem_erase hl (Fin.castAdd_injective n n h))],
        by rwa [Function.update_of_ne (left_ne_right a r).symm]⟩
  have nc : ∃ x y, f (Function.update x idx false) ≠ f (Function.update y idx false) := by
    refine ⟨pairInput b p,fun _ => false,?_⟩
    rw [eqf,eqf,(Onlyfr.PrivateOrReader.pair_edge_iff J' _ _ _).mpr ⟨hp,hbS,hpb⟩,edgeFun_zero]
    decide
  have smaller := Onlyfr.PrivateGateDrop.restrict_input _ t f idx false ht nc
  rw [funext eqf] at smaller
  exact wide_three (S.erase a) T h3 remains smaller
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem haS

end Onlyfr.KMTripleBound
