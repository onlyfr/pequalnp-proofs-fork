import PEqualNP.Outside.PrivateArcMarginal
import PEqualNP.Outside.PrivateIncidenceDrop

namespace Onlyfr.PrivateGridPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGateDrop

variable {n : ℕ}
abbrev Rel (n : ℕ) := Fin n → Fin n → Prop
def off (I : Rel n) (p : Fin n) : Rel n := fun q a => q ≠ p ∧ I q a

theorem pin_point (I : Rel n) (S : Finset (Fin n)) (p : Fin n) (x : Fin (n+n) → Bool) :
    edgeFun I S (Function.update x (Fin.castAdd n p) false) = edgeFun (off I p) S x := by
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun_true,edgeFun_true]
  constructor
  · rintro ⟨q,a,ha,inc,hq,hs⟩
    have neq : q ≠ p := by rintro rfl; simp at hq
    rw [Function.update_of_ne (fun e => neq (Fin.castAdd_injective n n e))] at hq
    rw [Function.update_of_ne (left_ne_right p a).symm] at hs
    exact ⟨q,a,ha,⟨neq,inc⟩,hq,hs⟩
  · rintro ⟨q,a,ha,⟨neq,inc⟩,hq,hs⟩
    exact ⟨q,a,ha,inc,by rwa [Function.update_of_ne (fun e => neq (Fin.castAdd_injective n n e))],
      by rwa [Function.update_of_ne (left_ne_right p a).symm]⟩

theorem pair_on (I : Rel n) (S : Finset (Fin n)) {p l : Fin n} (hl : l ∈ S) (inc : I p l) :
    edgeFun I S (pairInput p l) = true := (edgeFun_true ..).mpr
      ⟨p,l,hl,inc,by rw [pair_point]; simp,by rw [pair_line]; simp⟩

theorem active_nc (I : Rel n) (S : Finset (Fin n)) {p l : Fin n} (hl : l ∈ S) (inc : I p l) :
    ∃ x y, edgeFun I S x ≠ edgeFun I S y :=
  ⟨pairInput p l,fun _ => false,by rw [pair_on I S hl inc,edgeFun_zero]; decide⟩

theorem active_dep (I : Rel n) (S : Finset (Fin n)) {p l : Fin n} (hl : l ∈ S) (inc : I p l) :
    Dep (edgeFun I S) (Fin.castAdd n p) := by
  refine ⟨pairInput p l,?_⟩
  rw [pair_point,show (!(decide (p=p))) = false by simp,pin_point,pair_on I S hl inc]
  intro e
  obtain ⟨q,a,_,⟨ne,_⟩,hq,_⟩ := (edgeFun_true ..).mp e
  exact ne (of_decide_eq_true ((pair_point ..).symm.trans hq))

/-- Private bits disappear from the incidence function once their line is erased. -/
theorem private_off (I : Rel n) (S : Finset (Fin n)) {p l : Fin n}
    (priv : ∀ a ∈ S.erase l, ¬ I p a) : edgeFun (off I p) (S.erase l) = edgeFun I (S.erase l) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun_true,edgeFun_true]
  constructor
  · rintro ⟨q,a,ha,⟨_,inc⟩,hq,hs⟩
    exact ⟨q,a,ha,inc,hq,hs⟩
  · rintro ⟨q,a,ha,inc,hq,hs⟩
    exact ⟨q,a,ha,⟨fun e => priv a ha (e ▸ inc),inc⟩,hq,hs⟩

/-- Both phases of a private point give the erased function when its line
is subsequently pinned to zero. -/
theorem pin_both (I : Rel n) (S : Finset (Fin n)) {p l : Fin n}
    (priv : ∀ a ∈ S.erase l, ¬ I p a) (b : Bool) (x : Fin (n+n) → Bool) :
    edgeFun I S (Function.update (Function.update x (Fin.natAdd n l) false) (Fin.castAdd n p) b) =
      edgeFun I (S.erase l) x := by
  let y := Function.update (Function.update x (Fin.natAdd n l) false) (Fin.castAdd n p) b
  have sel (a) : y (Fin.natAdd n a) = (if a=l then false else x (Fin.natAdd n a)) := by
    dsimp only [y]
    rw [Function.update_of_ne (left_ne_right p a).symm]
    by_cases e : a=l
    · subst a; simp
    · rw [Function.update_of_ne (fun h => e (Fin.natAdd_injective n n h)),ite_eq_right e]
  have pt (q) (neq : q ≠ p) : y (Fin.castAdd n q) = x (Fin.castAdd n q) := by
    simp only [y,Function.update_of_ne (fun h => neq (Fin.castAdd_injective n n h)),
      Function.update_of_ne (left_ne_right q l)]
  change edgeFun I S y = _
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun_true,edgeFun_true]
  constructor
  · rintro ⟨q,a,ha,inc,hq,hs⟩
    have ne : a ≠ l := by rintro rfl; rw [sel,ite_eq_left rfl] at hs; contradiction
    have active := Finset.mem_erase.mpr ⟨ne,ha⟩
    rw [sel,ite_eq_right ne] at hs
    exact ⟨q,a,active,inc,(pt q (fun e => priv a active (e ▸ inc))).symm.trans hq,hs⟩
  · rintro ⟨q,a,ha,inc,hq,hs⟩
    exact ⟨q,a,Finset.mem_of_mem_erase ha,inc,(pt q (fun e => priv a ha (e ▸ inc))).trans hq,
      by rwa [sel,ite_eq_right (Finset.ne_of_mem_erase ha)]⟩

/-- One private point, a different incident witness and a surviving edge
give three gate deletions: two on one phase, then one on the selector. -/
theorem last_three (I : Rel n) (S : Finset (Fin n)) {p l w r a : Fin n}
    (hl : l ∈ S) (hp : I p l) (priv : ∀ v ∈ S.erase l, ¬ I p v)
    (ne : w ≠ p) (inc : I w l) (ha : a ∈ S.erase l) (survive : I r a)
    {s : ℕ} (size : HasMonoSize (n+n) (edgeFun I S) s) :
    ∃ t, t+3 ≤ s ∧ HasMonoSize (n+n) (edgeFun I (S.erase l)) t := by
  let U := Fin.castAdd n p
  let L := Fin.natAdd n l
  let f (b : Bool) (x : Fin (n+n) → Bool) := edgeFun I S (Function.update x U b)
  have erase (b) (x) : f b (Function.update x L false) = edgeFun I (S.erase l) x :=
    pin_both I S priv b x
  obtain ⟨x,y,xy⟩ := active_nc I _ ha survive
  have nonconst (b) : ∃ v z, f b v ≠ f b z :=
    ⟨_,_,fun e => xy ((erase b x).symm.trans (e.trans (erase b y)))⟩
  obtain ⟨b,t,ht,hf⟩ := PrivateArcMarginal.expensive_phase U (active_dep I S hl hp) size nonconst
  let z := pairInput w l
  have pos : f b z = true := (edgeFun_true ..).mpr ⟨w,l,hl,inc,by
    rw [Function.update_of_ne (fun h => ne (Fin.castAdd_injective n n h))]; simp only [z,pair_point,decide_true],by
    rw [Function.update_of_ne (left_ne_right p l).symm]; simp only [z,pair_line,decide_true]⟩
  have negative : edgeFun I (S.erase l) z ≠ true := by
    intro e
    obtain ⟨_,v,hv,_,_,sel⟩ := (edgeFun_true ..).mp e
    exact Finset.ne_of_mem_erase hv (of_decide_eq_true ((pair_line ..).symm.trans sel))
  have dep : Dep (f b) L := by
    refine ⟨z,?_⟩
    have on : z L = true := by change pairInput w l (Fin.natAdd n l) = true; rw [pair_line]; simp
    rw [on]; change f b (Function.update z L false) ≠ _
    rw [erase,pos]; exact negative
  obtain ⟨v,hv,done⟩ := one_input _ _ (f b) L false hf dep ⟨x,y,by simpa only [erase] using xy⟩
  rw [show (fun x => f b (Function.update x L false)) = _ from funext (erase b)] at done
  exact ⟨v,by omega,done⟩

/-- Pin the other private points one at a time, then use the expensive
phase of the last private point. The bound is |P|+3 for |P|+1 private points. -/
theorem private_drop (S : Finset (Fin n)) (l p w r a : Fin n) (P : Finset (Fin n))
    (I : Rel n) (hl : l ∈ S) (hp : I p l) (priv : ∀ v ∈ S.erase l, ¬ I p v)
    (ne : w ≠ p) (inc : I w l) (ha : a ∈ S.erase l) (survive : I r a)
    (outside : p ∉ P) (wout : w ∉ P)
    (points : ∀ q ∈ P, I q l ∧ ∀ v ∈ S.erase l, ¬ I q v)
    {s : ℕ} (size : HasMonoSize (n+n) (edgeFun I S) s) :
    ∃ t, t+P.card+3 ≤ s ∧ HasMonoSize (n+n) (edgeFun I (S.erase l)) t := by
  classical
  induction P using Finset.induction_on generalizing I s with
  | empty => simpa using last_three I S hl hp priv ne inc ha survive size
  | @insert q P fresh ih =>
    have qmem := Finset.mem_insert_self q P
    have ql := points q qmem
    have diff : r ≠ q := fun e => ql.2 a ha (e ▸ survive)
    have nc := active_nc (off I q) S (Finset.mem_of_mem_erase ha) (show off I q r a from ⟨diff,survive⟩)
    have eq : (fun x => edgeFun I S (Function.update x (Fin.castAdd n q) false)) = edgeFun (off I q) S :=
      funext (pin_point I S q)
    obtain ⟨v,hv,pinned⟩ := one_input _ _ _ _ false size (active_dep I S hl ql.1) (by simpa only [pin_point] using nc)
    rw [eq] at pinned
    have pn : p ≠ q ∧ p ∉ P := by simpa using outside
    have wn : w ≠ q ∧ w ∉ P := by simpa using wout
    obtain ⟨t,ht,done⟩ := ih (off I q) ⟨pn.1,hp⟩ (fun v h inc => priv v h inc.2)
      ⟨wn.1,inc⟩ ⟨diff,survive⟩ pn.2 wn.2 (by
        intro k hk
        have orig := points k (Finset.mem_insert_of_mem hk)
        exact ⟨⟨fun e => fresh (e ▸ hk),orig.1⟩,fun v h i => orig.2 v h i.2⟩) pinned
    rw [private_off I S ql.2] at done
    rw [Finset.card_insert_of_notMem fresh]
    exact ⟨t,by omega,done⟩

/-- After crossing c is fixed off, these witnesses remain on the deleted
line: eight private points, another incident point, and an edge on a survivor. -/
structure EightPrivate (I : Rel n) (S : Finset (Fin n)) (l c : Fin n) where
  seven : Finset (Fin n)
  card : seven.card = 7
  last : Fin n
  keep : Fin n
  survivor : Fin n
  point : Fin n
  active : l ∈ S
  lastOn : off I c last l
  privateLast : ∀ v ∈ S.erase l, ¬ off I c last v
  different : keep ≠ last
  keepOn : off I c keep l
  survived : survivor ∈ S.erase l
  edge : off I c point survivor
  lastOut : last ∉ seven
  keepOut : keep ∉ seven
  privateSeven : ∀ q ∈ seven, off I c q l ∧ ∀ v ∈ S.erase l, ¬ off I c q v

theorem pinned_ten (I : Rel n) (S : Finset (Fin n)) (l c : Fin n)
    (w : EightPrivate I S l c) {s : ℕ}
    (size : HasMonoSize (n+n) (fun x => edgeFun I S (Function.update x (Fin.castAdd n c) false)) s) :
    ∃ t, t+10 ≤ s ∧ HasMonoSize (n+n)
      (fun x => edgeFun I (S.erase l) (Function.update x (Fin.castAdd n c) false)) t := by
  simp only [pin_point] at size ⊢
  obtain ⟨t,bound,done⟩ := private_drop S l w.last w.keep w.point w.survivor w.seven (off I c)
    w.active w.lastOn w.privateLast w.different w.keepOn w.survived w.edge w.lastOut w.keepOut
    w.privateSeven size
  rw [w.card] at bound
  exact ⟨t,by omega,done⟩

end Onlyfr.PrivateGridPin
