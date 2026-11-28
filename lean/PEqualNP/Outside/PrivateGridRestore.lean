import PEqualNP.Outside.PrivateGridCompose
import PEqualNP.Outside.PrivateGridPin

namespace Onlyfr.PrivateGridRestore
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Loc Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGridPin
open Onlyfr.PrivateGridCompose

variable {n : ℕ}
def insertEdge (I : Rel n) (p l : Fin n) : Rel n := fun q a => I q a ∨ (q=p ∧ a=l)

/-- Copy a raw point bit into a private bit of its required line. This adds
one incidence and preserves every preexisting incidence of the source point. -/
theorem insert_via_private (I : Rel n) (S : Finset (Fin n)) (p l k : Fin n)
    (on : I k l) (privateBit : ∀ a ∈ S, I k a → a=l)
    {s : ℕ} (size : HasMonoSize (n+n) (edgeFun I S) s)
    (nc : ∃ x y, edgeFun I S x ≠ edgeFun I S y) :
    HasMonoSize (n+n) (edgeFun (insertEdge I p l) S) (s+1) := by
  let K := Fin.castAdd n k
  let P := Fin.castAdd n p
  have h := add_twin (edgeFun I S) size nc K P
  convert h using 1
  funext x
  let y := Function.update x K (x K || x P)
  change edgeFun (insertEdge I p l) S x = edgeFun I S y
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun_true,edgeFun_true]
  have sel (a) : y (Fin.natAdd n a) = x (Fin.natAdd n a) := Function.update_of_ne (left_ne_right k a).symm ..
  have self : y K = (x K || x P) := Function.update_self ..
  have other (q) (ne : q ≠ k) : y (Fin.castAdd n q) = x (Fin.castAdd n q) :=
    Function.update_of_ne (fun e => ne (Fin.castAdd_injective n n e)) ..
  constructor
  · rintro ⟨q,a,ha,old|⟨rfl,rfl⟩,hq,hs⟩
    · by_cases e : q=k
      · subst q
        exact ⟨k,a,ha,old,self.trans (Bool.or_eq_true_iff.mpr (Or.inl hq)),(sel a).trans hs⟩
      · exact ⟨q,a,ha,old,(other q e).trans hq,(sel a).trans hs⟩
    · exact ⟨k,_,ha,on,self.trans (Bool.or_eq_true_iff.mpr (Or.inr hq)),(sel _).trans hs⟩
  · rintro ⟨q,a,ha,old,hq,hs⟩
    rw [sel] at hs
    by_cases e : q=k
    · subst q
      rcases Bool.or_eq_true_iff.mp (self.symm.trans hq) with hk|hp
      · exact ⟨k,a,ha,Or.inl old,hk,hs⟩
      · exact ⟨p,a,ha,Or.inr ⟨rfl,privateBit a ha old⟩,hp,hs⟩
    · exact ⟨q,a,ha,Or.inl old,(other q e).symm.trans hq,hs⟩

def extended (I : Rel n) (A : Finset (Fin n × Fin n)) : Rel n := fun p l => I p l ∨ (p,l) ∈ A

theorem copy_edges (I : Rel n) (S : Finset (Fin n)) (A : Finset (Fin n × Fin n))
    (w : Fin n → Fin n) (helper : ∀ z ∈ A, I (w z.2) z.2 ∧ ∀ a ∈ S, I (w z.2) a → a=z.2)
    (fresh : ∀ z ∈ A, ∀ u ∈ A, w z.2 ≠ u.1)
    (active : ∃ p l, l ∈ S ∧ I p l) {s : ℕ} (size : HasMonoSize (n+n) (edgeFun I S) s) :
    HasMonoSize (n+n) (edgeFun (extended I A) S) (s+A.card) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have eq : extended I ∅ = I := by funext q l; simp [extended]
    simpa only [eq,Finset.card_empty,Nat.add_zero] using size
  | @insert z A hz ih =>
    have sub := Finset.subset_insert z A
    have prev := ih (fun v hv => helper v (sub hv)) (fun v hv u hu => fresh v (sub hv) u (sub hu))
    obtain ⟨p,l,hl,inc⟩ := active
    obtain ⟨on,only⟩ := helper z (Finset.mem_insert_self ..)
    have added := insert_via_private (extended I A) S z.1 z.2 (w z.2) (Or.inl on) (by
      intro a ha e
      rcases e with e|e
      · exact only a ha e
      · exact False.elim (fresh z (Finset.mem_insert_self ..) _ (sub e) rfl)) prev
      (active_nc _ _ hl (Or.inl inc))
    have eq : insertEdge (extended I A) z.1 z.2 = extended I (insert z A) := by
      funext q l
      apply propext
      simp only [insertEdge,extended,Finset.mem_insert]
      rcases z with ⟨a,b⟩
      simp only [Prod.mk.injEq]
      tauto
    rw [eq] at added
    rw [Finset.card_insert_of_notMem hz]
    exact added

noncomputable def addLines (base : (Fin (n+n) → Bool) → Bool) (T : Finset (Fin n))
    (P : Fin n → Finset (Fin n)) (x : Fin (n+n) → Bool) : Bool := by
  classical exact base x || decide (∃ l ∈ T, x (Fin.natAdd n l) = true ∧
    ∃ p ∈ P l, x (Fin.castAdd n p) = true)

/-- Physically append arbitrary missing lines at the sum of their individual
star costs. Shared hub and crossing inputs may occur in many of these stars. -/
theorem append_lines (base : (Fin (n+n) → Bool) → Bool) (T : Finset (Fin n))
    (P : Fin n → Finset (Fin n)) (nonempty : ∀ l ∈ T, (P l).Nonempty)
    (zero : base (fun _ => false) = false) (yes : ∃ x, base x = true)
    {s : ℕ} (size : HasMonoSize (n+n) base s) :
    HasMonoSize (n+n) (addLines base T P) (s+∑ l ∈ T, ((P l).card+1)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have eq : addLines base ∅ P = base := by funext x; simp [addLines]
    simpa [eq] using size
  | @insert l T hl ih =>
    have prev := ih (fun k hk => nonempty k (Finset.mem_insert_of_mem hk))
    obtain ⟨x,hx⟩ := yes
    have nc : ∃ x y, addLines base T P x ≠ addLines base T P y :=
      ⟨x,fun _ => false,by simp [addLines,hx,zero]⟩
    let A := (P l).image (Fin.castAdd n)
    have aPos : A.Nonempty := (nonempty l (Finset.mem_insert_self ..)).image _
    have run := add_star _ prev nc (Fin.natAdd n l) A aPos
    have eq : (fun x : Fin (n+n) → Bool => addLines base T P x ||
        (x (Fin.natAdd n l) && decide (∃ u ∈ A, x u = true))) = addLines base (insert l T) P := by
      funext y
      apply Bool.eq_iff_iff.mpr
      simp only [addLines,Bool.or_eq_true_iff,Bool.and_eq_true,decide_eq_true_eq,
        Finset.exists_mem_insert,A,Finset.exists_mem_image]
      simp only [or_left_comm,or_comm]
    rw [eq] at run
    have card : A.card = (P l).card := Finset.card_image_of_injective _ (Fin.castAdd_injective n n)
    rw [Finset.sum_insert hl]
    exact run.mono (by omega)

/-- Restore a cut from any circuit correct on its zero subcube. Missing
incidences on surviving lines are copied into private inputs, and every
removed line is then appended. The bound applies to the actual least circuit. -/
theorem restore_cut {gs cs : List PEqualNP.CircuitLowerBounds.Gate} {o v : ℕ}
    (I : Rel n) (S T Q : Finset (Fin n)) (sub : T ⊆ S)
    (least : MLeast (n+n) (edgeFun I S) gs o) (hc : MClean (n+n) cs)
    (agree : ∀ x, (∀ p ∈ Q, x (Fin.castAdd n p) = false) → vl cs x v = edgeFun I S x)
    (allDark : ∀ l ∈ T, ∀ p, I p l → p ∈ Q)
    (A : Finset (Fin n × Fin n)) (w : Fin n → Fin n)
    (missing : ∀ p l, (p,l) ∈ A ↔ l ∈ S \ T ∧ p ∈ Q ∧ I p l)
    (privateBit : ∀ l ∈ S \ T, w l ∉ Q ∧ I (w l) l ∧ ∀ a ∈ S \ T, I (w l) a → a=l)
    (alive : ∃ p l, l ∈ S \ T ∧ p ∉ Q ∧ I p l)
    (pts : Fin n → Finset (Fin n)) (neighbors : ∀ l ∈ T, ∀ p, p ∈ pts l ↔ I p l)
    (nonempty : ∀ l ∈ T, (pts l).Nonempty) :
    gs.length ≤ cs.length+A.card+∑ l ∈ T, ((pts l).card+1) := by
  classical
  let B : Rel n := fun p l => p ∉ Q ∧ I p l
  let inp := Q.image (Fin.castAdd n)
  have point (p) : Fin.castAdd n p ∈ inp ↔ p ∈ Q := by simp [inp]
  have line (l) : Fin.natAdd n l ∉ inp := by
    intro h
    obtain ⟨p,_,e⟩ := Finset.mem_image.mp h
    exact left_ne_right p l e
  have restricted (x) : edgeFun I S (PrivateGateDrop.pin inp x) = edgeFun B (S \ T) x := by
    apply Bool.eq_iff_iff.mpr
    rw [edgeFun_true,edgeFun_true]
    constructor
    · rintro ⟨p,l,hl,inc,hp,hs⟩
      have survive : p ∉ Q := by
        intro h
        simp [PrivateGateDrop.pin,(point p).mpr h] at hp
      have ht : l ∉ T := fun h => survive (allDark l h p inc)
      exact ⟨p,l,Finset.mem_sdiff.mpr ⟨hl,ht⟩,⟨survive,inc⟩,by
        simpa only [PrivateGateDrop.pin,ite_eq_right (fun h => survive ((point p).mp h))] using hp,
        by simpa only [PrivateGateDrop.pin,ite_eq_right (line l)] using hs⟩
    · rintro ⟨p,l,hl,⟨survive,inc⟩,hp,hs⟩
      exact ⟨p,l,(Finset.mem_sdiff.mp hl).1,inc,by
        simpa only [PrivateGateDrop.pin,ite_eq_right (fun h => survive ((point p).mp h))] using hp,
        by simpa only [PrivateGateDrop.pin,ite_eq_right (line l)] using hs⟩
  obtain ⟨p,l,hl,hq,inc⟩ := alive
  have nc := active_nc B _ hl (show B p l from ⟨hq,inc⟩)
  have start := PrivateGridRewire.size_from_subcube inp hc (edgeFun I S) v (fun x hx =>
    agree x (fun p h => hx _ ((point p).mpr h))) (by simpa only [restricted] using nc)
  simp only [restricted] at start
  have copied := copy_edges B (S \ T) A w (by
    intro z hz
    have h := privateBit _ ((missing ..).mp hz).1
    exact ⟨⟨h.1,h.2.1⟩,fun a ha i => h.2.2 a ha i.2⟩) (by
    intro z hz u hu e
    exact (privateBit _ ((missing ..).mp hz).1).1 (e.symm ▸ ((missing ..).mp hu).2.1))
    ⟨p,l,hl,hq,inc⟩ start
  have complete : edgeFun (extended B A) (S \ T) = edgeFun I (S \ T) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [edgeFun_true,edgeFun_true]
    constructor
    · rintro ⟨q,a,ha,old|new,hx,hs⟩
      · exact ⟨q,a,ha,old.2,hx,hs⟩
      · exact ⟨q,a,ha,((missing ..).mp new).2.2,hx,hs⟩
    · rintro ⟨q,a,ha,old,hx,hs⟩
      by_cases h : q ∈ Q
      · exact ⟨q,a,ha,Or.inr ((missing ..).mpr ⟨ha,h,old⟩),hx,hs⟩
      · exact ⟨q,a,ha,Or.inl ⟨h,old⟩,hx,hs⟩
  rw [complete] at copied
  have built := append_lines _ T pts nonempty (edgeFun_zero ..) ⟨_,pair_on I _ hl inc⟩ copied
  have full : addLines (edgeFun I (S \ T)) T pts = edgeFun I S := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [addLines,Bool.or_eq_true_iff,decide_eq_true_eq,edgeFun_true]
    constructor
    · rintro (⟨q,a,ha,old,hx,hs⟩|⟨a,ha,hs,q,hq,hx⟩)
      · exact ⟨q,a,(Finset.mem_sdiff.mp ha).1,old,hx,hs⟩
      · exact ⟨q,a,sub ha,(neighbors a ha q).mp hq,hx,hs⟩
    · rintro ⟨q,a,ha,old,hx,hs⟩
      by_cases h : a ∈ T
      · exact Or.inr ⟨a,h,hs,q,(neighbors a h q).mpr old,hx⟩
      · exact Or.inl ⟨q,a,Finset.mem_sdiff.mpr ⟨ha,h⟩,old,hx,hs⟩
  rw [full] at built
  obtain ⟨ls,out,hcl,hn,len,ev⟩ := Clean.mclean_of _ _ _ (active_nc I S (Finset.mem_sdiff.mp hl).1 inc) built
  exact (least.2.2.2 ls out hcl hn ev).trans len

end Onlyfr.PrivateGridRestore
