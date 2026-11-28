import PEqualNP.Outside.PrivateGrid1009
import PEqualNP.Outside.PrivateGridRestore
import PEqualNP.Outside.PrivateGridAverage

namespace Onlyfr.PrivateGrid1009
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGridRestore

def coord (v : Bool) (i : Crossing) := if v then i.2 else i.1
def atCross (v : Bool) (a b : Axis) : Crossing := if v then (b,a) else (a,b)

private theorem active_index {l : Fin N} (h : l ∈ lines) : ∃ v a, l = line v a := by
  rcases Finset.mem_union.mp h with h|h <;> obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h
  · exact ⟨false,a,rfl⟩
  · exact ⟨true,a,rfl⟩

@[simp] theorem line_eq (v u : Bool) (a b : Axis) : line v a = line u b ↔ v=u ∧ a=b := by
  simp [line,priv]

def darkTest (v : Bool) (D : Finset Axis) : Point → Prop
  | .inl i => coord v i ∈ D
  | .inr (.inl (u,a,_)) => u=v ∧ a ∈ D
  | .inr (.inr u) => u=v
noncomputable def darkPoints (v : Bool) (D : Finset Axis) : Finset (Fin N) := by
  classical exact Finset.univ.filter (fun p => darkTest v D (idx.symm p))
noncomputable def darkLines (v : Bool) (D : Finset Axis) := D.image (line v)
noncomputable def patchEdges (v : Bool) (D : Finset Axis) : Finset (Fin N × Fin N) :=
  (D ×ˢ (Finset.univ : Finset Axis)).image (fun z => (cross (atCross v z.1 z.2),line (!v) z.2)) ∪
    (Finset.univ \ D).image (fun a => (hub v,line v a))
@[simp] theorem point_dark (v : Bool) (D : Finset Axis) (q : Point) :
    idx q ∈ darkPoints v D ↔ darkTest v D q := by simp [darkPoints]
@[simp] theorem line_dark (v u : Bool) (D : Finset Axis) (a : Axis) :
    line u a ∈ darkLines v D ↔ v=u ∧ a ∈ D := by
  simp [darkLines,and_comm]

private theorem covered (v : Bool) (D : Finset Axis) {l p : Fin N} (hl : l ∈ darkLines v D)
    (h : inc p l) : p ∈ darkPoints v D := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨q,rfl⟩ := idx.surjective p
  rw [point_dark]
  have hx := (at_line ..).mp h
  rcases q with ⟨r,c⟩|⟨⟨s,b,k⟩|s⟩
  · change coord v (r,c) ∈ D
    exact (congrArg (fun t : Axis => t ∈ D) (show coord v (r,c) = a from hx)).mpr ha
  · exact ⟨hx.1,hx.2.symm ▸ ha⟩
  · exact hx

theorem patch_spec (v : Bool) (D : Finset Axis) (p l : Fin N) :
    (p,l) ∈ patchEdges v D ↔ l ∈ lines \ darkLines v D ∧ p ∈ darkPoints v D ∧ inc p l := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨⟨a,b⟩,hab,eq⟩ := Finset.mem_image.mp h
      cases eq
      have ha := (Finset.mem_product.mp hab).1
      cases v <;> simp [atCross,cross,darkTest,coord,onLine,ha]
    · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp h
      cases eq
      have survive := (Finset.mem_sdiff.mp ha).2
      simp [hub,darkTest,onLine,survive]
  · rintro ⟨hl,hp,h⟩
    obtain ⟨s,b,rfl⟩ := active_index (Finset.mem_sdiff.mp hl).1
    have alive := (Finset.mem_sdiff.mp hl).2
    obtain ⟨q,rfl⟩ := idx.surjective p
    rw [point_dark] at hp
    have inc' := (at_line ..).mp h
    rcases q with ⟨r,c⟩|⟨⟨u,a,k⟩|u⟩
    · apply Finset.mem_union_left
      cases v <;> cases s <;> simp [darkTest,coord,onLine] at hp inc' <;> subst b
      · exact (alive (by simp [hp])).elim
      · exact Finset.mem_image.mpr ⟨(r,c),Finset.mem_product.mpr ⟨hp,Finset.mem_univ _⟩,rfl⟩
      · exact Finset.mem_image.mpr ⟨(c,r),Finset.mem_product.mpr ⟨hp,Finset.mem_univ _⟩,rfl⟩
      · exact (alive (by simp [hp])).elim
    · obtain ⟨uv,hd⟩ := hp
      obtain ⟨us,ab⟩ := inc'
      subst u; subst s; subst b
      exact (alive (by simp [hd])).elim
    · change u=v at hp
      change u=s at inc'
      subst s; subst u
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨b,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun h => alive (by simp [h])⟩,rfl⟩

noncomputable def star (v : Bool) (a : Axis) : Finset (Fin N) :=
  ((Finset.univ.image (fun b => cross (atCross v a b))) ∪
    Finset.univ.image (priv v a)) ∪ {hub v}

theorem star_iff (v : Bool) (a : Axis) (p : Fin N) : p ∈ star v a ↔ inc p (line v a) := by
  obtain ⟨q,rfl⟩ := idx.surjective p
  rcases q with ⟨r,c⟩|⟨⟨u,b,k⟩|u⟩ <;> cases v <;>
    simp [star,atCross,cross,priv,hub,onLine] <;> grind

theorem star_bound (v : Bool) (a : Axis) : (star v a).card ≤ 1010 := by
  unfold star
  apply le_trans (Finset.card_union_le ..)
  have h := Finset.card_union_le (Finset.univ.image (fun b => cross (atCross v a b))) (Finset.univ.image (priv v a))
  have x := Finset.card_image_le (s := Finset.univ) (f := fun b => cross (atCross v a b))
  have y := Finset.card_image_le (s := Finset.univ) (f := priv v a)
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_singleton] at *
  omega

private noncomputable def axisOf (i : Fin N) : Axis :=
  match idx.symm i with
  | .inr (.inl (_,a,_)) => a
  | _ => 0

@[simp] private theorem axis_line (v : Bool) (a : Axis) : axisOf (line v a) = a := by
  simp [axisOf,line,priv]

/-- Restore the full uncompressed grid after cutting any subset of one
pencil, including its common hub. The bound counts all eight private points. -/
theorem restore_grid {gs cs : List Gate} {o out : ℕ} (v : Bool) (D : Finset Axis)
    (least : MLeast (N+N) (edgeFun inc lines) gs o) (hc : MClean (N+N) cs)
    (agree : ∀ x, (∀ p ∈ darkPoints v D, x (Fin.castAdd N p) = false) →
      vl cs x out = edgeFun inc lines x) :
    gs.length ≤ cs.length + (2011*D.card+1001) := by
  classical
  let T := darkLines v D
  let Q := darkPoints v D
  let pts (l : Fin N) := star v (axisOf l)
  have sub : T ⊆ lines := by
    intro l h
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h
    exact line_mem ..
  have helper (l) (hl : l ∈ lines \ T) : l ∉ Q ∧ inc l l ∧ ∀ a ∈ lines \ T, inc l a → a=l := by
    obtain ⟨s,b,rfl⟩ := active_index (Finset.mem_sdiff.mp hl).1
    have survive := (Finset.mem_sdiff.mp hl).2
    change line s b ∉ darkLines v D at survive
    rw [line_dark] at survive
    refine ⟨?_,?_,?_⟩
    · change priv s b 0 ∉ darkPoints v D
      rw [priv,point_dark]
      change ¬(s=v ∧ b ∈ D)
      exact fun h => survive ⟨h.1.symm,h.2⟩
    · change inc (priv s b 0) (line s b)
      simp [priv,onLine]
    · intro a ha h
      obtain ⟨u,c,rfl⟩ := active_index (Finset.mem_sdiff.mp ha).1
      change inc (priv s b 0) (line u c) at h
      have e : s=u ∧ b=c := (at_line ..).mp h
      exact (line_eq ..).mpr ⟨e.1.symm,e.2.symm⟩
  have live : line (!v) 0 ∈ lines \ T := Finset.mem_sdiff.mpr ⟨line_mem ..,by
    change line (!v) 0 ∉ darkLines v D
    cases v <;> simp⟩
  have nb (l) (hl : l ∈ T) (p) : p ∈ pts l ↔ inc p l := by
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hl
    simpa only [pts,axis_line] using star_iff v a p
  have cost := restore_cut inc lines T Q sub least hc agree (fun l hl p h => covered v D hl h)
    (patchEdges v D) id (patch_spec v D) helper
    ⟨_,_,live,(helper _ live).1,(helper _ live).2.1⟩ pts nb (by
      intro l hl
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨hub v,(nb _ hl _).mpr (by simp [hub,onLine])⟩)
  have cnt : T.card = D.card := Finset.card_image_of_injective _ (fun a b e => ((line_eq ..).mp e).2)
  have stars := Finset.sum_le_sum (s := T) (fun l _ => Nat.add_le_add_right (star_bound v (axisOf l)) 1)
  change (∑ l ∈ T, ((pts l).card+1)) ≤ ∑ _l ∈ T, (1011 : ℕ) at stars
  rw [Finset.sum_const_nat (fun _ _ => rfl),cnt] at stars
  have bound : (patchEdges v D).card ≤ D.card*1001+(1001-D.card) := by
    unfold patchEdges
    apply le_trans (Finset.card_union_le ..)
    have h := Nat.add_le_add (Finset.card_image_le (s := D ×ˢ (Finset.univ : Finset Axis))
      (f := fun z => (cross (atCross v z.1 z.2),line (!v) z.2)))
      (Finset.card_image_le (s := Finset.univ \ D) (f := fun a => (hub v,line v a)))
    simpa only [Finset.card_product,Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ,Fintype.card_fin] using h
  have dh := Finset.card_le_card (Finset.subset_univ D)
  simp only [Finset.card_univ,Fintype.card_fin] at dh
  omega

open Onlyfr.PrivateGridMatching Onlyfr.PrivateGridRewire PEqualNP.MetaComplexity.Helpers.Readers
set_option maxRecDepth 4096

def crossingsOn (v : Bool) (D : Finset Axis) : Finset Crossing :=
  (D ×ˢ Finset.univ).image (fun z => atCross v z.1 z.2)

theorem crossing_on (v : Bool) (D : Finset Axis) (i : Crossing) :
    i ∈ crossingsOn v D ↔ coord v i ∈ D := by
  rcases i with ⟨a,b⟩
  cases v <;> simp [crossingsOn,coord,atCross,Finset.mem_image]

theorem crossing_count (v : Bool) (D : Finset Axis) : (crossingsOn v D).card = 1001*D.card := by
  have inj : Function.Injective (fun z : Crossing => atCross v z.1 z.2) := by
    rintro ⟨a,b⟩ ⟨c,d⟩ e
    cases v <;> simp [atCross] at e ⊢ <;> tauto
  simp [crossingsOn,Finset.card_image_of_injective _ inj,Nat.mul_comm]



/-- With the matching fixed before either pencil or its cut is chosen, every
cut satisfies the weighted reader bound in the uncompressed grid. -/
theorem pointwise_cut {gs : List Gate} {o : ℕ} (least : MLeast (N+N) (edgeFun inc lines) gs o)
    (ho : o < N+N+gs.length) (r t f : Crossing → ℕ) (fi : Function.Injective f)
    (reader : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (use : ∀ i, Reads gs (f i) (N+N+r i)) (v : Bool) (D : Finset Axis) :
    let U := crossingsOn v D
    let H := U.image t
    let A := Finset.univ.filter (fun i => t i ∈ H)
    A.card + (U.filter (fun i => N+N+f i ∈ Finset.univ.image t)).card ≤
      (1010*D.card+1001)+H.card := by
  classical
  intro U H A
  have hc := least.clean
  have ev := least.2.2.1
  have ri := incidence_reader_inj inc lines cross r t o hc ev reader sole sep
  let P : Set (Fin (N+N) → Bool) := {x | ∀ p ∈ darkPoints v D, x (Fin.castAdd N p) = false}
  have bound := indexed_cut hc ho (fun i => Fin.castAdd N (cross i)) r t f ri fi reader use
    (fun i => consumer_class inc lines cross r t hc ev reader sole sep i (f i) (use i))
    Finset.univ U (Finset.subset_univ _) P (2011*D.card+1001)
    (fun i hi x hx => hx _ ((point_dark ..).mpr ((crossing_on ..).mp hi))) (by
      intro i hi x hx
      have hit := (crossing_on ..).mp hi
      have on : inc (cross i) (line v (coord v i)) := by
        rcases i with ⟨a,b⟩; cases v <;> simp [cross,onLine,coord]
      exact dark_partner_sound inc lines (cross i) _ (line_mem ..) on hc ev (reader i) (sole i) x
        (fun p h => hx p (covered v D (Finset.mem_image_of_mem (line v) hit) h)))
    (fun cs out clean _ same => restore_grid v D least clean (fun x hx => (same x hx).trans (ev x)))
  change A.card+U.card+_ ≤ _+H.card at bound
  have count : U.card = 1001*D.card := crossing_count v D
  omega

/-- A ten-gate upper bound for one specified row yields a single matching
and both families of pointwise cut inequalities in its minimum circuit. -/
theorem cuts_of_ten {gs : List Gate} {o e : ℕ} (a : Axis) (ho : o < gs.length)
    (least : MLeast (N+N) (edgeFun inc lines) gs (N+N+o)) (ten : gs.length ≤ e+10)
    (emin : ∀ s, HasMonoSize (N+N) (edgeFun inc (lines.erase (line false a))) s → e ≤ s) :
    ∃ r t f : Crossing → ℕ, Function.Injective f ∧
      (∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i) ∧
        (∀ k, Reads gs k (Fin.castAdd N (cross i)) → k=r i) ∧ Reads gs (f i) (N+N+r i)) ∧
      ∀ v (D : Finset Axis),
        let U := crossingsOn v D
        let H := U.image t
        (Finset.univ.filter (fun i => t i ∈ H)).card +
          (U.filter (fun i => N+N+f i ∈ Finset.univ.image t)).card ≤ 1010*D.card+1001+H.card := by
  obtain ⟨r,t,f,fi,readers⟩ := matched_one_row a ho least ten emin
  refine ⟨r,t,f,fi,readers,?_⟩
  exact pointwise_cut least (by omega) r t f fi (fun i => (readers i).1)
    (fun i => (readers i).2.1) (fun i => (readers i).2.2)

private noncomputable def sideOf (i : Fin N) : Bool :=
  match idx.symm i with
  | .inr (.inl (v,_,_)) => v
  | _ => false

theorem lines_card : lines.card = 2002 := by
  have inj (v) : Function.Injective (line v) := fun _ _ e => ((line_eq ..).mp e).2
  have dis : Disjoint (Finset.univ.image (line false)) (Finset.univ.image (line true)) := by
    apply Finset.disjoint_left.mpr
    intro k h f
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp f
    exact Bool.noConfusion ((line_eq ..).mp e).1
  simp only [lines,Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ (inj _),
    Finset.card_univ,Fintype.card_fin]

/-- Start with one surviving edge, then append all 2,001 remaining stars.
The repeated seed edge is harmless and avoids any constant-gate convention. -/
theorem erased_upper (a : Axis) :
    HasMonoSize (N+N) (edgeFun inc (lines.erase (line false a))) 2023012 := by
  classical
  let S := lines.erase (line false a)
  let l := line true 0
  let p := priv true 0 0
  have hl : l ∈ S := Finset.mem_erase.mpr ⟨by simp [l,line_eq],line_mem ..⟩
  have hp : inc p l := by simp [p,l,onLine,priv]
  let U := Fin.castAdd N p
  let V := Fin.natAdd N l
  let base (x : Fin (N+N) → Bool) := x U && x V
  have clean : MClean (N+N) [] := by constructor <;> simp [CleanL,NotFree]
  obtain ⟨done,run⟩ := PrivateGridCompose.snoc_and clean (a := U.val) (by simp)
    (b := V.val) (by simp)
  have seed := Clean.ToolOfClean_proof (N+N) _ (N+N+([] : List Gate).length) done
  have eq : (fun x => vl ([] ++ [⟨GateOp.and,[U.val,V.val]⟩]) x (N+N+([] : List Gate).length)) = base := by
    funext x
    rw [(run x).1,vl_input _ _ _ U.isLt,vl_input _ _ _ V.isLt]
  rw [eq] at seed
  let pts (k : Fin N) := star (sideOf k) (axisOf k)
  have nb (k) (hk : k ∈ S) (q) : q ∈ pts k ↔ inc q k := by
    obtain ⟨v,b,rfl⟩ := active_index (Finset.mem_of_mem_erase hk)
    simpa only [pts,axis_line,show sideOf (line v b) = v by simp [sideOf,line,priv]] using star_iff v b q
  have h := append_lines base S pts (by
    intro k hk
    obtain ⟨v,b,rfl⟩ := active_index (Finset.mem_of_mem_erase hk)
    exact ⟨hub v,(nb _ hk _).mpr (by simp [hub,onLine])⟩) rfl ⟨fun _ => true,rfl⟩
    (show HasMonoSize (N+N) base 1 from seed)
  have all : addLines base S pts = edgeFun inc S := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [addLines,base,Bool.or_eq_true_iff,Bool.and_eq_true,decide_eq_true_eq,edgeFun_true]
    constructor
    · rintro (⟨hx,hs⟩|⟨k,hk,hs,q,hq,hx⟩)
      · exact ⟨p,l,hl,hp,hx,hs⟩
      · exact ⟨q,k,hk,(nb k hk q).mp hq,hx,hs⟩
    · rintro ⟨q,k,hk,inc,hx,hs⟩
      exact Or.inr ⟨k,hk,hs,q,(nb k hk q).mpr inc,hx⟩
  rw [all] at h
  have card : S.card=2001 := by rw [Finset.card_erase_of_mem (line_mem ..),lines_card]
  have budget := Finset.sum_le_sum (s := S) (fun k _ =>
    Nat.add_le_add_right (star_bound (sideOf k) (axisOf k)) 1)
  change (∑ k ∈ S, ((pts k).card+1)) ≤ ∑ _k ∈ S, (1011 : ℕ) at budget
  rw [Finset.sum_const_nat (fun _ _ => rfl),card] at budget
  exact h.mono (by omega)

/-- The reader and matched-partner counts in the cut theorem have the
precise fiber form used by the all-subsets average. -/
theorem incompatible_counts {gs : List Gate} {o : ℕ} (least : MLeast (N+N) (edgeFun inc lines) gs o)
    (ho : o < N+N+gs.length) (r t f : Crossing → ℕ) (fi : Function.Injective f)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (use : ∀ i, Reads gs (f i) (N+N+r i)) (B : ℕ)
    (size : 1001^2+(Finset.univ.image t).card+B ≤ 2023022)
    (matched : 1001^2 ≤ (Finset.univ.filter (fun i => N+N+f i ∈ Finset.univ.image t)).card+B)
    (probes : 2*1001^2 ≤ (Finset.univ.image t).card+8*B) : False := by
  classical
  let X : Finset Crossing := Finset.univ
  let M := X.filter (fun i => N+N+f i ∈ X.image t)
  have nx : X.card=1001^2 := by simp [X,Crossing,Axis,pow_two]
  apply PrivateGridAverage.fiber_contradiction X M t (coord false) (coord true)
    (fun i j e h => Prod.ext e h) nx B (by rw [nx]; exact size)
    (by rw [nx]; exact matched) (by rw [nx]; exact probes)
  intro c hc D
  obtain ⟨v,rfl⟩ : ∃ v, c=coord v := hc.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  have U : X.filter (fun i => coord v i ∈ D) = crossingsOn v D := by
    ext i
    simp only [X,Finset.mem_filter,Finset.mem_univ,true_and,crossing_on]
  have eq : M.filter (fun i => coord v i ∈ D) =
      (crossingsOn v D).filter (fun i => N+N+f i ∈ X.image t) := by
    ext i
    simp only [M,X,Finset.mem_filter,Finset.mem_univ,true_and,crossing_on,and_comm]
  dsimp only
  rw [U,eq]
  exact pointwise_cut least ho r t f fi rd sole use v D

end Onlyfr.PrivateGrid1009