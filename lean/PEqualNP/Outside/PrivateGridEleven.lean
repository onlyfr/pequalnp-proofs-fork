import PEqualNP.Outside.PrivateGridCharges

namespace Onlyfr.PrivateGrid1009
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGridRewire Onlyfr.PrivateGridMatching
set_option maxRecDepth 4096

private abbrev wire (k : ℕ) := N+N+k
private def sig (gs : List Gate) (w : ℕ) (v : Bool) (a : Axis) :=
  vl gs (singleton (Fin.natAdd N (line v a))) w = true

/-- A partner hit twice by one crossing needs an internal operand outside
the readers and partners. Its singleton-selector signature identifies both
coordinates of that crossing. -/
theorem duplicate_witness {gs : List Gate} {o : ℕ}
    (least : MLeast (N+N) (edgeFun inc lines) gs o) (r t : Crossing → ℕ)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (i z : Crossing) (k : ℕ) (part : wire k=t z) (use : Reads gs k (wire (r i)))
    (both : ∀ v, let l := line v (coord v i)
      let x := singleton (Fin.natAdd N l)
      let y := pairInput (cross i) l
      vl gs x (wire k) ≠ vl gs y (wire k) ∧
      ∀ w, Reads gs k w → w ≠ wire (r i) → vl gs x w = vl gs y w) :
    ∃ w, N+N ≤ w ∧ w < N+N+gs.length ∧ (∀ j, w ≠ wire (r j)) ∧ (∀ j, w ≠ t j) ∧
      ∀ v a, sig gs w v a ↔ a = coord v i := by
  have hc := least.clean
  obtain ⟨g,hg,hand⟩ := (consumer_class inc lines cross r t hc least.2.2.1 rd sole sep i k use).2 z part
  obtain ⟨g',hg',mem⟩ := use
  cases Option.some.inj (hg.symm.trans hg')
  obtain ⟨a,b,_,_,ins,_⟩ := Free.vl_bin least.1 hc.2 hg
  have haveW : ∃ w, Reads gs k w ∧ ∀ x : Fin (N+N) → Bool, vl gs x (wire k) = (vl gs x (wire (r i)) && vl gs x w) := by
    rcases (show wire (r i)=a ∨ wire (r i)=b by simpa [ins] using mem) with eq|eq
    · refine ⟨b,⟨g,hg,by simp [ins]⟩,fun x => ?_⟩
      rw [show wire k=N+N+k from rfl,vl_gate _ least.1 _ _ _ hg,hand,ins,eq]
      simp [GateOp.eval]
    · refine ⟨a,⟨g,hg,by simp [ins]⟩,fun x => ?_⟩
      rw [show wire k=N+N+k from rfl,vl_gate _ least.1 _ _ _ hg,hand,ins,eq]
      simp [GateOp.eval,Bool.and_comm]
  obtain ⟨w,hw,gate⟩ := haveW
  let raw := Fin.castAdd N (cross i)
  have readOn (x : Fin (N+N) → Bool) (h : x raw=true) : vl gs x (wire (r i))=true := by
    rw [show wire (r i)=N+N+r i from rfl,orrd_eval least.1 (rd i)]
    exact Bool.or_eq_true_iff.mpr (Or.inl ((vl_input _ _ _ raw.isLt).trans h))
  have wr : w ≠ wire (r i) := by
    intro e
    apply partner_off_singleton z least (rd z) (sole z) raw
    rw [←part,gate,e,readOn _ (decide_eq_true rfl)]
    rfl
  have top (v) : sig gs w v (coord v i) := by
    obtain ⟨diff,agree⟩ := both v
    change vl gs _ w = true
    by_contra! no
    have off := Bool.eq_false_iff.mpr no
    have off' := (agree _ hw wr).symm.trans off
    apply diff
    rw [gate,gate,off,off']; simp
  have lim : w < N+N+gs.length := by
    have := reads_lt least.1 hw
    have := reads_len hw
    omega
  have zi : z ≠ i := by
    rintro rfl
    obtain ⟨q,hq,_,hs⟩ := rd z
    have ht : Reads gs (r z) (t z) := ⟨q,hq,by rcases hs with h|h <;> simp [h]⟩
    have e := reads_lt least.1 ht
    have f := reads_lt least.1 (show Reads gs k (wire (r z)) from ⟨g,hg,mem⟩)
    dsimp only [wire] at *
    omega
  have unique (v a) (on : sig gs w v a) : a = coord v i := by
    let l := line v a
    let y := pairInput (cross i) l
    have lifted : vl gs y w = true := wire_mono hc _ y (by
      intro j hj
      exact decide_eq_true (Or.inr (of_decide_eq_true hj))) w lim on
    have rawOn : y raw = true := by change pairInput (cross i) l (Fin.castAdd N (cross i)) = true; rw [pair_point]; simp
    have yes : vl gs y (t z) = true := by rw [←part,gate,readOn y rawOn,lifted]; rfl
    obtain ⟨s,hs,hz,miss⟩ := sep z i zi
    have dark q (hq : inc q s) : y (Fin.castAdd N q) = false := by
      change pairInput (cross i) l (Fin.castAdd N q) = false
      rw [pair_point]; exact decide_eq_false (fun e => miss (e ▸ hq))
    have edge := dark_partner_sound inc lines _ s hs hz hc least.2.2.1 (rd z) (sole z) y dark yes
    rw [least.2.2.1] at edge
    have inc' := ((Onlyfr.PrivateOrReader.pair_edge_iff inc lines (cross i) l).mp edge).2
    rcases i with ⟨b,c⟩
    cases v <;> apply Eq.symm <;> simpa [l,cross,onLine,coord] using inc'
  refine ⟨w,?_,lim,?_,?_,fun v a => ⟨unique v a,fun e => e.symm ▸ top v⟩⟩
  · by_contra! lt
    have hit (v) : (⟨w,lt⟩ : Fin (N+N)) = Fin.natAdd N (line v (coord v i)) := by
      have h := top v
      unfold sig at h
      rw [vl_input _ _ _ lt] at h
      exact of_decide_eq_true h
    have e := Fin.natAdd_injective N N ((hit false).symm.trans (hit true))
    exact Bool.noConfusion ((line_eq ..).mp e).1
  · intro j e
    have h := top false
    unfold sig at h
    rw [e,show wire (r j)=N+N+r j from rfl,orrd_eval least.1 (rd j)] at h
    rcases Bool.or_eq_true_iff.mp h with h|h
    · rw [vl_input _ _ _ (Fin.castAdd N (cross j)).isLt] at h
      exact left_ne_right (cross j) _ (of_decide_eq_true h)
    · exact partner_off_singleton j least (rd j) (sole j) _ h
  · intro j e
    exact partner_off_singleton j least (rd j) (sole j) _ (e ▸ top false)

/-- Count a double hit once, at the second side of its crossing. -/
def duplicateHits {J : Type*} [Fintype J] (T : Finset ℕ) (k : J × Bool → ℕ) :
    Finset (J × Bool) :=
  (Finset.univ.filter (fun p => k p ∈ T)).filter
    (fun p => p.2=true ∧ k (p.1,false)=k (p.1,true))

/-- Probes reaching a partner normally spend one slot there. The second
side of a duplicate uses its identifying outside wire. Outside consumers
have four slots indexed by operand position and probe side. -/
private theorem slots {J : Type*} [Fintype J] (T B : Finset ℕ)
    (k : J × Bool → ℕ) (port : J × Bool → Bool) (identifies : ℕ → J → Prop)
    (ident : ∀ w i j, identifies w i → identifies w j → i=j)
    (whereK : ∀ p, k p ∉ T → k p ∈ B)
    (exclusive : ∀ p q, k p ∈ T → k p=k q → p.1=q.1)
    (portUnique : ∀ p q, k p=k q → port p=port q → p.1=q.1)
    (witness : ∀ i, k (i,false) ∈ T → k (i,false)=k (i,true) → ∃ w ∈ B, identifies w i) :
    (duplicateHits T k).card ≤ B.card ∧ 2*Fintype.card J ≤ T.card+5*B.card := by
  classical
  let X : Finset (J × Bool) := Finset.univ
  let P := X.filter (fun p => k p ∈ T)
  let D := P.filter (fun p => p.2=true ∧ k (p.1,false)=k (p.1,true))
  have inside (p) (hp : p ∈ P) : k p ∈ T := (Finset.mem_filter.mp hp).2
  have duplicate (p : D) : ∃ w ∈ B, identifies w p.val.1 := by
    obtain ⟨hp,ht,e⟩ := Finset.mem_filter.mp p.property
    have eq : (p.val.1,true) = p.val := Prod.ext rfl ht.symm
    apply witness _ _ e
    rw [e,eq]; exact inside _ hp
  choose w hw hs using duplicate
  have dw : D.card ≤ B.card := by
    have h := Finset.card_le_card_of_injOn (s := D.attach) (t := B) w
      (fun p _ => hw p) (by
        intro p _ q _ eq
        apply Subtype.ext
        apply Prod.ext (ident _ _ _ (hs p) (eq.symm ▸ hs q))
        exact (Finset.mem_filter.mp p.property).2.1.trans (Finset.mem_filter.mp q.property).2.1.symm)
    simpa using h
  have singles : (P \ D).card ≤ T.card := Finset.card_le_card_of_injOn k
    (fun p hp => inside p (Finset.mem_sdiff.mp hp).1) (by
      rintro ⟨i,b⟩ hp ⟨j,c⟩ hq e
      have ij : i=j := exclusive _ _ (inside _ (Finset.mem_sdiff.mp hp).1) e
      subst j
      obtain ⟨ip,np⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨iq,nq⟩ := Finset.mem_sdiff.mp hq
      cases b <;> cases c
      · rfl
      · exact (nq (Finset.mem_filter.mpr ⟨iq,rfl,e⟩)).elim
      · exact (np (Finset.mem_filter.mpr ⟨ip,rfl,e.symm⟩)).elim
      · rfl)
  let pool := B ×ˢ (Finset.univ : Finset (Bool × Bool))
  have outside := Finset.card_le_card_of_injOn (s := X \ P) (t := pool)
    (fun p => (k p,(port p,p.2))) (by
      intro p hp
      obtain ⟨hx,no⟩ := Finset.mem_sdiff.mp hp
      exact Finset.mem_product.mpr ⟨whereK p (fun h => no (Finset.mem_filter.mpr ⟨hx,h⟩)), Finset.mem_univ _⟩)
    (by
      intro p _ q _ h
      obtain ⟨hk,hi⟩ := Prod.mk.inj h
      obtain ⟨hb,hc⟩ := Prod.mk.inj hi
      exact Prod.ext (portUnique p q hk hb) hc)
  have pd := Finset.card_sdiff_add_card_eq_card (show D ⊆ P from Finset.filter_subset ..)
  have xp := Finset.card_sdiff_add_card_eq_card (show P ⊆ X from Finset.filter_subset ..)
  simp only [pool,Finset.card_product,Finset.card_univ,Fintype.card_prod,Fintype.card_bool] at outside
  have nx : X.card=Fintype.card J * 2 := by simp [X]
  rw [nx] at xp
  exact ⟨dw,by omega⟩

set_option linter.constructorNameAsVariable false in
/-- Full-circuit first-probe budget, including repeated hits to one partner. -/
theorem probe_accounting {gs : List Gate} {o : ℕ}
    (least : MLeast (N+N) (edgeFun inc lines) gs (wire o)) (r t f : Crossing → ℕ)
    (fi : Function.Injective f)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (use : ∀ i, Reads gs (f i) (wire (r i))) (c : Crossing × Bool → ℕ)
    (hc : ∀ i v, let l := line v (coord v i)
      let x := singleton (Fin.natAdd N l)
      let y := pairInput (cross i) l
      Reads gs (c (i,v)) (wire (r i)) ∧ vl gs x (wire (c (i,v))) ≠ vl gs y (wire (c (i,v))) ∧
      ∀ w, Reads gs (c (i,v)) w → w ≠ wire (r i) → vl gs x w = vl gs y w) :
    let T := Finset.univ.image t
    let budget := gs.length-(1001^2+T.card)
    (duplicateHits T (fun p => wire (c p))).card ≤ budget ∧ 2*1001^2 ≤ T.card+5*budget := by
  classical
  let G := (Finset.range gs.length).image wire
  let R := Finset.univ.image (fun i => wire (r i))
  let T := Finset.univ.image t
  let B := G \ (R ∪ T)
  have partition := (explicit_partition least r t f fi rd sole use).1
  change 1001^2+T.card+B.card=gs.length at partition
  change (duplicateHits T (fun p => wire (c p))).card ≤ gs.length-(1001^2+T.card) ∧
    2*1001^2 ≤ T.card+5*(gs.length-(1001^2+T.card))
  have tin (w : ℕ) : w ∈ T ↔ ∃ i, t i=w := by simp only [T,Finset.mem_image,Finset.mem_univ,true_and]
  have bin (w : ℕ) : w ∈ G → (∀ i, w ≠ wire (r i)) → w ∉ T → w ∈ B := by
    intro wg nr nt
    change w ∈ G \ (R ∪ T)
    rw [Finset.mem_sdiff,Finset.mem_union]
    refine ⟨wg,fun h => h.elim (fun hr => ?_) nt⟩
    simp only [R,Finset.mem_image,Finset.mem_univ,true_and] at hr
    obtain ⟨i,e⟩ := hr
    exact nr i e.symm
  have gateMem (k : ℕ) (len : k < gs.length) : wire k ∈ G :=
    Finset.mem_image_of_mem wire (Finset.mem_range.mpr len)
  clear_value B T R G
  let k (p : Crossing × Bool) := wire (c p)
  have read (p : Crossing × Bool) : Reads gs (c p) (wire (r p.1)) := (hc p.1 p.2).1
  have classif (p : Crossing × Bool) := consumer_class inc lines cross r t least.clean least.2.2.1 rd sole sep p.1 (c p) (read p)
  have ri := incidence_reader_inj inc lines cross r t _ least.clean least.2.2.1 rd sole sep
  have ports (p : Crossing × Bool) := port_of_reads least.clean (read p)
  choose port hport using ports
  let iden (w : ℕ) (i : Crossing) := ∀ v a, sig gs w v a ↔ a=coord v i
  have idUnique w i j (hi : iden w i) (hj : iden w j) : i=j := by
    have eq (v) := (hj v _).mp ((hi v _).mpr rfl)
    exact Prod.ext (eq false) (eq true)
  have out (p : Crossing × Bool) (no : k p ∉ T) : k p ∈ B := by
    exact bin _ (gateMem _ (reads_len (read p))) (fun j e => (classif p).1 j (Nat.add_left_cancel e)) no
  have ex (p q : Crossing × Bool) (hp : k p ∈ T) (eq : k p=k q) : p.1=q.1 := by
    obtain ⟨z,hz⟩ := (tin _).mp hp
    have e : c p=c q := Nat.add_left_cancel eq
    exact (charged_partner_exclusive least r t rd sole p.1 q.1 z p.2 (c p) hz.symm (read p)
      (e.symm ▸ read q) (hc p.1 p.2).2.1 (hc p.1 p.2).2.2).symm
  have pu (p q : Crossing × Bool) (eq : k p=k q) (e : port p=port q) : p.1=q.1 := by
    have ck : c p=c q := Nat.add_left_cancel eq
    have h := hport p
    rw [ck,e,hport q] at h
    exact ri (Nat.add_left_cancel (Option.some.inj h.symm))
  have dup (i) (ht : k (i,false) ∈ T) (eq : k (i,false)=k (i,true)) : ∃ w ∈ B, iden w i := by
    obtain ⟨z,hz⟩ := (tin _).mp ht
    have same : c (i,false)=c (i,true) := Nat.add_left_cancel eq
    obtain ⟨w,lo,upper,nr,nt,idw⟩ := duplicate_witness least r t rd sole i z (c (i,false))
      hz.symm (read (i,false)) (by
        intro v; cases v
        · exact (hc i false).2
        · rw [same]; exact (hc i true).2)
    have wg := gateMem (w-(N+N)) (by omega)
    have we : wire (w-(N+N))=w := by dsimp only [wire]; omega
    rw [we] at wg
    exact ⟨w,bin w wg nr (fun h => by obtain ⟨j,e⟩ := (tin w).mp h; exact nt j e.symm),idw⟩
  have bound := slots T B k port iden idUnique out ex pu dup
  have card : Fintype.card Crossing = 1001^2 := by simp [Crossing,Axis,pow_two]
  rw [card] at bound
  have nb : gs.length-(1001^2+T.card) = B.card := by omega
  rw [nb]
  exact bound

/-- The resulting budget with the first changed consumers chosen by the circuit. -/
theorem probe_budget_five {gs : List Gate} {o : ℕ} (ho : o < gs.length)
    (least : MLeast (N+N) (edgeFun inc lines) gs (wire o)) (r t f : Crossing → ℕ)
    (fi : Function.Injective f)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (use : ∀ i, Reads gs (f i) (wire (r i))) :
    2*1001^2 ≤ (Finset.univ.image t).card+5*(gs.length-(1001^2+(Finset.univ.image t).card)) := by
  obtain ⟨c,hc⟩ := first_probes ho least r t rd sole
  exact (probe_accounting least r t f fi rd sole use c hc).2

/-- Every horizontal deletion saves at least eleven gates in the minimum
monotone circuit size of the order-1009 active grid. -/
theorem row_deletion_eleven (a : Axis) {s : ℕ}
    (full : HasMonoSize (N+N) (edgeFun inc lines) s) :
    ∃ e, HasMonoSize (N+N) (edgeFun inc (lines.erase (line false a))) e ∧ e+11 ≤ s := by
  classical
  have hex : ∃ e, HasMonoSize (N+N) (edgeFun inc (lines.erase (line false a))) e :=
    ⟨_,erased_upper a⟩
  have nc := PrivateGridPin.active_nc inc lines (line_mem false a)
    (show inc (cross (a,a)) (line false a) by simp [cross,onLine])
  obtain ⟨gs,out,least,len⟩ := Clean.ToolLeast_proof _ _ _ nc full
  have lim := Removal.out_lt least.2.2.1 nc
  have lower : N+N ≤ out := by
    by_contra! raw
    let u : Fin (N+N) := ⟨out,raw⟩
    have ev := least.2.2.1 (singleton u)
    rw [vl_input _ _ _ raw] at ev
    have yes := (show singleton u ⟨out,raw⟩ = true from decide_eq_true rfl)
    obtain ⟨q,l,_,_,hq,hl⟩ := (edgeFun_true ..).mp (ev.symm.trans yes)
    exact left_ne_right q l ((of_decide_eq_true hq).trans (of_decide_eq_true hl).symm)
  let o := out-(N+N)
  have eq : out = wire o := by dsimp [o,wire]; omega
  rw [eq] at least
  have ho : o < gs.length := by dsimp [o]; omega
  have drop := eleven_of_probe_bound a ho least (fun _ h => Nat.find_min' hex h) (by
    intro r t f fi h
    have five := probe_budget_five ho least r t f fi (fun i => (h i).1)
      (fun i => (h i).2.1) (fun i => (h i).2.2)
    omega)
  exact ⟨Nat.find hex,Nat.find_spec hex,le_trans drop len⟩

private def transpose : Point → Point
  | .inl (a,b) => .inl (b,a)
  | .inr (.inl (v,a,k)) => .inr (.inl (!v,a,k))
  | .inr (.inr v) => .inr (.inr (!v))

private noncomputable def flipIdx (p : Fin N) := idx (transpose (idx.symm p))

private theorem flip_line (v : Bool) (a : Axis) : flipIdx (line v a) = line (!v) a := by
  simp [flipIdx,line,priv,transpose]

private theorem flip_invol (p : Fin N) : flipIdx (flipIdx p) = p := by
  obtain ⟨q,rfl⟩ := idx.surjective p
  rcases q with ⟨a,b⟩|⟨⟨v,a,k⟩|v⟩ <;> simp [flipIdx,transpose]

private theorem line_form {l : Fin N} (hl : l ∈ lines) : ∃ v a, l=line v a := by
  rcases Finset.mem_union.mp hl with h|h <;> obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h
  · exact ⟨false,a,rfl⟩
  · exact ⟨true,a,rfl⟩

private theorem flip_inc {p l : Fin N} (hl : l ∈ lines) : inc (flipIdx p) (flipIdx l) ↔ inc p l := by
  obtain ⟨v,a,rfl⟩ := line_form hl
  obtain ⟨q,rfl⟩ := idx.surjective p
  rw [flip_line]
  rcases q with ⟨r,c⟩|⟨⟨d,b,k⟩|d⟩ <;> cases v <;> simp [flipIdx,transpose,onLine]

private theorem flip_active {v : Bool} {a : Axis} {l : Fin N} (hl : l ∈ lines.erase (line v a)) :
    flipIdx l ∈ lines.erase (line (!v) a) := by
  obtain ⟨d,b,rfl⟩ := line_form (Finset.mem_of_mem_erase hl)
  refine Finset.mem_erase.mpr ⟨fun eq => Finset.ne_of_mem_erase hl ?_,by rw [flip_line]; exact line_mem ..⟩
  have e := congrArg flipIdx eq
  simpa only [flip_invol,flip_line,Bool.not_not] using e

private theorem erased_transpose (a : Axis) {e : ℕ}
    (row : HasMonoSize (N+N) (edgeFun inc (lines.erase (line false a))) e) :
    HasMonoSize (N+N) (edgeFun inc (lines.erase (line true a))) e := by
  let π : Fin (N+N) → Fin (N+N) := Fin.addCases (fun p => Fin.castAdd N (flipIdx p))
    (fun l => Fin.natAdd N (flipIdx l))
  have h := Clean.relabel_mono π _ e row
  convert h using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun_true,edgeFun_true]
  have pt (p) : (x ∘ π) (Fin.castAdd N p) = x (Fin.castAdd N (flipIdx p)) := by simp [π]
  have sel (l) : (x ∘ π) (Fin.natAdd N l) = x (Fin.natAdd N (flipIdx l)) := by
    simp only [π,Function.comp_apply,Fin.addCases_right]
  constructor
  · rintro ⟨p,l,hl,i,hp,hs⟩
    exact ⟨flipIdx p,flipIdx l,flip_active (v := true) (a := a) (l := l) hl,(flip_inc (p := p) (l := l) (Finset.mem_of_mem_erase hl)).mpr i,by
      simpa only [pt,flip_invol] using hp,by simpa only [sel,flip_invol] using hs⟩
  · rintro ⟨p,l,hl,i,hp,hs⟩
    exact ⟨flipIdx p,flipIdx l,flip_active (v := false) (a := a) (l := l) hl,(flip_inc (p := p) (l := l) (Finset.mem_of_mem_erase hl)).mpr i,
      (pt p).symm.trans hp,(sel l).symm.trans hs⟩

/-- Deleting any selected line from either pencil saves at least eleven gates.
Both infinity inputs are free in the supplied and constructed functions. -/
theorem deletion_eleven (v : Bool) (a : Axis) {s : ℕ}
    (full : HasMonoSize (N+N) (edgeFun inc lines) s) :
    ∃ e, HasMonoSize (N+N) (edgeFun inc (lines.erase (line v a))) e ∧ e+11 ≤ s := by
  obtain ⟨e,h,drop⟩ := row_deletion_eleven a full
  cases v
  · exact ⟨e,h,drop⟩
  · exact ⟨e,erased_transpose a h,drop⟩

private theorem full_exists : ∃ s, HasMonoSize (N+N) (edgeFun inc lines) s := by
  classical
  let l := line false 0
  let S := lines.erase l
  have other : line true 0 ∈ S := Finset.mem_erase.mpr ⟨by simp [l,line_eq],line_mem ..⟩
  have inc' : inc (hub true) (line true 0) := by simp [hub,onLine]
  have starPos : (star false 0).Nonempty :=
    ⟨hub false,(star_iff ..).mpr (by simp [hub,onLine])⟩
  have h := PrivateGridRestore.append_lines (edgeFun inc S) {l} (fun _ => star false 0)
    (fun _ _ => starPos) (edgeFun_zero ..) ⟨_,PrivateGridPin.pair_on inc S other inc'⟩ (erased_upper 0)
  have eq : PrivateGridRestore.addLines (edgeFun inc S) {l} (fun _ => star false 0) = edgeFun inc lines := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [PrivateGridRestore.addLines,Bool.or_eq_true_iff,decide_eq_true_eq,edgeFun_true,
      Finset.mem_singleton,exists_eq_left]
    constructor
    · rintro (⟨p,k,hk,hi,hp,hs⟩|⟨hs,p,hp,hx⟩)
      · exact ⟨p,k,(Finset.mem_erase.mp hk).2,hi,hp,hs⟩
      · exact ⟨p,l,line_mem ..,(star_iff ..).mp hp,hx,hs⟩
    · rintro ⟨p,k,hk,hi,hp,hs⟩
      by_cases e : k=l
      · subst k; exact Or.inr ⟨hs,p,(star_iff ..).mpr hi,hp⟩
      · exact Or.inl ⟨p,k,Finset.mem_erase.mpr ⟨e,hk⟩,hi,hp,hs⟩
  rw [eq] at h
  exact ⟨_,h⟩

/-- Both optima exist and the erased optimum plus eleven is at most the
original optimum, for every one of the 2,002 line choices. -/
theorem minimum_deletion_eleven (v : Bool) (a : Axis) :
    ∃ d e : ℕ, IsLeast {s | HasMonoSize (N+N) (edgeFun inc lines) s} d ∧
      IsLeast {s | HasMonoSize (N+N) (edgeFun inc (lines.erase (line v a))) s} e ∧ e+11 ≤ d := by
  classical
  let d := Nat.find full_exists
  have hd := Nat.find_spec full_exists
  obtain ⟨s,hs,drop⟩ := deletion_eleven v a hd
  have ex : ∃ e, HasMonoSize (N+N) (edgeFun inc (lines.erase (line v a))) e := ⟨s,hs⟩
  exact ⟨d,Nat.find ex,⟨hd,fun _ h => Nat.find_min' full_exists h⟩,
    ⟨Nat.find_spec ex,fun _ h => Nat.find_min' ex h⟩,by
      have := Nat.find_min' ex hs
      dsimp only [d]
      omega⟩

end Onlyfr.PrivateGrid1009
