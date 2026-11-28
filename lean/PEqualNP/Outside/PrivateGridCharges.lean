import PEqualNP.Outside.PrivateGridCuts

namespace Onlyfr.PrivateGrid1009
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGridRewire Onlyfr.PrivateGridMatching
set_option maxRecDepth 4096

private theorem misses (i : Crossing) (q : Fin N) (ne : q ≠ cross i) :
    ∃ l ∈ lines, inc (cross i) l ∧ ¬ inc q l := by
  obtain ⟨p,rfl⟩ := idx.surjective q
  rcases p with j|⟨⟨v,a,k⟩|v⟩
  · exact sep i j (fun e => ne (e ▸ rfl))
  · refine ⟨line (!v) (coord (!v) i),line_mem ..,?_,?_⟩
    · rcases i with ⟨r,c⟩; cases v <;> simp [cross,coord,onLine]
    · cases v <;> simp [onLine]
  · refine ⟨line (!v) (coord (!v) i),line_mem ..,?_,?_⟩
    · rcases i with ⟨r,c⟩; cases v <;> simp [cross,coord,onLine]
    · cases v <;> simp [onLine]

def singleton {m : ℕ} (a z : Fin m) : Bool := decide (z=a)

private theorem singleton_negative (u : Fin (N+N)) : edgeFun inc lines (singleton u) ≠ true := by
  intro h
  obtain ⟨p,l,_,_,hp,hl⟩ := (edgeFun_true ..).mp h
  exact left_ne_right p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)

theorem partner_off_singleton {gs : List Gate} {o r t : ℕ} (i : Crossing)
    (least : MLeast (N+N) (edgeFun inc lines) gs o) (rd : OrRd gs r (Fin.castAdd N (cross i)) t)
    (sole : ∀ k, Reads gs k (Fin.castAdd N (cross i)) → k=r) (u : Fin (N+N)) :
    vl gs (singleton u) t ≠ true := by
  let a := Fin.castAdd N (cross i)
  have hc := least.clean
  obtain ⟨g,hg,hop,ins⟩ := rd
  have reader : OrRd gs r a t := ⟨g,hg,hop,ins⟩
  have tr : Reads gs r t := ⟨g,hg,by rcases ins with e|e <;> simp [e]⟩
  have early := reads_lt hc.1 tr
  have ta : t ≠ a.val := by
    intro eq
    have nc := PrivateGridPin.active_nc inc lines (line_mem false i.1)
      (show inc (cross i) (line false i.1) by rcases i with ⟨b,c⟩; simp [cross,onLine])
    obtain ⟨cs,v,clean,len,ev⟩ := Free.elimAl Removal.ToolRemoval_proof least nc Set.univ {r} (fun _ => t) (by
      intro k hk
      have kr : k=r := Finset.mem_singleton.mp hk
      subst k
      exact ⟨reads_len tr,early,fun x _ => by rw [orrd_eval hc.1 reader,eq,Bool.or_self]⟩)
    have le := least.2.2.2 cs v clean.1 clean.2 (fun x => ev x (Set.mem_univ x))
    simp only [Finset.card_singleton] at len
    omega
  have negative (l : Fin N) (hl : l ∈ lines) (on : inc (cross i) l)
      (dark : ∀ q, inc q l → singleton u (Fin.castAdd N q) = false) : vl gs (singleton u) t ≠ true :=
    fun h => singleton_negative u ((least.2.2.1 _).symm.trans
      (dark_partner_sound inc lines _ l hl on hc least.2.2.1 reader sole _ dark h))
  by_cases own : u=a
  · subst u
    let z : Fin (N+N) → Bool := fun _ => false
    have eq : vl gs (singleton a) t = vl gs z t := by
      apply agree_B gs hc.1 _ _ (fun w => w=a.val) (t+1) _ _ t (by omega) ta
      · intro j hj ne
        rw [vl_input _ _ _ hj,vl_input _ _ _ hj]
        exact decide_eq_false (fun e => ne (congrArg Fin.val e))
      · intro k gate hgate less _ h _
        obtain ⟨w,hw,rfl⟩ := h
        have e := sole k ⟨gate,hgate,hw⟩
        omega
    rw [eq]
    intro h
    have on : inc (cross i) (line false i.1) := by rcases i with ⟨b,c⟩; simp [cross,onLine]
    have yes := dark_partner_sound inc lines _ _ (line_mem ..) on hc least.2.2.1 reader sole z (fun _ _ => rfl) h
    rw [least.2.2.1,edgeFun_zero] at yes
    contradiction
  · revert own
    induction u using Fin.addCases with
    | left q =>
      intro neq
      obtain ⟨l,hl,on,miss⟩ := misses i q (fun e => neq (congrArg (Fin.castAdd N) e))
      apply negative l hl on
      intro p hp
      exact decide_eq_false (fun e => miss (Fin.castAdd_injective N N e ▸ hp))
    | right l =>
      intro _
      apply negative (line false i.1) (line_mem ..)
      · rcases i with ⟨b,c⟩; simp [cross,onLine]
      · intro p _
        exact decide_eq_false (left_ne_right p l)

private theorem partition_core {J : Type*} (X : Finset J) (G : Finset ℕ) (r t f : J → ℕ)
    (ri : Function.Injective r) (fi : Function.Injective f)
    (rs : ∀ i ∈ X, r i ∈ G) (ts : ∀ i ∈ X, t i ∈ G) (fs : ∀ i ∈ X, f i ∈ G)
    (rt : ∀ i j, r i ≠ t j) (fr : ∀ i j, f i ≠ r j) :
    let R := X.image r
    let T := X.image t
    let B := G \ (R ∪ T)
    X.card+T.card+B.card=G.card ∧ X.card ≤ (X.filter (fun i => f i ∈ T)).card+B.card := by
  classical
  intro R T B
  have cover : R ∪ T ⊆ G := by
    intro k hk
    rcases Finset.mem_union.mp hk with hr|ht
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr; exact rs i hi
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht; exact ts i hi
  have dis : Disjoint R T := by
    apply Finset.disjoint_left.mpr
    intro k hr ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp ht
    exact rt i j e.symm
  have nb := Finset.card_sdiff_add_card_eq_card cover
  rw [Finset.card_union_of_disjoint dis,show R.card=X.card from Finset.card_image_of_injective _ ri] at nb
  let U := X.filter (fun i => f i ∈ T)
  have sub : (X \ U).image f ⊆ B := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hi,hout⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_sdiff.mpr ⟨fs i hi,?_⟩
    intro h
    rcases Finset.mem_union.mp h with hr|ht
    · obtain ⟨j,_,e⟩ := Finset.mem_image.mp hr
      exact fr i j e.symm
    · exact hout (Finset.mem_filter.mpr ⟨hi,ht⟩)
  have cb := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ fi] at cb
  have partition := Finset.card_sdiff_add_card_eq_card (show U ⊆ X from Finset.filter_subset ..)
  change B.card+(X.card+T.card)=G.card at nb
  change _ ∧ X.card ≤ U.card+B.card
  omega

theorem explicit_partition {gs : List Gate} {o : ℕ} (least : MLeast (N+N) (edgeFun inc lines) gs o)
    (r t f : Crossing → ℕ) (fi : Function.Injective f)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (use : ∀ i, Reads gs (f i) (N+N+r i)) :
    let B := ((Finset.range gs.length).image (fun k => N+N+k)) \ ((Finset.univ.image (fun i => N+N+r i)) ∪ Finset.univ.image t)
    1001^2+(Finset.univ.image t).card+B.card = gs.length ∧
      1001^2 ≤ (Finset.univ.filter (fun i => N+N+f i ∈ Finset.univ.image t)).card+B.card := by
  classical
  let X : Finset Crossing := Finset.univ
  have nx : X.card=1001^2 := by simp [X,Crossing,Axis,pow_two]
  let wire (k : ℕ) := N+N+k
  have wi : Function.Injective wire := fun _ _ e => Nat.add_left_cancel e
  let G := (Finset.range gs.length).image wire
  let R := X.image (fun i => wire (r i))
  let T := X.image t
  let B := G \ (R ∪ T)
  have ri := incidence_reader_inj inc lines cross r t o least.clean least.2.2.1 rd sole sep
  have tr (i) : Reads gs (r i) (t i) := by
    obtain ⟨g,hg,_,a|a⟩ := rd i <;> exact ⟨g,hg,by simp [a]⟩
  have no := fun i => partner_off_singleton i least (rd i) (sole i)
  have ins (i) : t i ∈ G := by
    have h := reads_lt least.1 (tr i)
    have len := reads_len (tr i)
    have lower : N+N ≤ t i := by
      by_contra! small
      let a := (⟨t i,small⟩ : Fin (N+N))
      apply no i a
      rw [vl_input _ _ _ small]
      exact decide_eq_true rfl
    exact Finset.mem_image.mpr ⟨t i-(N+N),Finset.mem_range.mpr (by omega),by dsimp [wire]; omega⟩
  have rt (i j) : wire (r i) ≠ t j := by
    intro e
    let a := Fin.castAdd N (cross i)
    apply no j a
    rw [←e,show wire (r i) = N+N+r i from rfl,orrd_eval least.1 (rd i)]
    exact Bool.or_eq_true_iff.mpr (Or.inl ((vl_input _ _ _ a.isLt).trans (decide_eq_true rfl)))
  have counts := partition_core X G (fun i => wire (r i)) t (fun i => wire (f i)) (wi.comp ri)
    (wi.comp fi) (fun i _ => Finset.mem_image_of_mem wire (Finset.mem_range.mpr (reads_len (tr i))))
    (fun i _ => ins i) (fun i _ => Finset.mem_image_of_mem wire (Finset.mem_range.mpr (reads_len (use i))))
    rt (fun i j e => (consumer_class inc lines cross r t least.clean least.2.2.1 rd sole sep i (f i) (use i)).1 j (wi e))
  have ng : G.card = gs.length := (Finset.card_image_of_injective _ wi).trans (Finset.card_range _)
  change X.card+T.card+B.card=G.card ∧ X.card ≤ (X.filter (fun i => wire (f i) ∈ T)).card+B.card at counts
  rw [nx,ng] at counts
  exact counts

theorem gate_partition {gs : List Gate} {o : ℕ} (least : MLeast (N+N) (edgeFun inc lines) gs o)
    (r t f : Crossing → ℕ) (fi : Function.Injective f)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (use : ∀ i, Reads gs (f i) (N+N+r i)) :
    ∃ B, 1001^2+(Finset.univ.image t).card+B = gs.length ∧
      1001^2 ≤ (Finset.univ.filter (fun i => N+N+f i ∈ Finset.univ.image t)).card+B := by
  exact ⟨_,explicit_partition least r t f fi rd sole use⟩

/-- Each of the two endpoint tests is charged to a genuine first changed
consumer. Its other operand keeps its old selector-singleton value. -/
theorem first_probes {gs : List Gate} {o : ℕ} (ho : o < gs.length)
    (least : MLeast (N+N) (edgeFun inc lines) gs (N+N+o)) (r t : Crossing → ℕ)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i) :
    ∃ assign : Crossing × Bool → ℕ, ∀ i v,
      let l := line v (coord v i)
      let x := singleton (Fin.natAdd N l)
      let y := pairInput (cross i) l
      let k := assign (i,v)
      Reads gs k (N+N+r i) ∧ vl gs x (N+N+k) ≠ vl gs y (N+N+k) ∧
        ∀ w, Reads gs k w → w ≠ N+N+r i → vl gs x w = vl gs y w := by
  classical
  have charge (i : Crossing) (v : Bool) :
      let l := line v (coord v i)
      let x := singleton (Fin.natAdd N l)
      let y := pairInput (cross i) l
      ∃ k, Reads gs k (N+N+r i) ∧ vl gs x (N+N+k) ≠ vl gs y (N+N+k) ∧
        ∀ w, Reads gs k w → w ≠ N+N+r i → vl gs x w = vl gs y w := by
    intro l x y
    refine PrivateGridProbe.first_changed_consumer least.clean x y (Fin.castAdd N (cross i)) (r i) ?_ (sole i) ?_
    · intro a ha
      simp only [x,y,singleton,pairInput,ha,false_or]
    · have diff : o ≠ r i := by
        intro eq
        let a := Fin.castAdd N (cross i)
        apply singleton_negative a
        rw [←least.2.2.1,eq,orrd_eval least.1 (rd i)]
        exact Bool.or_eq_true_iff.mpr (Or.inl ((vl_input _ _ _ a.isLt).trans (decide_eq_true rfl)))
      have yes : edgeFun inc lines y = true := Onlyfr.PrivateGridPin.pair_on inc lines (line_mem ..) (by
        rcases i with ⟨a,b⟩; cases v <;> simp [l,cross,coord,onLine])
      exact ⟨o,ho,diff,fun e => singleton_negative _ ((least.2.2.1 x).symm.trans
        (e.trans ((least.2.2.1 y).trans yes)))⟩
  choose c hc using charge
  exact ⟨fun z => c z.1 z.2,hc⟩

/-- A partner charged by an endpoint probe cannot take a different reader
as its second input. This remains true when readers have multiple consumers. -/
theorem charged_partner_exclusive {gs : List Gate} {o : ℕ}
    (least : MLeast (N+N) (edgeFun inc lines) gs o) (r t : Crossing → ℕ)
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd N (cross i)) → k=r i)
    (i j z : Crossing) (v : Bool) (k : ℕ) (part : N+N+k=t z)
    (hi : Reads gs k (N+N+r i)) (hj : Reads gs k (N+N+r j))
    (change : let l := line v (coord v i)
      vl gs (singleton (Fin.natAdd N l)) (N+N+k) ≠ vl gs (pairInput (cross i) l) (N+N+k))
    (agree : let l := line v (coord v i)
      ∀ w, Reads gs k w → w ≠ N+N+r i →
        vl gs (singleton (Fin.natAdd N l)) w = vl gs (pairInput (cross i) l) w) : j=i := by
  by_contra ne
  let l := line v (coord v i)
  let x := singleton (Fin.natAdd N l)
  let y := pairInput (cross i) l
  have ri := incidence_reader_inj inc lines cross r t o least.clean least.2.2.1 rd sole sep
  have different : N+N+r j ≠ N+N+r i := fun e => ne (ri (Nat.add_left_cancel e))
  have off : vl gs x (N+N+r j) = false := by
    rw [orrd_eval least.1 (rd j),vl_input _ _ _ (Fin.castAdd N (cross j)).isLt]
    change (singleton (Fin.natAdd N l) (Fin.castAdd N (cross j)) || vl gs x (t j)) = false
    have raw : singleton (Fin.natAdd N l) (Fin.castAdd N (cross j)) = false :=
      decide_eq_false (left_ne_right (cross j) l)
    rw [raw,Bool.eq_false_iff.mpr (partner_off_singleton j least (rd j) (sole j) _)]
    rfl
  obtain ⟨g,hg,hand⟩ := (consumer_class inc lines cross r t least.clean least.2.2.1 rd sole sep i k hi).2 z part
  obtain ⟨g',hg',mem⟩ := hj
  cases Option.some.inj (hg.symm.trans hg')
  have off' : vl gs y (N+N+r j) = false := (agree _ ⟨g,hg,mem⟩ different).symm.trans off
  have blocked (u : Fin (N+N) → Bool) (h : vl gs u (N+N+r j) = false) : vl gs u (N+N+k) = false := by
    have eq := vl_abs gs least.1 u k g hg (Or.inl hand) _ mem
    simpa only [fixBit,hand] using eq (by simpa [fixBit,hand] using h)
  exact change ((blocked x off).trans (blocked y off').symm)

/-- Sole remaining quantitative hypothesis: the first-probe charge bound in
each tight minimum circuit. B is fixed by the circuit length and partner count. -/
theorem eleven_of_probe_bound {gs : List Gate} {o e : ℕ} (a : Axis) (ho : o < gs.length)
    (least : MLeast (N+N) (edgeFun inc lines) gs (N+N+o))
    (emin : ∀ s, HasMonoSize (N+N) (edgeFun inc (lines.erase (line false a))) s → e ≤ s)
    (probeBound : ∀ r t f : Crossing → ℕ, Function.Injective f →
      (∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i) ∧
        (∀ k, Reads gs k (Fin.castAdd N (cross i)) → k=r i) ∧ Reads gs (f i) (N+N+r i)) →
      2*1001^2 ≤ (Finset.univ.image t).card + 8*(gs.length-(1001^2+(Finset.univ.image t).card))) :
    e+11 ≤ gs.length := by
  by_contra! bad
  have ten : gs.length ≤ e+10 := by omega
  obtain ⟨r,t,f,fi,readers⟩ := matched_one_row a ho least ten emin
  have rd i := (readers i).1
  have sole i := (readers i).2.1
  have use i := (readers i).2.2
  obtain ⟨B,partition,matched⟩ := gate_partition least r t f fi rd sole use
  have total := emin _ (erased_upper a)
  have probes := probeBound r t f fi readers
  have eq : gs.length-(1001^2+(Finset.univ.image t).card)=B := by omega
  rw [eq] at probes
  exact incompatible_counts least (by omega) r t f fi rd sole use B (by omega) matched probes

end Onlyfr.PrivateGrid1009