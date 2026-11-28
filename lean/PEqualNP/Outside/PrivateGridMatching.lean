import PEqualNP.Outside.PrivateGridProbe
import PEqualNP.Outside.PrivateGridRewire

namespace Onlyfr.PrivateGridMatching
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc

/-- The actual operand on the indicated input port of a gate. -/
def operand (gs : List Gate) (k : ℕ) (b : Bool) : Option ℕ :=
  gs[k]?.bind fun g => g.inputs[if b then 1 else 0]?

private theorem port_of_reads {m k w : ℕ} {gs : List Gate} (hc : MClean m gs)
    (h : Reads gs k w) : ∃ b, operand gs k b = some w := by
  obtain ⟨g,hg,hw⟩ := h
  rcases hc.1 k g hg with ⟨_,a,_,ha⟩ | ⟨_,a,b,_,_,hab⟩
  · have e : w = a := by simpa [ha] using hw
    exact ⟨false,by simp [operand,hg,ha,e]⟩
  · have e : w = a ∨ w = b := by simpa [hab] using hw
    rcases e with rfl|rfl
    · exact ⟨false,by simp [operand,hg,hab]⟩
    · exact ⟨true,by simp [operand,hg,hab]⟩

/-- A reader either has two distinct consumers or has a consumer exclusive
to it among the designated reader outputs. No port assignment is assumed. -/
theorem match_readers {I : Type*} [Finite I] {m : ℕ} {gs : List Gate}
    (hc : MClean m gs) (r : I → ℕ) (inj : Function.Injective r)
    (degree : ∀ i, (∃ k, Reads gs k (m+r i) ∧ ∀ j, Reads gs k (m+r j) → j=i) ∨
      ∃ k l, k ≠ l ∧ Reads gs k (m+r i) ∧ Reads gs l (m+r i)) :
    ∃ f : I → ℕ, Function.Injective f ∧ ∀ i, Reads gs (f i) (m+r i) := by
  classical
  let exclusive (i : I) (k : ℕ) := ∀ j, Reads gs k (m+r j) → j=i
  let valid (i : I) (p : ℕ × Bool) := Reads gs p.1 (m+r i) ∧
    (exclusive i p.1 ∨ operand gs p.1 p.2 = some (m+r i))
  have unique {i j : I} {p} (hi : valid i p) (hj : valid j p) : i=j := by
    rcases hi.2 with a|a
    · exact (a j hj.1).symm
    rcases hj.2 with b|b
    · exact b i hi.1
    exact inj (Nat.add_left_cancel (Option.some.inj (a.symm.trans b)))
  have two (i : I) : ∃ a b, a ≠ b ∧ valid i a ∧ valid i b := by
    rcases degree i with ⟨k,hk,he⟩|⟨k,l,ne,hk,hl⟩
    · exact ⟨(k,false),(k,true),by simp,⟨hk,Or.inl he⟩,⟨hk,Or.inl he⟩⟩
    · obtain ⟨a,ha⟩ := port_of_reads hc hk
      obtain ⟨b,hb⟩ := port_of_reads hc hl
      exact ⟨(k,a),(l,b),fun h => ne (congrArg Prod.fst h),⟨hk,Or.inr ha⟩,⟨hl,Or.inr hb⟩⟩
  choose a b ne va vb using two
  let slot (x : I × Bool) := if x.2 then b x.1 else a x.1
  have hv (x : I × Bool) : valid x.1 (slot x) := by
    obtain ⟨i,t⟩ := x
    cases t with | false => exact va i | true => exact vb i
  have si : Function.Injective slot := by
    rintro ⟨i,t⟩ ⟨j,u⟩ h
    have hj : valid j (slot (i,t)) := by rw [h]; exact hv (j,u)
    have e : i=j := unique (hv (i,t)) hj
    subst j
    cases t <;> cases u
    · rfl
    · exact (ne i h).elim
    · exact (ne i h.symm).elim
    · rfl
  let adj (i : I) := (Finset.range gs.length).filter (fun k => Reads gs k (m+r i))
  obtain ⟨f,hf,good⟩ := PrivateGridProbe.consumer_matching adj ⟨slot,si⟩ (by
    intro x
    have h := (hv x).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (reads_len h),h⟩)
  exact ⟨f,hf,fun i => (Finset.mem_filter.mp (good i)).2⟩

/-- A test changes a non-reader gate when flipping just one raw input. -/
def Probe {m : ℕ} (gs : List Gate) (u : Fin m) (r : ℕ) (x y : Fin m → Bool) :=
  (∀ a, a ≠ u → x a = y a) ∧
  ∃ k, k < gs.length ∧ k ≠ r ∧ vl gs x (m+k) ≠ vl gs y (m+k)

/-- A second reader cannot block both a gate's absorbing-value test and
the output change if this is the only consumer of the first reader. -/
theorem match_of_tests {I : Type*} [Finite I] {m : ℕ} {gs : List Gate}
    (hc : MClean m gs) (u : I → Fin m) (r : I → ℕ) (inj : Function.Injective r)
    (sole : ∀ i k, Reads gs k (u i) → k=r i)
    (live : ∀ i, ∃ x y, Probe gs (u i) (r i) x y)
    (tests : ∀ i j, i ≠ j → ∀ bit : Bool, ∃ x y,
      Probe gs (u i) (r i) x y ∧ vl gs x (m+r j) = bit) :
    ∃ f : I → ℕ, Function.Injective f ∧ ∀ i, Reads gs (f i) (m+r i) := by
  classical
  apply match_readers hc r inj
  intro i
  obtain ⟨x,y,same,change⟩ := live i
  obtain ⟨k,hk,_⟩ := PrivateGridProbe.first_changed_consumer hc x y (u i) (r i)
    same (sole i) change
  by_cases alt : ∃ l, k ≠ l ∧ Reads gs l (m+r i)
  · obtain ⟨l,hl,hr⟩ := alt
    exact Or.inr ⟨k,l,hl,hk,hr⟩
  refine Or.inl ⟨k,hk,?_⟩
  intro j hj
  by_contra ne
  obtain ⟨g,hg,mem⟩ := hj
  have ops : g.op = .and ∨ g.op = .or := by
    rcases hc.1 k g hg with ⟨h,_⟩|⟨h,_⟩
    · exact False.elim (hc.2 g (List.mem_of_getElem? hg) h)
    · exact h
  obtain ⟨a,b,⟨hab,out⟩,mask⟩ := tests i j (Ne.symm ne) (fixBit g)
  obtain ⟨l,hl,diff,agree⟩ := PrivateGridProbe.first_changed_consumer hc a b (u i) (r i)
    hab (sole i) out
  have eq : k=l := by by_contra n; exact alt ⟨l,n,hl⟩
  subst l
  have wd : m+r j ≠ m+r i := fun h => ne (inj (Nat.add_left_cancel h))
  have keep := agree _ ⟨g,hg,mem⟩ wd
  exact diff ((vl_abs gs hc.1 a k g hg ops _ mem mask).trans
    (vl_abs gs hc.1 b k g hg ops _ mem (keep.symm.trans mask)).symm)

/-- The matching is chosen before the cut. Its restriction gives exactly
one distinct foldable consumer per dark reader. -/
theorem cut_consumers {I : Type*} {m : ℕ} {gs : List Gate} (D : Finset I)
    (r f : I → ℕ) (inj : Function.Injective f) (uses : ∀ i, Reads gs (f i) (m+r i)) :
    (D.image f).card = D.card ∧ ∀ k ∈ D.image f, ∃ i ∈ D, Reads gs k (m+r i) := by
  refine ⟨Finset.card_image_of_injective _ inj,?_⟩
  intro k hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  exact ⟨i,hi,uses i⟩

open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGridRewire

/-- Turn on crossing i with only one of its selectors active. Reader j is
held high by its own raw point, or low by the dark-line partner lemma. -/
theorem incidence_test {J : Type*} {n : ℕ} {gs : List Gate}
    (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (p : J → Fin n) (r t : J → ℕ) (o : ℕ) (ho : o < gs.length)
    (hc : MClean (n+n) gs) (ev : Computes (n+n) gs (n+n+o) (edgeFun I S))
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd n (p i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd n (p i)) → k=r i)
    (i j : J) (l h : Fin n) (hl : l ∈ S) (hi : I (p i) l) (miss : ¬ I (p j) l)
    (hh : h ∈ S) (hj : I (p j) h) (bit : Bool) :
    ∃ x y, Probe gs (Fin.castAdd n (p i)) (r i) x y ∧ vl gs x (n+n+r j) = bit := by
  classical
  let raw := Fin.castAdd n (p i)
  let x (z : Fin (n+n)) := decide (z = Fin.natAdd n l ∨ (z = Fin.castAdd n (p j) ∧ bit = true))
  let y := Function.update x raw true
  have xp (q : Fin n) : x (Fin.castAdd n q) = true ↔ q = p j ∧ bit = true := by
    simp only [x,decide_eq_true_eq,left_ne_right,false_or,Fin.castAdd_inj]
  have xl (v : Fin n) : x (Fin.natAdd n v) = true ↔ v=l := by
    simp only [x,decide_eq_true_eq,(left_ne_right (p j) v).symm,false_and,or_false,
      (Fin.natAdd_injective n n).eq_iff]
  have neg : edgeFun I S x = false := by
    apply Bool.eq_false_iff.mpr
    intro e
    obtain ⟨q,v,_,inc,a,b⟩ := (edgeFun_true ..).mp e
    exact miss (by
      simpa [((xp q).mp a).1,(xl v).mp b] using inc)
  have pos : edgeFun I S y = true := (edgeFun_true ..).mpr
    ⟨p i,l,hl,hi,by simp [y,raw],by
      rw [show y (Fin.natAdd n l) = x (Fin.natAdd n l) from Function.update_of_ne
        (left_ne_right (p i) l).symm ..]
      exact (xl l).mpr rfl⟩
  have distinct : o ≠ r i := by
    intro eq
    let s (z : Fin (n+n)) := decide (z=raw)
    have accept : vl gs s (n+n+r i) = true := by
      rw [orrd_eval hc.1 (rd i),vl_input _ _ _ (Fin.castAdd n (p i)).isLt]
      change (s raw || _) = true
      exact Bool.or_eq_true_iff.mpr (Or.inl (by simp [s]))
    rw [← eq,ev] at accept
    obtain ⟨_,v,_,_,_,e⟩ := (edgeFun_true ..).mp accept
    exact (left_ne_right (p i) v).symm (of_decide_eq_true e)
  refine ⟨x,y,⟨fun a ne => (Function.update_of_ne ne ..).symm,
    o,ho,distinct,by rw [ev,ev,neg,pos]; decide⟩,?_⟩
  rw [orrd_eval hc.1 (rd j),vl_input _ _ _ (Fin.castAdd n (p j)).isLt]
  change (x (Fin.castAdd n (p j)) || _) = bit
  cases bit with
  | true => exact Bool.or_eq_true_iff.mpr (Or.inl ((xp _).mpr ⟨rfl,rfl⟩))
  | false =>
    have dark (q : Fin n) : x (Fin.castAdd n q) = false := by
      exact Bool.eq_false_iff.mpr (fun e => Bool.noConfusion ((xp q).mp e).2)
    have no : vl gs x (t j) ≠ true := by
      intro fire
      have e := dark_partner_sound I S (p j) h hh hj hc ev (rd j) (sole j) x
        (fun q _ => dark q) fire
      rw [ev,neg] at e
      contradiction
    rw [dark,Bool.eq_false_iff.mpr no]; rfl

/-- Distinguishable active points with unique OR readers admit a single
matching to direct consumers, simultaneously for all row and column cuts. -/
theorem incidence_matching {J : Type*} [Finite J] [Nontrivial J] {n : ℕ} {gs : List Gate}
    (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (p : J → Fin n) (r t : J → ℕ) (o : ℕ) (ho : o < gs.length)
    (hc : MClean (n+n) gs) (ev : Computes (n+n) gs (n+n+o) (edgeFun I S))
    (rd : ∀ i, OrRd gs (r i) (Fin.castAdd n (p i)) (t i))
    (sole : ∀ i k, Reads gs k (Fin.castAdd n (p i)) → k=r i)
    (sep : ∀ i j, i ≠ j → ∃ l ∈ S, I (p i) l ∧ ¬ I (p j) l) :
    ∃ f : J → ℕ, Function.Injective f ∧ ∀ i, Reads gs (f i) (n+n+r i) := by
  have test (i j : J) (ne : i ≠ j) (b : Bool) : ∃ x y, Probe gs (Fin.castAdd n (p i)) (r i) x y ∧ vl gs x (n+n+r j) = b := by
    obtain ⟨l,hl,hi,miss⟩ := sep i j ne
    obtain ⟨h,hh,hj,_⟩ := sep j i ne.symm
    exact incidence_test I S p r t o ho hc ev rd sole i j l h hl hi miss hh hj b
  apply match_of_tests hc (fun i => Fin.castAdd n (p i)) r _ sole _ test
  · intro i j eq
    by_contra ne

    obtain ⟨l,hl,hi,miss⟩ := sep i j ne
    have diff : p i ≠ p j := fun e => miss (e ▸ hi)
    -- If the readers coincide, exchanging the two raw bits at their
    -- common OR leaves the circuit unchanged.
    have ri : Reads gs (r i) (Fin.castAdd n (p i)) := by
      obtain ⟨g,hg,_,a|a⟩ := rd i <;> exact ⟨g,hg,by simp [a]⟩
    have rj : Reads gs (r i) (Fin.castAdd n (p j)) := by
      rw [eq]
      obtain ⟨g,hg,_,a|a⟩ := rd j <;> exact ⟨g,hg,by simp [a]⟩
    obtain ⟨g,hg,op,a⟩ := rd i
    have mem := rj.choose_spec
    have eg := Option.some.inj (mem.1.symm.trans hg)
    have hmem : (Fin.castAdd n (p j) : ℕ) ∈ g.inputs := eg ▸ mem.2
    have neq : (Fin.castAdd n (p j) : ℕ) ≠ (Fin.castAdd n (p i) : ℕ) :=
      fun e => diff (Fin.ext e.symm)
    have same : (Fin.castAdd n (p j) : ℕ) = t i := by
      rcases a with a|a <;> simp only [a,List.mem_cons,List.not_mem_nil,or_false] at hmem
      · exact hmem.resolve_left neq
      · exact hmem.resolve_right neq
    let z := pairInput (p j) l
    have dark (q) (hq : I q l) : z (Fin.castAdd n q) = false := by
      have nq : q ≠ p j := fun e => miss (e ▸ hq)
      simp [z,pair_point,nq]
    have fire : vl gs z (t i) = true := by
      rw [←same,vl_input _ _ _ (Fin.castAdd n (p j)).isLt]
      change pairInput (p j) l (Fin.castAdd n (p j)) = true
      rw [pair_point]; simp
    have pos := dark_partner_sound I S (p i) l hl hi hc ev (rd i) (sole i) z dark fire
    rw [ev] at pos
    obtain ⟨q,v,_,inc,hq,hv⟩ := (edgeFun_true ..).mp pos
    have qeq : q=p j := by simpa [z,pair_point] using hq
    have veq : v=l := by simpa only [z,pair_line,decide_eq_true_eq] using hv
    exact miss (qeq ▸ veq ▸ inc)
  · intro i
    obtain ⟨j,ne⟩ := exists_ne i
    obtain ⟨x,y,h,_⟩ := test i j ne.symm false
    exact ⟨x,y,h⟩

/-- For any cut, fold the preselected consumers of dark readers. Restoring
the cut at cost c in a minimum circuit bounds the net savings by c. -/
theorem matched_cut {m o : ℕ} {gs : List Gate} (hc : MClean m gs) (ho : o < m+gs.length)
    (P : Set (Fin m → Bool)) (D S E Z : Finset ℕ) (f src tag : ℕ → ℕ) (c : ℕ)
    (inj : Set.InjOn f D) (sub : D ⊆ S) (use : ∀ i ∈ D, Reads gs (f i) (m+i))
    (dis : Disjoint S (D.image f)) (disE : Disjoint (S ∪ D.image f) E)
    (rd : ∀ k ∈ S, OrRd gs k (src k) (tag k))
    (dark : ∀ i ∈ D, ∀ x ∈ P, vl gs x (src i) = false ∧ src i < m)
    (zero : ∀ z ∈ Z, ∃ k ∈ D.image f, z=m+k ∧ ∃ g, gs[k]? = some g ∧ g.op = .and)
    (extra : ∀ k ∈ E, ∃ a z, z ∈ Z ∧ OrRd gs k a z)
    (credit : (Z \ S.image tag).card ≤ E.card)
    (sound : ∀ k ∈ S, ∀ x ∈ P, vl gs x (tag k) = true → vl gs x o = true)
    (restore : ∀ cs v, MClean m cs → v < m+cs.length →
      (∀ x ∈ P, vl cs x v = vl gs x o) → gs.length ≤ cs.length+c) :
    S.card+D.card+Z.card ≤ c+(S.image tag).card := by
  have folds k (hk : k ∈ D.image f) : ∃ i ∈ S, Reads gs k (m+i) ∧ ∀ x ∈ P, vl gs x (src i) = false ∧ src i < m := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    exact Exists.intro i (And.intro (sub hi) (And.intro (use i hi) (dark i hi)))
  obtain ⟨cs,v,hc',hv,len,ev⟩ := cut_and_fold hc ho P (D.image f) E Z dis disE rd
    folds zero extra sound
  have bound := restore cs v hc' hv ev
  rw [Finset.card_image_of_injOn inj] at len
  apply PrivateGridProbe.zero_partner_credit
  omega

/-- In the two-pencil grid either the row or the column distinguishes any
two crossings. The two infinity inputs may take arbitrary Boolean values. -/
theorem grid_separates {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (p : Fin 1001 × Fin 1001 → Fin n) (row col : Fin 1001 → Fin n)
    (rows : ∀ a, row a ∈ S) (cols : ∀ b, col b ∈ S)
    (hr : ∀ i a, I (p i) (row a) ↔ i.1=a) (hc : ∀ i b, I (p i) (col b) ↔ i.2=b)
    (i j : Fin 1001 × Fin 1001) (ne : i ≠ j) : ∃ l ∈ S, I (p i) l ∧ ¬ I (p j) l := by
  by_cases e : i.1=j.1
  · have d : i.2 ≠ j.2 := fun h => ne (Prod.ext e h)
    exact ⟨col i.2,cols _,(hc ..).mpr rfl,fun h => d ((hc ..).mp h).symm⟩
  · exact ⟨row i.1,rows _,(hr ..).mpr rfl,fun h => e ((hr ..).mp h).symm⟩

/-- Select one actual OR reader for each untouched zero partner. Distinct
partners give different extra gates even when their groups have unequal sizes. -/
theorem extra_readers {gs : List Gate} (R S F Z : Finset ℕ) (src tag : ℕ → ℕ)
    (cover : Z ⊆ R.image tag) (separate : Disjoint R F)
    (rd : ∀ k ∈ R, OrRd gs k (src k) (tag k)) :
    ∃ E : Finset ℕ, Disjoint (S ∪ F) E ∧ E.card = (Z \ S.image tag).card ∧
      ∀ k ∈ E, ∃ a z, z ∈ Z ∧ OrRd gs k a z := by
  classical
  let U := Z \ S.image tag
  have pick (z : U) : ∃ k ∈ R, tag k = z.val :=
    Finset.mem_image.mp (cover (Finset.mem_sdiff.mp z.property).1)
  choose k hk eq using pick
  have inj : Function.Injective k := by
    intro a b h
    exact Subtype.ext ((eq a).symm.trans ((congrArg tag h).trans (eq b)))
  let E := U.attach.image k
  refine ⟨E,Finset.disjoint_left.mpr ?_,?_,?_⟩
  · intro v hv he
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_union.mp hv with hs|hf
    · exact (Finset.mem_sdiff.mp z.property).2
        (Finset.mem_image.mpr ⟨k z,hs,eq z⟩)
    · exact Finset.disjoint_left.mp separate (hk z) hf
  · simp [E,U,Finset.card_image_of_injective _ inj]
  · intro v hv
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨_,_,(Finset.mem_sdiff.mp z.property).1,eq z ▸ rd _ (hk z)⟩

/-- The one-gate bound on pinning each crossing enforces all of the reader
hypotheses used by the incidence matching. -/
theorem tight_matching {J : Type*} [Finite J] [Nontrivial J] {n : ℕ} {gs : List Gate}
    (I : Fin n → Fin n → Prop) (S : Finset (Fin n)) (p : J → Fin n)
    (o : ℕ) (ho : o < gs.length) (least : MLeast (n+n) (edgeFun I S) gs (n+n+o))
    (sep : ∀ i j, i ≠ j → ∃ l ∈ S, I (p i) l ∧ ¬ I (p j) l)
    (dep : ∀ i, ∃ x, edgeFun I S (Function.update x (Fin.castAdd n (p i))
      (!(x (Fin.castAdd n (p i))))) ≠ edgeFun I S x)
    (nc : ∀ i, ∃ x y, edgeFun I S (Function.update x (Fin.castAdd n (p i)) false) ≠
      edgeFun I S (Function.update y (Fin.castAdd n (p i)) false))
    (tight : ∀ i s, HasMonoSize (n+n)
      (fun x => edgeFun I S (Function.update x (Fin.castAdd n (p i)) false)) s →
      gs.length ≤ s+1) :
    ∃ r t f : J → ℕ, Function.Injective f ∧
      ∀ i, OrRd gs (r i) (Fin.castAdd n (p i)) (t i) ∧
        (∀ k, Reads gs k (Fin.castAdd n (p i)) → k=r i) ∧ Reads gs (f i) (n+n+r i) := by
  classical
  have someReader (i : J) : ∃ k, Reads gs k (Fin.castAdd n (p i)) := by
    apply Free.read_of_dep least.2.2.1 _ (dep i)
    have := (Fin.castAdd n (p i)).isLt
    omega
  choose r hr using someReader
  have rigid i := PrivateGridMarginal.rigid_reader least (Fin.castAdd n (p i)) (nc i) (tight i)
  have sole i k (h : Reads gs k (Fin.castAdd n (p i))) := (rigid i).1 _ _ h (hr i)
  have orGate i : ∃ t, OrRd gs (r i) (Fin.castAdd n (p i)) t := by
    obtain ⟨g,hg,mem⟩ := hr i
    rcases least.1 _ _ hg with ⟨hn,_⟩|⟨ops,a,b,_,_,ins⟩
    · exact False.elim (least.clean.2 g (List.mem_of_getElem? hg) hn)
    have op := ops.resolve_left ((rigid i).2 _ g hg mem)
    simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with e|e
    · exact ⟨b,g,hg,op,Or.inl (e.symm ▸ ins)⟩
    · exact ⟨a,g,hg,op,Or.inr (e.symm ▸ ins)⟩
  choose t ht using orGate
  obtain ⟨f,inj,hf⟩ := incidence_matching I S p r t o ho least.clean least.2.2.1 ht sole sep
  exact ⟨r,t,f,inj,fun i => ⟨ht i,sole i,hf i⟩⟩

/-- Separating lines give both essentiality of the raw crossing and a
nonconstant cofactor after it is pinned off. -/
theorem crossing_tests {J : Type*} [Nontrivial J] {n : ℕ}
    (I : Fin n → Fin n → Prop) (S : Finset (Fin n)) (p : J → Fin n)
    (sep : ∀ i j, i ≠ j → ∃ l ∈ S, I (p i) l ∧ ¬ I (p j) l) (i : J) :
    (∃ x, edgeFun I S (Function.update x (Fin.castAdd n (p i))
      (!(x (Fin.castAdd n (p i))))) ≠ edgeFun I S x) ∧
    ∃ x y, edgeFun I S (Function.update x (Fin.castAdd n (p i)) false) ≠
      edgeFun I S (Function.update y (Fin.castAdd n (p i)) false) := by
  classical
  obtain ⟨j,ne⟩ := exists_ne i
  obtain ⟨l,hl,hi,miss⟩ := sep i j ne.symm
  obtain ⟨h,hh,hj,_⟩ := sep j i ne
  let a := Fin.castAdd n (p i)
  let x (z : Fin (n+n)) := decide (z = Fin.natAdd n l)
  have off (q : Fin n) : x (Fin.castAdd n q) = false := by
    exact decide_eq_false (left_ne_right q l)
  have neg : edgeFun I S x = false := by
    apply Bool.eq_false_iff.mpr
    intro e
    obtain ⟨q,_,_,_,on,_⟩ := (edgeFun_true ..).mp e
    rw [off] at on
    contradiction
  have pos : edgeFun I S (Function.update x a true) = true := (edgeFun_true ..).mpr
    ⟨p i,l,hl,hi,by exact Function.update_self ..,by
      rw [Function.update_of_ne (left_ne_right (p i) l).symm]
      simp [x]⟩
  constructor
  · exact ⟨x,by rw [off]; exact fun e => Bool.noConfusion (pos.symm.trans (e.trans neg))⟩
  · let z := pairInput (p j) h
    have neq : p j ≠ p i := fun e => miss (e.symm ▸ hi)
    have on : edgeFun I S (Function.update z a false) = true := (edgeFun_true ..).mpr
      ⟨p j,h,hh,hj,by
        rw [Function.update_of_ne (show Fin.castAdd n (p j) ≠ a from
          fun e => neq ((Fin.castAdd_injective n n) e))]
        simp only [z,pair_point,decide_true],by
        rw [Function.update_of_ne (left_ne_right (p i) h).symm]
        simp only [z,pair_line,decide_true]⟩
    have zero : Function.update (fun _ : Fin (n+n) => false) a false = fun _ => false := by
      funext v
      by_cases e : v=a <;> simp [e]
    exact ⟨_,z,by rw [zero,edgeFun_zero,on]; decide⟩

/-- Transfer a ten-gate deletion budget to the pinned crossing by restoring
one erased twin. The lower bound on the pinned deletion is a separate input. -/
theorem ten_matching {J : Type*} [Finite J] [Nontrivial J] {n : ℕ} {gs : List Gate}
    (I : Fin n → Fin n → Prop) (S : Finset (Fin n)) (l : Fin n) (p : J → Fin n)
    (o e : ℕ) (ho : o < gs.length) (least : MLeast (n+n) (edgeFun I S) gs (n+n+o))
    (sep : ∀ i j, i ≠ j → ∃ a ∈ S, I (p i) a ∧ ¬ I (p j) a)
    (ten : gs.length ≤ e+10)
    (emin : ∀ s, HasMonoSize (n+n) (edgeFun I (S.erase l)) s → e ≤ s)
    (pinDrop : ∀ i s, HasMonoSize (n+n)
      (fun x => edgeFun I S (Function.update x (Fin.castAdd n (p i)) false)) s →
      ∃ t, t+10 ≤ s ∧ HasMonoSize (n+n)
        (fun x => edgeFun I (S.erase l) (Function.update x (Fin.castAdd n (p i)) false)) t)
    (restoreTwin : ∀ i t, HasMonoSize (n+n)
      (fun x => edgeFun I (S.erase l) (Function.update x (Fin.castAdd n (p i)) false)) t →
      HasMonoSize (n+n) (edgeFun I (S.erase l)) (t+1)) :
    ∃ r t f : J → ℕ, Function.Injective f ∧
      ∀ i, OrRd gs (r i) (Fin.castAdd n (p i)) (t i) ∧
        (∀ k, Reads gs k (Fin.castAdd n (p i)) → k=r i) ∧ Reads gs (f i) (n+n+r i) := by
  apply tight_matching I S p o ho least sep (fun i => (crossing_tests I S p sep i).1)
    (fun i => (crossing_tests I S p sep i).2)
  intro i s hs
  obtain ⟨t,ht,small⟩ := pinDrop i s hs
  have := emin _ (restoreTwin i t small)
  omega

end Onlyfr.PrivateGridMatching
