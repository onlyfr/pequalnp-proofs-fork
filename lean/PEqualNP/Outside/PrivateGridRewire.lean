import PEqualNP.Outside.PrivateReaderDrop
import PEqualNP.Outside.PrivateOrReader

namespace Onlyfr.PrivateGridRewire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
variable {m : ℕ} {gs : List Gate} {S : Finset ℕ} {src tag : ℕ → ℕ}

/-- Keep original numbering until all taps and constant folds have been specified. -/
def bypass (gs : List Gate) (S : Finset ℕ) (src : ℕ → ℕ) : List Gate :=
  List.ofFn fun i : Fin gs.length =>
    if i.val ∈ S then ⟨.and, [src i, src i]⟩ else gs[i]

@[simp] theorem bypass_length : (bypass gs S src).length = gs.length := by simp [bypass]

theorem bypass_get (hk : k < gs.length) :
    (bypass gs S src)[k]? = some (if k ∈ S then ⟨.and,[src k,src k]⟩ else gs[k]) := by
  simp [bypass,hk]

theorem bypass_clean (hc : MClean m gs) (early : ∀ k ∈ S, src k < m+k) :
    MClean m (bypass gs S src) := by
  constructor
  · intro k g hg
    have hk : k < gs.length := by
      by_contra! bad
      simp [List.getElem?_eq_none_iff.mpr (by simpa using bad : (bypass gs S src).length ≤ k)] at hg
    rw [bypass_get hk] at hg
    by_cases h : k ∈ S
    · simp [h] at hg
      subst g
      exact Or.inr ⟨Or.inl rfl,src k,src k,early k h,early k h,rfl⟩
    · simp [h] at hg
      subst g
      exact hc.1 k _ (List.getElem?_eq_getElem hk)
  · intro g hg
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hg
    have hlen : k < gs.length := by
      by_contra! bad
      simp [List.getElem?_eq_none_iff.mpr (by simpa using bad : (bypass gs S src).length ≤ k)] at hk
    rw [bypass_get hlen] at hk
    by_cases h : k ∈ S <;> simp [h] at hk <;> subst g
    · intro e; cases e
    · exact hc.2 _ (List.getElem_mem ..)

theorem bypass_alias (hc : MClean m gs) (early : ∀ k ∈ S, src k < m+k)
    (hk : k < gs.length) (hs : k ∈ S) (x : Fin m → Bool) :
    vl (bypass gs S src) x (m+k) = vl (bypass gs S src) x (src k) := by
  have hg := bypass_get (S := S) (src := src) hk
  simp only [hs,ite_true] at hg
  rw [vl_gate _ (bypass_clean hc early).1 _ _ _ hg]
  simp [GateOp.eval]

theorem orrd_eval (hc : CleanL m gs) (h : OrRd gs k a b) (x : Fin m → Bool) :
    vl gs x (m+k) = (vl gs x a || vl gs x b) := by
  obtain ⟨g,hg,op,ins|ins⟩ := h <;>
    rw [vl_gate _ hc _ _ _ hg,op,ins] <;> simp [GateOp.eval,Bool.or_comm]

private theorem gate_mono (op : GateOp) (hop : op = .and ∨ op = .or) (l : List ℕ)
    (v w : ℕ → Bool) (le : ∀ j ∈ l, v j = true → w j = true)
    (h : op.eval (l.map v) = true) : op.eval (l.map w) = true := by
  rcases hop with rfl|rfl
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id] at h ⊢
    exact fun j hj => le j hj (h j hj)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id] at h ⊢
    obtain ⟨j,hj,hy⟩ := h
    exact ⟨j,hj,le j hj hy⟩

/-- Every rewired wire is a lower approximation. If the modified taps all
vanish then every wire agrees, including taps depending on earlier readers. -/
theorem bypass_values (hc : MClean m gs) (read : ∀ k ∈ S, OrRd gs k (src k) (tag k))
    (x : Fin m → Bool) (w : ℕ) (bound : w < m+gs.length) :
    let V := vl (bypass gs S src) x
    (V w = true → vl gs x w = true) ∧
    ((∀ k ∈ S, V (tag k) = false) → V w = vl gs x w) := by
  have rd (k) (hk : k ∈ S) : Reads gs k (src k) ∧ Reads gs k (tag k) := by
    obtain ⟨g,hg,_,hi|hi⟩ := read k hk <;>
      exact ⟨⟨g,hg,by simp [hi]⟩,⟨g,hg,by simp [hi]⟩⟩
  have early (k) (hk : k ∈ S) := reads_lt hc.1 (rd k hk).1
  have hc' := (bypass_clean hc early).1
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    dsimp only
    by_cases raw : w < m
    · simp [vl_input _ x w raw]
    obtain ⟨k,rfl⟩ : ∃ k, w = m+k := ⟨w-m,by omega⟩
    have hk : k < gs.length := by omega
    by_cases h : k ∈ S
    · have a := ih (src k) (early k h) (by have := early k h; omega)
      have et := reads_lt hc.1 (rd k h).2
      have b := ih (tag k) et (by omega)
      rw [bypass_alias hc early hk h,orrd_eval hc.1 (read k h)]
      constructor
      · intro yes
        simp [a.1 yes]
      · intro off
        rw [← a.2 off, ← b.2 off, off k h, Bool.or_false]
    · have hg := List.getElem?_eq_getElem (l := gs) hk
      have hg' := bypass_get (S := S) (src := src) hk
      simp only [h,ite_false] at hg'
      have clean := hc.1 k _ hg
      have op : gs[k].op = .and ∨ gs[k].op = .or := by
        rcases clean with ⟨bad,_⟩|⟨good,_⟩
        · exact False.elim (hc.2 _ (List.getElem_mem ..) bad)
        · exact good
      rw [vl_gate _ hc' _ _ _ hg',vl_gate _ hc.1 _ _ _ hg]
      constructor
      · apply gate_mono _ op
        intro j hj
        have lt := clean.lt j hj
        exact (ih j lt (by omega)).1
      · intro off
        congr 1
        apply List.map_congr_left
        intro j hj
        have lt := clean.lt j hj
        exact (ih j lt (by omega)).2 off

/-- One additional OR per distinct tap; all intermediate taps are read
from the same gate list. -/
theorem append_taps (hc : MClean m gs) (ho : o < m+gs.length) (T : Finset ℕ)
    (valid : ∀ t ∈ T, t < m+gs.length) :
    ∃ (cs : List Gate) (v : ℕ), MClean m cs ∧ v < m+cs.length ∧
      cs.length = gs.length+T.card ∧
      (∀ x : Fin m → Bool, vl cs x v = true ↔
        vl gs x o = true ∨ ∃ t ∈ T, vl gs x t = true) ∧
      ∀ x : Fin m → Bool, ∀ j < m+gs.length, vl cs x j = vl gs x j := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨gs,o,hc,ho,by simp,by simp,by simp⟩
  | @insert t T ht ih =>
    obtain ⟨cs,v,hcs,hv,len,out,keep⟩ := ih (fun a ha => valid a (Finset.mem_insert_of_mem ha))
    have ht0 := valid t (Finset.mem_insert_self ..)
    obtain ⟨hc',values⟩ := Clean.ToolSnoc_proof m cs v t hcs hv (by omega)
    refine ⟨_,m+cs.length,hc',by simp,by simp [len,ht,Nat.add_assoc],?_,?_⟩
    · intro x
      rw [(values x).1, Bool.or_eq_true, out x, keep x t ht0]
      simp only [Finset.mem_insert]
      aesop
    · intro x j hj
      exact ((values x).2 j (by omega)).trans (keep x j hj)

/-- Compress the modified DAG on the restriction P, then append only the
surviving taps. The alias hypotheses concern the modified circuit, not the
original one. All removals share one renumbering of wires. -/
theorem repair_circuit (hc : MClean m gs) (ho : o < m+gs.length)
    (read : ∀ k ∈ S, OrRd gs k (src k) (tag k))
    (P : Set (Fin m → Bool)) (drop taps : Finset ℕ) (toWire : ℕ → ℕ)
    (aliases : ∀ k ∈ drop, k < gs.length ∧ toWire k < m+k ∧ ∀ x ∈ P,
      vl (bypass gs S src) x (m+k) = vl (bypass gs S src) x (toWire k))
    (valid : ∀ t ∈ taps, t < m+gs.length)
    (sound : ∀ x ∈ P, ∀ t ∈ taps, vl gs x t = true → vl gs x o = true)
    (cover : ∀ x ∈ P, ∀ k ∈ S, vl (bypass gs S src) x (tag k) = true →
      ∃ t ∈ taps, vl (bypass gs S src) x t = true) :
    ∃ (cs : List Gate) (v : ℕ), MClean m cs ∧ v < m+cs.length ∧
      cs.length+drop.card ≤ gs.length+taps.card ∧
      ∀ x ∈ P, vl cs x v = vl gs x o := by
  classical
  let bs := bypass gs S src
  have early k (h : k ∈ S) : src k < m+k := by
    obtain ⟨g,hg,_,hi|hi⟩ := read k h <;>
      exact reads_lt hc.1 (show Reads gs k (src k) from ⟨g,hg,by simp [hi]⟩)
  have hb : MClean m bs := bypass_clean hc early
  have bl : bs.length = gs.length := bypass_length
  have rem : Removable m bs o P drop (fun k => some (toWire k)) := by
    intro k hk
    obtain ⟨bound,lt,eq⟩ := aliases k hk
    exact ⟨bl.symm ▸ bound, Or.inl ⟨_,rfl,lt,eq⟩⟩
  obtain ⟨ds,r,hd,hmono,hlen,_,hval⟩ :=
    Removal.ToolRemoval_proof m bs o P drop _ hb.1 rem
  have val (j) (hj : j < m+gs.length) := hval j (by omega) (by simp)
  obtain ⟨cs,v,clean,hv,len,out,_⟩ := append_taps (show MClean m ds from ⟨hd,hmono hb.2⟩)
    (val o ho).1 (taps.image r) (by
      intro j hj
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hj
      exact (val t (valid t ht)).1)
  have card := Finset.card_image_le (s := taps) (f := r)
  refine ⟨cs,v,clean,hv,by omega,?_⟩
  intro x hx
  apply Bool.eq_iff_iff.mpr
  rw [out x,(val o ho).2 x hx]
  constructor
  · rintro (h|⟨j,hj,h⟩)
    · exact (bypass_values hc read x o ho).1 h
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hj
      rw [(val t (valid t ht)).2 x hx] at h
      exact sound x hx t ht ((bypass_values hc read x t (valid t ht)).1 h)
  · intro h
    by_cases off : ∀ k ∈ S, vl bs x (tag k) = false
    · exact Or.inl (((bypass_values hc read x o ho).2 off).trans h)
    · push Not at off
      obtain ⟨k,hk,on⟩ := off
      obtain ⟨t,ht,tv⟩ := cover x hx k hk (by simpa [bs] using on)
      exact Or.inr ⟨_,Finset.mem_image_of_mem r ht,((val t (valid t ht)).2 x hx).trans tv⟩

theorem keep_get (h : k ∉ S) (hg : gs[k]? = some g) :
    (bypass gs S src)[k]? = some g := by
  by_cases hk : k < gs.length
  · rw [bypass_get hk,ite_eq_right h,← List.getElem?_eq_getElem hk]
    exact hg
  · simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hk)] at hg

/-- Concrete simultaneous bypass and fold. S contains the readers bypassed;
F the matched consumers of zero inputs; E the untouched readers whose
partners are forced false. No hypothesis postulates the desired circuit or
the number of gates saved. -/
theorem cut_and_fold (hc : MClean m gs) (ho : o < m+gs.length)
    (P : Set (Fin m → Bool)) (F E Z : Finset ℕ)
    (disSF : Disjoint S F) (disE : Disjoint (S ∪ F) E)
    (read : ∀ k ∈ S, OrRd gs k (src k) (tag k))
    (folds : ∀ k ∈ F, ∃ i ∈ S, Reads gs k (m+i) ∧
      ∀ x ∈ P, vl gs x (src i) = false ∧ src i < m)
    (zeros : ∀ z ∈ Z, ∃ k ∈ F, z = m+k ∧
      ∃ g, gs[k]? = some g ∧ g.op = .and)
    (extra : ∀ k ∈ E, ∃ a z, z ∈ Z ∧ OrRd gs k a z)
    (sound : ∀ k ∈ S, ∀ x ∈ P, vl gs x (tag k) = true → vl gs x o = true) :
    ∃ (cs : List Gate) (v : ℕ), MClean m cs ∧ v < m+cs.length ∧
      cs.length+S.card+F.card+E.card ≤ gs.length+((S.image tag) \ Z).card ∧
      ∀ x ∈ P, vl cs x v = vl gs x o := by
  classical
  let bs := bypass gs S src
  have rr k (hk : k ∈ S) : Reads gs k (src k) ∧ Reads gs k (tag k) := by
    obtain ⟨g,hg,_,hi|hi⟩ := read k hk <;>
      exact ⟨⟨g,hg,by simp [hi]⟩,⟨g,hg,by simp [hi]⟩⟩
  have early k (hk : k ∈ S) := reads_lt hc.1 (rr k hk).1
  have hb : MClean m bs := bypass_clean hc early
  have Fnot k (hk : k ∈ F) : k ∉ S := fun h => Finset.disjoint_left.mp disSF h hk
  have Enot k (hk : k ∈ E) : k ∉ S := fun h =>
    Finset.disjoint_left.mp disE (Finset.mem_union_left _ h) hk
  have low k (hk : k ∈ F) : ∃ w, Reads bs k w ∧ ∀ x ∈ P, vl bs x w = false := by
    obtain ⟨i,hi,⟨g,hg,hin⟩,off⟩ := folds k hk
    refine ⟨m+i,⟨g,keep_get (Fnot k hk) hg,hin⟩,?_⟩
    intro x hx
    have ⟨hz,raw⟩ := off x hx
    rw [bypass_alias hc early (reads_len (rr i hi).1) hi,
      vl_input _ x _ raw, ← vl_input gs x _ raw]
    exact hz
  have zero z (hz : z ∈ Z) (x) (hx : x ∈ P) : vl bs x z = false := by
    obtain ⟨k,hk,rfl,g,hg,hand⟩ := zeros z hz
    obtain ⟨w,⟨g',hg',hw⟩,off⟩ := low k hk
    have keep : bs[k]? = some g := keep_get (Fnot k hk) hg
    have eq : g' = g := Option.some.inj (hg'.symm.trans keep)
    subst g'
    have ev := vl_abs bs hb.1 x k g keep (Or.inl hand) w hw
    simpa [fixBit,hand] using ev (by simpa [fixBit,hand] using off x hx)
  let D := (S ∪ F) ∪ E
  have aliases k (hk : k ∈ D) : k < gs.length ∧ ∃ t < m+k,
      ∀ x ∈ P, vl bs x (m+k) = vl bs x t := by
    rcases Finset.mem_union.mp hk with h|he
    · rcases Finset.mem_union.mp h with hs|hf
      · exact ⟨reads_len (rr k hs).1,src k,early k hs,fun x _ =>
          bypass_alias hc early (reads_len (rr k hs).1) hs x⟩
      · obtain ⟨w,hr,off⟩ := low k hf
        exact ⟨by simpa [bs] using reads_len hr, Free.alias_of_rd hb.1 hb.2 hr P false off⟩
    · obtain ⟨a,z,hz,g,hg,hop,hin⟩ := extra k he
      have og : OrRd bs k a z := ⟨g,keep_get (Enot k he) hg,hop,hin⟩
      have rd : Reads gs k a := ⟨g,hg,by rcases hin with h|h <;> simp [h]⟩
      exact ⟨reads_len rd,a,reads_lt hc.1 rd,fun x hx => by
        rw [orrd_eval hb.1 og,zero z hz x hx,Bool.or_false]⟩
  let tgt (k : ℕ) := if h : k ∈ D then ((aliases k h).2).choose else 0
  have dc : D.card = S.card+F.card+E.card := by
    rw [show D = (S ∪ F) ∪ E from rfl,Finset.card_union_of_disjoint disE,
      Finset.card_union_of_disjoint disSF]
  obtain ⟨cs,v,hc',hv,len,agree⟩ := repair_circuit hc ho read P D ((S.image tag) \ Z) tgt
    (by
      intro k hk
      simpa [tgt,hk] using And.intro (aliases k hk).1 (aliases k hk).2.choose_spec)
    (by
      intro t ht
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp ht).1
      have := reads_lt hc.1 (rr k hk).2
      have := reads_len (rr k hk).2
      omega)
    (by
      intro x hx t ht
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp ht).1
      exact sound k hk x hx)
    (by
      intro x hx k hk on
      refine ⟨tag k,Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hk,?_⟩,on⟩
      intro hz
      exact Bool.noConfusion ((zero _ hz x hx).symm.trans on))
  exact ⟨cs,v,hc',hv,by omega,agree⟩

private theorem wire_mono (hc : MClean m gs) (x y : Fin m → Bool)
    (le : ∀ i, x i = true → y i = true) (w : ℕ) (hw : w < m+gs.length) :
    vl gs x w = true → vl gs y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w < m
    · simpa [vl_input gs x w raw,vl_input gs y w raw] using le ⟨w,raw⟩
    obtain ⟨k,rfl⟩ : ∃ k, w = m+k := ⟨w-m,by omega⟩
    have hk : k < gs.length := by omega
    have hg := List.getElem?_eq_getElem (l := gs) hk
    have cl := hc.1 k _ hg
    have op : gs[k].op = .and ∨ gs[k].op = .or := by
      rcases cl with ⟨bad,_⟩|⟨good,_⟩
      · exact False.elim (hc.2 _ (List.getElem_mem ..) bad)
      · exact good
    rw [vl_gate _ hc.1 x _ _ hg,vl_gate _ hc.1 y _ _ hg]
    apply gate_mono _ op
    intro j hj
    have lt := cl.lt j hj
    exact ih j lt (by omega)

open Onlyfr.PrivateIncidenceDrop

/-- On any input with all points of an active line off, the partner of an
incident crossing certifies the output. The line selector need not be off. -/
theorem dark_partner_sound {n : ℕ} (I : Fin n → Fin n → Prop) (lines : Finset (Fin n))
    (p l : Fin n) (hl : l ∈ lines) (inc : I p l)
    (hc : MClean (n+n) gs) (hev : Computes (n+n) gs o (edgeFun I lines))
    (reader : OrRd gs k (Fin.castAdd n p) t)
    (onlyReader : ∀ j, Reads gs j (Fin.castAdd n p) → j = k)
    (x : Fin (n+n) → Bool) (dark : ∀ q, I q l → x (Fin.castAdd n q) = false) :
    vl gs x t = true → vl gs x o = true := by
  classical
  intro fire
  let a := Fin.castAdd n p
  let b := Fin.natAdd n l
  let y := Function.update x b true
  let z := Function.update y a true
  have ne : a ≠ b := left_ne_right p l
  have up (w : Fin (n+n) → Bool) (j u : Fin (n+n)) :
      w u = true → Function.update w j true u = true := by
    by_cases e : u = j <;> simp [e]
  have rt : Reads gs k t := by
    obtain ⟨g,hg,_,hi|hi⟩ := reader <;> exact ⟨g,hg,by simp [hi]⟩
  have lim : t < n+n+gs.length := by
    have := reads_lt hc.1 rt
    have := reads_len rt
    omega
  have fy := wire_mono hc x y (up x b) t lim fire
  have fz := wire_mono hc y z (up y a) t lim fy
  have yes : vl gs z o = true := by
    rw [hev]
    exact (edgeFun_true ..).mpr ⟨p,l,hl,inc,by simp [z,a],by
      change Function.update y a true b = true
      rw [Function.update_of_ne ne.symm]
      exact Function.update_self ..⟩
  have ho : o ≠ (a : ℕ) := by
    intro eq
    let s : Fin (n+n) → Bool := fun j => decide (j = a)
    have hs := hev s
    rw [eq,vl_input _ _ _ a.isLt] at hs
    have st : edgeFun I lines s = true := by simpa [s] using hs.symm
    obtain ⟨q,v,_,_,_,hv⟩ := (edgeFun_true ..).mp st
    exact (left_ne_right p v).symm (of_decide_eq_true hv)
  have agree := Onlyfr.PrivateOrReader.agree_of_one_reader hc.1 y z
    (fun j => j = (a : ℕ)) k o ho (by
      intro j hj
      have ne' : j ≠ a := fun eq => hj (congrArg Fin.val eq)
      simp [z,ne']) (by
      intro j w hr eq
      exact onlyReader j (eq ▸ hr)) (by simp [orrd_eval hc.1 reader,fy,fz])
  have hy := agree.trans yes
  rw [hev] at hy ⊢
  obtain ⟨q,v,hv,hi,hq,hs⟩ := (edgeFun_true ..).mp hy
  have hqx : x (Fin.castAdd n q) = true := by
    simpa only [y,b,Function.update_of_ne (left_ne_right q l)] using hq
  have vne : v ≠ l := by
    rintro rfl
    rw [dark q hi] at hqx
    contradiction
  have different : Fin.natAdd n v ≠ b := fun eq => vne (Fin.natAdd_injective n n eq)
  exact (edgeFun_true ..).mpr ⟨q,v,hv,hi,hqx,by simpa only [y,Function.update_of_ne different] using hs⟩

open Onlyfr.PrivateGateDrop

/-- Restrict arbitrarily many input bits without increasing size whenever
the final function is nonconstant. -/
theorem pin_size (Q : Finset (Fin m)) (f : (Fin m → Bool) → Bool)
    (hf : HasMonoSize m f s)
    (nc : ∃ x y, f (pin Q x) ≠ f (pin Q y)) :
    HasMonoSize m (fun x => f (pin Q x)) s := by
  classical
  induction Q using Finset.induction_on generalizing f with
  | empty => simpa only [pin_empty] using hf
  | @insert i A hi ih =>
    let f' := fun x => f (Function.update x i false)
    have nc' : ∃ x y, f' (pin A x) ≠ f' (pin A y) := by
      simpa only [pin_insert,f'] using nc
    obtain ⟨x,y,hxy⟩ := nc'
    have h := restrict_input m s f i false hf ⟨pin A x,pin A y,hxy⟩
    simpa only [pin_insert,f'] using ih f' h ⟨x,y,hxy⟩

/-- Convert agreement on a pinned subcube to a circuit computing the pinned
target on every input, as required before precomposing the private twins. -/
theorem size_from_subcube (Q : Finset (Fin m)) (hc : MClean m gs)
    (f : (Fin m → Bool) → Bool) (o : ℕ)
    (agree : ∀ x, (∀ i ∈ Q, x i = false) → vl gs x o = f x)
    (nc : ∃ x y, f (pin Q x) ≠ f (pin Q y)) :
    HasMonoSize m (fun x => f (pin Q x)) gs.length := by
  have eq (x : Fin m → Bool) : vl gs (pin Q x) o = f (pin Q x) :=
    agree _ (fun i hi => by simp [pin,hi])
  have := pin_size Q (fun x => vl gs x o) (Clean.ToolOfClean_proof m gs o hc)
    (by simpa only [eq] using nc)
  simpa only [eq] using this
end Onlyfr.PrivateGridRewire
