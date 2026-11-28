import PEqualNP.Outside.PrivateGridRewire

namespace Onlyfr.PrivateGridCompose
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateGridRewire

/-- Run a clean core after a prefix supplying its input wires. -/
theorem compose_prefix {m n : ℕ} (pre core : List Gate) (hp : MClean m pre)
    (hc : MClean n core) (input : Fin n → ℕ)
    (range : ∀ i, input i < m+pre.length) (o : ℕ) (out : o < n+core.length) :
    ∃ (gs : List Gate) (v : ℕ), MClean m gs ∧ v < m+gs.length ∧
      gs.length = pre.length+core.length ∧
      ∀ x : Fin m → Bool, vl gs x v = vl core (fun i => vl pre x (input i)) o := by
  let r (w : ℕ) := if h : w < n then input ⟨w,h⟩ else m+pre.length+(w-n)
  let gs := pre ++ core.map (Removal.rg r)
  have len : gs.length = pre.length+core.length := by simp [gs]
  have rb (w k : ℕ) (h : w < n+k) : r w < m+(pre.length+k) := by
    dsimp only [r]
    split
    · have := range ⟨w,by assumption⟩
      omega
    · omega
  have get (k : ℕ) (g : Gate) (h : core[k]? = some g) :
      gs[pre.length+k]? = some (Removal.rg r g) := by
    simp [gs,List.getElem?_append_right,h]
  have clean : MClean m gs := by
    constructor
    · intro j g hg
      by_cases h : j < pre.length
      · exact hp.1 _ _ (by simpa [gs,List.getElem?_append_left h] using hg)
      obtain ⟨k,rfl⟩ : ∃ k, j = pre.length+k := ⟨j-pre.length,by omega⟩
      have hh : (core[k]?).map (Removal.rg r) = some g := by
        simpa [gs,List.getElem?_append_right] using hg
      obtain ⟨q,hq,rfl⟩ := Option.map_eq_some_iff.mp hh
      rcases hc.1 k q hq with ⟨hn,a,ha,ins⟩|⟨hop,a,b,ha,hb,ins⟩
      · exact Or.inl ⟨hn,r a,rb _ _ ha,by simp [Removal.rg,ins]⟩
      · exact Or.inr ⟨hop,r a,r b,rb _ _ ha,rb _ _ hb,by simp [Removal.rg,ins]⟩
    · intro g hg
      rcases List.mem_append.mp hg with h|h
      · exact hp.2 _ h
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
      exact hc.2 q hq
  refine ⟨gs,r o,clean,by simpa [len] using rb o _ out,len,?_⟩
  intro x
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    by_cases h : o < n
    · rw [vl_input _ _ _ h]
      have hr : r o = input ⟨o,h⟩ := by simp [r,h]
      rw [hr]
      unfold vl
      simp only [gs,wiresFrom_append]
      rw [getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simpa using range ⟨o,h⟩)]
    obtain ⟨k,rfl⟩ : ∃ k, o = n+k := ⟨o-n,by omega⟩
    have hk : k < core.length := by omega
    have hg := List.getElem?_eq_getElem (l := core) hk
    have hr : r (n+k) = m+(pre.length+k) := by simp [r,Nat.add_assoc]
    rw [hr,vl_gate _ clean.1 _ _ _ (get k _ hg),vl_gate _ hc.1 _ _ _ hg]
    simp only [Removal.rg,List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    have lt := (hc.1 k _ hg).lt w hw
    exact ih w lt (by omega)

/-- Replace a private bit by its OR with one more input, costing one gate.
This works even if that private bit has unbounded fanout. -/
theorem add_twin {m s : ℕ} (f : (Fin m → Bool) → Bool) (hf : HasMonoSize m f s)
    (nc : ∃ x y, f x ≠ f y) (i j : Fin m) :
    HasMonoSize m (fun x => f (Function.update x i (x i || x j))) (s+1) := by
  obtain ⟨gs,o,hc,hn,len,eval⟩ := Clean.mclean_of m f s nc hf
  have out : o < m+gs.length := by
    by_contra! h
    obtain ⟨x,y,ne⟩ := nc
    exact ne (by rw [← eval x,← eval y,Removal.vl_past gs x h,Removal.vl_past gs y h])
  let pre : List Gate := [⟨.or,[i,j]⟩]
  have empty : MClean m [] := by constructor <;> simp [CleanL,NotFree]
  obtain ⟨cl,values⟩ := Clean.ToolSnoc_proof m [] i j empty (by simp) (by simp)
  let input (a : Fin m) := if a = i then m else a.val
  obtain ⟨cs,v,clean,_,size,run⟩ := compose_prefix pre gs (by simpa [pre] using cl)
    ⟨hc,hn⟩ input (by intro a; simp [input,pre]; split <;> omega) o out
  have funEq : (fun x => vl cs x v) = fun x => f (Function.update x i (x i || x j)) := by
    funext x
    rw [run,eval]
    congr 1
    funext a
    by_cases eq : a = i
    · subst a
      simpa [pre,input,vl_input _ _ _ i.isLt,vl_input _ _ _ j.isLt] using (values x).1
    · simp [input,eq,vl_input pre x _ a.isLt]
  have := Clean.ToolOfClean_proof m cs v clean
  rw [funEq] at this
  exact this.mono (by simp [pre] at size; omega)
private theorem snoc_and (hc : MClean m gs) (ha : a < m+gs.length) (hb : b < m+gs.length) :
    let cs := gs ++ [⟨GateOp.and,[a,b]⟩]
    MClean m cs ∧ ∀ x : Fin m → Bool,
      vl cs x (m+gs.length) = (vl gs x a && vl gs x b) ∧
      ∀ j < m+gs.length, vl cs x j = vl gs x j := by
  let g : Gate := ⟨.and,[a,b]⟩
  have clean : CleanL m (gs++[g]) := by
    intro k q h
    by_cases keep : k < gs.length
    · rw [List.getElem?_append_left keep] at h
      exact hc.1 k q h
    · rw [List.getElem?_append_right (by omega)] at h
      have eq : k-gs.length = 0 := by
        by_contra bad
        rw [List.getElem?_eq_none (by simp; omega)] at h
        contradiction
      rw [eq] at h
      simp at h
      subst q
      have e : k = gs.length := by omega
      subst k
      exact Or.inr ⟨Or.inl rfl,a,b,ha,hb,rfl⟩
  have keep (x : Fin m → Bool) (j) (hj : j < m+gs.length) :
      vl (gs++[g]) x j = vl gs x j := by
    unfold vl
    rw [wiresFrom_append,getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simpa using hj)]
  refine ⟨⟨clean,?_⟩,fun x => ⟨?_,keep x⟩⟩
  · intro q hq
    rcases List.mem_append.mp hq with h|h
    · exact hc.2 q h
    · simp at h; subst q; intro e; cases e
  · change vl (gs++[g]) x (m+gs.length) = _
    rw [vl_gate _ clean x _ g (by simp)]
    simp [g,GateOp.eval,keep x a ha,keep x b hb]

/-- Restore a star by appending the OR of its raw point bits, the line AND
and an output OR. No extra initial constant gate is needed. -/
theorem add_star {m s : ℕ} (f : (Fin m → Bool) → Bool) (hf : HasMonoSize m f s)
    (nc : ∃ x y, f x ≠ f y) (l : Fin m) (P : Finset (Fin m)) (nonempty : P.Nonempty) :
    HasMonoSize m (fun x => f x || (x l && decide (∃ p ∈ P, x p = true))) (s+P.card+1) := by
  classical
  obtain ⟨gs,o,hg,hn,len,ev⟩ := Clean.mclean_of m f s nc hf
  have ho := Removal.out_lt ev nc
  obtain ⟨p,hp⟩ := nonempty
  let taps := (P.erase p).image Fin.val
  have card : taps.card+1 = P.card := by
    rw [show taps.card = (P.erase p).card from Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_erase_of_mem hp]
    have := Finset.card_pos.mpr (show P.Nonempty from ⟨p,hp⟩)
    omega
  obtain ⟨cs,v,hc,hv,lc,anyPoint,keep⟩ :=
    append_taps (show MClean m gs from ⟨hg,hn⟩) (o := p.val) (by omega) taps (by
      intro j hj
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hj
      omega)
  have row (x : Fin m → Bool) : vl cs x v = decide (∃ p ∈ P, x p = true) := by
    apply Bool.eq_iff_iff.mpr
    rw [anyPoint x,decide_eq_true_eq]
    constructor
    · rintro (h|⟨j,hj,h⟩)
      · exact ⟨p,hp,by simpa [vl_input gs x _ p.isLt] using h⟩
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hj
        exact ⟨u,Finset.mem_of_mem_erase hu,by simpa [vl_input gs x _ u.isLt] using h⟩
    · rintro ⟨u,hu,h⟩
      by_cases e : u = p
      · subst u; exact Or.inl (by simpa [vl_input gs x _ p.isLt] using h)
      · exact Or.inr ⟨_,Finset.mem_image_of_mem Fin.val (Finset.mem_erase.mpr ⟨e,hu⟩),
          by simpa [vl_input gs x _ u.isLt] using h⟩
  obtain ⟨hd,andVal⟩ := snoc_and hc (a := l.val) (by omega) hv
  let ds := cs ++ [⟨GateOp.and,[l.val,v]⟩]
  have ld : ds.length = cs.length+1 := by simp [ds]
  obtain ⟨he,orVal⟩ := Clean.ToolSnoc_proof m ds o (m+cs.length) hd (by omega) (by omega)
  have h := Clean.ToolOfClean_proof m _ (m+ds.length) he
  have eq : (fun x => vl (ds ++ [⟨GateOp.or,[o,m+cs.length]⟩]) x (m+ds.length)) =
      fun x => f x || (x l && decide (∃ p ∈ P, x p = true)) := by
    funext x
    rw [(orVal x).1, (andVal x).1, (andVal x).2 o (by omega),
      keep x o ho, ev x,vl_input cs x _ l.isLt,row x]
  rw [eq] at h
  exact h.mono (by simp; omega)

end Onlyfr.PrivateGridCompose
