import PEqualNP.Outside.PrivateTwoGateDrop

namespace Onlyfr.PrivateGeneralDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateTwoGateDrop

/-- Every gate of H loses all its uses when the AND gate r is bypassed. -/
theorem save_exclusive_block {m : ℕ} {gs : List Gate} {o r : ℕ} {f : (Fin m → Bool) → Bool}
    (hL : MLeast m f gs o) (i : Fin m) {g : Gate} (hg : gs[r]? = some g)
    (hop : g.op = .and) (hi : (i : ℕ) ∈ g.inputs) (H : Finset ℕ)
    (hbefore : ∀ d ∈ H, d < r)
    (huses : ∀ d ∈ H, ∀ j, Reads gs j (m+d) → j ∈ insert r H)
    (hnc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false)) :
    ∃ t, t + H.card + 1 ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i false)) t := by
  classical
  obtain ⟨x,y,hxy⟩ := hnc
  have hr : Reads gs r i := ⟨g,hg,hi⟩
  have hrlen := reads_len hr
  have hrH : r ∉ H := fun h => (Nat.lt_irrefl r) (hbefore r h)
  have hout (d) (hd : d ∈ H) : o ≠ m+d := by
    intro he
    let last := gs.length-1
    have hb := hbefore d hd
    have hlast : last < gs.length := by dsimp [last]; omega
    have hne : o ≠ m+last := by dsimp [last]; omega
    obtain ⟨j,hj⟩ := Free.live Removal.ToolRemoval_proof hL ⟨_,_,hxy⟩ hlast hne
    have h1 := reads_lt hL.1 hj
    have h2 := reads_len hj
    dsimp [last] at h1
    omega
  let P : Set (Fin m → Bool) := {z | z i = false}
  let tgt (j : ℕ) : Option ℕ := if j = r then some i.val else none
  have rem : Removable m gs o P (insert r H) tgt := by
    intro j hj
    rcases Finset.mem_insert.mp hj with h | h
    · subst j
      refine ⟨hrlen,Or.inl ⟨i,by simp [tgt],reads_lt hL.1 hr,?_⟩⟩
      intro z hz
      obtain ⟨a,b,_,_,hin,_⟩ := Free.vl_bin hL.1 hL.2.1 hg
      have hw : (i : ℕ) = a ∨ (i : ℕ) = b := by simpa [hin] using hi
      have hh : z i = false := hz
      rw [vl_gate gs hL.1 z r g hg,hop,hin]
      rcases hw with rfl | rfl <;> simp [GateOp.eval, vl_input gs z i i.isLt, hh]
    · have hb := hbefore j h
      refine ⟨by omega,Or.inr ⟨by simp [tgt, Nat.ne_of_lt hb],hout j h,huses j h,?_⟩⟩
      intro v _
      have hh : i.val ≠ m+j := by have := i.isLt; omega
      by_cases he : v = r <;> simp [tgt,he,hh]
  obtain ⟨gs',map,hc,hnf,hlen,_,hval⟩ := Removal.ToolRemoval_proof m gs o P (insert r H) tgt hL.1 rem
  have hh := hval o (Free.out_lt hL.2.2.1 ⟨_,_,hxy⟩) (by
    intro d hd ht
    rcases Finset.mem_insert.mp hd with he | he
    · simp [tgt,he] at ht
    · exact hout d he)
  have heq : (fun z => vl gs' (Function.update z i false) (map o)) =
      (fun z => f (Function.update z i false)) := by
    funext z
    exact (hh.2 _ (Function.update_self i false z)).trans (hL.2.2.1 _)
  have hres := Clean.ToolRestrict_proof m gs' (map o) i false ⟨hc,hnf hL.2.1⟩
    ⟨x,y,by change (fun z => vl gs' (Function.update z i false) (map o)) x ≠
                     (fun z => vl gs' (Function.update z i false) (map o)) y; rw [heq]; exact hxy⟩
  rw [Finset.card_insert_of_notMem hrH] at hlen
  exact ⟨gs'.length,by omega,heq ▸ hres⟩

/-- Count distinct input wires read within a block without assuming it is a tree. -/
theorem inputs_le_twice {m : ℕ} {gs : List Gate} (hc : MClean m gs) (H W : Finset ℕ)
    (hread : ∀ w ∈ W, ∃ d ∈ H, Reads gs d w) : W.card ≤ 2 * H.card := by
  classical
  let ws (d : ℕ) := ((gs[d]?).map (fun g => g.inputs.toFinset)).getD ∅
  have hsub : W ⊆ H.biUnion ws := by
    intro w hw
    obtain ⟨d,hd,g,hg,hin⟩ := hread w hw
    exact Finset.mem_biUnion.mpr ⟨d,hd,by simpa [ws,hg] using hin⟩
  have hb (d : ℕ) : (ws d).card ≤ 2 := by
    cases hg : gs[d]? with
    | none => simp [ws,hg]
    | some g =>
      obtain ⟨a,b,_,_,hin,_⟩ := Free.vl_bin hc.1 hc.2 hg
      have hcount : ([a,b] : List ℕ).toFinset.card ≤ 2 := by
        simpa using (List.toFinset_card_le (l := [a,b]))
      simpa [ws,hg,hin] using hcount
  calc
    W.card ≤ (H.biUnion ws).card := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ H, (ws d).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ H, 2 := Finset.sum_le_sum (fun d _ => hb d)
    _ = _ := by simp [Nat.mul_comm]

/-- A block with enough distinct point inputs gives the full deletion
inequality at every order, even when those points lie on other lines. -/
theorem hdrop_of_exclusive_inputs {n q : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (D : Circuit) {gs : List Gate} {o r : ℕ} (hL : MLeast (n+n) (edgeFun I S) gs o)
    (hsize : gs.length ≤ D.size) (l : Fin n) (hl : l ∈ S)
    (hother : ∃ a ∈ S.erase l, ∃ p, I p a)
    {g : Gate} (hg : gs[r]? = some g) (hop : g.op = .and) (hi : (Fin.natAdd n l : ℕ) ∈ g.inputs)
    (H : Finset ℕ) (hbefore : ∀ d ∈ H, d < r)
    (huses : ∀ d ∈ H, ∀ j, Reads gs j (n+n+d) → j ∈ insert r H)
    (W : Finset (Fin n)) (hload : q ≤ 50*W.card)
    (hread : ∀ p ∈ W, ∃ d ∈ H, Reads gs d (Fin.castAdd n p)) :
    ∃ removed ∈ S, ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase removed ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      100*E.size + q ≤ 100*D.size := by
  classical
  let ws : Fin n → ℕ := fun p => (Fin.castAdd n p).val
  have hinj : Function.Injective ws := by intro p t h; exact Fin.ext h
  have hc := inputs_le_twice ⟨hL.1,hL.2.1⟩ H (W.image ws) (by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    exact hread p hp)
  rw [Finset.card_image_of_injective _ hinj] at hc
  obtain ⟨a,ha,p,hp⟩ := hother
  have hnc : ∃ x y, edgeFun I S (Function.update x (Fin.natAdd n l) false) ≠
      edgeFun I S (Function.update y (Fin.natAdd n l) false) := by
    refine ⟨pairInput p a,fun _ => false,?_⟩
    rw [erase_eq,erase_eq,(Onlyfr.PrivateOrReader.pair_edge_iff I _ p a).mpr ⟨ha,hp⟩,edgeFun_zero]
    decide
  obtain ⟨t,ht,hf⟩ := save_exclusive_block hL (Fin.natAdd n l) hg hop hi H hbefore huses hnc
  obtain ⟨E,hE,hs,hev⟩ := monotone2_of_has hf
  exact ⟨l,hl,E,hE,fun x => by rw [hev,erase_eq,edgeFun_true],by omega⟩

/-- A low upper bound at S, together with a uniform lower bound at a
smaller layer, forces a failed deletion somewhere above that layer. -/
theorem deficit_witness {α : Type*} [DecidableEq α] (cost : Finset α → ℕ)
    (S : Finset α) (b k L : ℕ) (hb : b ≤ S.card)
    (hbase : ∀ T ⊆ S, T.card = b → L ≤ cost T)
    (hcheap : cost S < L + k * (S.card-b)) :
    ∃ T ⊆ S, b < T.card ∧ ∀ l ∈ T, cost T < cost (T.erase l) + k := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases he : S.card = b
    · have := hbase S (Finset.Subset.refl _) he
      rw [he,Nat.sub_self,Nat.mul_zero,Nat.add_zero] at hcheap
      omega
    by_cases bad : ∀ l ∈ S, cost S < cost (S.erase l)+k
    · exact ⟨S,Finset.Subset.refl _,by omega,bad⟩
    push_neg at bad
    obtain ⟨l,hl,hs⟩ := bad
    have hc := Finset.card_erase_of_mem hl
    have hbe : b ≤ (S.erase l).card := by omega
    have hdiff : S.card-b = ((S.erase l).card-b)+1 := by omega
    rw [hdiff,Nat.mul_add,Nat.mul_one] at hcheap
    obtain ⟨T,hT,hcard,hfail⟩ := ih (S.erase l) (Finset.erase_ssubset hl) hbe
      (fun T hT ht => hbase T (hT.trans (Finset.erase_subset _ _)) ht) (by omega)
    exact ⟨T,hT.trans (Finset.erase_subset _ _),hcard,hfail⟩

end Onlyfr.PrivateGeneralDrop
