import PEqualNP.Outside.PrivateReaderDrop

namespace Onlyfr.PrivateArcMarginal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateGateDrop

/-- Two pinned wires can jointly pay for distinct readers, including a
reader that uses both pins, counted once. The pins may have opposite values. -/
theorem two_pin_readers {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (i j : Fin m) (hij : i ≠ j) (b c : Bool)
    (R : Finset ℕ) (read : ∀ r ∈ R, Reads gs r i ∨ Reads gs r j)
    (nc : ∃ x y, f (Function.update (Function.update x j c) i b) ≠
      f (Function.update (Function.update y j c) i b)) :
    ∃ t, t + R.card ≤ gs.length ∧ HasMonoSize m
      (fun x => f (Function.update (Function.update x j c) i b)) t := by
  classical
  let fix (x : Fin m → Bool) := Function.update (Function.update x j c) i b
  let P : Set (Fin m → Bool) := {z | z i = b ∧ z j = c}
  have mem (x) : fix x ∈ P := by
    change (Function.update (Function.update x j c) i b) i = b ∧ (Function.update (Function.update x j c) i b) j = c
    simp [Function.update_of_ne (Ne.symm hij)]
  have alias' (r) (hr : r ∈ R) : ∃ w, w < m+r ∧ ∀ z ∈ P, vl gs z (m+r) = vl gs z w := by
    rcases read r hr with h|h
    · exact Free.alias_of_rd hL.1 hL.2.1 h P b (fun z hz => (vl_input gs z i i.isLt).trans hz.1)
    · exact Free.alias_of_rd hL.1 hL.2.1 h P c (fun z hz => (vl_input gs z j j.isLt).trans hz.2)
  let tgt r := if h : r ∈ R then (alias' r h).choose else 0
  obtain ⟨x,y,hxy⟩ := nc
  obtain ⟨gs',o',hc,hlen,hev⟩ := Free.elimAl Removal.ToolRemoval_proof hL
    ⟨_,_,hxy⟩ P R tgt (by
      intro r hr
      have len : r < gs.length := (read r hr).elim reads_len reads_len
      simpa only [tgt,dif_pos hr] using And.intro len (alias' r hr).choose_spec)
  have eqn (z) : vl gs' (fix z) o' = f (fix z) := hev _ (mem z)
  have n₁ : ∃ u v, vl gs' (Function.update u i b) o' ≠ vl gs' (Function.update v i b) o' := by
    refine ⟨Function.update x j c, Function.update y j c, ?_⟩
    change vl gs' (fix x) o' ≠ vl gs' (fix y) o'
    rwa [eqn,eqn]
  have h₁ := Clean.ToolRestrict_proof m gs' o' i b hc n₁
  have h₂ := restrict_input m gs'.length (fun z => vl gs' (Function.update z i b) o')
    j c h₁ ⟨x,y,by change vl gs' (fix x) o' ≠ vl gs' (fix y) o'; rwa [eqn,eqn]⟩
  exact ⟨gs'.length,hlen,(funext eqn) ▸ h₂⟩

/-- Choose the absorbing value of a gate reading an essential input. Both
that gate and one live successor disappear on this cofactor. -/
theorem expensive_phase {m s : ℕ} {f : (Fin m → Bool) → Bool} (i : Fin m)
    (hd : Dep f i) (hf : HasMonoSize m f s)
    (hnc : ∀ b : Bool, ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b)) :
    ∃ b t, t + 2 ≤ s ∧ HasMonoSize m (fun x => f (Function.update x i b)) t := by
  classical
  obtain ⟨x,y,hxy⟩ := hnc false
  obtain ⟨gs,o,hL,hlen⟩ := Clean.ToolLeast_proof m f s ⟨_,_,hxy⟩ hf
  have hoi : o ≠ (i : ℕ) := by
    intro he
    apply hxy
    rw [← hL.2.2.1, ← hL.2.2.1, he, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨r,hr⟩ := Free.read_of_dep hL.2.2.1 i hd hoi
  obtain ⟨g,hg,hi⟩ := hr
  have hr : Reads gs r i := ⟨g,hg,hi⟩
  obtain ⟨u,v,_,_,hin,hop⟩ := Free.vl_bin hL.1 hL.2.1 hg
  have side : (i : ℕ) = u ∨ (i : ℕ) = v := by simpa [hin] using hi
  have forced : ∃ b : Bool, ∀ z : Fin m → Bool, z i = b → vl gs z (m+r) = b := by
    rcases hop with hand|hor
    · refine ⟨false,fun z hz => ?_⟩
      rw [hand]; rcases side with rfl|rfl <;> simp [vl_input gs z i i.isLt,hz]
    · refine ⟨true,fun z hz => ?_⟩
      rw [hor]; rcases side with rfl|rfl <;> simp [vl_input gs z i i.isLt,hz]
  obtain ⟨b,forced⟩ := forced
  obtain ⟨v,w,hvw⟩ := hnc b
  have hout : o ≠ m+r := by
    intro he
    apply hvw
    rw [← hL.2.2.1, ← hL.2.2.1, he, forced _ (by simp), forced _ (by simp)]
  obtain ⟨j,hj⟩ := Free.live Removal.ToolRemoval_proof hL ⟨_,_,hvw⟩ (reads_len hr) hout
  have ne : r ≠ j := by have := reads_lt hL.1 hj; omega
  obtain ⟨t,ht,hf'⟩ := Onlyfr.PrivateReaderDrop.save_aliases hL i b ⟨v,w,hvw⟩ {r,j} (by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact reads_len hr
    · exact reads_len hj) (by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact ⟨i,reads_lt hL.1 hr, fun z hz => (forced z hz).trans (hz.symm.trans (vl_input gs z i i.isLt).symm)⟩
    · exact Free.alias_of_rd hL.1 hL.2.1 hj {z | z i = b} b forced)
  rw [Finset.card_pair ne] at ht
  exact ⟨b,t,by omega,hf'⟩

/-- Separate the new line bit z and its private point p; core is the
incidence predicate from pairs of surviving lines. -/
def full {J : Type*} (core z p : Prop) (y u x : J → Prop) : Prop :=
  core ∨ (∃ j, y j ∧ (u j ∨ x j)) ∨ (z ∧ (p ∨ ∃ j, x j))

def erased {J : Type*} (core : Prop) (y u x : J → Prop) : Prop :=
  core ∨ ∃ j, y j ∧ (u j ∨ x j)

theorem private_on {J : Type*} (core z : Prop) (y u x : J → Prop) :
    full core z True y u x ↔ z ∨ erased core y u x := by simp [full,erased, or_left_comm, or_comm]

theorem line_off {J : Type*} (core p : Prop) (y u x : J → Prop) :
    full core False p y u x ↔ erased core y u x := by simp [full,erased]

theorem line_on {J : Type*} (core p : Prop) (y u x : J → Prop) :
    full core True p y u x ↔ (core ∨ ∃ j, y j ∧ u j) ∨ (p ∨ ∃ j, x j) := by
  unfold full
  constructor
  · rintro (h|h|h)
    · exact Or.inl (Or.inl h)
    · obtain ⟨j,hj,hu|hx⟩ := h
      · exact Or.inl (Or.inr ⟨j,hj,hu⟩)
      · exact Or.inr (Or.inr ⟨j,hx⟩)
    · exact Or.inr h.2
  · rintro ((h|h)|h)
    · exact Or.inl h
    · obtain ⟨j,hj,hu⟩ := h
      exact Or.inr (Or.inl ⟨j,hj,Or.inl hu⟩)
    · exact Or.inr (Or.inr ⟨trivial,h⟩)

/-- After pinning the deleted line's private point and k incident crossings,
both line cofactors cost at least E-k, where E is the deletion cost. Any
extra savings already obtained from these point pins survive in the marginal. -/
theorem balanced_marginal {m D E k extra s : ℕ} {f : (Fin m → Bool) → Bool}
    (i : Fin m) (hd : Dep f i) (hf : HasMonoSize m f s)
    (pins : s + k + 1 + extra ≤ D)
    (nc : ∀ b : Bool, ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (cofactors : ∀ b t, HasMonoSize m (fun x => f (Function.update x i b)) t → E ≤ t+k) :
    E + 3 + extra ≤ D := by
  obtain ⟨b,t,hs,ht⟩ := expensive_phase i hd hf nc
  have := cofactors b t ht
  omega

end Onlyfr.PrivateArcMarginal
