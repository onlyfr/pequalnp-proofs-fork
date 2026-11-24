import PEqualNP.Outside.PrivateGateDrop

namespace Onlyfr.PrivateReaderDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc

private theorem save_aliases {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (i : Fin m) (b : Bool)
    (hnc : ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (R : Finset ℕ) (hlen : ∀ r ∈ R, r < gs.length)
    (hal : ∀ r ∈ R, ∃ t, t < m + r ∧ ∀ x : Fin m → Bool, x i = b →
      vl gs x (m+r) = vl gs x t) :
    ∃ t, t + R.card ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i b)) t := by
  classical
  obtain ⟨x, y, hxy⟩ := hnc
  let P : Set (Fin m → Bool) := {z | z i = b}
  let tgt (r : ℕ) := if hr : r ∈ R then (hal r hr).choose else 0
  obtain ⟨gs', o', hc, hs, hev⟩ := Free.elimAl Removal.ToolRemoval_proof hL
    ⟨_, _, hxy⟩ P R tgt (by
      intro r hr
      refine ⟨hlen r hr, ?_⟩
      have ht : tgt r = (hal r hr).choose := dif_pos hr
      rw [ht]
      exact ⟨(hal r hr).choose_spec.1, fun z hz => (hal r hr).choose_spec.2 z hz⟩)
  have heq : (fun z => vl gs' (Function.update z i b) o') =
      fun z => f (Function.update z i b) := by
    funext z
    exact hev _ (Function.update_self i b z)
  have hres := Clean.ToolRestrict_proof m gs' o' i b hc
    ⟨x, y, by change (fun z => vl gs' (Function.update z i b) o') x ≠ (fun z => vl gs' (Function.update z i b) o') y; rw [heq]; exact hxy⟩
  exact ⟨gs'.length, hs, heq ▸ hres⟩

/-- Every distinct gate reading an input that is fixed becomes removable,
even when one selected gate feeds another. -/
theorem save_readers {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (i : Fin m) (b : Bool)
    (hnc : ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (R : Finset ℕ) (hR : ∀ r ∈ R, Reads gs r i) :
    ∃ t, t + R.card ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i b)) t := by
  apply save_aliases hL i b hnc R (fun r hr => reads_len (hR r hr))
  intro r hr
  apply Free.alias_of_rd hL.1 hL.2.1 (hR r hr) {z | z i = b} b
  intro x hx
  rw [vl_input gs x i i.isLt]
  exact hx

/-- A direct AND reader and a live successor both disappear when its input is set false. -/
theorem save_and_reader {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o r : ℕ}
    (hL : MLeast m f gs o) (i : Fin m) {g : Gate} (hg : gs[r]? = some g)
    (hop : g.op = .and) (hi : (i : ℕ) ∈ g.inputs)
    (hnc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false)) :
    ∃ t, t + 2 ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i false)) t := by
  classical
  obtain ⟨x, y, hxy⟩ := hnc
  have hr : Reads gs r i := ⟨g, hg, hi⟩
  have hz (z : Fin m → Bool) (hi0 : z i = false) : vl gs z (m+r) = false := by
    obtain ⟨a, b, _, _, hin, _⟩ := Free.vl_bin hL.1 hL.2.1 hg
    rw [vl_gate gs hL.1 z r g hg, hop, hin]
    have hw : (i : ℕ) = a ∨ (i : ℕ) = b := by simpa [hin] using hi
    rcases hw with rfl | rfl <;> simp [GateOp.eval, vl_input gs z i i.isLt, hi0]
  have ho : o ≠ m+r := by
    intro he
    apply hxy
    rw [← hL.2.2.1, ← hL.2.2.1, he, hz _ (by simp), hz _ (by simp)]
  obtain ⟨u, hu⟩ := Free.live Removal.ToolRemoval_proof hL ⟨_, _, hxy⟩ (reads_len hr) ho
  have hru : r ≠ u := by have := reads_lt hL.1 hu; omega
  let R : Finset ℕ := {r,u}
  have hR (j) (hj : j ∈ R) : j = r ∨ j = u := by simpa [R] using hj
  have hc : R.card = 2 := Finset.card_pair hru
  rw [← hc]
  apply save_aliases hL i false ⟨x,y,hxy⟩ R
  · intro j hj
    rcases hR j hj with rfl | rfl
    · exact reads_len hr
    · exact reads_len hu
  · intro j hj
    rcases hR j hj with rfl | rfl
    · exact ⟨i, reads_lt hL.1 hr, fun z h => by rw [hz z h, vl_input gs z i i.isLt, h]⟩
    · exact Free.alias_of_rd hL.1 hL.2.1 hu {z | z i = false} false hz

end Onlyfr.PrivateReaderDrop