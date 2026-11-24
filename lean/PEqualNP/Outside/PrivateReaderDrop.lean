import PEqualNP.Outside.PrivateGateDrop

namespace Onlyfr.PrivateReaderDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc

/-- Every distinct gate reading an input that is fixed becomes removable,
even when one selected gate feeds another. -/
theorem save_readers {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (i : Fin m) (b : Bool)
    (hnc : ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b))
    (R : Finset ℕ) (hR : ∀ r ∈ R, Reads gs r i) :
    ∃ t, t + R.card ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i b)) t := by
  classical
  obtain ⟨x, y, hxy⟩ := hnc
  let P : Set (Fin m → Bool) := {z | z i = b}
  have hval (z) (hz : z ∈ P) : vl gs z i = b := by
    rw [vl_input gs z i i.isLt]
    exact hz
  have hal (r) (hr : r ∈ R) := Free.alias_of_rd hL.1 hL.2.1 (hR r hr) P b hval
  let tgt (r : ℕ) := if hr : r ∈ R then (hal r hr).choose else 0
  obtain ⟨gs', o', hc, hs, hev⟩ := Free.elimAl Removal.ToolRemoval_proof hL
    ⟨_, _, hxy⟩ P R tgt (by
      intro r hr
      refine ⟨reads_len (hR r hr), ?_⟩
      simpa only [tgt, dif_pos hr] using (hal r hr).choose_spec)
  have heq : (fun z => vl gs' (Function.update z i b) o') =
      fun z => f (Function.update z i b) := by
    funext z
    exact hev _ (Function.update_self i b z)
  have hres := Clean.ToolRestrict_proof m gs' o' i b hc
    ⟨x, y, by change (fun z => vl gs' (Function.update z i b) o') x ≠ (fun z => vl gs' (Function.update z i b) o') y; rw [heq]; exact hxy⟩
  exact ⟨gs'.length, hs, heq ▸ hres⟩

end Onlyfr.PrivateReaderDrop
