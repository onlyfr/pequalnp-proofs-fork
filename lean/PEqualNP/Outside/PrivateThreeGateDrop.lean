import PEqualNP.Outside.PrivateTwoGateDrop

namespace Onlyfr.PrivateThreeGateDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateReaderDrop Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateTwoGateDrop

/-- Wires reached from the selected input by following only AND gates. -/
inductive AndPath (m : ℕ) (gs : List Gate) (i : Fin m) : ℕ → Prop where
  | input : AndPath m gs i i
  | step {w r : ℕ} {g : Gate} : AndPath m gs i w → gs[r]? = some g →
      g.op = .and → w ∈ g.inputs → AndPath m gs i (m+r)

theorem AndPath.zero {m gs i w} (h : AndPath m gs i w) (hc : MClean m gs)
    (x : Fin m → Bool) (hx : x i = false) : vl gs x w = false := by
  induction h with
  | input => rw [vl_input gs x i i.isLt]; exact hx
  | @step w r g _ hg hand hw ih =>
    obtain ⟨a,b,_,_,hin,_⟩ := Free.vl_bin hc.1 hc.2 hg
    rw [vl_gate gs hc.1 x r g hg,hand,hin]
    have he : w = a ∨ w = b := by simpa [hin] using hw
    rcases he with rfl | rfl <;> simp [GateOp.eval, ih]

/-- Count distinct readers even when several AND paths lead to the same gate. -/
theorem save_path_readers {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hL : MLeast m f gs o) (i : Fin m)
    (hnc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false))
    (R : Finset ℕ) (hR : ∀ j ∈ R, ∃ w, AndPath m gs i w ∧ Reads gs j w) :
    ∃ t, t + R.card ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i false)) t := by
  apply save_aliases hL i false hnc R
  · intro j hj
    obtain ⟨_,_,hr⟩ := hR j hj
    exact reads_len hr
  · intro j hj
    obtain ⟨w,hw,hr⟩ := hR j hj
    exact Free.alias_of_rd hL.1 hL.2.1 hr {x | x i = false} false
      (fun x hx => hw.zero ⟨hL.1,hL.2.1⟩ x hx)

/-- A structural certificate for the required inequality, for any q. -/
theorem hdrop_of_readers {n q : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (D : Circuit) {gs : List Gate} {o : ℕ} (hL : MLeast (n+n) (edgeFun I S) gs o)
    (hsize : gs.length ≤ D.size) (l : Fin n) (hl : l ∈ S)
    (hother : ∃ a ∈ S.erase l, ∃ p, I p a) (R : Finset ℕ) (hq : q ≤ 100 * R.card)
    (hR : ∀ j ∈ R, ∃ w, AndPath (n+n) gs (Fin.natAdd n l) w ∧ Reads gs j w) :
    ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase l ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      100 * E.size + q ≤ 100 * D.size := by
  obtain ⟨a,ha,p,hp⟩ := hother
  have hnc : ∃ x y, edgeFun I S (Function.update x (Fin.natAdd n l) false) ≠
      edgeFun I S (Function.update y (Fin.natAdd n l) false) := by
    refine ⟨pairInput p a,fun _ => false,?_⟩
    rw [erase_eq,erase_eq,(Onlyfr.PrivateOrReader.pair_edge_iff I _ p a).mpr ⟨ha,hp⟩,edgeFun_zero]
    decide
  obtain ⟨t,ht,hf⟩ := save_path_readers hL _ hnc R hR
  obtain ⟨E,hE,hs,hev⟩ := monotone2_of_has hf
  exact ⟨E,hE,fun x => by rw [hev,erase_eq,edgeFun_true],by omega⟩

end Onlyfr.PrivateThreeGateDrop
