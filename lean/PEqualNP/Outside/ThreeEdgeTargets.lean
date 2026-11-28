import PEqualNP.Outside.ThreeEdgeTypes
import PEqualNP.MetaComplexity.L106

namespace Onlyfr.ThreeEdgeProjection
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

def vertex (c : Fin 4) : Fin 7 := ⟨2*c.val,by omega⟩
def mid (i : Fin 3) : Fin 7 := ⟨2*i.val+1,by omega⟩

def target (s : Bool) (x : Fin 7 → Bool) : Bool := decide (∃ i,
  x (mid i) = true ∧ (x (vertex (colors s i).1) = true ∨ x (vertex (colors s i).2) = true))

private def tree := SimpleGraph.fromRel (fun a b : Fin 7 =>
  ∃ i, a = mid i ∧ (b = vertex (colors true i).1 ∨ b = vertex (colors true i).2))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem target_lower (s : Bool) {t : ℕ} (h : HasCircuitSize 7 (target s) t) : 8 ≤ t := by
  cases s
  · let wrap (v : Fin 7) : Fin 6 := ⟨v.val % 6,by omega⟩
    have proj := PermInputs.relabel_size wrap _ _ h
    let cyc (x : Fin 6 → Bool) := decide (∃ i j : Fin 6, (i.val+1)%6 = j.val ∧ x i = true ∧ x j = true)
    have eq : (fun x => target false (x ∘ wrap)) = cyc := by
      funext x
      exact (by decide : ∀ x, target false (x ∘ wrap) = cyc x) x
    rw [eq] at proj
    have := (L106 6 t (by decide)).mp proj
    omega
  · let rank (v : Fin 7) := if v = 6 then 0 else if v.val%2=1 then 1 else 2
    let : DecidableRel tree.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)
    have ac := Onlyfr.PrivateForestLift.acyclic_of_unique_lower tree rank (by decide)
    have eq : (fun x : Fin 7 → Bool => decide (∃ i j, tree.Adj i j ∧ x i = true ∧ x j = true)) = target true := by
      funext x
      exact (by decide : ∀ x : Fin 7 → Bool, decide (∃ i j, tree.Adj i j ∧ x i = true ∧ x j = true) = target true x) x
    have cov : ∀ T : Finset (Fin 7), (∀ i j, tree.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by decide
    have bound := Forest.forest_bound 7 3 t tree ac ⟨1,0,by decide⟩ cov (eq.symm ▸ h)
    have edges : tree.edgeFinset.card = 6 := by decide
    omega

end Onlyfr.ThreeEdgeProjection
