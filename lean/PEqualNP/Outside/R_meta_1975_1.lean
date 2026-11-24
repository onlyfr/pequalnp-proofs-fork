import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1975_1
  (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ (u v : Fin n), G.Adj u v → u ∉ S) → (∃ u v : Fin n, G.Adj u v) →
    (∀ x : Fin n → Bool, f x = true ↔ (∃ v ∈ S, x v = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = f →
    (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ S,
      let gs := C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ))
      gs.length = 3 ∧ ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    3 * (n - S.card) + S.card ≤ C.size + 1)
  (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
    (∀ v ∉ S, (G.neighborSet v).ncard = 3) → (∀ (u v : Fin n), G.Adj u v → u ∉ S) → (∃ u v : Fin n, G.Adj u v) →
    (∀ x : Fin n → Bool, f x = true ↔ (∃ v ∈ S, x v = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    ∀ v ∉ S, ∃ s : ℕ, s + 7 ≤ 3 * (n - S.card) + S.card ∧
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x v false)) s) :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ v ∉ S, (G.neighborSet v).ncard = 3) → (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ (u v : Fin n), G.Adj u v → u ∉ S) → (∃ u v : Fin n, G.Adj u v) →
    (∀ x : Fin n → Bool, f x = true ↔ (∃ v ∈ S, x v = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = f →
    (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ S,
      let gs := C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ))
      gs.length = 3 ∧ ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    ∃ v ∉ S, ∃ s : ℕ, s + 4 ≤ C.size ∧
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x v false)) s := by
  intro n G S f C hdeg _hgirth hiso hedge hfun hfan heq hmin hreads
  have hl := h1 n G S f C hiso hedge hfun hfan heq hmin hreads
  obtain ⟨v, w, hvw⟩ := hedge
  have hv := hiso v w hvw
  obtain ⟨s, hs, hc⟩ := h2 n G S f hdeg hiso ⟨v, w, hvw⟩ hfun v hv
  exact ⟨v, hv, s, by omega, hc⟩
