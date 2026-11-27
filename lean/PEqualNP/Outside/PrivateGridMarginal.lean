import PEqualNP.Outside.PrivateReaderDrop

namespace Onlyfr.PrivateGridMarginal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc Onlyfr.PrivateReaderDrop

/-- A one-gate marginal for pinning an input low rules out both fanout and
an AND reader in every minimum clean circuit. -/
theorem rigid_reader {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (i : Fin m)
    (hnc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false))
    (tight : ∀ t, HasMonoSize m (fun x => f (Function.update x i false)) t → gs.length ≤ t+1) :
    (∀ r j, Reads gs r i → Reads gs j i → r = j) ∧
    (∀ (r : ℕ) (g : Gate), gs[r]? = some g → (i : ℕ) ∈ g.inputs → g.op ≠ .and) := by
  classical
  constructor
  · intro r j hr hj
    by_contra ne
    obtain ⟨t,ht,hf⟩ := save_readers hL i false hnc {r,j} (by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hr
      · exact hj)
    rw [Finset.card_pair ne] at ht
    have := tight t hf
    omega
  · intro r g hg hi hop
    obtain ⟨t,ht,hf⟩ := save_and_reader hL i hg hop hi hnc
    have := tight t hf
    omega

/-- A row's crossing costs have unit lower increments. Equality at the
end forces a unit increment at every intermediate step. -/
theorem tight_path (D : ℕ → ℕ) (n : ℕ)
    (step : ∀ k < n, D k + 1 ≤ D (k+1)) :
    D n = D 0 + n ↔ ∀ k < n, D (k+1) = D k + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun k hk => step k (by omega))
    have lower (j : ℕ) (hj : j ≤ n+1) : D 0 + j ≤ D j := by
      induction j with
      | zero => simp
      | succ j rec =>
        have := rec (by omega)
        have := step j (by omega)
        omega
    constructor
    · intro eq k hk
      have := lower n (by omega)
      have := step n (by omega)
      have en : D n = D 0 + n := by omega
      by_cases h : k = n
      · subst k; omega
      · exact prev.mp en k (by omega)
    · intro all
      have := prev.mpr (fun k hk => all k (by omega))
      have := all n (by omega)
      omega
end Onlyfr.PrivateGridMarginal
