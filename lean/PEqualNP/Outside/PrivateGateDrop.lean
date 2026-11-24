import PEqualNP.MetaComplexity.Helpers.LocClean
import PEqualNP.MetaComplexity.Helpers.LocRemoval
import PEqualNP.MetaComplexity.Helpers.LocFree

namespace Onlyfr.PrivateGateDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc

theorem one_input (m s : ℕ) (f : (Fin m → Bool) → Bool)
    (i : Fin m) (b : Bool) (h : HasMonoSize m f s)
    (hd : Dep f i)
    (hnc : ∃ x y : Fin m → Bool, f (Function.update x i b) ≠ f (Function.update y i b)) :
    ∃ t, t + 1 ≤ s ∧ HasMonoSize m (fun x => f (Function.update x i b)) t := by
  classical
  have hnc0 : ∃ x y : Fin m → Bool, f x ≠ f y := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨_, _, hxy⟩
  obtain ⟨gs, o, hleast, hlen⟩ := Clean.ToolLeast_proof m f s hnc0 h
  have hoi : o ≠ (i : ℕ) := by
    intro he
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hleast.2.2.1, ← hleast.2.2.1, he,
      vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨p, hread⟩ := Free.read_of_dep hleast.2.2.1 i hd hoi
  obtain ⟨a, ha, hval⟩ := Free.alias_of_rd hleast.1 hleast.2.1 hread
    {x : Fin m → Bool | x i = b} b (by intro x hx; rw [vl_input gs x i i.isLt]; exact hx)
  have hp : p < gs.length := by
    obtain ⟨g, hg, _⟩ := hread
    exact List.getElem?_eq_some_iff.mp hg |>.1
  obtain ⟨gs', o', hc', hsave, hev⟩ := Free.elimAl Removal.ToolRemoval_proof
    hleast hnc0 {x : Fin m → Bool | x i = b} {p} (fun _ => a) (by
      intro j hj
      have he : j = p := Finset.mem_singleton.mp hj
      subst j
      exact ⟨hp, ha, hval⟩)
  have hnc' : ∃ x y : Fin m → Bool,
      vl gs' (Function.update x i b) o' ≠ vl gs' (Function.update y i b) o' := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨x, y, ?_⟩
    rw [hev _ (by simp), hev _ (by simp)]
    exact hxy
  have hres := Clean.ToolRestrict_proof m gs' o' i b hc' hnc'
  have heq : (fun x => vl gs' (Function.update x i b) o') =
      fun x => f (Function.update x i b) := by
    funext x
    exact hev _ (by simp)
  rw [heq] at hres
  refine ⟨gs'.length, ?_, hres⟩
  simp only [Finset.card_singleton] at hsave
  omega

theorem restrict_input (m s : ℕ) (f : (Fin m → Bool) → Bool)
    (i : Fin m) (b : Bool) (h : HasMonoSize m f s)
    (hnc : ∃ x y : Fin m → Bool, f (Function.update x i b) ≠ f (Function.update y i b)) :
    HasMonoSize m (fun x => f (Function.update x i b)) s := by
  obtain ⟨x, y, hxy⟩ := hnc
  obtain ⟨gs, o, hcl, hnf, hlen, hev⟩ := Clean.mclean_of m f s ⟨_, _, hxy⟩ h
  have hres := Clean.ToolRestrict_proof m gs o i b ⟨hcl, hnf⟩
    ⟨x, y, by rw [hev, hev]; exact hxy⟩
  have heq : (fun x => vl gs (Function.update x i b) o) =
      fun x => f (Function.update x i b) := funext fun x => hev _
  rw [heq] at hres
  exact hres.mono hlen

def pin {m : ℕ} (A : Finset (Fin m)) (x : Fin m → Bool) : Fin m → Bool :=
  fun i => if i ∈ A then false else x i

theorem pin_empty {m : ℕ} (x : Fin m → Bool) : pin ∅ x = x := by
  funext i
  simp [pin]

theorem pin_insert {m : ℕ} (i : Fin m) (A : Finset (Fin m)) (x : Fin m → Bool) :
    pin (insert i A) x = Function.update (pin A x) i false := by
  funext j
  by_cases h : j = i
  · subst j; simp [pin]
  · simp [pin, h, Function.update_of_ne h]

theorem pin_update {m : ℕ} (i : Fin m) (A : Finset (Fin m)) (x : Fin m → Bool) :
    pin A (Function.update x i false) = pin (insert i A) x := by
  funext j
  by_cases h : j = i
  · subst j; simp [pin]
  · simp [pin, h, Function.update_of_ne h]

theorem many_inputs {m : ℕ} (P : Finset (Fin m)) :
    ∀ (f : (Fin m → Bool) → Bool) (s : ℕ), HasMonoSize m f s →
    (∀ A ⊆ P, ∃ x y : Fin m → Bool, f (pin A x) ≠ f (pin A y)) →
    (∀ A ⊆ P, ∀ i ∈ P \ A, Dep (fun x => f (pin A x)) i) →
    ∃ t, t + P.card ≤ s ∧ HasMonoSize m (fun x => f (pin P x)) t := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      intro f s h _ _
      refine ⟨s, by simp, ?_⟩
      simpa only [pin_empty] using h
  | @insert i P hi ih =>
      intro f s h hnc hdep
      have hd : Dep f i := by
        simpa only [pin_empty] using hdep ∅ (by simp) i (by simp)
      have hn : ∃ x y : Fin m → Bool,
          f (Function.update x i false) ≠ f (Function.update y i false) := by
        simpa only [pin_insert, pin_empty] using hnc (insert i ∅) (by simp)
      obtain ⟨s', hs', hf'⟩ := one_input m s f i false h hd hn
      have hnc' : ∀ A ⊆ P, ∃ x y : Fin m → Bool,
          (fun x => f (Function.update x i false)) (pin A x) ≠
          (fun x => f (Function.update x i false)) (pin A y) := by
        intro A hA
        simpa only [← pin_insert] using hnc (insert i A) (Finset.insert_subset_insert i hA)
      have hdep' : ∀ A ⊆ P, ∀ j ∈ P \ A,
          Dep (fun x => (fun x => f (Function.update x i false)) (pin A x)) j := by
        intro A hA j hj
        have hjP := (Finset.mem_sdiff.mp hj).1
        have hjA := (Finset.mem_sdiff.mp hj).2
        have hji : j ≠ i := by intro he; subst j; exact hi hjP
        have hh := hdep (insert i A) (Finset.insert_subset_insert i hA) j
          (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hjP, by simp [hji, hjA]⟩)
        simpa only [← pin_insert] using hh
      obtain ⟨t, ht, hf⟩ := ih (fun x => f (Function.update x i false)) s' hf' hnc' hdep'
      refine ⟨t, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hi]
        omega
      · simpa only [← pin_insert] using hf

end Onlyfr.PrivateGateDrop

