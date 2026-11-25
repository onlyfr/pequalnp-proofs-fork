import Mathlib

namespace Onlyfr.PrivateFanoutBudget

/-- At most three monotone Boolean functions can cross a one-wire interface:
false, the wire itself, and true. Include the all-off probe among the probes. -/
theorem segment_capacity {A Y : Type*} [Fintype A]
    (localFn : Option A → Bool → Bool) (mono : ∀ a, Monotone (localFn a))
    (input : Y → Bool) (observe : Y → Bool → Bool)
    (separate : Function.Injective (fun a y => observe y (localFn a (input y)))) :
    Fintype.card A ≤ 2 := by
  classical
  let code (a : Option A) : Fin 3 :=
    if localFn a false then 2 else if localFn a true then 1 else 0
  have inj : Function.Injective code := by
    intro a b he
    apply separate
    have eq : localFn a = localFn b := by
      have ha := mono a (show false ≤ true by decide)
      have hb := mono b (show false ≤ true by decide)
      simp only [code] at he
      funext z
      cases h₁ : localFn a false <;> cases h₂ : localFn a true <;>
        cases h₃ : localFn b false <;> cases h₄ : localFn b true <;>
        cases z <;> simp_all <;> first | exact (by decide : ¬ (true ≤ false)) ha | exact (by decide : ¬ (true ≤ false)) hb
    simp only [eq]
  have h := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_option, Fintype.card_fin] at h
  omega

inductive Shape where
  | point
  | port
  | join (left right : Shape)

def ports : Shape → ℕ
  | .point => 0
  | .port => 1
  | .join l r => ports l + ports r

/-- Branch points of the minimal subtree spanning the ports and the root. -/
def forks : Shape → ℕ
  | .point | .port => 0
  | .join l r => forks l + forks r + if 0 < ports l ∧ 0 < ports r then 1 else 0

theorem forks_count (t : Shape) : forks t = ports t - 1 := by
  induction t with
  | point | port => rfl
  | join l r hl hr =>
    simp only [ports, forks, hl, hr]
    split <;> omega

/-- A component with ports has one chain per port or fork. A portless tree
has a single Boolean output and hence at most one distinguishable point. -/
theorem component_budget (t : Shape) (p : ℕ)
    (pure : ports t = 0 → p ≤ 1)
    (mixed : 0 < ports t → p ≤ 2 * (ports t + forks t)) :
    p ≤ 4 * ports t + 1 := by
  have := forks_count t
  by_cases h : ports t = 0
  · have := pure h; omega
  · have := mixed (by omega); omega

theorem forest_budget {A : Type*} (components : Finset A) (t : A → Shape)
    (p : A → ℕ) (m r : ℕ)
    (capacities : ∀ i ∈ components, p i ≤ 4 * ports (t i) + 1)
    (wireCount : ∑ i ∈ components, ports (t i) ≤ m + 2*r)
    (rootCount : components.card ≤ r+1) :
    ∑ i ∈ components, p i ≤ 4*m + 9*r + 1 := by
  have h := Finset.sum_le_sum capacities
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    smul_eq_mul, mul_one] at h
  omega

theorem full_arc_budget (s r : ℕ)
    (binary : s = 511564 + r) (distinctPoints : 510555 ≤ 4*1010 + 9*r + 1) :
    567844 ≤ s := by omega

/-- One-hot line tests already distinguish the all-off probe and every
singleton point probe: their supports are the empty set, singletons and pairs. -/
theorem support_probe_injective {L : Type*} [DecidableEq L] :
    Function.Injective (fun (U : Finset L) (l : L) => decide (l ∈ U)) := by
  intro U V h
  ext l
  have he := congrFun h l
  simpa using he

/-- The support family for all lines of the arc, including the empty probe. -/
theorem probe_count (s : Finset (Fin 1010)) (hs : s = Finset.univ) :
    ((s.powersetCard 0 ∪ s.powersetCard 1) ∪ s.powersetCard 2).card = 510556 := by
  subst s
  have dis (i j : ℕ) (h : i ≠ j) :
      Disjoint ((Finset.univ : Finset (Fin 1010)).powersetCard i) (Finset.univ.powersetCard j) := by
    apply Finset.disjoint_left.mpr
    intro U hi hj
    exact h ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dis 0 2 (by decide), dis 1 2 (by decide)⟩),
    Finset.card_union_of_disjoint (dis 0 1 (by decide))]
  norm_num [Finset.card_powersetCard,Nat.choose_two_right]

end Onlyfr.PrivateFanoutBudget
