import Mathlib

namespace Onlyfr.PrivateGridAverage

set_option exponentiation.threshold 1002
set_option maxRecDepth 4096
abbrev Line := Fin 1001
def cuts := (Finset.univ : Finset Line).powerset
def countHit (A : Finset Line) := (cuts.filter (fun D => (A ∩ D).Nonempty)).card

theorem countHit_eq (A : Finset Line) :
    countHit A + 2^(1001-A.card) = 2^1001 := by
  classical
  have missing : cuts \ cuts.filter (fun D => (A ∩ D).Nonempty) =
      ((Finset.univ : Finset Line) \ A).powerset := by
    ext D
    simp only [cuts,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_powerset,
      Finset.Nonempty,Finset.mem_inter]
    grind
  have h := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset
    (fun D => (A ∩ D).Nonempty) cuts)
  rw [missing] at h
  simpa [cuts,countHit,Nat.add_comm,Finset.card_sdiff_of_subset (Finset.subset_univ A)] using h

private theorem hit_single (j : Line) : countHit {j} = 2^1000 := by
  have h := countHit_eq {j}
  simp only [Finset.card_singleton] at h
  omega

private theorem hit_bounds (A : Finset Line) (k : ℕ) (hk : k ≤ A.card) :
    2^1001 ≤ countHit A + 2^(1001-k) := by
  have h := countHit_eq A
  have le : 1001-A.card ≤ 1001-k := Nat.sub_le_sub_left hk _
  have := Nat.pow_le_pow_right (by decide : 0 < 2) le
  omega

/-- Total tap cost over all cuts, with the sum grouped by partner. -/
theorem group_sum {G : Type*} (groups : Finset G) (w : G → ℕ) (touch : G → Finset Line) :
    (∑ D ∈ cuts, ∑ g ∈ groups, if (touch g ∩ D).Nonempty then w g else 0) =
      ∑ g ∈ groups, countHit (touch g) * w g := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.sum_filter]
  simp [countHit]

/-- Count a list of matched crossings on every cut without requiring their
line coordinates to be independent or distinct. -/
theorem matched_sum {J : Type*} (matched : Finset J) (line : J → Line) :
    (∑ D ∈ cuts, (matched.filter (fun i => line i ∈ D)).card) =
      matched.card * 2^1000 := by
  classical
  have h := group_sum matched (fun _ => 1) (fun i => {line i})
  have single (a : Line) (D : Finset Line) : (({a} : Finset Line) ∩ D).Nonempty ↔ a ∈ D := by
    simp only [Finset.Nonempty,Finset.mem_inter,Finset.mem_singleton,exists_eq_left]
  simp only [single,Finset.sum_boole,hit_single,Nat.mul_one,Finset.sum_const,
    nsmul_eq_mul] at h
  exact h

theorem card_sum : (∑ D ∈ cuts, D.card) = 1001*2^1000 := by
  have h := matched_sum (Finset.univ : Finset Line) id
  simpa using h

theorem one_orientation {G J : Type*} (groups : Finset G) (matched : Finset J)
    (line : J → Line) (w : G → ℕ) (touch : G → Finset Line)
    (pointwise : ∀ D : Finset Line,
      (∑ g ∈ groups, if (touch g ∩ D).Nonempty then w g else 0) +
        (matched.filter (fun i => line i ∈ D)).card ≤ 1003*D.card+1001) :
    (∑ g ∈ groups, countHit (touch g)*w g) + matched.card*2^1000 ≤
      1003*(1001*2^1000) + 2^1001*1001 := by
  classical
  have sumBudget (ds : Finset (Finset Line)) :
      (∑ D ∈ ds, (1003*D.card+1001)) = 1003*(∑ D ∈ ds, D.card)+ds.card*1001 := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const_nat (fun _ _ => rfl)]
  have card : cuts.card = 2^1001 :=
    (Finset.card_powerset (Finset.univ : Finset Line)).trans
      (congrArg (2^·) (Finset.card_univ.trans (Fintype.card_fin 1001)))
  have h := Finset.sum_le_sum (s := cuts) (fun D _ => pointwise D)
  have rhs : (∑ D ∈ cuts, (1003*D.card+1001)) = 1003*(1001*2^1000)+2^1001*1001 := by
    rw [sumBudget]
    rw [card_sum,card]
  rw [rhs,Finset.sum_add_distrib,group_sum,matched_sum] at h
  exact h

/-- The two actual families of cut inequalities, without assumed numerical
expectation estimates. Non-singleton groups span two lines in one direction. -/
theorem cut_contradiction {G J : Type*} (gs : Finset G) (ms : Finset J)
    (row col : G → Finset Line) (yr yc : J → Line) (w : G → ℕ) (B : ℕ)
    (mass : (∑ g ∈ gs, w g) + gs.card = 1001^2)
    (geometry : ∀ g ∈ gs, 0 < w g → 1 ≤ (row g).card ∧ 1 ≤ (col g).card ∧
      (2 ≤ (row g).card ∨ 2 ≤ (col g).card))
    (size : 1001^2 + gs.card + B ≤ 2009006) (matchedCount : 1001^2 ≤ ms.card+B)
    (probes : 2*1001^2 ≤ gs.card+5*B)
    (rows : ∀ D : Finset Line, (∑ g ∈ gs, if (row g ∩ D).Nonempty then w g else 0) +
        (ms.filter (fun i => yr i ∈ D)).card ≤ 1003*D.card+1001)
    (cols : ∀ D : Finset Line, (∑ g ∈ gs, if (col g ∩ D).Nonempty then w g else 0) +
        (ms.filter (fun i => yc i ∈ D)).card ≤ 1003*D.card+1001) : False := by
  classical
  have r := one_orientation gs ms yr w row rows
  have c := one_orientation gs ms yc w col cols
  have terms (g) (hg : g ∈ gs) :
      (5*2^999)*w g ≤ (countHit (row g) + countHit (col g))*w g := by
    by_cases h : w g = 0
    · simp [h]
    obtain ⟨a,b,ab⟩ := geometry g hg (by omega)
    have hr := hit_bounds _ 1 a
    have hc := hit_bounds _ 1 b
    apply Nat.mul_le_mul_right
    rcases ab with a|b
    · have := hit_bounds _ 2 a
      omega
    · have := hit_bounds _ 2 b
      omega
  have total := Finset.sum_le_sum terms
  simp only [Nat.add_mul,Finset.sum_add_distrib,← Finset.mul_sum] at total
  omega
end Onlyfr.PrivateGridAverage
