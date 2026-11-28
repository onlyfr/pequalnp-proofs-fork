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
        (matched.filter (fun i => line i ∈ D)).card ≤ 1010*D.card+1001) :
    (∑ g ∈ groups, countHit (touch g)*w g) + matched.card*2^1000 ≤
      1010*(1001*2^1000) + 2^1001*1001 := by
  classical
  have sumBudget (ds : Finset (Finset Line)) :
      (∑ D ∈ ds, (1010*D.card+1001)) = 1010*(∑ D ∈ ds, D.card)+ds.card*1001 := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const_nat (fun _ _ => rfl)]
  have card : cuts.card = 2^1001 :=
    (Finset.card_powerset (Finset.univ : Finset Line)).trans
      (congrArg (2^·) (Finset.card_univ.trans (Fintype.card_fin 1001)))
  have h := Finset.sum_le_sum (s := cuts) (fun D _ => pointwise D)
  have rhs : (∑ D ∈ cuts, (1010*D.card+1001)) = 1010*(1001*2^1000)+2^1001*1001 := by
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
    (size : 1001^2 + gs.card + B ≤ 2023022) (matchedCount : 1001^2 ≤ ms.card+B)
    (probes : 2*1001^2 ≤ gs.card+8*B)
    (rows : ∀ D : Finset Line, (∑ g ∈ gs, if (row g ∩ D).Nonempty then w g else 0) +
        (ms.filter (fun i => yr i ∈ D)).card ≤ 1010*D.card+1001)
    (cols : ∀ D : Finset Line, (∑ g ∈ gs, if (col g ∩ D).Nonempty then w g else 0) +
        (ms.filter (fun i => yc i ∈ D)).card ≤ 1010*D.card+1001) : False := by
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
/-- Sum "group size minus one" exactly, with no statistical assumption
on a common partner or its distribution over lines. -/
theorem fiber_mass {J G : Type*} [DecidableEq G] (X U : Finset J) (tag : J → G) (sub : U ⊆ X) :
    let H := U.image tag
    (∑ g ∈ H, ((X.filter (fun i => tag i=g)).card-1))+H.card =
      (X.filter (fun i => tag i ∈ H)).card := by
  classical
  intro H
  let A := X.filter (fun i => tag i ∈ H)
  have count := Finset.card_eq_sum_card_fiberwise (s := A) (t := H) (f := tag)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have each (g) (hg : g ∈ H) :
      (A.filter (fun i => tag i=g)).card = (X.filter (fun i => tag i=g)).card-1+1 := by
    have eq : A.filter (fun i => tag i=g) = X.filter (fun i => tag i=g) := by
      ext i
      simp only [A,Finset.mem_filter]
      grind
    rw [eq]
    obtain ⟨i,hi,e⟩ := Finset.mem_image.mp hg
    have := Finset.card_pos.mpr (show (X.filter (fun j => tag j=g)).Nonempty from
      ⟨i,Finset.mem_filter.mpr ⟨sub hi,e⟩⟩)
    omega
  rw [Finset.sum_congr rfl each,Finset.sum_add_distrib] at count
  simpa only [Finset.sum_const,smul_eq_mul,mul_one,Nat.cast_id] using count.symm

/-- Exchange the sum over hit groups for a sum over groups whose support
meets the cut. Each crossing can use its own partner. -/
theorem fiber_hits {J G L : Type*} [DecidableEq G] [DecidableEq L] (X : Finset J) (tag : J → G)
    (axis : J → L) (D : Finset L) (w : G → ℕ) :
    (∑ g ∈ X.image tag, if (((X.filter (fun i => tag i=g)).image axis) ∩ D).Nonempty then w g else 0) =
      ∑ g ∈ (X.filter (fun i => axis i ∈ D)).image tag, w g := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext g
  simp only [Finset.mem_filter,Finset.mem_image,Finset.Nonempty,Finset.mem_inter]
  constructor
  · rintro ⟨_,a,⟨i,⟨hi,e⟩,rfl⟩,hd⟩
    exact ⟨i,⟨hi,hd⟩,e⟩
  · rintro ⟨i,⟨hi,hd⟩,e⟩
    exact ⟨⟨i,hi,e⟩,axis i,⟨i,⟨hi,e⟩,rfl⟩,hd⟩

/-- Convert pointwise reader counts into the two support sums and apply
averaging. The matched set may correlate arbitrarily with the partition. -/
theorem fiber_contradiction {J G : Type*} [DecidableEq G] (X M : Finset J) (tag : J → G)
    (a b : J → Line) (unique : ∀ i j, a i=a j → b i=b j → i=j)
    (nX : X.card=1001^2) (B : ℕ)
    (size : X.card+(X.image tag).card+B ≤ 2023022)
    (matched : X.card ≤ M.card+B) (probes : 2*X.card ≤ (X.image tag).card+8*B)
    (cuts : ∀ c : J → Line, c=a ∨ c=b → ∀ D : Finset Line,
      let U := X.filter (fun i => c i ∈ D)
      let H := U.image tag
      (X.filter (fun i => tag i ∈ H)).card + (M.filter (fun i => c i ∈ D)).card ≤
        1010*D.card+1001+H.card) : False := by
  classical
  let fiber (g : G) := X.filter (fun i => tag i=g)
  let w (g : G) := (fiber g).card-1
  have total := fiber_mass X X tag (fun _ h => h)
  have all : X.filter (fun i => tag i ∈ X.image tag) = X :=
    Finset.filter_true_of_mem (fun i hi => Finset.mem_image_of_mem tag hi)
  dsimp only at total
  rw [all,nX] at total
  have bounds (c : J → Line) (hc : c=a ∨ c=b) (D : Finset Line) :
      (∑ g ∈ X.image tag, if ((fiber g).image c ∩ D).Nonempty then w g else 0) +
        (M.filter (fun i => c i ∈ D)).card ≤ 1010*D.card+1001 := by
    let U := X.filter (fun i => c i ∈ D)
    have mass := fiber_mass X U tag (Finset.filter_subset ..)
    have cut := cuts c hc D
    rw [fiber_hits X tag c D w]
    change (∑ g ∈ U.image tag, w g)+(M.filter (fun i => c i ∈ D)).card ≤ _
    change (∑ g ∈ U.image tag, w g)+(U.image tag).card = _ at mass
    change (X.filter (fun i => tag i ∈ U.image tag)).card+_ ≤ _+(U.image tag).card at cut
    omega
  apply cut_contradiction (X.image tag) M (fun g => (fiber g).image a) (fun g => (fiber g).image b)
    a b w B total _ (nX ▸ size) (nX ▸ matched) (nX ▸ probes) (bounds a (Or.inl rfl)) (bounds b (Or.inr rfl))
  intro g _ hg
  have gt : 1 < (fiber g).card := by dsimp only [w] at hg; omega
  obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp gt
  have two (c : J → Line) (h : c i ≠ c j) : 2 ≤ ((fiber g).image c).card :=
    Finset.one_lt_card.mpr ⟨_,Finset.mem_image_of_mem c hi,_,Finset.mem_image_of_mem c hj,h⟩
  have one (c : J → Line) : 1 ≤ ((fiber g).image c).card :=
    Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem c hi⟩
  refine ⟨one a,one b,?_⟩
  by_cases e : a i=a j
  · exact Or.inr (two b (fun eq => ne (unique i j e eq)))
  · exact Or.inl (two a e)

end Onlyfr.PrivateGridAverage
