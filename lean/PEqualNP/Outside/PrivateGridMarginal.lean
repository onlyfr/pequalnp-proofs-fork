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
/-- After cutting a family of OR readers with common partner, the residual
network is a context in the reader outputs and the other raw variables. -/
theorem shared_partner_repair {G X : Type*}
    (C : (G → Prop) → X → Prop) (T guard : X → Prop)
    (fire : ∀ (p : G → Prop) x, T x → guard x → C (fun j => p j ∨ T x) x)
    (cover : ∀ (p : G → Prop) x, C (fun j => p j ∨ T x) x → guard x)
    (mono : ∀ (p q : G → Prop) x, (∀ j, p j → q j) → C p x → C q x) (p : G → Prop) (x : X) :
    C (fun j => p j ∨ T x) x ↔ C p x ∨ (T x ∧ guard x) := by
  constructor
  · intro h
    by_cases ht : T x
    · exact Or.inr ⟨ht,cover p x h⟩
    · exact Or.inl (by simpa [ht] using h)
  · rintro (h|⟨ht,hg⟩)
    · exact mono p _ x (fun _ hp => Or.inl hp) h
    · exact fire p x ht hg

/-- If active selectors cover the grouped crossing cases, saturating the
group forces the incidence output exactly when at least one selector is on. -/
theorem saturated_grid {G L : Type*} (touch : G → L → Prop) (y : L → Prop)
    (covered : ∀ l, ∃ g, touch g l) (outside : Prop)
    (hon : outside → ∃ l, y l) :
    (outside ∨ ∃ g l, touch g l ∧ y l) ↔ ∃ l, y l := by
  constructor
  · rintro (h|⟨_,l,_,hy⟩)
    · exact hon h
    · exact ⟨l,hy⟩
  · rintro ⟨l,hy⟩
    obtain ⟨g,hg⟩ := covered l
    exact Or.inr ⟨g,l,hg,hy⟩
/-- For a prefix of dependency layers, its last layer contributes no
crossing ancestors inside the prefix. The parameters bound the cut and repair sizes. -/
theorem row_layer_bound {r w a : ℕ} (hr : r ≤ 1001) (hw : w ≤ r)
    (anc : a ≤ 1001*(r-w)) (least : 1001*r ≤ 4004+r+a) :
    w ≤ 5 ∧ (r < 1001 → w ≤ 4) := by omega

theorem row_layer_depth {layers : ℕ} (capacity : 1001 ≤ 4*(layers-1)+5) :
    250 ≤ layers := by omega

/-- An upper approximation agrees when the common control is true. A
sufficient accepting predicate for the remaining minimal witnesses repairs it. -/
theorem common_control_repair (f upper control correction : Prop)
    (le : f → upper) (agree : control → upper → f)
    (sound : correction → f) (cover : f → ¬ control → correction) :
    f ↔ (control ∧ upper) ∨ correction := by
  constructor
  · intro h
    by_cases hc : control
    · exact Or.inl ⟨hc,le h⟩
    · exact Or.inr (cover h hc)
  · rintro (⟨h,u⟩|h)
    · exact agree h u
    · exact sound h
/-- With the vertical infinity point suppressed, a negative input on which a
whole row partner fires must have a separate point covering every column. -/
theorem column_cover_card {P C : Type*} [Fintype C] (active : Finset P)
    (cover : P → C → Prop) (all : ∀ c, ∃ p ∈ active, cover p c)
    (unique : ∀ p ∈ active, ∀ c d, cover p c → cover p d → c = d) :
    Fintype.card C ≤ active.card := by
  classical
  choose pick mem spec using all
  let emb : C → ↥active := fun c => ⟨pick c,mem c⟩
  have inj : Function.Injective emb := by
    intro c d eq
    have he : pick c = pick d := congrArg Subtype.val eq
    exact unique _ (mem c) c d (spec c) (he.symm ▸ spec d)
  simpa using Fintype.card_le_of_injective emb inj

theorem one_sound_row {r : ℕ} (least : 1001*r ≤ 1002+r) : r ≤ 1 := by omega

/-- Capacity of h layers of crossing inputs in the labelled dependency graph. -/
theorem pair_layer_capacity (m : ℕ → ℕ) (base : m 0 = 0)
    (step : ∀ h, m (h+1) ≤ 6006 + 2*m h) (h : ℕ) :
    m h + 6006 ≤ 6006 * 2^h := by
  induction h with
  | zero => simp [base]
  | succ h ih =>
    rw [pow_succ]
    have := step h
    omega
/-- If a line has no active points, toggling its selector cannot change f.
If a partner hides restoration of an incident crossing even with that line on,
truth of the partner on the dark restriction already certifies f. -/
theorem dark_line_sound (f partner lineOnPartner lineOn restored : Prop)
    (dark : lineOn ↔ f) (mono : partner → lineOnPartner)
    (hidden : lineOnPartner → (restored ↔ lineOn)) (inc : restored) :
    partner → f := fun hp => dark.mp ((hidden (mono hp)).mp inc)

/-- Restore a column's affine bits and its infinity bit after an arbitrary
circuit repair on the dark restriction. -/
theorem restore_column {R C : Type*} (base hub : Prop) (v : C → Prop)
    (c : C) (y x : R → Prop) (priv : Prop) :
    (base ∨ (∃ j, hub ∧ v j) ∨ (priv ∧ v c) ∨
      ∃ i, x i ∧ (v c ∨ y i)) ↔
    base ∨ (hub ∧ ∃ j, v j) ∨ (v c ∧ (priv ∨ ∃ i, x i)) ∨ ∃ i, x i ∧ y i := by
  constructor
  · rintro (h|⟨j,hh,hj⟩|⟨hp,hc⟩|⟨i,hx,hc|hy⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hh,j,hj⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hc,Or.inl hp⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hc,Or.inr ⟨i,hx⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i,hx,hy⟩))
  · rintro (h|⟨hh,j,hj⟩|⟨hc,hp|⟨i,hx⟩⟩|⟨i,hx,hy⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨j,hh,hj⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hp,hc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i,hx,Or.inl hc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i,hx,Or.inr hy⟩))
end Onlyfr.PrivateGridMarginal
