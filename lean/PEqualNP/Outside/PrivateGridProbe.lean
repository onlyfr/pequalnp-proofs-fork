import PEqualNP.Outside.PrivateGridMarginal

namespace Onlyfr.PrivateGridProbe
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc

/-- After changing one input with a sole reader r, the first other changed
gate reads wire m+r. Every different operand of that gate is unchanged. -/
theorem first_changed_consumer {m : ℕ} {gs : List Gate} (clean : MClean m gs)
    (x y : Fin m → Bool) (i : Fin m) (r : ℕ)
    (same : ∀ a, a ≠ i → x a = y a)
    (sole : ∀ k, Reads gs k i → k = r)
    (existsChange : ∃ k, k < gs.length ∧ k ≠ r ∧ vl gs x (m+k) ≠ vl gs y (m+k)) :
    ∃ k, Reads gs k (m+r) ∧ vl gs x (m+k) ≠ vl gs y (m+k) ∧
      ∀ w, Reads gs k w → w ≠ m+r → vl gs x w = vl gs y w := by
  classical
  let k := Nat.find existsChange
  obtain ⟨hk,hkr,change⟩ := Nat.find_spec existsChange
  let g := gs[k]
  have hg : gs[k]? = some g := by simp [g]
  have other (w : ℕ) (hr : Reads gs k w) (hne : w ≠ m+r) :
      vl gs x w = vl gs y w := by
    by_cases hw : w < m
    · have ne : (⟨w,hw⟩ : Fin m) ≠ i := by
        intro he
        have e : w = (i : ℕ) := congrArg Fin.val he
        exact hkr (sole k (e ▸ hr))
      simpa only [vl_input gs x w hw,vl_input gs y w hw] using same ⟨w,hw⟩ ne
    · have lt := reads_lt clean.1 hr
      let j := w-m
      have eq : w = m+j := by dsimp [j]; omega
      have hj : j < k := by omega
      have early := Nat.find_min existsChange hj
      rw [eq]
      by_contra diff
      exact early ⟨by omega,by omega,diff⟩
  refine ⟨k,?_,change,other⟩
  by_contra noRead
  exact change (vl_congr gs clean.1 x y k g hg fun w hw =>
    other w ⟨g,hg,hw⟩ (fun e => noRead (e ▸ (show Reads gs k w from ⟨g,hg,hw⟩))))

/-- Accounting after charging the two selector probes per crossing. O
counts other gates directly consuming a reader, and S counts exceptional
two-selector signatures first created outside these O gates. -/
theorem probe_budget {M K B O S : ℕ}
    (charges : 2*M ≤ K + S + 4*O) (separate : S+O ≤ B) :
    2*M ≤ K+4*B := by omega

theorem distinct_budget_1001 {B : ℕ} (charges : 2*(1001^2) ≤ 1001^2+4*B) :
    250501 ≤ B := by omega

theorem tight_partner_ceiling {K B : ℕ}
    (charges : 2*(1001^2) ≤ K+4*B) (tight : 1001^2+K+B ≤ 2009006) :
    K ≤ 674672 := by omega

/-- At a nonincident pair for a different point, add a line through the
reader's own point missing the tested point. A true partner would mask a
change from a negative input to a positive incidence. -/
theorem reject_nonincident_pair {P L : Type*} [DecidableEq P] [DecidableEq L]
    (I : P → L → Prop) (z p : P) (l b : L) (absent : ¬ I p l)
    (through : I z b) (miss : ¬ I p b) (T : Finset L → Prop)
    (mono : T {l} → T {l,b})
    (masked : T {l,b} →
      ((∃ u ∈ ({p,z} : Finset P), ∃ a ∈ ({l,b} : Finset L), I u a) ↔
       (∃ u ∈ ({p} : Finset P), ∃ a ∈ ({l,b} : Finset L), I u a))) :
    ¬ T {l} := by
  intro h
  have yes : ∃ u ∈ ({p,z} : Finset P), ∃ a ∈ ({l,b} : Finset L), I u a :=
    ⟨z,by simp,b,by simp,through⟩
  have no := (masked (mono h)).mp yes
  simp [absent,miss] at no

/-- Following a repeated singleton-selector signature backwards must arrive
at a gate which actually creates that signature. -/
theorem signature_origin (sig : ℕ → α) (target : α) (origin : ℕ → Prop)
    (seen : ∃ w, sig w = target)
    (trace : ∀ w, sig w = target → origin w ∨ ∃ u < w, sig u = target) :
    ∃ w, sig w = target ∧ origin w := by
  classical
  let w := Nat.find seen
  have hw : sig w = target := Nat.find_spec seen
  refine ⟨w,hw,?_⟩
  rcases trace w hw with h|⟨u,lt,hu⟩
  · exact h
  · exact False.elim ((Nat.find_min seen lt) hu)
/-- Count a finite assignment of probes to consumer gates, with capacity one
for ordinary partners, two for exceptional partners, and four for other consumers. -/
theorem count_probe_charges {P G : Type*} [DecidableEq G]
    (probes : Finset P) (partners other exceptional : Finset G) (assign : P → G)
    (dis : Disjoint partners other) (sub : exceptional ⊆ partners)
    (uses : ∀ p ∈ probes, assign p ∈ partners ∪ other)
    (partCap : ∀ g ∈ partners, (probes.filter (fun p => assign p = g)).card ≤
      1 + (if g ∈ exceptional then 1 else 0))
    (otherCap : ∀ g ∈ other, (probes.filter (fun p => assign p = g)).card ≤ 4) :
    probes.card ≤ partners.card + exceptional.card + 4*other.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := assign) (s := probes)
    (t := partners ∪ other) (fun p hp => uses p hp)
  rw [Finset.sum_union dis] at h
  have hp := Finset.sum_le_sum partCap
  have ho := Finset.sum_le_sum otherCap
  have inter : partners ∩ exceptional = exceptional := Finset.inter_eq_right.mpr sub
  simp [Finset.sum_add_distrib,inter] at hp
  simp at ho
  omega
/-- A doubly charged AND's other wire has exactly the two endpoint selectors
in its singleton signature. The crossing reader is on in every paired test. -/
theorem double_charge_signature {L : Type*} [DecidableEq L] (h v : L)
    (sig paired : L → Prop) (monotone : ∀ l, sig l → paired l)
    (nonedge : ∀ l, l ≠ h → l ≠ v → ¬ paired l)
    (hh : sig h) (hv : sig v) (l : L) : sig l ↔ l ∈ ({h,v} : Finset L) := by
  classical
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hs
    by_contra! hn
    exact nonedge l hn.1 hn.2 (monotone l hs)
  · rintro (rfl|rfl)
    · exact hh
    · exact hv

/-- On selector singletons the reader has empty signature. A binary gate
consuming it either has empty signature or copies the other input. -/
theorem consuming_signature {L : Type*} (R W G : Set L) (empty : R = ∅)
    (op : G = R ∩ W ∨ G = R ∪ W) : G = ∅ ∨ G = W := by
  subst R
  simpa using op
end Onlyfr.PrivateGridProbe
