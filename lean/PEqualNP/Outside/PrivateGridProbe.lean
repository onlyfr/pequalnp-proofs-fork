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
/-- In the dark column, restore the horizontal incidences by adding each
crossing to its own row's private bit, and restore the hub in surviving columns. -/
theorem restore_with_twins {R C : Type*} (other : Prop)
    (row rowPrivate cross : R → Prop) (col colPrivate : C → Prop)
    (hub chosen chosenPrivate : Prop) :
    (other ∨ (∃ i, row i ∧ (rowPrivate i ∨ cross i)) ∨
      (∃ j, col j ∧ (colPrivate j ∨ hub)) ∨
      (chosen ∧ (chosenPrivate ∨ hub ∨ ∃ i, cross i))) ↔
    (other ∨ (∃ i, row i ∧ rowPrivate i) ∨ (∃ j, col j ∧ colPrivate j) ∨
      (∃ i, row i ∧ cross i) ∨ (hub ∧ ∃ j, col j) ∨
      (chosen ∧ (chosenPrivate ∨ hub ∨ ∃ i, cross i))) := by
  aesop

/-- Integer supporting bound, sharp on complete 3 by 3 and 3 by 4 groups. -/
theorem rectangle_charge (g r c : ℕ) (pos : 1 ≤ g) (area : g ≤ r*c) :
    29*g ≤ 117 + 3*((g-1)*(r+c)) := by
  by_cases big : 10 ≤ r+c
  · have h := Nat.mul_le_mul_left (g-1) big
    omega
  · have hr : r ≤ 9 := by omega
    have hc : c ≤ 9 := by omega
    interval_cases r <;> interval_cases c <;> simp_all <;> omega

theorem shared_lower_1001 {K total : ℕ}
    (groups : 29*1001^2 ≤ 117*K+3*total)
    (cuts : total ≤ 2*1001*3005) : 94103 ≤ K := by omega
/-- Scaled two-term inclusion-exclusion score for a uniform 24-column cut.
Using only seven columns of a group suffices for the integer certificate. -/
def cutScore (n : ℕ) : ℕ :=
  let t := min n 7
  2000*t - 23*t*(t-1)

theorem batch_rectangle_charge (g r c : ℕ) (pos : 1 ≤ g) (area : g ≤ r*c) :
    12678*g ≤ 26988 + (g-1)*(cutScore r+cutScore c) := by
  have large (h : 13034 ≤ cutScore r+cutScore c) := Nat.mul_le_mul_left (g-1) h
  by_cases hr : 7 ≤ r
  · have eq : cutScore r = 13034 := by simp [cutScore,min_eq_right hr]
    have h := large (by omega)
    omega
  by_cases hc : 7 ≤ c
  · have eq : cutScore c = 13034 := by simp [cutScore,min_eq_right hc]
    have h := large (by omega)
    omega
  interval_cases r <;> interval_cases c <;> norm_num [cutScore] at * <;> omega

theorem batch_partner_lower {K total : ℕ}
    (groups : 12678*1001^2 ≤ 26988*K+total)
    (cuts : 24*total ≤ 2*2000*1001*49097) : 167199 ≤ K := by omega
/-- Hall's inequality for a reader subset, split into exclusive leaves and
the remaining vertices. The latter have at least two incidences apiece and
each consumer has at most two reader inputs. -/
theorem consumer_hall_count {leaves rest incidences consumers neighbours : ℕ}
    (left : 2*rest ≤ incidences) (right : incidences ≤ 2*consumers)
    (exclusive : leaves+consumers ≤ neighbours) : leaves+rest ≤ neighbours := by omega

theorem matched_rectangle_charge (g r c : ℕ) (pos : 1 ≤ g) (area : g ≤ r*c) :
    8885*g ≤ 11816 + (g-1)*(cutScore r+cutScore c) := by
  have large (h : 13034 ≤ cutScore r+cutScore c) := Nat.mul_le_mul_left (g-1) h
  by_cases hr : 7 ≤ r
  · have eq : cutScore r = 13034 := by simp [cutScore,min_eq_right hr]
    have h := large (by omega)
    omega
  by_cases hc : 7 ≤ c
  · have eq : cutScore c = 13034 := by simp [cutScore,min_eq_right hc]
    have h := large (by omega)
    omega
  interval_cases r <;> interval_cases c <;> norm_num [cutScore] at * <;> omega

theorem matched_batch_lower {K total : ℕ}
    (groups : 8885*1001^2 ≤ 11816*K+total)
    (cuts : 24*total ≤ 2*2000*1001*(49097-24*1001)) : 399439 ≤ K := by omega

/-- A double charge on a two-reader consumer needs a spare reader slot
elsewhere. The unused partner slots cancel between the two capacity bounds. -/
theorem spare_probe_bound {M K B A C N P0 C0 S twice unused p a c : ℕ}
    (partition : B = A+C+N) (origins : S ≤ N) (tests : 2*M = p+a+c)
    (partner : p+P0 ≤ K+S) (single : c+2*C0 ≤ 2*C)
    (dual : a+unused = 2*A+twice) (cap : a ≤ 4*A)
    (spare : twice ≤ unused+C0+2*P0) :
    2*M ≤ K+3*B := by omega

theorem spare_partner_ceiling {K B : ℕ}
    (charges : 2*(1001^2) ≤ K+3*B) (tight : 1001^2+K+B ≤ 2009006) :
    K ≤ 508506 := by omega
def cutScore47 (n : ℕ) : ℕ :=
  let t := min n 7
  2000*t - 46*t*(t-1)

theorem matched_rectangle_47 (g r c : ℕ) (pos : 1 ≤ g) (area : g ≤ r*c) :
    8770*g ≤ 11632 + (g-1)*(cutScore47 r+cutScore47 c) := by
  have large (h : 12068 ≤ cutScore47 r+cutScore47 c) := Nat.mul_le_mul_left (g-1) h
  by_cases hr : 7 ≤ r
  · have eq : cutScore47 r = 12068 := by simp [cutScore47,min_eq_right hr]
    have h := large (by omega)
    omega
  by_cases hc : 7 ≤ c
  · have eq : cutScore47 c = 12068 := by simp [cutScore47,min_eq_right hc]
    have h := large (by omega)
    omega
  interval_cases r <;> interval_cases c <;> norm_num [cutScore47] at * <;> omega

theorem matched_lower_47 {K total : ℕ}
    (groups : 8770*1001^2 ≤ 11632*K+total)
    (cuts : 47*total ≤ 2*2000*1001*48142) : 402877 ≤ K := by omega
/-- Two distinct slots per reader suffice for an injective choice of actual
consumers. Exclusive leaves take both slots of their consumer; other readers
use their own input ports at two different consumers. -/
theorem consumer_matching {I G : Type*} [Finite I] [DecidableEq G]
    (adj : I → Finset G) (port : I × Bool ↪ G × Bool)
    (valid : ∀ x, (port x).1 ∈ adj x.1) :
    ∃ f : I → G, Function.Injective f ∧ ∀ i, f i ∈ adj i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp
  intro s
  have sub : ((s ×ˢ (Finset.univ : Finset Bool)).map port) ⊆
      ((s.biUnion adj) ×ˢ (Finset.univ : Finset Bool)) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_biUnion.mpr ⟨x.1,(Finset.mem_product.mp hx).1,valid x⟩,Finset.mem_univ _⟩
  have h := Finset.card_le_card sub
  simp only [Finset.card_map,Finset.card_product,Finset.card_univ,Fintype.card_bool] at h
  omega
/-- Count the second saving without counting any bypassed reader twice.
A zero partner inside the cut needs no tap. Outside the cut it removes at
least one further reader in its own group. -/
theorem zero_partner_credit {touched zero : Finset ℕ} {bypassed matched restore : ℕ}
    (least : bypassed + matched + (zero \ touched).card ≤
      restore + (touched \ zero).card) :
    bypassed + matched + zero.card ≤ restore + touched.card := by
  have a := Finset.card_sdiff_add_card_inter zero touched
  have b := Finset.card_sdiff_add_card_inter touched zero
  rw [Finset.inter_comm touched zero] at b
  omega

/-- H distinct matched consumers are themselves partners. Each matched
crossing is selected with probability 3/1001 in a three-column cut. -/
theorem paired_three_cut_impossible {B H : ℕ}
    (size : 1001^2 + 501501 + B ≤ 2009006)
    (matched : 1001^2 ≤ H+B)
    (cuts : 2997*1001 + 3*H ≤ 4010*1001) : False := by omega

/-- Scaled sum of the row and column expectation bounds after the additional
zero-partner saving. -/
theorem strengthened_lower_47 {K B H score : ℕ}
    (size : 1001^2 + K + B ≤ 2009006)
    (matched : 1001^2 ≤ H+B)
    (groups : 8770*1001^2 ≤ 11632*K + score)
    (cuts : 47*score + 4000*47*H ≤ 4000*1001*48142) :
    611406 ≤ K := by omega

theorem tight_grid_bounds_incompatible {K B H score : ℕ}
    (size : 1001^2 + K + B ≤ 2009006)
    (matched : 1001^2 ≤ H+B)
    (groups : 8770*1001^2 ≤ 11632*K + score)
    (cuts : 47*score + 4000*47*H ≤ 4000*1001*48142)
    (probes : 2*1001^2 ≤ K+3*B) : False := by
  have := strengthened_lower_47 size matched groups cuts
  have := spare_partner_ceiling probes size
  omega
/-- For 24 dark lines, any nonsingleton group touches at least one line
in each direction and at least two in one direction. The sum of its two hit
probabilities is at least (24/1001)*(2977/1000). -/
theorem tight_grid_uniform_impossible {K B H : ℕ}
    (size : 1001^2 + K + B ≤ 2009006) (matched : 1001^2 ≤ H+B)
    (cuts : 24*(2977*1001^2+2000*H) ≤ 2000*1001*25073 + 24*2977*K)
    (probes : 2*1001^2 ≤ K+5*B) : False := by
  have low : 902194 ≤ K := by omega
  have high : K ≤ 757755 := by omega
  omega
/-- Sum the pointwise circuit bound over a finite family of cuts. The input
losses for each group and the zero-partner credits can be correlated. -/
theorem sum_cut_credits {C G : Type*} (cuts : Finset C) (groups : Finset G)
    (loss : C → G → ℕ) (credit : C → ℕ) (lower : G → ℕ) (z allowance : ℕ)
    (pointwise : ∀ c ∈ cuts, (∑ g ∈ groups, loss c g) + credit c ≤ allowance)
    (hits : ∀ g ∈ groups, lower g ≤ ∑ c ∈ cuts, loss c g)
    (matched : z ≤ ∑ c ∈ cuts, credit c) :
    (∑ g ∈ groups, lower g) + z ≤ cuts.card * allowance := by
  have h := Finset.sum_le_sum pointwise
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := cuts) (t := groups)] at h
  have hl := Finset.sum_le_sum hits
  simpa using (le_trans (Nat.add_le_add hl matched) h)
end Onlyfr.PrivateGridProbe
