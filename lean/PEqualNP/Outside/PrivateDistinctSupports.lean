import PEqualNP.Outside.PrivateTwoGateDrop

namespace Onlyfr.PrivateDistinctSupports

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateOrReader Onlyfr.PrivateReaderDrop
open Onlyfr.PrivateTwoGateDrop Onlyfr.PrivateGateDrop

/-- Either ordering of an OR gate makes its two sole input leaves
indistinguishable. Distinct supports may be nested. -/
private theorem twins {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    {gs : List Gate} {o r : ℕ} {g : Gate} (hc : CleanL (n+n) gs)
    (hev : ∀ x, vl gs x o = edgeFun I S x)
    (p l a : Fin n) (hl : l ∈ S) (hpl : I p l) (hpa : ¬ I p a)
    (hg : gs[r]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [(Fin.natAdd n l : ℕ), (Fin.natAdd n a : ℕ)] ∨
           g.inputs = [(Fin.natAdd n a : ℕ), (Fin.natAdd n l : ℕ)])
    (hrl : ∀ k, Reads gs k (Fin.natAdd n l) → k = r)
    (hra : ∀ k, Reads gs k (Fin.natAdd n a) → k = r)
    (hol : o ≠ (Fin.natAdd n l : ℕ)) (hoa : o ≠ (Fin.natAdd n a : ℕ)) : False := by
  let B := fun j : ℕ => j = (Fin.natAdd n l : ℕ) ∨ j = (Fin.natAdd n a : ℕ)
  have hh := agree_of_one_reader hc (pairInput p l) (pairInput p a) B r o
    (fun h => h.elim hol hoa) (by
      intro j hj
      have hn (v : Fin n) (h : B (Fin.natAdd n v)) : j ≠ Fin.natAdd n v := by
        rintro rfl; exact hj h
      simp only [pairInput, hn l (Or.inl rfl), hn a (Or.inr rfl), or_false]) (by
      intro k w hr hw
      rcases hw with e|e
      · exact hrl k (e ▸ hr)
      · exact hra k (e ▸ hr)) (by
      rw [vl_gate gs hc _ r g hg, vl_gate gs hc _ r g hg, hop]
      rcases hin with h|h <;> rw [h] <;>
        simp only [List.map_cons, List.map_nil, vl_input gs _ _ (Fin.natAdd n l).isLt,
          vl_input gs _ _ (Fin.natAdd n a).isLt]
      · change GateOp.or.eval [pairInput p l (Fin.natAdd n l), pairInput p l (Fin.natAdd n a)] =
          GateOp.or.eval [pairInput p a (Fin.natAdd n l), pairInput p a (Fin.natAdd n a)]
        simp only [pair_line]; simp [GateOp.eval]
      · change GateOp.or.eval [pairInput p l (Fin.natAdd n a), pairInput p l (Fin.natAdd n l)] =
          GateOp.or.eval [pairInput p a (Fin.natAdd n a), pairInput p a (Fin.natAdd n l)]
        simp only [pair_line]; simp [GateOp.eval])
  rw [hev,hev] at hh
  exact hpa (((pair_edge_iff I S p a).mp (hh ▸ (pair_edge_iff I S p l).mpr ⟨hl,hpl⟩)).2)

theorem peel {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (point : ∀ a ∈ S, ∃ p, I p a)
    (diff : ∀ l ∈ S, ∀ a ∈ S, l ≠ a →
      (∃ p, I p l ∧ ¬ I p a) ∨ ∃ p, I p a ∧ ¬ I p l)
    (hs : 2 ≤ S.card) {s : ℕ} (hf : HasMonoSize (n+n) (edgeFun I S) s) :
    ∃ a ∈ S, ∃ t, t+2 ≤ s ∧ HasMonoSize (n+n) (edgeFun I (S.erase a)) t := by
  classical
  have nc (A : Finset (Fin n)) (sub : A ⊆ S) (ha : A.Nonempty) :
      ∃ x y, edgeFun I A x ≠ edgeFun I A y := by
    obtain ⟨a,ha⟩ := ha
    obtain ⟨p,hp⟩ := point a (sub ha)
    exact ⟨pairInput p a,fun _ => false,by rw [(pair_edge_iff I A p a).mpr ⟨ha,hp⟩,edgeFun_zero]; decide⟩
  have hne := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨gs,o,hL,hlen⟩ := Clean.ToolLeast_proof _ _ _ (nc S (by rfl) hne) hf
  have hnc (a) (ha : a ∈ S) : ∃ x y : Fin (n+n) → Bool, edgeFun I S (Function.update x (Fin.natAdd n a) false) ≠
      edgeFun I S (Function.update y (Fin.natAdd n a) false) := by
    simp only [erase_eq]
    apply nc _ (Finset.erase_subset ..)
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    omega
  have hout (a) (ha : a ∈ S) : o ≠ (Fin.natAdd n a : ℕ) := by
    intro he
    obtain ⟨x,y,h⟩ := hnc a ha
    apply h
    rw [← hL.2.2.1,← hL.2.2.1,he,vl_input gs _ _ (Fin.natAdd n a).isLt,
      vl_input gs _ _ (Fin.natAdd n a).isLt]
    change Function.update x (Fin.natAdd n a) false (Fin.natAdd n a) = Function.update y (Fin.natAdd n a) false (Fin.natAdd n a)
    simp
  let P := fun k => ∃ a ∈ S, Reads gs k (Fin.natAdd n a)
  have someRead : ∃ k, P k := by
    obtain ⟨a,ha⟩ := hne
    obtain ⟨p,hp⟩ := point a ha
    let i := Fin.natAdd n a
    have dep : Dep (edgeFun I S) i := by
      refine ⟨pairInput p a, ?_⟩
      have hz : (!(pairInput p a i)) = false := by rw [show i = Fin.natAdd n a from rfl, pair_line]; simp
      rw [hz,erase_eq,(pair_edge_iff I S p a).mpr ⟨ha,hp⟩]
      intro he
      exact Finset.ne_of_mem_erase ((pair_edge_iff I _ p a).mp he).1 rfl
    have ho : o ≠ (i : ℕ) := by
      intro he
      obtain ⟨x,y,hh⟩ := hnc a ha
      apply hh
      rw [← hL.2.2.1, ← hL.2.2.1, he, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
      change Function.update x i false i = Function.update y i false i
      simp
    obtain ⟨k,hk⟩ := Free.read_of_dep hL.2.2.1 i dep ho
    exact ⟨k,a,ha,hk⟩
  let r := Nat.find someRead
  obtain ⟨l,hl,hr⟩ := Nat.find_spec someRead
  have hr' : Reads gs r (Fin.natAdd n l) := hr
  have first : ∀ k v, Reads gs k v → active S v → r ≤ k := by
    rintro k v hk ⟨a,ha,rfl⟩
    exact Nat.find_min' someRead ⟨a,ha,hk⟩
  have finish (a) (h : ∃ t, t+2 ≤ gs.length ∧ HasMonoSize (n+n)
      (fun x => edgeFun I S (Function.update x (Fin.natAdd n a) false)) t) :
      ∃ t, t+2 ≤ s ∧ HasMonoSize (n+n) (edgeFun I (S.erase a)) t := by
    obtain ⟨t,ht,hf'⟩ := h
    exact ⟨t,by omega,by simpa only [erase_eq] using hf'⟩
  by_cases many : ∃ a ∈ S, ∃ u v, u ≠ v ∧ Reads gs u (Fin.natAdd n a) ∧ Reads gs v (Fin.natAdd n a)
  · obtain ⟨a,ha,u,v,huv,hu,hv⟩ := many
    apply Exists.intro a
    refine ⟨ha,finish a ?_⟩
    have h := save_readers hL _ false (hnc a ha) {u,v} (by
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> assumption)
    rwa [Finset.card_pair huv] at h
  have only (a) (ha : a ∈ S) (h : Reads gs r (Fin.natAdd n a)) :
      ∀ k, Reads gs k (Fin.natAdd n a) → k = r := by
    intro k hk
    by_contra he
    exact many ⟨a,ha,k,r,he,hk,h⟩
  obtain ⟨g,hg,hinl⟩ := hr'
  by_cases hand : g.op = .and
  · exact ⟨l,hl,finish l (save_and_reader hL _ hg hand hinl (hnc l hl))⟩
  obtain ⟨w,hop,hor⟩ : ∃ w, g.op = .or ∧
      (g.inputs = [(Fin.natAdd n l : ℕ),w] ∨ g.inputs = [w,(Fin.natAdd n l : ℕ)]) := by
    rcases hL.1 r g hg with ⟨hn,_⟩ | ⟨hop,j,k,_,_,hin⟩
    · exact False.elim (hL.2.1 g (List.mem_of_getElem? hg) hn)
    have he := hop.resolve_left hand
    have hjk : (Fin.natAdd n l : ℕ) = j ∨ (Fin.natAdd n l : ℕ) = k := by simpa [hin] using hinl
    rcases hjk with rfl | rfl
    · exact ⟨k,he,Or.inl hin⟩
    · exact ⟨j,he,Or.inr hin⟩
  obtain ⟨p,hp⟩ := point l hl
  obtain ⟨a,ha,rfl⟩ := active_partner I S ⟨hL.1,hL.2.1⟩ hL.2.2.1 p l hl hp hg hop hor first (only l hl hr)
  have hra : Reads gs r (Fin.natAdd n a) := ⟨g,hg,by rcases hor with h|h <;> simp [h]⟩
  have hla : l ≠ a := by
    rintro rfl
    apply Removal.ToolNoAlias_proof _ _ _ _ hL (nc S (by rfl) hne) r (reads_len hr) _ (reads_lt hL.1 hr)
    intro x
    rw [vl_gate gs hL.1 x r g hg,hop,hor.elim id id]
    simp [GateOp.eval]
  exfalso
  rcases diff l hl a ha hla with ⟨p,hp,hq⟩|⟨p,hp,hq⟩
  · exact twins I S hL.1 hL.2.2.1 p l a hl hp hq hg hop hor (only l hl hr)
      (only a ha hra) (hout l hl) (hout a ha)
  · exact twins I S hL.1 hL.2.2.1 p a l ha hp hq hg hop hor.symm (only a ha hra)
      (only l hl hr) (hout a ha) (hout l hl)

/-- Iterating the two-gate elimination: the remaining supports never change. -/
theorem distinct_lower {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (point : ∀ a ∈ S, ∃ p, I p a)
    (diff : ∀ l ∈ S, ∀ a ∈ S, l ≠ a →
      (∃ p, I p l ∧ ¬ I p a) ∨ ∃ p, I p a ∧ ¬ I p l)
    {s : ℕ} (hf : HasMonoSize (n+n) (edgeFun I S) s) : 2*S.card ≤ s+1 := by
  classical
  by_cases h : 2 ≤ S.card
  · obtain ⟨a,ha,t,ht,hf'⟩ := peel I S point diff h hf
    have step := distinct_lower I (S.erase a) (fun l hl => point l (Finset.mem_of_mem_erase hl))
      (fun l hl b hb => diff l (Finset.mem_of_mem_erase hl) b (Finset.mem_of_mem_erase hb)) hf'
    have := Finset.card_erase_of_mem ha
    omega
  · by_cases pos : S.Nonempty
    · obtain ⟨a,ha⟩ := pos
      obtain ⟨p,hp⟩ := point a ha
      let i := Fin.natAdd n a
      have dep : Dep (edgeFun I S) i := by
        refine ⟨pairInput p a, ?_⟩
        have hz : (!(pairInput p a i)) = false := by rw [show i = Fin.natAdd n a from rfl, pair_line]; simp
        rw [hz,erase_eq,(pair_edge_iff I S p a).mpr ⟨ha,hp⟩]
        intro he
        exact Finset.ne_of_mem_erase ((pair_edge_iff I _ p a).mp he).1 rfl
      have nc : ∃ x y, edgeFun I S (Function.update x i true) ≠ edgeFun I S (Function.update y i true) := by
        refine ⟨pairInput p a, fun _ => false, ?_⟩
        have on : edgeFun I S (Function.update (pairInput p a) i true) = true := by
          apply (edgeFun_true ..).mpr
          exact ⟨p,a,ha,hp,by rw [Function.update_of_ne (left_ne_right p a)]; simp [pair_point],by simp [i]⟩
        rw [on]
        intro he
        obtain ⟨v,_,_,_,hv,_⟩ := (edgeFun_true ..).mp he.symm
        rw [Function.update_of_ne (left_ne_right v a)] at hv
        contradiction
      obtain ⟨t,ht,_⟩ := one_input _ _ _ _ true hf dep nc
      omega
    · have := Finset.not_nonempty_iff_eq_empty.mp pos
      simp [this]
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem ha

/-- Select one representative of each support and charge the remaining
essential inputs one gate each before applying the distinct-support bound. -/
theorem representative_lower {n : ℕ} (I : Fin n → Fin n → Prop) (S T : Finset (Fin n))
    (sub : T ⊆ S) (hne : T.Nonempty) (point : ∀ a ∈ S, ∃ p, I p a)
    (diff : ∀ l ∈ T, ∀ a ∈ T, l ≠ a →
      (∃ p, I p l ∧ ¬ I p a) ∨ ∃ p, I p a ∧ ¬ I p l)
    {s : ℕ} (hf : HasMonoSize (n+n) (edgeFun I S) s) : S.card + T.card ≤ s+1 := by
  classical
  by_cases eq : S = T
  · subst T
    have := distinct_lower I S point diff hf
    omega
  · obtain ⟨a,ha,hat⟩ : ∃ a ∈ S, a ∉ T := by
      by_contra! no
      exact eq (Finset.Subset.antisymm no sub)
    obtain ⟨p,hp⟩ := point a ha
    let i := Fin.natAdd n a
    have dep : Dep (edgeFun I S) i := by
      refine ⟨pairInput p a, ?_⟩
      have hz : (!(pairInput p a i)) = false := by rw [show i = Fin.natAdd n a from rfl,pair_line]; simp
      rw [hz,erase_eq,(pair_edge_iff I S p a).mpr ⟨ha,hp⟩]
      intro he
      exact Finset.ne_of_mem_erase ((pair_edge_iff I _ p a).mp he).1 rfl
    have sub' : T ⊆ S.erase a := by
      intro l hl
      exact Finset.mem_erase.mpr ⟨fun he => hat (he ▸ hl),sub hl⟩
    obtain ⟨l,hl⟩ := hne
    obtain ⟨v,hv⟩ := point l (sub hl)
    have nc : ∃ x y, edgeFun I S (Function.update x i false) ≠ edgeFun I S (Function.update y i false) := by
      exact ⟨pairInput v l, fun _ => false, by
        simp only [i,erase_eq,(pair_edge_iff I _ v l).mpr ⟨sub' hl,hv⟩,edgeFun_zero]; decide⟩
    obtain ⟨t,ht,ht'⟩ := one_input _ _ _ _ false hf dep nc
    have hf' : HasMonoSize (n+n) (edgeFun I (S.erase a)) t := by simpa only [i,erase_eq] using ht'
    have step := representative_lower I (S.erase a) T sub' ⟨l,hl⟩
      (fun d hd => point d (Finset.mem_of_mem_erase hd)) diff hf'
    have := Finset.card_erase_of_mem ha
    omega
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem ha

end Onlyfr.PrivateDistinctSupports
