import PEqualNP.Outside.PrivateOrReader
import PEqualNP.Outside.PrivateReaderDrop
import PEqualNP.Outside.PrivateDropSmall

namespace Onlyfr.PrivateTwoGateDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateOrReader Onlyfr.PrivateReaderDrop

private theorem erase_eq {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n)) (l : Fin n)
    (x : Fin (n+n) → Bool) :
    edgeFun I S (Function.update x (Fin.natAdd n l) false) = edgeFun I (S.erase l) x := by
  apply Bool.eq_iff_iff.mpr
  rw [edgeFun_true, edgeFun_true]
  constructor
  · rintro ⟨p,a,ha,hpa,hp,hat⟩
    have hal : a ≠ l := by rintro rfl; simp at hat
    have hne : Fin.natAdd n a ≠ Fin.natAdd n l := fun h => hal (Fin.natAdd_injective n n h)
    rw [Function.update_of_ne hne] at hat
    rw [Function.update_of_ne (left_ne_right p l)] at hp
    exact ⟨p,a,Finset.mem_erase.mpr ⟨hal,ha⟩,hpa,hp,hat⟩
  · rintro ⟨p,a,ha,hpa,hp,hat⟩
    have hne : Fin.natAdd n a ≠ Fin.natAdd n l := fun h => Finset.ne_of_mem_erase ha (Fin.natAdd_injective n n h)
    exact ⟨p,a,Finset.mem_of_mem_erase ha,hpa,by rwa [Function.update_of_ne (left_ne_right p l)],
      by rwa [Function.update_of_ne hne]⟩

private theorem separate {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    {l a : Fin n} (hla : l ≠ a) (hd : 2 ≤ Fintype.card {p // I p l})
    (hj : ∀ p r, p ≠ r → ∃! b, I p b ∧ I r b) : ∃ p, I p l ∧ ¬ I p a := by
  classical
  by_contra! h
  have hone : (Finset.univ.filter (fun p => I p l)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp r hr
    by_contra hpr
    have hp' := (Finset.mem_filter.mp hp).2
    have hr' := (Finset.mem_filter.mp hr).2
    exact hla ((hj p r hpr).unique ⟨hp',hr'⟩ ⟨h p hp',h r hr'⟩)
  rw [Fintype.card_subtype] at hd
  omega

theorem two_gate_drop {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hd : ∀ a, 2 ≤ Fintype.card {p // I p a}) (hj : ∀ p r, p ≠ r → ∃! b, I p b ∧ I r b)
    (S : Finset (Fin n)) (hs : 2 ≤ S.card) (D : Circuit) (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) :
    ∃ l ∈ S, ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = edgeFun I (S.erase l) x) ∧ E.size+2 ≤ D.size := by
  classical
  have point (a) : ∃ p, I p a := by
    have h := hd a
    rw [Fintype.card_subtype] at h
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun p => I p a)).card)
    exact ⟨p,(Finset.mem_filter.mp hp).2⟩
  have nc (A : Finset (Fin n)) (ha : A.Nonempty) : ∃ x y, edgeFun I A x ≠ edgeFun I A y := by
    obtain ⟨a,ha⟩ := ha
    obtain ⟨p,hp⟩ := point a
    exact ⟨pairInput p a,fun _ => false,by rw [(pair_edge_iff I A p a).mpr ⟨ha,hp⟩,edgeFun_zero]; decide⟩
  have hne := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨gs,o,hL,hlen⟩ := Clean.ToolLeast_proof _ _ _ (nc S hne) (mono_size_of_exact I S D hm hex)
  have hnc (a) (ha : a ∈ S) : ∃ x y, edgeFun I S (Function.update x (Fin.natAdd n a) false) ≠
      edgeFun I S (Function.update y (Fin.natAdd n a) false) := by
    simp only [erase_eq]
    apply nc
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    omega
  let P := fun k => ∃ a ∈ S, Reads gs k (Fin.natAdd n a)
  have someRead : ∃ k, P k := by
    obtain ⟨a,ha⟩ := hne
    obtain ⟨p,hp⟩ := point a
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
      simp [i]
    obtain ⟨k,hk⟩ := Free.read_of_dep hL.2.2.1 i dep ho
    exact ⟨k,a,ha,hk⟩
  let r := Nat.find someRead
  obtain ⟨l,hl,hr⟩ := Nat.find_spec someRead
  have hr' : Reads gs r (Fin.natAdd n l) := hr
  have first : ∀ k v, Reads gs k v → active S v → r ≤ k := by
    rintro k v hk ⟨a,ha,rfl⟩
    exact Nat.find_min' someRead ⟨a,ha,hk⟩
  have finish (a) (ha : a ∈ S) (h : ∃ t, t+2 ≤ gs.length ∧ HasMonoSize (n+n)
      (fun x => edgeFun I S (Function.update x (Fin.natAdd n a) false)) t) :
      ∃ E : Circuit, Monotone2 E ∧ (∀ x, circuitFun (n+n) E x = edgeFun I (S.erase a) x) ∧
        E.size+2 ≤ D.size := by
    obtain ⟨t,ht,hf⟩ := h
    obtain ⟨E,hE,hsize,hev⟩ := monotone2_of_has hf
    exact ⟨E,hE,fun x => (hev x).trans (erase_eq I S a x),by omega⟩
  by_cases many : ∃ a ∈ S, ∃ u v, u ≠ v ∧ Reads gs u (Fin.natAdd n a) ∧ Reads gs v (Fin.natAdd n a)
  · obtain ⟨a,ha,u,v,huv,hu,hv⟩ := many
    apply Exists.intro a
    refine ⟨ha,finish a ha ?_⟩
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
  · exact ⟨l,hl,finish l hl (save_and_reader hL _ hg hand hinl (hnc l hl))⟩
  obtain ⟨w,hop,hor⟩ : ∃ w, g.op = .or ∧
      (g.inputs = [(Fin.natAdd n l : ℕ),w] ∨ g.inputs = [w,(Fin.natAdd n l : ℕ)]) := by
    rcases hL.1 r g hg with ⟨hn,_⟩ | ⟨hop,j,k,_,_,hin⟩
    · exact False.elim (hL.2.1 g (List.mem_of_getElem? hg) hn)
    have he := hop.resolve_left hand
    have hjk : (Fin.natAdd n l : ℕ) = j ∨ (Fin.natAdd n l : ℕ) = k := by simpa [hin] using hinl
    rcases hjk with rfl | rfl
    · exact ⟨k,he,Or.inl hin⟩
    · exact ⟨j,he,Or.inr hin⟩
  obtain ⟨p,hp⟩ := point l
  obtain ⟨a,ha,rfl⟩ := active_partner I S ⟨hL.1,hL.2.1⟩ hL.2.2.1 p l hl hp hg hop hor first (only l hl hr)
  have hra : Reads gs r (Fin.natAdd n a) := ⟨g,hg,by rcases hor with h|h <;> simp [h]⟩
  have hla : l ≠ a := by
    rintro rfl
    apply Removal.ToolNoAlias_proof _ _ _ _ hL (nc S hne) r (reads_len hr) _ (reads_lt hL.1 hr)
    intro x
    rw [vl_gate gs hL.1 x r g hg,hop,hor.elim id id]
    simp [GateOp.eval]
  exfalso
  rcases hor with h|h
  · obtain ⟨v,hvl,hva⟩ := separate I hla (hd l) hj
    exact no_shared_or I S hL.1 hL.2.2.1 v l a hl hvl hva hg hop h (only l hl hr) (only a ha hra)
  · obtain ⟨v,hva,hvl⟩ := separate I hla.symm (hd a) hj
    exact no_shared_or I S hL.1 hL.2.2.1 v a l ha hva hvl hg hop h (only a ha hra) (only l hl hr)

/-- The reduction's deletion premise for every nonempty active set at orders up to 200. -/
theorem hdrop_le_200 {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hcap : q ≤ 200)
    (hd : ∀ a, Fintype.card {p // I p a} = q+1) (hj : ∀ p r, p ≠ r → ∃! b, I p b ∧ I r b)
    (S : Finset (Fin n)) (D : Circuit) (hne : S.Nonempty) (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) :
    ∃ l ∈ S, ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase l ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      100 * E.size + q ≤ 100 * D.size := by
  classical
  by_cases hs : 2 ≤ S.card
  · obtain ⟨l,hl,E,hE,hev,hsize⟩ := two_gate_drop I (fun a => by rw [hd]; omega) hj S hs D hm hex
    exact ⟨l,hl,E,hE,fun x => by rw [hev,edgeFun_true],by omega⟩
  · exact Onlyfr.PrivateDropSmall.hdrop_small_succ I hd hj S D hne (by omega) hm hex

end Onlyfr.PrivateTwoGateDrop