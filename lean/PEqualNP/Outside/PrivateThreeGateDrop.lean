import PEqualNP.Outside.PrivateTwoGateDrop

namespace Onlyfr.PrivateThreeGateDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateReaderDrop Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateTwoGateDrop

/-- Wires reached from the selected input by following only AND gates. -/
inductive AndPath (m : ℕ) (gs : List Gate) (i : Fin m) : ℕ → Prop where
  | input : AndPath m gs i i
  | step {w r : ℕ} {g : Gate} : AndPath m gs i w → gs[r]? = some g →
      g.op = .and → w ∈ g.inputs → AndPath m gs i (m+r)

theorem AndPath.zero {m gs i w} (h : AndPath m gs i w) (hc : MClean m gs)
    (x : Fin m → Bool) (hx : x i = false) : vl gs x w = false := by
  induction h with
  | input => rw [vl_input gs x i i.isLt]; exact hx
  | @step w r g _ hg hand hw ih =>
    obtain ⟨a,b,_,_,hin,_⟩ := Free.vl_bin hc.1 hc.2 hg
    rw [vl_gate gs hc.1 x r g hg,hand,hin]
    have he : w = a ∨ w = b := by simpa [hin] using hw
    rcases he with rfl | rfl <;> simp [GateOp.eval, ih]

/-- Count distinct readers even when several AND paths lead to the same gate. -/
theorem save_path_readers {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hL : MLeast m f gs o) (i : Fin m)
    (hnc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false))
    (R : Finset ℕ) (hR : ∀ j ∈ R, ∃ w, AndPath m gs i w ∧ Reads gs j w) :
    ∃ t, t + R.card ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i false)) t := by
  apply save_aliases hL i false hnc R
  · intro j hj
    obtain ⟨_,_,hr⟩ := hR j hj
    exact reads_len hr
  · intro j hj
    obtain ⟨w,hw,hr⟩ := hR j hj
    exact Free.alias_of_rd hL.1 hL.2.1 hr {x | x i = false} false
      (fun x hx => hw.zero ⟨hL.1,hL.2.1⟩ x hx)

/-- A structural certificate for the required inequality, for any q. -/
theorem hdrop_of_readers {n q : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (D : Circuit) {gs : List Gate} {o : ℕ} (hL : MLeast (n+n) (edgeFun I S) gs o)
    (hsize : gs.length ≤ D.size) (l : Fin n) (hl : l ∈ S)
    (hother : ∃ a ∈ S.erase l, ∃ p, I p a) (R : Finset ℕ) (hq : q ≤ 100 * R.card)
    (hR : ∀ j ∈ R, ∃ w, AndPath (n+n) gs (Fin.natAdd n l) w ∧ Reads gs j w) :
    ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase l ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      100 * E.size + q ≤ 100 * D.size := by
  obtain ⟨a,ha,p,hp⟩ := hother
  have hnc : ∃ x y, edgeFun I S (Function.update x (Fin.natAdd n l) false) ≠
      edgeFun I S (Function.update y (Fin.natAdd n l) false) := by
    refine ⟨pairInput p a,fun _ => false,?_⟩
    rw [erase_eq,erase_eq,(Onlyfr.PrivateOrReader.pair_edge_iff I _ p a).mpr ⟨ha,hp⟩,edgeFun_zero]
    decide
  obtain ⟨t,ht,hf⟩ := save_path_readers hL _ hnc R hR
  obtain ⟨E,hE,hs,hev⟩ := monotone2_of_has hf
  exact ⟨E,hE,fun x => by rw [hev,erase_eq,edgeFun_true],by omega⟩

/-- A repeated intersection on the removed line improves the private-point bound by one. -/
theorem private_of_concurrent {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (S : Finset (Fin n)) {l a b v : Fin n} (hl : l ∈ S) (ha : a ∈ S.erase l)
    (hb : b ∈ S.erase l) (hab : a ≠ b) (hvl : I v l) (hva : I v a) (hvb : I v b)
    (hd : Fintype.card {p // I p l} = q+1)
    (hj : ∀ p r, p ≠ r → ∃! t, I p t ∧ I r t) :
    q+3-S.card ≤ ((Finset.univ.filter (fun p => I p l)).filter
      (fun p => ∀ t ∈ S.erase l, ¬ I p t)).card := by
  classical
  let pts := fun t => Finset.univ.filter (fun p => I p t)
  have hbl := Finset.ne_of_mem_erase hb
  have hdeg : (pts l).card = q+1 := by simpa [pts,Fintype.card_subtype] using hd
  have hu (p r : Fin n) (hpr : p ≠ r) (c d : Fin n) :
      p ∈ pts c → r ∈ pts c → p ∈ pts d → r ∈ pts d → c = d := by
    intro h1 h2 h3 h4
    exact (hj p r hpr).unique ⟨(Finset.mem_filter.mp h1).2,(Finset.mem_filter.mp h2).2⟩
      ⟨(Finset.mem_filter.mp h3).2,(Finset.mem_filter.mp h4).2⟩
  have hmem := Finset.mem_of_mem_erase hb
  have hc := Onlyfr.PrivateLineAudit.lower_bound pts (S.erase b) l
    (Finset.mem_erase.mpr ⟨hbl.symm,hl⟩) q hdeg hu
  have sub : (pts l).filter (fun p => ∀ t ∈ (S.erase b).erase l, p ∉ pts t) ⊆
      (pts l).filter (fun p => ∀ t ∈ S.erase l, ¬ I p t) := by
    intro p hp
    obtain ⟨hpl,hn⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpl,?_⟩
    intro t ht hpt
    by_cases he : t = b
    · subst t
      have hpv : p = v := by
        by_contra hne
        exact hbl ((hj p v hne).unique ⟨hpt,hvb⟩ ⟨(Finset.mem_filter.mp hpl).2,hvl⟩)
      subst p
      exact hn a (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase ha,
        Finset.mem_erase.mpr ⟨hab,Finset.mem_of_mem_erase ha⟩⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hva⟩)
    · exact hn t (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase ht,
        Finset.mem_erase.mpr ⟨he,Finset.mem_of_mem_erase ht⟩⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpt⟩)
  have hc' := Finset.card_le_card sub
  rw [Finset.card_erase_of_mem hmem] at hc
  have hpos := Finset.card_pos.mpr (show S.Nonempty from ⟨l,hl⟩)
  change q+3-S.card ≤ ((pts l).filter _).card
  omega

theorem hdrop_concurrent {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hq : 201 ≤ q) (hcap : q ≤ 300) (S : Finset (Fin n)) (hs : S.card ≤ q+1)
    {l a b v : Fin n} (hl : l ∈ S) (ha : a ∈ S.erase l) (hb : b ∈ S.erase l)
    (hab : a ≠ b) (hvl : I v l) (hva : I v a) (hvb : I v b)
    (hd : Fintype.card {p // I p l} = q+1) (hj : ∀ p r, p ≠ r → ∃! t, I p t ∧ I r t)
    (D : Circuit) (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p t, t ∈ S ∧ I p t ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n t) = true) :
    ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p t, t ∈ S.erase l ∧ I p t ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n t) = true) ∧
      100 * E.size + q ≤ 100 * D.size := by
  classical
  let P := (Finset.univ.filter (fun p => I p l)).filter (fun p => ∀ t ∈ S.erase l, ¬ I p t)
  have hcard : q+3-S.card ≤ P.card := private_of_concurrent I S hl ha hb hab hvl hva hvb hd hj
  have hpriv (p) (hp : p ∈ P) : I p l ∧ ∀ t ∈ S.erase l, ¬ I p t :=
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2,(Finset.mem_filter.mp hp).2⟩
  have hv : v ∉ P := fun h => (hpriv v h).2 a ha hva
  obtain ⟨E,hE,hev,ht⟩ := private_points_and_line_save I S l P D 1 (by decide)
    (fun _ => ⟨v,hv,hvl⟩) hl hpriv ⟨a,ha,v,hva⟩ hm hex
  exact ⟨E,hE,hev,by omega⟩

end Onlyfr.PrivateThreeGateDrop