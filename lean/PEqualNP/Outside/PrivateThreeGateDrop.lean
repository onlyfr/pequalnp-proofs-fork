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
  have hc : q+2-(S.erase b).card ≤ ((pts l).filter
      (fun p => ∀ t ∈ (S.erase b).erase l, p ∉ pts t)).card := by
    convert Onlyfr.PrivateLineAudit.lower_bound pts (S.erase b) l
      (Finset.mem_erase.mpr ⟨hbl.symm,hl⟩) q hdeg hu using 1 <;> congr 1 <;> ext p <;> simp
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

/-- If the partner of an AND input is a gate feeding only that AND, the
partner gate itself is dead after setting the input false. -/
theorem save_exclusive_partner {m : ℕ} {gs : List Gate} {o d r : ℕ} {f : (Fin m → Bool) → Bool}
    (hL : MLeast m f gs o) (i : Fin m) {g : Gate} (hg : gs[r]? = some g) (hop : g.op = .and)
    (hi : (i : ℕ) ∈ g.inputs) (hd : m+d ∈ g.inputs)
    (honly : ∀ j, Reads gs j (m+d) → j = r)
    (hnc : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false)) :
    ∃ t, t+3 ≤ gs.length ∧ HasMonoSize m (fun x => f (Function.update x i false)) t := by
  classical
  obtain ⟨x,y,hxy⟩ := hnc
  have hr : Reads gs r i := ⟨g,hg,hi⟩
  have hdr := reads_lt hL.1 (show Reads gs r (m+d) from ⟨g,hg,hd⟩)
  have hrlen := reads_len hr
  have hout : o ≠ m+d := by
    intro he
    let last := gs.length-1
    have hlast : last < gs.length := by dsimp [last]; omega
    have hne : o ≠ m+last := by dsimp [last]; omega
    obtain ⟨j,hj⟩ := Free.live Removal.ToolRemoval_proof hL ⟨_,_,hxy⟩ hlast hne
    have h1 := reads_lt hL.1 hj
    have h2 := reads_len hj
    dsimp [last] at h1
    omega
  let P : Set (Fin m → Bool) := {z | z i = false}
  have hz (z) (hz : z ∈ P) : vl gs z (m+r) = false := by
    exact (AndPath.step (AndPath.input (m := m) (gs := gs) (i := i)) hg hop hi).zero ⟨hL.1,hL.2.1⟩ z hz
  have hor : o ≠ m+r := by
    intro he
    apply hxy
    rw [← hL.2.2.1, ← hL.2.2.1, he,hz _ (Function.update_self i false x),hz _ (Function.update_self i false y)]
  obtain ⟨u,hu⟩ := Free.live Removal.ToolRemoval_proof hL ⟨_,_,hxy⟩ hrlen hor
  have hru := reads_lt hL.1 hu
  have hul := reads_len hu
  obtain ⟨gu,hgu,hw⟩ := hu
  have havoid : m+d ∉ gu.inputs := fun h => (by omega : u ≠ r) (honly u ⟨gu,hgu,h⟩)
  obtain ⟨j,k,hj,hk,hin,he⟩ := Free.vl_bin hL.1 hL.2.1 hgu
  have hmem : m+r = j ∨ m+r = k := by simpa [hin] using hw
  have htarget : ∃ t, t < m+u ∧ t ≠ m+d ∧ ∀ z ∈ P, vl gs z (m+u) = vl gs z t := by
    have hjd : j ≠ m+d := by rintro rfl; exact havoid (by simp [hin])
    have hkd : k ≠ m+d := by rintro rfl; exact havoid (by simp [hin])
    rcases hmem with rfl | rfl <;> rcases he with he | he
    · exact ⟨_,hj,hjd,fun z h => by rw [he,hz z h]; simp⟩
    · exact ⟨_,hk,hkd,fun z h => by rw [he,hz z h]; simp⟩
    · exact ⟨_,hk,hkd,fun z h => by rw [he,hz z h]; simp⟩
    · exact ⟨_,hj,hjd,fun z h => by rw [he,hz z h]; simp⟩
  obtain ⟨t,ht,htd,htv⟩ := htarget
  let A : Finset ℕ := {d,r,u}
  let target (j : ℕ) : Option ℕ := if j = d then none else if j = r then some i.val else some t
  have hrd : r ≠ d := by omega
  have hud : u ≠ d := by omega
  have hur : u ≠ r := by omega
  have hid : i.val ≠ m+d := by have := i.isLt; omega
  have rem : Removable m gs o P A target := by
    intro j h
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with h | h | h <;> subst j
    · refine ⟨by omega,Or.inr ⟨by simp [target],hout,?_,?_⟩⟩
      · intro v hv
        rw [honly v hv]
        simp [A]
      · intro v _
        simp only [target]
        by_cases hv : v = d <;> by_cases hw : v = r <;> simp [hv,hw,hid,htd,hrd]
    · refine ⟨hrlen,Or.inl ⟨i,by simp [target,hrd],reads_lt hL.1 hr,?_⟩⟩
      intro z h
      rw [hz z h,vl_input gs z i i.isLt]
      exact h.symm
    · exact ⟨hul,Or.inl ⟨t,by simp [target,hud,hur],ht,htv⟩⟩
  obtain ⟨gs',map,hc,hfree,hlen,_,hval⟩ :=
    Removal.ToolRemoval_proof m gs o P A target hL.1 rem
  have hh := hval o (Free.out_lt hL.2.2.1 ⟨_,_,hxy⟩) (by
    intro j _ hj
    by_cases h : j = d
    · simpa [h] using hout
    · by_cases h' : j = r <;> simp [target,h,h',hrd] at hj)
  have heq : (fun z => vl gs' (Function.update z i false) (map o)) =
      (fun z => f (Function.update z i false)) := by
    funext z
    exact (hh.2 _ (Function.update_self i false z)).trans (hL.2.2.1 _)
  have hres := Clean.ToolRestrict_proof m gs' (map o) i false ⟨hc,hfree hL.2.1⟩
    ⟨x,y,by change (fun z => vl gs' (Function.update z i false) (map o)) x ≠
                     (fun z => vl gs' (Function.update z i false) (map o)) y; rw [heq]; exact hxy⟩
  have hcA : A.card = 3 := by simp [A,Ne.symm hrd,Ne.symm hud,Ne.symm hur]
  exact ⟨_,by omega,heq ▸ hres⟩

end Onlyfr.PrivateThreeGateDrop