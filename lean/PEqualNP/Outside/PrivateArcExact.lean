import PEqualNP.Outside.PrivateDistinctSupports
import PEqualNP.Outside.PrivateForestLift
import PEqualNP.MetaComplexity.Helpers.CoverCircuitList

namespace Onlyfr.PrivateArcExact

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.Helpers.PermInputs
open Onlyfr.PrivateDistinctSupports Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateForestLift

private theorem relabel_mono {n m s : ℕ} (π : Fin n → Fin m) {f}
    (hf : HasMonoSize n f s) : HasMonoSize m (fun x => f (x ∘ π)) s := by
  obtain ⟨C,ok,nf,sz,ev⟩ := hf
  refine ⟨relabel n m π C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.mp hg
    exact ⟨(ok _ hg₀).1, by simpa [relGate] using (ok _ hg₀).2⟩
  · intro g hg
    obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.mp hg
    exact nf g₀ hg₀
  · simpa [relabel,Circuit.size] using sz
  · intro x
    change _ = f (x ∘ π)
    rw [← ev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

section Rows
variable {P L : Type*} [DecidableEq P] [DecidableEq L]
variable {n : ℕ} (row : L → Finset P) (S : Finset L)
variable (pt : P ≃ Fin n) (ln : L ↪ Fin n) (I : Fin n → Fin n → Prop)
variable (rows : ∀ l ∈ S, ∀ p, I (pt p) (ln l) ↔ p ∈ row l)

include rows

private theorem encoded_lower (T : Finset P) (sub : T ⊆ S.biUnion row)
    (hne : T.Nonempty)
    (diff : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∃ l ∈ S, ¬ (p ∈ row l ↔ q ∈ row l))
    {t : ℕ} (hf : HasMonoSize (n+n) (edgeFun I (S.map ln)) t) :
    (S.biUnion row).card + T.card ≤ t+1 := by
  classical
  let A := (S.biUnion row).map pt.toEmbedding
  let J (l p : Fin n) := l ∈ S.map ln ∧ I p l
  let swap : Fin (n+n) → Fin (n+n) := Fin.addCases (Fin.natAdd n) (Fin.castAdd n)
  have eqf : (fun x => edgeFun I (S.map ln) (x ∘ swap)) = edgeFun J A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [edgeFun_true,edgeFun_true]
    simp only [Function.comp_apply,swap,Fin.addCases_left,Fin.addCases_right]
    constructor
    · rintro ⟨p,l,hl,hi,hp,hy⟩
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hl
      obtain ⟨v,rfl⟩ := pt.surjective p
      exact ⟨_,_,Finset.mem_map_of_mem _ (Finset.mem_biUnion.mpr ⟨a,ha,(rows a ha v).mp hi⟩),
        ⟨Finset.mem_map_of_mem _ ha,hi⟩,hy,hp⟩
    · rintro ⟨l,p,_,⟨hl,hi⟩,hy,hp⟩
      exact ⟨p,l,hl,hi,hp,hy⟩
  have ht := relabel_mono swap hf
  rw [eqf] at ht
  have h := representative_lower J A (T.map pt.toEmbedding) (Finset.map_subset_map.mpr sub)
    hne.map (by
      intro u hu
      obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨l,hl,hi⟩ := Finset.mem_biUnion.mp hp
      exact ⟨_,Finset.mem_map_of_mem _ hl,(rows l hl p).mpr hi⟩) (by
      intro u hu v hv hne'
      obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨l,hl,hd⟩ := diff p hp q hq (fun e => hne' (congrArg pt e))
      have mem := Finset.mem_map_of_mem ln hl
      by_cases h : p ∈ row l
      · exact Or.inl ⟨ln l,⟨mem,(rows l hl p).mpr h⟩, fun H => hd (iff_of_true h ((rows l hl q).mp H.2))⟩
      · have hq' : q ∈ row l := by by_contra hh; exact hd (iff_of_false h hh)
        exact Or.inr ⟨ln l,⟨mem,(rows l hl q).mpr hq'⟩,fun H => h ((rows l hl p).mp H.2)⟩) ht
  simpa only [A,Finset.card_map] using h

private theorem encoded_upper (hn : S.Nonempty) (nonempty : ∀ l ∈ S, (row l).Nonempty) :
    HasMonoSize (n+n) (edgeFun I (S.map ln)) ((∑ l ∈ S, (row l).card) + S.card - 1) := by
  classical
  let entries := S.sigma row
  let edges := entries.toList.map (fun e => ((pt e.2).val,n+(ln e.1).val))
  let cover := S.toList.map (fun l => n+(ln l).val)
  have em {a b : ℕ} : (a,b) ∈ edges ↔ ∃ l ∈ S, ∃ p ∈ row l, (pt p).val = a ∧ n+(ln l).val = b := by
    simp [edges,entries,Finset.mem_sigma,Prod.ext_iff,Sigma.exists, and_assoc]
  have bounds (e) (he : e ∈ edges) : e.1 < n+n ∧ e.2 < n+n := by
    obtain ⟨a,b⟩ := e
    obtain ⟨l,_,p,_,rfl,rfl⟩ := em.mp he
    have := (pt p).isLt
    have := (ln l).isLt
    omega
  have cov (e) (he : e ∈ edges) : e.1 ∈ cover ∨ e.2 ∈ cover := by
    obtain ⟨a,b⟩ := e
    obtain ⟨l,hl,p,_,rfl,rfl⟩ := em.mp he
    exact Or.inr (List.mem_map.mpr ⟨l,Finset.mem_toList.mpr hl,rfl⟩)
  obtain ⟨l,hl⟩ := hn
  obtain ⟨p,hp⟩ := nonempty l hl
  have ne : edges ≠ [] := by
    intro h
    have hm := em.mpr ⟨l,hl,p,hp,rfl,rfl⟩
    simp [h] at hm
  obtain ⟨hok,hnf⟩ := CoverCircuit.fanInTwo_notFree (n+n) edges cover
  refine ⟨_,hok,hnf,?_,?_⟩
  · have hs := CoverCircuit.size_le (n+n) edges cover ne
    have elen : edges.length = ∑ l ∈ S, (row l).card := by simp [edges,entries,Finset.card_sigma]
    have clen : cover.length = S.card := by simp [cover]
    rw [elen,clen] at hs
    omega
  · intro x
    change circuitFun _ _ x = _
    rw [CoverCircuit.circuitFun_eq _ _ _ bounds cov,Bool.eq_iff_iff,decide_eq_true_eq,edgeFun_true]
    constructor
    · rintro ⟨a,b,h,hx,hy⟩
      rcases h with h|h
      · obtain ⟨l,hl,p,hp,ha,hb⟩ := em.mp h
        have ea : Fin.castAdd n (pt p) = a := Fin.ext ha
        have eb : Fin.natAdd n (ln l) = b := Fin.ext hb
        exact ⟨_,_,Finset.mem_map_of_mem _ hl,(rows l hl p).mpr hp,ea ▸ hx,eb ▸ hy⟩
      · obtain ⟨l,hl,p,hp,ha,hb⟩ := em.mp h
        have ea : Fin.castAdd n (pt p) = b := Fin.ext ha
        have eb : Fin.natAdd n (ln l) = a := Fin.ext hb
        exact ⟨_,_,Finset.mem_map_of_mem _ hl,(rows l hl p).mpr hp,ea ▸ hy,eb ▸ hx⟩
    · rintro ⟨u,v,hv,hi,hx,hy⟩
      obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨p,rfl⟩ := pt.surjective u
      exact ⟨_,_,Or.inl (em.mpr ⟨l,hl,p,(rows l hl p).mp hi,rfl,rfl⟩),hx,hy⟩

end Rows
section Arc
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {n : ℕ} (S : Finset (Option K)) (pt : ((K × K) ⊕ Option K) ≃ Fin n)
variable (ln : Option K ↪ Fin n) (I : Fin n → Fin n → Prop)
variable (rows : ∀ l ∈ S, ∀ p, I (pt p) (ln l) ↔ arcInc l p)

include rows

/-- Exact threshold on the actual two-block incidence inputs, allowing arbitrary
numberings of points and lines and arbitrary incidences outside the active rows. -/
theorem arc_size_iff (hne : S.Nonempty) (t : ℕ) :
    HasMonoSize (n+n) (edgeFun I (S.map ln)) t ↔ S.card * (Fintype.card K+2)-1 ≤ t := by
  classical
  have roweq (l) (hl : l ∈ S) (p) : I (pt p) (ln l) ↔ p ∈ arcPts l :=
    (rows l hl p).trans mem_arcPts.symm
  have total : (∑ l ∈ S, (arcPts l).card) + S.card = S.card * (Fintype.card K+2) := by
    simp [arcPts_card,Nat.mul_add]
    <;> ring
  constructor
  · intro hf
    let A := S.biUnion arcPts
    let support (p : (K × K) ⊕ Option K) := S.filter (fun l => p ∈ arcPts l)
    let B := A.filter (fun p => (support p).card = 2)
    have inSup (p l) : l ∈ support p ↔ l ∈ S ∧ p ∈ arcPts l := Finset.mem_filter
    have two (p) : (support p).card ≤ 2 := by
      by_contra! h
      obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp h
      exact arc_no_triple hab hac hbc p (mem_arcPts.mp ((inSup p a).mp ha).2)
        (mem_arcPts.mp ((inSup p b).mp hb).2) (mem_arcPts.mp ((inSup p c).mp hc).2)
    have sizes : (∑ l ∈ S, (arcPts l).card) = A.card+B.card := by
      calc
        _ = ∑ p ∈ A, (support p).card := by
          have he (p) : Finset.univ.filter (fun j => j ∈ S ∧ p ∈ arcPts j) = support p := by
            ext j; simp [support]
          simpa only [he] using Finset.sum_card_eq_sum_biUnion_card arcPts S
        _ = ∑ p ∈ A, (1 + if (support p).card = 2 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          obtain ⟨l,hl,hi⟩ := Finset.mem_biUnion.mp hp
          have pos := Finset.card_pos.mpr ⟨l,(inSup p l).mpr ⟨hl,hi⟩⟩
          have := two p
          split <;> omega
        _ = _ := by simp [B,Finset.sum_add_distrib,Finset.sum_boole]
    have privatePt (l) (hl : l ∈ S) : ∃ p, support p = {l} := by
      let priv := arcPts l \ (S.erase l).biUnion (fun a => arcPts l ∩ arcPts a)
      have cnt := projective_arc_private_card S l hl
      rw [arcPts_card] at cnt
      change priv.card + _ = _ at cnt
      have bound : S.card ≤ Fintype.card K + 1 := by simpa using S.card_le_univ
      have hs := Finset.card_pos.mpr hne
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < priv.card)
      obtain ⟨hi,hn⟩ := Finset.mem_sdiff.mp hp
      refine ⟨p, ?_⟩
      ext a
      rw [inSup,Finset.mem_singleton]
      refine ⟨fun ⟨ha,hpa⟩ => ?_, fun e => e ▸ ⟨hl,hi⟩⟩
      by_contra h
      exact hn (Finset.mem_biUnion.mpr ⟨a,Finset.mem_erase.mpr ⟨h,ha⟩,Finset.mem_inter.mpr ⟨hi,hpa⟩⟩)
    let leaf (l : Option K) := if h : l ∈ S then (privatePt l h).choose else Sum.inr none
    have leafEq (l) (hl : l ∈ S) : support (leaf l) = {l} := by
      simpa only [leaf,dif_pos hl] using (privatePt l hl).choose_spec
    let U := S.image leaf
    have leafInj : (↑S : Set (Option K)).InjOn leaf := by
      intro a ha b hb h
      simpa only [leafEq a ha,leafEq b hb,Finset.singleton_inj] using congrArg support h
    have dis : Disjoint U B := by
      apply Finset.disjoint_left.mpr
      rintro p hp hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
      have := (Finset.mem_filter.mp hb).2
      simp [leafEq a ha] at this
    have sub : U ∪ B ⊆ A := by
      intro p hp
      rcases Finset.mem_union.mp hp with hu|hb
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_biUnion.mpr ⟨l,hl,((inSup _ l).mp (by simp [leafEq l hl])).2⟩
      · exact (Finset.mem_filter.mp hb).1
    have inj : (↑(U ∪ B) : Set ((K × K) ⊕ Option K)).InjOn support := by
      intro p hp q hq eq
      by_cases b : p ∈ B
      · have card := (Finset.mem_filter.mp b).2
        obtain ⟨a,d,had,hs⟩ := Finset.card_eq_two.mp card
        have h1 : a ∈ support p := by simp [hs]
        have h2 : d ∈ support p := by simp [hs]
        exact (arc_pair_unique had).unique
          ⟨mem_arcPts.mp ((inSup p a).mp h1).2,mem_arcPts.mp ((inSup p d).mp h2).2⟩
          ⟨mem_arcPts.mp ((inSup q a).mp (eq ▸ h1)).2,mem_arcPts.mp ((inSup q d).mp (eq ▸ h2)).2⟩
      · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hp).resolve_right b)
        rcases Finset.mem_union.mp hq with hu|hb
        · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hu
          rw [leafEq a ha,leafEq d hd,Finset.singleton_inj] at eq
          rw [eq]
        · have := (Finset.mem_filter.mp hb).2
          simp [← eq,leafEq a ha] at this
    have lb := encoded_lower arcPts S pt ln I roweq (U ∪ B) sub
      ((hne.image leaf).mono (Finset.subset_union_left)) (by
        intro p hp q hq h
        by_contra! agree
        apply h (inj hp hq ?_)
        ext l
        simp only [inSup]
        exact and_congr_right (agree l)) hf
    have ucard : U.card = S.card := Finset.card_image_of_injOn leafInj
    rw [Finset.card_union_of_disjoint dis,ucard] at lb
    change A.card + _ ≤ _ at lb
    omega
  · intro ht
    have ub := encoded_upper arcPts S pt ln I roweq hne (fun l _ => Finset.card_pos.mp (by rw [arcPts_card]; omega))
    rw [total] at ub
    exact ub.mono ht

theorem deletion_1009 (hK : Fintype.card K = 1009) {l : Option K} (hl : l ∈ S)
    (hs : 2 ≤ S.card) {t : ℕ} (hf : HasMonoSize (n+n) (edgeFun I (S.map ln)) t) :
    ∃ u, HasMonoSize (n+n) (edgeFun I ((S.erase l).map ln)) u ∧ u+1011 ≤ t := by
  have lb := (arc_size_iff S pt ln I rows ⟨l,hl⟩ t).mp hf
  have hc := Finset.card_erase_of_mem hl
  have hn : (S.erase l).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨_,(arc_size_iff (S.erase l) pt ln I (fun a ha => rows a (Finset.mem_of_mem_erase ha)) hn _).mpr (le_refl _),?_⟩
  rw [hK] at lb ⊢
  omega

/-- The circuit witness and the inequality in the original deletion premise. -/
theorem arc_hdrop_1009 (hK : Fintype.card K = 1009) {l : Option K} (hl : l ∈ S)
    (hs : 2 ≤ S.card) (D : Circuit) (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S.map ln ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) :
    ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = edgeFun I ((S.map ln).erase (ln l)) x) ∧
      100 * E.size + 1009 ≤ 100 * D.size := by
  obtain ⟨u,hu,hsave⟩ := deletion_1009 S pt ln I rows hK hl hs
    (mono_size_of_exact I (S.map ln) D hm hex)
  obtain ⟨E,hE,hsize,heval⟩ := monotone2_of_has hu
  exact ⟨E,hE,by simpa only [Finset.map_erase] using heval,by omega⟩

omit rows in
/-- The two numerical thresholds on the same numbered inputs. -/
theorem full_and_erased_1009 (hK : Fintype.card K = 1009)
    (allRows : ∀ l p, I (pt p) (ln l) ↔ arcInc l p) (l : Option K) (t : ℕ) :
    (HasMonoSize (n+n) (edgeFun I (Finset.univ.map ln)) t ↔ 1021109 ≤ t) ∧
    (HasMonoSize (n+n) (edgeFun I ((Finset.univ.erase l).map ln)) t ↔ 1020098 ≤ t) := by
  have hcard : (Finset.univ : Finset (Option K)).card = 1010 := by simp [hK]
  have hmem : l ∈ (Finset.univ : Finset (Option K)) := Finset.mem_univ _
  have he := Finset.card_erase_of_mem hmem
  rw [hcard] at he
  have hne : (Finset.univ.erase l).Nonempty := Finset.card_pos.mp (by omega)
  constructor
  · simpa only [hK,hcard] using
      arc_size_iff Finset.univ pt ln I (fun a _ => allRows a) ⟨l,hmem⟩ t
  · simpa only [hK,he] using
      arc_size_iff (Finset.univ.erase l) pt ln I (fun a _ => allRows a) hne t

end Arc
end Onlyfr.PrivateArcExact
