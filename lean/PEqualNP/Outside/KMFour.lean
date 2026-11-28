import PEqualNP.Outside.KMTripleBound

namespace Onlyfr.KMFour
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.Helpers
open Onlyfr.PrivateIncidenceDrop Onlyfr.KMTripleBound

private def pair : Fin 6 → Finset (Fin 4) := ![{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}]
private def ringEdge (c : Fin 4 → Fin 4) (i : Fin 4) : Finset (Fin 4) := {c i,c (i+1)}

-- There are just three undirected four-cycles on four labelled vertices.
private def orders : List (Fin 4 → Fin 4) := [![0,1,2,3],![0,1,3,2],![0,2,1,3]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem classify : ∀ E : Finset (Fin 6), E.card = 4 →
    (∀ j ∈ E, ∀ v ∈ pair j, ∃ k ∈ E.erase j, v ∈ pair k) →
    ∃ c ∈ orders, ∀ i, ∃ j ∈ E, pair j = ringEdge c i := by decide +kernel

private def mid (i : Fin 4) : Fin 8 := ⟨2*i.val+1,by omega⟩
private def vert (i : Fin 4) : Fin 8 := ⟨2*i.val,by omega⟩
private def cyc (x : Fin 8 → Bool) := decide (∃ i j : Fin 8, (i.val+1)%8=j.val ∧ x i = true ∧ x j = true)
set_option maxRecDepth 10000 in
private theorem cycle (x : Fin 8 → Bool) : cyc x = true ↔ ∃ i, x (mid i) = true ∧ (x (vert i) = true ∨ x (vert (i+1)) = true) :=
    (by decide : ∀ x, cyc x = true ↔ ∃ i, x (mid i) = true ∧ (x (vert i) = true ∨ x (vert (i+1)) = true)) x
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem small_cycle {n t : ℕ} (J : Fin n → Fin n → Prop) [DecidableRel J]
    (T : Finset (Fin n)) (h4 : T.card = 4)
    (two : ∀ p ∈ T, (pts J p).card = 2)
    (different : ∀ p ∈ T, ∀ r ∈ T, pts J p = pts J r → p = r)
    (shared : ∀ p ∈ T, ∀ l ∈ pts J p, ∃ r ∈ T.erase p, l ∈ pts J r)
    (ht : HasMonoSize (n+n) (edgeFun J T) t) : 11 ≤ t := by
  classical
  let U := active J T
  have count := Finset.sum_card_eq_sum_biUnion_card (pts J) T
  rw [Finset.sum_const_nat two,h4] at count
  have ge (v) (hv : v ∈ U) : 2 ≤ (Finset.univ.filter (fun p => p ∈ T ∧ v ∈ pts J p)).card := by
    obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨r,hr,hrv⟩ := shared p hp v hv
    exact Finset.one_lt_card.mpr ⟨r,by simp [Finset.mem_of_mem_erase hr,hrv],p,by simp [hp,hv],Finset.ne_of_mem_erase hr⟩
  have small := Finset.sum_le_sum ge
  change _ ≤ ∑ v ∈ U, _ at small
  change 4*2 = ∑ v ∈ U, _ at count
  have same : (∑ v ∈ U, (Finset.univ.filter (fun p => p ∈ T ∧ v ∈ pts J p)).card) = 8 := by convert count.symm using 1
  rw [same] at small
  simp only [Finset.sum_const,nsmul_eq_mul] at small
  have size : Fintype.card U ≤ 4 := by rw [Fintype.card_coe]; exact Nat.le_of_mul_le_mul_right small (by decide)
  let tag := (Fintype.equivFin U).toEmbedding.trans (Fin.castLEEmb size)
  let lab (v : Fin n) := if h : v ∈ U then tag ⟨v,h⟩ else 0
  have memU (p : T) (v) (h : v ∈ pts J p) : v ∈ U := Finset.mem_biUnion.mpr ⟨p,p.property,h⟩
  have inj : (↑U : Set (Fin n)).InjOn lab := by
    intro v hv w hw e
    change v ∈ U at hv
    change w ∈ U at hw
    have h : tag ⟨v,hv⟩ = tag ⟨w,hw⟩ := by simpa only [lab,dite_eq_left hv,dite_eq_left hw] using e
    exact congrArg Subtype.val (tag.injective h)
  let row (p : T) := (pts J p).image lab
  have card (p : T) : (row p).card = 2 := by
    dsimp only [row]
    rw [Finset.card_image_of_injOn (fun v hv w hw => inj (memU p v hv) (memU p w hw)),two _ p.property]
  have enum : ∀ A : Finset (Fin 4), A.card = 2 → ∃ j, pair j = A := by decide
  choose code codeRow using fun p => enum (row p) (card p)
  have recover (p : T) {v} (hv : v ∈ U) : lab v ∈ row p ↔ v ∈ pts J p := by
    constructor
    · rintro h
      obtain ⟨w,hw,e⟩ := Finset.mem_image.mp h
      exact inj (memU p w hw) hv e ▸ hw
    · exact Finset.mem_image_of_mem _
  have ci : Function.Injective code := by
    intro p r eq
    have re : row p = row r := (codeRow p).symm.trans ((congrArg pair eq).trans (codeRow r))
    apply Subtype.ext
    apply different p p.property r r.property
    ext v
    by_cases hv : v ∈ U
    · rw [← recover p hv,← recover r hv,re]
    · exact iff_of_false (fun h => hv (memU p _ h)) (fun h => hv (memU r _ h))
  let E := Finset.univ.image code
  have ec : E.card = 4 := by simpa [E,Finset.card_image_of_injective _ ci]
  have repeated (j) (hj : j ∈ E) (v) (hv : v ∈ pair j) : ∃ k ∈ E.erase j, v ∈ pair k := by
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hj
    rw [codeRow] at hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨r,hr,hrw⟩ := shared p p.property w hw
    let r' : T := ⟨r,Finset.mem_of_mem_erase hr⟩
    refine ⟨code r',Finset.mem_erase.mpr ⟨fun e => Finset.ne_of_mem_erase hr (congrArg Subtype.val (ci e)),Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,?_⟩
    rw [codeRow]; exact Finset.mem_image_of_mem _ hrw
  obtain ⟨c,hc,allEdges⟩ := classify E ec repeated
  have cbij : Function.Bijective c := (by decide : ∀ c ∈ orders, Function.Bijective c) _ hc
  have edgeInj : Function.Injective (ringEdge c) := (by decide : ∀ c ∈ orders, Function.Injective (ringEdge c)) _ hc
  have choice (i) : ∃ p : T, row p = ringEdge c i := by
    obtain ⟨j,hj,h⟩ := allEdges i
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hj
    exact ⟨p,(codeRow p).symm.trans h⟩
  choose pick pickRow using choice
  have pinj : Function.Injective pick := fun i j e => edgeInj ((pickRow i).symm.trans ((congrArg row e).trans (pickRow j)))
  let pe := Equiv.ofBijective pick ((Fintype.bijective_iff_injective_and_card pick).mpr ⟨pinj,by simp [h4]⟩)
  let ce := Equiv.ofBijective c cbij
  let R (v : Fin n) := vert (ce.symm (lab v))
  let P (p : Fin n) := if h : p ∈ T then mid (pe.symm ⟨p,h⟩) else 0
  let wires : Fin (n+n) → Fin 8 := Fin.addCases R P
  have eq : (fun x => edgeFun J T (x ∘ wires)) = cyc := by
    funext x; apply Bool.eq_iff_iff.mpr
    rw [cycle,edgeFun_true]
    simp only [Function.comp_apply,wires,Fin.addCases_left,Fin.addCases_right]
    constructor
    · rintro ⟨v,p,hp,hi,hv,hy⟩
      let i := pe.symm ⟨p,hp⟩
      have ep : pick i = ⟨p,hp⟩ := pe.apply_symm_apply _
      have vv : v ∈ pts J p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
      have h : lab v ∈ row (pick i) := ep ▸ Finset.mem_image_of_mem _ vv
      rw [pickRow] at h
      refine ⟨i,by simpa only [P,dite_eq_left hp] using hy,?_⟩
      rcases Finset.mem_insert.mp h with h|h
      · left; simpa only [R,h,show ce.symm (c i) = i from ce.symm_apply_apply i] using hv
      · right; simpa only [R,Finset.mem_singleton.mp h,show ce.symm (c (i+1)) = i+1 from ce.symm_apply_apply _] using hv
    · rintro ⟨i,hy,hx⟩
      have hit (j) (hj : c j ∈ ringEdge c i) (h : x (vert j) = true) : ∃ v, J v (pick i) ∧ x (R v) = true := by
        rw [← pickRow] at hj
        obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hj
        exact ⟨v,(Finset.mem_filter.mp hv).2,by simpa only [R,eq,show ce.symm (c j) = j from ce.symm_apply_apply j] using h⟩
      obtain ⟨v,hv,hx⟩ := hx.elim (hit i (by simp [ringEdge])) (hit (i+1) (by simp [ringEdge]))
      exact ⟨v,pick i,(pick i).property,hv,hx,by simpa only [P,dite_eq_left (pick i).property,show pe.symm (pick i) = i from pe.symm_apply_apply i] using hy⟩
  have pr := PermInputs.relabel_size wires _ _ ht.has
  rw [eq] at pr
  have := (L106 8 t (by decide)).mp pr
  omega

theorem four_lower {n t : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (S T : Finset (Fin n)) (h4 : T.card = 4)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (sizes : ∀ p ∈ T, (sig I S p).card = 2 ∨ (sig I S p).card = 4)
    (ht : HasMonoSize (n+n) (edgeFun (fun l p => l ∈ S ∧ I p l) T) t) : 11 ≤ t := by
  classical
  let J (l p : Fin n) := l ∈ S ∧ I p l
  have eq (p) : pts J p = sig I S p := by ext l; simp [pts,sig,J]
  have ge (p) (hp : p ∈ T) : 2 ≤ (sig I S p).card := by rcases sizes p hp with e|e <;> omega
  by_cases priv : ∃ p ∈ T, ∃ l, J l p ∧ ∀ r ∈ T.erase p, ¬ J l r
  · obtain ⟨p,hp,l,hp',only⟩ := priv
    have hmem : l ∈ sig I S p := Finset.mem_filter.mpr hp'
    have hpos := ge p hp
    obtain ⟨k,hk⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hmem]; omega : 0 < ((sig I S p).erase l).card)
    have hc : (T.erase p).card = 3 := by rw [Finset.card_erase_of_mem hp,h4]
    obtain ⟨r,hr⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase p).card)
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (ge r (Finset.mem_of_mem_erase hr)))
    obtain ⟨u,hu,hle⟩ := Onlyfr.PrivatePointPhase.drop J T hp hp' only
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hk)) (Finset.ne_of_mem_erase hk)
      hr (Finset.mem_filter.mp hv) ht
    have := Onlyfr.KMTripleBound.wide_three I join S (T.erase p) hc (fun a ha => ge a (Finset.mem_of_mem_erase ha)) hu
    omega
  push Not at priv
  have two (p) (hp : p ∈ T) : (pts J p).card = 2 := by
    rw [eq]
    rcases sizes p hp with h|h
    · exact h
    let B := (T.erase p).biUnion (fun r => (sig I S p).filter (I r))
    have sub : sig I S p ⊆ B := by
      intro l hl
      obtain ⟨r,hr,hi⟩ := priv p hp l (Finset.mem_filter.mp hl)
      exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_filter.mpr ⟨hl,hi.2⟩⟩
    have small : B.card ≤ 3 := by
      calc
        _ ≤ ∑ r ∈ T.erase p, ((sig I S p).filter (I r)).card := Finset.card_biUnion_le
        _ ≤ ∑ _r ∈ T.erase p, 1 := Finset.sum_le_sum (fun r hr => by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          exact (join p r (Finset.ne_of_mem_erase hr).symm).unique
            ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2,(Finset.mem_filter.mp ha).2⟩
            ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2,(Finset.mem_filter.mp hb).2⟩)
        _ = 3 := by simp [Finset.card_erase_of_mem hp,h4]
    have := Finset.card_le_card sub
    omega
  apply small_cycle J T h4 two _ _ ht
  · intro p hp r _ e
    by_contra ne
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (by rw [two p hp]; decide)
    have both v (hv : v ∈ pts J p) : I p v ∧ I r v := by
      have hv' : v ∈ pts J r := e ▸ hv
      exact ⟨(Finset.mem_filter.mp hv).2.2,(Finset.mem_filter.mp hv').2.2⟩
    exact ab ((join p r ne).unique (both a ha) (both b hb))
  · intro p hp l hl
    obtain ⟨r,hr,hi⟩ := priv p hp l (Finset.mem_filter.mp hl).2
    exact ⟨r,hr,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩

end Onlyfr.KMFour
