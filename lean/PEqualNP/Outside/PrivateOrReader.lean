import PEqualNP.Outside.PrivateIncidenceDrop

namespace Onlyfr.PrivateOrReader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc
open Onlyfr.PrivateIncidenceDrop

/-- Changing only the marked inputs cannot affect other wires if their sole reader agrees. -/
theorem agree_of_one_reader {m : ℕ} {gs : List Gate} (hc : CleanL m gs)
    (x y : Fin m → Bool) (B : ℕ → Prop) (r o : ℕ) (ho : ¬ B o)
    (hxy : ∀ j : Fin m, ¬ B j → x j = y j)
    (hr : ∀ k w, Reads gs k w → B w → k = r)
    (hv : vl gs x (m+r) = vl gs y (m+r)) : vl gs x o = vl gs y o := by
  apply agree_B gs hc x y B (o+1) _ _ o (by omega) ho
  · intro j hj hB
    rw [vl_input gs x j hj, vl_input gs y j hj]
    exact hxy ⟨j,hj⟩ hB
  · intro k g hg _ _ h _
    obtain ⟨w, hw, hB⟩ := h
    exact hr k w ⟨g,hg,hw⟩ hB ▸ hv

theorem pair_edge_iff {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    (p a : Fin n) : edgeFun I S (pairInput p a) = true ↔ a ∈ S ∧ I p a := by
  rw [edgeFun_true]
  simp only [pair_point, pair_line, decide_eq_true_eq]
  constructor
  · rintro ⟨_, _, ha, hpa, rfl, rfl⟩
    exact ⟨ha,hpa⟩
  · exact fun h => ⟨p,a,h.1,h.2,rfl,rfl⟩

private theorem out_ne_line {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    {gs : List Gate} {o : ℕ} (hev : ∀ x, vl gs x o = edgeFun I S x) (a : Fin n) :
    o ≠ (Fin.natAdd n a : ℕ) := by
  intro he
  let x : Fin (n+n) → Bool := fun z => decide (z = Fin.natAdd n a)
  have ht : edgeFun I S x = true := by
    rw [← hev, he, vl_input gs x _ (Fin.natAdd n a).isLt]
    exact decide_eq_true (rfl : Fin.natAdd n a = Fin.natAdd n a)
  obtain ⟨p, _, _, _, hp, _⟩ := (edgeFun_true I S x).mp ht
  exact left_ne_right p a (of_decide_eq_true hp)

/-- If the two lines have different incidence at p, an OR of their inputs
cannot be the only gate reading either input. -/
theorem no_shared_or {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    {gs : List Gate} {o r : ℕ} {g : Gate} (hc : CleanL (n+n) gs)
    (hev : ∀ x, vl gs x o = edgeFun I S x)
    (p l a : Fin n) (hl : l ∈ S) (hpl : I p l) (hpa : ¬ I p a)
    (hg : gs[r]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [(Fin.natAdd n l : ℕ), (Fin.natAdd n a : ℕ)])
    (hrl : ∀ k, Reads gs k (Fin.natAdd n l) → k = r)
    (hra : ∀ k, Reads gs k (Fin.natAdd n a) → k = r) : False := by
  let B := fun j : ℕ => j = (Fin.natAdd n l : ℕ) ∨ j = (Fin.natAdd n a : ℕ)
  have ho : ¬ B o := fun h => h.elim (out_ne_line I S hev l) (out_ne_line I S hev a)
  have hh := agree_of_one_reader hc (pairInput p l) (pairInput p a) B r o ho (by
    intro j hj
    have hn (v : Fin n) (h : B (Fin.natAdd n v)) : j ≠ Fin.natAdd n v := by
      rintro rfl
      exact hj h
    simp only [pairInput, hn l (Or.inl rfl), hn a (Or.inr rfl), or_false]) (by
    intro k w hr hw
    rcases hw with e | e
    · exact hrl k (e ▸ hr)
    · exact hra k (e ▸ hr)) (by
    rw [vl_gate gs hc _ r g hg, vl_gate gs hc _ r g hg, hop, hin]
    simp only [List.map_cons, List.map_nil, vl_input gs _ _ (Fin.natAdd n l).isLt,
      vl_input gs _ _ (Fin.natAdd n a).isLt, pair_line]
    change GateOp.or.eval [pairInput p l (Fin.natAdd n l), pairInput p l (Fin.natAdd n a)] =
      GateOp.or.eval [pairInput p a (Fin.natAdd n l), pairInput p a (Fin.natAdd n a)]
    simp only [pair_line]; simp [GateOp.eval])
  rw [hev, hev] at hh
  exact hpa (((pair_edge_iff I S p a).mp (hh ▸ (pair_edge_iff I S p l).mpr ⟨hl,hpl⟩)).2)

/-- Before the first gate touching a marked input, unmarked wires are true
whenever all unmarked primary inputs are true. -/
private theorem prefix_true {m : ℕ} {gs : List Gate} (hc : MClean m gs)
    (B : ℕ → Prop) (r : ℕ) (hr : r < gs.length)
    (hfirst : ∀ k w, Reads gs k w → B w → r ≤ k)
    (x : Fin m → Bool) (hx : ∀ j : Fin m, ¬ B j → x j = true)
    (w : ℕ) (hw : w < m+r) (hb : ¬ B w) : vl gs x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h : w < m
    · rw [vl_input gs x w h]
      exact hx ⟨w,h⟩ hb
    obtain ⟨k,rfl⟩ : ∃ k, w = m+k := ⟨w-m, by omega⟩
    have hk : k < gs.length := by omega
    let g := gs[k]
    have hg : gs[k]? = some g := List.getElem?_eq_getElem hk
    obtain ⟨a,b,ha,hb',hin,hgate⟩ := Free.vl_bin hc.1 hc.2 hg
    have hv (j) (hj : j ∈ g.inputs) (hlt : j < m+k) : vl gs x j = true := by
      apply ih j hlt (by omega)
      intro hB
      have := hfirst k j ⟨g,hg,hj⟩ hB
      omega
    have h1 := hv a (by simp [hin]) ha
    have h2 := hv b (by simp [hin]) hb'
    rcases hgate with hgate | hgate <;> simp [hgate x,h1,h2]

def active {n : ℕ} (S : Finset (Fin n)) (w : ℕ) := ∃ a ∈ S, w = (Fin.natAdd n a : ℕ)

/-- The other operand of a first, sole OR reader must be an active line wire. -/
theorem active_partner {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    {gs : List Gate} {o r w : ℕ} {g : Gate} (hc : MClean (n+n) gs)
    (hev : ∀ x, vl gs x o = edgeFun I S x)
    (p l : Fin n) (hl : l ∈ S) (hp : I p l) (hg : gs[r]? = some g) (hop : g.op = .or)
    (hin : g.inputs = [(Fin.natAdd n l : ℕ),w] ∨ g.inputs = [w,(Fin.natAdd n l : ℕ)])
    (hfirst : ∀ k v, Reads gs k v → active S v → r ≤ k)
    (honly : ∀ k, Reads gs k (Fin.natAdd n l) → k = r) : active S w := by
  classical
  by_contra hn
  let i := Fin.natAdd n l
  let x : Fin (n+n) → Bool := fun j => decide (¬ active S j)
  let y := Function.update x i true
  have hwr : Reads gs r w := ⟨g,hg,by rcases hin with h|h <;> simp [h]⟩
  have hpoint : ¬ active S (Fin.castAdd n p) := by
    rintro ⟨a,_,ha⟩
    exact left_ne_right p a (Fin.ext ha)
  have hx : edgeFun I S x = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨_,a,ha,_,_,hav⟩ := (edgeFun_true I S x).mp hh
    exact (of_decide_eq_true hav) ⟨a,ha,rfl⟩
  have hy : edgeFun I S y = true := by
    apply (edgeFun_true I S y).mpr
    exact ⟨p,l,hl,hp,by rw [show y (Fin.castAdd n p) = x (Fin.castAdd n p) from Function.update_of_ne (left_ne_right p l) true x]; exact decide_eq_true hpoint,
      Function.update_self i true x⟩
  have htw (z : Fin (n+n) → Bool) (hz : ∀ j : Fin (n+n), ¬ active S j → z j = true) :
      vl gs z (n+n+r) = true := by
    have ht := prefix_true hc (active S) r (reads_len hwr) hfirst z hz w (reads_lt hc.1 hwr) hn
    rw [vl_gate gs hc.1 _ r g hg, hop]
    rcases hin with h|h <;> simp [h,GateOp.eval,ht]
  have eqr : vl gs x (n+n+r) = vl gs y (n+n+r) := by
    rw [htw x (by simp [x]), htw y (by
      intro j hj
      by_cases he : j = i
      · subst j; exact Function.update_self i true x
      · rw [show y j = x j from Function.update_of_ne he true x]
        exact decide_eq_true hj)]
  have hh := agree_of_one_reader hc.1 x y (fun j => j = (i : ℕ)) r o (out_ne_line I S hev l)
    (by intro j hj; exact (Function.update_of_ne (fun e => hj (congrArg Fin.val e)) true x).symm)
    (by intro k v hr he; exact honly k (he ▸ hr)) eqr
  rw [hev, hev, hx, hy] at hh
  contradiction

end Onlyfr.PrivateOrReader