import PEqualNP.Outside.PrivateArcMarginal
import PEqualNP.Outside.PrivateTwoGateDrop

namespace Onlyfr.PrivatePointPhase
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.Helpers.Readers
open Onlyfr.PrivateIncidenceDrop Onlyfr.PrivateGateDrop

/-- Pin the private point in its expensive phase, then turn off its still
essential line. Both point phases compute the same function after the line pin. -/
theorem drop {n s : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n))
    {l p r a v : Fin n} (hl : l ∈ S) (hp : I p l)
    (priv : ∀ c ∈ S.erase l, ¬ I p c) (hr : I r l) (hrp : r ≠ p)
    (ha : a ∈ S.erase l) (hv : I v a) (hf : HasMonoSize (n+n) (edgeFun I S) s) :
    ∃ u, HasMonoSize (n+n) (edgeFun I (S.erase l)) u ∧ u+3 ≤ s := by
  classical
  let i := Fin.castAdd n p
  let j := Fin.natAdd n l
  let f (b : Bool) (x : Fin (n+n) → Bool) := edgeFun I S (Function.update x i b)
  have eq (b x) : f b (Function.update x j false) = edgeFun I (S.erase l) x := by
    unfold f
    rw [Function.update_comm (left_ne_right p l).symm,Onlyfr.PrivateTwoGateDrop.erase_eq]
    apply Bool.eq_iff_iff.mpr
    simp only [edgeFun_true]
    constructor <;> rintro ⟨w,c,hc,hi,hw,hy⟩
    all_goals
      have hwp : w ≠ p := by rintro rfl; exact priv c hc hi
      have hwi : Fin.castAdd n w ≠ Fin.castAdd n p := fun e => hwp (Fin.castAdd_injective n n e)
      have hci : Fin.natAdd n c ≠ Fin.castAdd n p := (left_ne_right p c).symm
      exact ⟨w,c,hc,hi,by simpa only [Function.update_of_ne hwi] using hw,by simpa only [Function.update_of_ne hci] using hy⟩
  have dep : Dep (edgeFun I S) i := by
    have h := point_deps I S l {p} hl (by simpa using hp) ∅ (Finset.empty_subset _) i (by simp [i])
    simpa [pin_empty] using h
  have nc : ∃ x y, edgeFun I (S.erase l) x ≠ edgeFun I (S.erase l) y := by
    exact ⟨pairInput v a,fun _ => false,by rw [(Onlyfr.PrivateOrReader.pair_edge_iff I _ _ _).mpr ⟨ha,hv⟩,edgeFun_zero]; decide⟩
  obtain ⟨x,y,hxy⟩ := nc
  have both (b) : f b (Function.update x j false) ≠ f b (Function.update y j false) := by
    simpa only [eq] using hxy
  obtain ⟨b,t,ht,hm⟩ := Onlyfr.PrivateArcMarginal.expensive_phase i dep hf
    (fun b => ⟨_,_,both b⟩)
  have line : Dep (f b) j := by
    refine ⟨pairInput r l,?_⟩
    have yes : f b (pairInput r l) = true := by
      apply (edgeFun_true _ _ _).mpr
      exact ⟨r,l,hl,hr,by rw [Function.update_of_ne (show Fin.castAdd n r ≠ i from fun e => hrp (Fin.castAdd_injective n n e)),pair_point]; simp,
        by rw [Function.update_of_ne (left_ne_right p l).symm,pair_line]; simp⟩
    have no : edgeFun I (S.erase l) (pairInput r l) ≠ true := fun h =>
      Finset.notMem_erase _ _ ((Onlyfr.PrivateOrReader.pair_edge_iff _ _ _ _).mp h).1
    have hj : pairInput r l j = true := (pair_line r l l).trans (by simp)
    rw [hj,Bool.not_true,eq,yes]
    exact no
  obtain ⟨u,hu,hu'⟩ := one_input _ t (f b) j false hm line ⟨x,y,both b⟩
  exact ⟨u,(funext (eq b)) ▸ hu',by omega⟩

end Onlyfr.PrivatePointPhase


