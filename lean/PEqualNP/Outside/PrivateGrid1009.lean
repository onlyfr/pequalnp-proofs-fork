import PEqualNP.Outside.PrivateGridMatching

namespace Onlyfr.PrivateGrid1009
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.Helpers.Readers Onlyfr.PrivateIncidenceDrop
open Onlyfr.PrivateGridPin Onlyfr.PrivateGridMatching

abbrev Axis := Fin 1001
abbrev Crossing := Axis × Axis
/-- Active point inputs: all affine crossings, eight private affine points
per line, and two independent points at infinity. -/
abbrev Point := Crossing ⊕ ((Bool × Axis × Fin 8) ⊕ Bool)
abbrev N := Fintype.card Point
noncomputable def idx := Fintype.equivFin Point
noncomputable def cross (i : Crossing) : Fin N := idx (.inl i)
noncomputable def priv (v : Bool) (a : Axis) (k : Fin 8) : Fin N := idx (.inr (.inl (v,a,k)))
noncomputable def hub (v : Bool) : Fin N := idx (.inr (.inr v))
noncomputable def line (v : Bool) (a : Axis) := priv v a 0
noncomputable def lines : Finset (Fin N) := (Finset.univ.image (line false)) ∪ (Finset.univ.image (line true))

def onLine (p : Point) (v : Bool) (a : Axis) : Prop :=
  match p with
  | .inl (i,j) => (if v then j else i) = a
  | .inr (.inl (w,h,_)) => w=v ∧ h=a
  | .inr (.inr w) => w=v

noncomputable def inc (p l : Fin N) : Prop :=
  match idx.symm l with
  | .inr (.inl (v,a,_)) => onLine (idx.symm p) v a
  | _ => False

@[simp] theorem line_mem (v : Bool) (a : Axis) : line v a ∈ lines := by
  cases v <;> simp [lines,Finset.mem_image]
@[simp] theorem at_line (q : Point) (v : Bool) (a : Axis) :
    inc (idx q) (line v a) ↔ onLine q v a := by simp [inc,line,priv]
theorem sep (i j : Crossing) (ne : i ≠ j) : ∃ l ∈ lines, inc (cross i) l ∧ ¬ inc (cross j) l := by
  apply grid_separates inc lines cross (line false) (line true) (line_mem _) (line_mem _) _ _ i j ne
  · intro z a; rcases z with ⟨b,c⟩; simp [cross,onLine]
  · intro z a; rcases z with ⟨b,c⟩; simp [cross,onLine]

private theorem active_form {l : Fin N} (hl : l ∈ lines) : ∃ v a, l = line v a := by
  rcases Finset.mem_union.mp hl with h|h <;> obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h
  · exact ⟨false,a,rfl⟩
  · exact ⟨true,a,rfl⟩

private theorem private_row (i : Crossing) (k : Fin 8) :
    ∀ v ∈ lines.erase (line false i.1), ¬ off inc (cross i) (priv false i.1 k) v := by
  intro v hv h
  obtain ⟨d,a,rfl⟩ := active_form (Finset.mem_of_mem_erase hv)
  have eq := (at_line _ _ _).mp h.2
  change false=d ∧ i.1=a at eq
  exact Finset.ne_of_mem_erase hv (by rw [←eq.1,←eq.2])

noncomputable def eight (i : Crossing) : EightPrivate inc lines (line false i.1) (cross i) := by
  classical
  let P := (Finset.univ.erase (0 : Fin 8)).image (priv false i.1)
  have inj : Function.Injective (priv false i.1) := by
    intro a b e
    simpa [priv] using e
  have row (k : Fin 8) : off inc (cross i) (priv false i.1 k) (line false i.1) := by
    constructor
    · simp [priv,cross]
    · simp [priv,onLine]
  refine { seven := P, card := ?_, last := priv false i.1 0, keep := hub false,
           survivor := line true i.2, point := priv true i.2 0,
           active := line_mem .., lastOn := row _, privateLast := private_row i _,
           different := ?_, keepOn := ?_, survived := ?_, edge := ?_,
           lastOut := ?_, keepOut := ?_, privateSeven := ?_ }
  · rw [show P.card = (Finset.univ.erase (0 : Fin 8)).card from Finset.card_image_of_injective _ inj]
    simp
  · simp [hub,priv]
  · exact ⟨by simp [hub,cross],by simp [hub,onLine]⟩
  · exact Finset.mem_erase.mpr ⟨by simp [line,priv],line_mem ..⟩
  · exact ⟨by simp [priv,cross],by simp [priv,onLine]⟩
  · intro h
    obtain ⟨k,hk,e⟩ := Finset.mem_image.mp h
    exact Finset.ne_of_mem_erase hk (inj e)
  · intro h
    obtain ⟨k,_,e⟩ := Finset.mem_image.mp h
    simp [priv,hub] at e
  · intro q h
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp h
    exact ⟨row k,private_row i k⟩

theorem twin (i : Crossing) : ∃ b, b ≠ cross i ∧
    (∀ a ∈ lines.erase (line false i.1), inc (cross i) a ↔ inc b a) ∧
    ∃ a ∈ lines.erase (line false i.1), inc b a := by
  refine ⟨priv true i.2 0,by simp [priv,cross],?_,line true i.2,
    Finset.mem_erase.mpr ⟨by simp [line,priv],line_mem ..⟩,by simp [priv,onLine]⟩
  intro a ha
  obtain ⟨v,c,rfl⟩ := active_form (Finset.mem_of_mem_erase ha)
  cases v with
  | false =>
    have ne : i.1 ≠ c := fun h => Finset.ne_of_mem_erase ha (h ▸ rfl)
    rcases i with ⟨u,v⟩
    simpa [cross,priv,onLine] using ne
  | true => rcases i with ⟨u,v⟩; simp [cross,priv,onLine]

set_option maxRecDepth 4096 in
/-- In a least circuit, if no horizontal deletion saves eleven gates, all
1,002,001 crossing readers have pairwise distinct direct consumers. -/
theorem matched_under_ten {gs : List Gate} {o : ℕ} (ho : o < gs.length)
    (least : MLeast (N+N) (edgeFun inc lines) gs (N+N+o))
    (e : Axis → ℕ) (ten : ∀ a, gs.length ≤ e a+10)
    (emin : ∀ a s, HasMonoSize (N+N) (edgeFun inc (lines.erase (line false a))) s → e a ≤ s) :
    ∃ r t f : Crossing → ℕ, Function.Injective f ∧
      ∀ i, OrRd gs (r i) (Fin.castAdd N (cross i)) (t i) ∧
        (∀ k, Reads gs k (Fin.castAdd N (cross i)) → k=r i) ∧ Reads gs (f i) (N+N+r i) :=
  ten_matching (J := Crossing) (n := N) (gs := gs) inc lines (fun i => line false i.1) cross o (fun i => e i.1)
    ho least sep (fun i => ten i.1) (fun i => emin i.1) eight twin

end Onlyfr.PrivateGrid1009
