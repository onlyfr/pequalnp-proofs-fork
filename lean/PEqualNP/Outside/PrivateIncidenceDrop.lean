import PEqualNP.Outside.PrivateGateDrop
import PEqualNP.Outside.PrivateLineAudit
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Onlyfr.PrivateIncidenceDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.Helpers.Readers
open Onlyfr.PrivateGateDrop

noncomputable def edgeFun {n : ℕ} (I : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (x : Fin (n+n) → Bool) : Bool := by
  classical
  exact decide (∃ p l, l ∈ S ∧ I p l ∧
    x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)

theorem edgeFun_true {n : ℕ} (I : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (x : Fin (n+n) → Bool) :
    edgeFun I S x = true ↔ ∃ p l, l ∈ S ∧ I p l ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true := by
  classical
  simp [edgeFun]

theorem left_ne_right {n : ℕ} (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  have := p.isLt
  omega

def pairInput {n : ℕ} (p l : Fin n) (z : Fin (n+n)) : Bool :=
  decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)

theorem pair_point {n : ℕ} (p l r : Fin n) :
    pairInput p l (Fin.castAdd n r) = decide (r = p) := by
  simp only [pairInput, left_ne_right, or_false, Fin.castAdd_inj]

theorem pair_line {n : ℕ} (p l a : Fin n) :
    pairInput p l (Fin.natAdd n a) = decide (a = l) := by
  have h := (left_ne_right p a).symm
  have he : Fin.natAdd n a = Fin.natAdd n l ↔ a = l :=
    ⟨fun h => Fin.natAdd_injective n n h, congrArg (Fin.natAdd n)⟩
  simp only [pairInput, h, false_or, he]

theorem edgeFun_zero {n : ℕ} (I : Fin n → Fin n → Prop) (S : Finset (Fin n)) :
    edgeFun I S (fun _ => false) = false := by
  classical
  simp [edgeFun]

theorem edgeFun_eq_of_points_lines {n : ℕ} (I : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (x y : Fin (n+n) → Bool)
    (hp : ∀ p, x (Fin.castAdd n p) = y (Fin.castAdd n p))
    (hl : ∀ l, x (Fin.natAdd n l) = y (Fin.natAdd n l)) : edgeFun I S x = edgeFun I S y := by
  classical
  simp only [edgeFun, hp, hl]

theorem mono_size_of_exact {n : ℕ} (I : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (D : Circuit) (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p l, l ∈ S ∧ I p l ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) :
    HasMonoSize (n+n) (edgeFun I S) D.size := by
  refine ⟨D, ?_, ?_, le_refl _, ?_⟩
  · intro g hg
    obtain ⟨ho, hi⟩ := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp id Or.inl, hi⟩
  · intro g hg he
    obtain ⟨ho, _⟩ := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> rw [ho] at he <;> cases he
  · intro x
    have hh := (hex x).trans (edgeFun_true I S x).symm
    change circuitFun (n+n) D x = edgeFun I S x
    cases hD : circuitFun (n+n) D x <;> cases hF : edgeFun I S x <;> simp_all

theorem monotone2_of_has {m s : ℕ} {f : (Fin m → Bool) → Bool}
    (h : HasMonoSize m f s) :
    ∃ E : Circuit, Monotone2 E ∧ E.size ≤ s ∧ ∀ x, circuitFun m E x = f x := by
  obtain ⟨E, hb, hn, hs, he⟩ := h
  refine ⟨E, ?_, hs, he⟩
  intro g hg
  obtain ⟨ho, hi⟩ := hb g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
  refine ⟨?_, hi⟩
  rcases ho with ho | ho | ho
  · exact Or.inl ho
  · exact Or.inr ho
  · exact False.elim (hn g hg ho)

theorem point_deps {n : ℕ} (I : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (l : Fin n) (P : Finset (Fin n))
    (hl : l ∈ S) (hpoints : ∀ p ∈ P, I p l)
    (A : Finset (Fin (n+n))) (hA : A ⊆ P.image (Fin.castAdd n))
    (i : Fin (n+n)) (hi : i ∈ P.image (Fin.castAdd n) \ A) :
    Dep (fun x => edgeFun I S (pin A x)) i := by
  classical
  have no_line (a : Fin n) : Fin.natAdd n a ∉ A := by
    intro ha
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (hA ha)
    exact left_ne_right p a hp
  obtain ⟨hiQ, hiA⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hiQ
  refine ⟨pairInput p l, ?_⟩
  have ht : edgeFun I S (pin A (pairInput p l)) = true := by
    apply (edgeFun_true I S _).mpr
    exact ⟨p, l, hl, hpoints p hp,
      by simp [pin, hiA, pair_point], by rw [pin, if_neg (no_line l), pair_line]; simp⟩
  have hz : edgeFun I S (pin A (Function.update (pairInput p l)
      (Fin.castAdd n p) (!(pairInput p l (Fin.castAdd n p))))) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨r, a, _, _, hr, _⟩ := (edgeFun_true I S _).mp hh
    by_cases he : r = p
    · subst r; simp [pin, pair_point] at hr
    · have he' : Fin.castAdd n r ≠ Fin.castAdd n p := fun h => he (Fin.castAdd_injective n n h)
      simp [pin, Function.update_of_ne he', pair_point, he] at hr
  dsimp only
  rw [hz, ht]
  decide

theorem private_points_and_line_save {n : ℕ} (I : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (l : Fin n) (P : Finset (Fin n)) (D : Circuit)
    (bonus : ℕ) (hbonus : bonus ≤ 1) (hkeep : 0 < bonus → ∃ p ∉ P, I p l) (hl : l ∈ S) (hprivate : ∀ p ∈ P, I p l ∧ ∀ a ∈ S.erase l, ¬ I p a)
    (hother : ∃ a ∈ S.erase l, ∃ r, I r a)
    (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) :
    ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase l ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      E.size + P.card + bonus ≤ D.size := by
  classical
  let Q : Finset (Fin (n+n)) := P.image (Fin.castAdd n)
  have hQcard : Q.card = P.card := Finset.card_image_of_injective _ (Fin.castAdd_injective n n)
  have no_line (A : Finset (Fin (n+n))) (hA : A ⊆ Q) (a : Fin n) : Fin.natAdd n a ∉ A := by
    intro ha
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (hA ha)
    exact left_ne_right p a hp
  have nc (A : Finset (Fin (n+n))) (hA : A ⊆ Q) :
      ∃ x y, edgeFun I S (pin A x) ≠ edgeFun I S (pin A y) := by
    obtain ⟨a, ha, r, hra⟩ := hother
    have hrP : r ∉ P := by
      intro hr
      exact (hprivate r hr).2 a ha hra
    have hrA : Fin.castAdd n r ∉ A := by
      intro hr
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp (hA hr)
      have hpr : p = r := Fin.castAdd_injective n n he
      exact hrP (hpr ▸ hp)
    refine ⟨pairInput r a, fun _ => false, ?_⟩
    have ht : edgeFun I S (pin A (pairInput r a)) = true := by
      apply (edgeFun_true I S _).mpr
      exact ⟨r, a, Finset.mem_of_mem_erase ha, hra,
        by simp [pin, hrA, pair_point], by rw [pin, if_neg (no_line A hA a), pair_line]; simp⟩
    have hz : pin A (fun _ => false) = fun _ => false := by funext z; simp [pin]
    rw [ht, hz, edgeFun_zero]
    decide
  have deps (A : Finset (Fin (n+n))) (hA : A ⊆ Q) (i : Fin (n+n)) (hi : i ∈ Q \ A) :
      Dep (fun x => edgeFun I S (pin A x)) i := by
    exact point_deps I S l P hl (fun p hp => (hprivate p hp).1) A hA i hi
  obtain ⟨t, ht, hf⟩ := many_inputs Q (edgeFun I S) D.size (mono_size_of_exact I S D hm hex) nc deps
  let f := fun x => edgeFun I S (pin Q x)
  have final_eq (x : Fin (n+n) → Bool) :
      f (Function.update x (Fin.natAdd n l) false) = edgeFun I (S.erase l) x := by
    change edgeFun I S (pin Q (Function.update x (Fin.natAdd n l) false)) = _
    apply Bool.eq_iff_iff.mpr
    rw [edgeFun_true, edgeFun_true]
    constructor
    · rintro ⟨p, a, ha, hpa, hp, hax⟩
      have hal : a ≠ l := by
        intro he
        subst a
        rw [pin, if_neg (no_line Q (fun _ h => h) l), Function.update_self] at hax
        cases hax
      have hpP : p ∉ P := fun h => (hprivate p h).2 a (Finset.mem_erase.mpr ⟨hal, ha⟩) hpa
      have hpQ : Fin.castAdd n p ∉ Q := by simpa [Q] using hpP
      refine ⟨p, a, Finset.mem_erase.mpr ⟨hal, ha⟩, hpa, ?_, ?_⟩
      · rw [pin, if_neg hpQ, Function.update_of_ne (left_ne_right p l)] at hp
        exact hp
      · have he : Fin.natAdd n a ≠ Fin.natAdd n l := fun h => hal (Fin.natAdd_injective n n h)
        rw [pin, if_neg (no_line Q (fun _ h => h) a), Function.update_of_ne he] at hax
        exact hax
    · rintro ⟨p, a, ha, hpa, hp, hax⟩
      have hpP : p ∉ P := fun h => (hprivate p h).2 a ha hpa
      have hpQ : Fin.castAdd n p ∉ Q := by simpa [Q] using hpP
      have hal : a ≠ l := Finset.ne_of_mem_erase ha
      have he : Fin.natAdd n a ≠ Fin.natAdd n l := fun h => hal (Fin.natAdd_injective n n h)
      refine ⟨p, a, Finset.mem_of_mem_erase ha, hpa, ?_, ?_⟩
      · rw [pin, if_neg hpQ, Function.update_of_ne (left_ne_right p l)]
        exact hp
      · rw [pin, if_neg (no_line Q (fun _ h => h) a), Function.update_of_ne he]
        exact hax
  have hnc : ∃ x y, f (Function.update x (Fin.natAdd n l) false) ≠
      f (Function.update y (Fin.natAdd n l) false) := by
    obtain ⟨a, ha, r, hra⟩ := hother
    refine ⟨pairInput r a, fun _ => false, ?_⟩
    rw [final_eq, final_eq, edgeFun_zero]
    have hh : edgeFun I (S.erase l) (pairInput r a) = true := by
      exact (edgeFun_true I _ _).mpr ⟨r, a, ha, hra, by rw [pair_point]; simp, by rw [pair_line]; simp⟩
    rw [hh]
    decide
  obtain ⟨u, hu, hres⟩ : ∃ u,
      u + bonus ≤ t ∧
      HasMonoSize (n+n) (fun x => f (Function.update x (Fin.natAdd n l) false)) u := by
    by_cases hb : bonus = 0
    · exact ⟨t, by omega, restrict_input (n+n) t f (Fin.natAdd n l) false hf hnc⟩
    · have hleft := hkeep (by omega)
      rw [show bonus = 1 by omega]
      apply one_input _ _ _ _ _ hf _ hnc
      obtain ⟨p, hp, hpl⟩ := hleft
      refine ⟨pairInput p l, ?_⟩
      have hpQ : Fin.castAdd n p ∉ Q := by simpa [Q] using hp
      have ht : f (pairInput p l) = true := (edgeFun_true I S _).mpr
        ⟨p, l, hl, hpl, by simp [pin, hpQ, pair_point],
          by rw [pin, if_neg (no_line Q (fun _ h => h) l), pair_line]; simp⟩
      have hz : edgeFun I (S.erase l) (pairInput p l) = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        obtain ⟨_, a, ha, _, _, hax⟩ := (edgeFun_true I _ _).mp hh
        rw [pair_line] at hax
        exact (Finset.ne_of_mem_erase ha) (of_decide_eq_true hax)
      dsimp only
      rw [pair_line p l l, show (!(decide (l = l))) = false by simp]
      change f (Function.update (pairInput p l) (Fin.natAdd n l) false) ≠ f (pairInput p l)
      rw [final_eq, hz, ht]
      decide
  have heq : (fun x => f (Function.update x (Fin.natAdd n l) false)) = edgeFun I (S.erase l) :=
    funext final_eq
  rw [heq] at hres
  obtain ⟨E, hE, hs, hev⟩ := monotone2_of_has hres
  refine ⟨E, hE, fun x => ?_, ?_⟩
  · rw [hev x, edgeFun_true]
  · rw [hQcard] at ht
    omega

theorem private_points_save {n : ℕ} (I : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (l : Fin n) (P : Finset (Fin n)) (D : Circuit)
    (hl : l ∈ S) (hprivate : ∀ p ∈ P, I p l ∧ ∀ a ∈ S.erase l, ¬ I p a)
    (hother : ∃ a ∈ S.erase l, ∃ r, I r a)
    (hm : Monotone2 D)
    (hex : ∀ x, circuitFun (n+n) D x = true ↔ ∃ p a, a ∈ S ∧ I p a ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) :
    ∃ E : Circuit, Monotone2 E ∧
      (∀ x, circuitFun (n+n) E x = true ↔ ∃ p a, a ∈ S.erase l ∧ I p a ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n a) = true) ∧
      E.size + P.card ≤ D.size := by
  classical
  obtain ⟨E, hmE, he, hs⟩ := private_points_and_line_save I S l P D 0 (by decide) (by omega) hl hprivate hother hm hex
  exact ⟨E, hmE, he, by omega⟩

end Onlyfr.PrivateIncidenceDrop

