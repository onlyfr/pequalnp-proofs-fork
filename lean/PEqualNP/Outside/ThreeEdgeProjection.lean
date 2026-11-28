import PEqualNP.Outside.ThreeEdgeTypes

namespace Onlyfr.ThreeEdgeProjection

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem covers (b01 b02 b03 b04 b05 b12 b13 b14 b15 b23 b24 b25 b34 b35 b45 : Bool) :
    ((b01 ≠ true)) →
    ((b23 ≠ true)) →
    ((b45 ≠ true)) →
    (((b02 = true) → (b13 ≠ true)) ∧ ((b03 = true) → (b12 ≠ true))) →
    (((b04 = true) → (b15 ≠ true)) ∧ ((b05 = true) → (b14 ≠ true))) →
    (((b24 = true) → (b35 ≠ true)) ∧ ((b25 = true) → (b34 ≠ true))) →
    ((((b01 = true) ∧ (b12 = true)) → (b02 = true)) ∧ (((b02 = true) ∧ (b12 = true)) → (b01 = true)) ∧ (((b01 = true) ∧ (b02 = true)) → (b12 = true))) →
    ((((b01 = true) ∧ (b13 = true)) → (b03 = true)) ∧ (((b03 = true) ∧ (b13 = true)) → (b01 = true)) ∧ (((b01 = true) ∧ (b03 = true)) → (b13 = true))) →
    ((((b01 = true) ∧ (b14 = true)) → (b04 = true)) ∧ (((b04 = true) ∧ (b14 = true)) → (b01 = true)) ∧ (((b01 = true) ∧ (b04 = true)) → (b14 = true))) →
    ((((b01 = true) ∧ (b15 = true)) → (b05 = true)) ∧ (((b05 = true) ∧ (b15 = true)) → (b01 = true)) ∧ (((b01 = true) ∧ (b05 = true)) → (b15 = true))) →
    ((((b02 = true) ∧ (b23 = true)) → (b03 = true)) ∧ (((b03 = true) ∧ (b23 = true)) → (b02 = true)) ∧ (((b02 = true) ∧ (b03 = true)) → (b23 = true))) →
    ((((b02 = true) ∧ (b24 = true)) → (b04 = true)) ∧ (((b04 = true) ∧ (b24 = true)) → (b02 = true)) ∧ (((b02 = true) ∧ (b04 = true)) → (b24 = true))) →
    ((((b02 = true) ∧ (b25 = true)) → (b05 = true)) ∧ (((b05 = true) ∧ (b25 = true)) → (b02 = true)) ∧ (((b02 = true) ∧ (b05 = true)) → (b25 = true))) →
    ((((b03 = true) ∧ (b34 = true)) → (b04 = true)) ∧ (((b04 = true) ∧ (b34 = true)) → (b03 = true)) ∧ (((b03 = true) ∧ (b04 = true)) → (b34 = true))) →
    ((((b03 = true) ∧ (b35 = true)) → (b05 = true)) ∧ (((b05 = true) ∧ (b35 = true)) → (b03 = true)) ∧ (((b03 = true) ∧ (b05 = true)) → (b35 = true))) →
    ((((b04 = true) ∧ (b45 = true)) → (b05 = true)) ∧ (((b05 = true) ∧ (b45 = true)) → (b04 = true)) ∧ (((b04 = true) ∧ (b05 = true)) → (b45 = true))) →
    ((((b12 = true) ∧ (b23 = true)) → (b13 = true)) ∧ (((b13 = true) ∧ (b23 = true)) → (b12 = true)) ∧ (((b12 = true) ∧ (b13 = true)) → (b23 = true))) →
    ((((b12 = true) ∧ (b24 = true)) → (b14 = true)) ∧ (((b14 = true) ∧ (b24 = true)) → (b12 = true)) ∧ (((b12 = true) ∧ (b14 = true)) → (b24 = true))) →
    ((((b12 = true) ∧ (b25 = true)) → (b15 = true)) ∧ (((b15 = true) ∧ (b25 = true)) → (b12 = true)) ∧ (((b12 = true) ∧ (b15 = true)) → (b25 = true))) →
    ((((b13 = true) ∧ (b34 = true)) → (b14 = true)) ∧ (((b14 = true) ∧ (b34 = true)) → (b13 = true)) ∧ (((b13 = true) ∧ (b14 = true)) → (b34 = true))) →
    ((((b13 = true) ∧ (b35 = true)) → (b15 = true)) ∧ (((b15 = true) ∧ (b35 = true)) → (b13 = true)) ∧ (((b13 = true) ∧ (b15 = true)) → (b35 = true))) →
    ((((b14 = true) ∧ (b45 = true)) → (b15 = true)) ∧ (((b15 = true) ∧ (b45 = true)) → (b14 = true)) ∧ (((b14 = true) ∧ (b15 = true)) → (b45 = true))) →
    ((((b23 = true) ∧ (b34 = true)) → (b24 = true)) ∧ (((b24 = true) ∧ (b34 = true)) → (b23 = true)) ∧ (((b23 = true) ∧ (b24 = true)) → (b34 = true))) →
    ((((b23 = true) ∧ (b35 = true)) → (b25 = true)) ∧ (((b25 = true) ∧ (b35 = true)) → (b23 = true)) ∧ (((b23 = true) ∧ (b25 = true)) → (b35 = true))) →
    ((((b24 = true) ∧ (b45 = true)) → (b25 = true)) ∧ (((b25 = true) ∧ (b45 = true)) → (b24 = true)) ∧ (((b24 = true) ∧ (b25 = true)) → (b45 = true))) →
    ((((b34 = true) ∧ (b45 = true)) → (b35 = true)) ∧ (((b35 = true) ∧ (b45 = true)) → (b34 = true)) ∧ (((b34 = true) ∧ (b35 = true)) → (b45 = true))) →
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b04 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b05 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b04 ≠ true) ∧ (b12 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b03 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b03 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b03 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b03 ≠ true) ∧ (b04 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b04 ≠ true) ∧ (b12 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b13 ≠ true) ∧ (b15 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b13 ≠ true) ∧ (b14 ≠ true) ∧ (b24 ≠ true) ∧ (b34 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b15 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b35 ≠ true)) ∨
    ((b02 ≠ true) ∧ (b03 ≠ true) ∧ (b04 ≠ true) ∧ (b05 ≠ true) ∧ (b12 ≠ true) ∧ (b14 ≠ true) ∧ (b24 ≠ true) ∧ (b25 ≠ true) ∧ (b34 ≠ true)) := by
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  all_goals cases b01 <;> (try simp at *)
  all_goals cases b23 <;> (try simp at *)
  all_goals cases b45 <;> (try simp at *)
  all_goals cases b02 <;> (try simp at *)
  all_goals cases b03 <;> (try simp at *)
  all_goals cases b12 <;> (try simp at *)
  all_goals cases b13 <;> (try simp at *)
  all_goals cases b04 <;> (try simp at *)
  all_goals cases b05 <;> (try simp at *)
  all_goals cases b14 <;> (try simp at *)
  all_goals cases b15 <;> (try simp at *)
  all_goals cases b24 <;> (try simp at *)
  all_goals cases b25 <;> (try simp at *)
  all_goals cases b34 <;> (try simp at *)
  all_goals cases b35 <;> (try simp at *)

set_option maxHeartbeats 4000000 in
theorem colorable {α : Type*} (v : Fin 6 → α)
    (hpair : ∀ i, (ends v i).1 ≠ (ends v i).2)
    (hdiff : ∀ i j, i ≠ j → ¬ ((ends v i = ends v j) ∨ (ends v i = (ends v j).swap))) :
    ∃ star, ∃ c : α → Fin 4, ∀ i,
      (c (ends v i).1,c (ends v i).2) = colors star i ∨
      (c (ends v i).2,c (ends v i).1) = colors star i := by
  classical
  have h0 := hpair 0
  have h1 := hpair 1
  have h2 := hpair 2
  have h01 := hdiff 0 1 (by decide)
  have h02 := hdiff 0 2 (by decide)
  have h12 := hdiff 1 2 (by decide)
  simp [ends,Prod.ext_iff,Prod.swap] at h0 h1 h2 h01 h02 h12
  have cover :
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 3 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 4 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 3 ∧ v 1 ≠ v 4 ∧ v 2 ≠ v 4 ∧ v 3 ≠ v 4 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 5 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 5) ∨
    (v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 0 ≠ v 4 ∧ v 0 ≠ v 5 ∧ v 1 ≠ v 2 ∧ v 1 ≠ v 4 ∧ v 2 ≠ v 4 ∧ v 2 ≠ v 5 ∧ v 3 ≠ v 4) := by
    have eq012 : ((v 0 = v 1 ∧ v 1 = v 2) → v 0 = v 2) ∧ ((v 0 = v 2 ∧ v 1 = v 2) → v 0 = v 1) ∧ ((v 0 = v 1 ∧ v 0 = v 2) → v 1 = v 2) := by grind
    have eq013 : ((v 0 = v 1 ∧ v 1 = v 3) → v 0 = v 3) ∧ ((v 0 = v 3 ∧ v 1 = v 3) → v 0 = v 1) ∧ ((v 0 = v 1 ∧ v 0 = v 3) → v 1 = v 3) := by grind
    have eq014 : ((v 0 = v 1 ∧ v 1 = v 4) → v 0 = v 4) ∧ ((v 0 = v 4 ∧ v 1 = v 4) → v 0 = v 1) ∧ ((v 0 = v 1 ∧ v 0 = v 4) → v 1 = v 4) := by grind
    have eq015 : ((v 0 = v 1 ∧ v 1 = v 5) → v 0 = v 5) ∧ ((v 0 = v 5 ∧ v 1 = v 5) → v 0 = v 1) ∧ ((v 0 = v 1 ∧ v 0 = v 5) → v 1 = v 5) := by grind
    have eq023 : ((v 0 = v 2 ∧ v 2 = v 3) → v 0 = v 3) ∧ ((v 0 = v 3 ∧ v 2 = v 3) → v 0 = v 2) ∧ ((v 0 = v 2 ∧ v 0 = v 3) → v 2 = v 3) := by grind
    have eq024 : ((v 0 = v 2 ∧ v 2 = v 4) → v 0 = v 4) ∧ ((v 0 = v 4 ∧ v 2 = v 4) → v 0 = v 2) ∧ ((v 0 = v 2 ∧ v 0 = v 4) → v 2 = v 4) := by grind
    have eq025 : ((v 0 = v 2 ∧ v 2 = v 5) → v 0 = v 5) ∧ ((v 0 = v 5 ∧ v 2 = v 5) → v 0 = v 2) ∧ ((v 0 = v 2 ∧ v 0 = v 5) → v 2 = v 5) := by grind
    have eq034 : ((v 0 = v 3 ∧ v 3 = v 4) → v 0 = v 4) ∧ ((v 0 = v 4 ∧ v 3 = v 4) → v 0 = v 3) ∧ ((v 0 = v 3 ∧ v 0 = v 4) → v 3 = v 4) := by grind
    have eq035 : ((v 0 = v 3 ∧ v 3 = v 5) → v 0 = v 5) ∧ ((v 0 = v 5 ∧ v 3 = v 5) → v 0 = v 3) ∧ ((v 0 = v 3 ∧ v 0 = v 5) → v 3 = v 5) := by grind
    have eq045 : ((v 0 = v 4 ∧ v 4 = v 5) → v 0 = v 5) ∧ ((v 0 = v 5 ∧ v 4 = v 5) → v 0 = v 4) ∧ ((v 0 = v 4 ∧ v 0 = v 5) → v 4 = v 5) := by grind
    have eq123 : ((v 1 = v 2 ∧ v 2 = v 3) → v 1 = v 3) ∧ ((v 1 = v 3 ∧ v 2 = v 3) → v 1 = v 2) ∧ ((v 1 = v 2 ∧ v 1 = v 3) → v 2 = v 3) := by grind
    have eq124 : ((v 1 = v 2 ∧ v 2 = v 4) → v 1 = v 4) ∧ ((v 1 = v 4 ∧ v 2 = v 4) → v 1 = v 2) ∧ ((v 1 = v 2 ∧ v 1 = v 4) → v 2 = v 4) := by grind
    have eq125 : ((v 1 = v 2 ∧ v 2 = v 5) → v 1 = v 5) ∧ ((v 1 = v 5 ∧ v 2 = v 5) → v 1 = v 2) ∧ ((v 1 = v 2 ∧ v 1 = v 5) → v 2 = v 5) := by grind
    have eq134 : ((v 1 = v 3 ∧ v 3 = v 4) → v 1 = v 4) ∧ ((v 1 = v 4 ∧ v 3 = v 4) → v 1 = v 3) ∧ ((v 1 = v 3 ∧ v 1 = v 4) → v 3 = v 4) := by grind
    have eq135 : ((v 1 = v 3 ∧ v 3 = v 5) → v 1 = v 5) ∧ ((v 1 = v 5 ∧ v 3 = v 5) → v 1 = v 3) ∧ ((v 1 = v 3 ∧ v 1 = v 5) → v 3 = v 5) := by grind
    have eq145 : ((v 1 = v 4 ∧ v 4 = v 5) → v 1 = v 5) ∧ ((v 1 = v 5 ∧ v 4 = v 5) → v 1 = v 4) ∧ ((v 1 = v 4 ∧ v 1 = v 5) → v 4 = v 5) := by grind
    have eq234 : ((v 2 = v 3 ∧ v 3 = v 4) → v 2 = v 4) ∧ ((v 2 = v 4 ∧ v 3 = v 4) → v 2 = v 3) ∧ ((v 2 = v 3 ∧ v 2 = v 4) → v 3 = v 4) := by grind
    have eq235 : ((v 2 = v 3 ∧ v 3 = v 5) → v 2 = v 5) ∧ ((v 2 = v 5 ∧ v 3 = v 5) → v 2 = v 3) ∧ ((v 2 = v 3 ∧ v 2 = v 5) → v 3 = v 5) := by grind
    have eq245 : ((v 2 = v 4 ∧ v 4 = v 5) → v 2 = v 5) ∧ ((v 2 = v 5 ∧ v 4 = v 5) → v 2 = v 4) ∧ ((v 2 = v 4 ∧ v 2 = v 5) → v 4 = v 5) := by grind
    have eq345 : ((v 3 = v 4 ∧ v 4 = v 5) → v 3 = v 5) ∧ ((v 3 = v 5 ∧ v 4 = v 5) → v 3 = v 4) ∧ ((v 3 = v 4 ∧ v 3 = v 5) → v 4 = v 5) := by grind
    have hc := covers (decide (v 0 = v 1)) (decide (v 0 = v 2)) (decide (v 0 = v 3)) (decide (v 0 = v 4)) (decide (v 0 = v 5)) (decide (v 1 = v 2)) (decide (v 1 = v 3)) (decide (v 1 = v 4)) (decide (v 1 = v 5)) (decide (v 2 = v 3)) (decide (v 2 = v 4)) (decide (v 2 = v 5)) (decide (v 3 = v 4)) (decide (v 3 = v 5)) (decide (v 4 = v 5))
    simp only [ne_eq,decide_eq_true_eq] at hc
    exact hc h0 h1 h2 h01 h02 h12 eq012 eq013 eq014 eq015 eq023 eq024 eq025 eq034 eq035 eq045 eq123 eq124 eq125 eq134 eq135 eq145 eq234 eq235 eq245 eq345
  rcases cover with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨n02,n03,n04,n13,n14,n15,n24,n25,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 ∨ x = v 5 then 0 else if x = v 1 ∨ x = v 2 then 1 else if x = v 3 ∨ x = v 4 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n03,n05,n13,n14,n15,n24,n25,n34⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 ∨ x = v 4 then 0 else if x = v 1 ∨ x = v 2 then 1 else if x = v 3 ∨ x = v 5 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n03,n04,n12,n14,n15,n25,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 ∨ x = v 5 then 0 else if x = v 1 ∨ x = v 3 then 1 else if x = v 2 ∨ x = v 4 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n03,n05,n12,n14,n15,n24,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 ∨ x = v 4 then 0 else if x = v 1 ∨ x = v 3 then 1 else if x = v 2 ∨ x = v 5 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n03,n04,n05,n12,n13,n14,n24,n25,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 ∨ x = v 5 then 0 else if x = v 0 ∨ x = v 2 then 1 else if x = v 3 ∨ x = v 4 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n03,n04,n05,n12,n13,n15,n24,n25,n34⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 ∨ x = v 4 then 0 else if x = v 0 ∨ x = v 2 then 1 else if x = v 3 ∨ x = v 5 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n04,n05,n12,n13,n14,n25,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 ∨ x = v 5 then 0 else if x = v 0 ∨ x = v 3 then 1 else if x = v 2 ∨ x = v 4 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n04,n05,n12,n13,n15,n24,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 ∨ x = v 4 then 0 else if x = v 0 ∨ x = v 3 then 1 else if x = v 2 ∨ x = v 5 then 2 else 3
    refine ⟨false,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n03,n05,n12,n13,n14,n15,n25,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 then 0 else if x = v 3 then 1 else if x = v 5 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n03,n04,n12,n13,n14,n15,n24,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 then 0 else if x = v 3 then 1 else if x = v 4 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n05,n12,n13,n14,n15,n24,n25,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 then 0 else if x = v 2 then 1 else if x = v 5 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n04,n12,n13,n14,n15,n24,n25,n34⟩ := h
    let c (x : α) : Fin 4 := if x = v 1 then 0 else if x = v 2 then 1 else if x = v 4 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n03,n04,n05,n13,n15,n25,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 then 0 else if x = v 3 then 1 else if x = v 5 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n03,n04,n05,n13,n14,n24,n34,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 then 0 else if x = v 3 then 1 else if x = v 4 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n03,n04,n05,n12,n15,n24,n25,n35⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 then 0 else if x = v 2 then 1 else if x = v 5 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind
  · obtain ⟨n02,n03,n04,n05,n12,n14,n24,n25,n34⟩ := h
    let c (x : α) : Fin 4 := if x = v 0 then 0 else if x = v 2 then 1 else if x = v 4 then 2 else 3
    refine ⟨true,c,?_⟩
    intro i
    fin_cases i <;> simp only [ends,colors] <;> dsimp [c] <;> grind

end Onlyfr.ThreeEdgeProjection
