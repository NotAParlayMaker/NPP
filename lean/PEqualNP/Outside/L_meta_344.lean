import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem obstruction : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool),
    ((if b0 || b1 then 1 else 0) + (if b0 || b4 then 1 else 0) + (if b0 || b5 then 1 else 0) + (if b0 || b6 then 1 else 0) + (if b1 || b2 then 1 else 0) + (if b1 || b6 then 1 else 0) + (if b1 || b7 then 1 else 0) + (if b2 || b7 then 1 else 0) + (if b2 || b8 then 1 else 0) + (if b3 || b4 then 1 else 0) + (if b3 || b8 then 1 else 0) + (if b3 || b9 then 1 else 0) + (if b4 || b5 then 1 else 0) + (if b4 || b9 then 1 else 0) + (if b5 || b10 then 1 else 0) + (if b5 || b13 then 1 else 0) + (if b6 || b11 then 1 else 0) + (if b6 || b14 then 1 else 0) + (if b7 || b10 then 1 else 0) + (if b7 || b12 then 1 else 0) + (if b8 || b11 then 1 else 0) + (if b8 || b13 then 1 else 0) + (if b9 || b12 then 1 else 0) + (if b9 || b14 then 1 else 0) + (if b10 || b12 then 1 else 0) + (if b12 || b14 then 1 else 0)) % 2 = 1 →
    (((!b0 && (b1 || b4 || b5 || b6)) && (!b1 && (b0 || b2 || b6 || b7))) ||
      ((!b0 && (b1 || b4 || b5 || b6)) && (!b4 && (b0 || b3 || b5 || b9))) ||
      ((!b0 && (b1 || b4 || b5 || b6)) && (!b5 && (b0 || b4 || b10 || b13))) ||
      ((!b0 && (b1 || b4 || b5 || b6)) && (!b6 && (b0 || b1 || b11 || b14))) ||
      ((!b1 && (b0 || b2 || b6 || b7)) && (!b2 && (b1 || b7 || b8))) ||
      ((!b1 && (b0 || b2 || b6 || b7)) && (!b6 && (b0 || b1 || b11 || b14))) ||
      ((!b1 && (b0 || b2 || b6 || b7)) && (!b7 && (b1 || b2 || b10 || b12))) ||
      ((!b2 && (b1 || b7 || b8)) && (!b3 && (b4 || b8 || b9))) ||
      ((!b2 && (b1 || b7 || b8)) && (!b7 && (b1 || b2 || b10 || b12))) ||
      ((!b2 && (b1 || b7 || b8)) && (!b8 && (b2 || b3 || b11 || b13))) ||
      ((!b3 && (b4 || b8 || b9)) && (!b4 && (b0 || b3 || b5 || b9))) ||
      ((!b3 && (b4 || b8 || b9)) && (!b8 && (b2 || b3 || b11 || b13))) ||
      ((!b3 && (b4 || b8 || b9)) && (!b9 && (b3 || b4 || b12 || b14))) ||
      ((!b4 && (b0 || b3 || b5 || b9)) && (!b5 && (b0 || b4 || b10 || b13))) ||
      ((!b4 && (b0 || b3 || b5 || b9)) && (!b9 && (b3 || b4 || b12 || b14))) ||
      ((!b5 && (b0 || b4 || b10 || b13)) && (!b10 && (b5 || b7 || b12))) ||
      ((!b5 && (b0 || b4 || b10 || b13)) && (!b13 && (b5 || b8))) ||
      ((!b6 && (b0 || b1 || b11 || b14)) && (!b11 && (b6 || b8))) ||
      ((!b6 && (b0 || b1 || b11 || b14)) && (!b14 && (b6 || b9 || b12))) ||
      ((!b7 && (b1 || b2 || b10 || b12)) && (!b10 && (b5 || b7 || b12))) ||
      ((!b7 && (b1 || b2 || b10 || b12)) && (!b12 && (b7 || b9 || b10 || b14))) ||
      ((!b8 && (b2 || b3 || b11 || b13)) && (!b11 && (b6 || b8))) ||
      ((!b8 && (b2 || b3 || b11 || b13)) && (!b13 && (b5 || b8))) ||
      ((!b9 && (b3 || b4 || b12 || b14)) && (!b12 && (b7 || b9 || b10 || b14))) ||
      ((!b9 && (b3 || b4 || b12 || b14)) && (!b14 && (b6 || b9 || b12))) ||
      ((!b10 && (b5 || b7 || b12)) && (!b12 && (b7 || b9 || b10 || b14))) ||
      ((!b10 && (b5 || b7 || b12)) && (!b13 && (b5 || b8))) ||
      ((!b11 && (b6 || b8)) && (!b13 && (b5 || b8))) ||
      ((!b11 && (b6 || b8)) && (!b14 && (b6 || b9 || b12))) ||
      ((!b12 && (b7 || b9 || b10 || b14)) && (!b14 && (b6 || b9 || b12)))) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem L_meta_344 : ∀ E : List (Fin 15 × Fin 15), E = [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (1, 6), (1, 7), (2, 3), (2, 7), (2, 8), (3, 4), (3, 8), (3, 9), (4, 5), (4, 9), (5, 10), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 12), (10, 13), (11, 13), (11, 14), (12, 14)] → ∃ S : Finset (Fin 15 × Fin 15), (∀ e ∈ S, e ∈ E) ∧ S.Nonempty ∧ ¬ ∃ C : Finset (Fin 15), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 15, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  classical
  rintro E rfl
  let S : Finset (Fin 15 × Fin 15) := {(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (1, 6), (1, 7), (2, 7), (2, 8), (3, 4), (3, 8), (3, 9), (4, 5), (4, 9), (5, 10), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 12), (12, 14)}
  refine ⟨S, by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨C, _, boundary, odd⟩
  have cardSum : (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card =
      ∑ e ∈ S, (if e.1 ∈ C ∨ e.2 ∈ C then 1 else 0 : ℕ) := by simp
  rw [cardSum] at odd
  simp (disch := decide) only [S, Finset.sum_insert, Finset.sum_singleton] at odd
  have witness := obstruction (decide (0 ∈ C)) (decide (1 ∈ C)) (decide (2 ∈ C)) (decide (3 ∈ C)) (decide (4 ∈ C)) (decide (5 ∈ C)) (decide (6 ∈ C)) (decide (7 ∈ C)) (decide (8 ∈ C)) (decide (9 ∈ C)) (decide (10 ∈ C)) (decide (11 ∈ C)) (decide (12 ∈ C)) (decide (13 ∈ C)) (decide (14 ∈ C)) (by
    simpa only [Bool.or_eq_true, decide_eq_true_eq, Nat.add_assoc] using odd)
  let B (i : Fin 15) := i ∉ C ∧ ∃ x ∈ C, (x,i) ∈ S ∨ (i,x) ∈ S
  have ban (i j : Fin 15) (h : (i,j) ∈ ([(0,1),(0,4),(0,5),(0,6),(1,2),(1,6),(1,7),(2,3),(2,7),(2,8),(3,4),(3,8),(3,9),(4,5),(4,9),(5,10),(5,13),(6,11),(6,14),(7,10),(7,12),(8,11),(8,13),(9,12),(9,14),(10,12),(10,13),(11,13),(11,14),(12,14)] : List (Fin 15 × Fin 15))) :
      ¬ (B i ∧ B j) := by
    rintro ⟨⟨hi,hx⟩,⟨hj,hy⟩⟩
    exact boundary i j hi hj hx hy (Or.inl h)
  have local0 : (!(decide (0 ∈ C)) && ((decide (1 ∈ C)) || (decide (4 ∈ C)) || (decide (5 ∈ C)) || (decide (6 ∈ C)))) = true → B 0 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local1 : (!(decide (1 ∈ C)) && ((decide (0 ∈ C)) || (decide (2 ∈ C)) || (decide (6 ∈ C)) || (decide (7 ∈ C)))) = true → B 1 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local2 : (!(decide (2 ∈ C)) && ((decide (1 ∈ C)) || (decide (7 ∈ C)) || (decide (8 ∈ C)))) = true → B 2 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local3 : (!(decide (3 ∈ C)) && ((decide (4 ∈ C)) || (decide (8 ∈ C)) || (decide (9 ∈ C)))) = true → B 3 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local4 : (!(decide (4 ∈ C)) && ((decide (0 ∈ C)) || (decide (3 ∈ C)) || (decide (5 ∈ C)) || (decide (9 ∈ C)))) = true → B 4 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local5 : (!(decide (5 ∈ C)) && ((decide (0 ∈ C)) || (decide (4 ∈ C)) || (decide (10 ∈ C)) || (decide (13 ∈ C)))) = true → B 5 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local6 : (!(decide (6 ∈ C)) && ((decide (0 ∈ C)) || (decide (1 ∈ C)) || (decide (11 ∈ C)) || (decide (14 ∈ C)))) = true → B 6 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local7 : (!(decide (7 ∈ C)) && ((decide (1 ∈ C)) || (decide (2 ∈ C)) || (decide (10 ∈ C)) || (decide (12 ∈ C)))) = true → B 7 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local8 : (!(decide (8 ∈ C)) && ((decide (2 ∈ C)) || (decide (3 ∈ C)) || (decide (11 ∈ C)) || (decide (13 ∈ C)))) = true → B 8 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local9 : (!(decide (9 ∈ C)) && ((decide (3 ∈ C)) || (decide (4 ∈ C)) || (decide (12 ∈ C)) || (decide (14 ∈ C)))) = true → B 9 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local10 : (!(decide (10 ∈ C)) && ((decide (5 ∈ C)) || (decide (7 ∈ C)) || (decide (12 ∈ C)))) = true → B 10 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local11 : (!(decide (11 ∈ C)) && ((decide (6 ∈ C)) || (decide (8 ∈ C)))) = true → B 11 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local12 : (!(decide (12 ∈ C)) && ((decide (7 ∈ C)) || (decide (9 ∈ C)) || (decide (10 ∈ C)) || (decide (14 ∈ C)))) = true → B 12 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local13 : (!(decide (13 ∈ C)) && ((decide (5 ∈ C)) || (decide (8 ∈ C)))) = true → B 13 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  have local14 : (!(decide (14 ∈ C)) && ((decide (6 ∈ C)) || (decide (9 ∈ C)) || (decide (12 ∈ C)))) = true → B 14 := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
    rintro ⟨hout,(h|h|h)⟩ <;> refine ⟨hout, _, h, by decide⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, or_assoc] at witness
  rcases witness with ⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩|⟨h,h'⟩
  · exact ban 0 1 (by decide) ⟨local0 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local1 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 0 4 (by decide) ⟨local0 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local4 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 0 5 (by decide) ⟨local0 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local5 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 0 6 (by decide) ⟨local0 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local6 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 1 2 (by decide) ⟨local1 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local2 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 1 6 (by decide) ⟨local1 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local6 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 1 7 (by decide) ⟨local1 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local7 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 2 3 (by decide) ⟨local2 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local3 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 2 7 (by decide) ⟨local2 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local7 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 2 8 (by decide) ⟨local2 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local8 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 3 4 (by decide) ⟨local3 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local4 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 3 8 (by decide) ⟨local3 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local8 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 3 9 (by decide) ⟨local3 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local9 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 4 5 (by decide) ⟨local4 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local5 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 4 9 (by decide) ⟨local4 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local9 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 5 10 (by decide) ⟨local5 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local10 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 5 13 (by decide) ⟨local5 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local13 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 6 11 (by decide) ⟨local6 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local11 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 6 14 (by decide) ⟨local6 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local14 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 7 10 (by decide) ⟨local7 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local10 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 7 12 (by decide) ⟨local7 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local12 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 8 11 (by decide) ⟨local8 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local11 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 8 13 (by decide) ⟨local8 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local13 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 9 12 (by decide) ⟨local9 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local12 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 9 14 (by decide) ⟨local9 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local14 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 10 12 (by decide) ⟨local10 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local12 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 10 13 (by decide) ⟨local10 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local13 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 11 13 (by decide) ⟨local11 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local13 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 11 14 (by decide) ⟨local11 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local14 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩
  · exact ban 12 14 (by decide) ⟨local12 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h), local14 (by simpa only [Bool.and_eq_true, Bool.or_eq_true, or_assoc] using h')⟩

end PEqualNP.Outside
