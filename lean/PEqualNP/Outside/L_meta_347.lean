import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_347

-- The edge set chosen by six bits, one bit per edge of the net.
def T (b0 b1 b2 b3 b4 b5 : Bool) : Finset (Fin 6 × Fin 6) :=
  (if b0 then {(0, 1)} else ∅) ∪ (if b1 then {(0, 2)} else ∅) ∪ (if b2 then {(1, 2)} else ∅) ∪
    (if b3 then {(0, 3)} else ∅) ∪ (if b4 then {(1, 4)} else ∅) ∪ (if b5 then {(2, 5)} else ∅)

theorem mem_T (b0 b1 b2 b3 b4 b5 : Bool) (e : Fin 6 × Fin 6) :
    e ∈ T b0 b1 b2 b3 b4 b5 ↔ (b0 = true ∧ e = (0, 1)) ∨ (b1 = true ∧ e = (0, 2)) ∨
      (b2 = true ∧ e = (1, 2)) ∨ (b3 = true ∧ e = (0, 3)) ∨ (b4 = true ∧ e = (1, 4)) ∨
      (b5 = true ∧ e = (2, 5)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [T, or_assoc]

-- Every nonempty edge set of the net has a witness among seven candidate vertex sets:
-- the six single vertices, and the pair of vertices 0 and 1 (needed only for the triangle).
set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
theorem key : ∀ b0 b1 b2 b3 b4 b5 : Bool, (T b0 b1 b2 b3 b4 b5).Nonempty →
    ∃ C ∈ ([{0}, {1}, {2}, {3}, {4}, {5}, {0, 1}] : List (Finset (Fin 6))),
      (∀ A ∈ C.powerset, A.Nonempty → A ≠ C → ∃ e ∈ T b0 b1 b2 b3 b4 b5,
        (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧
      (∀ a b : Fin 6, a ∉ C → b ∉ C →
        (∃ x ∈ C, (x, a) ∈ T b0 b1 b2 b3 b4 b5 ∨ (a, x) ∈ T b0 b1 b2 b3 b4 b5) →
        (∃ y ∈ C, (y, b) ∈ T b0 b1 b2 b3 b4 b5 ∨ (b, y) ∈ T b0 b1 b2 b3 b4 b5) →
        ¬ ((a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)) ∨
          (b, a) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)))) ∧
      ((T b0 b1 b2 b3 b4 b5).filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  decide +kernel

-- Any edge set of the net is the one chosen by its own six membership bits.
theorem eq_T (S : Finset (Fin 6 × Fin 6))
    (hS : ∀ e ∈ S, e ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))) :
    S = T (decide ((0, 1) ∈ S)) (decide ((0, 2) ∈ S)) (decide ((1, 2) ∈ S)) (decide ((0, 3) ∈ S))
      (decide ((1, 4) ∈ S)) (decide ((2, 5) ∈ S)) := by
  ext e
  rw [mem_T]
  constructor
  · intro he
    have h := hS e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [he]
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;>
      exact of_decide_eq_true h

end PEqualNP.Outside.L_meta_347

theorem PEqualNP.Outside.L_meta_347 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ S : Finset (Fin 6 × Fin 6), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 6), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 6, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  intro E hE S hS hne
  subst hE
  have hT := PEqualNP.Outside.L_meta_347.eq_T S hS
  rw [hT] at hne ⊢
  obtain ⟨C, -, h1, h2, h3⟩ := PEqualNP.Outside.L_meta_347.key _ _ _ _ _ _ hne
  exact ⟨C, fun A hA hA0 hAC => h1 A (Finset.mem_powerset.2 hA) hA0 hAC, h2, h3⟩
