import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_347

-- the net: a triangle 0 1 2 with one pendant edge at each corner
-- the vertex set chosen for an edge set S: a pendant vertex whose edge is in S if there is
-- one; otherwise S lies in the triangle, and a corner on exactly one edge of S, or two
-- corners when S is the whole triangle
def pick (S : Finset (Fin 6 × Fin 6)) : Finset (Fin 6) :=
  if (0, 3) ∈ S then {3} else if (1, 4) ∈ S then {4} else if (2, 5) ∈ S then {5}
  else if (0, 1) ∈ S then
    (if (0, 2) ∈ S then (if (1, 2) ∈ S then {0, 1} else {1}) else {0})
  else if (0, 2) ∈ S then {0} else {1}

def Good (E : List (Fin 6 × Fin 6)) (S : Finset (Fin 6 × Fin 6)) (C : Finset (Fin 6)) : Prop :=
  (∀ A ∈ C.powerset, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 6, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1

-- an edge set given by six bits, one for each edge of the net
def bset (b1 b2 b3 b4 b5 b6 : Bool) : Finset (Fin 6 × Fin 6) :=
  (if b1 then {(0, 1)} else ∅) ∪ (if b2 then {(0, 2)} else ∅) ∪ (if b3 then {(1, 2)} else ∅) ∪
    (if b4 then {(0, 3)} else ∅) ∪ (if b5 then {(1, 4)} else ∅) ∪ (if b6 then {(2, 5)} else ∅)

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 4000000 in
theorem all_good : ∀ b1 b2 b3 b4 b5 b6 : Bool, (bset b1 b2 b3 b4 b5 b6).Nonempty →
    Good [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] (bset b1 b2 b3 b4 b5 b6)
      (pick (bset b1 b2 b3 b4 b5 b6)) := by
  unfold Good
  decide

theorem eq_bset (S : Finset (Fin 6 × Fin 6))
    (hS : ∀ e ∈ S, e ∈ [((0 : Fin 6), (1 : Fin 6)), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)]) :
    S = bset (decide ((0, 1) ∈ S)) (decide ((0, 2) ∈ S)) (decide ((1, 2) ∈ S))
      (decide ((0, 3) ∈ S)) (decide ((1, 4) ∈ S)) (decide ((2, 5) ∈ S)) := by
  ext e
  constructor
  · intro he
    have h := hS e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> subst h <;> simp [bset, he]
  · intro he
    simp only [bset, Finset.mem_union] at he
    rcases he with ((((h | h) | h) | h) | h) | h <;>
      · split_ifs at h with h2
        · rw [Finset.mem_singleton] at h
          rw [h]
          simpa using h2
        · simp at h

end PEqualNP.Outside.L_meta_347

theorem PEqualNP.Outside.L_meta_347 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ S : Finset (Fin 6 × Fin 6), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 6), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 6, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  intro E hE S hS hne
  subst hE
  have e := PEqualNP.Outside.L_meta_347.eq_bset S hS
  rw [e] at hne
  obtain ⟨h1, h2, h3⟩ := PEqualNP.Outside.L_meta_347.all_good _ _ _ _ _ _ hne
  rw [← e] at h1 h2 h3
  exact ⟨PEqualNP.Outside.L_meta_347.pick S, fun A hA => h1 A (Finset.mem_powerset.2 hA), h2, h3⟩
