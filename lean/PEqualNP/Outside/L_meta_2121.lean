import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2121_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧
      t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    simp only [List.foldl_cons, ht, List.append_assoc, List.singleton_append]

theorem test : ∀ (a b c d : Bool), (List.ofFn ![a, b, c, d]) = [a, b, c, d] := by
  intro a b c d
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_2121_aux

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_2121 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 4 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun z : Fin 4 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 1 && z 2) || (z 1 && z 3)) x) → 3 ≤ C.size := by
  intro C hM hR h
  by_contra hc
  push Not at hc
  have a1 := h ![true, false, true, false]
  have a2 := h ![false, false, true, false]
  have a3 := h ![false, true, true, false]
  have a4 := h ![true, false, false, false]
  have a5 := h ![true, false, false, true]
  obtain ⟨gs, o⟩ := C
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hc
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_meta_2121_aux.test] at a1 a2 a3 a4 a5
  rcases gs with _ | ⟨⟨op0, l0⟩, _ | ⟨⟨op1, l1⟩, _ | ⟨g2, r⟩⟩⟩
  rotate_left 3
  · simp at hc
    omega
  all_goals rcases (show o < 6 ∨ ∃ k, o = k + 6 from by
    rcases Nat.lt_or_ge o 6 with h6 | h6
    · exact Or.inl h6
    · exact Or.inr ⟨o - 6, by omega⟩) with ho | ⟨k, rfl⟩
  all_goals try interval_cases o
  all_goals simp at a1 a2 a3 a4 a5
  all_goals try simp_all
  · have m0 := (hM ⟨op0, l0⟩ (by simp)).2
    have b0 := hR 0 (by simp)
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at b0
    simp at m0 b0
    rcases l0 with _ | ⟨p, _ | ⟨q, _ | ⟨r0, t0⟩⟩⟩
    rotate_left 3
    · simp at m0
    all_goals simp at b0
    all_goals try (obtain ⟨bp, bq⟩ : _ ∧ _ := b0)
    all_goals try interval_cases p
    all_goals try interval_cases q
    all_goals simp at a1 a2 a3 a4 a5
    all_goals simp_all
  · have m0 := (hM ⟨op0, l0⟩ (by simp)).2
    have b0 := hR 0 (by simp)
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at b0
    simp at m0 b0
    rcases l0 with _ | ⟨p, _ | ⟨q, _ | ⟨r0, t0⟩⟩⟩
    rotate_left 3
    · simp at m0
    all_goals simp at b0
    all_goals try (obtain ⟨bp, bq⟩ : _ ∧ _ := b0)
    all_goals try interval_cases p
    all_goals try interval_cases q
    all_goals simp at a1 a2 a3 a4 a5
    all_goals simp_all
  · have m1 := (hM ⟨op1, l1⟩ (by simp)).2
    have b1 := hR 1 (by simp)
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at b1
    simp at m1 b1
    rcases l1 with _ | ⟨u, _ | ⟨v, _ | ⟨r1, t1⟩⟩⟩
    rotate_left 3
    · simp at m1
    all_goals simp at b1
    all_goals try (obtain ⟨bu, bv⟩ : _ ∧ _ := b1)
    all_goals try interval_cases u
    all_goals try interval_cases v
    all_goals simp at a1 a2 a3 a4 a5
    all_goals try simp_all
    all_goals
      have m0 := (hM ⟨op0, l0⟩ (by simp)).2
      have b0 := hR 0 (by simp)
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at b0
      simp at m0 b0
      rcases l0 with _ | ⟨p, _ | ⟨q, _ | ⟨r0, t0⟩⟩⟩
      rotate_left 3
      · simp at m0
      all_goals simp at b0
      all_goals try (obtain ⟨bp, bq⟩ : _ ∧ _ := b0)
      all_goals try interval_cases p
      all_goals try interval_cases q
      all_goals simp at a1 a2 a3 a4 a5
      all_goals simp_all
