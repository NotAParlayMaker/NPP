import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4955_1
  (H1 : (∀ F : List (Finset (Fin (285:ℕ))), F.length ≤ 87 → (∀ i : Fin F.length, 26 ≤ i.val → ∃ P ∈ F, ∃ Q ∈ F, ¬P ⊆ Q ∧ ¬Q ⊆ P ∧ (F.get i = P ∩ Q ∨ F.get i = P ∪ Q)) → ∀ A ∈ F, ∀ B ∈ F, ¬A ⊆ B → ¬B ⊆ A → A ∩ B ≠ ((List.filter (fun (r : Fin (285:ℕ)) => decide ((r:ℕ) < 51)) (List.finRange (285:ℕ))).toFinset)))
  (H2 : (∀ i : Fin (26:ℕ), (List.range (26:ℕ)).get i = i.val))
  : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →       ∀ x6 ∈ x2 ++ x3, ∀ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∩ x8 ≠ (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset := by
  have _ := H2
  intro x1 x2 x3 hx3len hgen
  let F : List (Finset (Fin (285:ℕ))) := x2 ++ x3
  have hx2len : x2.length = 26 := by
    simp [x2]
  have hFlen : F.length ≤ 87 := by
    simp [F, hx2len]
    omega
  have hgenF : ∀ i : Fin F.length, 26 ≤ i.val →
      ∃ P ∈ F, ∃ Q ∈ F, ¬P ⊆ Q ∧ ¬Q ⊆ P ∧
        (F.get i = P ∩ Q ∨ F.get i = P ∪ Q) := by
    intro i hi
    let t : ℕ := i.val - 26
    have hi_lt : i.val < 26 + x3.length := by
      simpa [F, hx2len] using i.isLt
    have ht : t < x3.length := by omega
    have hival : i.val = 26 + t := by omega
    rcases hgen ⟨t, ht⟩ with ⟨P, hP, Q, hQ, hPQ, hQP, hnotmem, heq⟩
    have hPF : P ∈ F := by
      rcases List.mem_append.mp hP with hp | hp
      · exact List.mem_append_left x3 hp
      · exact List.mem_append_right x2 (List.mem_of_mem_take hp)
    have hQF : Q ∈ F := by
      rcases List.mem_append.mp hQ with hq | hq
      · exact List.mem_append_left x3 hq
      · exact List.mem_append_right x2 (List.mem_of_mem_take hq)
    have hget : F.get i = x3.get ⟨t, ht⟩ := by
      simp [F, hx2len, hival]
    refine ⟨P, hPF, Q, hQF, hPQ, hQP, ?_⟩
    rw [hget]
    exact heq
  have hres := H1 F hFlen hgenF
  intro A hA B hB hnAB hnBA hEq
  exact hres A hA B hB hnAB hnBA hEq
