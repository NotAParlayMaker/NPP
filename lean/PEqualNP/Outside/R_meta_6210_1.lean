import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.LowMerge

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_6210_1
  (valid_gate : ∀ (D : Circuit) (w : ℕ), Monotone2 D → ReadsBack 26 D →
    w < 26 + D.size → RightOnIncidentPairs singerLines3 ⟨D.gates, w⟩ →
    (∀ Q, IsQuadrangle singerLines3 Q →
      wireVal D (incidenceInput Q (missLines singerLines3 Q)) w = false) →
    64 ≤ D.size)
  (append_and : ∀ (E : Circuit) (x : List Bool), x.length = 26 → ∀ (u v : ℕ),
    wireVal ⟨E.gates ++ [⟨GateOp.and, [u, v]⟩], 26 + E.size⟩ x (26 + E.size) =
      (wireVal E x u && wireVal E x v)) :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x9 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x9)) x8;           have x9 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x9 : ℕ) => {x10 : Fin (13 : ℕ) × Fin (13 : ℕ) | x10.1 ∉ PEqualNP.HeptadCover.singerLines3 x10.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x10.1} {x10.2}) x9 = Bool.true};           (x9 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x13 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x13 → x8 x2 x13 = Bool.false ∨ x8 x3 x13 = Bool.false) → (∃ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 ∧ x8 x2 x14 = Bool.false ∧ x8 x3 x14 = Bool.true) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x8 x3 x15 = Bool.false ∧ x8 x2 x15 = Bool.true) → (63 : ℕ) ≤ x1.size) := by
  classical
  intro C a b hmono hback ha hb hx8 hx9 hle hra hrb hquad hq1 hq2
  let D : Circuit := ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], 26 + C.size⟩
  let k : ℕ := 26 + C.size
  have hDmono : Monotone2 D := by
    intro g hg
    simp only [D, Circuit.size, List.length_append, List.length_singleton] at hg ⊢
    rcases List.mem_append.mp hg with hg | hg
    · simpa using hmono g hg
    · simp only [List.mem_singleton] at hg
      subst g
      constructor
      · simp
      · simp
  have hDback : ReadsBack 26 D := by
    intro j hj i hi
    by_cases hj' : j < C.gates.length
    · have hgate : gateAt D j = gateAt C j := by
        simp [D, gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
      have hi' : i ∈ (gateAt C j).inputs := by simpa [hgate] using hi
      exact hback j hj' i hi'
    · have hjEq : j = C.gates.length := by
        have hjlt : j < C.gates.length + 1 := by simpa [D] using hj
        omega
      subst j
      have hi' : i = a ∨ i = b := by
        simpa [D, gateAt] using hi
      rcases hi' with rfl | rfl
      · simpa [Circuit.size] using ha
      · simpa [Circuit.size] using hb
  have hklt : k < 26 + D.size := by
    simp [D, k, Circuit.size]
  have hrightk : RightOnIncidentPairs singerLines3 ⟨D.gates, k⟩ := by
    intro l p hp
    have hpa := hra l p hp
    have hpb := hrb l p hp
    change wireVal C (incidenceInput {p} {l}) a = true at hpa
    change wireVal C (incidenceInput {p} {l}) b = true at hpb
    change wireVal ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], 26 + C.size⟩
      (incidenceInput {p} {l}) (26 + C.size) = true
    rw [append_and C _ (by simp [incidenceInput])]
    simpa [hpa, hpb]
  have hquadk : ∀ Q, IsQuadrangle singerLines3 Q →
      wireVal D (incidenceInput Q (missLines singerLines3 Q)) k = false := by
    intro Q hQ
    have hq := hquad Q hQ
    change wireVal C (incidenceInput Q (missLines singerLines3 Q)) a = false ∨
      wireVal C (incidenceInput Q (missLines singerLines3 Q)) b = false at hq
    change wireVal ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], 26 + C.size⟩
      (incidenceInput Q (missLines singerLines3 Q)) (26 + C.size) = false
    rw [append_and C _ (by simp [incidenceInput])]
    rcases hq with hq | hq
    · simp [hq]
    · simp [hq]
  have h64 := valid_gate D k hDmono hDback hklt hrightk hquadk
  have hsize : D.size = C.size + 1 := by simp [D, Circuit.size]
  omega
