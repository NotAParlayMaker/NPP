import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3014_819
    (coreSmall :
      have edges : List (ℕ × ℕ) := [(1,9),(1,13),(2,12),(2,13),(3,11),(3,12),(4,11),(4,13),(5,9),(5,12),(6,9),(6,11)]
      ∃ C : Circuit, IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.size ≤ 14 ∧
        14 ≤ C.output ∧ C.output < 14 + C.size ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
          decide (∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true))
    (pencilExact :
      have edges : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(2,8),(3,7),(4,10),(5,10),(6,8)]
      ∃ D : Circuit, IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.size = 11 ∧
        14 ≤ D.output ∧ D.output < 14 + D.size ∧
        ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) =
          decide (∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true))
    (combine :
      ∀ (n : ℕ) (C D : Circuit), IsAO2 n C → IsAO2 n D →
        (∀ g ∈ C.gates, g.inputs.Nodup) → (∀ g ∈ D.gates, g.inputs.Nodup) →
        n ≤ C.output → C.output < n + C.size → n ≤ D.output → D.output < n + D.size →
        ∃ E : Circuit, IsAO2 n E ∧ (∀ g ∈ E.gates, g.inputs.Nodup) ∧
          E.size = C.size + D.size + 1 ∧
          ∀ x : Fin n → Bool, E.eval (List.ofFn x) = (C.eval (List.ofFn x) || D.eval (List.ofFn x))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6 = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  let core : List (ℕ × ℕ) := [(1,9),(1,13),(2,12),(2,13),(3,11),(3,12),(4,11),(4,13),(5,9),(5,12),(6,9),(6,11)]
  let pencil : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(2,8),(3,7),(4,10),(5,10),(6,8)]
  let full : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let edgeFun (es : List (ℕ × ℕ)) (x : Fin 14 → Bool) : Bool :=
    decide (∃ u v : Fin 14, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true)
  have partition : ∀ u v : Fin 14,
      ((u.val, v.val) ∈ full) ↔ ((u.val, v.val) ∈ core ∨ (u.val, v.val) ∈ pencil) := by
    decide
  have combineEdges (x : Fin 14 → Bool) :
      edgeFun full x = (edgeFun core x || edgeFun pencil x) := by
    rw [Bool.eq_iff_iff]
    simp only [edgeFun, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases (partition u v).mp huv with h | h
      · exact Or.inl ⟨u, v, h, hu, hv⟩
      · exact Or.inr ⟨u, v, h, hu, hv⟩
    · rintro (⟨u, v, h, hu, hv⟩ | ⟨u, v, h, hu, hv⟩)
      · exact ⟨u, v, (partition u v).mpr (Or.inl h), hu, hv⟩
      · exact ⟨u, v, (partition u v).mpr (Or.inr h), hu, hv⟩
  obtain ⟨C, hC, hCd, hCsize, hClo, hChi, hCval⟩ := coreSmall
  obtain ⟨D, hD, hDd, hDsize, hDlo, hDhi, hDval⟩ := pencilExact
  obtain ⟨E, hE, hEd, hEsize, hEval⟩ := combine 14 D C hD hC hDd hCd hDlo hDhi hClo hChi
  have evaluates (x : Fin 14 → Bool) : E.eval (List.ofFn x) = edgeFun full x := by
    rw [hEval, hDval, hCval, Bool.or_comm]
    exact (combineEdges x).symm
  exact ⟨E, hE, hEd, by omega, by omega,
    (fun x hx _ => (evaluates x).trans hx), (fun x hx _ => (evaluates x).trans hx)⟩
