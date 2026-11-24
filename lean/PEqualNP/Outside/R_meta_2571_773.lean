import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2571_773
  (frontier :
    let F := fun x : Fin 25 → Bool => ∃ a b : Fin 25,
        a.val < 12 ∧ 12 ≤ b.val ∧ (a.val+b.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧
        a.val ∉ ([0,2,8] : List ℕ) ∧ x a = true ∧ x b = true
    let S : Finset (Fin 25) := {13,15,21}
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 45 ∧ C.output < 25+C.size ∧ w < 25+C.size ∧
      (∀ x, Minimal F x → C.eval (List.ofFn x) = true) ∧
      (∀ x, Maximal (fun z => ¬ F z) x → C.eval (List.ofFn x) = false) ∧
      (∀ i ∈ S, (C.wires (List.ofFn fun j : Fin 25 => decide (j = i))).getD w false = true) ∧
      (∀ x, Maximal (fun z => ¬ F z ∧ ∀ i ∈ S, z i = false) x →
        (C.wires (List.ofFn x)).getD w false = false))
  (extendRows : ∀ (n : ℕ) (F : (Fin n → Bool) → Prop) (S : Finset (Fin n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x, Minimal F x → C.eval (List.ofFn x) = true) →
    (∀ x, Maximal (fun z => ¬ F z) x → C.eval (List.ofFn x) = false) →
    (∀ i ∈ S, (C.wires (List.ofFn fun j : Fin n => decide (j = i))).getD w false = true) →
    (∀ x, Maximal (fun z => ¬ F z ∧ ∀ i ∈ S, z i = false) x →
      (C.wires (List.ofFn x)).getD w false = false) →
    ∀ x, (C.eval (List.ofFn x) = true ↔ F x) ∧
      (C.eval (List.ofFn x) = false →
        ((C.wires (List.ofFn x)).getD w false = true ↔ ∃ i ∈ S, x i = true))) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let F := fun x : Fin 25 → Bool => ∃ a b : Fin 25,
        a.val < 12 ∧ 12 ≤ b.val ∧ (a.val+b.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧
        a.val ∉ ([0,2,8] : List ℕ) ∧ x a = true ∧ x b = true
  let S : Finset (Fin 25) := {13,15,21}
  obtain ⟨C,w,model,size,outBound,wireBound,positives,negatives,auxPos,auxNeg⟩ := frontier
  have whole := extendRows 25 F S C w model positives negatives auxPos auxNeg
  refine ⟨C,w,model,size,outBound,wireBound,fun x => ⟨(whole x).1,?_⟩⟩
  intro zero
  apply Bool.eq_iff_iff.mpr
  rw [(whole x).2 zero]
  simp only [Bool.or_eq_true]
  constructor
  · rintro ⟨i,hi,hx⟩
    have listed : i = 13 ∨ i = 15 ∨ i = 21 := by simpa [S] using hi
    rcases listed with rfl | rfl | rfl
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  · rintro ((h | h) | h)
    · exact ⟨13,by simp [S],h⟩
    · exact ⟨15,by simp [S],h⟩
    · exact ⟨21,by simp [S],h⟩
