import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2571_1
    (extrapolate : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ) (b : Bool)
      (F : Finset (Fin n) → Prop), PEqualNP.MetaComplexity.Monotone2 C →
      let f := fun S : Finset (Fin n) =>
        let w := C.wires (List.ofFn fun i => decide (i ∈ S))
        w.getD C.output false || (b && w.getD q false)
      (∀ S, Minimal F S → f S = true) →
      (∀ S, Maximal (fun A => ¬ F A) S → f S = false) →
      ∀ S, f S = true ↔ F S)
    (finiteSearch : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 45 ∧ C.output < 25+C.size ∧ q < 25+C.size ∧
      ∀ b : Bool,
        let F := fun S : Finset (Fin 25) =>
          (∃ p ∈ S, ∃ l ∈ S, p.val < 12 ∧ 12 ≤ l.val ∧
            (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)) ∨
          (b = true ∧ ((13 : Fin 25) ∈ S ∨ (15 : Fin 25) ∈ S ∨ (21 : Fin 25) ∈ S))
        let f := fun S : Finset (Fin 25) =>
          let w := C.wires (List.ofFn fun i => decide (i ∈ S))
          w.getD C.output false || (b && w.getD q false)
        (∀ S, Minimal F S → f S = true) ∧ (∀ S, Maximal (fun A => ¬F A) S → f S = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  obtain ⟨C,q,hm,sz,oc,qc,checks⟩ := finiteSearch
  refine ⟨C,q,hm,sz,oc,qc,?_⟩
  intro x
  let S := Finset.univ.filter fun i => x i = true
  have mem (i : Fin 25) : i ∈ S ↔ x i = true := by simp [S]
  have coeff : (fun i => decide (i ∈ S)) = x := by
    funext i
    cases h : x i <;> simp [mem,h]
  let E := fun A : Finset (Fin 25) =>
    ∃ p ∈ A, ∃ l ∈ A, p.val < 12 ∧ 12 ≤ l.val ∧
      (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)
  let Q := fun A : Finset (Fin 25) => (13 : Fin 25) ∈ A ∨ (15 : Fin 25) ∈ A ∨ (21 : Fin 25) ∈ A
  have modes (b : Bool) :
      ((C.wires (List.ofFn x)).getD C.output false ||
        (b && (C.wires (List.ofFn x)).getD q false)) = true ↔ E S ∨ (b = true ∧ Q S) := by
    have a := checks b
    have h := extrapolate 25 C q b (fun A => E A ∨ (b=true ∧ Q A)) hm a.1 a.2 S
    change ((C.wires (List.ofFn fun i => decide (i ∈ S))).getD C.output false ||
      (b && (C.wires (List.ofFn fun i => decide (i ∈ S))).getD q false)) = true ↔ _ at h
    rw [coeff] at h
    exact h
  have left : C.eval (List.ofFn x) = true ↔ E S := by
    change (C.wires (List.ofFn x)).getD C.output false = true ↔ _
    simpa only [Bool.false_and,Bool.or_false,Bool.false_eq_true,false_and,or_false] using modes false
  constructor
  · rw [left]
    constructor
    · rintro ⟨p,hp,l,hl,pl,ll,inc,active⟩
      exact ⟨p,l,pl,ll,inc,active,(mem p).mp hp,(mem l).mp hl⟩
    · rintro ⟨p,l,pl,ll,inc,active,hp,hl⟩
      exact ⟨p,(mem p).mpr hp,l,(mem l).mpr hl,pl,ll,inc,active⟩
  · intro rej
    have hE : ¬E S := fun yes => Bool.noConfusion ((left.mpr yes).symm.trans rej)
    change (C.wires (List.ofFn x)).getD C.output false = false at rej
    have h := modes true
    rw [rej] at h
    apply Bool.eq_iff_iff.mpr
    simpa [hE,Q,mem,Bool.or_eq_true,or_assoc] using h
