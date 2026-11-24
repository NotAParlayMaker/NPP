import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5294_317
    (c22 : ∀ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Finset ℕ) (x5 : Bool),
      x3.size ≤ (11 : ℕ) →
      (x5 = Bool.true → x3.output ∈ x4) →
      (∀ x9 ∈ x3.gates, ∃ (x11 : Bool) (x12 : Bool),
        (x11 = Bool.true → x9.left ∈ x4) ∧ (x12 = Bool.true → x9.right ∈ x4) ∧
        ((x9.op = fun (x13 x14 : Bool) => x13 != x11 && x14 != x12) ∨
         x9.op = fun (x13 x14 : Bool) => x13 != x11 || x14 != x12)) →
      ¬∀ (x10 : Fin (9 : ℕ) → Bool),
        (x3.eval (List.ofFn x10 ++ [x10 (2 : Fin (9 : ℕ)), Bool.false]) != x5) =
        [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (9 : ℕ) (x11 / (10 : ℕ))) && x10 (Fin.ofNat (9 : ℕ) (x11 % (10 : ℕ))))
    (c23 : ∀ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Finset ℕ) (x5 : Bool),
      x3.size ≤ (11 : ℕ) →
      (x5 = Bool.true → x3.output ∈ x4) →
      (∀ x9 ∈ x3.gates, ∃ (x11 : Bool) (x12 : Bool),
        (x11 = Bool.true → x9.left ∈ x4) ∧ (x12 = Bool.true → x9.right ∈ x4) ∧
        ((x9.op = fun (x13 x14 : Bool) => x13 != x11 && x14 != x12) ∨
         x9.op = fun (x13 x14 : Bool) => x13 != x11 || x14 != x12)) →
      ¬∀ (x10 : Fin (9 : ℕ) → Bool),
        (x3.eval (List.ofFn x10 ++ [x10 (2 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)), Bool.false]) != x5) =
        [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (9 : ℕ) (x11 / (10 : ℕ))) && x10 (Fin.ofNat (9 : ℕ) (x11 % (10 : ℕ))))
    (c28 : ∀ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Finset ℕ) (x5 : Bool),
      x3.size ≤ (11 : ℕ) →
      (x5 = Bool.true → x3.output ∈ x4) →
      (∀ x9 ∈ x3.gates, ∃ (x11 : Bool) (x12 : Bool),
        (x11 = Bool.true → x9.left ∈ x4) ∧ (x12 = Bool.true → x9.right ∈ x4) ∧
        ((x9.op = fun (x13 x14 : Bool) => x13 != x11 && x14 != x12) ∨
         x9.op = fun (x13 x14 : Bool) => x13 != x11 || x14 != x12)) →
      ¬∀ (x10 : Fin (9 : ℕ) → Bool),
        (x3.eval (List.ofFn x10 ++ [x10 (2 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)), Bool.false]) != x5) =
        [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (9 : ℕ) (x11 / (10 : ℕ))) && x10 (Fin.ofNat (9 : ℕ) (x11 % (10 : ℕ))))
    (c33 : ∀ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Finset ℕ) (x5 : Bool),
      x3.size ≤ (11 : ℕ) →
      (x5 = Bool.true → x3.output ∈ x4) →
      (∀ x9 ∈ x3.gates, ∃ (x11 : Bool) (x12 : Bool),
        (x11 = Bool.true → x9.left ∈ x4) ∧ (x12 = Bool.true → x9.right ∈ x4) ∧
        ((x9.op = fun (x13 x14 : Bool) => x13 != x11 && x14 != x12) ∨
         x9.op = fun (x13 x14 : Bool) => x13 != x11 || x14 != x12)) →
      ¬∀ (x10 : Fin (9 : ℕ) → Bool),
        (x3.eval (List.ofFn x10 ++ [x10 (3 : Fin (9 : ℕ)), Bool.false]) != x5) =
        [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (9 : ℕ) (x11 / (10 : ℕ))) && x10 (Fin.ofNat (9 : ℕ) (x11 % (10 : ℕ)))) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Finset ℕ) (x5 : Bool), x1 = (2 : Fin (9 : ℕ)) ∧ (x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (8 : Fin (9 : ℕ))) ∨ x1 = (3 : Fin (9 : ℕ)) ∧ x2 = (3 : Fin (9 : ℕ)) → x3.size ≤ (11 : ℕ) → (x5 = Bool.true → x3.output ∈ x4) → (∀ x9 ∈ x3.gates, ∃ (x11 : Bool) (x12 : Bool), (x11 = Bool.true → x9.left ∈ x4) ∧ (x12 = Bool.true → x9.right ∈ x4) ∧ ((x9.op = fun (x13 x14 : Bool) => x13 != x11 && x14 != x12) ∨ x9.op = fun (x13 x14 : Bool) => x13 != x11 || x14 != x12)) → ¬∀ (x10 : Fin (9 : ℕ) → Bool), (x3.eval (List.ofFn x10 ++ [x10 x1 || x10 x2, Bool.false]) != x5) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x11 : ℕ) => x10 (Fin.ofNat (9 : ℕ) (x11 / (10 : ℕ))) && x10 (Fin.ofNat (9 : ℕ) (x11 % (10 : ℕ))) := by
  intro x1 x2 x3 x4 x5 hcase hsize hout hgates hfun
  rcases hcase with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact c22 x3 x4 x5 hsize hout hgates (fun x10 => by simpa only [Bool.or_self] using hfun x10)
  · exact c23 x3 x4 x5 hsize hout hgates hfun
  · exact c28 x3 x4 x5 hsize hout hgates hfun
  · exact c33 x3 x4 x5 hsize hout hgates (fun x10 => by simpa only [Bool.or_self] using hfun x10)
