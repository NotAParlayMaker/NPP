import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4732_1
    (hsmall : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ Q : Finset (Fin 13),
        Q.card = 4 →
        (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
        C.eval (((List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) ++ [b]) = false) →
      ∀ S : Finset (Fin 26), S.card ≤ 1 →
        C.eval ((List.ofFn fun i : Fin 26 => decide (i ∈ S)) ++ [b]) = false)
    (hpair : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ Q : Finset (Fin 13),
        Q.card = 4 →
        (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
        C.eval (((List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) ++ [b]) = false) →
      ∀ S : Finset (Fin 26), S.card = 2 →
        C.eval ((List.ofFn fun i : Fin 26 => decide (i ∈ S)) ++ [b]) = true →
        ∃ p l : Fin 13,
          p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          S = ({⟨p.val, by omega⟩, ⟨13 + l.val, by omega⟩} : Finset (Fin 26)))
    (hcount : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool) (x6 : Fin 13),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
        (p ≠ 0 ∨ l ≠ x6) →
        C.eval (((List.ofFn fun i : Fin 13 => decide (i = p)) ++
          List.ofFn fun i : Fin 13 => decide (i = l)) ++ [b]) = true) →
      (∀ S : Finset (Fin 26), S.card ≤ 1 →
        C.eval ((List.ofFn fun i : Fin 26 => decide (i ∈ S)) ++ [b]) = false) →
      (∀ S : Finset (Fin 26), S.card = 2 →
        C.eval ((List.ofFn fun i : Fin 26 => decide (i ∈ S)) ++ [b]) = true →
        ∃ p l : Fin 13,
          p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
          S = ({⟨p.val, by omega⟩, ⟨13 + l.val, by omega⟩} : Finset (Fin 26))) →
      63 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
    have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun x2 x3 =>
      (List.ofFn fun x4 : Fin (13 : ℕ) => decide (x4 = x2)) ++
      List.ofFn fun x4 : Fin (13 : ℕ) => decide (x4 = x3);
    have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun x3 =>
      (List.ofFn fun x4 : Fin (13 : ℕ) => decide (x4 ∈ x3)) ++
      List.ofFn fun x4 : Fin (13 : ℕ) => decide (∀ x5 ∈ x3, x5 - x4 ∉ x1);
    have x4 : Finset (Fin (13 : ℕ)) → Prop := fun x4 =>
      x4.card = 4 ∧ ∀ x5 : Fin (13 : ℕ), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ 2;
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ (x9 : Fin C.gates.length) (x10 : ℕ), x10 ∈ (C.gates.get x9).inputs → x10 < 27 + ↑x9) →
      (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ 0 ∨ x11 ≠ x6 →
        C.eval (x2 x10 x11 ++ [x7]) = true) →
      (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → C.eval (x3 x11 ++ [x7]) = false) →
      63 ≤ C.size := by
  intro x1 x2 x3 x4 C x6 x7 hM hRB hpos hneg
  apply hcount C x7 x6 hM
  · intro p l hp hne
    simpa [x1, x2] using hpos p l (by simpa [x1] using hp) hne
  · exact hsmall C x7 hM (by
      intro Q hcard hline
      have hQ : x4 Q := ⟨hcard, by intro l; simpa [x1] using hline l⟩
      simpa [x1, x3] using hneg Q hQ)
  · exact hpair C x7 hM (by
      intro Q hcard hline
      have hQ : x4 Q := ⟨hcard, by intro l; simpa [x1] using hline l⟩
      simpa [x1, x3] using hneg Q hQ)
