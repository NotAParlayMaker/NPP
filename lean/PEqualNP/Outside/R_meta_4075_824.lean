import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4075_824
    (hSupport : let f : (Fin 10 → Bool) → Bool := fun x =>
        (List.finRange 5).any (fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))));
      ∀ a b : (Fin 10 → Bool) → Bool, (∀ x, (a x && b x) = f x) →
        (∀ i : Fin 10, ∃ x, a x ≠ a (Function.update x i true)) ∨
        (∀ i : Fin 10, ∃ x, b x ≠ b (Function.update x i true)))
    (hCircuit : let f : (Fin 10 → Bool) → Bool := fun x =>
        (List.finRange 5).any (fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))));
      ∀ (s : Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 17 →
        let w : (Fin 10 → Bool) → ℕ → Bool := fun x i =>
          (C.wires (List.ofFn x ++ [x 0 && if s then x 1 else x 2])).getD i false;
        (∀ x, (w x u && w x v) = f x) →
        (∀ j : Fin 10, ∃ x, w x u ≠ w (Function.update x j true) u) →
        (∃ x, w x u = true ∧ w x v = false) →
        (∃ x, w x u = false ∧ w x v = true) → False) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro s C u v hC hsize f w huv hvu hcover
  by_contra hfalse
  have hAnd (x : Fin 10 → Bool) : (w x u && w x v) = f x := by
    cases hf : f x with
    | false =>
      cases hu : w x u <;> cases hv : w x v <;> try rfl
      exact False.elim (hfalse ⟨x, hf, hu, hv⟩)
    | true =>
      obtain ⟨hu, hv⟩ := hcover x hf
      simp [hu, hv]
  let p : (Fin 10 → Bool) → Bool := fun x =>
    (List.finRange 5).any (fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))
  have hp (x : Fin 10 → Bool) : p x = f x := by
    change ((((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) ||
      false)))))) = f x
    dsimp only [f]
    simp only [Bool.or_false]
    ac_rfl
  have hP (x : Fin 10 → Bool) : (w x u && w x v) = p x := (hAnd x).trans (hp x).symm
  rcases hSupport (fun x => w x u) (fun x => w x v) hP with h | h
  · exact hCircuit s C u v hC hsize hP h huv hvu
  · exact hCircuit s C v u hC hsize
      (fun x => (Bool.and_comm _ _).trans (hP x)) h
      (by obtain ⟨x, h1, h2⟩ := hvu; exact ⟨x, h2, h1⟩)
      (by obtain ⟨x, h1, h2⟩ := huv; exact ⟨x, h2, h1⟩)
