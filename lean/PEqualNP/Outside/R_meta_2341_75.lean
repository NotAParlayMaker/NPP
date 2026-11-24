import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2341_75
    (transport : let delta : Finset (Fin 13) := {0,1,3,9}
    let flag := fun (p l : Fin 13) (b : Bool) =>
      (List.ofFn (fun z : Fin 13 => decide (z=p)) ++ List.ofFn (fun z : Fin 13 => decide (z=l))) ++ [b]
    let anti := fun (Q : Finset (Fin 13)) (b : Bool) =>
      (List.ofFn (fun p : Fin 13 => decide (p∈Q)) ++ List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ delta))) ++ [b]
    let quad := fun Q : Finset (Fin 13) => Q.card=4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p-l ∈ delta)).card≤2
    let back := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
      ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27+i.val
    let accepts := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13) (b : Bool) =>
      (∀ x y : Fin 13, x-y∈delta → x≠p ∨ y≠l → C.eval (flag x y b)=true) ∧
      ∀ Q : Finset (Fin 13), quad Q → C.eval (anti Q b)=false
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13) (b : Bool),
      PEqualNP.MetaComplexity.Monotone2 C → back C → accepts C p l b →
      ∃ A : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 A ∧
        back A ∧ accepts A 0 0 false ∧ A.size = C.size)
    (fixed : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ 0 ∨ x12 ≠ 0 → x1.eval (x8 x11 x12 ++ [false]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [false]) = Bool.false) → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C p l bit hm hb
  dsimp only
  intro positive negative
  obtain ⟨A,hA,hB,hs,sz⟩ := transport C p l bit hm hb ⟨positive,negative⟩
  exact sz ▸ fixed A hA hB hs.1 hs.2
