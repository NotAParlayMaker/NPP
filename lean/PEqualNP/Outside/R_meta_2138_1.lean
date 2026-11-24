import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2138_1
    (h_0 : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 12 ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn (Fin.snoc x (!(x 0)) : Fin 9 → Bool)) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4)))
    (h_1 : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 12 ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn (Fin.snoc x (!(x 1)) : Fin 9 → Bool)) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4)))
    (h_project : ∀ (f : (Fin 9 → Bool) → Bool),
      (f (fun j => decide (j = 1)) ≠ f (fun j => decide (j = 1 ∨ j = 6))) →
      (f (Fin.insertNth (6 : Fin 9) false (fun _ => false)) ≠
      f (Fin.insertNth (6 : Fin 9) false (fun _ => true))) → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ g ∈ C.gates[1]?.toList, 9 ∈ g.inputs) → PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = f →
    ∃ i : Fin 8, ∀ σ : Fin 8 → Fin 8, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size+3 ≤ C.size ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn (Fin.snoc y (!(y (σ i))) : Fin 9 → Bool)) =
        f (Fin.insertNth (6 : Fin 9) false (y ∘ σ))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∃ x2 ∈ x1.gates[(1 : ℕ)]?.toList, (9 : ℕ) ∈ x2.inputs) → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C second fan first computes
  by_contra! small
  let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let f8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  let rot : Fin 8 → Fin 8 → Fin 8 := ![
    ![0,1,2,3,4,5,6,7],
    ![0,1,2,3,4,5,6,7],
    ![3,2,1,0,7,6,5,4],
    ![3,2,1,0,7,6,5,4],
    ![0,4,7,3,1,6,5,2],
    ![5,1,2,6,7,0,3,4],
    ![5,7,4,6,1,3,0,2],
    ![3,7,4,0,2,5,6,1]]
  let toMinor : Fin 8 → Fin 8 := ![1,0,4,7,5,2,6,3]
  obtain ⟨i,project⟩ := h_project f (by decide) (by decide) C second fan first computes
  let σ := (rot (toMinor i)) ∘ toMinor
  obtain ⟨D,ok,cost,eval⟩ := project σ
  have dsize : D.size ≤ 12 := by omega
  -- The eight vertex relabelings take the complemented input to one of two orbit representatives.
  have rows : ∀ (j : Fin 8) (a b c d e f' g h : Bool),
      let y : Fin 8 → Bool := ![a,b,c,d,e,f',g,h]
      let ρ := (rot (toMinor j)) ∘ toMinor
      (ρ j = 0 ∨ ρ j = 1) ∧ f (Fin.insertNth (6 : Fin 9) false (y ∘ ρ)) = f8 y := by
    decide +kernel
  have orbit : σ i = 0 ∨ σ i = 1 := (rows i false false false false false false false false).1
  have values (y : Fin 8 → Bool) : f (Fin.insertNth (6 : Fin 9) false (y ∘ σ)) = f8 y := by
    have unroll : y = ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7] := by
      funext j
      fin_cases j <;> rfl
    rw [unroll]
    exact (rows i _ _ _ _ _ _ _ _).2
  rcases orbit with h|h
  · apply h_0
    exact ⟨D,ok,dsize,fun y => (h ▸ eval y).trans (values y)⟩
  · apply h_1
    exact ⟨D,ok,dsize,fun y => (h ▸ eval y).trans (values y)⟩
