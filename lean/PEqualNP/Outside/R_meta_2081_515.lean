import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_2081_515
    (bridge : ∀ (C : Circuit) (b : Bool), IsAO2 26 C →
      lineSingle C 26 (fun i => if b then decide (i < 13) else decide (13 ≤ i)) 0 13 = false →
      ∃ t : ℕ → Bool,
        (∀ i < 26, t i = decide (i = if b then 0 else 13)) ∧
        (∀ (k : ℕ) (g : Gate) (a c : ℕ),
          C.gates[k]? = some g → g.inputs = [a,c] →
          let w := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if b then 13 else 0))
          (g.op = GateOp.and → t (26+k) = (w.getD a false && t c || t a && w.getD c false)) ∧
          (g.op = GateOp.or → t (26+k) = (t a || t c))) ∧ t C.output = false)
    (witness : ∃ C : Circuit, C.size ≤ 64 ∧ IsAO2 26 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ x y : Fin 13 → Bool, C.eval (List.ofFn (Fin.addCases x y)) = true ↔
        ∃ i j : Fin 13, (i = j ∨ i = j + 1 ∨ i = j + 3 ∨ i = j + 9) ∧ x i = true ∧ y j = true) ∧
      ∀ b : Bool, lineSingle C 26 (fun i => if b then decide (i < 13) else decide (13 ≤ i)) 0 13 = false) :have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false := by
  dsimp only
  obtain ⟨C,size,model,nodup,correct,trace⟩ := witness
  refine ⟨C,size,model,nodup,?_,?_,fun b => bridge C b model (trace b)⟩
  · intro p l h
    exact (correct _ _).mpr ⟨p,l,h,by simp,by simp⟩
  · intro x _
    let y := fun j : Fin 13 => !(x j || x (j + 1) || x (j + 3) || x (j + 9))
    change C.eval (List.ofFn (Fin.addCases x y)) = false
    cases h : C.eval (List.ofFn (Fin.addCases x y)) with
    | false => rfl
    | true =>
      obtain ⟨i,j,inc,hi,hj⟩ := (correct x y).mp h
      rcases inc with rfl | rfl | rfl | rfl <;> simp [y,hi] at hj