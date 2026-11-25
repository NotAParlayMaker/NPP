import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2619_626
  (h1 : let good := fun (D : Circuit) (U : Finset (Fin 13)) =>
      (IsAO2 26 D ∧ ∀ g ∈ D.gates, g.inputs.Nodup) ∧ (26 ≤ D.output ∧ D.output < 26+D.size) ∧
      ∀ p l : Fin 13 → Bool, D.eval (List.ofFn fun k : Fin (13+13) => Fin.addCases p l k) = true ↔
        ∃ i ∈ U, (l i && (p i || p (i+1) || p (i+3) || p (i+9))) = true
    ∃ (U : Finset (Fin 13)) (D : Circuit), 1 ∉ U ∧ D.size+2 ≤ 5*U.card ∧ good D U)
  (h2 : let good := fun (D : Circuit) (U : Finset (Fin 13)) =>
      (IsAO2 26 D ∧ ∀ g ∈ D.gates, g.inputs.Nodup) ∧ (26 ≤ D.output ∧ D.output < 26+D.size) ∧
      ∀ p l : Fin 13 → Bool, D.eval (List.ofFn fun k : Fin (13+13) => Fin.addCases p l k) = true ↔
        ∃ i ∈ U, (l i && (p i || p (i+1) || p (i+3) || p (i+9))) = true
    ∀ (U : Finset (Fin 13)) (D : Circuit), 1 ∉ U → good D U →
      ∃ E : Circuit, E.size + 5*U.card = D.size + 60 ∧ good E (Finset.univ.erase (1 : Fin 13)))
  (h3 : let good := fun (D : Circuit) (U : Finset (Fin 13)) =>
      (IsAO2 26 D ∧ ∀ g ∈ D.gates, g.inputs.Nodup) ∧ (26 ≤ D.output ∧ D.output < 26+D.size) ∧
      ∀ p l : Fin 13 → Bool, D.eval (List.ofFn fun k : Fin (13+13) => Fin.addCases p l k) = true ↔
        ∃ i ∈ U, (l i && (p i || p (i+1) || p (i+3) || p (i+9))) = true
    ∀ D : Circuit, good D (Finset.univ.erase (1 : Fin 13)) →
      ∃ C : Circuit, C.size = D.size+6 ∧ good C Finset.univ ∧ ∃ j a b : ℕ, C.output = 26+j ∧ C.gates[j]? = some ⟨.and,[a,b]⟩ ∧
          ∀ s : Bool, let w := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if s then 13 else 0))
                      w.getD a false = false ∧ w.getD b false = false)
    : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false := by
  obtain ⟨U,D,skip,small,good⟩ := h1
  obtain ⟨E,t,done⟩ := h2 U D skip good
  obtain ⟨C,sz,⟨⟨ao,distinct⟩,_,spec⟩,last⟩ := h3 E done
  refine ⟨C,by omega,ao,distinct,?_,last⟩
  intro p l
  simpa only [Finset.mem_univ,true_and,Bool.and_eq_true] using spec p l
