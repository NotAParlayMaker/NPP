import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4017 :
  have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop :=
    fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) =>
      ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),
        x4 = (26 : ℕ) + x5 ∧
        x1.gates[x5]? = Option.some x6 ∧
        (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧
        (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true);
  ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ)) (x4 : ℕ) (x5 : ℕ → Bool),
    have x6 : List Bool := x2.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x3));
    x5 x4 = Bool.true →
    (∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate) (x10 x11 : ℕ),
      x2.gates[x8]? = Option.some x9 → x9.inputs = [x10, x11] →
      (x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x8) =
        (x6.getD x10 Bool.false && x5 x11 || x5 x10 && x6.getD x11 Bool.false)) ∧
      (x9.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x8) = (x5 x10 || x5 x11))) →
    Relation.ReflTransGen (x1 x2 x3) x4 x2.output → x5 x2.output = Bool.true := by
  dsimp only
  intro circuit marked source active hsource hgates
  generalize circuit.output = targetWire
  intro hpath
  induction hpath with
  | refl => exact hsource
  | @tail fromWire _ _ hedge ih =>
      rcases hedge with ⟨index, gate, other, rfl, hgate, hinputs, hor | ⟨hand, hother⟩⟩
      · rcases hinputs with hinputs | hinputs
        · rw [(hgates index gate fromWire other hgate hinputs).2 hor]
          simp [ih]
        · rw [(hgates index gate other fromWire hgate hinputs).2 hor]
          simp [ih]
      · rcases hinputs with hinputs | hinputs
        · rw [(hgates index gate fromWire other hgate hinputs).1 hand]
          rw [hother, ih] <;> simp
        · rw [(hgates index gate other fromWire hgate hinputs).1 hand]
          rw [hother, ih] <;> simp
