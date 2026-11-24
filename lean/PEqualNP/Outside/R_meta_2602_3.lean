import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_2602_3
    (branch : ∀ (C : Circuit) (p q : ℕ) (v : ℕ → Bool),
      let S := fun w : ℕ => (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = p))).getD w false
      let T := fun w : ℕ => (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = p ∨ i.val = q))).getD w false
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) → (∀ j < 26, v j = decide (j = q)) →
      (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → v (26+j) = (S a && v b || v a && S b)) ∧
        (g.op = .or → v (26+j) = (v a || v b))) → T C.output = true → S C.output = false → v C.output = false →
      ∃ g ∈ C.gates, g.op = .and ∧ ∀ z ∈ g.inputs, T z = true ∧ S z = false)
    (paths : ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u l : Fin 13,
        (u = l ∨ u = l+1 ∨ u = l+3 ∨ u = l+9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 l) = true) →
      let S := fun (p w : ℕ) => (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = p))).getD w false
      let T := fun w : ℕ => (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0 ∨ i.val = 13))).getD w false
      let blocked := fun p : ℕ => ∃ g ∈ C.gates, g.op = .and ∧ ∀ z ∈ g.inputs, T z = true ∧ S p z = false
      let step := fun p u w : ℕ => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ w = 26+j ∧ u ∈ g.inputs ∧
        (g.op = .or ∨ ∀ z ∈ g.inputs, z ≠ u → S p z = true)
      blocked 0 → blocked 13 → Relation.ReflTransGen (step 0) 13 C.output ∨
        Relation.ReflTransGen (step 13) 0 C.output) :
¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  rintro ⟨C, lo, hi, legal, computes, ⟨v, vr, vs, vz⟩, ⟨y, yr, ys, yz⟩⟩
  let S := fun (p w : ℕ) => (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = p))).getD w false
  let T := fun w : ℕ => (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0 ∨ i.val = 13))).getD w false
  let step := fun p u w : ℕ => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ w = 26+j ∧ u ∈ g.inputs ∧
        (g.op = .or ∨ ∀ z ∈ g.inputs, z ≠ u → S p z = true)
  have empty (p : ℕ) : S p C.output = false := by
    cases h : S p C.output with
    | false => rfl
    | true =>
      obtain ⟨u,l,_,hu,hl⟩ := (computes _).mp h
      simp only [decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at hu hl
      omega
  have pair : T C.output = true := (computes _).mpr ⟨0,0,Or.inl rfl,by decide,by decide⟩
  have fwd := branch C 0 13 v legal vr vs pair (empty 0) vz
  have revPair : (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13 ∨ i.val = 0))).getD C.output false = true := by
    simpa only [T, or_comm] using pair
  have rev := branch C 13 0 y legal yr ys revPair (empty 13) yz
  have back : ∃ g ∈ C.gates, g.op = .and ∧ ∀ z ∈ g.inputs, T z = true ∧ S 13 z = false := by
    simpa only [T, S, or_comm] using rev
  have run (p q : ℕ) (w : ℕ → Bool) (hq : q < 26) (raw : ∀ j < 26, w j = decide (j = q))
      (law : (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → w (26+j) = (S p a && w b || w a && S p b)) ∧
        (g.op = .or → w (26+j) = (w a || w b))))
      (path : Relation.ReflTransGen (step p) q C.output) : w C.output = true := by
    have push {u t : ℕ} (prev : w u = true) (edge : step p u t) : w t = true := by
      obtain ⟨j,g,hg,rfl,mem,pass⟩ := edge
      obtain ⟨op,a,b,ins,ne,_,_⟩ := legal j g hg
      have dual := law j g a b hg ins
      have member : u = a ∨ u = b := by simpa [ins] using mem
      rcases op with ha | ho
      · have rest := pass.resolve_left (by simp [ha])
        rcases member with rfl | rfl
        · have on := rest b (by simp [ins]) ne.symm
          simp [dual.1 ha, prev, on]
        · have on := rest a (by simp [ins]) ne
          simp [dual.1 ha, prev, on]
      · rcases member with rfl | rfl <;> simp [dual.2 ho, prev]
    have follow (t : ℕ) (h : Relation.ReflTransGen (step p) q t) : w t = true := by
      induction h with
      | refl => simpa using raw q hq
      | tail _ edge ih => exact push ih edge
    exact follow C.output path
  rcases paths C lo hi legal computes fwd back with a | b
  · exact Bool.noConfusion (vz.symm.trans (run 0 13 v (by decide) vr vs a))
  · exact Bool.noConfusion (yz.symm.trans (run 13 0 y (by decide) yr ys b))

