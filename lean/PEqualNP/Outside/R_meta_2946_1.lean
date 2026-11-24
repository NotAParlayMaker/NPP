import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2946_1
    (hlow : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (htwo : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → (2 : ℕ) ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))
    (hzero : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))
    (hcore : ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x3 ∈ x2.gates, x3.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → x2.size = (13 : ℕ) → (∀ (x4 : Bool), ∃ (x6 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), x4]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) → ∃ (x6 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), !x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → x2.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), !x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro i C hfan _hpos hsize
  by_contra hcon
  push Not at hcon
  -- Wires of the circuit with a gate AND(x0, x2) and a gate g2 put in front of `C`.
  have hfront : ∀ (g2 : Gate) (x : Fin 9 → Bool),
      Circuit.wires ⟨⟨GateOp.and, [0, 2]⟩ :: g2 :: C.gates, C.output⟩ (List.ofFn x)
        = C.wires (List.ofFn x ++ [x 0 && x 2,
            g2.op.eval (g2.inputs.map fun j => (List.ofFn x ++ [x 0 && x 2]).getD j false)]) := by
    intro g2 x
    have hand : GateOp.and.eval ([0, 2].map fun j => (List.ofFn x).getD j false)
        = (x 0 && x 2) := by
      show (x 0 && (x 2 && true)) = (x 0 && x 2)
      rw [Bool.and_true]
    have e1 : Circuit.wires ⟨⟨GateOp.and, [0, 2]⟩ :: g2 :: C.gates, C.output⟩ (List.ofFn x)
        = C.wires ((List.ofFn x ++ [GateOp.and.eval ([0, 2].map fun j => (List.ofFn x).getD j false)])
          ++ [g2.op.eval (g2.inputs.map fun j => (List.ofFn x ++
            [GateOp.and.eval ([0, 2].map fun j => (List.ofFn x).getD j false)]).getD j false)]) := rfl
    rw [e1, hand, List.append_assoc]
    rfl
  -- The bits of the input list survive every gate.
  have hpre : ∀ (gs : List Gate) (w : List Bool), ∃ t : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w
        = w ++ t := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
      refine ⟨g.op.eval (g.inputs.map fun j => w.getD j false) :: t, ?_⟩
      rw [List.foldl_cons, ht]
      simp
  have hwire9 : ∀ (g2 : Gate) (x : Fin 9 → Bool),
      (Circuit.wires ⟨⟨GateOp.and, [0, 2]⟩ :: g2 :: C.gates, C.output⟩ (List.ofFn x)).getD 9 false
        = (x 0 && x 2) := by
    intro g2 x
    rw [hfront]
    obtain ⟨t, ht⟩ := hpre C.gates (List.ofFn x ++ [x 0 && x 2,
      g2.op.eval (g2.inputs.map fun j => (List.ofFn x ++ [x 0 && x 2]).getD j false)])
    have hw : C.wires (List.ofFn x ++ [x 0 && x 2,
        g2.op.eval (g2.inputs.map fun j => (List.ofFn x ++ [x 0 && x 2]).getD j false)])
        = (List.ofFn x ++ [x 0 && x 2,
        g2.op.eval (g2.inputs.map fun j => (List.ofFn x ++ [x 0 && x 2]).getD j false)]) ++ t := ht
    rw [hw, List.getD_append _ _ _ _ (by simp)]
    simp
  have hfun : ∀ (g2 : Gate) (x : Fin 9 → Bool),
      circuitFun 9 ⟨⟨GateOp.and, [0, 2]⟩ :: g2 :: C.gates, C.output⟩ x
        = C.eval (List.ofFn x ++ [x 0 && x 2,
            g2.op.eval (g2.inputs.map fun j => (List.ofFn x ++ [x 0 && x 2]).getD j false)]) := by
    intro g2 x
    show (Circuit.wires ⟨⟨GateOp.and, [0, 2]⟩ :: g2 :: C.gates, C.output⟩ (List.ofFn x)).getD
      C.output false = _
    rw [hfront]
    rfl
  have hfan2 : ∀ g2 : Gate, g2.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      g2.inputs.length ≤ 2 →
      FanInTwo ⟨⟨GateOp.and, [0, 2]⟩ :: g2 :: C.gates, C.output⟩ := by
    intro g2 hop hlen g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact ⟨hop, hlen⟩
    · exact hfan g hg
  have hsize2 : ∀ g2 : Gate,
      (⟨⟨GateOp.and, [0, 2]⟩ :: g2 :: C.gates, C.output⟩ : Circuit).size = C.size + 2 := by
    intro g2
    show (_ :: _ :: C.gates).length = C.gates.length + 2
    rfl
  -- The circuit with NOT x_i in front computes the edge function.
  let gN : Gate := ⟨GateOp.not, [i.val]⟩
  have hNval : ∀ x : Fin 9 → Bool,
      gN.op.eval (gN.inputs.map fun j => (List.ofFn x ++ [x 0 && x 2]).getD j false) = !x i := by
    intro x
    fin_cases i <;> rfl
  have key := hlow ⟨⟨GateOp.and, [0, 2]⟩ :: gN :: C.gates, C.output⟩
    (hfan2 gN (by simp [gN]) (by simp [gN])) (hwire9 gN)
    (by funext x; rw [hfun, hNval]; exact hcon x)
  rw [hsize2] at key
  have h13 : C.size = 13 := by omega
  by_cases hn : 1 ≤ C.gates.countP
      (fun g : Gate => GateOp.rec false false true (fun _ => false) false g.op)
  · exact htwo ⟨⟨GateOp.and, [0, 2]⟩ :: gN :: C.gates, C.output⟩
      (hfan2 gN (by simp [gN]) (by simp [gN])) (hwire9 gN) (by rw [hsize2]; omega)
      (by
        simp only [List.countP_cons, gN, ↓reduceIte, Bool.false_eq_true]
        omega)
      (by funext x; rw [hfun, hNval]; exact hcon x)
  · have hz : C.gates.countP
        (fun g : Gate => GateOp.rec false false true (fun _ => false) false g.op) = 0 := by
      omega
    have hnot : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
      intro g hg hop
      have hpos : 0 < C.gates.countP
          (fun g : Gate => GateOp.rec false false true (fun _ => false) false g.op) :=
        List.countP_pos_iff.mpr ⟨g, hg, by simp [hop]⟩
      omega
    obtain ⟨x, hx⟩ := hcore i C hfan hnot h13 (by
      intro b
      by_contra h
      push Not at h
      cases b
      · exact hzero ⟨⟨GateOp.and, [0, 2]⟩ :: ⟨GateOp.or, []⟩ :: C.gates, C.output⟩
          (hfan2 _ (by simp) (by simp)) (hwire9 _) (by rw [hsize2]; omega)
          (by simp only [List.countP_cons]; simp [hz])
          (by funext x; rw [hfun]; exact h x)
      · exact hzero ⟨⟨GateOp.and, [0, 2]⟩ :: ⟨GateOp.and, []⟩ :: C.gates, C.output⟩
          (hfan2 _ (by simp) (by simp)) (hwire9 _) (by rw [hsize2]; omega)
          (by simp only [List.countP_cons]; simp [hz])
          (by funext x; rw [hfun]; exact h x))
    exact hx (hcon x)
