import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3821_2
  (hMono : (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) → (14 : ℕ) ≤ x2.size → (10 : ℕ) ≤ x3 → x3 < (10 : ℕ) + x2.size → (10 : ℕ) ≤ x4 → x4 < (10 : ℕ) + x2.size → (∀ g ∈ x2.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →        have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12)))
  (hNot : (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) → (14 : ℕ) ≤ x2.size → (10 : ℕ) ≤ x3 → x3 < (10 : ℕ) + x2.size → (10 : ℕ) ≤ x4 → x4 < (10 : ℕ) + x2.size → (∃ g ∈ x2.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →        have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12))) :
  (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12)) := by

  dsimp only
  intro x2 x3 x4 hfan hsize hd1 hd2 hmatch
  let F : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (j : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) j) && x1 (Fin.castAdd (5 : ℕ) (j + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) j) && x1 (Fin.natAdd (5 : ℕ) j) || x1 (Fin.natAdd (5 : ℕ) j) && x1 (Fin.natAdd (5 : ℕ) (j + (2 : Fin (5 : ℕ))))
  have hmatch' : ∀ x : Fin (10 : ℕ) → Bool, F x = false →
      ((x2.wires (List.ofFn x)).getD x3 false || (x2.wires (List.ofFn x)).getD x4 false) = F x := by
    intro x hx
    exact hmatch x (Or.inl hx)
  let wf : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool :=
    fun gs w => gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wf_eq : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool), D.wires x = wf D.gates x :=
    fun D x => rfl
  have wf_append : ∀ (p q : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wf (p ++ q) w = wf q (wf p w) := by
    intro p q w
    simp [wf, List.foldl_append]
  have wf_length : ∀ (p : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wf p w).length = w.length + p.length := by
    intro p
    induction p with
    | nil => intro w; simp [wf]
    | cons g p ih =>
        intro w
        show (wf p (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
        rw [ih]
        simp
        omega
  have wf_getD : ∀ (p : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (wf p w).getD i false = w.getD i false := by
    intro p
    induction p with
    | nil => intro w i hi; simp [wf]
    | cons g p ih =>
        intro w i hi
        show (wf p (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
        rw [ih _ _ (by simp; omega)]
        rw [List.getD_append _ _ _ _ hi]
  have wf_snoc : ∀ (p : List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wf (p ++ [g]) w = (wf p w) ++ [g.op.eval (g.inputs.map fun i => (wf p w).getD i false)] := by
    intro p g w
    rw [wf_append]
    simp [wf]
  have wires_in : ∀ (x : Fin (10 : ℕ) → Bool) (i : Fin (10 : ℕ)),
      (x2.wires (List.ofFn x)).getD i.val false = x i := by
    intro x i
    rw [wf_eq, wf_getD _ _ _ (by simpa using i.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
  have wires_out : ∀ (x : Fin (10 : ℕ) → Bool) (i : ℕ), 10 + x2.size ≤ i →
      (x2.wires (List.ofFn x)).getD i false = false := by
    intro x i hi
    rw [wf_eq]
    apply List.getD_eq_default
    rw [wf_length]
    have hs : x2.size = x2.gates.length := rfl
    simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  by_cases hsmall : x2.size ≤ 13
  · let g0 : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
    let g1 : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [x3, x4]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[g0] ++ (x2.gates ++ [g1]), 10 + x2.size⟩
    have hsz : D.size ≤ 15 := by
      show ([g0] ++ (x2.gates ++ [g1])).length ≤ 15
      rw [List.length_append, List.length_append]
      simp only [g0, g1, List.length_cons, List.length_nil]
      have hs : x2.size = x2.gates.length := rfl
      omega
    have hfanD : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      simp only [D, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        false_or, or_false] at hg
      rcases hg with rfl | hg | rfl
      · exact ⟨by simp [g0], by simp [g0]⟩
      · exact hfan g hg
      · exact ⟨by simp [g1], by simp [g1]⟩
    refine ⟨Equiv.refl _, false, D, ?_, hfanD, ?_, ?_⟩
    · intro x
      rfl
    · show D.size ≤ if (false = true) then (10 : ℕ) else 15
      rw [if_neg (by decide)]
      exact hsz
    · intro y
      have hlast : List.ofFn (fun i : Fin ((9 : ℕ) + (1 : ℕ)) => Fin.lastCases false y i) =
          List.ofFn y ++ [false] := by
        rw [List.ofFn_succ']
        simp only [Fin.lastCases_castSucc]
        rfl
      have heval : D.eval (List.ofFn y) =
          ((x2.wires (List.ofFn y ++ [false])).getD x3 false ||
            (x2.wires (List.ofFn y ++ [false])).getD x4 false) := by
        show (wf ([g0] ++ (x2.gates ++ [g1])) (List.ofFn y)).getD (10 + x2.size) false =
          ((x2.wires (List.ofFn y ++ [false])).getD x3 false ||
            (x2.wires (List.ofFn y ++ [false])).getD x4 false)
        rw [wf_append]
        have hg0 : wf [g0] (List.ofFn y) = List.ofFn y ++ [false] := by
          simp [wf, g0, PEqualNP.CircuitLowerBounds.GateOp.eval]
        rw [hg0, wf_snoc]
        simp only [g1, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, Bool.or_false]
        have hlen : (wf x2.gates (List.ofFn y ++ [false])).length = 10 + x2.size := by
          rw [wf_length]
          simp [PEqualNP.CircuitLowerBounds.Circuit.size]
        rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
        rw [hlen, Nat.sub_self]
        simp [wf_eq]
      rw [heval]
      simp only [Equiv.coe_refl, Function.comp_id]
      rw [hlast]
  · have h14 : 14 ≤ x2.size := by omega
    by_cases hgate : 10 ≤ x3 ∧ x3 < 10 + x2.size ∧ 10 ≤ x4 ∧ x4 < 10 + x2.size
    · by_cases hmono : ∀ g ∈ x2.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
      · exact hMono x2 x3 x4 hfan hsize h14 hgate.1 hgate.2.1 hgate.2.2.1 hgate.2.2.2 hmono hd1 hd2 hmatch
      · push_neg at hmono
        exact hNot x2 x3 x4 hfan hsize h14 hgate.1 hgate.2.1 hgate.2.2.1 hgate.2.2.2 hmono hd1 hd2 hmatch
    · exfalso
      have hsingle : ∀ i : Fin (10 : ℕ), F (fun j : Fin (10 : ℕ) => decide (j = i)) = false := by
        intro i
        exact (by decide : ∀ i : Fin (10 : ℕ),
          F (fun j : Fin (10 : ℕ) => decide (j = i)) = false) i
      have ha : 10 ≤ x3 ∧ x3 < 10 + x2.size := by
        rcases (by omega : x3 < 10 ∨ (10 ≤ x3 ∧ x3 < 10 + x2.size) ∨ 10 + x2.size ≤ x3) with h | h | h
        · let i : Fin (10 : ℕ) := ⟨x3, h⟩
          have hw : (x2.wires (List.ofFn (fun j : Fin (10 : ℕ) => decide (j = i)))).getD x3 false = true := by
            simpa [i] using wires_in (fun j : Fin (10 : ℕ) => decide (j = i)) i
          have hm := hmatch' (fun j : Fin (10 : ℕ) => decide (j = i)) (hsingle i)
          rw [hw, hsingle i] at hm
          simp at hm
        · exact h
        · obtain ⟨x, hx, _⟩ := hd1
          rw [wires_out x x3 h] at hx
          simp at hx
      have hb : 10 ≤ x4 ∧ x4 < 10 + x2.size := by
        rcases (by omega : x4 < 10 ∨ (10 ≤ x4 ∧ x4 < 10 + x2.size) ∨ 10 + x2.size ≤ x4) with h | h | h
        · let i : Fin (10 : ℕ) := ⟨x4, h⟩
          have hw : (x2.wires (List.ofFn (fun j : Fin (10 : ℕ) => decide (j = i)))).getD x4 false = true := by
            simpa [i] using wires_in (fun j : Fin (10 : ℕ) => decide (j = i)) i
          have hm := hmatch' (fun j : Fin (10 : ℕ) => decide (j = i)) (hsingle i)
          rw [hw, hsingle i] at hm
          simp at hm
        · exact h
        · obtain ⟨x, _, hx⟩ := hd2
          rw [wires_out x x4 h] at hx
          simp at hx
      exact hgate ⟨ha.1, ha.2, hb.1, hb.2⟩
