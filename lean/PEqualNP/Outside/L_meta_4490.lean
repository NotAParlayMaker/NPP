import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4490

lemma foldl_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_getD_of_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp
      omega
    rw [ih _ hi']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_eq_false_of_le (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma not_eval_eq_getD (w : List Bool) (hw : w.length = 13) (inputs : List ℕ) :
    PEqualNP.CircuitLowerBounds.GateOp.not.eval (inputs.map fun j => w.getD j false) =
      !(w.getD (min (inputs.headD 13) 13) false) := by
  cases inputs with
  | nil =>
    simp only [List.map_nil, List.headD_nil, min_self, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.headD_nil]
    rw [getD_eq_false_of_le w 13 (by omega)]
  | cons i tl =>
    simp only [List.map_cons, List.headD_cons, PEqualNP.CircuitLowerBounds.GateOp.eval]
    by_cases h : i < 13
    · have hmin : min i 13 = i := Nat.min_eq_left (Nat.le_of_lt h)
      rw [hmin]
    · have hle : 13 ≤ i := Nat.le_of_not_lt h
      have hmin : min i 13 = 13 := Nat.min_eq_right hle
      rw [hmin, getD_eq_false_of_le w i (by omega), getD_eq_false_of_le w 13 (by omega)]

end PEqualNP.Outside.L_meta_4490

theorem PEqualNP.Outside.L_meta_4490 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (4 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) →       (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) →         ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)),           x5.size = (3 : ℕ) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               x6.size + (5 : ℕ) = x1.size ∧                 PEqualNP.MetaComplexity.FanInTwo x6 ∧                   (∃! x8 : Fin x6.gates.length, (x6.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧                     ∀ (x8 : Fin (9 : ℕ) → Bool),                       have x9 : List Bool := x5.wires (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ))]);                       x6.eval (x9 ++ [!x9.getD (↑x7) Bool.false]) = x1.eval (List.ofFn x8) := by
  intro x1 hF hnot hw9
  rcases x1 with ⟨gates, out⟩
  rcases hnot with ⟨x3, x4, hx34, hx3_val, hx3_not, hx4_not, huniq⟩
  rcases gates with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, rest⟩⟩⟩⟩⟩
  · have h := x3.isLt; dsimp at h; omega
  · have h := x3.isLt; dsimp at h; omega
  · have h := x3.isLt; dsimp at h; omega
  · have h := x3.isLt; dsimp at h; omega
  · have h := x3.isLt; dsimp at h; omega
  have hx3_eq : x3 = ⟨4, by simp⟩ := Fin.ext hx3_val
  have hg4_not : g4.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    rw [hx3_eq] at hx3_not
    exact hx3_not
  have hx34_val : (x3 : ℕ) < (x4 : ℕ) := hx34
  have hx4_lt : (x4 : ℕ) < rest.length + 5 := by
    have h := x4.isLt
    simp only [List.length_cons] at h
    exact h
  refine ⟨⟨[g1, g2, g3], 0⟩, ⟨rest, out⟩, ⟨min (g4.inputs.headD 13) 13, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro g hg
    have hg_mem : g ∈ g0 :: g1 :: g2 :: g3 :: g4 :: rest := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
      rcases hg with rfl | rfl | rfl <;> simp
    have ⟨hop, hlen⟩ := hF g hg_mem
    refine ⟨?_, hlen⟩
    have hne : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro hgn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · have h1 := huniq ⟨1, by simp⟩ hgn
        rcases h1 with h1 | h1
        · have := congrArg Fin.val h1; simp at this; omega
        · have := congrArg Fin.val h1; simp at this; omega
      · have h2 := huniq ⟨2, by simp⟩ hgn
        rcases h2 with h2 | h2
        · have := congrArg Fin.val h2; simp at this; omega
        · have := congrArg Fin.val h2; simp at this; omega
      · have h3 := huniq ⟨3, by simp⟩ hgn
        rcases h3 with h3 | h3
        · have := congrArg Fin.val h3; simp at this; omega
        · have := congrArg Fin.val h3; simp at this; omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hne h)
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro g hg
    exact hF g (by simp [hg])
  · refine ⟨⟨(x4 : ℕ) - 5, by dsimp; omega⟩, ?_, ?_⟩
    · have hx4_eq : x4 = ⟨(x4 : ℕ) - 5 + 5, by simp only [List.length_cons]; omega⟩ := by
        ext
        dsimp
        omega
      rw [hx4_eq] at hx4_not
      exact hx4_not
    · intro k hk
      have hk_lt : (k : ℕ) < rest.length := k.isLt
      have hk' := huniq ⟨(k : ℕ) + 5, by simp only [List.length_cons]; omega⟩ hk
      rcases hk' with hk' | hk'
      · have hval := congrArg Fin.val hk'
        dsimp at hval
        omega
      · have hval := congrArg Fin.val hk'
        ext
        dsimp at hval ⊢
        omega
  · intro x8
    dsimp only
    let v0 : List Bool := List.ofFn x8
    let b0 : Bool := g0.op.eval (g0.inputs.map fun i => v0.getD i false)
    have hv0_len : v0.length = 9 := by simp [v0]
    have hb0 : b0 = (x8 0 || x8 2) := by
      have h9 := hw9 x8
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons] at h9
      have hlt : 9 < (v0 ++ [b0]).length := by simp [hv0_len]
      have hfold := PEqualNP.Outside.L_meta_4490.foldl_getD_of_lt (g1 :: g2 :: g3 :: g4 :: rest) (v0 ++ [b0]) 9 hlt
      have h9' : (v0 ++ [b0]).getD 9 false = (x8 0 || x8 2) := by
        rw [← hfold]
        exact h9
      have hget : (v0 ++ [b0]).getD 9 false = b0 := by
        rw [← hv0_len]
        simp [List.getD_eq_getElem?_getD]
      rw [← hget]
      exact h9'
    let x9 : List Bool := (⟨[g1, g2, g3], 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
      (List.ofFn x8 ++ [x8 0 || x8 2])
    have hx9_len : x9.length = 13 := by
      simp only [x9, PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [PEqualNP.Outside.L_meta_4490.foldl_length]
      simp
    have hg4_eval : g4.op.eval (g4.inputs.map fun i => x9.getD i false) =
        !x9.getD (min (g4.inputs.headD 13) 13) false := by
      rw [hg4_not]
      exact PEqualNP.Outside.L_meta_4490.not_eval_eq_getD x9 hx9_len g4.inputs
    have hwires :
        (⟨rest, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
          (x9 ++ [!x9.getD (min (g4.inputs.headD 13) 13) false]) =
        (⟨g0 :: g1 :: g2 :: g3 :: g4 :: rest, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
          (List.ofFn x8) := by
      have hsplit : g0 :: g1 :: g2 :: g3 :: g4 :: rest = ([g0] ++ [g1, g2, g3]) ++ ([g4] ++ rest) := rfl
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_append]
      have hstep0 :
          [g0].foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x8) =
            List.ofFn x8 ++ [x8 0 || x8 2] := by
        change v0 ++ [b0] = List.ofFn x8 ++ [x8 0 || x8 2]
        rw [hb0]
      rw [hstep0]
      have hstep4 :
          [g4].foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x9 =
            x9 ++ [!x9.getD (min (g4.inputs.headD 13) 13) false] := by
        simp only [List.foldl_cons, List.foldl_nil, hg4_eval]
      change rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (x9 ++ [!x9.getD (min (g4.inputs.headD 13) 13) false]) =
        rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          ([g4].foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x9)
      rw [hstep4]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
    exact congrArg (fun w => w.getD out false) hwires
