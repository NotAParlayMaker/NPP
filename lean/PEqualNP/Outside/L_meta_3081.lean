import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem getD_append_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem gate_eq (g : Gate) (w1 w2 : List Bool) (r : ℕ)
    (h : ∀ i, i ≠ r → w1.getD i false = w2.getD i false)
    (hn : ¬ (g.op = GateOp.not ∧ g.inputs.head? = some r ∨ g.op ≠ GateOp.not ∧ r ∈ g.inputs)) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  by_cases hop : g.op = GateOp.not
  · rw [hop]
    have hh : g.inputs.head? ≠ some r := fun e => hn (Or.inl ⟨hop, e⟩)
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      rw [hi] at hh
      have ha : a ≠ r := fun e => hh (by simp [e])
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      rw [h a ha]
  · have hr : r ∉ g.inputs := fun e => hn (Or.inr ⟨hop, e⟩)
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (fun e => hr (e ▸ hi))

theorem agree (r : ℕ) : ∀ (gs : List Gate) (w1 w2 : List Bool), w1.length = w2.length →
    (∀ i, i ≠ r → w1.getD i false = w2.getD i false) →
    (∀ g ∈ gs, ¬ (g.op = GateOp.not ∧ g.inputs.head? = some r ∨ g.op ≠ GateOp.not ∧ r ∈ g.inputs)) →
    ∀ i, i ≠ r → (gs.foldl step w1).getD i false = (gs.foldl step w2).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w1 w2 _ h _
    exact h
  | cons g gs ih =>
    intro w1 w2 hl h hg
    simp only [List.foldl_cons]
    apply ih
    · simp [step, hl]
    · intro i hi
      have hge := gate_eq g w1 w2 r h (hg g List.mem_cons_self)
      unfold step
      by_cases h1 : i < w1.length
      · rw [getD_append_lt _ _ _ h1, getD_append_lt _ _ _ (hl ▸ h1)]
        exact h i hi
      · by_cases h2 : i = w1.length
        · subst h2
          rw [getD_append_len, hl, getD_append_len]
          exact hge
        · rw [getD_of_length_le _ _ (by simp; omega), getD_of_length_le _ _ (by simp; omega)]
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')

theorem core (C : Circuit) (r : ℕ) (a b : Fin 9 → Bool)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (hab : ∀ i, i ≠ r → (List.ofFn a).getD i false = (List.ofFn b).getD i false)
    (h9a : (a 0 || a 2) = (b 0 || b 2))
    (hg : ∀ g ∈ C.gates.drop 1, ¬ (g.op = GateOp.not ∧ g.inputs.head? = some r ∨ g.op ≠ GateOp.not ∧ r ∈ g.inputs)) :
    ∀ i, i ≠ r → (C.wires (List.ofFn a)).getD i false = (C.wires (List.ofFn b)).getD i false := by
  cases hC : C.gates with
  | nil =>
    have := h9 (fun _ => true)
    rw [wires_eq, hC] at this
    simp [List.getD_eq_getElem?_getD] at this
  | cons g0 gs =>
    rw [hC] at hg
    simp only [List.drop_succ_cons, List.drop_zero] at hg
    have ha := h9 a
    have hb := h9 b
    rw [wires_eq, hC, List.foldl_cons] at ha hb
    simp only [wires_eq, hC, List.foldl_cons]
    rw [foldl_step_getD _ _ _ (by simp [step])] at ha hb
    apply agree r gs _ _ (by simp [step]) _ hg
    intro i hi
    unfold step
    by_cases h1 : i < 9
    · rw [getD_append_lt _ _ _ (by simpa using h1), getD_append_lt _ _ _ (by simpa using h1)]
      exact hab i hi
    · by_cases h2 : i = 9
      · subst h2
        unfold step at ha hb
        have e1 := getD_append_len (List.ofFn a) (g0.op.eval (g0.inputs.map fun i => (List.ofFn a).getD i false))
        have e2 := getD_append_len (List.ofFn b) (g0.op.eval (g0.inputs.map fun i => (List.ofFn b).getD i false))
        simp only [List.length_ofFn] at e1 e2
        rw [e1, e2]
        rw [e1] at ha
        rw [e2] at hb
        rw [ha, hb, h9a]
      · rw [getD_of_length_le _ _ (by simp; omega), getD_of_length_le _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3081

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 := by
  dsimp only
  intro C h9 hf r hr
  by_contra hno
  push_neg at hno
  have hg : ∀ g ∈ C.gates.drop 1, ¬ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some r ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ r ∈ g.inputs) := by
    intro g hgm hor
    rcases hor with h | h
    · exact (hno g hgm).1 h.1 h.2
    · exact (hno g hgm).2 h.1 h.2
  have hev : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD C.output false = PEqualNP.MetaComplexity.circuitFun 9 C x := fun x => rfl
  rcases hr with rfl | rfl
  · have key := PEqualNP.Outside.L_meta_3081.core C 0 ![true, false, true, false, true, false, false, false, false] ![false, false, true, false, true, false, false, false, false] h9 (by
      intro i hi
      by_cases h : i < 9
      · interval_cases i <;> first | rfl | exact absurd rfl hi
      · rw [PEqualNP.Outside.L_meta_3081.getD_of_length_le _ _ (by simp; omega), PEqualNP.Outside.L_meta_3081.getD_of_length_le _ _ (by simp; omega)]) (by decide) hg
    by_cases ho : C.output = 0
    · have h1 := hev ![true, false, false, false, false, false, false, false, false]
      rw [hf, ho, PEqualNP.Outside.L_meta_3081.wires_eq, PEqualNP.Outside.L_meta_3081.foldl_step_getD _ _ _ (by simp)] at h1
      exact absurd h1 (by decide)
    · have h1 := key C.output ho
      rw [hev, hev, hf] at h1
      exact absurd h1 (by decide)
  · have key := PEqualNP.Outside.L_meta_3081.core C 2 ![true, false, true, true, false, false, false, false, false] ![true, false, false, true, false, false, false, false, false] h9 (by
      intro i hi
      by_cases h : i < 9
      · interval_cases i <;> first | rfl | exact absurd rfl hi
      · rw [PEqualNP.Outside.L_meta_3081.getD_of_length_le _ _ (by simp; omega), PEqualNP.Outside.L_meta_3081.getD_of_length_le _ _ (by simp; omega)]) (by decide) hg
    by_cases ho : C.output = 2
    · have h1 := hev ![false, false, true, false, false, false, false, false, false]
      rw [hf, ho, PEqualNP.Outside.L_meta_3081.wires_eq, PEqualNP.Outside.L_meta_3081.foldl_step_getD _ _ _ (by simp)] at h1
      exact absurd h1 (by decide)
    · have h1 := key C.output ho
      rw [hev, hev, hf] at h1
      exact absurd h1 (by decide)
