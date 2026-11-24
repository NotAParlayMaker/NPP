import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def readsWire (g : Gate) (k : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = Option.some k ∨ g.op ≠ GateOp.not ∧ k ∈ g.inputs

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_append_left_lt (w u : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ u).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_step_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWires w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (stepWires w g).length := by
      simp [stepWires]; omega
    rw [List.foldl_cons, ih (stepWires w g) hi']
    exact getD_append_left_lt w _ i hi

theorem gate_eval_eq_of_not_reads (g : Gate) (k : ℕ) (hno : ¬ readsWire g k)
    (w1 w2 : List Bool) (heq : ∀ j, j ≠ k → w1.getD j false = w2.getD j false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  by_cases hnot : g.op = GateOp.not
  · rw [hnot]
    cases hin : g.inputs with
    | nil => rfl
    | cons a as =>
      have hne : a ≠ k := by
        intro hak
        apply hno
        left
        exact ⟨hnot, by simp [hin, hak]⟩
      dsimp only [GateOp.eval, List.map, List.headD]
      rw [heq a hne]
  · have hmem : k ∉ g.inputs := by
      intro hk
      exact hno (Or.inr ⟨hnot, hk⟩)
    have hmap : g.inputs.map (fun i => w1.getD i false) =
        g.inputs.map (fun i => w2.getD i false) := by
      apply List.map_congr_left
      intro j hj
      exact heq j (fun hjk => hmem (hjk ▸ hj))
    rw [hmap]

theorem stepWires_agree (g : Gate) (k : ℕ) (hno : ¬ readsWire g k)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (heq : ∀ j, j ≠ k → w1.getD j false = w2.getD j false) :
    (stepWires w1 g).length = (stepWires w2 g).length ∧
      ∀ j, j ≠ k → (stepWires w1 g).getD j false = (stepWires w2 g).getD j false := by
  have hv := gate_eval_eq_of_not_reads g k hno w1 w2 heq
  refine ⟨by simp [stepWires, hlen], ?_⟩
  intro j hj
  dsimp only [stepWires]
  rw [hv]
  by_cases hlt : j < w1.length
  · have hlt2 : j < w2.length := hlen ▸ hlt
    rw [getD_append_left_lt w1 _ j hlt, getD_append_left_lt w2 _ j hlt2]
    exact heq j hj
  · by_cases heql : j = w1.length
    · subst heql
      rw [getD_snoc_eq]
      rw [hlen, getD_snoc_eq]
    · have hgt1 : (w1 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]).length ≤ j := by
        simp; omega
      have hgt2 : (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]).length ≤ j := by
        simp; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hgt1, List.getElem?_eq_none hgt2]

theorem foldl_step_agree (gs : List Gate) (k : ℕ) (hno : ∀ g ∈ gs, ¬ readsWire g k)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (heq : ∀ j, j ≠ k → w1.getD j false = w2.getD j false) :
    ∀ j, j ≠ k → (gs.foldl stepWires w1).getD j false = (gs.foldl stepWires w2).getD j false := by
  induction gs generalizing w1 w2 with
  | nil => exact heq
  | cons g gs ih =>
    obtain ⟨hlen', heq'⟩ := stepWires_agree g k (hno g List.mem_cons_self) w1 w2 hlen heq
    exact ih (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))
      (stepWires w1 g) (stepWires w2 g) hlen' heq'

def g9Fun (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def inpC0 : Fin 9 → Bool := fun i => decide (i = 0)
def inpA0 : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 4)
def inpB0 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 4)

def inpC2 : Fin 9 → Bool := fun i => decide (i = 2)
def inpA2 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 3)
def inpB2 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 3)

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWires x := rfl

theorem step0_eq_of_h9 (g0 : Gate) (gs : List Gate)
    (h9 : ∀ x3 : Fin 9 → Bool, ((Circuit.mk (g0 :: gs) 0).wires (List.ofFn x3)).getD 9 false = (x3 0 || x3 2))
    (x3 : Fin 9 → Bool) :
    stepWires (List.ofFn x3) g0 = List.ofFn x3 ++ [x3 0 || x3 2] := by
  have hlen : (List.ofFn x3).length = 9 := List.length_ofFn
  have hlt : 9 < (stepWires (List.ofFn x3) g0).length := by
    simp [stepWires]
  have hp := foldl_step_prefix gs (stepWires (List.ofFn x3) g0) 9 hlt
  have h9x := h9 x3
  rw [wires_eq_foldl, List.foldl_cons, hp] at h9x
  dsimp only [stepWires] at h9x ⊢
  have hget : (List.ofFn x3 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x3).getD i false)]).getD 9 false =
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x3).getD i false) := by
    simp
  rw [hget] at h9x
  rw [h9x]

theorem agree_init_0 :
    ∀ j, j ≠ 0 →
      (List.ofFn inpA0 ++ [inpA0 0 || inpA0 2]).getD j false =
        (List.ofFn inpB0 ++ [inpB0 0 || inpB0 2]).getD j false := by
  intro j hj
  by_cases hlt : j < 10
  · interval_cases j <;> first | exact absurd rfl hj | decide
  · have h1 : (List.ofFn inpA0 ++ [inpA0 0 || inpA0 2]).length ≤ j := by simp; omega
    have h2 : (List.ofFn inpB0 ++ [inpB0 0 || inpB0 2]).length ≤ j := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none h1, List.getElem?_eq_none h2]

theorem agree_init_2 :
    ∀ j, j ≠ 2 →
      (List.ofFn inpA2 ++ [inpA2 0 || inpA2 2]).getD j false =
        (List.ofFn inpB2 ++ [inpB2 0 || inpB2 2]).getD j false := by
  intro j hj
  by_cases hlt : j < 10
  · interval_cases j <;> first | exact absurd rfl hj | decide
  · have h1 : (List.ofFn inpA2 ++ [inpA2 0 || inpA2 2]).length ≤ j := by simp; omega
    have h2 : (List.ofFn inpB2 ++ [inpB2 0 || inpB2 2]).length ≤ j := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none h1, List.getElem?_eq_none h2]

end PEqualNP.Outside.L_meta_3081

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 := by
  dsimp only
  intro x2 h9 hf x5 hx5
  open PEqualNP.Outside.L_meta_3081 in
  cases hx2 : x2.gates with
  | nil =>
    exfalso
    have h := h9 (fun _ => true)
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires, hx2] at h
  | cons g0 gs =>
    by_contra hnone
    have hno : ∀ g ∈ gs, ¬ readsWire g x5 := by
      intro g hg hr
      exact hnone ⟨g, by simpa [List.drop] using hg, hr⟩
    have h9' : ∀ x3 : Fin 9 → Bool,
        ((PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) 0).wires (List.ofFn x3)).getD 9 false =
          (x3 0 || x3 2) := by
      intro x3
      have := h9 x3
      simpa [PEqualNP.CircuitLowerBounds.Circuit.wires, hx2] using this
    have hstep0 := step0_eq_of_h9 g0 gs h9'
    rcases hx5 with rfl | rfl
    · have hout : x2.output ≠ 0 := by
        intro ho
        have hc := congrFun hf inpC0
        dsimp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval] at hc
        rw [ho, wires_eq_foldl, hx2] at hc
        have hp := foldl_step_prefix (g0 :: gs) (List.ofFn inpC0) 0 (by simp)
        rw [hp] at hc
        have hl : (List.ofFn inpC0).getD 0 false = true := by decide
        have hr : g9Fun inpC0 = false := by decide
        change (List.ofFn inpC0).getD 0 false = g9Fun inpC0 at hc
        rw [hl, hr] at hc
        exact Bool.noConfusion hc
      have hag := foldl_step_agree gs 0 hno
        (List.ofFn inpA0 ++ [inpA0 0 || inpA0 2])
        (List.ofFn inpB0 ++ [inpB0 0 || inpB0 2])
        (by simp) agree_init_0 x2.output hout
      have ha := congrFun hf inpA0
      have hb := congrFun hf inpB0
      dsimp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval] at ha hb
      rw [wires_eq_foldl, hx2, List.foldl_cons, hstep0 inpA0] at ha
      rw [wires_eq_foldl, hx2, List.foldl_cons, hstep0 inpB0] at hb
      rw [hag] at ha
      change _ = g9Fun inpA0 at ha
      change _ = g9Fun inpB0 at hb
      have hva : g9Fun inpA0 = false := by decide
      have hvb : g9Fun inpB0 = true := by decide
      rw [ha, hva, hvb] at hb
      exact Bool.noConfusion hb
    · have hout : x2.output ≠ 2 := by
        intro ho
        have hc := congrFun hf inpC2
        dsimp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval] at hc
        rw [ho, wires_eq_foldl, hx2] at hc
        have hp := foldl_step_prefix (g0 :: gs) (List.ofFn inpC2) 2 (by simp)
        rw [hp] at hc
        have hl : (List.ofFn inpC2).getD 2 false = true := by decide
        have hr : g9Fun inpC2 = false := by decide
        change (List.ofFn inpC2).getD 2 false = g9Fun inpC2 at hc
        rw [hl, hr] at hc
        exact Bool.noConfusion hc
      have hag := foldl_step_agree gs 2 hno
        (List.ofFn inpA2 ++ [inpA2 0 || inpA2 2])
        (List.ofFn inpB2 ++ [inpB2 0 || inpB2 2])
        (by simp) agree_init_2 x2.output hout
      have ha := congrFun hf inpA2
      have hb := congrFun hf inpB2
      dsimp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval] at ha hb
      rw [wires_eq_foldl, hx2, List.foldl_cons, hstep0 inpA2] at ha
      rw [wires_eq_foldl, hx2, List.foldl_cons, hstep0 inpB2] at hb
      rw [hag] at ha
      change _ = g9Fun inpA2 at ha
      change _ = g9Fun inpB2 at hb
      have hva : g9Fun inpA2 = false := by decide
      have hvb : g9Fun inpB2 = true := by decide
      rw [ha, hva, hvb] at hb
      exact Bool.noConfusion hb
