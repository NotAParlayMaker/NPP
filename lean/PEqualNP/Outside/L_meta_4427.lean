import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4427

open PEqualNP.CircuitLowerBounds

/-- `g` reads wire `v`: NOT reads only its first input, every other gate reads all of them. -/
def Reads (g : Gate) (v : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs

/-- Two wire lists agree except possibly at index `v`. -/
def Agree (v : ℕ) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, i ≠ v → w.getD i false = w'.getD i false

lemma gate_congr (g : Gate) (v : ℕ) (hg : ¬ Reads g v) (w w' : List Bool)
    (h : ∀ i, i ≠ v → w.getD i false = w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  by_cases hn : g.op = GateOp.not
  · have hh : g.inputs.head? ≠ some v := fun e => hg (Or.inl ⟨hn, e⟩)
    rw [hn]
    cases hi : g.inputs with
    | nil => rfl
    | cons a l =>
      rw [hi] at hh
      have ha : a ≠ v := fun e => hh (by simp [e])
      simp only [GateOp.eval, List.map_cons, List.headD_cons, h a ha]
  · have hm : v ∉ g.inputs := fun e => hg (Or.inr ⟨hn, e⟩)
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (fun e => hm (e ▸ hi))

lemma agree_snoc {v : ℕ} {w w' : List Bool} (h : Agree v w w') (a : Bool) :
    Agree v (w ++ [a]) (w' ++ [a]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  rcases lt_or_ge i w.length with hl | hl
  · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ (h.1 ▸ hl)]
    exact h.2 i hi
  · rw [List.getD_append_right _ _ _ _ hl, List.getD_append_right _ _ _ _ (h.1 ▸ hl), h.1]

abbrev step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_agree (v : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, ¬ Reads g v) →
    ∀ w w', Agree v w w' → Agree v (gs.foldl step w) (gs.foldl step w') := by
  intro gs
  induction gs with
  | nil => intro _ w w' h; simpa using h
  | cons g gs ih =>
    intro hg w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    have e := gate_congr g v (hg g (List.mem_cons_self ..)) w w' h.2
    simp only [step]
    rw [e]
    exact agree_snoc h _

lemma fold_prefix : ∀ (gs : List Gate) (w : List Bool), ∃ t, gs.foldl step w = w ++ t := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t,
      by simp only [List.foldl_cons, ht, step, List.append_assoc]⟩

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

/-- the base wires: inputs then `x0 || x2` -/
def base (y : Fin 9 → Bool) : List Bool := List.ofFn y ++ [y 0 || y 2]

/-- all eleven input wires, with the NOT wire written through the head of its list -/
def W (h : Option (Fin 11)) (y : Fin 9 → Bool) : List Bool :=
  base y ++ [!((h.map fun j => (base y).getD (↑j) false).getD false)]

lemma headD_map {α β : Type} (l : List α) (f : α → β) (d : β) :
    (l.map f).headD d = (l.head?.map f).getD d := by
  cases l <;> rfl

def edge (x4 : Fin 9 → Bool) : Bool :=
  x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 || x4 3 && x4 4 || x4 4 && x4 0 ||
    x4 0 && x4 5 || x4 1 && x4 6 || x4 2 && x4 7 || x4 3 && x4 8 || x4 5 && x4 7 ||
    x4 6 && x4 8 || x4 8 && x4 5

/-- decidable version of agreement on the eleven input wires -/
def agreeB (v : ℕ) (w w' : List Bool) : Bool :=
  w.length == w'.length && (List.range w.length).all fun i => i == v || w.getD i false == w'.getD i false

lemma agree_of_agreeB {v : ℕ} {w w' : List Bool} (hb : agreeB v w w' = true) : Agree v w w' := by
  simp only [agreeB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hb
  refine ⟨hb.1, fun i hi => ?_⟩
  rcases lt_or_ge i w.length with hl | hl
  · rcases hb.2 i hl with e | e
    · exact absurd (by simpa using e) hi
    · simpa using e
  · rw [List.getD_eq_default _ _ hl, List.getD_eq_default _ _ (hb.1 ▸ hl)]

def sgl (s : List (Fin 9)) : Fin 9 → Bool := fun i => decide (i ∈ s)

/-- for each `v`: two inputs differing only at `v`, with equal `x0 || x2`, and different edge values -/
def pairFor : Fin 9 → (Fin 9 → Bool) × (Fin 9 → Bool)
  | 0 => (sgl [2, 4], sgl [0, 2, 4])
  | 1 => (sgl [6], sgl [1, 6])
  | 2 => (sgl [0, 3], sgl [0, 2, 3])
  | 3 => (sgl [8], sgl [3, 8])
  | 4 => (sgl [3], sgl [3, 4])
  | 5 => (sgl [7], sgl [5, 7])
  | 6 => (sgl [8], sgl [6, 8])
  | 7 => (sgl [5], sgl [5, 7])
  | 8 => (sgl [5], sgl [5, 8])

lemma pair_edge : ∀ v : Fin 9, edge (pairFor v).1 ≠ edge (pairFor v).2 := by decide

lemma pair_agree : ∀ v : Fin 9, ∀ h : Option (Fin 11), h ≠ some (Fin.castAdd 2 v) →
    agreeB (↑v) (W h (pairFor v).1) (W h (pairFor v).2) = true := by decide

lemma single_val : ∀ v : Fin 9, ∀ h : Option (Fin 11),
    (W h (sgl [v])).getD (↑v) false = true ∧ edge (sgl [v]) = false := by decide

lemma W_length (h : Option (Fin 11)) (y : Fin 9 → Bool) : (W h y).length = 11 := by
  simp [W, base]

lemma core (x2 : List (Fin 11)) (C : Circuit)
    (hC : ∀ y : Fin 9 → Bool, C.eval (W x2.head? y) = edge y) (v : Fin 9)
    (hv : x2.head? ≠ some (Fin.castAdd 2 v)) : ∃ g ∈ C.gates, Reads g v := by
  by_contra hno
  push Not at hno
  by_cases ho : C.output = ↑v
  · obtain ⟨t, ht⟩ := fold_prefix C.gates (W x2.head? (sgl [v]))
    have e := hC (sgl [v])
    obtain ⟨h1, h2⟩ := single_val v x2.head?
    rw [Circuit.eval, wires_eq, ht, ho,
      List.getD_append _ _ _ _ (by rw [W_length]; omega), h1, h2] at e
    exact Bool.noConfusion e
  · have ag := fold_agree (↑v) C.gates hno _ _ (agree_of_agreeB (pair_agree v x2.head? hv))
    have e1 := hC (pairFor v).1
    have e2 := hC (pairFor v).2
    rw [Circuit.eval, wires_eq] at e1 e2
    rw [ag.2 _ ho] at e1
    exact pair_edge v (e1.symm.trans e2)

end PEqualNP.Outside.L_meta_4427

theorem PEqualNP.Outside.L_meta_4427 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : List (Fin (11 : ℕ))) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x4 : Fin (9 : ℕ) → Bool),       have x5 : List Bool := List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))];       x3.eval (x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x6 : Fin (11 : ℕ)) => x5.getD (↑x6) Bool.false) x2)]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) →     ∀ (x5 : Fin (9 : ℕ)), x2.head? ≠ Option.some (Fin.castAdd (2 : ℕ) x5) → ∃ x7 ∈ x3.gates, x1 x7 ↑x5 := by
  intro x1 x2 x3 hC x5 hv
  apply PEqualNP.Outside.L_meta_4427.core x2 x3 _ x5 hv
  intro y
  have e := hC y
  rw [show PEqualNP.Outside.L_meta_4427.W x2.head? y =
      PEqualNP.Outside.L_meta_4427.base y ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
        (x2.map fun (j : Fin 11) => (PEqualNP.Outside.L_meta_4427.base y).getD (↑j) false)] from by cases x2 <;> rfl]
  exact e
