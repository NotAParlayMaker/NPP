import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1798

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]
  simp [hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]
    simp
    omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · rw [if_pos hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [if_neg hi, List.getD_eq_default]
      omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

def V {P L : ℕ} (C : Circuit) (w : Fin L) (g : ℕ) (pts : Fin P → Bool) : Bool :=
  wireVal C (restrictInput P L w pts) g

theorem restrict_length (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) :
    (restrictInput P L w pts).length = P + L := by
  simp [restrictInput]

def R {P L : ℕ} (C : Circuit) (w : Fin L) (t i : ℕ) (pts : Fin P → Bool) : Bool :=
  if i < t then V C w i pts else false

theorem V_gate {P L : ℕ} (C : Circuit) (w : Fin L) (j : ℕ) (hj : j < C.gates.length)
    (pts : Fin P → Bool) :
    V C w (P + L + j) pts
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => R C w (P + L + j) i pts) := by
  unfold V wireVal
  have h := wires_gate C (restrictInput P L w pts) j hj
  rw [restrict_length] at h
  rw [h]
  rfl

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

theorem wires_mono (C : Circuit) (hC : IsMonotoneCircuit C) (a b : List Bool)
    (hl : a.length = b.length) (h : LeL a b) : LeL (C.wires a) (C.wires b) :=
  fold_mono C.gates hC a b hl h

theorem restrict_getD_lt (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) (i : ℕ) (h : i < P) :
    (restrictInput P L w pts).getD i false = pts ⟨i, h⟩ := by
  unfold restrictInput
  rw [List.getD_append _ _ _ _ (by simp; exact h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem restrict_getD_ge (P L : ℕ) (w : Fin L) (pts pts' : Fin P → Bool) (i : ℕ) (h : P ≤ i) :
    (restrictInput P L w pts).getD i false = (restrictInput P L w pts').getD i false := by
  unfold restrictInput
  rw [List.getD_append_right _ _ _ _ (by simp; exact h),
    List.getD_append_right _ _ _ _ (by simp; exact h)]
  simp

theorem V_mono {P L : ℕ} (C : Circuit) (hC : IsMonotoneCircuit C) (w : Fin L) (g : ℕ)
    (pts pts' : Fin P → Bool) (h : ∀ p, pts p = true → pts' p = true) :
    V C w g pts = true → V C w g pts' = true := by
  unfold V wireVal
  apply wires_mono C hC _ _ (by rw [restrict_length, restrict_length])
  intro i hi
  by_cases hiP : i < P
  · rw [restrict_getD_lt _ _ _ _ _ hiP] at hi ⊢
    exact h _ hi
  · rw [restrict_getD_ge _ _ _ _ pts _ (by omega)]
    exact hi

theorem not_low_elim {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)
    {g : ℕ} (h : ¬ IsLow P L inc C g w) :
    ∃ pts : Fin P → Bool, V C w g pts = true ∧ ∀ p, inc p w = true → pts p = false := by
  change ¬ (∀ pts, V C w g pts = true → lineSum P L inc w pts = true) at h
  simp only [not_forall] at h
  obtain ⟨pts, h1, h2⟩ := h
  refine ⟨pts, h1, fun p hp => ?_⟩
  by_contra hc
  apply h2
  unfold lineSum
  simp only [decide_eq_true_eq]
  exact ⟨p, hp, by simpa using hc⟩

theorem and_low {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)
    (hC : IsMonotoneCircuit C) (t a b : ℕ) (hlow : IsLow P L inc C t w)
    (hv : ∀ pts : Fin P → Bool, V C w t pts = (V C w a pts && V C w b pts)) :
    IsLow P L inc C a w ∨ IsLow P L inc C b w := by
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨p1, h1, e1⟩ := not_low_elim inc C w hn.1
  obtain ⟨p2, h2, e2⟩ := not_low_elim inc C w hn.2
  let pts : Fin P → Bool := fun p => p1 p || p2 p
  have ha : V C w a pts = true := V_mono C hC w a p1 pts (fun p h => by simp [pts, h]) h1
  have hb : V C w b pts = true := V_mono C hC w b p2 pts (fun p h => by simp [pts, h]) h2
  have ht : V C w t pts = true := by rw [hv, ha, hb]; rfl
  have hs := hlow pts ht
  unfold lineSum at hs
  simp only [decide_eq_true_eq] at hs
  obtain ⟨p, hp, hpt⟩ := hs
  simp [pts, e1 p hp, e2 p hp] at hpt

end PEqualNP.Outside.L_meta_1798

theorem PEqualNP.Outside.L_meta_1798 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ (j a b : ℕ), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → a < P + L + j → b < P + L + j → ∀ w : Fin L, PEqualNP.LowMerge.IsLow P L inc C (P + L + j) w → PEqualNP.LowMerge.IsLow P L inc C a w ∨ PEqualNP.LowMerge.IsLow P L inc C b w := by
  intro P L inc C hC j a b hgate ha hb w hlow
  have hj : j < C.gates.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hgate
    contradiction
  have hgate' : C.gates[j] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ := by
    rw [List.getElem?_eq_getElem hj] at hgate
    exact Option.some.inj hgate
  have hv : ∀ pts : Fin P → Bool,
      PEqualNP.Outside.L_meta_1798.V C w (P + L + j) pts =
        (PEqualNP.Outside.L_meta_1798.V C w a pts &&
          PEqualNP.Outside.L_meta_1798.V C w b pts) := by
    intro pts
    rw [PEqualNP.Outside.L_meta_1798.V_gate C w j hj, hgate']
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval,
      PEqualNP.Outside.L_meta_1798.R, ha, hb]
  exact PEqualNP.Outside.L_meta_1798.and_low inc C w hC _ a b hlow hv
