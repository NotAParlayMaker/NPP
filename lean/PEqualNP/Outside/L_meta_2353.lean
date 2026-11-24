import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2353

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : a < b ∧ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ a ∈ (gateAt C rj).inputs)
    (hv : val C.gates a z = true) : val C.gates b z = true := by
  obtain ⟨hab, rj, hb, hlt, hop, hin⟩ := h
  subst hb
  rw [gateAt_eq C rj hlt] at hop hin
  exact (val_or C.gates z rj hlt hop).2 ⟨a, hin, hab, hv⟩

theorem reach_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b)
    (hv : val C.gates a z = true) : val C.gates b z = true := by
  induction h with
  | refl => exact hv
  | tail _ hstep ih => exact or_up n C z _ _ hstep ih

theorem two_mem (l : List ℕ) (hl : l.length = 2) (i : ℕ) (hi : i ∈ l) :
    i = l.getD 0 0 ∨ i = l.getD 1 0 := by
  match l, hl with
  | [a, b], _ =>
    simp at hi
    rcases hi with h | h
    · left; simp [h]
    · right; simp [h]

theorem and_up (n : ℕ) (C : Circuit) (hA : PEqualNP.TopForm.IsAO2 n C) (z : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : val C.gates ((gateAt C j).inputs.getD 0 0) z = true)
    (h1 : val C.gates ((gateAt C j).inputs.getD 1 0) z = true) :
    val C.gates (n + j) z = true := by
  obtain ⟨_, hRB, hlen⟩ := hA
  have hb := hRB j hj
  have hg := gateAt_eq C j hj
  have hl : (gateAt C j).inputs.length = 2 := by
    rw [hg]; exact hlen _ (List.getElem_mem hj)
  have hop2 : C.gates[j].op = GateOp.and := by rw [← hg]; exact hop
  apply (val_and C.gates z j hj hop2).2
  intro i hi
  rw [← hg] at hi
  refine ⟨hb i hi, ?_⟩
  rcases two_mem _ hl i hi with h | h
  · rw [h]; exact h0
  · rw [h]; exact h1

theorem main (n : ℕ) (C : Circuit) (hA : PEqualNP.TopForm.IsAO2 n C) (z : Fin n → Bool)
    (top : ℕ) (L : List ℕ)
    (hT : ∀ Q : ℕ → List ℕ → Prop,
      (∀ (qm qt : ℕ), Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧
        rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) qm qt →
        Q qt [qm]) →
      (∀ (qj qt : ℕ) (qL1 qL2 : List ℕ), qj < C.gates.length →
        (gateAt C qj).op = GateOp.and →
        Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧
          rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)
          (n + qj) qt →
        Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
        Q qt (qL1 ++ qL2)) → Q top L)
    (hL : ∀ m ∈ L, val C.gates m z = true) : val C.gates top z = true := by
  refine hT (fun t K => (∀ m ∈ K, val C.gates m z = true) → val C.gates t z = true) ?_ ?_ hL
  · intro qm qt hr hall
    exact reach_up n C z qm qt hr (hall qm (by simp))
  · intro qj qt qL1 qL2 hj hop hr h1 h2 hall
    refine reach_up n C z _ _ hr (and_up n C hA z qj hj hop (h1 ?_) (h2 ?_))
    · intro m hm; exact hall m (by simp [hm])
    · intro m hm; exact hall m (by simp [hm])

end PEqualNP.Outside.L_meta_2353

theorem PEqualNP.Outside.L_meta_2353 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List ℕ → Prop, T = (fun tt tL => ∀ Q : ℕ → List ℕ → Prop, (∀ (qm qt : ℕ), R qm qt → Q qt [qm]) → (∀ (qj qt : ℕ) (qL1 qL2 : List ℕ), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List ℕ) (z : Fin n → Bool), T top L → (∀ m ∈ L, (C.wires (List.ofFn z)).getD (m) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hA R hR T hT top L z hTL hL
  subst hR
  subst hT
  exact PEqualNP.Outside.L_meta_2353.main n C hA z top L hTL hL
