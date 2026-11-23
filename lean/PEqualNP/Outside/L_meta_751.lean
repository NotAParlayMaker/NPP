import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_751_aux

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

private theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

private def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

private theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

private theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

private theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
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
    · rw [if_neg hi, List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

private lemma op_mono (op : GateOp) (kind : op = .and ∨ op = .or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ j ∈ l, f j = true → f' j = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases kind with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi (H _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨_, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hi hx⟩

private def reads (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ k e, a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a

end PEqualNP.Outside.L_meta_751_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_751_aux

theorem PEqualNP.Outside.L_meta_751 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ), (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → Relation.ReflTransGen (fun a b : ℕ => ∃ (k : ℕ) (e : PEqualNP.CircuitLowerBounds.Gate), a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a) i (n + j) → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ x x' : Fin n → Bool, (∀ q : Fin n, x q = true → x' q = true) → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x)).getD i false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x')).getD i false = true := by
  intro n C i h x y lexy
  let cone := Relation.ReflTransGen (reads n C) i
  have wires (a : ℕ) : cone a → (C.wires (List.ofFn x)).getD a false = true →
      (C.wires (List.ofFn y)).getD a false = true := by
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      intro ha
      by_cases input : a < n
      · have read (z : Fin n → Bool) : (C.wires (List.ofFn z)).getD a false = z ⟨a,input⟩ := by
          rw [wires_input C _ a (by simpa using input), List.getD_eq_getElem _ _ (by simpa using input)]
          simp
        rw [read, read]
        exact lexy _
      · let k := a - n
        have coord : n+k=a := by dsimp [k]; omega
        by_cases inside : k < C.gates.length
        · let g := C.gates[k]
          have found : C.gates[k]? = some g := List.getElem?_eq_getElem inside
          have gateKind := h k g found (coord ▸ ha)
          have gateVal (z : Fin n → Bool) : (C.wires (List.ofFn z)).getD a false =
              g.op.eval (g.inputs.map (fun j => rd C (List.ofFn z) a j)) := by
            simpa only [List.length_ofFn,coord,g] using wires_gate C (List.ofFn z) k inside
          rw [gateVal, gateVal]
          apply op_mono _ gateKind
          intro j hj
          by_cases earlier : j < a
          · have next : reads n C a j := ⟨k,g,coord.symm,found,hj,earlier⟩
            simpa only [rd,if_pos earlier] using ih j earlier (Relation.ReflTransGen.tail ha next)
          · simp [rd,earlier]
        · have past : (C.wires (List.ofFn x)).length ≤ a := by
            rw [wires_length,List.length_ofFn]
            omega
          rw [List.getD_eq_default _ _ past]
          simp
  exact wires i Relation.ReflTransGen.refl
