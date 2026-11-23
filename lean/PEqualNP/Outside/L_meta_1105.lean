import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1105_aux
open PEqualNP.CircuitLowerBounds

theorem wires_snoc (gs : List Gate) (g : Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ x = Circuit.wires ⟨gs, o'⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o'⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_nil (o : ℕ) (x : List Bool) : Circuit.wires ⟨[], o⟩ x = x := by
  simp [Circuit.wires]

theorem wires_len (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires_nil]
  | append_singleton gs g ih => rw [wires_snoc gs g o o]; simp [ih]; omega

def sh (n i : ℕ) : ℕ := if i < n then i else i + 1

def ins (n : ℕ) (b : Bool) (W : List Bool) : List Bool := W.take n ++ b :: W.drop n

theorem ins_getD (n : ℕ) (b : Bool) (W : List Bool) (hn : n ≤ W.length) (i : ℕ) :
    (ins n b W).getD (sh n i) false = W.getD i false := by
  simp only [ins, sh, List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_take]
    have e : i + 1 - min n W.length = (i - n) + 1 := by omega
    rw [e, List.getElem?_cons_succ, List.getElem?_drop]
    congr 2
    omega

theorem ins_getD_n (n : ℕ) (b : Bool) (W : List Bool) (hn : n ≤ W.length) :
    (ins n b W).getD n false = b := by
  simp only [ins, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  have e : n - (List.take n W).length = 0 := by simp; omega
  rw [e]
  simp

theorem ins_snoc (n : ℕ) (b : Bool) (W : List Bool) (v : Bool) (hn : n ≤ W.length) :
    ins n b W ++ [v] = ins n b (W ++ [v]) := by
  simp [ins, List.take_append_of_le_length hn, List.drop_append_of_le_length hn]

def T (n : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.and, [n]⟩
  | _ => ⟨g.op, g.inputs.map (sh n)⟩

theorem T_not (n : ℕ) (g : Gate) (hg : g.op = GateOp.not) : T n g = ⟨GateOp.and, [n]⟩ := by
  unfold T; rw [hg]

theorem T_ne (n : ℕ) (g : Gate) (hg : g.op ≠ GateOp.not) : T n g = ⟨g.op, g.inputs.map (sh n)⟩ := by
  unfold T; split <;> simp_all

theorem main (n : ℕ) (b : Bool) (x : List Bool) (hx : x.length = n) (o o' : ℕ) (gs : List Gate)
    (h : ∀ k (hk : k < gs.length), gs[k].op = GateOp.not →
      gs[k].op.eval (gs[k].inputs.map fun i => (Circuit.wires ⟨gs.take k, o⟩ x).getD i false) = b) :
    Circuit.wires ⟨gs.map (T n), o'⟩ (x ++ [b]) = ins n b (Circuit.wires ⟨gs, o⟩ x) := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires_nil, ins, ← hx]
  | append_singleton gs g ih =>
    have ih' := ih (fun k hk hn => by
      have := h k (by simp; omega)
      simp only [List.getElem_append_left hk] at this
      rw [List.take_append_of_le_length (by omega)] at this
      exact this hn)
    have hl : n ≤ (Circuit.wires ⟨gs, o⟩ x).length := by rw [wires_len]; omega
    rw [List.map_append, List.map_singleton, wires_snoc _ _ o' o', ih', wires_snoc gs g o o,
      ← ins_snoc n b _ _ hl]
    congr 2
    by_cases hg : g.op = GateOp.not
    · have := h gs.length (by simp) (by simp [hg])
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero,
        List.take_left' rfl] at this
      rw [T_not n g hg, this]
      have e := ins_getD_n n b _ hl
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
      exact e
    · rw [T_ne n g hg]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ins_getD n b _ hl i

theorem headD_map (l : List ℕ) (F : ℕ → Bool) (d : ℕ) (hd : F d = false) :
    (l.map F).headD false = F (l.headD d) := by
  cases l <;> simp [hd]

end PEqualNP.Outside.L_meta_1105_aux

open PEqualNP.Outside.L_meta_1105_aux in
theorem PEqualNP.Outside.L_meta_1105 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), (∀ i (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[i]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (i = j ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not))) → ∃ (D H : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D ∧ PEqualNP.CircuitLowerBounds.IsMonotoneCircuit H ∧ D.size ≤ C.size ∧ H.size ≤ C.size ∧ ∀ x : List Bool, x.length = n → C.eval x = D.eval (x ++ [!(H.eval x)]) := by
  intro n C j hC
  obtain ⟨gs, out⟩ := C
  simp only at hC
  refine ⟨⟨gs.map (T n), sh n out⟩,
    ⟨gs.take j, (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs.headD (n + j)⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg'
    rcases hC i gs[i] (List.getElem?_eq_getElem hi) with h | h | ⟨_, h⟩
    · left; rw [T_ne n _ (by rw [h]; simp)]; exact h
    · right; rw [T_ne n _ (by rw [h]; simp)]; exact h
    · left; rw [T_not n _ h]
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    rcases hC i gs[i] (List.getElem?_eq_getElem (by omega)) with h | h | ⟨h1, _⟩
    · left; exact h
    · right; exact h
    · omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x hx
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
    rw [main n _ x hx ((gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs.headD (n + j)) _ gs]
    · have hl : n ≤ (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs.headD (n + j)⟩ x).length := by
        rw [wires_len]; omega
      rw [ins_getD n _ _ hl]
      rfl
    · intro k hk hn
      rcases hC k gs[k] (List.getElem?_eq_getElem hk) with h | h | ⟨rfl, _⟩
      · rw [h] at hn; cases hn
      · rw [h] at hn; cases hn
      · have e : gs.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ = gs[k] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        rw [e, hn]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
        congr 1
        apply headD_map
        apply List.getD_eq_default
        rw [wires_len]; simp; omega
