import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4923

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def xv (n : ℕ) (v : Fin n) : List Bool := List.ofFn fun (x7 : Fin n) => decide (x7 = v)

def S (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (C.wires (xv n v)).getD w false = true)

lemma mem_S {n : ℕ} {C : Circuit} {w : ℕ} {v : Fin n} :
    v ∈ S n C w ↔ (C.wires (xv n v)).getD w false = true := by simp [S]

lemma xv_length (n : ℕ) (v : Fin n) : (xv n v).length = n := by simp [xv]

lemma S_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) : (S n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_S, wires_eq_foldl, foldl_getD_lt _ _ _ (by rw [xv_length]; exact hw)] at ha hb
  simp [xv, List.getD_eq_getElem?_getD, hw] at ha hb
  rw [← ha, ← hb]

lemma S_big (n : ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) : S n C w = ∅ := by
  ext v
  rw [mem_S, wires_eq_foldl, getD_ge _ _ (by rw [foldl_length, xv_length]; exact hw)]
  simp

lemma gate_val (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (v : Fin n) :
    (C.wires (xv n v)).getD (n + j) false = (C.gates[j]).op.eval ((C.gates[j]).inputs.map
      fun i => if i < n + j then (C.wires (xv n v)).getD i false else false) := by
  have := foldl_getD_gate C.gates (xv n v) j hj
  rw [xv_length] at this
  exact this

lemma decomp (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) (j : ℕ) (hj : j < C.gates.length) :
    ∃ P Q : Finset (Fin n), S n C (n + j) = P ∪ Q ∧
      (P = ∅ ∨ ∃ i < n + j, P = S n C i) ∧ (Q = ∅ ∨ ∃ i < n + j, Q = S n C i) := by
  obtain ⟨hop, hlen⟩ := hC (C.gates[j]) (List.getElem_mem hj)
  have hT : ∀ i, (if i < n + j then S n C i else ∅) = ∅ ∨
      ∃ i' < n + j, (if i < n + j then S n C i else ∅) = S n C i' := by
    intro i
    split_ifs with h
    · exact Or.inr ⟨i, h, rfl⟩
    · exact Or.inl rfl
  have memT : ∀ i v, v ∈ (if i < n + j then S n C i else ∅) ↔
      (if i < n + j then (C.wires (xv n v)).getD i false else false) = true := by
    intro i v
    split_ifs <;> simp [mem_S]
  rcases hin : (C.gates[j]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · refine ⟨∅, ∅, ?_, Or.inl rfl, Or.inl rfl⟩
    ext v
    rw [mem_S, gate_val n C j hj, hop, hin]
    simp [GateOp.eval]
  · refine ⟨_, _, ?_, hT a, hT a⟩
    ext v
    rw [Finset.mem_union, memT, mem_S, gate_val n C j hj, hop, hin]
    simp [GateOp.eval]
  · refine ⟨_, _, ?_, hT a, hT b⟩
    ext v
    rw [Finset.mem_union, memT, memT, mem_S, gate_val n C j hj, hop, hin]
    simp [GateOp.eval]
  · rw [hin] at hlen
    simp at hlen

lemma good (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (R : Finset (Fin n))
    (hR : R = ∅ ∨ ∃ i < n + k, R = S n C i) :
    R.card ≤ 1 ∨ R ∈ List.take k ((List.range C.size).map fun j => S n C (n + j)) := by
  have hs : C.size = C.gates.length := rfl
  rcases hR with rfl | ⟨i, hi, rfl⟩
  · left; simp
  · rcases lt_or_ge i n with h | h
    · exact Or.inl (S_input n C i h)
    · right
      rw [← List.map_take, List.take_range]
      exact List.mem_map.2 ⟨i - n, List.mem_range.2 (by omega), by congr 1; omega⟩

end PEqualNP.Outside.L_meta_4923

open PEqualNP.Outside.L_meta_4923 in
theorem PEqualNP.Outside.L_meta_4923 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x3 ∈ x2.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs.length ≤ (2 : ℕ)) →     ∃ (x4 : List (Finset (Fin x1))),       x4.length ≤ x2.size ∧         (∀ (x5 : ℕ),             have x6 : Finset (Fin x1) := {x6 : Fin x1 | (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 = x6))).getD x5 Bool.false = Bool.true};             x6.card ≤ (1 : ℕ) ∨ x6 ∈ x4) ∧           ∀ (x5 : ℕ) (x6 : Finset (Fin x1)), x4[x5]? = Option.some x6 → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x1)), x6 = x8 ∪ x9 ∧ (x8.card ≤ (1 : ℕ) ∨ x8 ∈ List.take x5 x4) ∧ (x9.card ≤ (1 : ℕ) ∨ x9 ∈ List.take x5 x4) := by
  intro n C hC
  have hs : C.size = C.gates.length := rfl
  refine ⟨(List.range C.size).map (fun j => S n C (n + j)), by simp, ?_, ?_⟩
  · intro w
    dsimp only
    show (S n C w).card ≤ 1 ∨ S n C w ∈ _
    rcases lt_or_ge w n with h | h
    · exact Or.inl (S_input n C w h)
    · rcases lt_or_ge w (n + C.size) with h2 | h2
      · right
        exact List.mem_map.2 ⟨w - n, List.mem_range.2 (by omega), by congr 1; omega⟩
      · left
        rw [S_big n C w (by omega)]
        simp
  · intro k s hk
    rcases lt_or_ge k C.size with h | h
    · simp [h] at hk
      subst hk
      obtain ⟨P, Q, e, hP, hQ⟩ := decomp n C hC k (by omega)
      exact ⟨P, Q, e, good n C k (by omega) P hP, good n C k (by omega) Q hQ⟩
    · simp [h] at hk
