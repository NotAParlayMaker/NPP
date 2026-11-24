import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2738

/-- Insert the two constant inputs false, true at position 10. -/
def ins (w : List Bool) : List Bool := w.take 10 ++ [false, true] ++ w.drop 10

/-- The input index of an old gate at position k in the new circuit. -/
def mapIn (k i : ℕ) : ℕ :=
  if i < 10 then i else if i < 10 + k then i + 2 else 10

/-- The output index in the new circuit of an old wire index. -/
def shift (i : ℕ) : ℕ := if i < 10 then i else i + 2

/-- An allowed gate of the old circuit. -/
def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

/-- Normalize a gate from its operation and its already shifted input indices. -/
def normInputs (op : GateOp) (l : List ℕ) : Gate :=
  match op, l with
  | GateOp.not, [] => ⟨GateOp.or, [10, 11]⟩
  | GateOp.not, a :: _ => ⟨GateOp.not, [a]⟩
  | GateOp.and, [] => ⟨GateOp.or, [10, 11]⟩
  | GateOp.and, [a] => if a = 11 then ⟨GateOp.or, [10, 11]⟩ else ⟨GateOp.and, [a, 11]⟩
  | GateOp.and, a :: b :: _ =>
      if a = b then (if a = 11 then ⟨GateOp.or, [10, 11]⟩ else ⟨GateOp.and, [a, 11]⟩)
      else ⟨GateOp.and, [a, b]⟩
  | GateOp.or, [] => ⟨GateOp.and, [10, 11]⟩
  | GateOp.or, [a] => if a = 10 then ⟨GateOp.and, [10, 11]⟩ else ⟨GateOp.or, [a, 10]⟩
  | GateOp.or, a :: b :: _ =>
      if a = b then (if a = 10 then ⟨GateOp.and, [10, 11]⟩ else ⟨GateOp.or, [a, 10]⟩)
      else ⟨GateOp.or, [a, b]⟩
  | _, _ => ⟨GateOp.and, [10, 11]⟩

/-- Normalize one gate: shift earlier wires by two, send missing wires to the false input,
pad AND with true, OR with false, drop extra NOT inputs, and use constants for empty and
duplicate cases. -/
def normGate (k : ℕ) (g : Gate) : Gate := normInputs g.op (g.inputs.map (mapIn k))

/-- Normalize a whole gate list, with the position counter. -/
def normGates : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => normGate k g :: normGates (k + 1) gs

/-- One evaluation step of a circuit. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]


lemma ins_getD (k : ℕ) (w : List Bool) (hw : w.length = 10 + k) (i : ℕ) :
    (ins w).getD (mapIn k i) false = w.getD i false := by
  have hw10 : 10 ≤ w.length := by omega
  have htake : (w.take 10).length = 10 := by simp [List.length_take, hw10]
  have h12 : (w.take 10 ++ [false, true]).length = 12 := by simp [htake]
  unfold ins mapIn
  by_cases hi : i < 10
  · rw [if_pos hi]
    rw [List.getD_append _ _ _ _ (by rw [h12]; omega)]
    rw [List.getD_append _ _ _ _ (by rw [htake]; omega)]
    conv_rhs => rw [← List.take_append_drop 10 w]
    rw [List.getD_append _ _ _ _ (by rw [htake]; omega)]
  · rw [if_neg hi]
    by_cases hik : i < 10 + k
    · rw [if_pos hik]
      rw [List.getD_append_right _ _ _ _ (by rw [h12]; omega)]
      conv_rhs => rw [← List.take_append_drop 10 w]
      rw [List.getD_append_right _ _ _ _ (by rw [htake]; omega)]
      congr 1
      omega
    · rw [if_neg hik]
      rw [List.getD_append _ _ _ _ (by rw [h12]; omega)]
      rw [List.getD_append_right _ _ _ _ (by rw [htake])]
      rw [htake]
      have hwi : w.length ≤ i := by rw [hw]; omega
      rw [List.getD_eq_default _ _ hwi]
      rfl


lemma ins_getD_ten (k : ℕ) (w : List Bool) (hw : w.length = 10 + k) :
    (ins w).getD 10 false = false := by
  have hw10 : 10 ≤ w.length := by omega
  have htake : (w.take 10).length = 10 := by simp [List.length_take, hw10]
  have h12 : (w.take 10 ++ [false, true]).length = 12 := by simp [htake]
  unfold ins
  rw [List.getD_append _ _ _ _ (by rw [h12]; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp [htake])]
  simp [htake]

lemma ins_getD_eleven (k : ℕ) (w : List Bool) (hw : w.length = 10 + k) :
    (ins w).getD 11 false = true := by
  have hw10 : 10 ≤ w.length := by omega
  have htake : (w.take 10).length = 10 := by simp [List.length_take, hw10]
  have h12 : (w.take 10 ++ [false, true]).length = 12 := by simp [htake]
  unfold ins
  rw [List.getD_append _ _ _ _ (by rw [h12]; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp [htake])]
  simp [htake]

lemma normInputs_eval (op : GateOp) (l : List ℕ) (k : ℕ) (w : List Bool)
    (hw : w.length = 10 + k) (hlen : l.length ≤ 2)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) :
    (normInputs op l).op.eval ((normInputs op l).inputs.map fun i => (ins w).getD i false)
      = op.eval (l.map fun i => (ins w).getD i false) := by
  have h10 := ins_getD_ten k w hw
  have h11 := ins_getD_eleven k w hw
  rcases hop with rfl | rfl | rfl
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp only [normInputs, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        List.all_cons, List.all_nil, h10, h11, id_eq, Bool.or_false, Bool.or_true, Bool.and_true]
    · simp only [normInputs]
      split <;> (try split) <;> simp_all only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, h10, h11, id_eq, Bool.or_false, Bool.or_true, Bool.and_true, Bool.and_false, Bool.and_self, Bool.or_self]
    · simp only [normInputs]
      split <;> (try split) <;> simp_all only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, h10, h11, id_eq, Bool.or_false, Bool.or_true, Bool.and_true, Bool.and_false, Bool.and_self, Bool.or_self]
    · exfalso; simp at hlen
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp only [normInputs, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        List.all_cons, List.all_nil, h10, h11, id_eq, Bool.and_false, Bool.and_true, Bool.or_false]
    · simp only [normInputs]
      split <;> (try split) <;> simp_all only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, h10, h11, id_eq, Bool.or_false, Bool.or_true, Bool.and_true, Bool.and_false, Bool.and_self, Bool.or_self]
    · simp only [normInputs]
      split <;> (try split) <;> simp_all only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, h10, h11, id_eq, Bool.or_false, Bool.or_true, Bool.and_true, Bool.and_false, Bool.and_self, Bool.or_self]
    · exfalso; simp at hlen
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp only [normInputs, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        List.all_cons, List.all_nil, List.headD_nil, List.headD_cons, h10, h11, id_eq,
        Bool.or_false, Bool.or_true, Bool.not_false]
    · simp only [normInputs, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_false]
    · simp only [normInputs, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_false]
    · exfalso; simp at hlen


lemma ins_snoc (w : List Bool) (hw : 10 ≤ w.length) (v : Bool) :
    ins (w ++ [v]) = ins w ++ [v] := by
  unfold ins
  rw [List.take_append_of_le_length hw]
  rw [List.drop_append_of_le_length hw]
  simp [List.append_assoc]

lemma ins_of_length (w : List Bool) (h : w.length = 10) :
    ins w = w ++ [false, true] := by
  unfold ins
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega)]
  simp

lemma normGate_eval (k : ℕ) (g : Gate) (w : List Bool) (hw : w.length = 10 + k)
    (hok : Ok g) :
    (normGate k g).op.eval ((normGate k g).inputs.map fun i => (ins w).getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hok
  have hmap : (inputs.map (mapIn k)).map (fun i => (ins w).getD i false)
      = inputs.map (fun i => w.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => ins_getD k w hw i)
  have hlen' : (inputs.map (mapIn k)).length ≤ 2 := by simpa using hlen
  change (normInputs op (inputs.map (mapIn k))).op.eval
      ((normInputs op (inputs.map (mapIn k))).inputs.map fun i => (ins w).getD i false)
      = op.eval (inputs.map fun i => w.getD i false)
  rw [normInputs_eval op (inputs.map (mapIn k)) k w hw hlen' hop, hmap]

lemma normGates_wires (gs : List Gate) (k : ℕ) (w : List Bool)
    (hw : w.length = 10 + k) (hok : ∀ g ∈ gs, Ok g) :
    (normGates k gs).foldl step (ins w) = ins (gs.foldl step w) := by
  induction gs generalizing k w with
  | nil => rfl
  | cons g gs ih =>
    have hg : Ok g := hok g (by simp)
    have hgs : ∀ g' ∈ gs, Ok g' := fun g' hg' => hok g' (by simp [hg'])
    simp only [normGates, List.foldl_cons, step]
    have hins : ins (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        = ins w ++ [(normGate k g).op.eval
            ((normGate k g).inputs.map fun i => (ins w).getD i false)] := by
      rw [ins_snoc w (by omega) _, normGate_eval k g w hw hg]
    rw [← hins]
    exact ih (k + 1) (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp [hw]; omega) hgs


lemma mapIn_lt (k i : ℕ) : mapIn k i < 12 + k := by
  unfold mapIn
  by_cases h1 : i < 10
  · simp [h1]; omega
  · by_cases h2 : i < 10 + k
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega

lemma ten_lt (k : ℕ) : 10 < 12 + k := by omega
lemma eleven_lt (k : ℕ) : 11 < 12 + k := by omega

lemma normInputs_spec (op : GateOp) (l : List ℕ) (k : ℕ)
    (hok : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : l.length ≤ 2) (hbound : ∀ i ∈ l, i < 12 + k) :
    (∀ i ∈ (normInputs op l).inputs, i < 12 + k) ∧
    (normInputs op l).inputs.Nodup ∧
    ((normInputs op l).op = GateOp.not ∧ (normInputs op l).inputs.length = 1 ∨
      (normInputs op l).op ≠ GateOp.not ∧ (normInputs op l).inputs.length = 2) ∧
    ((normInputs op l).op = GateOp.and ∨ (normInputs op l).op = GateOp.or ∨
      (normInputs op l).op = GateOp.not) ∧ (normInputs op l).inputs.length ≤ 2 := by
  have h10 := ten_lt k
  have h11 := eleven_lt k
  rcases hok with rfl | rfl | rfl
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [normInputs, h10, h11]
    · have ha := hbound a (by simp)
      by_cases h : a = 11
      · simp [normInputs, h, h10, h11]
      · simp [normInputs, h, h10, h11, ha]
    · have ha := hbound a (by simp)
      have hb := hbound b (by simp)
      by_cases hab : a = b
      · subst b
        by_cases h : a = 11
        · simp [normInputs, h, h10, h11]
        · simp [normInputs, h, h10, h11, ha]
      · simp [normInputs, hab, h10, h11, ha, hb]
    · exfalso; simp at hlen
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [normInputs, h10, h11]
    · have ha := hbound a (by simp)
      by_cases h : a = 10
      · simp [normInputs, h, h10, h11]
      · simp [normInputs, h, h10, h11, ha]
    · have ha := hbound a (by simp)
      have hb := hbound b (by simp)
      by_cases hab : a = b
      · subst b
        by_cases h : a = 10
        · simp [normInputs, h, h10, h11]
        · simp [normInputs, h, h10, h11, ha]
      · simp [normInputs, hab, h10, h11, ha, hb]
    · exfalso; simp at hlen
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [normInputs, h10, h11]
    · have ha := hbound a (by simp)
      simp [normInputs, ha, h10, h11]
    · have ha := hbound a (by simp)
      simp [normInputs, ha, h10, h11]
    · exfalso; simp at hlen


lemma normGate_spec (k : ℕ) (g : Gate) (hok : Ok g) :
    (∀ i ∈ (normGate k g).inputs, i < 12 + k) ∧
    (normGate k g).inputs.Nodup ∧
    ((normGate k g).op = GateOp.not ∧ (normGate k g).inputs.length = 1 ∨
      (normGate k g).op ≠ GateOp.not ∧ (normGate k g).inputs.length = 2) ∧
    Ok (normGate k g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hok
  have hlen' : (inputs.map (mapIn k)).length ≤ 2 := by simpa using hlen
  have hbound : ∀ i ∈ inputs.map (mapIn k), i < 12 + k := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact mapIn_lt k j
  exact normInputs_spec op (inputs.map (mapIn k)) k hop hlen' hbound

lemma normGates_length (k : ℕ) (gs : List Gate) : (normGates k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [normGates, ih]

lemma normGates_ok (k : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, Ok g) :
    ∀ g ∈ normGates k gs, Ok g := by
  induction gs generalizing k with
  | nil => simp [normGates]
  | cons g gs ih =>
    intro g' hg'
    simp only [normGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact (normGate_spec k g (hok g (by simp))).2.2.2
    · exact ih (k + 1) (fun g'' hg'' => hok g'' (by simp [hg''])) g' hg'

lemma normGates_get_spec (k : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, Ok g) :
    ∀ i : Fin (normGates k gs).length,
      let g := (normGates k gs).get i
      (∀ j ∈ g.inputs, j < 12 + (k + (i : ℕ))) ∧
      g.inputs.Nodup ∧
      ((g.op = GateOp.not ∧ g.inputs.length = 1) ∨
        (g.op ≠ GateOp.not ∧ g.inputs.length = 2)) := by
  induction gs generalizing k with
  | nil =>
    intro i
    exact i.elim0
  | cons g gs ih =>
    intro i
    rcases i with ⟨n, hn⟩
    cases n with
    | zero =>
      simp only [normGates, List.get_cons_zero]
      have hspec := normGate_spec k g (hok g (by simp))
      simpa using ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩
    | succ n =>
      simp only [normGates, List.get_cons_succ]
      have hn' : n < (normGates (k + 1) gs).length := by
        simpa [normGates_length] using hn
      have hspec := ih (k + 1) (fun g' hg' => hok g' (by simp [hg'])) ⟨n, hn'⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hspec


lemma wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, step, ih]; omega

lemma shift_lt {n i : ℕ} (h : i < 10 + n) : shift i < 12 + n := by
  unfold shift
  by_cases hi : i < 10
  · simp [hi]; omega
  · simp [hi]; omega

lemma shift_eq_mapIn {n i : ℕ} (h : i < 10 + n) : shift i = mapIn n i := by
  unfold shift mapIn
  by_cases hi : i < 10
  · simp [hi]
  · simp [hi, h]

lemma eval_eq (x1 : List Gate) (x10 : List Bool) (hx : x10.length = 10)
    (hok : ∀ g ∈ x1, Ok g) (o : ℕ) (ho : o < 10 + x1.length) :
    ({ gates := normGates 0 x1, output := shift o } : Circuit).eval (x10 ++ [false, true])
      = ({ gates := x1, output := o } : Circuit).eval x10 := by
  have hw : (normGates 0 x1).foldl step (x10 ++ [false, true])
      = ins (x1.foldl step x10) := by
    rw [← ins_of_length x10 hx]
    exact normGates_wires x1 0 x10 (by omega) hok
  have hlenw : (x1.foldl step x10).length = 10 + x1.length := by
    rw [wires_length]; omega
  change ((normGates 0 x1).foldl step (x10 ++ [false, true])).getD (shift o) false
      = (x1.foldl step x10).getD o false
  rw [hw]
  rw [show shift o = mapIn x1.length o from shift_eq_mapIn (by omega)]
  exact ins_getD x1.length (x1.foldl step x10) hlenw o

end PEqualNP.Outside.L_meta_2738

open PEqualNP.Outside.L_meta_2738

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_2738 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     x2 < x3 →       x3 < (10 : ℕ) + x1.length →         ∃ (x7 : List PEqualNP.CircuitLowerBounds.Gate) (x8 : ℕ) (x9 : ℕ),           x7.length ≤ x1.length ∧             x8 < (12 : ℕ) + x7.length ∧               x9 < (12 : ℕ) + x7.length ∧                 PEqualNP.MetaComplexity.FanInTwo { gates := x7, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧                   (∀ (x10 : Fin x7.length),                       have x11 : PEqualNP.CircuitLowerBounds.Gate := x7.get x10;                       (∀ x12 ∈ x11.inputs, x12 < (12 : ℕ) + ↑x10) ∧ x11.inputs.Nodup ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (1 : ℕ) ∨ x11.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (2 : ℕ))) ∧                     ∀ (x10 : List Bool), x10.length = (10 : ℕ) → ({ gates := x7, output := x8 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true]) || { gates := x7, output := x9 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true])) = ({ gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10 || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10) := by
  intro x1 x2 x3 hfan h23 h3L
  have hok : ∀ g ∈ x1, Ok g := by
    intro g hg
    have h := hfan g hg
    exact ⟨by simpa using h.1, h.2⟩
  have hlen : (normGates 0 x1).length = x1.length := normGates_length 0 x1
  refine ⟨normGates 0 x1, shift x2, shift x3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen]
  · rw [hlen]
    exact shift_lt (by omega)
  · rw [hlen]
    exact shift_lt (by omega)
  · intro g hg
    have h := normGates_ok 0 x1 hok g hg
    exact ⟨by simpa using h.1, h.2⟩
  · intro i
    have h := normGates_get_spec 0 x1 hok i
    simpa [Nat.zero_add] using h
  · intro x10 hx10
    rw [eval_eq x1 x10 hx10 hok x2 (by omega),
        eval_eq x1 x10 hx10 hok x3 (by omega)]
