import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1105

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp
    omega

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

def shift (n i : ℕ) : ℕ := if i < n then i else i + 1

theorem read_shift (v : List Bool) (n : ℕ) (b : Bool) (i : ℕ) :
    (v.insertIdx n b).getD (shift n i) false = v.getD i false := by
  simp only [List.getD_eq_getElem?_getD, shift]
  split_ifs with h
  · rw [List.getElem?_insertIdx_of_lt h]
  · rw [List.getElem?_insertIdx_of_gt (by omega)]
    simp

theorem read_middle (v : List Bool) (n : ℕ) (b : Bool) (hn : n ≤ v.length) :
    (v.insertIdx n b).getD n false = b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_insertIdx_self, hn]

theorem insert_snoc (v : List Bool) (n : ℕ) (b a : Bool) (hn : n ≤ v.length) :
    (v ++ [a]).insertIdx n b = v.insertIdx n b ++ [a] := by
  induction v generalizing n with
  | nil =>
    have : n = 0 := by simpa using hn
    subst n
    rfl
  | cons c v ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.cons_append, List.insertIdx_succ_cons]
      rw [ih n (by simpa using hn)]

def translate (n : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.or, [n]⟩
  | op => ⟨op, g.inputs.map (shift n)⟩

def NotValue (gs : List Gate) (x : List Bool) (b : Bool) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (post : List Gate), gs = pre ++ g :: post →
    g.op = GateOp.not → g.op.eval (g.inputs.map fun i => (run pre x).getD i false) = b

theorem simulate (n : ℕ) (gs : List Gate) (x : List Bool) (b : Bool)
    (hx : x.length = n) (hnot : NotValue gs x b) :
    run (gs.map (translate n)) (x ++ [b]) = (run gs x).insertIdx n b := by
  induction gs using List.reverseRecOn with
  | nil =>
    simpa [run, hx] using (List.insertIdx_length_self (l := x) (x := b)).symm
  | append_singleton gs g ih =>
    have hpre : NotValue gs x b := by
      intro pre a post he ha
      apply hnot pre a (post ++ [g]) ?_ ha
      rw [he]
      simp [List.append_assoc]
    have hs := ih hpre
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc, hs]
    have hn : n ≤ (run gs x).length := by rw [run_length, hx]; omega
    have heval : (translate n g).op.eval
        ((translate n g).inputs.map fun i => ((run gs x).insertIdx n b).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs x).getD i false) := by
      cases hop : g.op with
      | not =>
        have hv := hnot gs g [] (by simp) hop
        rw [hop] at hv
        rw [hv]
        simpa only [translate, hop, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false] using read_middle (run gs x) n b hn
      | and => simp only [translate, hop, List.map_map, Function.comp_def, read_shift]
      | or => simp only [translate, hop, List.map_map, Function.comp_def, read_shift]
      | mod k => simp only [translate, hop, List.map_map, Function.comp_def, read_shift]
      | maj => simp only [translate, hop, List.map_map, Function.comp_def, read_shift]
    rw [heval, insert_snoc _ _ _ _ hn]

def body (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (translate n), shift n C.output⟩

def headCircuit (n : ℕ) (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.take j, ((C.gates[j]?).bind fun g => g.inputs.head?).getD (n + j)⟩

theorem not_head (v : List Bool) (ins : List ℕ) (k : ℕ) (hk : v.length ≤ k) :
    GateOp.not.eval (ins.map fun i => v.getD i false) = !(v.getD (ins.headD k) false) := by
  cases ins with
  | nil =>
    change true = !(v.getD k false)
    rw [List.getD_eq_default _ _ hk]
    rfl
  | cons i ins => rfl

theorem prefix_not_value (n : ℕ) (C : Circuit) (j : ℕ)
    (h : ∀ i (g : Gate), C.gates[i]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (i = j ∧ g.op = GateOp.not)))
    (x : List Bool) (hx : x.length = n) : NotValue C.gates x (!(headCircuit n C j).eval x) := by
  intro pre g post he hop
  have hidx : C.gates[pre.length]? = some g := by rw [he]; simp
  have hj : pre.length = j := by
    rcases h pre.length g hidx with ha | ha | ha
    · rw [hop] at ha; cases ha
    · rw [hop] at ha; cases ha
    · exact ha.1
  have hp : C.gates.take j = pre := by rw [← hj, he]; simp
  have hg : C.gates[j]? = some g := by rw [← hj]; exact hidx
  have hv : (headCircuit n C j).eval x = (run pre x).getD (g.inputs.headD (n + j)) false := by
    change (run (C.gates.take j) x).getD
      (((C.gates[j]?).bind fun g => g.inputs.head?).getD (n + j)) false = _
    rw [hp, hg]
    change (run pre x).getD (g.inputs.head?.getD (n + j)) false = _
    cases g.inputs <;> rfl
  rw [hv, hop]
  exact not_head _ _ _ (by rw [run_length, hx, hj])

theorem body_monotone (n : ℕ) (C : Circuit) (j : ℕ)
    (h : ∀ i (g : Gate), C.gates[i]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (i = j ∧ g.op = GateOp.not))) :
    IsMonotoneCircuit (body n C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  rcases h i _ (List.getElem?_eq_getElem hi) with hop | hop | ⟨_, hop⟩
  · simp [translate, hop]
  · simp [translate, hop]
  · simp [translate, hop]

theorem prefix_monotone (n : ℕ) (C : Circuit) (j : ℕ)
    (h : ∀ i (g : Gate), C.gates[i]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (i = j ∧ g.op = GateOp.not))) :
    IsMonotoneCircuit (headCircuit n C j) := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  change i < (C.gates.take j).length at hi
  have hiC : i < C.gates.length := by simp only [List.length_take] at hi; omega
  have hij : i < j := by simp only [List.length_take] at hi; omega
  change ((C.gates.take j)[i]).op = GateOp.and ∨ ((C.gates.take j)[i]).op = GateOp.or
  simp only [List.getElem_take]
  rcases h i _ (List.getElem?_eq_getElem hiC) with hop | hop | ⟨he, _⟩
  · exact Or.inl hop
  · exact Or.inr hop
  · omega

end PEqualNP.Outside.L_meta_1105

open PEqualNP.Outside.L_meta_1105 in
theorem PEqualNP.Outside.L_meta_1105 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), (∀ i (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[i]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (i = j ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not))) → ∃ (D H : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D ∧ PEqualNP.CircuitLowerBounds.IsMonotoneCircuit H ∧ D.size ≤ C.size ∧ H.size ≤ C.size ∧ ∀ x : List Bool, x.length = n → C.eval x = D.eval (x ++ [!(H.eval x)]) := by
  intro n C j h
  refine ⟨body n C, headCircuit n C j, body_monotone n C j h, prefix_monotone n C j h, ?_, ?_, ?_⟩
  · simp [body, PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp [headCircuit, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x hx
    change (run C.gates x).getD C.output false =
      (run (C.gates.map (translate n)) (x ++ [!(headCircuit n C j).eval x])).getD (shift n C.output) false
    rw [simulate n C.gates x _ hx (prefix_not_value n C j h x hx), read_shift]
