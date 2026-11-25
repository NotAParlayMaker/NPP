import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7211

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7211

theorem PEqualNP.Outside.L_meta_7211 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     x1 ≤ x2.output →       x2.output < x1 + x2.size →         (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x2.output - x1]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and) →           (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x7]? = Option.some x8 → ∃ (x10 : ℕ) (x11 : ℕ), x8.inputs = [x10, x11] ∧ x10 < x11 ∧ x11 < x1 + x7) →             ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ),               PEqualNP.MetaComplexity.Monotone2 x8 ∧                 x8.size + (1 : ℕ) ≤ x2.size ∧                   x9 < x10 ∧                     x10 < x1 + x8.size ∧                       have x11 : ℕ → (Fin x1 → Bool) → Bool := fun (x11 : ℕ) (x12 : Fin x1 → Bool) => (x8.wires (List.ofFn x12)).getD x11 Bool.false;                       (∀ (x12 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x12 = Bool.true → x11 x9 x12 = Bool.true ∧ x11 x10 x12 = Bool.true) ∧ ∀ (x12 x13 : Fin x1 → Bool), x11 x9 x12 = Bool.true → x11 x10 x13 = Bool.true → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x16 : Fin x1) => x12 x16 || x13 x16) = Bool.true := by
  intro n C hC ho1 ho2 hg hin
  obtain ⟨g, hg1, hg2⟩ := hg
  obtain ⟨a, b, hab, hlt, hb⟩ := hin _ _ hg1
  have hk : C.output - n < C.gates.length := by have : C.size = C.gates.length := rfl; omega
  have hop : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g h => by simpa using (hC g h).1
  have hop' : ∀ g ∈ C.gates.take (C.output - n), g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g h => hop g (List.mem_of_mem_take h)
  have hlen : (C.gates.take (C.output - n)).length = C.output - n := by rw [List.length_take]; omega
  have pre : ∀ (x : Fin n → Bool) (w : ℕ), w < n + (C.output - n) → (PEqualNP.Outside.L_meta_7211.run C.gates (List.ofFn x)).getD w false = (PEqualNP.Outside.L_meta_7211.run (C.gates.take (C.output - n)) (List.ofFn x)).getD w false := by
    intro x w hw
    have := PEqualNP.Outside.L_meta_7211.run_prefix (C.gates.take (C.output - n)) (C.gates.drop (C.output - n)) (List.ofFn x) w (by simp; omega)
    rw [List.take_append_drop] at this
    exact this
  have val : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = ((PEqualNP.Outside.L_meta_7211.run (C.gates.take (C.output - n)) (List.ofFn x)).getD a false && (PEqualNP.Outside.L_meta_7211.run (C.gates.take (C.output - n)) (List.ofFn x)).getD b false) := by
    intro x
    have h := PEqualNP.Outside.L_meta_7211.run_gate C.gates (List.ofFn x) (C.output - n) hk
    have e : C.gates[C.output - n] = g := by
      rw [List.getElem?_eq_getElem hk] at hg1
      exact Option.some.inj hg1
    rw [List.length_ofFn, e, hab, hg2] at h
    simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at h
    rw [if_pos (by omega), if_pos hb, pre x a (by omega), pre x b hb] at h
    rw [← h]
    have : n + (C.output - n) = C.output := by omega
    rw [this]
    rfl
  refine ⟨⟨C.gates.take (C.output - n), 0⟩, a, b, fun g hg => hC g (List.mem_of_mem_take hg), ?_, hlt, ?_, ?_⟩
  · change (C.gates.take (C.output - n)).length + 1 ≤ C.gates.length
    omega
  · change b < n + (C.gates.take (C.output - n)).length
    omega
  intro W
  have mo : ∀ (w : ℕ) (x y : Fin n → Bool), (∀ i, x i = true → y i = true) → W w x = true → W w y = true := by
    intro w x y hxy h
    refine PEqualNP.Outside.L_meta_7211.mono _ (List.ofFn x) (List.ofFn y) (by simp) ?_ hop' w h
    intro i hi
    by_cases hi' : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi'] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
  have val' : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = (W a x && W b x) := val
  refine ⟨fun x h => ?_, fun x y h1 h2 => ?_⟩
  · rw [val', Bool.and_eq_true] at h
    exact h
  · rw [val', Bool.and_eq_true]
    exact ⟨mo a x _ (fun i h => by simp [h]) h1, mo b y _ (fun i h => by simp [h]) h2⟩
