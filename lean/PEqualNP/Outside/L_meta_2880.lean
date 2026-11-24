import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2880_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma getD_snoc_lt (l : List Bool) (v d : Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (l : List Bool) (v d : Bool) (i : ℕ) (hi : i = l.length) :
    (l ++ [v]).getD i d = v := by
  subst hi
  simp [List.getD]

lemma all_imp {l l' : List Bool} (hlen : l.length = l'.length)
    (h : ∀ i (hi : i < l.length), l[i] = true → l'[i]'(by omega) = true) :
    l.all id = true → l'.all id = true := by
  intro hl
  rw [List.all_eq_true] at hl ⊢
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  have hi' : i < l.length := by omega
  exact h i hi' (hl _ (List.getElem_mem hi'))

lemma any_imp {l l' : List Bool} (hlen : l.length = l'.length)
    (h : ∀ i (hi : i < l.length), l[i] = true → l'[i]'(by omega) = true) :
    l.any id = true → l'.any id = true := by
  intro hl
  rw [List.any_eq_true] at hl ⊢
  rcases hl with ⟨b, hb, hbtrue⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  exact ⟨l'[i]'(by omega), List.getElem_mem _, h i hi hbtrue⟩

lemma gate_eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l l' : List Bool} (hlen : l.length = l'.length)
    (h : ∀ i (hi : i < l.length), l[i] = true → l'[i]'(by omega) = true) :
    op.eval l = true → op.eval l' = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval]
    exact all_imp hlen h
  · simp only [GateOp.eval]
    exact any_imp hlen h

lemma gate_eval_le {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {w w' : List Bool} (hlen : w.length = w'.length)
    (hle : ∀ i, w.getD i false ≤ w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [Bool.le_iff_imp]
  refine gate_eval_mono (l := g.inputs.map fun i => w.getD i false)
    (l' := g.inputs.map fun i => w'.getD i false) hop ?_ ?_
  · simp
  · intro i hi hli
    have hi' : i < g.inputs.length := by simpa using hi
    have hli' : w.getD (g.inputs[i]'hi') false = true := by
      simpa [List.getElem_map] using hli
    have := (Bool.le_iff_imp.mp (hle (g.inputs[i]'hi'))) hli'
    simpa [List.getElem_map] using this

def LeWires (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false ≤ w'.getD i false

lemma step_le {w w' : List Bool} (h : LeWires w w') {g : Gate}
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    LeWires (step w g) (step w' g) := by
  obtain ⟨hlen, hle⟩ := h
  constructor
  · simp [step, hlen]
  · intro i
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false ≤
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).getD i false
    by_cases hi : i < w.length
    · rw [getD_snoc_lt _ _ _ _ hi, getD_snoc_lt _ _ _ _ (by omega)]
      exact hle i
    · by_cases hie : i = w.length
      · subst hie
        rw [getD_snoc_eq _ _ _ _ rfl, getD_snoc_eq _ _ _ _ (by omega)]
        exact gate_eval_le hop hlen hle
      · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]

lemma foldl_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {w w' : List Bool} (h : LeWires w w') :
    LeWires (gs.foldl step w) (gs.foldl step w') := by
  induction gs generalizing w w' with
  | nil => simpa [step]
  | cons g gs ih =>
      simp only [List.foldl_cons]
      exact ih (fun h' hh' => hgs h' (List.mem_cons_of_mem _ hh'))
        (step_le h (hgs g (by simp)))

lemma ofFn_le {n : ℕ} {x y : Fin n → Bool} (hxy : x ≤ y) :
    LeWires (List.ofFn x) (List.ofFn y) := by
  constructor
  · simp
  · intro i
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simpa [List.getElem_ofFn] using (Pi.le_def.mp hxy ⟨i, hi⟩)
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma wires_mono {n : ℕ} {C : Circuit} (hmono : Monotone2 C)
    {x y : Fin n → Bool} (hxy : x ≤ y) :
    LeWires (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
  cases C with
  | mk gates output =>
    have hgs : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have h := (hmono g hg).1
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    have h := foldl_mono gates hgs (ofFn_le hxy)
    rw [wires_eq]
    exact h

lemma eval_mono {n : ℕ} {C : Circuit} (hmono : Monotone2 C)
    {x y : Fin n → Bool} (hxy : x ≤ y) :
    C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) := by
  have h := wires_mono hmono hxy
  unfold Circuit.eval
  exact h.2 C.output

lemma exists_minimal_true {n : ℕ} (f : (Fin n → Bool) → Prop) {x : Fin n → Bool}
    (hx : f x) : ∃ y, Minimal f y ∧ y ≤ x := by
  let s : Set (Fin n → Bool) := {y | f y ∧ y ≤ x}
  have hs : s.Finite := Set.finite_univ.subset (fun y _ => Set.mem_univ y)
  have hne : s.Nonempty := ⟨x, hx, le_rfl⟩
  obtain ⟨y, hy⟩ := Set.Finite.exists_minimal hs hne
  refine ⟨y, ⟨hy.1.1, ?_⟩, hy.1.2⟩
  intro z hfz hz
  exact hy.2 ⟨hfz, le_trans hz hy.1.2⟩ hz

lemma exists_maximal_false {n : ℕ} (f : (Fin n → Bool) → Prop) {x : Fin n → Bool}
    (hx : ¬ f x) : ∃ z, Maximal (fun z => ¬ f z) z ∧ x ≤ z := by
  let s : Set (Fin n → Bool) := {y | ¬ f y ∧ x ≤ y}
  have hs : s.Finite := Set.finite_univ.subset (fun y _ => Set.mem_univ y)
  have hne : s.Nonempty := ⟨x, hx, le_rfl⟩
  obtain ⟨z, hz⟩ := Set.Finite.exists_maximal hs hne
  refine ⟨z, ⟨hz.1.1, ?_⟩, hz.1.2⟩
  intro w hfw hw
  exact hz.2 ⟨hfw, le_trans hz.1.2 hw⟩ hw

end PEqualNP.Outside.L_meta_2880_aux

open PEqualNP.Outside.L_meta_2880_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2880 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x2 →
      ∀ (x4 : (Fin x1 → Bool) → Prop),
        (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) →
        (∀ (x6 : Fin x1 → Bool),
          Maximal (fun (x7 : Fin x1 → Bool) => ¬ x4 x7) x6 →
            x2.eval (List.ofFn x6) = Bool.false) →
        ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  intro n C hmono f hmin hmax x
  constructor
  · intro hC
    by_contra hfx
    obtain ⟨z, hzmax, hxz⟩ := exists_maximal_false f hfx
    have hzC : C.eval (List.ofFn z) = false := hmax z hzmax
    have hle : C.eval (List.ofFn x) ≤ C.eval (List.ofFn z) := eval_mono hmono hxz
    have hztrue : C.eval (List.ofFn z) = true := (Bool.le_iff_imp.mp hle) hC
    rw [hzC] at hztrue
    exact Bool.noConfusion hztrue
  · intro hfx
    obtain ⟨y, hymin, hyx⟩ := exists_minimal_true f hfx
    have hyC : C.eval (List.ofFn y) = true := hmin y hymin
    have hle : C.eval (List.ofFn y) ≤ C.eval (List.ofFn x) := eval_mono hmono hyx
    exact (Bool.le_iff_imp.mp hle) hyC
