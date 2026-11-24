import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3460
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]


def shift (n k i : ℕ) : ℕ := if i < n then i else i+k

lemma append_rel (n k : ℕ) (a b : List Bool) (v : Bool)
    (hn : n ≤ a.length) (hlen : b.length = a.length+k)
    (h : ∀ i, b.getD (shift n k i) false = a.getD i false) :
    ∀ i, (b++[v]).getD (shift n k i) false = (a++[v]).getD i false := by
  intro i
  by_cases hi : i < a.length
  · have hs : shift n k i < b.length := by unfold shift; split <;> omega
    rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hi]
    exact h i
  · by_cases he : i = a.length
    · subst i
      have hs : shift n k a.length = b.length := by simp [shift, Nat.not_lt.mpr hn, hlen]
      rw [hs, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      simp
    · have ha : (a++[v]).length ≤ i := by simp; omega
      have hb : (b++[v]).length ≤ shift n k i := by
        simp only [List.length_append,List.length_singleton]
        unfold shift
        split <;> omega
      rw [List.getD_eq_default _ _ hb, List.getD_eq_default _ _ ha]

lemma run_shift (n k : ℕ) (gs : List Gate) (a b : List Bool)
    (hn : n ≤ a.length) (hlen : b.length = a.length+k)
    (h : ∀ i, b.getD (shift n k i) false = a.getD i false) :
    ∀ i, (run (gs.map fun g => ({op := g.op, inputs := g.inputs.map (shift n k)} : Gate)) b).getD
      (shift n k i) false = (run gs a).getD i false := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, run_cons]
    have he : g.op.eval ((g.inputs.map (shift n k)).map (fun i => b.getD i false)) =
        g.op.eval (g.inputs.map fun i => a.getD i false) := by
      congr 1
      simp only [List.map_map, Function.comp_def, h]
    rw [he]
    apply ih
    · simp; omega
    · simp; omega
    · exact append_rel n k a b _ hn hlen h

end PEqualNP.Outside.L_meta_3460
open PEqualNP.Outside.L_meta_3460
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_3460 : ∀ (n : ℕ) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool), (∀ i < G0.length, ∀ w ∈ (G0.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w < n + i) → (∀ i : ℕ, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (if i < n then i else i + G0.length) false = (C.wires (List.ofFn x)).getD i false) ∧ (∀ i < G0.length, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false = ((⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false) := by
  intro n G0 C x _
  let a := List.ofFn x
  let b := run G0 a
  have ha : a.length = n := by simp [a]
  have hb : b.length = n+G0.length := by simp [b,run_length,ha]
  have hrel : ∀ i, b.getD (shift n G0.length i) false = a.getD i false := by
    intro i
    by_cases hi : i < n
    · simp only [shift, hi, ↓reduceIte]
      exact run_getD G0 a i (by omega)
    · have hbi : b.length ≤ shift n G0.length i := by simp [shift,hi,hb]; omega
      rw [List.getD_eq_default _ _ hbi, List.getD_eq_default _ _ (by omega)]
  constructor
  · change ∀ i, (run (G0 ++ C.gates.map (fun g =>
        ({op := g.op,inputs := g.inputs.map (shift n G0.length)} : PEqualNP.CircuitLowerBounds.Gate))) a).getD
        (shift n G0.length i) false = (run C.gates a).getD i false
    simp only [run,List.foldl_append]
    exact run_shift n G0.length C.gates a b (by omega) (by omega) hrel
  · intro i hi
    change (run (G0 ++ C.gates.map (fun g =>
        ({op := g.op,inputs := g.inputs.map (shift n G0.length)} : PEqualNP.CircuitLowerBounds.Gate))) a).getD
        (n+i) false = b.getD (n+i) false
    simp only [run,List.foldl_append]
    exact run_getD _ b (n+i) (by omega)
