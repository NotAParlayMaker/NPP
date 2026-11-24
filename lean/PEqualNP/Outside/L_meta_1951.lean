import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1951_aux

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

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true)
    (hN : ∀ k, ∀ hk : k < C.gates.length,
      ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
      value C x (n + k) = true → value C y (n + k) = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact hN (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]


lemma andOr_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  apply mono C x y hxy
  intro k hk hn
  exact (hn (hC _ (List.getElem_mem hk))).elim



end PEqualNP.Outside.L_meta_1951_aux

open PEqualNP.Outside.L_meta_1951_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_1951 : (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → ∀ (N240 : ℕ) (I240 : Fin N240 → Fin N240 → Prop) [DecidableRel I240] (C240 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g240 ∈ C240.gates, (g240.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g240.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g240.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N240 + N240) C240) → (∀ j240 < C240.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240 0 = 0) ∨ (∀ h240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240 0 = 0)) → (∀ p240 p240x1 w240 w240x1 : Fin N240, p240 ≠ p240x1 → w240 ≠ w240x1 → I240 p240 w240 → I240 p240x1 w240 → I240 p240 w240x1 → I240 p240x1 w240x1 → False) → (∃ p240x2 w240x2 : Fin N240, I240 p240x2 w240x2) → (∀ p240x3 w240x3 : Fin N240, I240 p240x3 w240x3 → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append (fun a240 : Fin N240 => decide (a240 = p240x3)) (fun a240x1 : Fin N240 => decide (a240x1 = w240x3))) = true) → (∀ x240 y240 : Fin N240 → Bool, (Finset.univ.filter (fun l240 : Fin N240 => y240 l240 = true)).card ≤ 1 → (¬ ∃ p240x4 w240x4 : Fin N240, I240 p240x4 w240x4 ∧ x240 p240x4 = true ∧ y240 w240x4 = true) → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append x240 y240) = false) → ∀ mixed240 : ℕ → Prop, mixed240 = (fun i240x1 : ℕ => 0 < (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD i240x1 0 ∧ 0 < (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x1 0) → ∀ cone240 : ℕ → Prop, cone240 = (fun j240x1 : ℕ => j240x1 < C240.gates.length ∧ mixed240 (N240 + N240 + j240x1) ∧ Relation.ReflTransGen (fun a240x2 b240 : ℕ => a240x2 < b240 ∧ ∃ f240 : Fin C240.gates.length, b240 = N240 + N240 + f240.val ∧ a240x2 ∈ (C240.gates.get f240).inputs) (N240 + N240 + j240x1) C240.output) → ∀ gok240 : (Fin N240 → Bool) → ℕ → Prop, gok240 = (fun (x240x1 : Fin N240 → Bool) (j240x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i240x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x2 0 = 0 ∧ (C240.wires (List.ofFn (Fin.append x240x1 (fun u240 : Fin N240 => false)))).getD i240x2 false = true) → ∀ step240 : (Fin N240 → Bool) → ℕ → ℕ → Prop, step240 = (fun (x240x2 : Fin N240 → Bool) (j240x3 j240x4 : ℕ) => cone240 j240x4 ∧ N240 + N240 + j240x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x4).inputs ∧ gok240 x240x2 j240x4) → ∀ slot240 : ℕ → ℕ → Prop, slot240 = (fun h240x1 j240x5 : ℕ => cone240 j240x5 ∧ h240x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x5).inputs ∧ (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240x1 0 = 0) → ∀ lh240 : ℕ → Fin N240 → Prop, lh240 = (fun (h240x2 : ℕ) (w240x5 : Fin N240) => (C240.wires (List.ofFn (Fin.append (fun u240x1 : Fin N240 => false) (fun a240x3 : Fin N240 => decide (a240x3 = w240x5))))).getD h240x2 false = true) → ∀ (h240x3 j240x6 j240x7 : ℕ) (w240x6 p240x5 : Fin N240), slot240 h240x3 j240x6 → lh240 h240x3 w240x6 → gok240 (fun a240x4 : Fin N240 => decide (¬ I240 a240x4 w240x6)) j240x6 → Relation.ReflTransGen (step240 (fun a240x5 : Fin N240 => decide (¬ I240 a240x5 w240x6))) j240x6 j240x7 → ¬ I240 p240x5 w240x6 → ∀ j240x8 : ℕ, N240 + N240 + j240x8 = C240.output → ¬ Relation.ReflTransGen (step240 (fun a240x6 : Fin N240 => decide (a240x6 = p240x5))) j240x7 j240x8 := by

  classical
  intro live N I inst C hC hkm hfour hedge haccept hreject
    mixed hmixed cone hcone gok hgok step hstep slot hslot lh hlh
    h j k w p hs hline hg hpath hnot o hout htail
  let lvx : (Fin N → Bool) → ℕ → Prop := fun x j => cone j ∧ gok x j ∧
    ∃ o, N+N+o=C.output ∧ Relation.ReflTransGen (step x) j o
  let ap : ℕ → Fin N → Prop := fun h p => ∃ j, slot h j ∧ lvx (fun a => decide (a=p)) j
  let lpw : ℕ → Fin N → Prop := fun h w => ∀ v, lh h v ↔ v=w
  let ppw : ℕ → Fin N → Prop := fun h p =>
    (∃ w v, w≠v ∧ lh h w ∧ lh h v) ∧ ∀ a, ap h a ↔ a=p
  let lps : Fin N → Fin N → Prop := fun p w => ∃ h, lpw h w ∧ ap h p
  let pps : Fin N → Fin N → Prop := fun p w => ∃ h, ppw h p ∧ lh h w
  have hall := live N I C hC hkm hfour hedge haccept hreject
    mixed hmixed cone hcone gok hgok step hstep lvx rfl slot hslot
    ap rfl lh hlh lpw rfl ppw rfl lps rfl pps rfl
  have ban := hall.2.2.2.1 h j w hs hline
  apply ban
  have hj : cone j := by rw [hslot] at hs; exact hs.1
  refine ⟨hj,hg,o,hout,hpath.trans ?_⟩
  apply Relation.ReflTransGen.mono ?_ k o htail
  intro a b hab
  rw [hstep] at hab ⊢
  refine ⟨hab.1,hab.2.1,?_⟩
  have hg' := hab.2.2
  rw [hgok] at hg' ⊢
  rcases hg' with hor | ⟨i,hi,hdeg,hval⟩
  · exact Or.inl hor
  · refine Or.inr ⟨i,hi,hdeg,?_⟩
    have hand : PEqualNP.EdgeOwnership.AndOrOnly C := fun g hg => (hC.1 g hg).1
    apply andOr_mono C hand _ _ ?_ i hval
    intro t
    refine Fin.addCases ?_ ?_ t
    · intro a ha
      have he : a=p := by simpa only [Fin.append_left,decide_eq_true_eq] using ha
      subst a
      simpa only [Fin.append_left,decide_eq_true_eq] using hnot
    · intro l hl
      simpa only [Fin.append_right] using hl
