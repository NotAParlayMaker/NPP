import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749_aux
open PEqualNP.CircuitLowerBounds

theorem wires_append (L : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨L ++ [g], 0⟩ x = Circuit.wires ⟨L, 0⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨L, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (L : List Gate) (x : List Bool) :
    (Circuit.wires ⟨L, 0⟩ x).length = x.length + L.length := by
  simp only [Circuit.wires]
  induction L generalizing x with
  | nil => simp
  | cons g L ih => rw [List.foldl_cons, ih]; simp; omega

theorem getD_snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : i - l.length = (i - l.length - 1) + 1 := by omega
    rw [this]
    simp

theorem mono_snoc (wx wy : List Bool) (k : ℕ) (hx : wx.length = k) (hy : wy.length = k)
    (h : ∀ i, wy.getD i false = true → wx.getD i false = true) (a b : Bool) (hab : a = true → b = true) :
    ∀ i, (wy ++ [a]).getD i false = true → (wx ++ [b]).getD i false = true := by
  intro i hi
  rw [getD_snoc] at hi ⊢
  rw [hx]
  rw [hy] at hi
  split_ifs at hi ⊢ with h1 h2
  · exact h i hi
  · exact hab hi

theorem base_mono (n : ℕ) (x y : Fin n → Bool) (hm : ∀ p : Fin n, y p = true → x p = true) (i : ℕ)
    (h : (List.ofFn y).getD i false = true) : (List.ofFn x).getD i false = true := by
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi] at h ⊢
    exact hm _ h
  · simp [List.getD_eq_getElem?_getD, hi] at h

end PEqualNP.Outside.L_meta_749_aux

open PEqualNP.Outside.L_meta_749_aux in
theorem L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hC hyX hmono hnot hlen hrep x hx
  have key : ∀ j, j ≤ C.length → PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C'.take j, 0⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn x) ∧ ∀ i, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).getD i false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn x)).getD i false = true := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp, ?_⟩
      intro i hi
      simp only [List.take_zero, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil] at hi ⊢
      exact base_mono n x y (hmono x hx) i hi
    | succ j ih =>
      intro hj
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hj' : j < C.length := by omega
      obtain ⟨g, hg⟩ : ∃ g, C[j]? = some g := ⟨C[j], List.getElem?_eq_getElem hj'⟩
      have hgm : g ∈ C := List.mem_of_getElem? hg
      obtain ⟨hops, -⟩ := hC g hgm
      obtain ⟨hr1, hr2⟩ := hrep j g hg
      have hnx := fun hn hy0 => hnot j g hg hn hy0 x hx
      have hlx : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn x)).length = n + j := by
        rw [wires_length]; simp; omega
      have hly : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).length = n + j := by
        rw [wires_length]; simp; omega
      rw [List.take_add_one (l := C), hg]
      simp only [Option.toList_some]
      rw [wires_append, wires_append]
      generalize PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn x) = wx at *
      generalize PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y) = wy at *
      rcases hops with h | h | h
      · have h2 := hr2 (by rw [h]; simp)
        rw [List.take_add_one (l := C'), h2]
        simp only [Option.toList_some]
        rw [wires_append, ih1]
        refine ⟨rfl, mono_snoc wx wy (n + j) hlx hly ih2 _ _ ?_⟩
        rw [h]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map]
        intro ha b hb
        obtain ⟨i, hi, rfl⟩ := hb
        exact ih2 i (ha _ ⟨i, hi, rfl⟩)
      · have h2 := hr2 (by rw [h]; simp)
        rw [List.take_add_one (l := C'), h2]
        simp only [Option.toList_some]
        rw [wires_append, ih1]
        refine ⟨rfl, mono_snoc wx wy (n + j) hlx hly ih2 _ _ ?_⟩
        rw [h]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map]
        intro ha
        obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := ha
        exact ⟨_, ⟨i, hi, rfl⟩, ih2 i hb⟩
      · by_cases ha : (g.inputs.map (fun i => wy.getD i false)).headD false = true
        · have h2 := (hr1 h).1 ha
          rw [List.take_add_one (l := C'), h2]
          simp only [Option.toList_some]
          rw [wires_append, ih1]
          have hxa : (g.inputs.map (fun i => wx.getD i false)).headD false = true := by
            cases hgi : g.inputs with
            | nil => rw [hgi] at ha; simp at ha
            | cons i t => rw [hgi] at ha; simp at ha ⊢; exact ih2 i ha
          refine ⟨?_, mono_snoc wx wy (n + j) hlx hly ih2 _ _ ?_⟩
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, h, hxa, Bool.not_true, List.map_nil, List.any_nil]
          · intro e
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, h, ha, Bool.not_true] at e
            exact absurd e Bool.false_ne_true
        · have ha' : (g.inputs.map (fun i => wy.getD i false)).headD false = false := by simpa using ha
          have h2 := (hr1 h).2 ha'
          rw [List.take_add_one (l := C'), h2]
          simp only [Option.toList_some]
          rw [wires_append, ih1]
          have hxa := hnx h ha'
          refine ⟨?_, mono_snoc wx wy (n + j) hlx hly ih2 _ _ ?_⟩
          · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, h, hxa, Bool.not_false, List.map_nil, List.all_nil]
          · intro _
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, h, hxa, Bool.not_false]
  intro w
  have hk := (key C.length le_rfl).1
  rw [List.take_length, ← hlen, List.take_length] at hk
  rw [hk]
