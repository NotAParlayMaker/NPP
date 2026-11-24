import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2802

-- The edge function of the Petersen graph minus a vertex, on nine inputs.
def F (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
  x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

-- The ten input wires: the nine inputs, then the first gate x0 OR x6.
def inp (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]

-- One gate appended to the wire values, as in the circuit model.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem length_foldl : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

-- Input wires keep their values.
theorem getD_foldl_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

-- A wire that no gate reads changes nothing but itself.
theorem agree_foldl (v : ℕ) : ∀ (gs : List Gate) (w w' : List Bool),
    (∀ g ∈ gs, v ∉ g.inputs) → w.length = w'.length → v < w.length →
    (∀ i, i ≠ v → w.getD i false = w'.getD i false) →
    ∀ i, i ≠ v → (gs.foldl step w).getD i false = (gs.foldl step w').getD i false := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ _ hag; exact hag
  | cons g gs ih =>
    intro w w' hv hlen hvl hag
    rw [List.foldl_cons, List.foldl_cons]
    have hmap : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => hag i (fun h => hv g (by simp) (h ▸ hi)))
    apply ih
    · exact fun g' hg' => hv g' (by simp [hg'])
    · simp [step, hlen]
    · simp [step]; omega
    · intro i hi
      unfold step
      rw [hmap]
      by_cases h : i < w.length
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hlen ▸ h)]
        exact hag i hi
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hlen]

theorem eval_agree (C : Circuit) (v : ℕ) (hv : ∀ g ∈ C.gates, v ∉ g.inputs) (ho : C.output ≠ v)
    (w w' : List Bool) (hlen : w.length = w'.length) (hvl : v < w.length)
    (hag : ∀ i, i ≠ v → w.getD i false = w'.getD i false) : C.eval w = C.eval w' := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  exact agree_foldl v C.gates w w' hv hlen hvl hag C.output ho

theorem length_inp (x : Fin 9 → Bool) : (inp x).length = 10 := by simp [inp]

-- Agreement off one position, checked on the ten wires only.
theorem agree_of_lt (v : ℕ) (x x' : Fin 9 → Bool)
    (h : ∀ i < 10, i ≠ v → (inp x).getD i false = (inp x').getD i false) :
    ∀ i, i ≠ v → (inp x).getD i false = (inp x').getD i false := by
  intro i hi
  by_cases hi10 : i < 10
  · exact h i hi10 hi
  · rw [List.getD_eq_default _ _ (by rw [length_inp]; omega),
      List.getD_eq_default _ _ (by rw [length_inp]; omega)]

-- The output is a gate: no input wire computes the function.
theorem out_ge (C : Circuit) (hC : ∀ x : Fin 9 → Bool, C.eval (inp x) = F x) :
    10 ≤ C.output := by
  by_contra hlt
  have key : ∀ x : Fin 9 → Bool, (inp x).getD C.output false = F x := by
    intro x
    rw [← hC x]
    unfold Circuit.eval
    rw [wires_eq, getD_foldl_lt _ _ _ (by rw [length_inp]; omega)]
  have k := key (fun i => decide (i.val = C.output % 9))
  generalize C.output = o at hlt k
  interval_cases o <;> revert k <;> decide

-- An input on which the function depends is read by some gate.
theorem needed (C : Circuit) (hC : ∀ x : Fin 9 → Bool, C.eval (inp x) = F x)
    (v : ℕ) (hv : v < 10) (x x' : Fin 9 → Bool)
    (hag : ∀ i < 10, i ≠ v → (inp x).getD i false = (inp x').getD i false) (hF : F x ≠ F x') :
    1 ≤ (C.gates.flatMap Gate.inputs).count v := by
  by_contra h0
  have hz : (C.gates.flatMap Gate.inputs).count v = 0 := by omega
  rw [List.count_eq_zero] at hz
  have hread : ∀ g ∈ C.gates, v ∉ g.inputs := fun g hg hm => hz (List.mem_flatMap.2 ⟨g, hg, hm⟩)
  have ho : C.output ≠ v := by have := out_ge C hC; omega
  apply hF
  rw [← hC x, ← hC x']
  exact eval_agree C v hread ho _ _ (by rw [length_inp, length_inp]) (by rw [length_inp]; exact hv)
    (agree_of_lt v x x' hag)

theorem count_sum_le : ∀ L : List ℕ,
    L.count 0 + L.count 1 + L.count 2 + L.count 3 + L.count 4 + L.count 5 + L.count 6 +
      L.count 7 + L.count 8 ≤ L.countP (fun n => decide (n < 10)) := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.count_cons, List.countP_cons]
    by_cases ha : a < 9
    · interval_cases a <;> simp <;> omega
    · have h0 : ∀ k : ℕ, k < 9 → (if (a == k) = true then 1 else 0) = 0 := fun k hk => by
        simp; omega
      rw [h0 0 (by omega), h0 1 (by omega), h0 2 (by omega), h0 3 (by omega), h0 4 (by omega),
        h0 5 (by omega), h0 6 (by omega), h0 7 (by omega), h0 8 (by omega)]
      have := Nat.zero_le (if decide (a < 10) = true then 1 else 0)
      omega

-- Vectors with the given set of true inputs.
def vec (l : List ℕ) : Fin 9 → Bool := fun i => decide (i.val ∈ l)

theorem main (C : Circuit) (hC : ∀ x : Fin 9 → Bool, C.eval (inp x) = F x)
    (hcnt : (C.output :: C.gates.flatMap Gate.inputs).countP (fun n => decide (n < 10)) ≤ 15) :
    ∃ v : Fin 9, v ≠ 0 ∧ v ≠ 6 ∧ C.output ≠ (v : ℕ) ∧
      (C.gates.flatMap Gate.inputs).count (v : ℕ) = 1 := by
  have hout := out_ge C hC
  have n0 := needed C hC 0 (by omega) (vec [0, 4, 6]) (vec [4, 6]) (by decide) (by decide)
  have n6 := needed C hC 6 (by omega) (vec [0, 6, 8]) (vec [0, 8]) (by decide) (by decide)
  have n1 := needed C hC 1 (by omega) (vec [1, 2]) (vec [2]) (by decide) (by decide)
  have n2 := needed C hC 2 (by omega) (vec [2, 3]) (vec [3]) (by decide) (by decide)
  have n3 := needed C hC 3 (by omega) (vec [3, 4]) (vec [4]) (by decide) (by decide)
  have n4 := needed C hC 4 (by omega) (vec [4, 3]) (vec [3]) (by decide) (by decide)
  have n5 := needed C hC 5 (by omega) (vec [5, 7]) (vec [7]) (by decide) (by decide)
  have n7 := needed C hC 7 (by omega) (vec [7, 5]) (vec [5]) (by decide) (by decide)
  have n8 := needed C hC 8 (by omega) (vec [8, 5]) (vec [5]) (by decide) (by decide)
  have hsum := count_sum_le (C.gates.flatMap Gate.inputs)
  rw [List.countP_cons] at hcnt
  by_contra hne
  have t : ∀ v : Fin 9, v ≠ 0 → v ≠ 6 → (C.gates.flatMap Gate.inputs).count (v : ℕ) ≠ 1 := by
    intro v h0 h6 h1
    exact hne ⟨v, h0, h6, by have := v.isLt; omega, h1⟩
  have t1 : (C.gates.flatMap Gate.inputs).count 1 ≠ 1 := t 1 (by decide) (by decide)
  have t2 : (C.gates.flatMap Gate.inputs).count 2 ≠ 1 := t 2 (by decide) (by decide)
  have t3 : (C.gates.flatMap Gate.inputs).count 3 ≠ 1 := t 3 (by decide) (by decide)
  have t4 : (C.gates.flatMap Gate.inputs).count 4 ≠ 1 := t 4 (by decide) (by decide)
  have t5 : (C.gates.flatMap Gate.inputs).count 5 ≠ 1 := t 5 (by decide) (by decide)
  have t7 : (C.gates.flatMap Gate.inputs).count 7 ≠ 1 := t 7 (by decide) (by decide)
  have t8 : (C.gates.flatMap Gate.inputs).count 8 ≠ 1 := t 8 (by decide) (by decide)
  split_ifs at hcnt <;> omega

end PEqualNP.Outside.L_meta_2802

theorem PEqualNP.Outside.L_meta_2802 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin (9 : ℕ) → Bool), x3.eval (x2 x4) = x1 x4) → List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < (10 : ℕ))) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) ≤ (15 : ℕ) → ∃ (x6 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (6 : Fin (9 : ℕ)) ∧ x3.output ≠ ↑x6 ∧ List.count (↑x6) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) = (1 : ℕ) := by
  intro f w C hC hcnt
  exact PEqualNP.Outside.L_meta_2802.main C hC hcnt
