import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2850_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (14 : ℕ) →
      (∃ (g : PEqualNP.CircuitLowerBounds.Gate), List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates = [g] ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      x2 = Bool.true →
      ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (14 : ℕ) →
      (∃ (g : PEqualNP.CircuitLowerBounds.Gate), List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates = [g] ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      x2 = Bool.true →
      ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (14 : ℕ) →
      (∃ (g : PEqualNP.CircuitLowerBounds.Gate), List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates = [g] ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      x2 = Bool.true →
      ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → x2 = Bool.true → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  have foldl_getD_zero : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (b : Bool) (t : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (b :: t)).getD 0 false = b := by
    intro gs
    induction gs with
    | nil => intro b t; rfl
    | cons g gs ih =>
      intro b t
      simpa [List.foldl, List.cons_append] using ih b (t ++ [g.op.eval (g.inputs.map fun i => (b :: t).getD i false)])
  have foldl_wires_eq_nonzero : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.inputs.contains 0 = false) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ k, k ≠ 0 → w1.getD k false = w2.getD k false) →
      ∀ k, k ≠ 0 →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD k false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD k false := by
    intro gs
    induction gs with
    | nil => intro _ w1 w2 _ heq; exact heq
    | cons g gs ih =>
      intro hno0 w1 w2 hlen heq
      have hg0 : g.inputs.contains 0 = false := hno0 g (by simp)
      have hmap : (g.inputs.map fun i => w1.getD i false) = (g.inputs.map fun i => w2.getD i false) := by
        apply List.map_congr_left
        intro i hi
        apply heq i
        intro h0
        subst h0
        have : g.inputs.contains 0 = true := by simp [hi]
        rw [hg0] at this
        exact Bool.false_ne_true this
      have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = g.op.eval (g.inputs.map fun i => w2.getD i false) := by
        rw [hmap]
      apply ih (fun g' hg' => hno0 g' (by simp [hg']))
      · simp [hlen]
      · intro k hk
        dsimp only
        rw [hv]
        by_cases hlt : k < w1.length
        · have hlt2 : k < w2.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hlt, List.getElem?_append_left hlt2]
          have := heq k hk
          rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
        · have hle1 : w1.length ≤ k := by omega
          have hle2 : w2.length ≤ k := by omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_right hle1, List.getElem?_append_right hle2, hlen]
  intro x1 x2 hfit hsize hfilt hx2
  subst hx2
  match hfl : List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates with
  | [] =>
    have hno0 : ∀ g ∈ x1.gates, g.inputs.contains 0 = false := by
      intro g hg
      have := List.filter_eq_nil_iff.mp hfl g hg
      cases hc : g.inputs.contains 0
      · rfl
      · exact False.elim (this hc)
    by_cases hout : x1.output = 0
    · refine ⟨fun _ => false, ?_⟩
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, hout]
      have hof : List.ofFn (fun (x8 : Fin 9) => if x8 = 0 then true != false else false) =
          true :: List.replicate 8 false := by decide
      rw [hof, foldl_getD_zero]
      decide
    · let a : Fin 9 → Bool := fun i => decide (i = 1)
      let b : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have heq_ab :
          PEqualNP.MetaComplexity.circuitFun 9 x1 (fun x8 => if x8 = 0 then true != a 0 else a x8) =
          PEqualNP.MetaComplexity.circuitFun 9 x1 (fun x8 => if x8 = 0 then true != b 0 else b x8) := by
        simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
          PEqualNP.CircuitLowerBounds.Circuit.wires]
        apply foldl_wires_eq_nonzero x1.gates hno0
        · simp
        · intro k hk
          by_cases hlt : k < 9
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_ofFn, List.getElem?_ofFn]
            simp only [hlt, ↓reduceDIte]
            have hne : (⟨k, hlt⟩ : Fin 9) ≠ 0 := by
              intro h0
              exact hk (congrArg Fin.val h0)
            simp [hne, a, b]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        · exact hout
      by_cases hva : PEqualNP.MetaComplexity.circuitFun 9 x1 (fun x8 => if x8 = 0 then true != a 0 else a x8) = false
      · refine ⟨b, ?_⟩
        rw [← heq_ab, hva]
        decide
      · refine ⟨a, ?_⟩
        intro hcontra
        have hfalse : (a 0 && a 1 || a 1 && a 2 || a 2 && a 3 || a 3 && a 4 || a 4 && a 0 || a 0 && a 5 || a 1 && a 6 || a 2 && a 7 || a 3 && a 8 || a 5 && a 7 || a 6 && a 8 || a 8 && a 5) = false := by decide
        rw [hfalse] at hcontra
        exact hva hcontra
  | [g] =>
    have hmem : g ∈ x1.gates := by
      have : g ∈ List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates := by
        rw [hfl]; simp
      exact (List.mem_filter.mp this).1
    have hgate := hfit g hmem
    cases hop : g.op
    · exact h1 x1 true hfit hsize ⟨g, hfl, hop⟩ rfl
    · exact h2 x1 true hfit hsize ⟨g, hfl, hop⟩ rfl
    · exact h3 x1 true hfit hsize ⟨g, hfl, hop⟩ rfl
    · simp [hop] at hgate
    · simp [hop] at hgate
  | _ :: _ :: _ =>
    rw [hfl] at hfilt
    simp at hfilt
