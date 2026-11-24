import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Input 4 is a vertex of degree two. With input 4 fixed to false the function is the
-- ten-edge function, which needs 13 gates: bound13 is the statement of the checked L_meta_2537.
-- fixInput says that fixing input 4 to false adds no gate and removes every gate that reads it.
-- So a circuit with at most 14 gates in which two gates read input 4 would leave at most
-- 12 gates for the ten-edge function. What remains is oneReader: at most one gate reads input 4.
theorem PEqualNP.Outside.R_meta_3829_529
    (bound13 : ∀ (s : ℕ), HasCircuitSize 9 (fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) s → 13 ≤ s)
    (fixInput : ∀ (C : Circuit), FanInTwo C →
      (∃ c : Bool, ∀ x : Fin 9 → Bool,
        circuitFun 9 C (fun i => if i = 4 then false else x i) = c) ∨
      ∃ D : Circuit, FanInTwo D ∧
        D.size + (C.gates.filter (fun g : Gate => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 4)).length ≤ C.size ∧
        ∀ x : Fin 9 → Bool,
          circuitFun 9 D x = circuitFun 9 C (fun i => if i = 4 then false else x i))
    (oneReader : ∀ (C : Circuit), FanInTwo C → C.size ≤ 14 →
      (C.gates.filter (fun g : Gate => g.inputs.contains 4)).length ≤ 1 →
      ∃ x : Fin 9 → Bool, circuitFun 9 C x ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x4 ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C hfan hsize
  by_contra hne
  push Not at hne
  have hgate : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      ∀ F : ℕ → Bool,
      g.op.eval ((if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).map F)
        = g.op.eval (g.inputs.map F) := by
    intro g hg F
    obtain ⟨op, inputs⟩ := g
    rcases hg with h | h | h
    · have e : op = GateOp.and := h
      subst e
      rfl
    · have e : op = GateOp.or := h
      subst e
      rfl
    · have e : op = GateOp.not := h
      subst e
      cases inputs <;> rfl
  have hw : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
      ∀ w : List Bool,
      (gs.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    intro gs
    induction gs with
    | nil => intro _ w; rfl
    | cons g gs ih =>
      intro hg w
      have e : w ++ [g.op.eval ((if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).map
          fun i => w.getD i false)] = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] :=
        congrArg (fun b => w ++ [b]) (hgate g (hg g List.mem_cons_self) (fun i => w.getD i false))
      exact (congrArg (fun a => (gs.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a) e).trans
        (ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _)
  have key : ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size ∧
      (∀ x : Fin 9 → Bool, circuitFun 9 C' x = circuitFun 9 C x) ∧
      (C'.gates.filter (fun g : Gate => g.inputs.contains 4)).length
        = (C.gates.filter (fun g : Gate => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 4)).length := by
    refine ⟨⟨C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate)), C.output⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      refine ⟨(hfan g0 hg0).1, ?_⟩
      show (if g0.op.eval [false] = true then g0.inputs.take 1 else g0.inputs).length ≤ 2
      split_ifs
      · simp only [List.length_take]
        omega
      · exact (hfan g0 hg0).2
    · exact List.length_map _
    · intro x
      show ((C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false
        = (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false
      rw [hw C.gates (fun g hg => (hfan g hg).1) (List.ofFn x)]
    · show ((C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).filter (fun g : Gate => g.inputs.contains 4)).length = _
      rw [List.filter_map, List.length_map]
      rfl
  obtain ⟨C', hfan', hsize', hfun', hcount⟩ := key
  by_cases hr : (C'.gates.filter (fun g : Gate => g.inputs.contains 4)).length ≤ 1
  · obtain ⟨x, hx⟩ := oneReader C' hfan' (by omega) hr
    exact hx ((hfun' x).trans (hne x))
  · rcases fixInput C hfan with ⟨c, hc⟩ | ⟨D, hD, hDs, hDf⟩
    · have h0 : c = false := by
        rw [← hc (fun _ => false), hne]
        simp
      have h1 : c = true := by
        rw [← hc (fun _ => true), hne]
        simp
      exact absurd (h0.symm.trans h1) (by decide)
    · have h13 := bound13 D.size ⟨D, hD, le_rfl, fun x => by
        show circuitFun 9 D x = _
        rw [hDf x, hne]
        simp⟩
      rw [hcount] at hr
      omega
