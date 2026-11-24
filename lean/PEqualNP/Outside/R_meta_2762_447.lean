import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- With input 0 false the function is the nine-edge function on the other eight vertices, which
-- needs 12 gates: small is the statement of the checked L_meta_1664, after renaming the vertices.
-- fixZero: with input 0 false, wire 9 is true and wire 10 is one OR gate; every gate that reads
-- wire 0 or wire 9 goes away. So three such gates among the 13 leave at most 11 gates.
-- What remains is fewReaders: at most two gates read wire 0 or wire 9.
theorem PEqualNP.Outside.R_meta_2762_447
    (small : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11)
    (fixZero : ∀ (a b : Fin 9) (C : Circuit), FanInTwo C →
      (∃ c : Bool, ∀ x : Fin 9 → Bool, x 0 = false →
        C.eval (List.ofFn x ++ [true, x a || x b]) = c) ∨
      ∃ E : Circuit, FanInTwo E ∧
        E.size + (C.gates.filter (fun g : Gate => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 0 || (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 9)).length ≤ C.size + 1 ∧
        ∀ x : Fin 9 → Bool, x 0 = false →
          E.eval (List.ofFn (fun j : Fin 8 => x (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0))) =
            C.eval (List.ofFn x ++ [true, x a || x b]))
    (fewReaders : ∀ (l : List ℕ), l.length = 2 →
      (∀ k ∈ l, k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 8) →
      ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      (C.gates.filter (fun g : Gate => g.inputs.contains 0 || g.inputs.contains 9)).length ≤ 2 →
      ∃ x : Fin 9 → Bool,
        C.eval ((List.ofFn x ++ [!x 0]) ++
          [GateOp.or.eval (List.map (fun (k : ℕ) => (List.ofFn x ++ [!x 0]).getD k false) l)]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro l hlen hmem C hfan hsize
  by_contra hne
  have hall : ∀ x : Fin 9 → Bool,
      C.eval ((List.ofFn x ++ [!x 0]) ++
        [GateOp.or.eval (List.map (fun (k : ℕ) => (List.ofFn x ++ [!x 0]).getD k false) l)]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have ha9 : a < 9 := by omega
  have hb9 : b < 9 := by omega
  have hget : ∀ (x : Fin 9 → Bool) (k : ℕ) (hk : k < 9),
      (List.ofFn x ++ [!x 0]).getD k false = x ⟨k, hk⟩ := by
    intro x k hk
    interval_cases k <;> rfl
  have hinput : ∀ x : Fin 9 → Bool, x 0 = false →
      (List.ofFn x ++ [!x 0]) ++
        [GateOp.or.eval (List.map (fun (k : ℕ) => (List.ofFn x ++ [!x 0]).getD k false) [a, b])]
      = List.ofFn x ++ [true, x ⟨a, ha9⟩ || x ⟨b, hb9⟩] := by
    intro x hx0
    have e1 : GateOp.or.eval (List.map (fun (k : ℕ) => (List.ofFn x ++ [!x 0]).getD k false) [a, b])
        = (x ⟨a, ha9⟩ || x ⟨b, hb9⟩) := by
      show ((List.ofFn x ++ [!x 0]).getD a false || ((List.ofFn x ++ [!x 0]).getD b false || false)) = _
      rw [hget x a ha9, hget x b hb9, Bool.or_false]
    rw [e1, hx0, List.append_assoc]
    rfl
  have hgate : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      ∀ Fv : ℕ → Bool,
      g.op.eval ((if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).map Fv)
        = g.op.eval (g.inputs.map Fv) := by
    intro g hg Fv
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
        congrArg (fun v => w ++ [v]) (hgate g (hg g List.mem_cons_self) (fun i => w.getD i false))
      exact (congrArg (fun u => (gs.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u) e).trans
        (ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _)
  have key : ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size ∧
      (∀ w : List Bool, C'.eval w = C.eval w) ∧
      (C'.gates.filter (fun g : Gate => g.inputs.contains 0 || g.inputs.contains 9)).length = (C.gates.filter (fun g : Gate => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 0 || (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 9)).length := by
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
    · intro w
      show ((C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD C.output false
        = (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD C.output false
      rw [hw C.gates (fun g hg => (hfan g hg).1) w]
    · show ((C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).filter (fun g : Gate => g.inputs.contains 0 || g.inputs.contains 9)).length = _
      rw [List.filter_map, List.length_map]
      rfl
  obtain ⟨C', hfan', hsize', heval', hcount⟩ := key
  by_cases hr : (C'.gates.filter (fun g : Gate => g.inputs.contains 0 || g.inputs.contains 9)).length ≤ 2
  · obtain ⟨x, hx⟩ := fewReaders [a, b] rfl hmem C' hfan' (by omega) hr
    exact hx ((heval' _).trans (hall x))
  · rw [hcount] at hr
    have hC : ∀ x : Fin 9 → Bool, x 0 = false →
        C.eval (List.ofFn x ++ [true, x ⟨a, ha9⟩ || x ⟨b, hb9⟩]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro x hx0
      rw [← hinput x hx0]
      exact hall x
    rcases fixZero ⟨a, ha9⟩ ⟨b, hb9⟩ C hfan with ⟨c, hc⟩ | ⟨E, hE, hEs, hEf⟩
    · have h0 : c = false := by
        rw [← hc (fun _ => false) rfl, hC (fun _ => false) rfl]
        rfl
      have h1 : c = true := by
        rw [← hc (fun i => decide (i ≠ 0)) rfl, hC (fun i => decide (i ≠ 0)) rfl]
        rfl
      exact absurd (h0.symm.trans h1) (by decide)
    · apply small
      refine ⟨E, hE, by omega, fun y => ?_⟩
      have hx0 : (fun i : Fin 9 => if i = 0 then false else y (([0, 0, 1, 2, 6, 7, 4, 5, 3] : List (Fin 8)).getD i.val 0)) 0 = false := rfl
      have hin : (fun j : Fin 8 => (fun i : Fin 9 => if i = 0 then false else y (([0, 0, 1, 2, 6, 7, 4, 5, 3] : List (Fin 8)).getD i.val 0)) (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0)) = y := by
        funext j
        fin_cases j <;> rfl
      have h1 := hEf (fun i : Fin 9 => if i = 0 then false else y (([0, 0, 1, 2, 6, 7, 4, 5, 3] : List (Fin 8)).getD i.val 0)) hx0
      rw [hin] at h1
      rw [h1, hC _ hx0]
      have taut : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
          (false && b0 || b0 && b1 || b1 && b2 || b2 && b6 || b6 && false || false && b7 ||
            b0 && b4 || b1 && b5 || b2 && b3 || b7 && b5 || b4 && b3 || b3 && b7)
          = ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b0) || (b1 && b5) ||
            (b2 && b6) || (b3 && b7) || (b5 && b7)) := by decide
      exact taut (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
