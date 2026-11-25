import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_5792_317
    (count : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x2 = x1 → (16 : ℕ) ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates)
    (few : ∀ (C : Circuit) (u : ℕ) (b : Bool), FanInTwo C → C.size = 18 →
      PEqualNP.NotBracket.notCount C ≤ 2 → ∃ x : Fin 10 → Bool,
        (if b = true then !(C.wires (List.ofFn x)).getD u false
          else (C.wires (List.ofFn x)).getD u false) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         x2.size = (17 : ℕ) →           have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));           have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;           ∃ (x11 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x10 x11 x3 else x10 x11 x3) ≠ x9 x11) := by
  intro g D u b hg hD _ hs
  dsimp only
  let C : Circuit := ⟨g :: D.gates, u⟩
  have fan : FanInTwo C := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | he
    · exact hg _ (List.mem_singleton_self _)
    · exact hD _ he
  have size : C.size = 18 := by
    change (g :: D.gates).length = 18
    change D.gates.length = 17 at hs
    simp [hs]
  have wires_eq : ∀ l : List Bool,
      D.wires (({ gates := [g], output := 0 } : Circuit).wires l) = C.wires l := fun _ => rfl
  by_cases hn : PEqualNP.NotBracket.notCount C ≤ 2
  · obtain ⟨x, hx⟩ := few C u b fan size hn
    exact ⟨x, by rw [wires_eq]; exact hx⟩
  by_contra hcon
  push Not at hcon
  have hc : ∀ x : Fin 10 → Bool, (if b = true then !(C.wires (List.ofFn x)).getD u false
      else (C.wires (List.ofFn x)).getD u false) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    rw [← wires_eq]
    exact hcon x
  have split : ∀ l : List Gate, (∀ h ∈ l, h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) →
      l.countP (fun h : Gate => !h.op.eval [false]) + PEqualNP.NotBracket.notCount ⟨l, 0⟩
        = l.length := by
    intro l hl
    induction l with
    | nil => simp [PEqualNP.NotBracket.notCount]
    | cons h t ih =>
      have ih' := ih (fun k hk => hl k (List.mem_cons_of_mem _ hk))
      rcases hl h (List.mem_cons_self) with e | e | e <;>
        simp [PEqualNP.NotBracket.notCount, e, GateOp.eval] at ih' ⊢ <;> omega
  have ops : ∀ h ∈ C.gates, h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not := by
    intro h hh
    have := (fan h hh).1
    simpa using this
  have hsplit := split C.gates ops
  have hlen : C.gates.length = 18 := size
  have hnot : 3 ≤ PEqualNP.NotBracket.notCount ⟨C.gates, 0⟩ := by
    have : PEqualNP.NotBracket.notCount ⟨C.gates, 0⟩ = PEqualNP.NotBracket.notCount C := rfl
    omega
  have wlen : ∀ (gs : List Gate) (l : List Bool),
      (gs.foldl (fun w k => w ++ [k.op.eval (k.inputs.map fun i => w.getD i false)]) l).length
        = l.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro l; simp
    | cons k t ih => intro l; rw [List.foldl_cons, ih]; simp; omega
  cases b with
  | false =>
    have eq : circuitFun 10 C = fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
      funext x
      have := hc x
      simp only [Bool.false_eq_true, ite_false] at this
      rw [← this]
      rfl
    have h16 := count C fan eq
    change 16 ≤ C.gates.countP (fun h : Gate => !h.op.eval [false]) at h16
    omega
  | true =>
    let C' : Circuit := ⟨C.gates ++ [({ op := GateOp.not, inputs := [u] } : Gate)], 28⟩
    have fan' : FanInTwo C' := by
      intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact fan h hh
      · simp at hh; subst hh; simp
    have eq : circuitFun 10 C' = fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
      funext x
      have := hc x
      simp only [ite_true] at this
      rw [← this]
      change ((C.gates ++ [({ op := GateOp.not, inputs := [u] } : Gate)]).foldl _ (List.ofFn x)).getD 28 false = _
      rw [List.foldl_append]
      have hl := wlen C.gates (List.ofFn x)
      rw [List.length_ofFn, hlen] at hl
      simp only [List.foldl_cons, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp)]
      rw [List.getElem_append_right (by omega)]
      simp only [hl, Nat.sub_self, List.getElem_cons_zero, List.map_cons, List.map_nil]
      rfl
    have h16 := count C' fan' eq
    change 16 ≤ (C.gates ++ [({ op := GateOp.not, inputs := [u] } : Gate)]).countP (fun h : Gate => !h.op.eval [false]) at h16
    rw [List.countP_append] at h16
    have z : [({ op := GateOp.not, inputs := [u] } : Gate)].countP (fun h : Gate => !h.op.eval [false]) = 0 := rfl
    omega
