import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split the residual after the forced first gate OR(x_0, x_1) by the operation of the second
-- gate. Size at least two follows from evaluation: a one-gate circuit cannot compute the
-- edge function. Fan-in two leaves only AND, OR, or NOT for that gate.
theorem PEqualNP.Outside.R_meta_2498_2
    (hAnd : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (∃ g, C.gates[1]? = some g ∧ g.op = GateOp.and) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
          (∃ i < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD i false))) →
        S.card ≤ 3) →
      16 ≤ C.size)
    (hOr : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (∃ g, C.gates[1]? = some g ∧ g.op = GateOp.or) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
          (∃ i < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD i false))) →
        S.card ≤ 3) →
      16 ≤ C.size)
    (hNot : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (∃ g, C.gates[1]? = some g ∧ g.op = GateOp.not) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
          (∃ i < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD i false))) →
        S.card ≤ 3) →
      16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro C hFan hFirst hFun hDeg
  let F : (Fin 9 → Bool) → Bool := fun x =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  have hFun' : circuitFun 9 C = F := hFun.trans (by decide +kernel)
  have step_len (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp; omega
  have wires_len (x : Fin 9 → Bool) :
      (C.wires (List.ofFn x)).length = 9 + C.size := by
    simpa [Circuit.wires, Circuit.size, List.length_ofFn] using step_len C.gates (List.ofFn x)
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
        = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp; omega
  let edge23 : Fin 9 → Bool := fun i => decide (i.val = 2 ∨ i.val = 3)
  let edge01 : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 1)
  have F23 : F edge23 = true := by decide +kernel
  have F01 : F edge01 = true := by decide +kernel
  have n01 : (fun x : Fin 9 → Bool => x 0 || x 1) ≠ F := by
    intro eq
    have h := congrFun eq edge23
    have hL : (edge23 0 || edge23 1) = false := by decide +kernel
    rw [hL, F23] at h
    exact Bool.false_ne_true h
  have nFalse : (fun _ : Fin 9 → Bool => false) ≠ F := by
    intro eq
    have h := congrFun eq edge01
    rw [F01] at h
    exact Bool.false_ne_true h
  have nBit (i : Fin 9) : (fun x : Fin 9 → Bool => x i) ≠ F := by
    intro eq
    by_cases hiv : i.val = 2 ∨ i.val = 3
    · have hL : edge01 i = false := by
        rcases hiv with hi | hi
        · have : i = 2 := Fin.eq_of_val_eq hi
          subst this
          decide +kernel
        · have : i = 3 := Fin.eq_of_val_eq hi
          subst this
          decide +kernel
      have h := congrFun eq edge01
      rw [hL, F01] at h
      exact Bool.false_ne_true h
    · have hL : edge23 i = false := by
        have : i.val ≠ 2 ∧ i.val ≠ 3 := ⟨fun h => hiv (Or.inl h), fun h => hiv (Or.inr h)⟩
        simp [edge23, this.1, this.2]
      have h := congrFun eq edge23
      rw [hL, F23] at h
      exact Bool.false_ne_true h
  have two : 2 ≤ C.size := by
    by_contra h
    have hs : C.size ≤ 1 := by omega
    interval_cases hsz : C.size
    · have hf := hFirst (fun _ => true)
      have hlen : (C.wires (List.ofFn (fun _ : Fin 9 => true))).length = 9 := by
        simpa [hsz] using wires_len (fun _ => true)
      have hz : (C.wires (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = false :=
        List.getD_eq_default _ _ (by omega)
      have ht : ((true : Bool) || true) = true := rfl
      rw [hz, ht] at hf
      exact Bool.false_ne_true hf
    · have hlen : (C.wires (List.ofFn edge01)).length = 10 := by
        simpa [hsz] using wires_len edge01
      by_cases h9 : C.output = 9
      · apply n01
        funext x
        have hx := hFirst x
        have hcf : C.eval (List.ofFn x) = F x := by
          simpa [circuitFun] using congrFun hFun' x
        change (C.wires (List.ofFn x)).getD C.output false = F x at hcf
        rw [h9] at hcf
        exact hx.symm.trans hcf
      · by_cases hlt : C.output < 9
        · apply nBit ⟨C.output, hlt⟩
          funext x
          have hi : C.output < (List.ofFn x).length := by simp; omega
          have hkeep := keep C.gates (List.ofFn x) C.output hi
          have hcf : C.eval (List.ofFn x) = F x := by
            simpa [circuitFun] using congrFun hFun' x
          change (C.wires (List.ofFn x)).getD C.output false = F x at hcf
          have hx : (C.wires (List.ofFn x)).getD C.output false = x ⟨C.output, hlt⟩ := by
            change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                (List.ofFn x)).getD C.output false = _
            rw [hkeep, List.getD_eq_getElem (l := List.ofFn x) (n := C.output) false (by simp; exact hlt)]
            exact List.getElem_ofFn (n := 9) (f := x) (i := C.output) (h := by simp; exact hlt)
          rw [← hx, hcf]
        · have heval : (C.wires (List.ofFn edge01)).getD C.output false = false :=
            List.getD_eq_default _ _ (by omega)
          have hcf : C.eval (List.ofFn edge01) = F edge01 := by
            simpa [circuitFun] using congrFun hFun' edge01
          change (C.wires (List.ofFn edge01)).getD C.output false = F edge01 at hcf
          rw [heval, F01] at hcf
          exact Bool.false_ne_true hcf
  have hg1 : ∃ g, C.gates[1]? = some g := by
    refine ⟨C.gates[1], ?_⟩
    exact List.getElem?_eq_getElem (show 1 < C.gates.length by simpa [Circuit.size] using (Nat.succ_le_iff.mp two))
  obtain ⟨g, hg⟩ := hg1
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    have hmem : g ∈ C.gates := List.mem_iff_getElem?.2 ⟨1, hg⟩
    have := (hFan g hmem).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hFedge : circuitFun 9 C = (fun x : Fin 9 → Bool =>
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) := hFun'
  rcases hop with hand | hor | hnot
  · exact hAnd C hFan hFirst ⟨g, hg, hand⟩ hFedge hDeg
  · exact hOr C hFan hFirst ⟨g, hg, hor⟩ hFedge hDeg
  · exact hNot C hFan hFirst ⟨g, hg, hnot⟩ hFedge hDeg
