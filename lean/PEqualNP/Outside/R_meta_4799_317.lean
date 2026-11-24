import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4799_317
    (cycle : ∀ s, HasCircuitSize 7 (fun x : Fin 7 → Bool =>
      let y := Function.update x (2 : Fin 7) false
      ([1, 12, 4, 15, 26, 35, 46, 36] : List ℕ).any fun e =>
        y (Fin.ofNat 7 (e / 10)) && y (Fin.ofNat 7 (e % 10))) s → 8 ≤ s)
    (extra : ∀ (n : ℕ) (C D : Circuit) (z : Fin n) (a : Fin n → Bool),
      FanInTwo C → D.output = C.output + 1 →
      List.Forall₂ (fun g h : Gate => g.op = h.op ∧
        List.Forall₂ (fun u v : ℕ => v = u + 1 ∨ v = 0) g.inputs h.inputs) C.gates D.gates →
      a z = true → circuitFun n C a = false → D.eval (true :: List.ofFn a) = true →
      ∃ S : Finset ℕ,
        (C.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains z.val)).length < S.card ∧
        ∀ j ∈ S, j < D.size ∧
          ∃ w ∈ (gateAt D j).inputs.take (bif (gateAt D j).op.eval [false] then 1 else 2),
            ∃ b : Bool, ∀ x : Fin n → Bool,
              ((⟨D.gates.take j, 0⟩ : Circuit).wires
                (true :: List.ofFn (Function.update x z false))).getD w false = b)
    (fold : ∀ (n : ℕ) (D : Circuit) (z : Fin n) (S : Finset ℕ),
      FanInTwo D → D.eval (true :: List.ofFn (fun _ : Fin n => false)) = false →
      (∀ j ∈ S, j < D.size ∧
        ∃ w ∈ (gateAt D j).inputs.take (bif (gateAt D j).op.eval [false] then 1 else 2),
          ∃ b : Bool, ∀ x : Fin n → Bool,
            ((⟨D.gates.take j, 0⟩ : Circuit).wires
              (true :: List.ofFn (Function.update x z false))).getD w false = b) →
      ∃ s, s + S.card ≤ D.size ∧
        HasCircuitSize n (fun x => D.eval (true :: List.ofFn (Function.update x z false))) s) :
have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length = (3 : ℕ) → False := by
  intro f C D a b hfan hsize hbase hedits hmodified hor
  let z : Fin 7 := 2
  let a0 : Fin 7 → Bool := fun i => decide (i = z)
  let E : Circuit := ⟨D.gates, C.output + 1⟩
  let edits (g h : Gate) : Prop := g.op = h.op ∧
    List.Forall₂ (fun u v : ℕ => v = u + 1 ∨ v = 0) g.inputs h.inputs
  have hEdits : List.Forall₂ edits C.gates E.gates := by
    apply hedits.imp
    intro g h hgh
    exact ⟨hgh.1, hgh.2.imp (fun _ _ hs => hs.imp id And.left)⟩
  let legal (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2
  have carry {l r : List Gate} (hh : List.Forall₂ edits l r) :
      (∀ g ∈ l, legal g) → ∀ g ∈ r, legal g := by
    induction hh with
    | nil => simp
    | @cons g h l r hgh hrest ih =>
      intro all u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · obtain ⟨hop, hlen⟩ := all g (by simp)
        exact ⟨hgh.1 ▸ hop, by rw [← hgh.2.length_eq]; exact hlen⟩
      · exact ih (fun v hv => all v (List.mem_cons_of_mem g hv)) u hu
  have hfanE : FanInTwo E := carry hEdits hfan
  have hsizeE : E.size = 11 := by
    change E.gates.length = 11
    rw [← hEdits.length_eq]
    exact hsize
  have hno : circuitFun 7 C a0 = false := by
    rw [hbase]
    decide
  have hyes : E.eval (true :: List.ofFn a0) = true := by
    change (D.wires (true :: List.ofFn a0)).getD (C.output + 1) false = true
    rw [hmodified]
    decide
  have hallFalse : E.eval (true :: List.ofFn (fun _ : Fin 7 => false)) = false := by
    change (D.wires (true :: List.ofFn (fun _ : Fin 7 => false))).getD (C.output + 1) false = false
    rw [hmodified]
    decide
  obtain ⟨S, hcard, hconstants⟩ :=
    extra 7 C E z a0 hfan rfl hEdits rfl hno hyes
  obtain ⟨s, hs, hcompute⟩ := fold 7 E z S hfanE hallFalse hconstants
  have hcof : (fun x : Fin 7 → Bool => E.eval (true :: List.ofFn (Function.update x z false))) =
      (fun x : Fin 7 → Bool => f (Function.update x (2 : Fin 7) false)) := by
    funext x
    change (D.wires (true :: List.ofFn (Function.update x z false))).getD (C.output + 1) false = _
    rw [hmodified]
    change (f (Function.update x (2 : Fin 7) false) ||
      Function.update x (2 : Fin 7) false (2 : Fin 7)) = f (Function.update x (2 : Fin 7) false)
    simp
  rw [hcof] at hcompute
  have hlo := cycle s hcompute
  change (C.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).length < S.card at hcard
  omega
