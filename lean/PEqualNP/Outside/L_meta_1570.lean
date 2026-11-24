import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

private def line (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}

private theorem two_points : (0 : Fin 13) ∈ line 0 ∧ (1 : Fin 13) ∈ line 0 := by decide

private theorem separated : ∀ t : Fin 13, t ≠ 0 → (0 : Fin 13) ∉ line t ∨ (1 : Fin 13) ∉ line t := by decide

private theorem wire_shape (gs : List Gate) (a : ℕ) (x : List Bool) :
    ∃ ys, Circuit.wires ⟨gs,a⟩ x = x ++ ys ∧ ys.length=gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[],by simp [Circuit.wires],rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => x.getD i false)
    obtain ⟨ys,shape,len⟩ := ih (x ++ [b])
    refine ⟨b::ys,?_,by simp [len]⟩
    change Circuit.wires ⟨gs,a⟩ (x ++ [b]) = x ++ (b::ys)
    rw [shape]
    simp

private theorem input_value (gs : List Gate) (k : Fin 13) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs,k.val⟩ (List.ofFn x) = x k := by
  obtain ⟨ys,h,_⟩ := wire_shape gs k.val (List.ofFn x)
  rw [Circuit.eval,h,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using k.isLt),List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt)]
  rw [List.getElem_ofFn]

private theorem past_value (gs : List Gate) (a : ℕ) (ha : 13+gs.length ≤ a) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs,a⟩ (List.ofFn x)=false := by
  obtain ⟨ys,h,len⟩ := wire_shape gs a (List.ofFn x)
  rw [Circuit.eval,h,List.getD_eq_default _ _ (by simpa only [List.length_append,List.length_ofFn,len] using ha)]

end PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L lines gs o _ _ correct
  have zero : (0 : Fin 13) ∈ L 0 := by rw [lines 0]; exact PEqualNP.Outside.L_meta_1570.two_points.1
  have one : (1 : Fin 13) ∈ L 0 := by rw [lines 0]; exact PEqualNP.Outside.L_meta_1570.two_points.2
  have hits (a : Fin 13) (mem : a ∈ L 0) (is01 : a=0 ∨ a=1) :
      Circuit.eval ⟨gs,o 0⟩ (List.ofFn fun v => decide (v=a))=true := by
    rw [correct 0 _ (by rcases is01 with rfl | rfl <;> simp)]
    exact decide_eq_true ⟨a,mem,by simp⟩
  have h0 := hits 0 zero (.inl rfl)
  have h1 := hits 1 one (.inr rfl)
  have lo : 13 ≤ o 0 := by
    by_contra! h
    let k : Fin 13 := ⟨o 0,h⟩
    have z := PEqualNP.Outside.L_meta_1570.input_value gs k (fun v => decide (v=0))
    have w := PEqualNP.Outside.L_meta_1570.input_value gs k (fun v => decide (v=1))
    change Circuit.eval ⟨gs,o 0⟩ _ = decide (k=0) at z
    change Circuit.eval ⟨gs,o 0⟩ _ = decide (k=1) at w
    rw [h0] at z
    rw [h1] at w
    have eq := (of_decide_eq_true z.symm).symm.trans (of_decide_eq_true w.symm)
    exact (by decide : (0 : Fin 13) ≠ 1) eq
  have hi : o 0 < 13+gs.length := by
    by_contra! h
    have off := PEqualNP.Outside.L_meta_1570.past_value gs (o 0) h (fun v => decide (v=0))
    rw [h0] at off
    contradiction
  refine ⟨lo,hi,h0,h1,?_,?_⟩
  · rw [correct 0 _ (.inr (.inr (fun v hv => by simpa using hv)))]
    simp
  · intro t ht
    have split : (0 : Fin 13) ∉ L t ∨ (1 : Fin 13) ∉ L t := by
      rw [lines t]
      exact PEqualNP.Outside.L_meta_1570.separated t ht
    have promise : decide ((0 : Fin 13) ∉ L t)=true ∨ decide ((1 : Fin 13) ∉ L t)=true :=
      split.imp (fun h => decide_eq_true h) (fun h => decide_eq_true h)
    rw [correct 0 _ (promise.imp_right Or.inl)]
    apply decide_eq_true
    exact promise.elim (fun h => ⟨0,zero,h⟩) (fun h => ⟨1,one,h⟩)
