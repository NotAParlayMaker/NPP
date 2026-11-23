import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926

lemma mk (n s : ℕ) (f : (Fin n → Bool) → Bool) (cs : List (Bool × ℕ × ℕ)) (o : ℕ)
    (hs : cs.length ≤ s)
    (hev : ∀ x : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨cs.map (fun c => (⟨if c.1 then PEqualNP.CircuitLowerBounds.GateOp.and
            else PEqualNP.CircuitLowerBounds.GateOp.or, [c.2.1, c.2.2]⟩ :
            PEqualNP.CircuitLowerBounds.Gate)), o⟩ (List.ofFn x) = f x) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  refine ⟨⟨cs.map (fun c => (⟨if c.1 then PEqualNP.CircuitLowerBounds.GateOp.and
            else PEqualNP.CircuitLowerBounds.GateOp.or, [c.2.1, c.2.2]⟩ :
            PEqualNP.CircuitLowerBounds.Gate)), o⟩, ?_, ?_, hev⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨⟨b, i, j⟩, -, rfl⟩ := hg
    cases b <;> simp
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hs

lemma ev2 (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin 2 → Bool) → Bool)
    (g : Bool → Bool → Bool)
    (hf : ∀ x : Fin 2 → Bool, f x = g (x 0) (x 1))
    (h : ∀ a0 a1 : Bool, C.eval [a0, a1] = g a0 a1) :
    ∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1] := by simp [List.ofFn_succ]
  rw [hx, hf]
  exact h _ _

lemma ev3 (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin 3 → Bool) → Bool)
    (g : Bool → Bool → Bool → Bool)
    (hf : ∀ x : Fin 3 → Bool, f x = g (x 0) (x 1) (x 2))
    (h : ∀ a0 a1 a2 : Bool, C.eval [a0, a1, a2] = g a0 a1 a2) :
    ∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2] := by simp [List.ofFn_succ]
  rw [hx, hf]
  exact h _ _ _

lemma ev4 (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin 4 → Bool) → Bool)
    (g : Bool → Bool → Bool → Bool → Bool)
    (hf : ∀ x : Fin 4 → Bool, f x = g (x 0) (x 1) (x 2) (x 3))
    (h : ∀ a0 a1 a2 a3 : Bool, C.eval [a0, a1, a2, a3] = g a0 a1 a2 a3) :
    ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by simp [List.ofFn_succ]
  rw [hx, hf]
  exact h _ _ _ _

lemma ev5 (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin 5 → Bool) → Bool)
    (g : Bool → Bool → Bool → Bool → Bool → Bool)
    (hf : ∀ x : Fin 5 → Bool, f x = g (x 0) (x 1) (x 2) (x 3) (x 4))
    (h : ∀ a0 a1 a2 a3 a4 : Bool, C.eval [a0, a1, a2, a3, a4] = g a0 a1 a2 a3 a4) :
    ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by simp [List.ofFn_succ]
  rw [hx, hf]
  exact h _ _ _ _ _

lemma ev6 (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin 6 → Bool) → Bool)
    (g : Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (hf : ∀ x : Fin 6 → Bool, f x = g (x 0) (x 1) (x 2) (x 3) (x 4) (x 5))
    (h : ∀ a0 a1 a2 a3 a4 a5 : Bool, C.eval [a0, a1, a2, a3, a4, a5] = g a0 a1 a2 a3 a4 a5) :
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by simp [List.ofFn_succ]
  rw [hx, hf]
  exact h _ _ _ _ _ _

lemma ev7 (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin 7 → Bool) → Bool)
    (g : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (hf : ∀ x : Fin 7 → Bool, f x = g (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6))
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool, C.eval [a0, a1, a2, a3, a4, a5, a6] = g a0 a1 a2 a3 a4 a5 a6) :
    ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by simp [List.ofFn_succ]
  rw [hx, hf]
  exact h _ _ _ _ _ _ _

lemma c01 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine PEqualNP.Outside.L_meta_926.mk 2 1 _ [(true, 0, 1)] 2 (by decide)
    (PEqualNP.Outside.L_meta_926.ev2 _ _ (fun a0 a1 => (a0 && a1)) (fun _ => rfl) ?_)
  decide +kernel

lemma c02 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine PEqualNP.Outside.L_meta_926.mk 3 2 _ [(false, 1, 2), (true, 0, 3)] 4 (by decide)
    (PEqualNP.Outside.L_meta_926.ev3 _ _ (fun a0 a1 a2 => (a0 && a1) || (a0 && a2)) (fun _ => rfl) ?_)
  decide +kernel

lemma c03 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine PEqualNP.Outside.L_meta_926.mk 3 4 _ [(false, 2, 1), (true, 0, 3), (true, 1, 2), (false, 4, 5)] 6 (by decide)
    (PEqualNP.Outside.L_meta_926.ev3 _ _ (fun a0 a1 a2 => (a0 && a1) || (a0 && a2) || (a1 && a2)) (fun _ => rfl) ?_)
  decide +kernel

lemma c04 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine PEqualNP.Outside.L_meta_926.mk 4 3 _ [(true, 0, 1), (true, 2, 3), (false, 4, 5)] 6 (by decide)
    (PEqualNP.Outside.L_meta_926.ev4 _ _ (fun a0 a1 a2 a3 => (a0 && a1) || (a2 && a3)) (fun _ => rfl) ?_)
  decide +kernel

lemma c05 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine PEqualNP.Outside.L_meta_926.mk 4 3 _ [(false, 1, 2), (false, 4, 3), (true, 0, 5)] 6 (by decide)
    (PEqualNP.Outside.L_meta_926.ev4 _ _ (fun a0 a1 a2 a3 => (a0 && a1) || (a0 && a2) || (a0 && a3)) (fun _ => rfl) ?_)
  decide +kernel

lemma c06 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine PEqualNP.Outside.L_meta_926.mk 4 4 _ [(false, 2, 1), (true, 0, 4), (true, 1, 3), (false, 5, 6)] 7 (by decide)
    (PEqualNP.Outside.L_meta_926.ev4 _ _ (fun a0 a1 a2 a3 => (a0 && a1) || (a0 && a2) || (a1 && a3)) (fun _ => rfl) ?_)
  decide +kernel

lemma c07 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine PEqualNP.Outside.L_meta_926.mk 4 5 _ [(false, 2, 3), (false, 4, 1), (true, 0, 5), (true, 1, 2), (false, 6, 7)] 8 (by decide)
    (PEqualNP.Outside.L_meta_926.ev4 _ _ (fun a0 a1 a2 a3 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2)) (fun _ => rfl) ?_)
  decide +kernel

lemma c08 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 4 _ [(false, 1, 2), (true, 0, 5), (true, 3, 4), (false, 6, 7)] 8 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a3 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c09 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 4 _ [(false, 1, 2), (false, 5, 3), (false, 6, 4), (true, 0, 7)] 8 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 5 _ [(false, 2, 3), (false, 5, 1), (true, 0, 6), (true, 1, 4), (false, 7, 8)] 9 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 6 _ [(false, 2, 1), (true, 0, 5), (true, 1, 2), (true, 3, 4), (false, 6, 7), (false, 9, 8)] 10 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a1 && a2) || (a3 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 5 _ [(false, 0, 3), (true, 1, 5), (false, 0, 4), (true, 2, 7), (false, 6, 8)] 9 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 6 _ [(false, 2, 3), (false, 5, 4), (false, 6, 1), (true, 0, 7), (true, 1, 2), (false, 8, 9)] 10 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2)) (fun _ => rfl) ?_)
  decide +kernel

lemma c14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 6 _ [(false, 2, 3), (false, 5, 1), (true, 0, 6), (false, 2, 4), (true, 1, 8), (false, 7, 9)] 10 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 7 _ [(false, 2, 1), (false, 5, 3), (true, 0, 6), (true, 1, 2), (true, 3, 4), (false, 7, 8), (false, 10, 9)] 11 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a3 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 7 _ [(false, 2, 1), (true, 0, 5), (true, 1, 3), (false, 2, 3), (true, 4, 8), (false, 6, 7), (false, 10, 9)] 11 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a3 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 5 8 _ [(false, 2, 4), (false, 5, 1), (false, 6, 3), (true, 0, 7), (true, 1, 2), (true, 3, 4), (false, 8, 9), (false, 11, 10)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev5 _ _ (fun a0 a1 a2 a3 a4 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a3 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 5 _ [(true, 0, 1), (true, 2, 3), (true, 4, 5), (false, 6, 7), (false, 9, 8)] 10 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a2 && a3) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 5 _ [(false, 1, 2), (false, 6, 3), (true, 0, 7), (true, 4, 5), (false, 8, 9)] 10 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 6 _ [(false, 2, 1), (true, 0, 6), (true, 1, 3), (true, 4, 5), (false, 7, 8), (false, 10, 9)] 11 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 5 _ [(false, 1, 2), (true, 0, 6), (false, 4, 5), (true, 3, 8), (false, 7, 9)] 10 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a3 && a4) || (a3 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 5 _ [(false, 1, 2), (false, 6, 3), (false, 7, 4), (false, 8, 5), (true, 0, 9)] 10 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 6 _ [(false, 2, 3), (false, 6, 4), (false, 7, 1), (true, 0, 8), (true, 1, 5), (false, 9, 10)] 11 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 7 _ [(false, 2, 3), (false, 6, 1), (true, 0, 7), (true, 1, 2), (true, 4, 5), (false, 8, 9), (false, 11, 10)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 6 _ [(false, 2, 3), (false, 6, 1), (true, 0, 7), (false, 4, 5), (true, 1, 9), (false, 8, 10)] 11 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a1 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 7 _ [(false, 3, 1), (false, 6, 2), (true, 0, 7), (true, 1, 4), (true, 2, 5), (false, 8, 9), (false, 11, 10)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 6 _ [(false, 1, 2), (false, 6, 3), (true, 0, 7), (false, 1, 5), (true, 4, 9), (false, 8, 10)] 11 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 7 _ [(false, 2, 1), (true, 0, 6), (true, 1, 2), (false, 4, 5), (true, 3, 9), (false, 7, 8), (false, 11, 10)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a1 && a2) || (a3 && a4) || (a3 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 7 _ [(false, 1, 2), (true, 0, 6), (true, 2, 4), (false, 1, 5), (true, 3, 9), (false, 7, 8), (false, 11, 10)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a3 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 7 _ [(false, 2, 3), (false, 6, 4), (false, 7, 5), (false, 8, 1), (true, 0, 9), (true, 1, 2), (false, 10, 11)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5) || (a1 && a2)) (fun _ => rfl) ?_)
  decide +kernel

lemma c31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 7 _ [(false, 2, 3), (false, 6, 4), (false, 7, 1), (true, 0, 8), (false, 2, 5), (true, 1, 10), (false, 9, 11)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a1 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 8 _ [(false, 2, 4), (false, 6, 1), (false, 7, 3), (true, 0, 8), (true, 1, 2), (true, 3, 5), (false, 9, 10), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a3 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 8 _ [(false, 3, 1), (false, 6, 2), (true, 0, 7), (false, 4, 2), (true, 1, 9), (true, 2, 5), (false, 8, 10), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a2 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 8 _ [(false, 2, 1), (false, 6, 3), (true, 0, 7), (false, 2, 4), (true, 1, 9), (true, 3, 5), (false, 8, 10), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a3 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 8 _ [(false, 2, 1), (false, 6, 3), (true, 0, 7), (true, 1, 2), (false, 4, 5), (true, 3, 10), (false, 8, 9), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a3 && a4) || (a3 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 8 _ [(false, 2, 3), (false, 6, 1), (true, 0, 7), (true, 1, 2), (false, 3, 5), (true, 4, 10), (false, 8, 9), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a3 && a4) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 8 _ [(false, 2, 3), (false, 6, 1), (true, 0, 7), (true, 1, 4), (false, 2, 4), (true, 5, 10), (false, 8, 9), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 9 _ [(false, 2, 1), (true, 0, 6), (true, 1, 2), (false, 5, 4), (true, 3, 9), (true, 4, 5), (false, 7, 8), (false, 12, 10), (false, 13, 11)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a1 && a2) || (a3 && a4) || (a3 && a5) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 8 _ [(false, 1, 2), (true, 0, 6), (false, 1, 5), (true, 3, 8), (false, 2, 5), (true, 4, 10), (false, 7, 9), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a3 && a5) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 9 _ [(false, 2, 4), (false, 6, 5), (false, 7, 1), (false, 8, 3), (true, 0, 9), (true, 1, 2), (true, 3, 4), (false, 10, 11), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5) || (a1 && a2) || (a3 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 9 _ [(false, 2, 4), (false, 6, 1), (false, 7, 3), (true, 0, 8), (false, 2, 5), (true, 1, 10), (true, 3, 4), (false, 9, 11), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a1 && a5) || (a3 && a4)) (fun _ => rfl) ?_)
  decide +kernel

lemma c42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 6 9 _ [(false, 2, 3), (false, 6, 1), (true, 0, 7), (false, 2, 4), (true, 1, 9), (false, 3, 4), (true, 5, 11), (false, 8, 10), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev6 _ _ (fun a0 a1 a2 a3 a4 a5 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a3 && a5) || (a4 && a5)) (fun _ => rfl) ?_)
  decide +kernel

lemma c43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 6 _ [(false, 1, 2), (true, 0, 7), (true, 3, 4), (true, 5, 6), (false, 8, 9), (false, 11, 10)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a3 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 6 _ [(false, 1, 2), (false, 7, 3), (false, 8, 4), (true, 0, 9), (true, 5, 6), (false, 10, 11)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 7 _ [(false, 2, 3), (false, 7, 1), (true, 0, 8), (true, 1, 4), (true, 5, 6), (false, 9, 10), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 6 _ [(false, 1, 2), (false, 7, 3), (true, 0, 8), (false, 5, 6), (true, 4, 10), (false, 9, 11)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a4 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 1), (true, 0, 7), (true, 1, 2), (true, 3, 4), (true, 5, 6), (false, 8, 9), (false, 12, 10), (false, 13, 11)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a1 && a2) || (a3 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 7 _ [(false, 0, 3), (true, 1, 7), (false, 0, 4), (true, 2, 9), (true, 5, 6), (false, 8, 10), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 7 _ [(false, 2, 1), (true, 0, 7), (true, 1, 3), (false, 5, 6), (true, 4, 10), (false, 8, 9), (false, 12, 11)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a4 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 6 _ [(false, 1, 2), (false, 7, 3), (false, 8, 4), (false, 9, 5), (false, 10, 6), (true, 0, 11)] 12 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5) || (a0 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 7 _ [(false, 2, 3), (false, 7, 4), (false, 8, 5), (false, 9, 1), (true, 0, 10), (true, 1, 6), (false, 11, 12)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5) || (a1 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 3), (false, 7, 4), (false, 8, 1), (true, 0, 9), (true, 1, 2), (true, 5, 6), (false, 10, 11), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 7 _ [(false, 2, 3), (false, 7, 4), (false, 8, 1), (true, 0, 9), (false, 5, 6), (true, 1, 11), (false, 10, 12)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a5) || (a1 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 3, 4), (false, 7, 1), (false, 8, 2), (true, 0, 9), (true, 1, 5), (true, 2, 6), (false, 10, 11), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a5) || (a2 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 7 _ [(false, 1, 2), (false, 7, 3), (false, 8, 4), (true, 0, 9), (false, 1, 6), (true, 5, 11), (false, 10, 12)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a5) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 3), (false, 7, 1), (true, 0, 8), (false, 2, 4), (true, 1, 10), (true, 5, 6), (false, 9, 11), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 1), (false, 7, 3), (true, 0, 8), (true, 1, 2), (true, 3, 4), (true, 5, 6), (false, 9, 10), (false, 13, 11), (false, 14, 12)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a3 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 3), (false, 7, 1), (true, 0, 8), (true, 1, 2), (false, 5, 6), (true, 4, 11), (false, 9, 10), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a4 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 3, 1), (false, 7, 2), (true, 0, 8), (false, 4, 5), (true, 1, 10), (true, 2, 6), (false, 9, 11), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a1 && a5) || (a2 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 0, 4), (true, 1, 7), (false, 0, 5), (true, 2, 9), (false, 0, 6), (true, 3, 11), (false, 8, 10), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5) || (a3 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 1, 3), (false, 7, 2), (true, 0, 8), (true, 2, 5), (false, 1, 6), (true, 4, 11), (false, 9, 10), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 7 _ [(false, 1, 2), (false, 7, 3), (true, 0, 8), (false, 1, 5), (false, 10, 6), (true, 4, 11), (false, 9, 12)] 13 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a4 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 3), (false, 7, 1), (true, 0, 8), (true, 1, 4), (false, 4, 6), (true, 5, 11), (false, 9, 10), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a4 && a5) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 1, 2), (false, 7, 3), (true, 0, 8), (false, 6, 5), (true, 4, 10), (true, 5, 6), (false, 9, 11), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a4 && a5) || (a4 && a6) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 1), (true, 0, 7), (true, 1, 2), (false, 5, 4), (true, 3, 10), (true, 4, 6), (false, 8, 9), (false, 13, 11), (false, 14, 12)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a1 && a2) || (a3 && a4) || (a3 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 1), (true, 0, 7), (true, 1, 3), (false, 2, 3), (true, 4, 10), (true, 5, 6), (false, 8, 9), (false, 13, 11), (false, 14, 12)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a3 && a4) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 1, 2), (true, 0, 7), (false, 1, 5), (true, 3, 9), (false, 2, 6), (true, 4, 11), (false, 8, 10), (false, 13, 12)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a3 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 3), (false, 7, 4), (false, 8, 5), (false, 9, 6), (false, 10, 1), (true, 0, 11), (true, 1, 2), (false, 12, 13)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5) || (a0 && a6) || (a1 && a2)) (fun _ => rfl) ?_)
  decide +kernel

lemma c69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 3), (false, 7, 4), (false, 8, 5), (false, 9, 1), (true, 0, 10), (false, 2, 6), (true, 1, 12), (false, 11, 13)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5) || (a1 && a2) || (a1 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 4), (false, 7, 5), (false, 8, 1), (false, 9, 3), (true, 0, 10), (true, 1, 2), (true, 3, 6), (false, 11, 12), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a0 && a5) || (a1 && a2) || (a3 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 8 _ [(false, 2, 3), (false, 7, 4), (false, 8, 1), (true, 0, 9), (false, 2, 5), (false, 11, 6), (true, 1, 12), (false, 10, 13)] 14 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a1 && a5) || (a1 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 3, 4), (false, 7, 1), (false, 8, 2), (true, 0, 9), (false, 5, 2), (true, 1, 11), (true, 2, 6), (false, 10, 12), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a1 && a5) || (a2 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 4), (false, 7, 1), (false, 8, 3), (true, 0, 9), (false, 2, 5), (true, 1, 11), (true, 3, 6), (false, 10, 12), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a1 && a5) || (a3 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 3), (false, 7, 4), (false, 8, 1), (true, 0, 9), (false, 2, 5), (true, 1, 11), (true, 5, 6), (false, 10, 12), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a1 && a5) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 4), (false, 7, 1), (false, 8, 3), (true, 0, 9), (true, 1, 2), (false, 5, 6), (true, 3, 12), (false, 10, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a3 && a5) || (a3 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 3), (false, 7, 4), (false, 8, 1), (true, 0, 9), (true, 1, 2), (false, 3, 6), (true, 5, 12), (false, 10, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a2) || (a3 && a5) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 3), (false, 7, 4), (false, 8, 1), (true, 0, 9), (false, 6, 5), (true, 1, 11), (true, 5, 6), (false, 10, 12), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a5) || (a1 && a6) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 3), (false, 7, 4), (false, 8, 1), (true, 0, 9), (true, 1, 5), (false, 2, 5), (true, 6, 12), (false, 10, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a5) || (a2 && a6) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 0, 4), (false, 7, 2), (true, 1, 8), (false, 0, 5), (true, 2, 10), (false, 0, 6), (true, 3, 12), (false, 9, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a2 && a5) || (a3 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 1), (false, 7, 3), (true, 0, 8), (false, 2, 4), (true, 1, 10), (false, 5, 6), (true, 3, 12), (false, 9, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a3 && a5) || (a3 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 3), (false, 7, 1), (true, 0, 8), (false, 2, 4), (true, 1, 10), (false, 3, 6), (true, 5, 12), (false, 9, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a1 && a4) || (a3 && a5) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 3), (false, 7, 1), (true, 0, 8), (true, 1, 2), (false, 3, 5), (false, 11, 6), (true, 4, 12), (false, 9, 10), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a2) || (a3 && a4) || (a4 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 2, 3), (false, 7, 1), (true, 0, 8), (false, 4, 5), (true, 1, 10), (false, 2, 4), (true, 6, 12), (false, 9, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a1 && a5) || (a2 && a6) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 1, 3), (false, 7, 2), (true, 0, 8), (true, 2, 5), (false, 1, 5), (false, 11, 6), (true, 4, 12), (false, 9, 10), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5) || (a4 && a5) || (a4 && a6)) (fun _ => rfl) ?_)
  decide +kernel

lemma c85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine PEqualNP.Outside.L_meta_926.mk 7 9 _ [(false, 1, 2), (false, 7, 3), (true, 0, 8), (false, 1, 6), (true, 4, 10), (false, 2, 6), (true, 5, 12), (false, 9, 11), (false, 14, 13)] 15 (by decide)
    (PEqualNP.Outside.L_meta_926.ev7 _ _ (fun a0 a1 a2 a3 a4 a5 a6 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5) || (a4 && a6) || (a5 && a6)) (fun _ => rfl) ?_)
  decide +kernel

end PEqualNP.Outside.L_meta_926

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  exact ⟨PEqualNP.Outside.L_meta_926.c01,
    PEqualNP.Outside.L_meta_926.c02,
    PEqualNP.Outside.L_meta_926.c03,
    PEqualNP.Outside.L_meta_926.c04,
    PEqualNP.Outside.L_meta_926.c05,
    PEqualNP.Outside.L_meta_926.c06,
    PEqualNP.Outside.L_meta_926.c07,
    PEqualNP.Outside.L_meta_926.c08,
    PEqualNP.Outside.L_meta_926.c09,
    PEqualNP.Outside.L_meta_926.c10,
    PEqualNP.Outside.L_meta_926.c11,
    PEqualNP.Outside.L_meta_926.c12,
    PEqualNP.Outside.L_meta_926.c13,
    PEqualNP.Outside.L_meta_926.c14,
    PEqualNP.Outside.L_meta_926.c15,
    PEqualNP.Outside.L_meta_926.c16,
    PEqualNP.Outside.L_meta_926.c17,
    PEqualNP.Outside.L_meta_926.c18,
    PEqualNP.Outside.L_meta_926.c19,
    PEqualNP.Outside.L_meta_926.c20,
    PEqualNP.Outside.L_meta_926.c21,
    PEqualNP.Outside.L_meta_926.c22,
    PEqualNP.Outside.L_meta_926.c23,
    PEqualNP.Outside.L_meta_926.c24,
    PEqualNP.Outside.L_meta_926.c25,
    PEqualNP.Outside.L_meta_926.c26,
    PEqualNP.Outside.L_meta_926.c27,
    PEqualNP.Outside.L_meta_926.c28,
    PEqualNP.Outside.L_meta_926.c29,
    PEqualNP.Outside.L_meta_926.c30,
    PEqualNP.Outside.L_meta_926.c31,
    PEqualNP.Outside.L_meta_926.c32,
    PEqualNP.Outside.L_meta_926.c33,
    PEqualNP.Outside.L_meta_926.c34,
    PEqualNP.Outside.L_meta_926.c35,
    PEqualNP.Outside.L_meta_926.c36,
    PEqualNP.Outside.L_meta_926.c37,
    PEqualNP.Outside.L_meta_926.c38,
    PEqualNP.Outside.L_meta_926.c39,
    PEqualNP.Outside.L_meta_926.c40,
    PEqualNP.Outside.L_meta_926.c41,
    PEqualNP.Outside.L_meta_926.c42,
    PEqualNP.Outside.L_meta_926.c43,
    PEqualNP.Outside.L_meta_926.c44,
    PEqualNP.Outside.L_meta_926.c45,
    PEqualNP.Outside.L_meta_926.c46,
    PEqualNP.Outside.L_meta_926.c47,
    PEqualNP.Outside.L_meta_926.c48,
    PEqualNP.Outside.L_meta_926.c49,
    PEqualNP.Outside.L_meta_926.c50,
    PEqualNP.Outside.L_meta_926.c51,
    PEqualNP.Outside.L_meta_926.c52,
    PEqualNP.Outside.L_meta_926.c53,
    PEqualNP.Outside.L_meta_926.c54,
    PEqualNP.Outside.L_meta_926.c55,
    PEqualNP.Outside.L_meta_926.c56,
    PEqualNP.Outside.L_meta_926.c57,
    PEqualNP.Outside.L_meta_926.c58,
    PEqualNP.Outside.L_meta_926.c59,
    PEqualNP.Outside.L_meta_926.c60,
    PEqualNP.Outside.L_meta_926.c61,
    PEqualNP.Outside.L_meta_926.c62,
    PEqualNP.Outside.L_meta_926.c63,
    PEqualNP.Outside.L_meta_926.c64,
    PEqualNP.Outside.L_meta_926.c65,
    PEqualNP.Outside.L_meta_926.c66,
    PEqualNP.Outside.L_meta_926.c67,
    PEqualNP.Outside.L_meta_926.c68,
    PEqualNP.Outside.L_meta_926.c69,
    PEqualNP.Outside.L_meta_926.c70,
    PEqualNP.Outside.L_meta_926.c71,
    PEqualNP.Outside.L_meta_926.c72,
    PEqualNP.Outside.L_meta_926.c73,
    PEqualNP.Outside.L_meta_926.c74,
    PEqualNP.Outside.L_meta_926.c75,
    PEqualNP.Outside.L_meta_926.c76,
    PEqualNP.Outside.L_meta_926.c77,
    PEqualNP.Outside.L_meta_926.c78,
    PEqualNP.Outside.L_meta_926.c79,
    PEqualNP.Outside.L_meta_926.c80,
    PEqualNP.Outside.L_meta_926.c81,
    PEqualNP.Outside.L_meta_926.c82,
    PEqualNP.Outside.L_meta_926.c83,
    PEqualNP.Outside.L_meta_926.c84,
    PEqualNP.Outside.L_meta_926.c85⟩
