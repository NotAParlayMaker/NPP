import PEqualNP.MetaComplexity.Helpers.ForestElim

namespace PEqualNP.Outside.L_meta_12989_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers

def target : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def input (w : ℕ) (i : Fin 6) : Bool := w.testBit i.val

private theorem budget {f : (Fin 6 → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize 6 f s) (le : s ≤ t) :
    HasCircuitSize 6 f t := by
  obtain ⟨c, ok, size, comp⟩ := h
  exact ⟨c, ok, size.trans le, comp⟩

def f0 (x : Fin 6 → Bool) : Bool := target (Function.update x 4 false)
def f01 (x : Fin 6 → Bool) : Bool := f0 (Function.update x 2 true)
def f010 (x : Fin 6 → Bool) : Bool := f01 (Function.update x 5 false)
def f0100 (x : Fin 6 → Bool) : Bool := f010 (Function.update x 0 false)
private theorem bound0100 {s : ℕ} (hc : HasCircuitSize 6 f0100 s) : 1 ≤ s := by
  let D : Finset (Fin 6) := {1, 3}
  have dep : ∀ i ∈ D, ∃ x, f0100 (Function.update x i (!x i)) ≠ f0100 x := by
    intro i hi
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨input 8, by decide +kernel⟩
    · exact ⟨input 2, by decide +kernel⟩
  have h := PermInputs.dep_lower_set 6 f0100 D dep s hc
  have card : D.card = 2 := by decide +kernel
  omega

def f0101 (x : Fin 6 → Bool) : Bool := f010 (Function.update x 0 true)
private theorem bound0101 {s : ℕ} (hc : HasCircuitSize 6 f0101 s) : 1 ≤ s := by
  let D : Finset (Fin 6) := {1, 3}
  have dep : ∀ i ∈ D, ∃ x, f0101 (Function.update x i (!x i)) ≠ f0101 x := by
    intro i hi
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨input 0, by decide +kernel⟩
    · exact ⟨input 0, by decide +kernel⟩
  have h := PermInputs.dep_lower_set 6 f0101 D dep s hc
  have card : D.card = 2 := by decide +kernel
  omega

private theorem bound010 {s : ℕ} (hc : HasCircuitSize 6 f010 s) : 3 ≤ s := by
  have dep : ∃ x, f010 (Function.update x 0 (!x 0)) ≠ f010 x := ⟨input 2, by decide +kernel⟩
  have nc (b : Bool) : ∃ x y, f010 (Function.update x 0 b) ≠ f010 (Function.update y 0 b) := by
    cases b
    · exact ⟨input 10, input 0, by decide +kernel⟩
    · exact ⟨input 2, input 0, by decide +kernel⟩
  obtain ⟨b, u, le, h⟩ := PermInputs.gate_elim_at 5 f010 0 s dep nc hc
  cases b
  · have low := bound0100 h
    omega
  · have low := bound0101 h
    omega

private theorem bound01 {s : ℕ} (hc : HasCircuitSize 6 f01 s) : 4 ≤ s := by
  have dep : ∃ x, f01 (Function.update x 5 (!x 5)) ≠ f01 x := ⟨input 1, by decide +kernel⟩
  by_contra! small
  have h := Forest.one_gate_at 5 f01 5 false 2 dep
    ⟨input 3, input 0, by decide +kernel⟩ (budget hc (show s ≤ 3 by omega))
  have low := bound010 h
  omega

private theorem bound0 {s : ℕ} (hc : HasCircuitSize 6 f0 s) : 5 ≤ s := by
  have dep : ∃ x, f0 (Function.update x 2 (!x 2)) ≠ f0 x := ⟨input 10, by decide +kernel⟩
  by_contra! small
  have h := Forest.one_gate_at 5 f0 2 true 3 dep
    ⟨input 3, input 0, by decide +kernel⟩ (budget hc (show s ≤ 4 by omega))
  have low := bound01 h
  omega

def f1 (x : Fin 6 → Bool) : Bool := target (Function.update x 4 true)
def f10 (x : Fin 6 → Bool) : Bool := f1 (Function.update x 2 false)
private theorem bound10 {s : ℕ} (hc : HasCircuitSize 6 f10 s) : 3 ≤ s := by
  let D : Finset (Fin 6) := {0, 1, 3, 5}
  have dep : ∀ i ∈ D, ∃ x, f10 (Function.update x i (!x i)) ≠ f10 x := by
    intro i hi
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨input 2, by decide +kernel⟩
    · exact ⟨input 1, by decide +kernel⟩
    · exact ⟨input 1, by decide +kernel⟩
    · exact ⟨input 1, by decide +kernel⟩
  have h := PermInputs.dep_lower_set 6 f10 D dep s hc
  have card : D.card = 4 := by decide +kernel
  omega

def f11 (x : Fin 6 → Bool) : Bool := f1 (Function.update x 2 true)
private theorem bound11 {s : ℕ} (hc : HasCircuitSize 6 f11 s) : 3 ≤ s := by
  let D : Finset (Fin 6) := {0, 1, 3, 5}
  have dep : ∀ i ∈ D, ∃ x, f11 (Function.update x i (!x i)) ≠ f11 x := by
    intro i hi
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨input 8, by decide +kernel⟩
    · exact ⟨input 0, by decide +kernel⟩
    · exact ⟨input 1, by decide +kernel⟩
    · exact ⟨input 1, by decide +kernel⟩
  have h := PermInputs.dep_lower_set 6 f11 D dep s hc
  have card : D.card = 4 := by decide +kernel
  omega

private theorem bound1 {s : ℕ} (hc : HasCircuitSize 6 f1 s) : 5 ≤ s := by
  have dep : ∃ x, f1 (Function.update x 2 (!x 2)) ≠ f1 x := ⟨input 2, by decide +kernel⟩
  have nc (b : Bool) : ∃ x y, f1 (Function.update x 2 b) ≠ f1 (Function.update y 2 b) := by
    cases b
    · exact ⟨input 3, input 0, by decide +kernel⟩
    · exact ⟨input 2, input 0, by decide +kernel⟩
  obtain ⟨b, u, le, h⟩ := PermInputs.gate_elim_at 5 f1 2 s dep nc hc
  cases b
  · have low := bound10 h
    omega
  · have low := bound11 h
    omega

private theorem boundRoot {s : ℕ} (hc : HasCircuitSize 6 target s) : 7 ≤ s := by
  have dep : ∃ x, target (Function.update x 4 (!x 4)) ≠ target x := ⟨input 6, by decide +kernel⟩
  have nc (b : Bool) : ∃ x y, target (Function.update x 4 b) ≠ target (Function.update y 4 b) := by
    cases b
    · exact ⟨input 3, input 0, by decide +kernel⟩
    · exact ⟨input 3, input 0, by decide +kernel⟩
  obtain ⟨b, u, le, h⟩ := PermInputs.gate_elim_at 5 target 4 s dep nc hc
  cases b
  · have low := bound0 h
    omega
  · have low := bound1 h
    omega

def witness : Circuit := ⟨[⟨.or, [3, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [2, 1]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩
private theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem computes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12989_aux

open PEqualNP.Outside.L_meta_12989_aux in
theorem PEqualNP.Outside.L_meta_12989 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264042 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hc
  exact ⟨witness, mono, boundRoot hc, computes⟩
