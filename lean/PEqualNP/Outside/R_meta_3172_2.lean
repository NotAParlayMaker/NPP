import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_3172_2
    (compile : ∀ (n : ℕ) (C : Circuit) (g : Gate) (bank : List (Bool ⊕ ℕ)) (S : Finset ℕ)
        (f : (Fin n → Bool) → Bool), FanInTwo C → FanInTwo ⟨[g],0⟩ →
        (∀ i, Sum.inr i ∈ bank → i < n+1) →
        (∀ i ∈ S, i < bank.length ∧ ∃ b, bank.getD i (Sum.inl false) = Sum.inl b) →
        (∃ x y, f x ≠ f y) →
        (∀ x : Fin n → Bool, let w := (Circuit.mk [g] 0).wires (List.ofFn x)
          C.eval (bank.map (Sum.elim id (fun i => w.getD i false))) = f x) →
        HasCircuitSize n f (1 + C.size - C.gates.countP (fun t =>
          (if t.op.eval [false,false] then t.inputs.take 1 else t.inputs).any (fun k => decide (k ∈ S)))))
    (full : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14)
    (minor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11)
    (sparse : ∀ a ∈ ([2,3,8] : List (Fin 9)), ∀ b ∈ ([2,3,8] : List (Fin 9)), a ≠ b → ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → C.gates.countP (fun g : Gate => ((if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun k => k == 0 || k == 9))) ≤ 2 → ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x a || x b]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  let F := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let H := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7))
  let counted := (fun g : Gate => ((if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun k => k == 0 || k == 9)))
  let ev (w : List Bool) := Sum.elim (id : Bool → Bool) (fun i => w.getD i false)
  let step (w : List Bool) (g : Gate) := (Circuit.mk [g] 0).wires w
  intro pins len _ small C fan cap
  rcases pins with _ | ⟨u,_|⟨v,tl⟩⟩ <;> simp only [List.length_nil,List.length_cons] at len
  · contradiction
  · contradiction
  have nil : tl = [] := List.length_eq_zero_iff.mp (by omega)
  subst tl
  let choices : List (Fin 9) := [2,3,8]
  have cv (j : ℕ) (hj : j ∈ [u,v]) : ∃ i ∈ choices, i.val = j := by
    rcases small j hj with rfl|rfl|rfl
    · exact ⟨2,by decide,rfl⟩
    · exact ⟨3,by decide,rfl⟩
    · exact ⟨8,by decide,rfl⟩
  obtain ⟨a,ha,rfl⟩ := cv u (by simp)
  obtain ⟨b,hb,rfl⟩ := cv v (by simp)
  by_contra! ok
  have correct (x : Fin 9 → Bool) :
      C.eval (List.ofFn x ++ [!x 0,x a || x b]) = F x := by
    have eq := Classical.not_not.mp (ok x)
    have atRaw (i : Fin 9) : (List.ofFn x ++ [!x 0]).getD i.val false = x i := by
      rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn ..
    change C.eval ((List.ofFn x ++ [!x 0]) ++ [((List.ofFn x ++ [!x 0]).getD a.val false || ((List.ofFn x ++ [!x 0]).getD b.val false || false))]) = F x at eq
    simpa only [atRaw,Bool.or_false,List.append_assoc,List.cons_append,List.nil_append] using eq
  by_cases same : a=b
  · subst b
    let bank : List (Sum Bool Nat) := (List.range 9).map Sum.inr ++ [.inr 9,.inr a.val]
    have bd : ∀ i, Sum.inr i ∈ bank → i < 10 := by
      intro i hi
      simp [bank] at hi
      rcases hi with hi|hi|hi <;> omega
    have source : ∀ (j : Fin 9) (x : Fin 9 → Bool),
        (((List.range 9).map Sum.inr ++ [.inr 9,.inr j.val] : List (Sum Bool Nat)).map
          (ev (step (List.ofFn x) ⟨.not,[0]⟩))) = List.ofFn x ++ [!x 0,x j || x j] := by decide +kernel
    have hc := compile 9 C ⟨.not,[0]⟩ bank ∅ F fan (by intro t ht; rcases List.mem_singleton.mp ht with rfl; simp) bd (by simp) ⟨fun _ => false,fun _ => true,by decide⟩ (fun x => (congrArg C.eval (source a x)).trans (correct x))
    obtain ⟨D,hD,hsize,he⟩ := hc
    exact full ⟨D,hD,by omega,he⟩
  · let p : Fin 9 → Fin 8 := ![0,0,1,2,6,7,4,5,3]
    let lift (y : Fin 8 → Bool) (i : Fin 9) := if i=0 then false else y (p i)
    let bank : List (Sum Bool Nat) := [.inl false,.inr 0,.inr 1,.inr 2,.inr 6,.inr 7,.inr 4,.inr 5,.inr 3,.inl true,.inr 8]
    have bd : ∀ i, Sum.inr i ∈ bank → i < 9 := by intro i hi; simp [bank] at hi; omega
    have fs : ∀ i ∈ ({0,9} : Finset ℕ), i < bank.length ∧ ∃ b, bank.getD i (Sum.inl false) = Sum.inl b := by intro i hi; simp at hi; rcases hi with rfl|rfl <;> decide
    have eqH : ∀ y, F (lift y) = H y := by decide +kernel
    have src : ∀ a ∈ choices, ∀ b ∈ choices, ∀ y : Fin 8 → Bool,
        bank.map (ev (step (List.ofFn y) ⟨.or,[(p a).val,(p b).val]⟩)) =
          List.ofFn (lift y) ++ [!(lift y 0),lift y a || lift y b] := by decide +kernel
    have hc := compile 8 C ⟨.or,[(p a).val,(p b).val]⟩ bank {0,9} H fan (by intro t ht; rcases List.mem_singleton.mp ht with rfl; simp) bd fs ⟨fun _ => false,fun _ => true,by decide⟩
      (fun y => (congrArg C.eval (src a ha b hb y)).trans ((correct _).trans (eqH y)))
    have rd : C.gates.countP counted = C.gates.countP (fun t =>
        (if t.op.eval [false,false] then t.inputs.take 1 else t.inputs).any (fun k => decide (k ∈ ({0,9} : Finset ℕ)))) := by
      apply List.countP_congr
      intro t _
      simp [counted]
    have smallCount : C.gates.countP counted ≤ 2 := by
      by_contra! big
      obtain ⟨D,hD,sz,he⟩ := hc
      exact minor ⟨D,hD,by omega,he⟩
    obtain ⟨x,hx⟩ := sparse a ha b hb same C fan cap smallCount
    exact hx (correct x)
