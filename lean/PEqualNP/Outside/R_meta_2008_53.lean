import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2008_53
 (geometry : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (uniq : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (L : Finset (Fin N)) (small : L.card ≤ q) (A : Finset (Fin (N+N)))
    (covers : ∀ p l, I p l → Fin.castAdd N p ∈ A ∨ Fin.natAdd N l ∈ A)
    (pbound : ∀ p, Fin.castAdd N p ∈ A → ∃ l ∈ L, I p l)
    (lbound : ∀ l, Fin.natAdd N l ∈ A → l ∉ L), (∀ p, Fin.castAdd N p ∈ A ↔ ∃ l ∈ L, I p l) ∧
    (∀ l, Fin.natAdd N l ∈ A ↔ l ∉ L))
 (switching : ∀ (M : ℕ) (C : Circuit), Monotone2 C → C.output < M+C.size → (∀ j (g : Gate), C.gates[j]? = some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a < b ∧ b < M+j) →
  let route := fun (s : ℕ → Bool) (A : ℕ → Finset (Fin M)) =>
 (∀ i : Fin M, A i.val={i}) ∧ ∀ j (g : Gate), C.gates[j]?=some g → ∀ a b : ℕ, g.inputs=[a,b] →
 A (M+j) = if g.op.eval [true,false] then A a ∪ A b else if s j then A b else A a
  (∀ s A, route s A → ∀ x : Fin M → Bool, C.eval (List.ofFn x) = true → ∃ i ∈ A C.output, x i = true) ∧
  (∀ x : Fin M → Bool, C.eval (List.ofFn x) = false → ∃ s A, route s A ∧ ∀ i ∈ A C.output, x i = false) ∧
  ∀ s A k B, route s A → route (Function.update s k (!(s k))) B →
     B C.output \ A C.output ⊆ B (M+k) \ A (M+k))
 (price : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
 (∀ l, Fintype.card {p // I p l} = q+1) → (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
 ∀ (L : Finset (Fin N)) (l : Fin N) (T : Finset (Fin (N+N))), l ∉ L →
 (∀ p, I p l → (∀ r ∈ L, ¬I p r) → Fin.castAdd N p ∈ T) → q+1 ≤ T.card + L.card)
 (bound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
  100 < q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
  (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C → C.output < N+N+C.size → (∀ j (g : Gate), C.gates[j]? = some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a < b ∧ b < (N+N)+j) →
  let route := fun (s : ℕ → Bool) (A : ℕ → Finset (Fin (N+N))) =>
 (∀ i : Fin (N+N), A i.val={i}) ∧ ∀ j (g : Gate), C.gates[j]?=some g → ∀ a b : ℕ, g.inputs=[a,b] →
 A (N+N+j) = if g.op.eval [true,false] then A a ∪ A b else if s j then A b else A a
  (∀ s A, route s A → ∀ p l, I p l → Fin.castAdd N p ∈ A C.output ∨ Fin.natAdd N l ∈ A C.output) →
  (∀ L : Finset (Fin N), L.card ≤ q → ∃ s A, route s A ∧
    (∀ p, Fin.castAdd N p ∈ A C.output ↔ ∃ l ∈ L, I p l) ∧ (∀ l, Fin.natAdd N l ∈ A C.output ↔ l ∉ L) ∧
    ∀ k B, route (Function.update s k (!(s k))) B → (∃ l ∉ L, Fin.natAdd N l ∉ B C.output) →
      q+1 ≤ (B (N+N+k) \ A (N+N+k)).card + L.card) →
  N*q ≤ 100*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by

  classical
  intro q N I inst C large count deg uniq mono valid shape yes no _ _ _
  obtain ⟨positive,negative,delta⟩ := switching (N+N) C mono valid shape
  let localRoute := fun (s : ℕ → Bool) (A : ℕ → Finset (Fin (N+N))) =>
   (∀ i : Fin (N+N), A i.val={i}) ∧ ∀ j (g : Gate), C.gates[j]?=some g → ∀ a b : ℕ, g.inputs=[a,b] →
   A (N+N+j) = if g.op.eval [true,false] then A a ∪ A b else if s j then A b else A a
  have cov (s : ℕ → Bool) (A : ℕ → Finset (Fin (N+N))) (route : localRoute s A) (p l : Fin N) (inc : I p l) :
      Fin.castAdd N p ∈ A C.output ∨ Fin.natAdd N l ∈ A C.output := by
    obtain ⟨i,hi,mem⟩ := positive s A route _ (yes p l inc)
    rcases of_decide_eq_true mem with rfl|rfl
    · exact Or.inl hi
    · exact Or.inr hi
  apply bound q N I C large count deg uniq mono valid shape cov
  intro L small
  let z : Fin (N+N) → Bool := Fin.addCases
    (fun p => decide (¬∃ l ∈ L, I p l)) (fun l => decide (l ∈ L))
  have left (p : Fin N) : z (Fin.castAdd N p) = decide (¬∃ l ∈ L, I p l) := Fin.addCases_left _
  have right (l : Fin N) : z (Fin.natAdd N l) = decide (l ∈ L) := Fin.addCases_right _
  have zsize : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q := by
    rw [Fintype.card_subtype]
    simpa only [right,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] using small
  have empty : ¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    rintro ⟨p,l,inc,op,ol⟩
    rw [left] at op
    rw [right] at ol
    exact of_decide_eq_true op ⟨l,of_decide_eq_true ol,inc⟩
  obtain ⟨s,A,route,off⟩ := negative z (no z zsize empty)
  obtain ⟨pCut,lCut⟩ := geometry q N I deg uniq L small (A C.output) (cov s A route) (by
    intro p hp; have eq := off _ hp; rw [left] at eq
    exact Classical.byContradiction (fun h => by simpa [h] using eq)) (by
    intro l hl; have eq := off _ hl; rw [right] at eq
    exact of_decide_eq_false eq)
  refine ⟨s,A,route,pCut,lCut,?_⟩
  intro k B alt lost
  obtain ⟨l,hl,missing⟩ := lost
  apply price q N I deg uniq L l _ hl
  intro p inc bare
  apply delta s A k B route alt
  refine Finset.mem_sdiff.mpr ⟨(cov _ B alt p l inc).resolve_right missing,?_⟩
  intro hp
  obtain ⟨r,hr,pr⟩ := (pCut p).mp hp
  exact bare r hr pr
