import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_267

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

private def record : List Gate → List Bool → ℕ → Bool
  | [], _, _ => false
  | g :: _, w, 0 => w.getD (g.inputs.headD 0) false
  | g :: gs, w, j + 1 => record gs (step w g) j

private def common (x y z : List Bool) : Prop :=
  ∀ i, x.getD i false = false → y.getD i false = false → z.getD i false = false

private theorem andCase : ∀ a b c d e f : Bool,
    (a = false → b = false → c = false) → (d = false → e = false → f = false) →
    a = b → (a && d) = false → (b && e) = false → (c && f) = false := by
  intro a b
  cases a <;> cases b <;> decide

private theorem orCase : ∀ a b c d e f : Bool,
    (a = false → b = false → c = false) → (d = false → e = false → f = false) →
    (a || d) = false → (b || e) = false → (c || f) = false := by decide

private theorem commonGate (g : Gate) (x y z : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : common x y z)
    (matchFirst : g.op = GateOp.and → x.getD (g.inputs.headD 0) false =
      y.getD (g.inputs.headD 0) false) :
    gateBit x g = false → gateBit y g = false → gateBit z g = false := by
  obtain ⟨op,ins⟩ := g
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil => rcases hop with rfl | rfl <;> simp [gateBit, GateOp.eval]
  | cons i rest =>
    cases rest with
    | nil => rcases hop with rfl | rfl <;> simpa [gateBit, GateOp.eval] using h i
    | cons j rest =>
      cases rest with
      | nil =>
        rcases hop with rfl | rfl
        · simpa [gateBit, GateOp.eval] using andCase _ _ _ _ _ _ (h i) (h j) (matchFirst rfl)
        · simpa [gateBit, GateOp.eval] using orCase _ _ _ _ _ _ (h i) (h j)
      | cons b more => simp at hlen

private theorem lastRead (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases heq : i = w.length
  · subst i
    simp [List.getD]
  · rw [ite_eq_right heq]
    by_cases hlt : i < w.length
    · simp [List.getD, List.getElem?_append_left hlt]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem propagate (gs : List Gate) (x y z : List Bool)
    (hx : x.length = z.length) (hy : y.length = z.length) (h : common x y z)
    (mono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (sig : ∀ j g, gs[j]? = some g → g.op = GateOp.and → record gs x j = record gs y j) :
    common (gs.foldl step x) (gs.foldl step y) (gs.foldl step z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨ho,hl⟩ := mono g (by simp)
    have first := commonGate g x y z ho hl h (sig 0 g (by simp))
    apply ih (step x g) (step y g) (step z g) (by simp [step,hx]) (by simp [step,hy])
    · intro i
      simp only [step,lastRead,hx,hy]
      by_cases hi : i = z.length
      · simpa only [ite_eq_left hi] using first
      · simpa only [ite_eq_right hi] using h i
    · exact fun q hq => mono q (List.mem_cons_of_mem _ hq)
    · intro j q hj hq
      exact sig (j+1) q (by simpa using hj) hq

private theorem unionBase {n : ℕ} (x y : Fin n → Bool) :
    common (List.ofFn x) (List.ofFn y) (List.ofFn (fun i => x i || y i)) := by
  intro i
  by_cases hi : i < n
  · simp [List.getD,hi]
    exact fun hx hy => ⟨hx,hy⟩
  · simp [List.getD,hi]

theorem noNine267 {n : ℕ} (C : Circuit) (A : Finset ℕ) (mono : Monotone2 C)
    (budget : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (xs : Fin 9 → Fin n → Bool) (fail : ∀ p, C.eval (List.ofFn (xs p)) = false)
    (separate : ∀ p q, p ≠ q → C.eval (List.ofFn (fun i => xs p i || xs q i)) = true) :
    9 ≤ 2 ^ A.card := by
  let code (p : Fin 9) (i : A) := record C.gates (List.ofFn (xs p)) i.val
  have inj : Function.Injective code := by
    intro p q eq
    by_contra diff
    have m (g : Gate) (hg : g ∈ C.gates) :
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      simpa using mono g hg
    have h := propagate C.gates (List.ofFn (xs p)) (List.ofFn (xs q))
      (List.ofFn (fun i => xs p i || xs q i)) (by simp) (by simp) (unionBase _ _) m
      (fun j g hg ha => congrFun eq ⟨j, budget j g hg ha⟩)
    have z : C.eval (List.ofFn (fun i => xs p i || xs q i)) = false :=
      h C.output (fail p) (fail q)
    rw [separate p q diff] at z
    contradiction
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective code inj

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def dualTriangleInput (p : Fin 9) (i : Fin 6) : Bool :=
  decide (i.val = p.val / 3 ∨ i.val = 3 + p.val % 3)

private def dualTriangleHit (x : Fin 6 → Bool) : Prop :=
  ∃ u v : Fin 6, (u.val, v.val) ∈
    ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧
    x u = true ∧ x v = true

theorem finish267
    (hNine : ∀ (C : Circuit) (A : Finset ℕ), Monotone2 C →
      (∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) →
      ∀ xs : Fin 9 → Fin 6 → Bool, (∀ p, C.eval (List.ofFn (xs p)) = false) →
      (∀ p q, p ≠ q → C.eval (List.ofFn (fun i => xs p i || xs q i)) = true) →
      9 ≤ 2 ^ A.card) :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨hm, A, hcard, hcover⟩, hc⟩
  have emptyEdges : ∀ p, ¬ dualTriangleHit (dualTriangleInput p) := by
    unfold dualTriangleHit
    decide +kernel
  have joinedEdges : ∀ p q, p ≠ q →
      dualTriangleHit (fun i => dualTriangleInput p i || dualTriangleInput q i) := by
    unfold dualTriangleHit
    decide +kernel
  have h := hNine C A hm hcover dualTriangleInput
    (fun p => Bool.eq_false_iff.mpr (fun ht => emptyEdges p ((hc _).mp ht)))
    (fun p q hpq => (hc _).mpr (joinedEdges p q hpq))
  exact (by decide : ¬ (9 ≤ 2 ^ 3)) (h.trans (Nat.pow_le_pow_right (by decide) hcard))

end PEqualNP.Outside.L_meta_267

open PEqualNP.Outside.L_meta_267

theorem PEqualNP.Outside.L_meta_267 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  exact finish267 (noNine267 (n := 6))
