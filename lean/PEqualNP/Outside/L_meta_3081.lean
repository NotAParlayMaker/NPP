import Mathlib.Data.List.OfFn
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def reads (g : Gate) (i : Nat) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some i) ∨
  (g.op ≠ GateOp.not ∧ i ∈ g.inputs)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

theorem run_ext (gs : List Gate) (w : List Bool) :
    ∃ e, run gs w = w ++ e ∧ e.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
      obtain ⟨e, he, hl⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: e, ?_,
        by simpa using hl⟩
      change run gs (step w g) = _
      rw [he]
      simp [step, List.append_assoc]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨e, he, hl⟩ := run_ext gs w
  simp [he, hl]

theorem run_getD (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
    (run gs w).getD j false = w.getD j false := by
  obtain ⟨e, he, _⟩ := run_ext gs w
  rw [he]
  exact List.getD_append _ _ _ _ hj

theorem gate_eval_noRead (g : Gate) (i : Nat) (w v : List Bool)
    (no : ¬ reads g i)
    (agree : ∀ j, j ≠ i → w.getD j false = v.getD j false) :
    g.op.eval (g.inputs.map fun j => w.getD j false) =
      g.op.eval (g.inputs.map fun j => v.getD j false) := by
  by_cases hn : g.op = GateOp.not
  · rw [hn]
    cases ins : g.inputs with
    | nil => rfl
    | cons j rest =>
        have ne : j ≠ i := by
          intro eq
          apply no
          exact Or.inl ⟨hn, by simp [ins, eq]⟩
        simpa [GateOp.eval] using congrArg Bool.not (agree j ne)
  · have eq : g.inputs.map (fun j => w.getD j false) =
        g.inputs.map (fun j => v.getD j false) := by
      apply List.map_congr_left
      intro j hj
      apply agree j
      intro eq
      apply no
      exact Or.inr ⟨hn, eq ▸ hj⟩
    rw [eq]

theorem append_same_except (i : Nat) (w v extra : List Bool)
    (len : w.length = v.length)
    (agree : ∀ j, j ≠ i → w.getD j false = v.getD j false) :
    ∀ j, j ≠ i → (w ++ extra).getD j false = (v ++ extra).getD j false := by
  intro j ne
  by_cases low : j < w.length
  · rw [List.getD_append _ _ _ _ low,
      List.getD_append _ _ _ _ (by omega)]
    exact agree j ne
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), len]

theorem run_noRead (gs : List Gate) (i : Nat) : ∀ (w v : List Bool),
    (∀ g ∈ gs, ¬ reads g i) → w.length = v.length →
    (∀ j, j ≠ i → w.getD j false = v.getD j false) →
    ∀ j, j ≠ i → (run gs w).getD j false = (run gs v).getD j false := by
  induction gs with
  | nil => intro w v no len agree; exact agree
  | cons g gs ih =>
      intro w v no len agree
      have out := gate_eval_noRead g i w v (no g (by simp)) agree
      have next : ∀ j, j ≠ i → (step w g).getD j false = (step v g).getD j false := by
        unfold step
        rw [out]
        exact append_same_except i w v _ len agree
      exact ih (step w g) (step v g) (fun a ha => no a (by simp [ha]))
        (by simpa [step] using len) next

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def on (s : List Nat) : Fin 9 → Bool := fun j => s.contains j.val

theorem output_ne (C : Circuit) (computes : circuitFun 9 C = edgeF)
    (i : Nat) (hi : i < 9) (alone : edgeF (on [i]) = false) : C.output ≠ i := by
  intro eq
  have he := congrFun computes (on [i])
  change (run C.gates (List.ofFn (on [i]))).getD C.output false = edgeF (on [i]) at he
  rw [eq, run_getD C.gates _ i (by simpa using hi), alone] at he
  interval_cases i <;> simp_all [on]

theorem firstValue (g : Gate) (rest : List Gate) (out : Nat)
    (first : ∀ x : Fin 9 → Bool,
      ((Circuit.mk (g :: rest) out).wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (x : Fin 9 → Bool) :
    g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false) = (x 0 || x 2) := by
  have he := first x
  change (run rest (List.ofFn x ++
    [g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)])).getD 9 false = _ at he
  rw [run_getD _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)] at he
  simpa using he

theorem reread (C : Circuit)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (computes : circuitFun 9 C = edgeF)
    (i : Nat) (hi : i < 9) (alone : edgeF (on [i]) = false)
    (a b : Fin 9 → Bool)
    (agree : ∀ j, j ≠ i → (List.ofFn a).getD j false = (List.ofFn b).getD j false)
    (sameFirst : (a 0 || a 2) = (b 0 || b 2))
    (different : edgeF a ≠ edgeF b) : ∃ g ∈ C.gates.drop 1, reads g i := by
  have notOutput := output_ne C computes i hi alone
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil =>
    have impossible := first (on [0])
    change false = true at impossible
    contradiction
  | cons g rest =>
    by_contra absent
    have no : ∀ h ∈ rest, ¬ reads h i := by
      intro h hh hr
      exact absent ⟨h, by simpa using hh, hr⟩
    have eqValue :
        g.op.eval (g.inputs.map fun j => (List.ofFn a).getD j false) =
          g.op.eval (g.inputs.map fun j => (List.ofFn b).getD j false) := by
      rw [firstValue g rest out first a, firstValue g rest out first b]
      exact sameFirst
    have afterFirst : ∀ j, j ≠ i →
        (step (List.ofFn a) g).getD j false = (step (List.ofFn b) g).getD j false := by
      unfold step
      rw [eqValue]
      exact append_same_except i _ _ _ (by simp) agree
    have eqOutput := run_noRead rest i (step (List.ofFn a) g) (step (List.ofFn b) g)
      no (by simp [step]) afterFirst out notOutput
    have ea := congrFun computes a
    have eb := congrFun computes b
    change (run rest (step (List.ofFn a) g)).getD out false = edgeF a at ea
    change (run rest (step (List.ofFn b) g)).getD out false = edgeF b at eb
    exact different (ea.symm.trans (eqOutput.trans eb))

theorem solve (C : Circuit)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (computes : circuitFun 9 C = edgeF) :
    ∀ i : Nat, i = 0 ∨ i = 2 → ∃ g ∈ C.gates.drop 1, reads g i := by
  intro i which
  rcases which with rfl | rfl
  · apply reread C first computes 0 (by decide) (by decide +kernel)
      (on [2,4]) (on [0,2,4]) ?_ (by decide +kernel) (by decide +kernel)
    intro j hj
    by_cases small : j < 9
    · interval_cases j <;> simp_all [on]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  · apply reread C first computes 2 (by decide) (by decide +kernel)
      (on [0,3]) (on [0,2,3]) ?_ (by decide +kernel) (by decide +kernel)
    intro j hj
    by_cases small : j < 9
    · interval_cases j <;> simp_all [on]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3081

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 := PEqualNP.Outside.L_meta_3081.solve
