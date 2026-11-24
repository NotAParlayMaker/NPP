import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The output-gate cut for `L-meta-606`: the linear bound for all monotone
circuits computing an edge function follows from the bound for circuits whose
output wire is produced by an AND gate together with the bound for circuits
whose output wire is produced by an OR gate. A circuit whose output wire is
an input wire computes a projection, and one whose output wire does not exist
computes the constant `false` function; neither is the edge function of a
graph with an edge, and an edgeless graph satisfies the bound trivially. -/
theorem PEqualNP.Outside.R_meta_606_18 :
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D =
        (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[D.output - n]? = some g ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      G.edgeFinset.card ≤ c * (D.size + 1)) →
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D =
        (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[D.output - n]? = some g ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      G.edgeFinset.card ≤ c * (D.size + 1)) →
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D =
        (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ c * (D.size + 1) := by
  rintro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
  refine ⟨max c₁ c₂, ?_⟩
  intro n G _ hgirth D hmono hfun
  have hsize : D.size = D.gates.length := rfl
  -- Folding gates only appends wire values: the length grows by the number of
  -- gates, and wires already present are never overwritten.
  have wires_length : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
        List.length_nil]
      omega
  have wires_getD : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
        = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i hi; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons,
        ih _ i (by simp only [List.length_append, List.length_singleton]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
  have eval_of_lt : ∀ (y : List Bool) (i : ℕ), i < y.length →
      (D.wires y).getD i false = y.getD i false :=
    fun y i hi => wires_getD D.gates y i hi
  have wires_len : ∀ y : List Bool, (D.wires y).length = y.length + D.gates.length :=
    fun y => wires_length D.gates y
  by_cases hA : D.output < n
  · -- The output wire is an input wire: `circuitFun n D` is a projection,
    -- which no edge function equals.
    exfalso
    have hcf : ∀ x : Fin n → Bool, circuitFun n D x = x ⟨D.output, hA⟩ := by
      intro x
      show (D.wires (List.ofFn x)).getD D.output false = x ⟨D.output, hA⟩
      rw [eval_of_lt _ _ (by rw [List.length_ofFn]; exact hA),
        List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hA]
    have hdec : decide (∃ i j : Fin n, G.Adj i j ∧ decide (i = ⟨D.output, hA⟩) = true ∧
        decide (j = ⟨D.output, hA⟩) = true) = true := by
      have h1 : circuitFun n D (fun j => decide (j = ⟨D.output, hA⟩)) = true := by
        rw [hcf]
        show decide ((⟨D.output, hA⟩ : Fin n) = ⟨D.output, hA⟩) = true
        exact decide_eq_true rfl
      have h2 := congrFun hfun (fun j => decide (j = ⟨D.output, hA⟩))
      rw [h1] at h2
      exact h2.symm
    obtain ⟨i, j, hadj, hi, hj⟩ := of_decide_eq_true hdec
    have hi' : i = ⟨D.output, hA⟩ := of_decide_eq_true hi
    have hj' : j = ⟨D.output, hA⟩ := of_decide_eq_true hj
    subst hi'
    subst hj'
    exact absurd rfl (G.ne_of_adj hadj)
  · by_cases hB : n + D.size ≤ D.output
    · -- The output wire does not exist: `circuitFun n D` is constantly `false`.
      have hcf : ∀ x : Fin n → Bool, circuitFun n D x = false := by
        intro x
        show (D.wires (List.ofFn x)).getD D.output false = false
        refine List.getD_eq_default _ _ ?_
        have hlen : (D.wires (List.ofFn x)).length = n + D.size := by
          rw [wires_len, List.length_ofFn, ← hsize]
        omega
      by_cases hedge : ∃ i j : Fin n, G.Adj i j
      · obtain ⟨i, j, hij⟩ := hedge
        exfalso
        have hx := congrFun hfun (fun v => decide (v = i ∨ v = j))
        simp only [hcf] at hx
        have hdec : decide (∃ a b : Fin n, G.Adj a b ∧ decide (a = i ∨ a = j) = true ∧
            decide (b = i ∨ b = j) = true) = true :=
          decide_eq_true ⟨i, j, hij, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
        have hft : (false : Bool) = true := hx.trans hdec
        simp at hft
      · -- No edges: the bound is trivial.
        have hempty : G.edgeFinset = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro s hs
          rw [SimpleGraph.mem_edgeFinset] at hs
          exact Sym2.inductionOn (f := fun s => s ∈ G.edgeSet → False) s
            (fun a b hab => hedge ⟨a, b, (SimpleGraph.mem_edgeSet G).mp hab⟩) hs
        rw [hempty]
        simp
    · -- The output wire is produced by a gate, which is an AND or an OR gate.
      have hnle : n ≤ D.output := by omega
      have hlt : D.output < n + D.size := by omega
      have hk : D.output - n < D.gates.length := by omega
      have hgmem : D.gates[D.output - n] ∈ D.gates := List.getElem_mem hk
      have hgop : (D.gates[D.output - n]).op = GateOp.and ∨
          (D.gates[D.output - n]).op = GateOp.or := by
        have h := (hmono _ hgmem).1
        simpa using h
      have hwit : D.gates[D.output - n]? = some (D.gates[D.output - n]) :=
        getElem?_pos D.gates (D.output - n) hk
      rcases hgop with hop | hop
      · exact (h₁ n G hgirth D hmono hfun ⟨_, hwit, hop⟩).trans
          (Nat.mul_le_mul_right _ (le_max_left c₁ c₂))
      · exact (h₂ n G hgirth D hmono hfun ⟨_, hwit, hop⟩).trans
          (Nat.mul_le_mul_right _ (le_max_right c₁ c₂))
