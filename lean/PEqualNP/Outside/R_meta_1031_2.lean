import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1031_2
    (hUpper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (S : Finset (Fin n)),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) →
      ∃ C : Circuit,
        (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        C.size + 1 ≤ G.edgeSet.ncard + S.card ∧
        ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
          (∃ c : Fin n,
            (∃ u v : Fin n, G.Adj u v ∧
              (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true) ∧
            ∀ u v : Fin n, G.Adj u v →
              (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true →
              u = c ∨ v = c) ∧
          (∀ (i : ℕ) (h : Gate), C.gates[i]? = some h → h.op = GateOp.and →
            ¬ Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h' : Gate),
              b = n + k ∧ C.gates[k]? = some h' ∧ a ∈ h'.inputs) (n + i) (n + t)))
    (hLower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (S : Finset (Fin n)) (D : Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → S.card ≤ T.card) →
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeSet.ncard + S.card ≤ D.size + 1) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  classical
  intro n G _ htri hcycle
  by_cases hedge : ∃ u v : Fin n, G.Adj u v
  · let P : ℕ → Prop := fun t => ∃ S : Finset (Fin n), S.card = t ∧
        ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S
    have hex : ∃ t, P t := by
      refine ⟨n, Finset.univ, by simp, ?_⟩
      intro u v huv
      exact Or.inl (Finset.mem_univ u)
    obtain ⟨S, hcard, hcover⟩ := Nat.find_spec hex
    have hmin : ∀ T : Finset (Fin n),
        (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → S.card ≤ T.card := by
      intro T hT
      rw [hcard]
      exact Nat.find_min' hex (show P T.card from ⟨T, rfl, hT⟩)
    obtain ⟨C, hmono, hfun, hsize, hown⟩ := hUpper n G S hedge hcover
    refine ⟨C, hmono, hfun, ?_, ?_⟩
    · intro D hDm hDf
      have hbound := hLower n G S D hedge htri hcycle hcover hmin hDm hDf
      omega
    · intro t g ht hop
      obtain ⟨⟨c, ⟨u, v, huv, hval⟩, hstar⟩, hno⟩ := hown t g ht hop
      refine ⟨c, ⟨u, v, huv, hval, ?_⟩, ?_⟩
      · intro i h hi hop' hpath
        exact False.elim (hno i h hi hop' hpath)
      · intro u' v' huv' hpair
        exact hstar u' v' huv' hpair.1
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro x
      change (List.ofFn x).getD n false = _
      have hlen : (List.ofFn x).length ≤ n := by simp
      rw [List.getD_eq_default _ _ hlen]
      have hfalse : ¬ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
        rintro ⟨i, j, hij, _, _⟩
        exact hedge ⟨i, j, hij⟩
      simp [hfalse]
    · intro D _ _
      simp [Circuit.size]
    · intro t g ht _
      simp at ht
