import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_1031_4
    (synthesize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (S : Finset (Fin n)), CoverPromise.IsVertexCover G S →
      ∃ os : List (Fin n × List (Fin n)),
        (∀ p ∈ os, ∀ v ∈ p.2, G.Adj p.1 v) ∧
        let C := coverCircuitB n (os.map fun p => (p.1.val, p.2.map Fin.val))
        Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧
          C.size ≤ G.edgeSet.ncard + S.card - 1)
    (blocks : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (os : List (Fin n × List (Fin n))),
      (∀ p ∈ os, ∀ v ∈ p.2, G.Adj p.1 v) →
      let C := coverCircuitB n (os.map fun p => (p.1.val, p.2.map Fin.val))
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
        ∃ c v : Fin n, G.Adj c v ∧ gateVal n C j (pairInput c v) = true ∧
          (∀ x, gateVal n C j x = true → x c = true) ∧
          ∀ (i : ℕ) (h : Gate), C.gates[i]? = some h → h.op = GateOp.and →
            ¬ Relation.TransGen (fun a b : ℕ => a < b ∧
              ∃ (k : ℕ) (f : Gate), b = n + k ∧ C.gates[k]? = some f ∧ a ∈ f.inputs)
                (n + i) (n + j))
    (lower : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  classical
  intro n G _ _ hfour
  have model (D : Circuit) : Monotone2 D ↔
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) := by
    delta Monotone2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have computes (D : Circuit) : circuitFun n D = graphFun G ∅ ↔
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) := by
    rw [funext_iff]
    delta circuitFun graphFun
    simp
  let coverSize (t : ℕ) := ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t
  have ex : ∃ t, coverSize t :=
    ⟨Finset.univ.card, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec ex
  obtain ⟨os, hadj, hmono, hfun, hsize⟩ := synthesize n G S hS
  let C := coverCircuitB n (os.map fun p => (p.1.val, p.2.map Fin.val))
  refine ⟨C, (model C).1 hmono, (computes C).1 hfun, ?_, ?_⟩
  · intro D hD hDf
    by_cases edge : ∃ u v : Fin n, G.Adj u v
    · have k := lower n (Nat.find ex) G D edge
          (fun a b c d _ hac _ _ hbd _ hab hbc hcd hda =>
            (hfour a b c d hab hbc hcd hda).elim hac hbd)
          ⟨S, hS, hcard⟩
          (fun T hT => Nat.find_min' ex (show coverSize T.card from ⟨T, hT, rfl⟩))
          ((model D).2 hD) (fun x => by rw [hDf]; simp)
      change C.size ≤ G.edgeSet.ncard + S.card - 1 at hsize
      omega
    · have emptyCover : coverSize 0 :=
        ⟨∅, fun u v huv => False.elim (edge ⟨u, v, huv⟩), rfl⟩
      have hz := Nat.find_min' ex emptyCover
      have he : G.edgeSet = ∅ := by
        ext e
        induction e using Sym2.inductionOn with
        | _ u v => simp [show ¬ G.Adj u v from fun h => edge ⟨u, v, h⟩]
      change C.size ≤ G.edgeSet.ncard + S.card - 1 at hsize
      rw [he, Set.ncard_empty] at hsize
      omega
  · intro j g hj hg
    obtain ⟨c, v, hcv, active, centre, separate⟩ := blocks n G os hadj j g hj hg
    refine ⟨c, ⟨c, v, hcv, active, ?_⟩, ?_⟩
    · intro i h hi hop path
      exact (separate i h hi hop path).elim
    · intro a b _ h
      have hc := centre (pairInput a b) h.1
      change decide (c = a ∨ c = b) = true at hc
      exact (of_decide_eq_true hc).imp Eq.symm Eq.symm
