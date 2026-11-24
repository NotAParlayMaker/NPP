import Mathlib.Data.List.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_612_3
    (coverFromAnd : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card ≤ (C.gates.filter (fun g => match g.op with
          | .and => true
          | _ => false)).length)
    (edgesFromOr : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      G.edgeSet.ncard ≤ (C.gates.filter (fun g => match g.op with
        | .or => true
        | _ => false)).length + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro n t G C hedge hfour _ hmin hmono heval
  obtain ⟨S, hS, hAnd⟩ := coverFromAnd n G C hedge hfour hmono heval
  have hOr := edgesFromOr n G C hedge hfour hmono heval
  have hCover := hmin S hS
  have partition : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
      (gs.filter (fun g => match g.op with | .and => true | _ => false)).length +
      (gs.filter (fun g => match g.op with | .or => true | _ => false)).length =
      gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro hg
      have ht : ∀ a ∈ gs, a.op = .and ∨ a.op = .or := by
        intro a ha
        exact hg a (List.mem_cons_of_mem g ha)
      have hi := ih ht
      rcases hg g (List.mem_cons_self) with hop | hop
      · simp [List.filter_cons, hop]
        omega
      · simp [List.filter_cons, hop]
        omega
  have hp := partition C.gates (by
    intro g hg
    have h := (hmono g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h)
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
