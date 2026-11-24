import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Restriction to edge inputs and the independent neighbor sets preserves
-- both the unique rectangle and its positive vertex label.
theorem PEqualNP.Outside.R_meta_4123_823
    (transfer : ∀ (n t : Nat) (G H : SimpleGraph (Fin n)) (z : Fin n) (f : (Fin n → Bool) → Bool),
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → H ≤ G → (∀ x, f x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      (∃ A B p, IsLiteralPartition n f (t+1) A B p (fun _ => true)) → ∃ (X Y : Fin (t+1) → Fin n → Fin n → Prop) (lab : Fin (t+1) → Fin n),
        ∀ u v a b, H.Adj u v → a=b ∨ H.Adj a b →
        (∃! j, X j u v ∧ Y j a b) ∧ ∀ j, X j u v → Y j a b →
          (lab j = u ∨ lab j = v) ∧ ¬((H.Adj a (lab j) ∨ H.Adj b (lab j)) ∧ lab j ≠ a ∧ lab j ≠ b))
    (remaining : ∀ (n t : Nat) (G H : SimpleGraph (Fin n)) (z : Fin n) (f : (Fin n → Bool) → Bool),
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → H = G.deleteEdges (G.incidenceSet z) →
      (∀ x, f x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) → HasCircuitSize n f t →
      ¬ (∃ A B p, IsLiteralPartition n f (t+1) A B p (fun _ => true)) → ∃ (X Y : Fin (t+1) → Fin n → Fin n → Prop) (lab : Fin (t+1) → Fin n),
        ∀ u v a b, H.Adj u v → a=b ∨ H.Adj a b →
        (∃! j, X j u v ∧ Y j a b) ∧ ∀ j, X j u v → Y j a b →
          (lab j = u ∨ lab j = v) ∧ ¬((H.Adj a (lab j) ∨ H.Adj b (lab j)) ∧ lab j ≠ a ∧ lab j ≠ b)) :
    ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool), (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) → (x3.neighborSet x5).ncard = (3 : ℕ) → (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → x4 = x3.deleteEdges (x3.incidenceSet x5) → (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 → ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x15 : Fin (x2 + (1 : ℕ)) → Fin x1), ∀ (x16 x17 x18 x19 : Fin x1), x4.Adj x16 x17 → x18 = x19 ∨ x4.Adj x18 x19 → (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧ ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 → (x15 x22 = x16 ∨ x15 x22 = x17) ∧ ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19) := by
  classical
  intro n t G H z f degrees deg girth deleted computes size
  by_cases cert : (∃ A B p, IsLiteralPartition n f (t+1) A B p (fun _ => true))
  · exact transfer n t G H z f girth (deleted ▸ G.deleteEdges_le _) computes cert
  · exact remaining n t G H z f degrees deg girth deleted computes size cert
