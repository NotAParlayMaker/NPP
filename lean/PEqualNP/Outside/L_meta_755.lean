import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755

open SimpleGraph

def adjB (a b : Fin 6) : Bool :=
  decide ((a.val, b.val) ∈ [(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (4, 5), (5, 4)])

abbrev G : SimpleGraph (Fin 6) where
  Adj a b := adjB a b = true
  symm := ⟨show ∀ a b : Fin 6, adjB a b = true → adjB b a = true by decide⟩
  loopless := ⟨show ∀ a : Fin 6, ¬ adjB a a = true by decide⟩

lemma f_eq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5))
    = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨h0, h1⟩) | ⟨h0, h1⟩)
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, h1⟩
    · exact ⟨0, 3, by decide, h0, h1⟩
    · exact ⟨4, 5, by decide, h0, h1⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp_all

lemma reach_closed {V : Type*} (H : SimpleGraph V) (P : V → Prop)
    (hc : ∀ a b, H.Adj a b → P a → P b) : ∀ {x y : V}, H.Walk x y → P x → P y := by
  intro x y p
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hx => ih (hc _ _ h hx)

set_option maxRecDepth 20000 in
lemma clos_leaf : ∀ v w a b : Fin 6, adjB v w = true → (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5) →
    adjB a b = true → ¬ ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) → a ≠ w → b ≠ w := by
  decide

set_option maxRecDepth 20000 in
lemma clos_root : ∀ v w a b : Fin 6, adjB v w = true → ¬ (w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5) →
    adjB a b = true → ¬ ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) → a = v → b = v := by
  decide

lemma G_acyclic : G.IsAcyclic := by
  rw [isAcyclic_iff_forall_isBridge]
  intro e
  refine Sym2.ind (fun v w => ?_) e
  intro he
  rw [mem_edgeSet] at he
  rw [isBridge_iff]
  rintro ⟨p⟩
  have key : ∀ a b, (G.deleteEdges {s(v, w)}).Adj a b →
      adjB a b = true ∧ ¬ ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) := by
    intro a b h
    rw [deleteEdges_adj] at h
    refine ⟨h.1, fun hab => h.2 ?_⟩
    rw [Set.mem_singleton_iff, Sym2.eq_iff]
    exact hab
  by_cases hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5
  · exact reach_closed _ (fun u => u ≠ w)
      (fun a b h => clos_leaf v w a b he hw (key a b h).1 (key a b h).2) p
      (G.ne_of_adj he) rfl
  · exact (G.ne_of_adj he) (reach_closed _ (fun u => u = v)
      (fun a b h => clos_root v w a b he hw (key a b h).1 (key a b h).2) p rfl).symm

lemma cover2 : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  rcases hT 0 1 (by decide) with h1 | h1 <;> rcases hT 4 5 (by decide) with h2 | h2 <;>
    exact Finset.one_lt_card.mpr ⟨_, h1, _, h2, by decide⟩

lemma edges4 : G.edgeFinset.card = 4 := by
  decide

end PEqualNP.Outside.L_meta_755

open PEqualNP.Outside.L_meta_755

theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [PEqualNP.Outside.L_meta_755.f_eq]
  constructor
  · intro h
    have hb := PEqualNP.MetaComplexity.L104 6 2 s PEqualNP.Outside.L_meta_755.G
      PEqualNP.Outside.L_meta_755.G_acyclic ⟨0, 1, by decide⟩ PEqualNP.Outside.L_meta_755.cover2 h
    rw [PEqualNP.Outside.L_meta_755.edges4] at hb
    omega
  · intro hs
    have hu := PEqualNP.MetaComplexity.L105 6 PEqualNP.Outside.L_meta_755.G {0, 4}
      ⟨0, 1, by decide⟩ (by decide)
    have hc : ({0, 4} : Finset (Fin 6)).card = 2 := by decide
    rw [PEqualNP.Outside.L_meta_755.edges4, hc] at hu
    obtain ⟨C, hC, hsz, hev⟩ := hu
    exact ⟨C, hC, by omega, hev⟩
