import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_757_aux

def rel (u v : Fin 6) : Bool :=
  decide ((u.val, v.val) ∈ ([(0, 1), (0, 2), (3, 4), (3, 5)] : List (ℕ × ℕ)) ∨
    (v.val, u.val) ∈ ([(0, 1), (0, 2), (3, 4), (3, 5)] : List (ℕ × ℕ)))

def graph : SimpleGraph (Fin 6) where
  Adj u v := rel u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (rel u v = true))

def lab (v : Fin 6) : ℕ := if v = 0 then 0 else if v = 3 then 1 else v.val + 2

theorem forest_two {V : Type*} (H : SimpleGraph V) (idv : V → ℕ)
    (hinj : Function.Injective idv)
    (hub : ∀ x u v, H.Adj x u → H.Adj x v → u ≠ v → idv x ≤ 1) : H.IsAcyclic := by
  classical
  intro z w cyc
  have onCycle (x : V) (hx : x ∈ w.support) : idv x ≤ 1 := by
    let q := w.rotate x hx
    have hq : q.IsCycle := cyc.rotate hx
    exact hub x _ _ (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm hq.snd_ne_penultimate
  have h0 := onCycle z w.start_mem_support
  have h1 := onCycle w.snd (w.getVert_mem_support 1)
  have h2 := onCycle w.penultimate (w.getVert_mem_support (w.length-1))
  have h01 : idv z ≠ idv w.snd := fun e => (w.adj_snd cyc.not_nil).ne (hinj e)
  have h02 : idv w.penultimate ≠ idv z := fun e => (w.adj_penultimate cyc.not_nil).ne (hinj e)
  have h12 : idv w.snd ≠ idv w.penultimate := fun e => cyc.snd_ne_penultimate (hinj e)
  omega

theorem acyc : graph.IsAcyclic :=
  forest_two graph lab (by decide) (by decide)

theorem hasEdge : ∃ i j : Fin 6, graph.Adj i j := ⟨0, 1, by decide⟩

theorem minCover : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, graph.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T h
  have h1 := h 0 1 (by decide)
  have h2 := h 3 4 (by decide)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    exact Finset.one_lt_card.mpr ⟨_, h1, _, h2, by decide⟩

theorem cover : ∀ i j : Fin 6, graph.Adj i j →
    i ∈ ({0, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 3} : Finset (Fin 6)) := by decide

theorem cardCover : ({0, 3} : Finset (Fin 6)).card = 2 := by decide

theorem cardEdges : graph.edgeFinset.card = 4 := by decide

theorem fnEq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨0, 1, by decide, h1, h2⟩
    · exact ⟨0, 2, by decide, h1, h2⟩
    · exact ⟨3, 4, by decide, h1, h2⟩
    · exact ⟨3, 5, by decide, h1, h2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have key : ∀ a b : Fin 6, graph.Adj a b →
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 3 ∧ b = 4) ∨ (a = 3 ∧ b = 5) ∨
        (b = 0 ∧ a = 1) ∨ (b = 0 ∧ a = 2) ∨ (b = 3 ∧ a = 4) ∨ (b = 3 ∧ a = 5) := by decide
    rcases key i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hi, hj]

end PEqualNP.Outside.L_meta_757_aux

open PEqualNP.Outside.L_meta_757_aux in
theorem PEqualNP.Outside.L_meta_757 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [fnEq]
  constructor
  · intro h
    have h1 := PEqualNP.MetaComplexity.L104 6 2 s graph acyc hasEdge minCover h
    rw [cardEdges] at h1
    omega
  · intro h
    obtain ⟨C, hC, hsz, hev⟩ := PEqualNP.MetaComplexity.L105 6 graph {0, 3} hasEdge cover
    rw [cardEdges, cardCover] at hsz
    exact ⟨C, hC, by omega, hev⟩
