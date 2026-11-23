import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755_aux

def E (i j : Fin 6) : Bool :=
  (i.val == 0 && (j.val == 1 || j.val == 2 || j.val == 3)) ||
  (j.val == 0 && (i.val == 1 || i.val == 2 || i.val == 3)) ||
  (i.val == 4 && j.val == 5) || (i.val == 5 && j.val == 4)

def G : SimpleGraph (Fin 6) where
  Adj i j := E i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (E i j = true))

lemma hub : ∀ x u v : Fin 6, G.Adj x u → G.Adj x v → u ≠ v → x = 0 := by
  show ∀ x u v : Fin 6, E x u = true → E x v = true → u ≠ v → x = 0
  decide

lemma acyc : G.IsAcyclic := by
  intro z w cyc
  have onCycle (x : Fin 6) (hx : x ∈ w.support) : x = 0 := by
    let q := w.rotate x hx
    have hq : q.IsCycle := cyc.rotate hx
    exact hub x _ _ (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm hq.snd_ne_penultimate
  have h0 := onCycle z w.start_mem_support
  have h1 := onCycle w.snd (w.getVert_mem_support 1)
  exact (w.adj_snd cyc.not_nil).ne (h0.trans h1.symm)

lemma edge : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, by decide⟩

lemma cover : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  show ∀ T : Finset (Fin 6), (∀ i j : Fin 6, E i j = true → i ∈ T ∨ j ∈ T) → 2 ≤ T.card
  decide

lemma card : G.edgeFinset.card = 4 := by decide

lemma feq : (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) =
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) := by
  funext x
  have : ∀ y : Fin 6 → Bool, decide (∃ i j : Fin 6, E i j = true ∧ y i = true ∧ y j = true) =
      ((y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 4 && y 5)) := by decide
  exact this x

end PEqualNP.Outside.L_meta_755_aux

open PEqualNP.Outside.L_meta_755_aux in
theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [← feq]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 2 s G acyc edge cover h
    rw [card] at this
    omega
  · intro hs
    have h := PEqualNP.MetaComplexity.L105 6 G {0, 4} edge (by
      show ∀ i j : Fin 6, E i j = true → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6))
      decide)
    rw [card] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    exact ⟨C, h1, by simp at h2; omega, h3⟩
