import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_759_aux

def ad (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(4,5),(5,4)])

def G : SimpleGraph (Fin 6) where
  Adj i j := ad i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (ad i j = true))

theorem acyc_of_lt {n : ℕ} (H : SimpleGraph (Fin n))
    (h : ∀ x u v : Fin n, H.Adj x u → H.Adj x v → u ≠ v → x < u ∨ x < v) : H.IsAcyclic := by
  classical
  intro z w cyc
  obtain ⟨m, hm, hmax⟩ := w.support.toFinset.exists_max_image id ⟨z, by simp⟩
  have hm' : m ∈ w.support := by simpa using hm
  have hq : (w.rotate m hm').IsCycle := cyc.rotate hm'
  have hs := (w.rotate m hm').adj_snd hq.not_nil
  have hp := ((w.rotate m hm').adj_penultimate hq.not_nil).symm
  have hne := hq.snd_ne_penultimate
  have m1 : (w.rotate m hm').snd ∈ w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have m2 : (w.rotate m hm').penultimate ∈ w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have b1 := hmax _ (by simpa using m1)
  have b2 := hmax _ (by simpa using m2)
  rcases h m _ _ hs hp hne with h1 | h1
  · exact absurd b1 (not_le.mpr h1)
  · exact absurd b2 (not_le.mpr h1)

theorem hacyc : G.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (e && f)) = decide (∃ i j : Fin 6, G.Adj i j ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) i = true ∧ (![a, b, c, d, e, f] : Fin 6 → Bool) j = true) := by
    decide
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard : G.edgeFinset.card = 5 := by
  decide

theorem hcov : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  have e1 := hT 0 2 (by decide)
  have e2 := hT 4 5 (by decide)
  rcases e1 with a | a <;> rcases e2 with b | b
  all_goals
    first
    | exact (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a, Finset.singleton_subset_iff.mpr b⟩)).trans' (by decide)

theorem hcov2 : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
  decide

end PEqualNP.Outside.L_meta_759_aux

open PEqualNP.Outside.L_meta_759_aux in
theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [hfun]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 2 s G hacyc ⟨0, 1, by decide⟩ hcov h
    rw [hcard] at this
    omega
  · intro hs
    have h := PEqualNP.MetaComplexity.L105 6 G {0, 4} ⟨0, 1, by decide⟩ hcov2
    rw [hcard] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 4} : Finset (Fin 6)).card = 2 := by decide
    rw [this] at h2
    omega
