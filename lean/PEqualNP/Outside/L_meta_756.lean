import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_756_aux

def rel (u v : Fin 6) : Bool :=
  decide ((u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] : List (ℕ × ℕ)) ∨
    (v.val, u.val) ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] : List (ℕ × ℕ)))

def graph : SimpleGraph (Fin 6) where
  Adj u v := rel u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance decAdj : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (rel u v = true))

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

theorem hub : ∀ x u v : Fin 6, rel x u = true → rel x v = true → u ≠ v → x.val ≤ 1 := by decide

theorem acyc : graph.IsAcyclic :=
  forest_two graph (fun u => u.val) Fin.val_injective (fun x u v hu hv hne => hub x u v hu hv hne)

theorem adj01 : rel 0 1 = true := by decide

theorem minCover : ∀ S : Finset (Fin 6),
    (∀ u v : Fin 6, rel u v = true → u ∈ S ∨ v ∈ S) → 2 ≤ S.card := by decide

theorem cover01 : ∀ u v : Fin 6, rel u v = true →
    u ∈ ({0, 1} : Finset (Fin 6)) ∨ v ∈ ({0, 1} : Finset (Fin 6)) := by decide

theorem edges_eq : graph.edgeFinset =
    ({s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 5)} : Finset (Sym2 (Fin 6))) := by
  ext e
  refine Sym2.ind (fun u v => ?_) e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert,
    Finset.mem_singleton, Sym2.eq_iff]
  change rel u v = true ↔ _
  revert u v
  decide

theorem edge_card : graph.edgeFinset.card = 5 := by
  rw [edges_eq]
  decide

theorem fn_eq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) =
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ((((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩)
    · exact ⟨0, 1, by decide, ha, hb⟩
    · exact ⟨0, 2, by decide, ha, hb⟩
    · exact ⟨0, 3, by decide, ha, hb⟩
    · exact ⟨0, 4, by decide, ha, hb⟩
    · exact ⟨1, 5, by decide, ha, hb⟩
  · rintro ⟨i, j, hadj, hi, hj⟩
    have key : ∀ i j : Fin 6, rel i j = true →
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
        (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
        (i = 1 ∧ j = 5) ∨ (i = 5 ∧ j = 1) := by decide
    rcases key i j hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hi, hj]

theorem size_eq : graph.edgeFinset.card + ({0, 1} : Finset (Fin 6)).card - 1 = 6 := by
  rw [edge_card]
  decide

end PEqualNP.Outside.L_meta_756_aux

open PEqualNP.Outside.L_meta_756_aux in
theorem PEqualNP.Outside.L_meta_756 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [fn_eq]
  constructor
  · intro h
    have h1 := PEqualNP.MetaComplexity.L104 6 2 s graph acyc ⟨0, 1, adj01⟩ minCover h
    rw [edge_card] at h1
    omega
  · intro hs
    have h2 := PEqualNP.MetaComplexity.L105 6 graph {0, 1} ⟨0, 1, adj01⟩ cover01
    rw [size_eq] at h2
    obtain ⟨C, hf, hsz, he⟩ := h2
    exact ⟨C, hf, hsz.trans hs, he⟩
