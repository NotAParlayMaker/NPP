import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.LMeta759

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def edgePairs : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)]

private def spiderRel (i j : Fin 6) : Bool :=
  edgePairs.any (fun p => (p.1 == i && p.2 == j) || (p.1 == j && p.2 == i))

private abbrev G : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun i j => spiderRel i j = true)

private def targetF (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)

private lemma targetF_eq_graph (x : Fin 6 → Bool) :
    targetF x = decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) := by
  have h1 : ∀ x0 x1 x2 x3 x4 x5 : Bool,
      ((x0 && x1) || (x0 && x2) || (x0 && x3) || (x1 && x4) || (x4 && x5)) =
      decide ((x0 = true ∧ x1 = true) ∨ (x0 = true ∧ x2 = true) ∨ (x0 = true ∧ x3 = true) ∨
        (x1 = true ∧ x4 = true) ∨ (x4 = true ∧ x5 = true)) := by decide
  have h2 : (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((x 0 = true ∧ x 1 = true) ∨ (x 0 = true ∧ x 2 = true) ∨ (x 0 = true ∧ x 3 = true) ∨
        (x 1 = true ∧ x 4 = true) ∨ (x 4 = true ∧ x 5 = true)) := by
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      fin_cases i <;> fin_cases j <;> simp_all [G, spiderRel, edgePairs]
    · rintro (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h0, h3⟩ | ⟨h1, h4⟩ | ⟨h4, h5⟩)
      · exact ⟨0, 1, by decide, h0, h1⟩
      · exact ⟨0, 2, by decide, h0, h2⟩
      · exact ⟨0, 3, by decide, h0, h3⟩
      · exact ⟨1, 4, by decide, h1, h4⟩
      · exact ⟨4, 5, by decide, h4, h5⟩
  rw [targetF, h1, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact h2.symm

private lemma isAcyclic_of_order {n : ℕ} (H : SimpleGraph (Fin n)) (ord : Fin n → ℕ)
    (hinj : Function.Injective ord)
    (hord : ∀ v u1 u2 : Fin n, H.Adj u1 v → H.Adj u2 v → ord u1 < ord v → ord u2 < ord v → u1 = u2) :
    H.IsAcyclic := by
  intro v c hc
  let S : Finset (Fin n) := c.support.toFinset
  have hS : S.Nonempty := ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image S ord hS
  have hm_supp : m ∈ c.support := List.mem_toFinset.mp hmS
  let c' := c.rotate m hm_supp
  have hc' : c'.IsCycle := hc.rotate hm_supp
  have hlen3 : 3 ≤ c'.length := hc'.three_le_length
  have hsupp_sub : ∀ w ∈ c'.support, w ∈ S := by
    intro w hw
    apply List.mem_toFinset.mpr
    by_cases hwm : w = m
    · exact hwm ▸ hm_supp
    · obtain ⟨n1, hn1⟩ := c.support_rotate m hm_supp
      have hw_tail : w ∈ c'.support.tail := by
        cases hc'eq : c' with
        | nil => rw [hc'eq] at hw; simp at hw; exact (hwm hw).elim
        | cons _ p =>
          rw [hc'eq] at hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, List.tail_cons] at hw ⊢
          exact hw.resolve_left hwm
      have hw_rot : w ∈ c.support.tail := by
        rw [← hn1]; exact List.mem_rotate.mpr hw_tail
      exact List.mem_of_mem_tail hw_rot
  cases hc'eq : c' with
  | nil => rw [hc'eq] at hlen3; simp at hlen3
  | cons h1 p1 =>
    rename_i u1
    have hu1_ne : u1 ≠ m := h1.ne.symm
    have hu1_S : u1 ∈ S := hsupp_sub u1 (by rw [hc'eq]; simp)
    have hlt1 : ord u1 < ord m := by
      have hle := hmax u1 hu1_S
      have hne : ord u1 ≠ ord m := fun e => hu1_ne (hinj e)
      omega
    cases hrev : c'.reverse with
    | nil =>
      have : c'.reverse.length = c'.length := SimpleGraph.Walk.length_reverse c'
      rw [hrev] at this; simp at this; omega
    | cons h2 p2 =>
      rename_i u2
      have hu2_ne : u2 ≠ m := h2.ne.symm
      have hu2_S : u2 ∈ S := by
        apply hsupp_sub u2
        have : u2 ∈ c'.reverse.support := by rw [hrev]; simp
        simpa [SimpleGraph.Walk.support_reverse] using this
      have hlt2 : ord u2 < ord m := by
        have hle := hmax u2 hu2_S
        have hne : ord u2 ≠ ord m := fun e => hu2_ne (hinj e)
        omega
      have hu12 : u1 = u2 := hord m u1 u2 h1.symm h2.symm hlt1 hlt2
      have hedg_nodup : c'.edges.Nodup := hc'.edges_nodup
      have hfirst : c'.edges.head? = some s(m, u1) := by rw [hc'eq]; rfl
      have hlast : c'.edges.getLast? = some s(u2, m) := by
        have hr : c'.reverse.edges = c'.edges.reverse := SimpleGraph.Walk.edges_reverse c'
        have hh : c'.reverse.edges.head? = some s(m, u2) := by rw [hrev]; rfl
        rw [hr, List.head?_reverse] at hh
        simpa [Sym2.eq_swap] using hh
      have hlen_e : 3 ≤ c'.edges.length := by simpa [SimpleGraph.Walk.length_edges] using hlen3
      cases he : c'.edges with
      | nil => rw [he] at hlen_e; simp at hlen_e
      | cons e0 es =>
        rw [he] at hedg_nodup hfirst hlast hlen_e
        simp only [List.head?_cons, Option.some.injEq] at hfirst
        cases hes : es with
        | nil => rw [hes] at hlen_e; simp at hlen_e
        | cons e1 es' =>
          rw [hes] at hedg_nodup hlast
          have hmem_last : s(u2, m) ∈ e1 :: es' := by
            have hgl : (e0 :: e1 :: es').getLast? = (e1 :: es').getLast? := by simp
            rw [hgl] at hlast
            exact List.mem_of_getLast? hlast
          have hnot_mem : e0 ∉ e1 :: es' := (List.nodup_cons.mp hedg_nodup).1
          rw [hfirst, hu12, Sym2.eq_swap] at hnot_mem
          exact hnot_mem hmem_last

private lemma spider_acyclic : G.IsAcyclic := by
  refine isAcyclic_of_order G (fun v : Fin 6 => v.val) (fun a b h => Fin.ext h) ?_
  decide

private lemma spider_edge_card : G.edgeFinset.card = 5 := by decide

private lemma spider_main (s : ℕ) :
    HasCircuitSize 6 targetF s ↔ 6 ≤ s := by
  have heq : targetF = (fun x : Fin 6 → Bool =>
      decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) :=
    funext targetF_eq_graph
  rw [heq]
  constructor
  · intro hs
    have hlb := PEqualNP.MetaComplexity.L104 6 2 s G spider_acyclic ⟨0, 1, by decide⟩
      (fun T hT => by
        have h1 : (0 : Fin 6) ∈ T ∨ (2 : Fin 6) ∈ T := hT 0 2 (by decide)
        have h2 : (4 : Fin 6) ∈ T ∨ (5 : Fin 6) ∈ T := hT 4 5 (by decide)
        let A : Finset (Fin 6) := T ∩ {0, 2}
        let B : Finset (Fin 6) := T ∩ {4, 5}
        have hA : 1 ≤ A.card := Finset.card_pos.mpr (by
          rcases h1 with h | h
          · exact ⟨0, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
          · exact ⟨2, Finset.mem_inter.mpr ⟨h, by decide⟩⟩)
        have hB : 1 ≤ B.card := Finset.card_pos.mpr (by
          rcases h2 with h | h
          · exact ⟨4, Finset.mem_inter.mpr ⟨h, by decide⟩⟩
          · exact ⟨5, Finset.mem_inter.mpr ⟨h, by decide⟩⟩)
        have hdisj : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have hx1' := (Finset.mem_inter.mp hx1).2
          have hx2' := (Finset.mem_inter.mp hx2).2
          clear hx1 hx2
          revert x hx1' hx2'
          decide
        have hsub : A ∪ B ⊆ T := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj] at hcard
        omega)
      hs
    rw [spider_edge_card] at hlb
    omega
  · intro hs
    have hub := PEqualNP.MetaComplexity.L105 6 G ({0, 4} : Finset (Fin 6)) ⟨0, 1, by decide⟩
      (fun i j hij => by revert i j hij; decide)
    rw [spider_edge_card, show ({0, 4} : Finset (Fin 6)).card = 2 from by decide] at hub
    obtain ⟨C, hF, hsz, hev⟩ := hub
    exact ⟨C, hF, hsz.trans (by omega), hev⟩

end PEqualNP.Outside.LMeta759

theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  exact PEqualNP.Outside.LMeta759.spider_main
