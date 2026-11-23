import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.LMeta759

open PEqualNP.MetaComplexity

private def targetF (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)

private def edgePairs : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)]

private def thetaRel (i j : Fin 6) : Bool :=
  edgePairs.any (fun p => (p.1 == i && p.2 == j) || (p.1 == j && p.2 == i))

private abbrev G : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun i j => thetaRel i j = true)

private lemma targetF_eq_graph (x : Fin 6 → Bool) :
    targetF x = decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · intro h
    unfold targetF at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · exact ⟨0, 1, by decide, h1, h2⟩
    · exact ⟨0, 2, by decide, h1, h2⟩
    · exact ⟨0, 3, by decide, h1, h2⟩
    · exact ⟨1, 4, by decide, h1, h2⟩
    · exact ⟨4, 5, by decide, h1, h2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hmem_all : ∀ a b : Fin 6, G.Adj a b → (a, b) ∈ edgePairs ∨ (b, a) ∈ edgePairs := by
      decide
    have hmem := hmem_all i j hij
    have hf : targetF x = false → False := by
      intro hf
      unfold targetF at hf
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hf
      have hchk : ∀ a b : Fin 6, (a, b) ∈ edgePairs → x a = true → x b = true → False := by
        intro a b hab ha hb
        simp only [edgePairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp_all
      rcases hmem with hm | hm
      · exact hchk i j hm hi hj
      · exact hchk j i hm hj hi
    cases ht : targetF x with
    | true => rfl
    | false => exact (hf ht).elim

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
            have hne_nil : (e1 :: es') ≠ [] := List.cons_ne_nil _ _
            have hgl : (e0 :: e1 :: es').getLast? = (e1 :: es').getLast? := by simp
            rw [hgl] at hlast
            exact List.mem_of_getLast? hlast
          have hnot_mem : e0 ∉ e1 :: es' := (List.nodup_cons.mp hedg_nodup).1
          rw [hfirst, hu12, Sym2.eq_swap] at hnot_mem
          exact hnot_mem hmem_last

private def ord6 (v : Fin 6) : ℕ := v.val

private lemma hacyc : G.IsAcyclic :=
  isAcyclic_of_order G ord6 Fin.val_injective (by decide)

private lemma edge_exists : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, by decide⟩

private lemma card_edges : G.edgeFinset.card = 5 := by decide

private lemma cover04 :
    ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
  decide

private lemma cover_min :
    ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide

private lemma hcs_congr {n s : ℕ} {f g : (Fin n → Bool) → Bool} (h : ∀ x, f x = g x) :
    HasCircuitSize n f s ↔ HasCircuitSize n g s := by
  constructor
  · rintro ⟨C, hF, hsz, hev⟩
    exact ⟨C, hF, hsz, fun x => (hev x).trans (h x)⟩
  · rintro ⟨C, hF, hsz, hev⟩
    exact ⟨C, hF, hsz, fun x => (hev x).trans (h x).symm⟩

end PEqualNP.Outside.LMeta759

open PEqualNP.Outside.LMeta759

theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  have hlam : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) = targetF := rfl
  rw [hlam]
  have key : PEqualNP.MetaComplexity.HasCircuitSize 6 targetF s ↔
      PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) s :=
    hcs_congr (fun x => targetF_eq_graph x)
  constructor
  · intro h
    have h2 := PEqualNP.MetaComplexity.L104 6 2 s G hacyc edge_exists cover_min (key.mp h)
    rw [card_edges] at h2
    omega
  · intro h6
    have hT : ({0, 4} : Finset (Fin 6)).card = 2 := by decide
    have hup := PEqualNP.MetaComplexity.L105 6 G ({0, 4} : Finset (Fin 6)) edge_exists cover04
    rw [card_edges, hT] at hup
    refine key.mpr ?_
    rcases hup with ⟨C, hF, hsz, hev⟩
    exact ⟨C, hF, le_trans hsz (by omega), hev⟩
