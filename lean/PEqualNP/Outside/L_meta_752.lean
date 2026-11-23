import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_752

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def f4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 2 && x 3)

def C4 : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

theorem C4_fanin : FanInTwo C4 := by
  intro g hg
  simp [C4] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem C4_eval : ∀ x : Fin 4 → Bool, C4.eval (List.ofFn x) = f4 x := by
  decide

theorem upper (s : ℕ) (hs : 3 ≤ s) : HasCircuitSize 4 f4 s := by
  refine ⟨C4, C4_fanin, ?_, C4_eval⟩
  change 3 ≤ s
  exact hs

def G4 : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)
  symm := ⟨by
    intro u v h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> revert h1 <;> decide⟩

instance : DecidableRel G4.Adj := by
  intro u v
  dsimp [G4]
  infer_instance

lemma isAcyclic_of_order {n : ℕ} (H : SimpleGraph (Fin n)) (ord : Fin n → ℕ)
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

lemma G4_acyclic : G4.IsAcyclic := by
  refine isAcyclic_of_order G4 (fun (v : Fin 4) => v.val) (fun a b h => Fin.ext h) ?_
  decide

lemma G4_has_edge : ∃ i j : Fin 4, G4.Adj i j := ⟨0, 1, by decide⟩

lemma G4_cover (T : Finset (Fin 4)) (hT : ∀ i j : Fin 4, G4.Adj i j → i ∈ T ∨ j ∈ T) :
    2 ≤ T.card := by
  revert hT
  revert T
  decide

lemma G4_edges : G4.edgeFinset.card = 2 := by
  decide

lemma G4_f4_eq : (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G4.Adj i j ∧ x i = true ∧ x j = true)) = f4 := by
  funext x
  revert x
  decide

theorem lower (s : ℕ) (hs : HasCircuitSize 4 f4 s) : 3 ≤ s := by
  have h_bound := PEqualNP.MetaComplexity.L104 4 2 s G4 G4_acyclic G4_has_edge G4_cover
  rw [G4_f4_eq] at h_bound
  have h_res := h_bound hs
  rw [G4_edges] at h_res
  omega

end PEqualNP.Outside.L_meta_752

theorem PEqualNP.Outside.L_meta_752 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  intro s
  exact ⟨PEqualNP.Outside.L_meta_752.lower s, PEqualNP.Outside.L_meta_752.upper s⟩
