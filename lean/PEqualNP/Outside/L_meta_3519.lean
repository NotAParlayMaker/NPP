import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3519

open scoped BigOperators

theorem fiberA_card (n m : ℕ) (EA : Finset (Fin n × Fin m)) (u : Fin n) :
    ((EA.filter (fun e => e.1 = u)).image Prod.snd).card =
      (EA.filter (fun e => e.1 = u)).card := by
  apply Finset.card_image_of_injOn
  intro e1 he1 e2 he2 hsnd
  simp only [Finset.mem_coe, Finset.mem_filter] at he1 he2
  exact Prod.ext (he1.2.trans he2.2.symm) hsnd

theorem fiberB_card (n m : ℕ) (EB : Finset (Fin n × Fin m)) (v : Fin m) :
    ((EB.filter (fun e => e.2 = v)).image Prod.fst).card =
      (EB.filter (fun e => e.2 = v)).card := by
  apply Finset.card_image_of_injOn
  intro e1 he1 e2 he2 hfst
  simp only [Finset.mem_coe, Finset.mem_filter] at he1 he2
  exact Prod.ext hfst (he1.2.trans he2.2.symm)

theorem main : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) := by
  classical
  intro n m E A B hcov
  let EA : Finset (Fin n × Fin m) := E.filter (fun e => e.1 ∈ A)
  let EB : Finset (Fin n × Fin m) := E.filter (fun e => e.1 ∉ A)
  let fA : Fin n → Finset (Fin m) := fun u => (EA.filter (fun e => e.1 = u)).image Prod.snd
  let fB : Fin m → Finset (Fin n) := fun v => (EB.filter (fun e => e.2 = v)).image Prod.fst
  let listA : Fin n → List ℕ := fun u => (fA u).toList.map (fun v => n + v.val)
  let listB : Fin m → List ℕ := fun v => (fB v).toList.map (fun u => u.val)
  let A' : Finset (Fin n) := A.filter (fun u => (fA u).Nonempty)
  let B' : Finset (Fin m) := B.filter (fun v => (fB v).Nonempty)
  let ownA : List (ℕ × List ℕ) := A'.toList.map (fun u => (u.val, listA u))
  let ownB : List (ℕ × List ℕ) := B'.toList.map (fun v => (n + v.val, listB v))
  refine ⟨ownA ++ ownB, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hpA | hpB
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hpA
      have hu' : u ∈ A' := Finset.mem_toList.mp hu
      have hne : (fA u).Nonempty := (Finset.mem_filter.mp hu').2
      refine ⟨?_, Or.inl ⟨u.isLt, ?_⟩⟩
      · intro hnil
        dsimp only at hnil
        have hlen : (listA u).length = 0 := by rw [hnil]; rfl
        have hcard : (fA u).card = 0 := by simpa [listA] using hlen
        exact hne.ne_empty (Finset.card_eq_zero.mp hcard)
      · intro r hr
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
        exact ⟨Nat.le_add_right n v.val, Nat.add_lt_add_left v.isLt n⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hpB
      have hv' : v ∈ B' := Finset.mem_toList.mp hv
      have hne : (fB v).Nonempty := (Finset.mem_filter.mp hv').2
      refine ⟨?_, Or.inr ⟨Nat.le_add_right n v.val, Nat.add_lt_add_left v.isLt n, ?_⟩⟩
      · intro hnil
        dsimp only at hnil
        have hlen : (listB v).length = 0 := by rw [hnil]; rfl
        have hcard : (fB v).card = 0 := by simpa [listB] using hlen
        exact hne.ne_empty (Finset.card_eq_zero.mp hcard)
      · intro r hr
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hr
        exact u.isLt
  · intro u v
    constructor
    · intro huv
      by_cases hu : u ∈ A
      · have huvA : (u, v) ∈ EA := Finset.mem_filter.mpr ⟨huv, hu⟩
        have hv : v ∈ fA u := Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨huvA, rfl⟩, rfl⟩
        have hu' : u ∈ A' := Finset.mem_filter.mpr ⟨hu, ⟨v, hv⟩⟩
        refine ⟨(u.val, listA u), List.mem_append_left _ (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu', rfl⟩), ?_⟩
        exact Or.inl ⟨rfl, List.mem_map.mpr ⟨v, Finset.mem_toList.mpr hv, rfl⟩⟩
      · have hvB : v ∈ B := (hcov (u, v) huv).resolve_left hu
        have huvB : (u, v) ∈ EB := Finset.mem_filter.mpr ⟨huv, hu⟩
        have huF : u ∈ fB v := Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨huvB, rfl⟩, rfl⟩
        have hv' : v ∈ B' := Finset.mem_filter.mpr ⟨hvB, ⟨u, huF⟩⟩
        refine ⟨(n + v.val, listB v), List.mem_append_right _ (List.mem_map.mpr ⟨v, Finset.mem_toList.mpr hv', rfl⟩), ?_⟩
        exact Or.inr ⟨rfl, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr huF, rfl⟩⟩
    · rintro ⟨p, hp, hcase⟩
      rcases List.mem_append.mp hp with hpA | hpB
      · obtain ⟨u', _, rfl⟩ := List.mem_map.mp hpA
        rcases hcase with ⟨heq, hmem⟩ | ⟨heq, _⟩
        · have hu' : u' = u := Fin.ext heq
          subst hu'
          obtain ⟨v', hv', hveq⟩ := List.mem_map.mp hmem
          have hv'' : v' = v := Fin.ext (Nat.add_left_cancel hveq)
          subst hv''
          obtain ⟨e, he, hesnd⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hv')
          obtain ⟨heEA, hefst⟩ := Finset.mem_filter.mp he
          have heq' : e = (u', v') := Prod.ext hefst hesnd
          exact (Finset.mem_filter.mp (heq' ▸ heEA)).1
        · exact False.elim (Nat.not_lt.mpr (Nat.le_add_right n v.val) (heq ▸ u'.isLt))
      · obtain ⟨v', _, rfl⟩ := List.mem_map.mp hpB
        rcases hcase with ⟨heq, _⟩ | ⟨heq, hmem⟩
        · dsimp only at heq
          have huLt := u.isLt
          omega
        · have hv' : v' = v := Fin.ext (Nat.add_left_cancel heq)
          subst hv'
          obtain ⟨u', hu', hueq⟩ := List.mem_map.mp hmem
          have hu'' : u' = u := Fin.ext hueq
          subst hu''
          obtain ⟨e, he, hefst⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hu')
          obtain ⟨heEB, hesnd⟩ := Finset.mem_filter.mp he
          have heq' : e = (u', v') := Prod.ext hefst hesnd
          exact (Finset.mem_filter.mp (heq' ▸ heEB)).1
  · have hlenA : ownA.length ≤ A.card := by
      rw [List.length_map, Finset.length_toList]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hlenB : ownB.length ≤ B.card := by
      rw [List.length_map, Finset.length_toList]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hsumA : (ownA.map (fun p => p.2.length)).sum ≤ EA.card := by
      have h1 : (ownA.map (fun p => p.2.length)).sum = ∑ u ∈ A', (fA u).card := by
        simp only [ownA, List.map_map, Function.comp_def, listA, List.length_map, Finset.length_toList]
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
        rfl
      rw [h1]
      have h2 : ∑ u ∈ A', (fA u).card ≤ ∑ u ∈ A, (fA u).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have h3 : ∑ u ∈ A, (fA u).card = EA.card := by
        have hf : ∀ u ∈ A, (fA u).card = (EA.filter (fun e => e.1 = u)).card :=
          fun u _ => fiberA_card n m EA u
        rw [Finset.sum_congr rfl hf]
        exact (Finset.card_eq_sum_card_fiberwise (fun e he => (Finset.mem_filter.mp he).2)).symm
      exact h2.trans_eq h3
    have hsumB : (ownB.map (fun p => p.2.length)).sum ≤ EB.card := by
      have h1 : (ownB.map (fun p => p.2.length)).sum = ∑ v ∈ B', (fB v).card := by
        simp only [ownB, List.map_map, Function.comp_def, listB, List.length_map, Finset.length_toList]
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
        rfl
      rw [h1]
      have h2 : ∑ v ∈ B', (fB v).card ≤ ∑ v ∈ B, (fB v).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have h3 : ∑ v ∈ B, (fB v).card = EB.card := by
        have hf : ∀ v ∈ B, (fB v).card = (EB.filter (fun e => e.2 = v)).card :=
          fun v _ => fiberB_card n m EB v
        rw [Finset.sum_congr rfl hf]
        refine (Finset.card_eq_sum_card_fiberwise ?_).symm
        intro e he
        obtain ⟨heE, hnotA⟩ := Finset.mem_filter.mp he
        exact (hcov e heE).resolve_left hnotA
      exact h2.trans_eq h3
    have hdisj : Disjoint EA EB := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
    have hunion : EA ∪ EB = E := by
      ext e
      simp only [EA, EB, Finset.mem_union, Finset.mem_filter]
      by_cases h : e.1 ∈ A <;> simp [h]
    have hEcard : EA.card + EB.card = E.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [List.map_append, List.sum_append, List.length_append]
    exact Nat.sub_le_sub_right (by omega) 1

end PEqualNP.Outside.L_meta_3519

theorem PEqualNP.Outside.L_meta_3519 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) :=
  PEqualNP.Outside.L_meta_3519.main
