import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection

-- The small-order bound uses the branching of the incidence graph on pair inputs.
-- The remaining game has an incident point and line on one side and at most q lines on the other.
theorem PEqualNP.Outside.R_meta_2984_67
    (linear : ∀ (q n : Nat) (S : Fin n → Finset (Fin n)) (C : Circuit), 2 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin n), Y.card ≤ 2 → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      3*n ≤ C.size+1)
    (proto : ∀ (n : Nat), let R := Finset (Fin n × Fin n) × Finset (Finset (Fin n))
      let box := fun r : R => r.1 ×ˢ r.2
      let legal := fun (w t : List R) => ∀ j : Fin t.length, ∃ a ∈ w++t.take j.val, ∃ b ∈ w++t.take j.val,
        box (t.get j) ⊆ box a ∪ box b
      ∀ (C : Circuit) (w : List R), IsAO2 w.length C → C.output < w.length+C.size →
      ∃ t : List R, t.length ≤ C.size ∧ legal w t ∧ ∃ r ∈ w++t,
        (∀ e, C.eval (w.map fun a => decide (e ∈ a.1)) = true → e ∈ r.1) ∧
        ∀ Y, C.eval (w.map fun a => decide (Y ∉ a.2)) = false → Y ∈ r.2)
    (hard : ∀ (q n : Nat) (S : Fin n → Finset (Fin n)), let R := Finset (Fin n × Fin n) × Finset (Finset (Fin n))
      let box := fun r : R => r.1 ×ˢ r.2
      let legal := fun (w t : List R) => ∀ j : Fin t.length, ∃ a ∈ w++t.take j.val, ∃ b ∈ w++t.take j.val,
        box (t.get j) ⊆ box a ∪ box b
      300 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      ∀ w t : List R, (∀ r ∈ w,
        (∃ p : Fin n, (∀ e ∈ r.1, p = e.1) ∧ ∀ Y ∈ r.2, p ∉ zeroSet S Y) ∨
        (∃ l : Fin n, (∀ e ∈ r.1, l = e.2) ∧ ∀ Y ∈ r.2, l ∉ Y)) →
      legal w t → (∃ r ∈ w++t, (∀ l : Fin n, ∀ p ∈ S l, (p,l) ∈ r.1) ∧
        ∀ Y : Finset (Fin n), Y.card ≤ q → Y ∈ r.2) → n*q ≤ 100*t.length) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q n S C hq order degree join model output accepts rejects
  by_cases high : 300 ≤ q
  · let R := Finset (Fin n × Fin n) × Finset (Finset (Fin n))
    let w : List R := (List.ofFn fun p : Fin n =>
      ((Finset.univ ×ˢ Finset.univ).filter (fun e : Fin n × Fin n => p = e.1),
       (Finset.univ : Finset (Fin n)).powerset.filter (fun Y : Finset (Fin n) => p ∉ zeroSet S Y))) ++
      (List.ofFn fun l : Fin n =>
      ((Finset.univ ×ˢ Finset.univ).filter (fun e : Fin n × Fin n => l = e.2),
       (Finset.univ : Finset (Fin n)).powerset.filter (fun Y : Finset (Fin n) => l ∉ Y)))
    have length : w.length = n+n := by simp [w]
    obtain ⟨t,le,path,r,mem,pos,neg⟩ := proto n C w (length.symm ▸ model) (by rwa [length])
    apply (hard q n S high order degree join w t ?_ path ?_).trans (Nat.mul_le_mul_left 100 le)
    · intro r hr
      simp only [w,List.mem_append,List.mem_ofFn] at hr
      rcases hr with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · exact Or.inl ⟨i, fun e he => (Finset.mem_filter.mp he).2, fun Y hy => (Finset.mem_filter.mp hy).2⟩
      · exact Or.inr ⟨i, fun e he => (Finset.mem_filter.mp he).2, fun Y hy => (Finset.mem_filter.mp hy).2⟩
    refine ⟨r,mem,?_,?_⟩
    · intro l p inc
      apply pos
      have h := accepts l p inc
      change C.eval ((List.ofFn fun x : Fin n => decide (x ∈ ({p} : Finset (Fin n)))) ++ (List.ofFn fun x : Fin n => decide (x ∈ ({l} : Finset (Fin n))))) = true at h
      simpa only [w,List.map_append,List.map_ofFn,Function.comp_def,Finset.mem_filter,Finset.mem_product,Finset.mem_powerset,Finset.subset_univ,Finset.mem_univ,true_and,Finset.mem_singleton] using h
    · intro Y size
      apply neg
      have miss : IsFalseInput S (zeroSet S Y) Y := by
        intro l hl
        apply Finset.disjoint_left.mpr
        intro p hp hz
        exact (Finset.mem_filter.mp hz).2 l hl hp
      have h := rejects (zeroSet S Y) Y size miss
      change C.eval ((List.ofFn fun x : Fin n => decide (x ∈ zeroSet S Y)) ++ (List.ofFn fun x : Fin n => decide (x ∈ Y))) = false at h
      simpa only [w,List.map_append,List.map_ofFn,Function.comp_def,Finset.mem_filter,Finset.mem_product,Finset.mem_powerset,Finset.subset_univ,Finset.mem_univ,true_and,not_not] using h
  · have base := linear q n S C (by omega) order degree join model accepts (fun X Y hy => rejects X Y (by omega))
    have lim := Nat.mul_le_mul_left n (show q ≤ 299 by omega)
    have enough : 100 ≤ n := by omega
    omega
