import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm PEqualNP.LowMerge

theorem PEqualNP.Outside.R_meta_3682_644
    (lineCount : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (l : Fin n)
      (J : Finset (Fin C.size)), IsAO2 (n + n) C → C.output < n + n + C.size →
      IsLow n n (fun p k => decide (p ∈ S k)) C C.output l →
      S l ⊆ aliveSet n n C C.output l →
      (∀ j : Fin C.size, IsNewLowMerge n n (fun p k => decide (p ∈ S k)) C (n+n+j.val) l → j ∈ J) →
      (S l).card ≤ J.card + 1)
    (uniqueLine : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (g : ℕ) (off : Finset (Fin n)),
      off = ∅ →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → IsMonotoneCircuit C →
      ∀ p r : Fin n, p ≠ r →
      wireValue C (incidenceInput {p} off) g = true →
      wireValue C (incidenceInput {r} off) g = true →
      ∀ l k : Fin n, IsLow n n (fun a t => decide (a ∈ S t)) C g l →
        IsLow n n (fun a t => decide (a ∈ S t)) C g k → l = k)
    (mixedReuse : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q ^ 2 + q + 1 → (∀ l, (S l).card = q + 1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n + n) C → ¬ PEqualNP.ReadK.IsReadK (n + n) C 2 →
      C.output < n + n + C.size → RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y →
        C.eval (incidenceInput X Y) = false) →
      ∀ (off : Finset (Fin n)), off = ∅ →
      ∀ (D : Finset (Fin C.size)) (M : Fin C.size → Finset (Fin n)),
      (∀ j ∈ D, ∀ p r : Fin n,
        wireValue C (incidenceInput {p} off) (n+n+j.val) = true →
        wireValue C (incidenceInput {r} off) (n+n+j.val) = true → p = r) →
      (∀ j ∈ D, ∀ l ∈ M j, IsNewLowMerge n n (fun p k => decide (p ∈ S k)) C (n+n+j.val) l) →
      (∑ j ∈ D, ((M j).card - 1)) ≤ 99 * C.size) : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn hline hjoin hmodel hread hout hpair hreject
  let inc := fun (p l : Fin n) => decide (p ∈ S l)
  let merges := fun (j : Fin C.size) (l : Fin n) =>
    IsNewLowMerge n n inc C (n + n + j.val) l
  let base := fun j : Fin C.size => Finset.univ.filter (fun p : Fin n =>
    wireValue C (incidenceInput {p} (∅ : Finset (Fin n))) (n + n + j.val) = true)
  let lines := fun j : Fin C.size => Finset.univ.filter (merges j)
  have low (l : Fin n) : IsLow n n inc C C.output l := by
    intro pts hv
    by_contra h
    let X := Finset.univ.filter fun p : Fin n => pts p = true
    have hx (p : Fin n) : decide (p ∈ X) = pts p := by simp [X]
    have he : incidenceInput X {l} = restrictInput n n l pts := by
      delta incidenceInput restrictInput
      simp [hx]
    have hf : IsFalseInput S X {l} := by
      intro k hk
      obtain rfl := Finset.mem_singleton.mp hk
      apply Finset.disjoint_left.mpr
      intro p hp hX
      exact h (by delta lineSum; simp only [decide_eq_true_eq]; exact ⟨p, by simpa [inc] using hp,
        (Finset.mem_filter.mp hX).2⟩)
    have hz := hreject X {l} (by simp; omega) hf
    rw [he] at hz
    exact Bool.noConfusion (hz.symm.trans hv)
  have row (l : Fin n) : q ≤ (Finset.univ.filter (fun j : Fin C.size => merges j l)).card := by
    have hv : S l ⊆ aliveSet n n C C.output l := by
      intro p hp
      have hit := hpair l p hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (C.wires (List.ofFn (fun a : Fin n => decide (a = p)) ++
        List.ofFn (fun b : Fin n => decide (b = l)))).getD C.output false = true
      change (C.wires (List.ofFn (fun a : Fin n => decide (a ∈ ({p} : Finset (Fin n)))) ++
        List.ofFn (fun b : Fin n => decide (b ∈ ({l} : Finset (Fin n)))))).getD C.output false = true at hit
      simpa only [Finset.mem_singleton] using hit
    have h := lineCount n S C l (Finset.univ.filter (fun j : Fin C.size => merges j l)) hmodel hout (low l) hv
      (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    rw [hline] at h
    change q + 1 ≤ (Finset.univ.filter (fun j : Fin C.size => merges j l)).card + 1 at h
    omega
  have stable (j : Fin C.size) (hb : 1 < (base j).card) : (lines j).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl k hk
    obtain ⟨p,hp,r,hr,hpr⟩ := Finset.one_lt_card.mp hb
    exact uniqueLine n S C _ ∅ rfl hjoin hmodel.1 p r hpr (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hr).2 l k
      ((Finset.mem_filter.mp hl).2).1 ((Finset.mem_filter.mp hk).2).1
  let D := Finset.univ.filter (fun j : Fin C.size => (base j).card ≤ 1)
  have reuse := mixedReuse q n S C hq hn hline hjoin hmodel hread hout hpair hreject ∅ rfl D lines
    (by
      intro j hj p r hp hr
      exact Finset.card_le_one.mp (Finset.mem_filter.mp hj).2 p
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩) r
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩))
    (fun _ _ _ hl => (Finset.mem_filter.mp hl).2)
  dsimp only [D] at reuse
  rw [Finset.sum_filter] at reuse
  have total : n * q ≤ ∑ j : Fin C.size, (lines j).card := by
    calc
      n * q = ∑ _ : Fin n, q := by simp
      _ ≤ ∑ l : Fin n, (Finset.univ.filter (fun j : Fin C.size => merges j l)).card :=
        Finset.sum_le_sum fun l _ => row l
      _ = ∑ j : Fin C.size, (lines j).card := by
        simp only [lines, Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
  have budget (j : Fin C.size) : (lines j).card ≤
      1 + (if (base j).card ≤ 1 then (lines j).card - 1 else 0) := by
    split_ifs with h
    · omega
    · have := stable j (by omega)
      omega
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun j _ => budget j)
  rw [Finset.sum_add_distrib] at bound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at bound
  omega
