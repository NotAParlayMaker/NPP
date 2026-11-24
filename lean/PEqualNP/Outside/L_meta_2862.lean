import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2862

open PEqualNP.CircuitLowerBounds

private def wireStep (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op.eval (g.inputs.map fun i => wires.getD i false)]

private theorem wireLength (gs : List Gate) (x : List Bool) :
    (gs.foldl wireStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, wireStep, List.length_append, List.length_nil]
    omega

private theorem getD_append_singleton {α : Type} (xs : List α) (a d : α) (i : ℕ) :
    (xs ++ [a]).getD i d =
      if i < xs.length then xs.getD i d else if i = xs.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with hlt heq
  · rw [List.getElem?_append_left hlt]
  · subst i
    simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

private theorem wireSupport (n : ℕ) (gs : List Gate) (targets : Finset ℕ)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ support : Finset ℕ, support.card ≤ targets.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ support, x.getD i false = y.getD i false) →
        ∀ i ∈ targets, (gs.foldl wireStep x).getD i false =
          (gs.foldl wireStep y).getD i false := by
  induction gs using List.reverseRecOn generalizing targets with
  | nil =>
    exact ⟨targets, by simp, fun x y _ _ h => h⟩
  | append_singleton gs g ih =>
    let w := n + gs.length
    let previous := if w ∈ targets then targets.erase w ∪ g.inputs.toFinset else targets
    have hprevious : previous.card ≤ targets.card + 1 := by
      by_cases hw : w ∈ targets
      · simp only [previous, ite_eq_left hw]
        have hu := Finset.card_union_le (targets.erase w) g.inputs.toFinset
        have he := Finset.card_erase_of_mem hw
        have hp := Finset.card_pos.mpr ⟨w, hw⟩
        have hi := List.toFinset_card_le g.inputs
        have hg := hfan g (by simp)
        omega
      · simp [previous, hw]
    obtain ⟨support, hcard, hagree⟩ :=
      ih previous (fun g' hg' => hfan g' (List.mem_append_left _ hg'))
    refine ⟨support, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy hs i hi
    have hX : (gs.foldl wireStep x).length = w := by simp [wireLength, hx, w]
    have hY : (gs.foldl wireStep y).length = w := by simp [wireLength, hy, w]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
    rw [getD_append_singleton, getD_append_singleton, hX, hY]
    split_ifs with hlt heq
    · apply hagree x y hx hy hs i
      by_cases hw : w ∈ targets
      · simp only [previous, ite_eq_left hw]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne_of_lt hlt, hi⟩)
      · simpa [previous, hw] using hi
    · subst i
      congr 1
      apply List.map_congr_left
      intro j hj
      apply hagree x y hx hy hs j
      simp only [previous, ite_eq_left hi]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr hj)
    · rfl

private theorem essential_mem {n : ℕ} (C : Circuit) (S : Finset ℕ)
    (hS : ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ S, x.getD i false = y.getD i false) → C.eval x = C.eval y)
    (i : Fin n) (a b : Fin n → Bool)
    (hagree : ∀ j, j ≠ i → a j = b j)
    (hdiff : PEqualNP.MetaComplexity.circuitFun n C a ≠
      PEqualNP.MetaComplexity.circuitFun n C b) : i.val ∈ S := by
  by_contra hi
  apply hdiff
  apply hS (List.ofFn a) (List.ofFn b) (by simp) (by simp)
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hj' : j < n
  · have hne : (⟨j, hj'⟩ : Fin n) ≠ i := fun h => hi (congrArg Fin.val h ▸ hj)
    simpa [hj'] using hagree ⟨j, hj'⟩ hne
  · simp [hj']

end PEqualNP.Outside.L_meta_2862

open PEqualNP.Outside.L_meta_2862 in
theorem PEqualNP.Outside.L_meta_2862 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x1 < (200 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C hq hq' hN hregular hpair hmono haccept hsound
  have hlarge : 100 ≤ N := by omega
  letI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨S, hcard, hS⟩ :=
    wireSupport (N + N) C.gates {C.output} (fun g hg => (hmono g hg).2)
  have heval : ∀ x y : List Bool, x.length = N + N → y.length = N + N →
      (∀ i ∈ S, x.getD i false = y.getD i false) → C.eval x = C.eval y :=
    fun x y hx hy h => hS x y hx hy h C.output (Finset.mem_singleton_self _)
  have hsep (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have hp := p.isLt
    omega
  have hsingle (i : Fin (N + N)) :
      PEqualNP.MetaComplexity.circuitFun (N + N) C (fun j => decide (j = i)) = false := by
    apply hsound
    · have hc : Fintype.card {j : Fin N // (decide (Fin.natAdd N j = i) : Bool) = true}
          ≤ 1 := by
        apply Fintype.card_le_one_iff_subsingleton.mpr
        refine ⟨fun a b => Subtype.ext ((Fin.natAdd_inj N).mp ?_)⟩
        exact (of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm
      exact hc.trans (by omega)
    · rintro ⟨p, l, _, hp, hl⟩
      exact hsep p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  have hall : ∀ i : Fin (N + N), i.val ∈ S := by
    refine Fin.addCases (motive := fun i : Fin (N + N) => i.val ∈ S) ?_ ?_
    · intro p
      obtain ⟨p', hp'⟩ := exists_ne p
      obtain ⟨l, hl, _⟩ := hpair p p' hp'.symm
      refine essential_mem C S heval (Fin.castAdd N p)
        (fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l))
        (fun j => decide (j = Fin.natAdd N l)) (fun j hj => by simp [hj]) ?_
      rw [haccept p l hl.1, hsingle]
      decide
    · intro l
      have hpos : 0 < Fintype.card {p : Fin N // I p l} := by rw [hregular]; omega
      obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hpos
      refine essential_mem C S heval (Fin.natAdd N l)
        (fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l))
        (fun j => decide (j = Fin.castAdd N p)) (fun j hj => by simp only [hj, or_false]) ?_
      rw [haccept p l hp, hsingle]
      decide
  have hrange : Finset.range (N + N) ⊆ S :=
    fun i hi => hall ⟨i, Finset.mem_range.mp hi⟩
  have hsize : N + N ≤ C.size + 1 := by
    have hs := Finset.card_le_card hrange
    simp only [Finset.card_range] at hs
    simp only [Finset.card_singleton] at hcard
    change S.card ≤ 1 + C.size at hcard
    omega
  calc
    N * q ≤ N * 199 := Nat.mul_le_mul_left N (by omega)
    _ ≤ 100 * C.size := by omega
