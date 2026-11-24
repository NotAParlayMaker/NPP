import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2986_aux
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl


lemma core2 (n : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ outs : List ℕ, ∃ T : Finset (Fin n), T.card ≤ gs.length + outs.length ∧
      ∀ o ∈ outs, ∀ x x' : Fin n → Bool, (∀ i ∈ T, x i = x' i) →
        val gs x o = val gs x' o := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ outs
    refine ⟨(outs.filterMap
      (fun o => if h : o < n then some (⟨o, h⟩ : Fin n) else none)).toFinset, ?_, ?_⟩
    · calc _ ≤ (outs.filterMap
            (fun o => if h : o < n then some (⟨o, h⟩ : Fin n) else none)).length :=
            List.toFinset_card_le _
        _ ≤ outs.length := List.length_filterMap_le _ _
        _ ≤ _ := by simp
    · intro o ho x x' hag
      rw [val_nil, val_nil]
      by_cases h : o < n
      · rw [dif_pos h, dif_pos h]
        apply hag
        rw [List.mem_toFinset, List.mem_filterMap]
        exact ⟨o, ho, by simp [h]⟩
      · rw [dif_neg h, dif_neg h]
  | append_singleton gs g ih =>
    intro hfan outs
    have hfan' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hg := hfan g (by simp)
    by_cases hmem : n + gs.length ∈ outs
    · have hperm := List.perm_cons_erase hmem
      obtain ⟨T, hc, hv⟩ := ih hfan' (outs.erase (n + gs.length) ++ g.inputs)
      refine ⟨T, ?_, ?_⟩
      · have h2 := hperm.length_eq
        rw [List.length_append] at hc
        simp only [List.length_cons, List.length_append, List.length_nil] at h2 ⊢
        omega
      · intro o ho x x' hag
        rw [val_snoc, val_snoc]
        by_cases ho' : o = n + gs.length
        · rw [if_pos ho', if_pos ho']
          congr 1
          apply List.map_congr_left
          intro j hj
          exact hv j (List.mem_append_right _ hj) x x' hag
        · rw [if_neg ho', if_neg ho']
          have hoe : o ∈ outs.erase (n + gs.length) := by
            have h3 := hperm.mem_iff.mp ho
            rcases List.mem_cons.mp h3 with h | h
            · exact absurd h ho'
            · exact h
          exact hv o (List.mem_append_left _ hoe) x x' hag
    · obtain ⟨T, hc, hv⟩ := ih hfan' outs
      refine ⟨T, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro o ho x x' hag
        have ho' : o ≠ n + gs.length := fun h => hmem (h ▸ ho)
        rw [val_snoc, val_snoc, if_neg ho', if_neg ho']
        exact hv o ho x x' hag

lemma cast_ne_nat (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  omega

lemma nat_inj (N : ℕ) (a b : Fin N) (h : Fin.natAdd N a = Fin.natAdd N b) : a = b := by
  have h1 := congrArg Fin.val h
  simp only [Fin.val_natAdd] at h1
  exact Fin.ext (by omega)

lemma card_single (N : ℕ) (l : Fin N) :
    Fintype.card {l' : Fin N // decide (Fin.natAdd N l' = Fin.natAdd N l) = true} ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  exact Subtype.ext ((nat_inj N a l ha).trans (nat_inj N b l hb).symm)

lemma card_none (N : ℕ) (p : Fin N) :
    Fintype.card {l' : Fin N // decide (Fin.natAdd N l' = Fin.castAdd N p) = true} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨a, ha⟩ => ?_⟩
  simp only [decide_eq_true_eq] at ha
  exact cast_ne_nat N p a ha.symm

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    (hacc : ∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true)
    (hsound : ∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) :
    2 * N ≤ C.size + 1 := by
  obtain ⟨T, hc, hv⟩ := core2 (N + N) C.gates (fun g hg => (hmono g hg).2) [C.output]
  have hv' : ∀ x x' : Fin (N + N) → Bool, (∀ i ∈ T, x i = x' i) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x
        = PEqualNP.MetaComplexity.circuitFun (N + N) C x' :=
    fun x x' h => hv C.output (by simp) x x' h
  have hN3 : 3 ≤ N := by
    have := Nat.zero_le (q ^ 2)
    omega
  have hall : ∀ k : Fin (N + N), k ∈ T := by
    intro k
    by_contra hk
    revert hk
    refine Fin.addCases (motive := fun k => k ∉ T → False) (fun p hk => ?_) (fun l hk => ?_) k
    · have hp' : ∃ p' : Fin N, p ≠ p' := by
        by_cases h0 : p.val = 0
        · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
          have h1 := congrArg Fin.val h
          simp only at h1
          omega
        · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
          have h1 := congrArg Fin.val h
          simp only at h1
          omega
      obtain ⟨p', hpp⟩ := hp'
      obtain ⟨l, ⟨hl, _⟩, _⟩ := huniq p p' hpp
      have e1 := hacc p l hl
      have e2 := hsound (fun k : Fin (N + N) => decide (k = Fin.natAdd N l))
        (le_trans (card_single N l) (by omega))
        (by
          rintro ⟨p1, l1, _, h1, _⟩
          simp only [decide_eq_true_eq] at h1
          exact cast_ne_nat N p1 l h1)
      have e3 := hv' (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
        (fun k : Fin (N + N) => decide (k = Fin.natAdd N l))
        (by
          intro i hi
          have hne : i ≠ Fin.castAdd N p := fun h => hk (h ▸ hi)
          simp [hne])
      rw [e1, e2] at e3
      exact absurd e3 (by simp)
    · have hpos : 0 < Fintype.card {p : Fin N // I p l} := by
        rw [hline l]
        omega
      obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hpos
      have e1 := hacc p l hp
      have e2 := hsound (fun k : Fin (N + N) => decide (k = Fin.castAdd N p))
        (by
          have h0 := card_none N p
          exact le_of_eq_of_le h0 (Nat.zero_le _))
        (by
          rintro ⟨p1, l1, _, _, h2⟩
          simp only [decide_eq_true_eq] at h2
          exact cast_ne_nat N p l1 h2.symm)
      have e3 := hv' (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
        (fun k : Fin (N + N) => decide (k = Fin.castAdd N p))
        (by
          intro i hi
          have hne : i ≠ Fin.natAdd N l := fun h => hk (h ▸ hi)
          simp only [hne, or_false])
      rw [e1, e2] at e3
      exact absurd e3 (by simp)
  have hT : T = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  rw [hT, Finset.card_univ, Fintype.card_fin] at hc
  simp only [List.length_singleton] at hc
  show 2 * N ≤ C.gates.length + 1
  omega

end PEqualNP.Outside.L_meta_2986_aux

theorem PEqualNP.Outside.L_meta_2986 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (x2 + x2) x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → (2 : ℕ) * x2 ≤ x5.size + (1 : ℕ) := by
  intro q N I inst C h1 h2 h3 h4 h5 h6 h7 h8
  exact PEqualNP.Outside.L_meta_2986_aux.main q N I C h1 h2 h3 h4 h5 h6 h7 h8
