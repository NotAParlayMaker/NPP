import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_706_aux

open PEqualNP.AndCount

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

theorem core {n m : ℕ} (i₀ : Fin (m + 1)) (U V B : Finset (Fin n))
    (G F : Finset (Fin (m + 1))) (val₁ : Fin m → Bool) (val : Fin (m + 1) → Bool)
    (P : Fin m → Prop) (Q : Fin (m + 1) → Prop)
    (hPQ : ∀ k, P k ↔ Q (i₀.succAbove k)) (hQi : i₀ ∈ G → Q i₀)
    (hFQ : i₀ ∈ G → ∀ j ∈ F, Q j) (hF : ∀ j ∈ F, j ≠ i₀)
    (h : ∀ k, P k → val₁ k = val (i₀.succAbove k))
    (hi : val i₀ = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, val j = true)) :
    ((∃ v ∈ (if i₀ ∈ G then V ∪ B else V), v ∈ U) ∨
      ∃ k ∈ Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ G ∨
        (i₀ ∈ G ∧ i₀.succAbove k ∈ F)), P k ∧ val₁ k = true) ↔
    ((∃ v ∈ V, v ∈ U) ∨ ∃ k ∈ G, Q k ∧ val k = true) := by
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k, hk, hP, hv⟩)
    · by_cases hi0 : i₀ ∈ G
      · rw [if_pos hi0] at hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact Or.inl ⟨v, hv, hvU⟩
        · exact Or.inr ⟨i₀, hi0, hQi hi0, hi.mpr (Or.inl ⟨v, hv, hvU⟩)⟩
      · rw [if_neg hi0] at hv
        exact Or.inl ⟨v, hv, hvU⟩
    · rw [h k hP] at hv
      rcases (Finset.mem_filter.mp hk).2 with hk | ⟨hi0, hk⟩
      · exact Or.inr ⟨i₀.succAbove k, hk, (hPQ k).mp hP, hv⟩
      · exact Or.inr ⟨i₀, hi0, hQi hi0, hi.mpr (Or.inr ⟨i₀.succAbove k, hk, hv⟩)⟩
  · rintro (⟨v, hv, hvU⟩ | ⟨k', hk', hQ, hv⟩)
    · refine Or.inl ⟨v, ?_, hvU⟩
      by_cases hi0 : i₀ ∈ G
      · rw [if_pos hi0]
        exact Finset.mem_union_left _ hv
      · rw [if_neg hi0]
        exact hv
    · by_cases hne : k' = i₀
      · subst hne
        rcases hi.mp hv with ⟨v, hvB, hvU⟩ | ⟨j', hj', hvj⟩
        · refine Or.inl ⟨v, ?_, hvU⟩
          rw [if_pos hk']
          exact Finset.mem_union_right _ hvB
        · have hQj := hFQ hk' j' hj'
          obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (hF j' hj')
          have hPk := (hPQ k).mpr hQj
          refine Or.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hk', hj'⟩⟩, hPk, ?_⟩
          rw [h k hPk]
          exact hvj
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
        have hPk := (hPQ k).mpr hQ
        refine Or.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hk'⟩, hPk, ?_⟩
        rw [h k hPk]
        exact hv

def nv {n m : ℕ} (i₀ : Fin (m + 1)) (B : Finset (Fin n)) (G : Finset (Fin (m + 1)))
    (V : Finset (Fin n)) : Finset (Fin n) := if i₀ ∈ G then V ∪ B else V

def ng {m : ℕ} (i₀ : Fin (m + 1)) (F G : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ G ∨ (i₀ ∈ G ∧ i₀.succAbove k ∈ F))

def rem {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (B : Finset (Fin n))
    (F : Finset (Fin (m + 1))) : AndCountCircuit n where
  size := m
  leftVars j := nv i₀ B (lg (i₀.succAbove j)) (lv (i₀.succAbove j))
  leftGates j := ng i₀ F (lg (i₀.succAbove j))
  rightVars j := nv i₀ B (rg (i₀.succAbove j)) (rv (i₀.succAbove j))
  rightGates j := ng i₀ F (rg (i₀.succAbove j))
  outVars := nv i₀ B og ov
  outGates := ng i₀ F og

theorem side_corr {n m : ℕ} (i₀ : Fin (m + 1)) (U V B : Finset (Fin n))
    (G F : Finset (Fin (m + 1))) (hF : ∀ j ∈ F, j < i₀) (j : Fin m) (val₁ : Fin m → Bool)
    (val : Fin (m + 1) → Bool) (h : ∀ k : Fin m, k < j → val₁ k = val (i₀.succAbove k))
    (hi : val i₀ = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, val j = true))
    (hG : ∀ k ∈ G, k < i₀.succAbove j) :
    AndCountCircuit.sideTrue U (nv i₀ B G V) (ng i₀ F G) j val₁ =
      AndCountCircuit.sideTrue U V G (i₀.succAbove j) val := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  exact core i₀ U V B G F val₁ val (fun k => k < j) (fun k => k < i₀.succAbove j)
    (fun k => Fin.succAbove_lt_succAbove_iff.symm) (fun h0 => hG _ h0)
    (fun h0 j' hj' => lt_trans (hF j' hj') (hG _ h0)) (fun j' hj' => ne_of_lt (hF j' hj')) h hi

theorem ng_lt {m : ℕ} (i₀ : Fin (m + 1)) (F G : Finset (Fin (m + 1))) (hF : ∀ j ∈ F, j < i₀)
    (j : Fin m) (hG : ∀ k ∈ G, k < i₀.succAbove j) : ∀ k ∈ ng i₀ F G, k < j := by
  intro k hk
  rcases (Finset.mem_filter.mp hk).2 with hk | ⟨hi0, hk⟩
  · exact Fin.succAbove_lt_succAbove_iff.mp (hG _ hk)
  · exact Fin.succAbove_lt_succAbove_iff.mp (lt_trans (hF _ hk) (hG _ hi0))

theorem rem_val {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (B : Finset (Fin n))
    (F : Finset (Fin (m + 1))) (hF : ∀ j ∈ F, j < i₀)
    (hwf : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) (U : Finset (Fin n))
    (hi : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U i₀ = true ↔
      ((∃ v ∈ B, v ∈ U) ∨
        ∃ j ∈ F, (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U j = true)) :
    ∀ (b : ℕ) (j : Fin m), j.val < b →
      (rem lv lg rv rg ov og i₀ B F).gateVal U j =
        (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U (i₀.succAbove j) := by
  intro b
  induction b with
  | zero =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ b ih =>
    intro j hj
    have key : ∀ k : Fin m, k < j → (rem lv lg rv rg ov og i₀ B F).gateVal U k =
        (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U (i₀.succAbove k) := by
      intro k hk
      have hkj : k.val < j.val := hk
      exact ih k (by omega)
    rw [gateVal_eq (rem lv lg rv rg ov og i₀ B F) U j,
      gateVal_eq (AndCountCircuit.mk (m + 1) lv lg rv rg ov og) U (i₀.succAbove j)]
    have e1 := side_corr i₀ U (lv (i₀.succAbove j)) B (lg (i₀.succAbove j)) F hF j
      ((rem lv lg rv rg ov og i₀ B F).gateVal U)
      ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U) key hi
      (hwf (i₀.succAbove j)).1
    have e2 := side_corr i₀ U (rv (i₀.succAbove j)) B (rg (i₀.succAbove j)) F hF j
      ((rem lv lg rv rg ov og i₀ B F).gateVal U)
      ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U) key hi
      (hwf (i₀.succAbove j)).2
    exact congrArg₂ (fun a c => a && c) e1 e2

theorem rem_eval {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (B : Finset (Fin n))
    (F : Finset (Fin (m + 1))) (hF : ∀ j ∈ F, j < i₀)
    (hwf : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) (U : Finset (Fin n))
    (hi : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U i₀ = true ↔
      ((∃ v ∈ B, v ∈ U) ∨
        ∃ j ∈ F, (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U j = true)) :
    (rem lv lg rv rg ov og i₀ B F).eval U =
      (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).eval U := by
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  have hc := core i₀ U ov B og F ((rem lv lg rv rg ov og i₀ B F).gateVal U)
    ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U) (fun _ => True) (fun _ => True)
    (fun _ => Iff.rfl) (fun _ => trivial) (fun _ _ _ => trivial)
    (fun j' hj' => ne_of_lt (hF j' hj'))
    (fun k _ => rem_val lv lg rv rg ov og i₀ B F hF hwf U hi (k.val + 1) k (Nat.lt_succ_self _))
    hi
  simp only [true_and] at hc
  exact hc

theorem rem_wf {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (B : Finset (Fin n))
    (F : Finset (Fin (m + 1))) (hF : ∀ j ∈ F, j < i₀)
    (hwf : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) :
    (rem lv lg rv rg ov og i₀ B F).WellFormed := by
  intro j
  exact ⟨ng_lt i₀ F _ hF j (hwf (i₀.succAbove j)).1, ng_lt i₀ F _ hF j (hwf (i₀.succAbove j)).2⟩

end PEqualNP.Outside.L_meta_706_aux

theorem PEqualNP.Outside.L_meta_706 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size)),
      (∀ j ∈ F, j < i) →
      (∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  intro n C hwf D i B F hF hi
  obtain ⟨size, lv, lg, rv, rg, ov, og⟩ := C
  cases size with
  | zero => exact i.elim0
  | succ m =>
    exact ⟨PEqualNP.Outside.L_meta_706_aux.rem lv lg rv rg ov og i B F,
      PEqualNP.Outside.L_meta_706_aux.rem_wf lv lg rv rg ov og i B F hF hwf, le_refl _,
      fun U hU => PEqualNP.Outside.L_meta_706_aux.rem_eval lv lg rv rg ov og i B F hF hwf U
        (hi U hU)⟩
