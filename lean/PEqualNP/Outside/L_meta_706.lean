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

def removeGate {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) : AndCountCircuit n where
  size := m
  leftVars j := lv (i₀.succAbove j)
  leftGates j := Finset.univ.filter (fun k => i₀.succAbove k ∈ lg (i₀.succAbove j))
  rightVars j := rv (i₀.succAbove j)
  rightGates j := Finset.univ.filter (fun k => i₀.succAbove k ∈ rg (i₀.succAbove j))
  outVars := ov
  outGates := Finset.univ.filter (fun k => i₀.succAbove k ∈ og)

theorem mem_leftGates {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (j k : Fin m) :
    k ∈ (removeGate lv lg rv rg ov og i₀).leftGates j ↔
      i₀.succAbove k ∈ lg (i₀.succAbove j) := by
  show k ∈ Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ lg (i₀.succAbove j)) ↔ _
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem mem_rightGates {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (j k : Fin m) :
    k ∈ (removeGate lv lg rv rg ov og i₀).rightGates j ↔
      i₀.succAbove k ∈ rg (i₀.succAbove j) := by
  show k ∈ Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ rg (i₀.succAbove j)) ↔ _
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem mem_outGates {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (k : Fin m) :
    k ∈ (removeGate lv lg rv rg ov og i₀).outGates ↔ i₀.succAbove k ∈ og := by
  show k ∈ Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ og) ↔ _
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem side_corr {n m : ℕ} (i₀ : Fin (m + 1)) (U B : Finset (Fin n))
    (F : Finset (Fin (m + 1))) (hF : i₀ ∉ F) (j : Fin m) (val₁ : Fin m → Bool)
    (val : Fin (m + 1) → Bool) (h : ∀ k : Fin m, k < j → val₁ k = val (i₀.succAbove k)) :
    AndCountCircuit.sideTrue U B (Finset.univ.filter (fun k => i₀.succAbove k ∈ F)) j val₁ =
      AndCountCircuit.sideTrue U B F (i₀.succAbove j) val := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨k, hk, hlt, hv⟩)
    · exact Or.inl h1
    · refine Or.inr ⟨i₀.succAbove k, (Finset.mem_filter.mp hk).2,
        Fin.succAbove_lt_succAbove_iff.mpr hlt, ?_⟩
      rw [← h k hlt]
      exact hv
  · rintro (h1 | ⟨k', hk', hlt, hv⟩)
    · exact Or.inl h1
    · have hne : k' ≠ i₀ := by
        intro e
        rw [e] at hk'
        exact hF hk'
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
      have hkj : k < j := Fin.succAbove_lt_succAbove_iff.mp hlt
      refine Or.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, hkj, ?_⟩
      rw [h k hkj]
      exact hv

theorem remove_val {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1))
    (hl : ∀ k, i₀ ∉ lg k) (hr : ∀ k, i₀ ∉ rg k) (U : Finset (Fin n)) :
    ∀ (b : ℕ) (j : Fin m), j.val < b →
      (removeGate lv lg rv rg ov og i₀).gateVal U j =
        (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U (i₀.succAbove j) := by
  intro b
  induction b with
  | zero =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ b ih =>
    intro j hj
    have key : ∀ k : Fin m, k < j → (removeGate lv lg rv rg ov og i₀).gateVal U k =
        (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U (i₀.succAbove k) := by
      intro k hk
      have hkj : k.val < j.val := hk
      exact ih k (by omega)
    rw [gateVal_eq (removeGate lv lg rv rg ov og i₀) U j,
      gateVal_eq (AndCountCircuit.mk (m + 1) lv lg rv rg ov og) U (i₀.succAbove j)]
    have e1 := side_corr i₀ U (lv (i₀.succAbove j)) (lg (i₀.succAbove j)) (hl _) j
      ((removeGate lv lg rv rg ov og i₀).gateVal U)
      ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U) key
    have e2 := side_corr i₀ U (rv (i₀.succAbove j)) (rg (i₀.succAbove j)) (hr _) j
      ((removeGate lv lg rv rg ov og i₀).gateVal U)
      ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U) key
    exact congrArg₂ (fun a c => a && c) e1 e2

theorem remove_eval {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (hout : i₀ ∉ og)
    (hl : ∀ k, i₀ ∉ lg k) (hr : ∀ k, i₀ ∉ rg k) (U : Finset (Fin n)) :
    (removeGate lv lg rv rg ov og i₀).eval U =
      (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).eval U := by
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hv⟩)
    · exact Or.inl h1
    · refine Or.inr ⟨i₀.succAbove j, (mem_outGates lv lg rv rg ov og i₀ j).mp hj, ?_⟩
      rw [← remove_val lv lg rv rg ov og i₀ hl hr U (j.val + 1) j (Nat.lt_succ_self _)]
      exact hv
  · rintro (h1 | ⟨j', hj', hv⟩)
    · exact Or.inl h1
    · have hne : j' ≠ i₀ := by
        intro e
        rw [e] at hj'
        exact hout hj'
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hne
      refine Or.inr ⟨j, (mem_outGates lv lg rv rg ov og i₀ j).mpr hj', ?_⟩
      rw [remove_val lv lg rv rg ov og i₀ hl hr U (j.val + 1) j (Nat.lt_succ_self _)]
      exact hv

theorem remove_wf {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1))
    (hwf : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) :
    (removeGate lv lg rv rg ov og i₀).WellFormed := by
  intro j
  constructor
  · intro k hk
    have h1 : i₀.succAbove k ∈ lg (i₀.succAbove j) :=
      (mem_leftGates lv lg rv rg ov og i₀ j k).mp hk
    exact Fin.succAbove_lt_succAbove_iff.mp ((hwf (i₀.succAbove j)).1 _ h1)
  · intro k hk
    have h1 : i₀.succAbove k ∈ rg (i₀.succAbove j) :=
      (mem_rightGates lv lg rv rg ov og i₀ j k).mp hk
    exact Fin.succAbove_lt_succAbove_iff.mp ((hwf (i₀.succAbove j)).2 _ h1)

theorem dropUnused {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size)
    (wf : C.WellFormed) (hl : ∀ k, i ∉ C.leftGates k)
    (hr : ∀ k, i ∉ C.rightGates k) (ho : i ∉ C.outGates) :
    ∃ R : AndCountCircuit n, R.WellFormed ∧ R.size + 1 ≤ C.size ∧ ∀ U, R.eval U = C.eval U := by
  cases C with
  | mk s lv lg rv rg ov og =>
    cases s with
    | zero => exact Fin.elim0 i
    | succ m =>
      exact ⟨_, remove_wf lv lg rv rg ov og i wf, le_rfl,
        remove_eval lv lg rv rg ov og i ho hl hr⟩

end PEqualNP.Outside.L_meta_706_aux

open PEqualNP.AndCount PEqualNP.Outside.L_meta_706_aux

theorem PEqualNP.Outside.L_meta_706 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size)),
      (∀ j ∈ F, j < i) →
      (∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  classical
  intro n C wf D i B F earlier repl
  let vars (V : Finset (Fin n)) (G : Finset (Fin C.size)) := if i ∈ G then V ∪ B else V
  let gates (G : Finset (Fin C.size)) := if i ∈ G then G.erase i ∪ F else G
  let S : AndCountCircuit n := {
    size := C.size
    leftVars := fun k => vars (C.leftVars k) (C.leftGates k)
    leftGates := fun k => gates (C.leftGates k)
    rightVars := fun k => vars (C.rightVars k) (C.rightGates k)
    rightGates := fun k => gates (C.rightGates k)
    outVars := vars C.outVars C.outGates
    outGates := gates C.outGates }
  have bound (k : Fin C.size) (G : Finset (Fin C.size)) (hg : ∀ j ∈ G, j < k) :
      ∀ j ∈ gates G, j < k := by
    intro j
    by_cases h : i ∈ G
    · simp only [gates, if_pos h, Finset.mem_union, Finset.mem_erase]
      rintro (⟨_, hj⟩ | hj)
      · exact hg j hj
      · exact lt_trans (earlier j hj) (hg i h)
    · simpa [gates, h] using hg j
  have sw : S.WellFormed := fun k =>
    ⟨bound k _ (wf k).1, bound k _ (wf k).2⟩
  have absent (G : Finset (Fin C.size)) : i ∉ gates G := by
    have hi : i ∉ F := fun h => (lt_irrefl i) (earlier i h)
    by_cases h : i ∈ G <;> simp [gates, h, hi]
  obtain ⟨R, rwf, rsize, req⟩ := dropUnused S i sw
    (fun k => absent (C.leftGates k)) (fun k => absent (C.rightGates k)) (absent C.outGates)
  refine ⟨R, rwf, rsize, ?_⟩
  intro U hU
  rw [req]
  have splice (V : Finset (Fin n)) (G : Finset (Fin C.size)) :
      ((∃ v ∈ vars V G, v ∈ U) ∨ ∃ j ∈ gates G, C.gateVal U j = true) ↔
      ((∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, C.gateVal U j = true) := by
    by_cases hi : i ∈ G
    · simp only [vars, gates, if_pos hi, Finset.mem_union, Finset.mem_erase]
      have hr := repl U hU
      constructor
      · rintro (⟨v, hv | hv, hu⟩ | ⟨j, hj | hj, hv⟩)
        · exact Or.inl ⟨v, hv, hu⟩
        · exact Or.inr ⟨i, hi, hr.mpr (Or.inl ⟨v, hv, hu⟩)⟩
        · exact Or.inr ⟨j, hj.2, hv⟩
        · exact Or.inr ⟨i, hi, hr.mpr (Or.inr ⟨j, hj, hv⟩)⟩
      · rintro (⟨v, hv, hu⟩ | ⟨j, hj, hv⟩)
        · exact Or.inl ⟨v, Or.inl hv, hu⟩
        · by_cases he : j = i
          · subst j
            rcases hr.mp hv with ⟨v, hb, hu⟩ | ⟨t, ht, hval⟩
            · exact Or.inl ⟨v, Or.inr hb, hu⟩
            · exact Or.inr ⟨t, Or.inr ht, hval⟩
          · exact Or.inr ⟨j, Or.inl ⟨he, hj⟩, hv⟩
    · simp [vars, gates, hi]
  have vals (k : Fin C.size) : S.gateVal U k = C.gateVal U k := by
    induction k using WellFoundedLT.induction with
    | ind k ih =>
      have side (V : Finset (Fin n)) (G : Finset (Fin C.size)) (hg : ∀ j ∈ G, j < k) :
          AndCountCircuit.sideTrue U (vars V G) (gates G) k (S.gateVal U) =
          AndCountCircuit.sideTrue U V G k (C.gateVal U) := by
        unfold AndCountCircuit.sideTrue
        rw [decide_eq_decide]
        have bh := bound k G hg
        constructor
        · rintro (hv | ⟨j, hj, hjk, hval⟩)
          · have h := (splice V G).mp (Or.inl hv)
            rcases h with h | ⟨t, ht, htval⟩
            · exact Or.inl h
            · exact Or.inr ⟨t, ht, hg t ht, htval⟩
          · rw [ih j hjk] at hval
            rcases (splice V G).mp (Or.inr ⟨j, hj, hval⟩) with h | ⟨t, ht, htval⟩
            · exact Or.inl h
            · exact Or.inr ⟨t, ht, hg t ht, htval⟩
        · intro h
          have original : (∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, C.gateVal U j = true := by
            rcases h with h | ⟨j, hj, _, hv⟩
            · exact Or.inl h
            · exact Or.inr ⟨j, hj, hv⟩
          rcases (splice V G).mpr original with hv | ⟨j, hj, hval⟩
          · exact Or.inl hv
          · exact Or.inr ⟨j, hj, bh j hj, (ih j (bh j hj)).trans hval⟩
      rw [gateVal_eq S U k, gateVal_eq C U k]
      exact congrArg₂ (fun a b => a && b) (side _ _ (wf k).1) (side _ _ (wf k).2)
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  change ((∃ v ∈ vars C.outVars C.outGates, v ∈ U) ∨ ∃ j ∈ gates C.outGates, S.gateVal U j = true) ↔ _
  simp only [vals]
  exact splice C.outVars C.outGates
