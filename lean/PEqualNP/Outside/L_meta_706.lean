import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_706

open PEqualNP.AndCount

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
    exact Fin.succAbove_lt_succAbove_iff.mp
      ((hwf (i₀.succAbove j)).1 _ ((mem_leftGates lv lg rv rg ov og i₀ j k).mp hk))
  · intro k hk
    exact Fin.succAbove_lt_succAbove_iff.mp
      ((hwf (i₀.succAbove j)).2 _ ((mem_rightGates lv lg rv rg ov og i₀ j k).mp hk))

theorem dropUnused {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (hw : C.WellFormed)
    (hl : ∀ j, i ∉ C.leftGates j) (hr : ∀ j, i ∉ C.rightGates j)
    (ho : i ∉ C.outGates) :
    ∃ C' : AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
      ∀ U, C'.eval U = C.eval U := by
  cases C with
  | mk size lv lg rv rg ov og =>
    have hi : i.val < size := by simpa using i.2
    have hsizepos : 0 < size := by omega
    obtain ⟨m, hsize⟩ : ∃ m, size = m + 1 := ⟨size - 1, by omega⟩
    subst size
    change (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed at hw
    change ∀ j : Fin (m + 1), i ∉ lg j at hl
    change ∀ j : Fin (m + 1), i ∉ rg j at hr
    change i ∉ og at ho
    refine ⟨removeGate lv lg rv rg ov og i, remove_wf lv lg rv rg ov og i hw, ?_, ?_⟩
    · simp [removeGate]
    · intro U
      exact remove_eval lv lg rv rg ov og i ho hl hr U



def substVars {n s : ℕ} (i : Fin s) (B X : Finset (Fin n)) (H : Finset (Fin s)) :
    Finset (Fin n) := if i ∈ H then X ∪ B else X

def substGates {s : ℕ} (i : Fin s) (F H : Finset (Fin s)) : Finset (Fin s) :=
  if i ∈ H then H.erase i ∪ F else H

theorem substHit {n s : ℕ} (i : Fin s) (U B X : Finset (Fin n)) (F H : Finset (Fin s))
    (old new : Fin s → Bool)
    (hi : old i = true ↔ (∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, old j = true)
    (hnew : ∀ j ∈ substGates i F H, new j = old j) :
    ((∃ v ∈ substVars i B X H, v ∈ U) ∨ ∃ j ∈ substGates i F H, new j = true) ↔
    ((∃ v ∈ X, v ∈ U) ∨ ∃ j ∈ H, old j = true) := by
  by_cases hm : i ∈ H <;> simp only [substGates, substVars, hm, if_true, if_false, Finset.mem_union, Finset.mem_erase] at hnew ⊢ <;> grind

theorem substEarlier {s : ℕ} (i k : Fin s) (F H : Finset (Fin s))
    (hH : ∀ j ∈ H, j < k) (hF : ∀ j ∈ F, j < i) :
    ∀ j ∈ substGates i F H, j < k := by
  by_cases hm : i ∈ H
  · intro j hj
    simp only [substGates, hm, if_true, Finset.mem_union, Finset.mem_erase] at hj
    exact hj.elim (fun h => hH _ h.2) (fun h => lt_trans (hF _ h) (hH _ hm))
  · simpa [substGates, hm] using hH

theorem substAvoid {s : ℕ} (i : Fin s) (F H : Finset (Fin s))
    (hF : ∀ j ∈ F, j < i) : i ∉ substGates i F H := by
  by_cases hm : i ∈ H
  · have h : i ∉ F := fun hi => (lt_irrefl i) (hF i hi)
    simp [substGates, hm, h]
  · simp [substGates, hm]


def rewired {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) : AndCountCircuit n where
  size := C.size
  leftVars k := substVars i B (C.leftVars k) (C.leftGates k)
  leftGates k := substGates i F (C.leftGates k)
  rightVars k := substVars i B (C.rightVars k) (C.rightGates k)
  rightGates k := substGates i F (C.rightGates k)
  outVars := substVars i B C.outVars C.outGates
  outGates := substGates i F C.outGates

lemma noGuard {n s : ℕ} (U X : Finset (Fin n)) (H : Finset (Fin s)) (k : Fin s)
    (v : Fin s → Bool) (h : ∀ j ∈ H, j < k) :
    AndCountCircuit.sideTrue U X H k v =
      decide ((∃ x ∈ X, x ∈ U) ∨ ∃ j ∈ H, v j = true) := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  apply or_congr_right
  exact
    ⟨fun ⟨j, hj, _, hv⟩ => ⟨j, hj, hv⟩, fun ⟨j, hj, hv⟩ => ⟨j, hj, h j hj, hv⟩⟩

lemma wire_correct {n : ℕ} (C : AndCountCircuit n) (hw : C.WellFormed)
    (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (hf : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) :
    (rewired C i B F).eval U = C.eval U := by
  let T := rewired C i B F
  have vals : ∀ k : Fin C.size, T.gateVal U k = C.gateVal U k := by
    intro k
    refine (wellFounded_lt (α := Fin C.size)).induction (C := fun j => T.gateVal U j = C.gateVal U j) k ?_
    intro k ih
    have side (X : Finset (Fin n)) (H : Finset (Fin C.size)) (earlier : ∀ j ∈ H, j < k) :
        AndCountCircuit.sideTrue U (substVars i B X H) (substGates i F H) k (T.gateVal U) =
        AndCountCircuit.sideTrue U X H k (C.gateVal U) := by
      have e := substEarlier i k F H earlier hf
      refine (noGuard U _ _ k (T.gateVal U) e).trans (?_ : _ = _)
      refine Eq.trans ?_ (noGuard U X H k (C.gateVal U) earlier).symm
      exact decide_eq_decide.mpr (substHit i U B X F H _ _ hi (fun j hj => ih j (e j hj)))
    rw [gateVal_eq T U k, gateVal_eq C U k]
    exact congrArg₂ (fun a b => a && b)
      (side _ _ ((hw k).1)) (side _ _ ((hw k).2))
  change T.eval U = C.eval U
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  exact substHit i U B C.outVars F C.outGates _ _ hi (fun j _ => vals j)

end PEqualNP.Outside.L_meta_706

open PEqualNP.Outside.L_meta_706

theorem PEqualNP.Outside.L_meta_706 :
∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (i : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size)),
      (∀ j ∈ F, j < i) →
      (∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U
    := by
  intro n C hw D i B F hf hi
  let T := rewired C i B F
  have w : T.WellFormed := fun k =>
    ⟨substEarlier i k F _ (hw k).1 hf, substEarlier i k F _ (hw k).2 hf⟩
  obtain ⟨C', hw', hs, he⟩ := dropUnused T i w
    (fun k => substAvoid i F (C.leftGates k) hf)
    (fun k => substAvoid i F (C.rightGates k) hf)
    (substAvoid i F C.outGates hf)
  exact ⟨C', hw', hs, fun U hU => (he U).trans (wire_correct C hw i B F hf U (hi U hU))⟩
