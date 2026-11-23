import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- A side only consults the gates before its own gate.
theorem side_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j, j < i → val j = val' j) :
    sideTrue U B F i val = sideTrue U B F i val' := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

-- Any fuel above the index of a gate gives the same value.
theorem fuel_stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val = m → ∀ d d' : ℕ, m < d → m < d' →
      gateValFuel C U d i = gateValFuel C U d' i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi d d' hd hd'
    cases d with
    | zero => omega
    | succ d =>
      cases d' with
      | zero => omega
      | succ d' =>
        simp only [gateValFuel]
        congr 1
        · apply side_congr
          intro j hj
          have hjv : j.val < i.val := hj
          exact ih j.val (by omega) j rfl d d' (by omega) (by omega)
        · apply side_congr
          intro j hj
          have hjv : j.val < i.val := hj
          exact ih j.val (by omega) j rfl d d' (by omega) (by omega)

theorem gv_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  unfold gateVal
  rw [fuel_stable C U i.val i rfl C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)]
  simp only [gateValFuel]
  congr 1
  · apply side_congr
    intro j hj
    have hjv : j.val < i.val := hj
    exact fuel_stable C U j.val j rfl _ _ hjv j.isLt
  · apply side_congr
    intro j hj
    have hjv : j.val < i.val := hj
    exact fuel_stable C U j.val j rfl _ _ hjv j.isLt

-- The value of a gate of a well-formed circuit, as a statement.
theorem gv_iff {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i = true ↔
      ((∃ v ∈ C.leftVars i, v ∈ U) ∨ ∃ j ∈ C.leftGates i, C.gateVal U j = true) ∧
      ((∃ v ∈ C.rightVars i, v ∈ U) ∨ ∃ j ∈ C.rightGates i, C.gateVal U j = true) := by
  rw [gv_unfold]
  simp only [Bool.and_eq_true, sideTrue, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases h2 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hW i).1 j hj, hv⟩
    · rcases h2 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hW i).2 j hj, hv⟩

-- The old index of a gate of the circuit with gate `i` removed.
def emb {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (k : Fin (C.size - 1)) : Fin C.size :=
  if k.val < i.val then ⟨k.val, by have := k.isLt; omega⟩ else ⟨k.val + 1, by have := k.isLt; omega⟩

theorem emb_val {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (k : Fin (C.size - 1)) :
    (emb C i k).val = if k.val < i.val then k.val else k.val + 1 := by
  unfold emb
  split_ifs <;> rfl

theorem emb_lt {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (k' k : Fin (C.size - 1))
    (h : emb C i k' < emb C i k) : k' < k := by
  have h' : (emb C i k').val < (emb C i k).val := h
  rw [emb_val, emb_val] at h'
  show k'.val < k.val
  split_ifs at h' <;> omega

theorem emb_surj {n : ℕ} (C : AndCountCircuit n) (i j : Fin C.size) (h : j ≠ i) :
    ∃ k, emb C i k = j := by
  have hv : j.val ≠ i.val := fun e => h (Fin.ext e)
  have hj := j.isLt
  have hi := i.isLt
  by_cases c : j.val < i.val
  · refine ⟨⟨j.val, by omega⟩, Fin.ext ?_⟩
    rw [emb_val]
    simp [c]
  · refine ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩
    rw [emb_val]
    have c' : ¬ (j.val - 1 < i.val) := by omega
    simp only [c', if_false]
    omega

-- A set of gates after the removal: gate `i` is replaced by the gates of `F`.
def subG {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (F G : Finset (Fin C.size)) :
    Finset (Fin (C.size - 1)) :=
  Finset.univ.filter (fun k => emb C i k ∈ G ∨ (i ∈ G ∧ emb C i k ∈ F))

-- A set of variables after the removal: reading gate `i` adds the variables of `B`.
def subV {n : ℕ} {m : ℕ} (i : Fin m) (B : Finset (Fin n)) (G : Finset (Fin m))
    (V : Finset (Fin n)) : Finset (Fin n) :=
  V ∪ (if i ∈ G then B else ∅)

def remove {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) : AndCountCircuit n where
  size := C.size - 1
  leftVars k := subV i B (C.leftGates (emb C i k)) (C.leftVars (emb C i k))
  leftGates k := subG C i F (C.leftGates (emb C i k))
  rightVars k := subV i B (C.rightGates (emb C i k)) (C.rightVars (emb C i k))
  rightGates k := subG C i F (C.rightGates (emb C i k))
  outVars := subV i B C.outGates C.outVars
  outGates := subG C i F C.outGates

theorem mem_subG {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (F G : Finset (Fin C.size))
    (k : Fin (C.size - 1)) :
    k ∈ subG C i F G ↔ (emb C i k ∈ G ∨ (i ∈ G ∧ emb C i k ∈ F)) := by
  simp [subG]

theorem remove_wf {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) :
    (remove C i B F).WellFormed := by
  intro k
  constructor
  · intro k' hk'
    have hk := (mem_subG C i F _ k').mp hk'
    apply emb_lt C i
    rcases hk with h | ⟨h1, h2⟩
    · exact (hW (emb C i k)).1 _ h
    · exact lt_trans (hF _ h2) ((hW (emb C i k)).1 i h1)
  · intro k' hk'
    have hk := (mem_subG C i F _ k').mp hk'
    apply emb_lt C i
    rcases hk with h | ⟨h1, h2⟩
    · exact (hW (emb C i k)).2 _ h
    · exact lt_trans (hF _ h2) ((hW (emb C i k)).2 i h1)

-- A side (or the output) of the new circuit is true exactly when the old one is.
theorem side_iff {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true))
    (gv' : Fin (C.size - 1) → Bool) (G : Finset (Fin C.size)) (V : Finset (Fin n))
    (hP : ∀ k', (emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F)) →
      (gv' k' = true ↔ C.gateVal U (emb C i k') = true)) :
    ((∃ v ∈ subV i B G V, v ∈ U) ∨ ∃ k' ∈ subG C i F G, gv' k' = true) ↔
      ((∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, C.gateVal U j = true) := by
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k', hk', hg⟩)
    · rcases Finset.mem_union.mp hv with h | h
      · exact Or.inl ⟨v, h, hvU⟩
      · by_cases hiG : i ∈ G
        · rw [if_pos hiG] at h
          exact Or.inr ⟨i, hiG, hi.mpr (Or.inl ⟨v, h, hvU⟩)⟩
        · rw [if_neg hiG] at h
          simp at h
    · have hk := (Finset.mem_filter.mp hk').2
      have hv := (hP k' hk).mp hg
      rcases hk with h | ⟨h1, h2⟩
      · exact Or.inr ⟨_, h, hv⟩
      · exact Or.inr ⟨i, h1, hi.mpr (Or.inr ⟨_, h2, hv⟩)⟩
  · rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩)
    · exact Or.inl ⟨v, Finset.mem_union_left _ hv, hvU⟩
    · by_cases hji : j = i
      · rw [hji] at hj hg
        rcases hi.mp hg with ⟨v, hv, hvU⟩ | ⟨j', hj', hg'⟩
        · exact Or.inl ⟨v, Finset.mem_union_right _ (by rw [if_pos hj]; exact hv), hvU⟩
        · obtain ⟨k', hk'⟩ := emb_surj C i j' (ne_of_lt (hF j' hj'))
          have hmem : emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F) :=
            Or.inr ⟨hj, by rw [hk']; exact hj'⟩
          exact Or.inr ⟨k', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩,
            (hP k' hmem).mpr (by rw [hk']; exact hg')⟩
      · obtain ⟨k', hk'⟩ := emb_surj C i j hji
        have hmem : emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F) :=
          Or.inl (by rw [hk']; exact hj)
        exact Or.inr ⟨k', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩,
          (hP k' hmem).mpr (by rw [hk']; exact hg)⟩

-- Every gate of the new circuit has the value of its old gate.
theorem gv_remove {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) :
    ∀ k : Fin (C.size - 1),
      ((remove C i B F).gateVal U k = true ↔ C.gateVal U (emb C i k) = true) := by
  have key : ∀ (m : ℕ) (k : Fin (C.size - 1)), k.val = m →
      ((remove C i B F).gateVal U k = true ↔ C.gateVal U (emb C i k) = true) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk
      rw [gv_iff (remove C i B F) (remove_wf C hW i B F hF) U k, gv_iff C hW U (emb C i k)]
      refine and_congr ?_ ?_
      · refine side_iff C i B F hF U hi ((remove C i B F).gateVal U)
          (C.leftGates (emb C i k)) (C.leftVars (emb C i k)) (fun k' hk' => ?_)
        have hlt : k' < k := by
          apply emb_lt C i
          rcases hk' with h | ⟨h1, h2⟩
          · exact (hW (emb C i k)).1 _ h
          · exact lt_trans (hF _ h2) ((hW (emb C i k)).1 i h1)
        have hlt' : k'.val < k.val := hlt
        exact ih k'.val (by omega) k' rfl
      · refine side_iff C i B F hF U hi ((remove C i B F).gateVal U)
          (C.rightGates (emb C i k)) (C.rightVars (emb C i k)) (fun k' hk' => ?_)
        have hlt : k' < k := by
          apply emb_lt C i
          rcases hk' with h | ⟨h1, h2⟩
          · exact (hW (emb C i k)).2 _ h
          · exact lt_trans (hF _ h2) ((hW (emb C i k)).2 i h1)
        have hlt' : k'.val < k.val := hlt
        exact ih k'.val (by omega) k' rfl
  exact fun k => key k.val k rfl

theorem eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  simp [AndCountCircuit.eval]

-- On an input where gate i has the value of the OR, removing it changes nothing.
theorem remove_eval_eq {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) :
    (remove C i B F).eval U = C.eval U := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  exact side_iff C i B F hF U hi ((remove C i B F).gateVal U) C.outGates C.outVars
    (fun k' _ => gv_remove C hW i B F hF U hi k')

-- One direction only: when gate i implies the OR, a true side stays true.
theorem side_imp {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true → ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true))
    (gv' : Fin (C.size - 1) → Bool) (G : Finset (Fin C.size)) (V : Finset (Fin n))
    (hP : ∀ k', (emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F)) →
      (C.gateVal U (emb C i k') = true → gv' k' = true))
    (h : (∃ v ∈ V, v ∈ U) ∨ ∃ j ∈ G, C.gateVal U j = true) :
    (∃ v ∈ subV i B G V, v ∈ U) ∨ ∃ k' ∈ subG C i F G, gv' k' = true := by
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, Finset.mem_union_left _ hv, hvU⟩
  · by_cases hji : j = i
    · rw [hji] at hj hg
      rcases hi hg with ⟨v, hv, hvU⟩ | ⟨j', hj', hg'⟩
      · exact Or.inl ⟨v, Finset.mem_union_right _ (by rw [if_pos hj]; exact hv), hvU⟩
      · obtain ⟨k', hk'⟩ := emb_surj C i j' (ne_of_lt (hF j' hj'))
        have hmem : emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F) :=
          Or.inr ⟨hj, by rw [hk']; exact hj'⟩
        exact Or.inr ⟨k', (mem_subG C i F G k').mpr hmem, hP k' hmem (by rw [hk']; exact hg')⟩
    · obtain ⟨k', hk'⟩ := emb_surj C i j hji
      have hmem : emb C i k' ∈ G ∨ (i ∈ G ∧ emb C i k' ∈ F) :=
        Or.inl (by rw [hk']; exact hj)
      exact Or.inr ⟨k', (mem_subG C i F G k').mpr hmem, hP k' hmem (by rw [hk']; exact hg)⟩

theorem gv_remove_mono {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true → ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) :
    ∀ k : Fin (C.size - 1),
      (C.gateVal U (emb C i k) = true → (remove C i B F).gateVal U k = true) := by
  have key : ∀ (m : ℕ) (k : Fin (C.size - 1)), k.val = m →
      (C.gateVal U (emb C i k) = true → (remove C i B F).gateVal U k = true) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk
      rw [gv_iff (remove C i B F) (remove_wf C hW i B F hF) U k, gv_iff C hW U (emb C i k)]
      rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · refine side_imp C i B F hF U hi ((remove C i B F).gateVal U)
          (C.leftGates (emb C i k)) (C.leftVars (emb C i k)) (fun k' hk' => ?_) h1
        have hlt : k' < k := by
          apply emb_lt C i
          rcases hk' with h | ⟨h1, h2⟩
          · exact (hW (emb C i k)).1 _ h
          · exact lt_trans (hF _ h2) ((hW (emb C i k)).1 i h1)
        have hlt' : k'.val < k.val := hlt
        exact ih k'.val (by omega) k' rfl
      · refine side_imp C i B F hF U hi ((remove C i B F).gateVal U)
          (C.rightGates (emb C i k)) (C.rightVars (emb C i k)) (fun k' hk' => ?_) h2
        have hlt : k' < k := by
          apply emb_lt C i
          rcases hk' with h | ⟨h1, h2⟩
          · exact (hW (emb C i k)).2 _ h
          · exact lt_trans (hF _ h2) ((hW (emb C i k)).2 i h1)
        have hlt' : k'.val < k.val := hlt
        exact ih k'.val (by omega) k' rfl
  exact fun k => key k.val k rfl

theorem remove_eval_mono {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (i : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (hF : ∀ j ∈ F, j < i) (U : Finset (Fin n))
    (hi : C.gateVal U i = true → ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true))
    (h : C.eval U = true) : (remove C i B F).eval U = true := by
  rw [eval_iff] at h ⊢
  exact side_imp C i B F hF U hi ((remove C i B F).gateVal U) C.outGates C.outVars
    (fun k' _ => gv_remove_mono C hW i B F hF U hi k') h

-- A family of zeros, any two of which have a true input inside their union, has at most
-- 2 ^ size members.
theorem bound {n : ℕ} {ι : Type} [DecidableEq ι] (Z : ι → Finset (Fin n)) :
    ∀ (m : ℕ) (C : AndCountCircuit n), C.WellFormed → C.size = m → ∀ S : Finset ι,
      (∀ s ∈ S, C.eval (Z s) = false) →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ W : Finset (Fin n), W ⊆ Z s ∪ Z t ∧ C.eval W = true) →
      S.card ≤ 2 ^ m := by
  intro m
  induction m with
  | zero =>
    intro C _ hs S hz hj
    have h1 : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro s hs' t ht
      by_contra hne
      obtain ⟨W, hW, hWt⟩ := hj s hs' t ht hne
      rw [eval_iff] at hWt
      rcases hWt with ⟨v, hv, hvW⟩ | ⟨j, _, _⟩
      · rcases Finset.mem_union.mp (hW hvW) with h | h
        · have := hz s hs'
          rw [(eval_iff C (Z s)).mpr (Or.inl ⟨v, hv, h⟩)] at this
          exact Bool.noConfusion this
        · have := hz t ht
          rw [(eval_iff C (Z t)).mpr (Or.inl ⟨v, hv, h⟩)] at this
          exact Bool.noConfusion this
      · have := j.isLt
        omega
    simpa using h1
  | succ m ih =>
    intro C hW hs S hz hj
    have hpos : 0 < C.size := by omega
    have hFl : ∀ j ∈ C.leftGates ⟨0, hpos⟩, j < (⟨0, hpos⟩ : Fin C.size) :=
      (hW ⟨0, hpos⟩).1
    have hFr : ∀ j ∈ C.rightGates ⟨0, hpos⟩, j < (⟨0, hpos⟩ : Fin C.size) :=
      (hW ⟨0, hpos⟩).2
    have hgv := fun U => gv_iff C hW U ⟨0, hpos⟩
    have ha := ih (remove C ⟨0, hpos⟩ (C.leftVars ⟨0, hpos⟩) (C.leftGates ⟨0, hpos⟩))
      (remove_wf C hW _ _ _ hFl) (by show C.size - 1 = m; omega)
      (S.filter (fun s => (remove C ⟨0, hpos⟩ (C.leftVars ⟨0, hpos⟩)
        (C.leftGates ⟨0, hpos⟩)).eval (Z s) = false))
      (fun s hs' => (Finset.mem_filter.mp hs').2)
      (by
        intro s hs' t ht hne
        obtain ⟨W, hWs, hWt⟩ := hj s (Finset.mem_filter.mp hs').1 t (Finset.mem_filter.mp ht).1 hne
        exact ⟨W, hWs, remove_eval_mono C hW _ _ _ hFl W (fun h => ((hgv W).mp h).1) hWt⟩)
    have hb := ih (remove C ⟨0, hpos⟩ (C.rightVars ⟨0, hpos⟩) (C.rightGates ⟨0, hpos⟩))
      (remove_wf C hW _ _ _ hFr) (by show C.size - 1 = m; omega)
      (S.filter (fun s => (remove C ⟨0, hpos⟩ (C.rightVars ⟨0, hpos⟩)
        (C.rightGates ⟨0, hpos⟩)).eval (Z s) = false))
      (fun s hs' => (Finset.mem_filter.mp hs').2)
      (by
        intro s hs' t ht hne
        obtain ⟨W, hWs, hWt⟩ := hj s (Finset.mem_filter.mp hs').1 t (Finset.mem_filter.mp ht).1 hne
        exact ⟨W, hWs, remove_eval_mono C hW _ _ _ hFr W (fun h => ((hgv W).mp h).2) hWt⟩)
    have hsub : S ⊆ S.filter (fun s => (remove C ⟨0, hpos⟩ (C.leftVars ⟨0, hpos⟩)
          (C.leftGates ⟨0, hpos⟩)).eval (Z s) = false) ∪
        S.filter (fun s => (remove C ⟨0, hpos⟩ (C.rightVars ⟨0, hpos⟩)
          (C.rightGates ⟨0, hpos⟩)).eval (Z s) = false) := by
      intro s hs'
      have hzs := hz s hs'
      by_cases hl : (∃ v ∈ C.leftVars ⟨0, hpos⟩, v ∈ Z s) ∨
          ∃ j ∈ C.leftGates ⟨0, hpos⟩, C.gateVal (Z s) j = true
      · by_cases hr : (∃ v ∈ C.rightVars ⟨0, hpos⟩, v ∈ Z s) ∨
            ∃ j ∈ C.rightGates ⟨0, hpos⟩, C.gateVal (Z s) j = true
        · apply Finset.mem_union_left
          refine Finset.mem_filter.mpr ⟨hs', ?_⟩
          rw [remove_eval_eq C hW _ _ _ hFl (Z s)
            ⟨fun _ => hl, fun _ => (hgv (Z s)).mpr ⟨hl, hr⟩⟩]
          exact hzs
        · apply Finset.mem_union_right
          refine Finset.mem_filter.mpr ⟨hs', ?_⟩
          rw [remove_eval_eq C hW _ _ _ hFr (Z s)
            ⟨fun h => ((hgv (Z s)).mp h).2, fun h => absurd h hr⟩]
          exact hzs
      · apply Finset.mem_union_left
        refine Finset.mem_filter.mpr ⟨hs', ?_⟩
        rw [remove_eval_eq C hW _ _ _ hFl (Z s)
          ⟨fun h => ((hgv (Z s)).mp h).1, fun h => absurd h hl⟩]
        exact hzs
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      (S.filter (fun s => (remove C ⟨0, hpos⟩ (C.leftVars ⟨0, hpos⟩)
        (C.leftGates ⟨0, hpos⟩)).eval (Z s) = false))
      (S.filter (fun s => (remove C ⟨0, hpos⟩ (C.rightVars ⟨0, hpos⟩)
        (C.rightGates ⟨0, hpos⟩)).eval (Z s) = false))
    have h3 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega

-- The lower bound from a family of maximal independent sets.
theorem lower {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (G : SimpleGraph (Fin n))
    (Z : ι → Finset (Fin n))
    (hmis : ∀ s, (∀ a ∈ Z s, ∀ c ∈ Z s, ¬ G.Adj a c) ∧ (∀ w, w ∉ Z s → ∃ a ∈ Z s, G.Adj a w))
    (hdiff : ∀ s t, s ≠ t → ∃ w ∈ Z t, w ∉ Z s)
    (C : AndCountCircuit n) (hW : C.WellFormed)
    (hP : ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true) :
    Fintype.card ι ≤ 2 ^ C.size := by
  have h := bound Z C.size C hW rfl Finset.univ
    (fun s _ => (hP (Z s) (hmis s).1 (hmis s).2).1)
    (fun s _ t _ hne => by
      obtain ⟨w, hwt, hws⟩ := hdiff s t hne
      refine ⟨insert w (Z s), ?_, (hP (Z s) (hmis s).1 (hmis s).2).2 w hws⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | h
      · exact Finset.mem_union_right _ hwt
      · exact Finset.mem_union_left _ h)
  simpa using h

def ZA : Fin 9 → Finset (Fin 6) :=
  ![{0, 3}, {0, 4}, {0, 5}, {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4}, {2, 5}]

def circA : AndCountCircuit 6 :=
  { size := 4
    leftVars := ![{0}, {1}, {3}, {4}]
    leftGates := fun _ => ∅
    rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
    rightGates := fun _ => ∅
    outVars := ∅
    outGates := Finset.univ }

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem misA : ∀ s : Fin 9,
    (∀ a ∈ ZA s, ∀ c ∈ ZA s, ¬ (SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))).Adj a c) ∧
      (∀ w, w ∉ ZA s → ∃ a ∈ ZA s, (SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))).Adj a w) := by
  simp only [SimpleGraph.fromRel_adj]
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem diffA : ∀ s t : Fin 9, s ≠ t → ∃ w ∈ ZA t, w ∉ ZA s := by
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem allA : ∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))).Adj a c) →
    (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, (SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))).Adj a w) → ∃ s : Fin 9, I = ZA s := by
  simp only [SimpleGraph.fromRel_adj]
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem wfA : circA.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem okA : ∀ s : Fin 9, circA.eval (ZA s) = false ∧
    ∀ w : Fin 6, w ∉ ZA s → circA.eval (insert w (ZA s)) = true := by
  decide

def ZB : Fin 5 → Finset (Fin 5) :=
  ![{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}]

def circB : AndCountCircuit 5 :=
  { size := 3
    leftVars := ![{0}, {2}, {3}]
    leftGates := fun _ => ∅
    rightVars := ![{1, 4}, {1, 3}, {4}]
    rightGates := fun _ => ∅
    outVars := ∅
    outGates := Finset.univ }

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem misB : ∀ s : Fin 5,
    (∀ a ∈ ZB s, ∀ c ∈ ZB s, ¬ (SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))).Adj a c) ∧
      (∀ w, w ∉ ZB s → ∃ a ∈ ZB s, (SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))).Adj a w) := by
  simp only [SimpleGraph.fromRel_adj]
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem diffB : ∀ s t : Fin 5, s ≠ t → ∃ w ∈ ZB t, w ∉ ZB s := by
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem allB : ∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))).Adj a c) →
    (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, (SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))).Adj a w) → ∃ s : Fin 5, I = ZB s := by
  simp only [SimpleGraph.fromRel_adj]
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem wfB : circB.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem okB : ∀ s : Fin 5, circB.eval (ZB s) = false ∧
    ∀ w : Fin 5, w ∉ ZB s → circB.eval (insert w (ZB s)) = true := by
  decide

def ZD : Fin 7 → Finset (Fin 7) :=
  ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 0}]

def circD : AndCountCircuit 7 :=
  { size := 3
    leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
    leftGates := ![∅, {0}, {1}]
    rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
    rightGates := ![∅, ∅, {0}]
    outVars := ∅
    outGates := {1, 2} }

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem misD : ∀ s : Fin 7,
    (∀ a ∈ ZD s, ∀ c ∈ ZD s, ¬ (SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))).Adj a c) ∧
      (∀ w, w ∉ ZD s → ∃ a ∈ ZD s, (SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))).Adj a w) := by
  simp only [SimpleGraph.fromRel_adj]
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem diffD : ∀ s t : Fin 7, s ≠ t → ∃ w ∈ ZD t, w ∉ ZD s := by
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem allD : ∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))).Adj a c) →
    (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, (SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))).Adj a w) → ∃ s : Fin 7, I = ZD s := by
  simp only [SimpleGraph.fromRel_adj]
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem wfD : circD.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem okD : ∀ s : Fin 7, circD.eval (ZD s) = false ∧
    ∀ w : Fin 7, w ∉ ZD s → circD.eval (insert w (ZD s)) = true := by
  decide

end PEqualNP.Outside.L_meta_906

theorem PEqualNP.Outside.L_meta_906 : (∀ G : SimpleGraph (Fin 6), G = SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed ∧ C.size ≤ 4 ∧
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed →
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true) →
    4 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 5), G = SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed →
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 7), G = SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed →
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G hG
    subst hG
    refine ⟨⟨PEqualNP.Outside.L_meta_906.circA, PEqualNP.Outside.L_meta_906.wfA, by decide, ?_⟩, ?_⟩
    · intro I h1 h2
      obtain ⟨s, rfl⟩ := PEqualNP.Outside.L_meta_906.allA I h1 h2
      exact PEqualNP.Outside.L_meta_906.okA s
    · intro C hW hP
      have h := PEqualNP.Outside.L_meta_906.lower _ PEqualNP.Outside.L_meta_906.ZA
        PEqualNP.Outside.L_meta_906.misA PEqualNP.Outside.L_meta_906.diffA C hW hP
      by_contra hlt
      have h2 : 2 ^ C.size ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp at h
      omega
  · intro G hG
    subst hG
    refine ⟨⟨PEqualNP.Outside.L_meta_906.circB, PEqualNP.Outside.L_meta_906.wfB, by decide, ?_⟩, ?_⟩
    · intro I h1 h2
      obtain ⟨s, rfl⟩ := PEqualNP.Outside.L_meta_906.allB I h1 h2
      exact PEqualNP.Outside.L_meta_906.okB s
    · intro C hW hP
      have h := PEqualNP.Outside.L_meta_906.lower _ PEqualNP.Outside.L_meta_906.ZB
        PEqualNP.Outside.L_meta_906.misB PEqualNP.Outside.L_meta_906.diffB C hW hP
      by_contra hlt
      have h2 : 2 ^ C.size ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp at h
      omega
  · intro G hG
    subst hG
    refine ⟨⟨PEqualNP.Outside.L_meta_906.circD, PEqualNP.Outside.L_meta_906.wfD, by decide, ?_⟩, ?_⟩
    · intro I h1 h2
      obtain ⟨s, rfl⟩ := PEqualNP.Outside.L_meta_906.allD I h1 h2
      exact PEqualNP.Outside.L_meta_906.okD s
    · intro C hW hP
      have h := PEqualNP.Outside.L_meta_906.lower _ PEqualNP.Outside.L_meta_906.ZD
        PEqualNP.Outside.L_meta_906.misD PEqualNP.Outside.L_meta_906.diffD C hW hP
      by_contra hlt
      have h2 : 2 ^ C.size ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp at h
      omega
