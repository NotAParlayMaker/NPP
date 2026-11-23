import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_707_aux

open PEqualNP.AndCount

-- The fuel argument adapts the one in L_meta_564.
private theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, (h j hlt) ▸ hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, (h j hlt).symm ▸ hv⟩

private theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero => omega
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => omega
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      simp only [AndCountCircuit.gateValFuel]
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  let d := C.size - 1
  have hd : C.size = d + 1 := by dsimp [d]; omega
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U d j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U d C.size j (by omega) j.2
  have step : C.gateVal U i = C.gateValFuel U (d + 1) i :=
    fuel_indep C U C.size (d + 1) i i.2 (by omega)
  rw [step, AndCountCircuit.gateValFuel]
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private def reads {n k : ℕ} (U X : Finset (Fin n)) (T : Finset (Fin k))
    (v : Fin k → Bool) : Prop :=
  (∃ x ∈ X, x ∈ U) ∨ ∃ j ∈ T, v j = true

private theorem sideTrue_iff {n k : ℕ} (U X : Finset (Fin n)) (T : Finset (Fin k))
    (i : Fin k) (v : Fin k → Bool) (earlier : ∀ j ∈ T, j < i) :
    AndCountCircuit.sideTrue U X T i v = true ↔ reads U X T v := by
  simp only [AndCountCircuit.sideTrue, decide_eq_true_eq, reads]
  constructor
  · rintro (h | ⟨j, hj, _, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hv⟩
  · rintro (h | ⟨j, hj, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, earlier j hj, hv⟩

private theorem gateVal_iff {n : ℕ} (C : AndCountCircuit n) (hwf : C.WellFormed)
    (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      reads U (C.leftVars i) (C.leftGates i) (C.gateVal U) ∧
      reads U (C.rightVars i) (C.rightGates i) (C.gateVal U) := by
  rw [gateVal_eq, Bool.and_eq_true_iff, sideTrue_iff _ _ _ _ _ (hwf i).1,
    sideTrue_iff _ _ _ _ _ (hwf i).2]

private def pull {k m : ℕ} (e : Fin m ↪o Fin k) (T : Finset (Fin k)) : Finset (Fin m) :=
  Finset.univ.filter fun j => e j ∈ T

private theorem mem_pull {k m : ℕ} (e : Fin m ↪o Fin k) (T : Finset (Fin k)) (j : Fin m) :
    j ∈ pull e T ↔ e j ∈ T := by simp [pull]

private def addVars {n k : ℕ} (p : Fin k) (B X : Finset (Fin n)) (T : Finset (Fin k)) :
    Finset (Fin n) :=
  X ∪ if p ∈ T then B else ∅

private def addGates {k : ℕ} (p : Fin k) (F T : Finset (Fin k)) : Finset (Fin k) :=
  T.erase p ∪ if p ∈ T then F else ∅

private theorem addGates_ne {k : ℕ} {p : Fin k} {F T : Finset (Fin k)} (hp : p ∉ F) :
    p ∉ addGates p F T := by
  by_cases h : p ∈ T <;> simp [addGates, h, hp]

private theorem addGates_lt {k : ℕ} {p i : Fin k} {F T : Finset (Fin k)}
    (hF : ∀ j ∈ F, j < p) (hT : ∀ j ∈ T, j < i) :
    ∀ j ∈ addGates p F T, j < i := by
  intro j hj
  by_cases hp : p ∈ T
  · simp only [addGates, hp, ite_true, Finset.mem_union, Finset.mem_erase] at hj
    rcases hj with ⟨_, hj⟩ | hj
    · exact hT j hj
    · exact (hF j hj).trans (hT p hp)
  · have hj' : j ∈ T.erase p := by
      simpa only [addGates, hp, ite_false, Finset.union_empty] using hj
    exact hT j (Finset.mem_erase.mp hj').2

private theorem reads_splice {n k : ℕ} (p : Fin k) (U B X : Finset (Fin n))
    (F T : Finset (Fin k)) (v : Fin k → Bool)
    (replacement : v p = true ↔ reads U B F v) :
    reads U (addVars p B X T) (addGates p F T) v ↔ reads U X T v := by
  by_cases hp : p ∈ T
  · simp only [reads, addVars, addGates, hp, ite_true, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (⟨x, hx | hx, hu⟩ | ⟨j, (⟨_, hj⟩ | hj), hv⟩)
      · exact Or.inl ⟨x, hx, hu⟩
      · exact Or.inr ⟨p, hp, replacement.mpr (Or.inl ⟨x, hx, hu⟩)⟩
      · exact Or.inr ⟨j, hj, hv⟩
      · exact Or.inr ⟨p, hp, replacement.mpr (Or.inr ⟨j, hj, hv⟩)⟩
    · rintro (⟨x, hx, hu⟩ | ⟨j, hj, hv⟩)
      · exact Or.inl ⟨x, Or.inl hx, hu⟩
      · by_cases h : j = p
        · subst j
          rcases replacement.mp hv with ⟨x, hx, hu⟩ | ⟨j, hj, hv⟩
          · exact Or.inl ⟨x, Or.inr hx, hu⟩
          · exact Or.inr ⟨j, Or.inr hj, hv⟩
        · exact Or.inr ⟨j, Or.inl ⟨h, hj⟩, hv⟩
  · simp [addVars, addGates, hp]

private theorem reads_pull {n k m : ℕ} (e : Fin m ↪o Fin k) (U X : Finset (Fin n))
    (T : Finset (Fin k)) (v : Fin k → Bool) (w : Fin m → Bool)
    (cover : ∀ j ∈ T, ∃ i, e i = j)
    (agree : ∀ i ∈ pull e T, w i = v (e i)) :
    reads U X (pull e T) w ↔ reads U X T v := by
  constructor
  · rintro (h | ⟨i, hi, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e i, (mem_pull _ _ _).mp hi, (agree i hi) ▸ hv⟩
  · rintro (h | ⟨j, hj, hv⟩)
    · exact Or.inl h
    · obtain ⟨i, rfl⟩ := cover j hj
      have hi := (mem_pull e T i).2 hj
      exact Or.inr ⟨i, hi, (agree i hi).symm ▸ hv⟩

private def splice {n m : ℕ} (C : AndCountCircuit n) (p : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (e : Fin m ↪o Fin C.size) :
    AndCountCircuit n where
  size := m
  leftVars i := addVars p B (C.leftVars (e i)) (C.leftGates (e i))
  leftGates i := pull e (addGates p F (C.leftGates (e i)))
  rightVars i := addVars p B (C.rightVars (e i)) (C.rightGates (e i))
  rightGates i := pull e (addGates p F (C.rightGates (e i)))
  outVars := addVars p B C.outVars C.outGates
  outGates := pull e (addGates p F C.outGates)

private theorem splice_wf {n m : ℕ} (C : AndCountCircuit n) (hwf : C.WellFormed)
    (p : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (earlier : ∀ j ∈ F, j < p) (e : Fin m ↪o Fin C.size) :
    (splice C p B F e).WellFormed := by
  intro i
  constructor
  · intro j hj
    exact e.lt_iff_lt.mp (addGates_lt earlier (hwf (e i)).1 (e j) ((mem_pull _ _ _).mp hj))
  · intro j hj
    exact e.lt_iff_lt.mp (addGates_lt earlier (hwf (e i)).2 (e j) ((mem_pull _ _ _).mp hj))

private theorem splice_reads {n m : ℕ} (C : AndCountCircuit n)
    (p : Fin C.size) (U B X : Finset (Fin n)) (F T : Finset (Fin C.size))
    (e : Fin m ↪o Fin C.size) (cover : ∀ j, j ≠ p → ∃ i, e i = j)
    (earlier : ∀ j ∈ F, j < p)
    (replacement : C.gateVal U p = true ↔ reads U B F (C.gateVal U))
    (agree : ∀ i ∈ pull e (addGates p F T), (splice C p B F e).gateVal U i = C.gateVal U (e i)) :
    reads U (addVars p B X T) (pull e (addGates p F T)) ((splice C p B F e).gateVal U) ↔
      reads U X T (C.gateVal U) := by
  have hp : p ∉ F := fun h => (lt_irrefl p) (earlier p h)
  have hits : ∀ j ∈ addGates p F T, ∃ i, e i = j := by
    intro j hj
    exact cover j (fun h => (addGates_ne hp) (h ▸ hj))
  exact (reads_pull e U _ _ _ _ hits agree).trans (reads_splice p U B X F T _ replacement)

private theorem splice_values {n m : ℕ} (C : AndCountCircuit n) (hwf : C.WellFormed)
    (p : Fin C.size) (U B : Finset (Fin n)) (F : Finset (Fin C.size))
    (e : Fin m ↪o Fin C.size) (cover : ∀ j, j ≠ p → ∃ i, e i = j)
    (earlier : ∀ j ∈ F, j < p)
    (replacement : C.gateVal U p = true ↔ reads U B F (C.gateVal U)) (i : Fin m) :
    (splice C p B F e).gateVal U i = C.gateVal U (e i) := by
  induction i using (measure fun i : Fin m => i.val).wf.induction with
  | h i ih =>
    apply Bool.eq_iff_iff.mpr
    change ((splice C p B F e).gateVal U i = true ↔ C.gateVal U (e i) = true)
    refine (gateVal_iff _ (splice_wf C hwf p B F earlier e) U i).trans
      ((and_congr ?_ ?_).trans (gateVal_iff C hwf U (e i)).symm)
    · apply splice_reads C p U B _ F _ e cover earlier replacement
      intro j hj
      apply ih j
      exact e.lt_iff_lt.mp (addGates_lt earlier (hwf (e i)).1 (e j) ((mem_pull _ _ _).mp hj))
    · apply splice_reads C p U B _ F _ e cover earlier replacement
      intro j hj
      apply ih j
      exact e.lt_iff_lt.mp (addGates_lt earlier (hwf (e i)).2 (e j) ((mem_pull _ _ _).mp hj))

private theorem splice_eval {n m : ℕ} (C : AndCountCircuit n) (hwf : C.WellFormed)
    (p : Fin C.size) (U B : Finset (Fin n)) (F : Finset (Fin C.size))
    (e : Fin m ↪o Fin C.size) (cover : ∀ j, j ≠ p → ∃ i, e i = j)
    (earlier : ∀ j ∈ F, j < p)
    (replacement : C.gateVal U p = true ↔ reads U B F (C.gateVal U)) :
    (splice C p B F e).eval U = C.eval U := by
  apply Bool.eq_iff_iff.mpr
  simp only [AndCountCircuit.eval, decide_eq_true_eq]
  exact splice_reads C p U B C.outVars F C.outGates e cover earlier replacement
    (fun i _ => splice_values C hwf p U B F e cover earlier replacement i)

private theorem remove_many {n : ℕ} (D : Set (Finset (Fin n))) (count : ℕ)
    (C : AndCountCircuit n) (hwf : C.WellFormed) (S : Finset (Fin C.size))
    (count_eq : S.card = count)
    (replaceable : ∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size),
      (∀ j ∈ F, j < i) ∧ ∀ U ∈ D, C.gateVal U i = true ↔ reads U B F (C.gateVal U)) :
    ∃ C' : AndCountCircuit n, C'.WellFormed ∧ C'.size + S.card ≤ C.size ∧
      ∀ U ∈ D, C'.eval U = C.eval U := by
  induction count generalizing C with
  | zero => exact ⟨C, hwf, by simp [count_eq], fun _ _ => rfl⟩
  | succ count ih =>
    have nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    let p := S.max' nonempty
    have hp : p ∈ S := S.max'_mem nonempty
    obtain ⟨B, F, earlier, same⟩ := replaceable p hp
    let kept := (Finset.univ : Finset (Fin C.size)).erase p
    let e : Fin kept.card ↪o Fin C.size := kept.orderEmbOfFin rfl
    have ne_p (i : Fin kept.card) : e i ≠ p := by
      have hi := kept.orderEmbOfFin_mem rfl i
      exact (Finset.mem_erase.mp hi).1
    have cover (j : Fin C.size) (hj : j ≠ p) : ∃ i, e i = j := by
      have hmem : j ∈ kept := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
      change j ∈ Set.range e
      rwa [Finset.range_orderEmbOfFin]
    let C₁ := splice C p B F e
    have hwf₁ : C₁.WellFormed := splice_wf C hwf p B F earlier e
    let S₁ := pull e S
    have hmap : S₁.map e.toEmbedding = S.erase p := by
      ext j
      rw [Finset.mem_map, Finset.mem_erase]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨ne_p i, (mem_pull e S i).mp hi⟩
      · rintro ⟨hj, hjS⟩
        obtain ⟨i, rfl⟩ := cover j hj
        exact ⟨i, (mem_pull e S i).mpr hjS, rfl⟩
    have count₁ : S₁.card = count := by
      have h := Finset.card_erase_add_one hp
      rw [← hmap, Finset.card_map] at h
      omega
    have remaining : ∀ i ∈ S₁, ∃ X : Finset (Fin n), ∃ T : Finset (Fin C₁.size),
        (∀ j ∈ T, j < i) ∧ ∀ U ∈ D, C₁.gateVal U i = true ↔ reads U X T (C₁.gateVal U) := by
      intro i hi
      have hiS := (mem_pull e S i).mp hi
      have hi_lt : e i < p := lt_of_le_of_ne (S.le_max' _ hiS) (ne_p i)
      obtain ⟨X, T, hT, hX⟩ := replaceable (e i) hiS
      have T_lt_p : ∀ j ∈ T, j < p := fun j hj => (hT j hj).trans hi_lt
      refine ⟨X, pull e T, ?_, ?_⟩
      · intro j hj
        exact e.lt_iff_lt.mp (hT (e j) ((mem_pull e T j).mp hj))
      · intro U hU
        change (splice C p B F e).gateVal U i = true ↔
          reads U X (pull e T) ((splice C p B F e).gateVal U)
        rw [splice_values C hwf p U B F e cover earlier (same U hU) i, hX U hU]
        exact (reads_pull e U X T _ _ (fun j hj => cover j (ne_of_lt (T_lt_p j hj)))
          (fun j _ => splice_values C hwf p U B F e cover earlier (same U hU) j)).symm
    obtain ⟨C', hwf', bound, eval'⟩ := ih C₁ hwf₁ S₁ count₁ remaining
    have size₁ : C₁.size + 1 = C.size := by
      change kept.card + 1 = C.size
      simpa [kept] using Finset.card_erase_add_one (Finset.mem_univ p)
    refine ⟨C', hwf', ?_, fun U hU =>
      (eval' U hU).trans (splice_eval C hwf p U B F e cover earlier (same U hU))⟩
    calc
      C'.size + S.card = (C'.size + S₁.card) + 1 := by rw [count_eq, count₁, Nat.add_assoc]
      _ ≤ C₁.size + 1 := Nat.add_le_add_right bound 1
      _ = C.size := size₁

end PEqualNP.Outside.L_meta_707_aux

open PEqualNP.Outside.L_meta_707_aux in
theorem PEqualNP.Outside.L_meta_707 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (S : Finset (Fin C.size)),
      (∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size), (∀ j ∈ F, j < i) ∧
        ∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + S.card ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  intro n C hwf D S h
  exact remove_many D S.card C hwf S rfl h
