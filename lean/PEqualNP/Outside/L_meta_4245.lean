import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mapG (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then x else false := by
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h1,
      List.getElem_append_left h1]
  · subst h2
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem run (ρ : ℕ → ℕ) (n m : ℕ) (hge : ∀ i, n ≤ i → ρ i = i - n + m)
    (hlt : ∀ i, i < n → ρ i < m) (gs : List Gate) :
    ∀ (a b : List Bool), n ≤ a.length → b.length + n = a.length + m →
      (∀ i, b.getD (ρ i) false = a.getD i false) →
      ∀ i, ((gs.map (mapG ρ)).foldl stepW b).getD (ρ i) false = (gs.foldl stepW a).getD i false := by
  induction gs with
  | nil => intro a b _ _ h i; exact h i
  | cons g gs ih =>
    intro a b hna hlen h
    show ∀ i, ((gs.map (mapG ρ)).foldl stepW (stepW b (mapG ρ g))).getD (ρ i) false =
      (gs.foldl stepW (stepW a g)).getD i false
    have hval : (mapG ρ g).op.eval ((mapG ρ g).inputs.map fun i => b.getD i false) =
        g.op.eval (g.inputs.map fun i => a.getD i false) := by
      simp only [mapG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    apply ih
    · simp [stepW]; omega
    · simp [stepW]; omega
    · intro i
      simp only [stepW]
      rw [getD_snoc, getD_snoc, hval]
      have hA : ρ i < b.length ↔ i < a.length := by
        by_cases hi : i < n
        · have := hlt i hi; constructor <;> intro _ <;> omega
        · rw [hge i (by omega)]; constructor <;> intro _ <;> omega
      have hB : ρ i = b.length ↔ i = a.length := by
        by_cases hi : i < n
        · have := hlt i hi; constructor <;> intro _ <;> omega
        · rw [hge i (by omega)]; constructor <;> intro _ <;> omega
      by_cases h1 : i < a.length
      · rw [if_pos (hA.2 h1), if_pos h1]
        exact h i
      · rw [if_neg (fun h' => h1 (hA.1 h')), if_neg h1]
        by_cases h2 : i = a.length
        · rw [if_pos (hB.2 h2), if_pos h2]
        · rw [if_neg (fun h' => h2 (hB.1 h')), if_neg h2]

def rho (x1 x2 : ℕ) (x3 : Fin x1) (x6 : Fin x1 → Fin x2) (i : ℕ) : ℕ :=
  if h : i < x1 then (if i = x3.val then x2 else (x6 ⟨i, h⟩).val) else i - x1 + (x2 + 1)

theorem rho_ge (x1 x2 : ℕ) (x3 : Fin x1) (x6 : Fin x1 → Fin x2) (i : ℕ) (hi : x1 ≤ i) :
    rho x1 x2 x3 x6 i = i - x1 + (x2 + 1) := by
  unfold rho
  rw [dif_neg (by omega)]

theorem rho_lt (x1 x2 : ℕ) (x3 : Fin x1) (x6 : Fin x1 → Fin x2) (i : ℕ) (hi : i < x1) :
    rho x1 x2 x3 x6 i < x2 + 1 := by
  unfold rho
  rw [dif_pos hi]
  split_ifs
  · omega
  · have := (x6 ⟨i, hi⟩).isLt
    omega

end PEqualNP.Outside.L_meta_4245

theorem PEqualNP.Outside.L_meta_4245 : ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2) (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧ x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) => if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12) := by
  open PEqualNP.Outside.L_meta_4245 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  intro x1 x2 x3 x4 x5 x6 C hM hRB
  refine ⟨⟨⟨GateOp.or, [x4.val, x5.val]⟩ :: C.gates.map (mapG (rho x1 x2 x3 x6)),
    rho x1 x2 x3 x6 C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨by simp, by simp⟩
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      obtain ⟨hop, hlen⟩ := hM g0 hg0
      exact ⟨hop, by simpa [mapG] using hlen⟩
  · intro j hj i hi
    cases j with
    | zero =>
      simp [NestedCover.gateAt] at hi
      rcases hi with rfl | rfl
      · exact x4.isLt
      · exact x5.isLt
    | succ k =>
      simp only [List.length_cons, List.length_map] at hj
      have hk : k < C.gates.length := by omega
      simp only [NestedCover.gateAt, List.getD_cons_succ] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hk)] at hi
      simp only [List.getElem_map, mapG, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hr := hRB k hk i0 (by
        simp only [NestedCover.gateAt]
        rw [List.getD_eq_getElem _ _ hk]
        exact hi0)
      by_cases hlt : i0 < x1
      · have := rho_lt x1 x2 x3 x6 i0 hlt
        omega
      · rw [rho_ge x1 x2 x3 x6 i0 (by omega)]
        omega
  · simp [Circuit.size]
  · intro y
    unfold circuitFun Circuit.eval Circuit.wires
    rw [List.foldl_cons]
    have h0 : (List.ofFn y ++ [GateOp.or.eval ([x4.val, x5.val].map
        fun i => (List.ofFn y).getD i false)]) = List.ofFn y ++ [y x4 || y x5] := by
      simp [GateOp.eval, List.getD_eq_getElem?_getD]
    rw [h0]
    apply run (rho x1 x2 x3 x6) x1 (x2 + 1) (rho_ge x1 x2 x3 x6) (rho_lt x1 x2 x3 x6) C.gates
    · simp
    · simp; omega
    · intro i
      by_cases hi : i < x1
      · have ha : (List.ofFn (fun x12 : Fin x1 => if x12 = x3 then y x4 || y x5 else y (x6 x12))).getD
            i false = (if (⟨i, hi⟩ : Fin x1) = x3 then y x4 || y x5 else y (x6 ⟨i, hi⟩)) := by
          rw [List.getD_eq_getElem _ _ (by simpa using hi)]
          simp
        rw [ha]
        unfold rho
        rw [dif_pos hi]
        by_cases he : i = x3.val
        · have hx : (⟨i, hi⟩ : Fin x1) = x3 := Fin.ext he
          rw [if_pos he, if_pos hx]
          rw [List.getD_eq_getElem _ _ (by simp)]
          simp
        · have hx : (⟨i, hi⟩ : Fin x1) ≠ x3 := fun h => he (by rw [← h])
          rw [if_neg he, if_neg hx]
          rw [List.getD_eq_getElem _ _ (by simp)]
          simp [List.getElem_append_left]
      · rw [rho_ge x1 x2 x3 x6 i (by omega), List.getD_eq_default _ _ (by simp <;> omega)]
        try rw [List.getD_eq_default _ _ (by simp <;> omega)]
