import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4754

def mF (w : ℕ) : ℕ := if w = 10 then 17 else if w = 15 then 16 else if w < 16 then w else w + 2

lemma mF_ten : mF 10 = 17 := by unfold mF; simp

lemma mF_fifteen : mF 15 = 16 := by unfold mF; simp

lemma mF_lt {w : ℕ} (h1 : w < 16) (h2 : w ≠ 10) (h3 : w ≠ 15) : mF w = w := by
  unfold mF
  rw [if_neg h2, if_neg h3, if_pos h1]

lemma mF_ge {w : ℕ} (h : 16 ≤ w) : mF w = w + 2 := by
  have h2 : w ≠ 10 := by omega
  have h3 : w ≠ 15 := by omega
  unfold mF
  rw [if_neg h2, if_neg h3, if_neg (by omega : ¬ w < 16)]

lemma mF_lt_wire {w j : ℕ} (h : w < 16 + j) : mF w < 17 + (j + 1) := by
  rcases eq_or_ne w 10 with h1 | h1
  · rw [h1, mF_ten]; omega
  rcases eq_or_ne w 15 with h2 | h2
  · rw [h2, mF_fifteen]; omega
  rcases lt_or_ge w 16 with h3 | h3
  · rw [mF_lt h3 h1 h2]; omega
  · rw [mF_ge h3]; omega

lemma mF_lt_of {w : ℕ} (h : w < 16) : mF w < 18 := by
  rcases eq_or_ne w 10 with h1 | h1
  · rw [h1, mF_ten]; omega
  rcases eq_or_ne w 15 with h2 | h2
  · rw [h2, mF_fifteen]; omega
  rw [mF_lt h h1 h2]; omega

def cg (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map mF }

def ckt (C : Circuit) : Circuit :=
  { gates := ⟨GateOp.or, [10, 15]⟩ :: C.gates.map cg, output := mF C.output }

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma stp_len (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  simp only [stp, List.length_append, List.length_singleton]

lemma getD_snoc_lt {L : List Bool} {a : Bool} {i : ℕ} (h : i < L.length) :
    (L ++ [a]).getD i false = L.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wires_fold (C : Circuit) (x : List Bool) : C.wires x = List.foldl stp x C.gates := rfl

lemma getD_snoc_len {L : List Bool} {a : Bool} : (L ++ [a]).getD L.length false = a := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl L.length)]
  simp

lemma getD_snoc_gt {L : List Bool} {a : Bool} {i : ℕ} (h : L.length < i) :
    (L ++ [a]).getD i false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega : L.length ≤ i)]
  simp [show i - L.length ≠ 0 by omega]

lemma Fold_corr (m : ℕ) (gs : List Gate) :
    ∀ (X' X : List Bool), X'.length = 18 + m → X.length = 16 + m →
      (∀ w < 16 + m, X'.getD (mF w) false = X.getD w false) →
      (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ i ∈ g.inputs, i < 16 + m + j) →
      ∀ w < 16 + m + gs.length,
        (List.foldl stp X' (gs.map cg)).getD (mF w) false = (List.foldl stp X gs).getD w false := by
  induction gs generalizing m with
  | nil =>
    intro X' X _ _ h _ w hw
    simpa using h w (by simpa using hw)
  | cons g gs ih =>
    intro X' X hX' hX h hpos
    have hgin : ∀ i ∈ g.inputs, i < 16 + m := by
      intro i hi
      exact hpos 0 g (by simp) i hi
    have hval : (cg g).op.eval ((cg g).inputs.map fun i => X'.getD i false) =
        g.op.eval (g.inputs.map fun i => X.getD i false) := by
      simp only [cg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply]
      exact h i (hgin i hi)
    have hX'' : (stp X' (cg g)).length = 18 + (m + 1) := by
      rw [stp_len, hX']; omega
    have hX2 : (stp X g).length = 16 + (m + 1) := by
      rw [stp_len, hX]; omega
    have hstep : ∀ w < 16 + m + 1,
        (stp X' (cg g)).getD (mF w) false = (stp X g).getD w false := by
      intro w hw1
      by_cases hold : w < 16 + m
      · have hpre := h w hold
        have hle : mF w < X'.length := by
          rcases eq_or_ne w 10 with h1 | h1
          · rw [h1, mF_ten]; omega
          rcases eq_or_ne w 15 with h2 | h2
          · rw [h2, mF_fifteen]; omega
          rcases lt_or_ge w 16 with h3 | h3
          · rw [mF_lt h3 h1 h2]; omega
          · rw [mF_ge h3]; omega
        rw [stp, getD_snoc_lt hle, hpre, stp, getD_snoc_lt (by omega : w < X.length)]
      · have hwe : w = 16 + m := by omega
        subst hwe
        have hmw : mF (16 + m) = X'.length := by
          rw [mF_ge (by omega), hX']
          omega
        rw [stp, hmw, getD_snoc_len (L := X')]
        rw [stp, ← hX, getD_snoc_len (L := X)]
        exact hval
    have hpos' : ∀ (j : ℕ) (g' : Gate), gs[j]? = some g' → ∀ i ∈ g'.inputs, i < 16 + (m + 1) + j := by
      intro j g' hj i hi
      have h1 : (g :: gs)[j + 1]? = some g' := by
        rw [List.getElem?_cons_succ]; exact hj
      have h2 := hpos (j + 1) g' h1 i hi
      omega
    intro w hw
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    exact ih (m + 1) (stp X' (cg g)) (stp X g) hX'' hX2 hstep hpos' w (by
      simp only [List.length_cons] at hw ⊢; omega)

end PEqualNP.Outside.L_meta_4754

open PEqualNP.Outside.L_meta_4754 in
theorem PEqualNP.Outside.L_meta_4754 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x4 ∧ x4.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x5 : Fin (17 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x4 x5 = PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x6 : Fin (16 : ℕ)) => if x6 = (10 : Fin (16 : ℕ)) then x5 (10 : Fin (17 : ℕ)) || x5 (15 : Fin (17 : ℕ)) else if x6 = (15 : Fin (16 : ℕ)) then x5 (16 : Fin (17 : ℕ)) else x5 (Fin.ofNat (17 : ℕ) ↑x6) := by
  intro C hmon hback
  refine ⟨ckt C, ?_, ?_, ?_, ?_⟩
  · simp only [PEqualNP.MetaComplexity.Monotone2] at hmon ⊢
    intro g hg
    simp only [ckt, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨(hmon g0 hg0).1, by simp only [cg, List.length_map]; exact (hmon g0 hg0).2⟩
  · simp only [PEqualNP.MetaComplexity.NestedCover.ReadsBack] at hback ⊢
    intro j hj i hi
    rcases j with _ | k
    · have h0 : (PEqualNP.MetaComplexity.NestedCover.gateAt (ckt C) 0).inputs = [10, 15] := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, ckt]
      rw [h0] at hi
      have hmem : i = 10 ∨ i = 15 := by simpa using hi
      omega
    · have hk : k < C.gates.length := by
        simp only [ckt, List.length_cons, List.length_map] at hj
        omega
      have hg : (PEqualNP.MetaComplexity.NestedCover.gateAt (ckt C) (k + 1)).inputs =
          (cg (C.gates[k]'hk)).inputs := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, ckt, List.getD_cons_succ,
          List.getElem?_eq_getElem hk]
      rw [hg] at hi
      simp only [cg, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k]'hk := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hk]
      have hin : i0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs := by
        rw [hga]; exact hi0
      have := mF_lt_wire (hback k hk i0 hin)
      omega
  · simp only [Circuit.size, ckt, List.length_cons, List.length_map]
    omega
  · intro x
    set y : Fin 16 → Bool := fun x6 => if x6 = (10 : Fin 16) then x 10 || x 15 else if x6 = (15 : Fin 16) then x 16 else x (Fin.ofNat 17 ↑x6) with hy
    have hX' : (stp (List.ofFn x) ⟨GateOp.or, [10, 15]⟩).length = 18 + 0 := by
      rw [stp_len]; simp
    have hX : (List.ofFn y).length = 16 + 0 := by simp
    have hbase : ∀ w < 16 + 0,
        (stp (List.ofFn x) ⟨GateOp.or, [10, 15]⟩).getD (mF w) false = (List.ofFn y).getD w false := by
      intro w hw
      interval_cases w <;>
        simp [stp, mF, hy, List.getD_eq_getElem?_getD, PEqualNP.CircuitLowerBounds.GateOp.eval]
    have hpos : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 16 + 0 + j := by
      intro j g hj i hi
      have hj' : j < C.gates.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      have hgj : C.gates[j]'hj' = g := by
        have h2 := hj
        rw [List.getElem?_eq_getElem hj'] at h2
        simpa using h2
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', hgj]
        rfl
      have := hback j hj' i (by rwa [hga])
      omega
    have hmain := Fold_corr 0 C.gates (stp (List.ofFn x) ⟨GateOp.or, [10, 15]⟩) (List.ofFn y)
      hX' hX hbase hpos
    by_cases hout : C.output < 16 + C.gates.length
    · have hgot := hmain C.output (by simpa using hout)
      simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires, ckt]
      show (List.foldl stp (List.ofFn x) (⟨GateOp.or, [10, 15]⟩ :: C.gates.map cg)).getD (mF C.output) false =
        (List.foldl stp (List.ofFn y) C.gates).getD C.output false
      rw [List.foldl_cons]
      exact hgot
    · have hlen : (List.foldl stp (List.ofFn y) C.gates).length = 16 + C.gates.length := by
        have : ∀ (gs : List Gate) (X : List Bool), (List.foldl stp X gs).length = X.length + gs.length := by
          intro gs X
          induction gs generalizing X with
          | nil => simp
          | cons g gs ih => rw [List.foldl_cons, ih, stp_len]; simp; omega
        rw [this]; simp
      have hlen' : (List.foldl stp (stp (List.ofFn x) ⟨GateOp.or, [10, 15]⟩) (C.gates.map cg)).length
          = 18 + C.gates.length := by
        have : ∀ (gs : List Gate) (X : List Bool), (List.foldl stp X gs).length = X.length + gs.length := by
          intro gs X
          induction gs generalizing X with
          | nil => simp
          | cons g gs ih => rw [List.foldl_cons, ih, stp_len]; simp; omega
        rw [this, List.length_map]
        rw [stp_len]; simp
      have h1 : (C.wires (List.ofFn y)).getD C.output false = false := by
        rw [wires_fold, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      have h2 : ((ckt C).wires (List.ofFn x)).getD (mF C.output) false = false := by
        rw [wires_fold, show (ckt C).gates = ⟨GateOp.or, [10, 15]⟩ :: C.gates.map cg from rfl,
          List.foldl_cons]
        have : mF C.output = C.output + 2 := mF_ge (by omega)
        rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval]
      rw [show (ckt C).output = mF C.output from rfl, h1, h2]
