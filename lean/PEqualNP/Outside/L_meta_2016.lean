import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2016

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma stepW_len (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

lemma preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepW w g).length := by rw [stepW_len]; omega
    rw [ih (stepW w g) hlt]
    simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma map_agree {w w' : List Bool} (p : ℕ)
    (h : ∀ i, i ≠ p → w.getD i false = w'.getD i false)
    (g : Gate) (hg : p ∉ g.inputs) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (fun hip => hg (hip ▸ hi))

lemma step_agree (p : ℕ) (g : Gate) (hg : p ∉ g.inputs)
    (w w' : List Bool) (hlen : w.length = w'.length)
    (h : ∀ i, i ≠ p → w.getD i false = w'.getD i false) :
    (stepW w g).length = (stepW w' g).length ∧
      ∀ i, i ≠ p → (stepW w g).getD i false = (stepW w' g).getD i false := by
  have hb := map_agree p h g hg
  constructor
  · rw [stepW_len, stepW_len, hlen]
  · intro i hi
    by_cases hlt : i < w.length
    · have hlt' : i < w'.length := hlen ▸ hlt
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt']
      exact h i hi
    · by_cases heq : i = w.length
      · have hy := atEnd w' (g.op.eval (g.inputs.map fun i => w'.getD i false))
        rw [← hlen] at hy
        subst heq
        simp only [stepW]
        rw [atEnd w (g.op.eval (g.inputs.map fun i => w.getD i false)), hy]
        exact hb
      · have hgt : w.length < i := by omega
        have hgt' : w'.length < i := by omega
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_of_lt hgt), List.getElem?_append_right (le_of_lt hgt')]
        rw [hlen]
        rw [List.getElem?_eq_none (by omega : (1:ℕ) ≤ i - w'.length),
            List.getElem?_eq_none (by omega : (1:ℕ) ≤ i - w'.length)]

lemma fold_agree (p : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, p ∉ g.inputs)
    (w w' : List Bool) (hlen : w.length = w'.length)
    (h : ∀ i, i ≠ p → w.getD i false = w'.getD i false) :
    (gs.foldl stepW w).length = (gs.foldl stepW w').length ∧
      ∀ i, i ≠ p → (gs.foldl stepW w).getD i false = (gs.foldl stepW w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact ⟨hlen, h⟩
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨hlen1, h1⟩ := step_agree p g (hgs g (by simp)) w w' hlen h
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) (stepW w g) (stepW w' g) hlen1 h1

end PEqualNP.Outside.L_meta_2016

theorem PEqualNP.Outside.L_meta_2016 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → (∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x5.inputs) ∧ ∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x5.inputs := by
  intro x1 C hFirst hFun
  cases hgates : C.gates with
  | nil =>
    exfalso
    have h := hFirst (fun _ : Fin 9 => true)
    rw [PEqualNP.Outside.L_meta_2016.wires_eq, hgates] at h
    simp only [List.foldl_nil] at h
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp : (List.ofFn (fun _ : Fin 9 => true)).length ≤ 9)] at h
    simp at h
  | cons g0 rest =>
    have hwires : ∀ z : Fin 9 → Bool,
        C.wires (List.ofFn z) = rest.foldl PEqualNP.Outside.L_meta_2016.stepW (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn z) g0) := by
      intro z
      rw [PEqualNP.Outside.L_meta_2016.wires_eq, hgates, List.foldl_cons]
    have hb : ∀ z : Fin 9 → Bool,
        (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn z) g0).getD 9 false = (z 0 || z 4) := by
      intro z
      have h := hFirst z
      rw [hwires z] at h
      rw [PEqualNP.Outside.L_meta_2016.preserved rest _ 9 (by rw [PEqualNP.Outside.L_meta_2016.stepW_len]; simp)] at h
      exact h
    constructor
    · by_contra hno
      push_neg at hno
      have hno_rest : ∀ g ∈ rest, (0 : ℕ) ∉ g.inputs := by
        intro g hg
        exact hno g (by simpa [hgates] using hg)
      have hout : C.output ≠ 0 := by
        intro hout0
        have hcongr := congr_fun hFun (fun i : Fin 9 => decide (i = 0))
        simp only [PEqualNP.MetaComplexity.circuitFun] at hcongr
        have h0 : C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0))) = true := by
          simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, hout0]
          rw [PEqualNP.Outside.L_meta_2016.wires_eq, PEqualNP.Outside.L_meta_2016.preserved C.gates (List.ofFn (fun i : Fin 9 => decide (i = 0))) 0 (by simp)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp
        have hx1e : x1 (fun i : Fin 9 => decide (i = 0)) = false := by
          decide
        rw [h0, hx1e] at hcongr
        exact absurd hcongr (by simp)
      let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4 ∨ i = 5)
      let y : Fin 9 → Bool := Function.update x 0 false
      have hx4 : x 4 = true := by decide
      have hy4 : y 4 = true := by
        simp only [y, Function.update_apply, if_neg (by decide : ¬ ((4 : Fin 9) = 0))]
        decide
      have hbxy : (x 0 || x 4) = (y 0 || y 4) := by
        have hy0 : y 0 = false := by simp [y]
        rw [hy0, hx4, hy4]; rfl
      have hinit : ∀ i, i ≠ 0 → (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn x) g0).getD i false =
          (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn y) g0).getD i false := by
        intro i hi
        simp only [PEqualNP.Outside.L_meta_2016.stepW]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        by_cases hlt : i < 9
        · rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_append_left (by simpa using hlt)]
          rw [List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hlt, dif_pos hlt]
          simp only [Option.getD_some]
          have hxy : x ⟨i, hlt⟩ = y ⟨i, hlt⟩ := by
            simp only [y, Function.update_apply]
            rw [if_neg (fun h => hi (by simpa using congrArg Fin.val h))]
          rw [hxy]
        · by_cases heq : i = 9
          · subst heq
            have h1 : (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun j => (List.ofFn x).getD j false)])[9]?
                = some (g0.op.eval (g0.inputs.map fun j => (List.ofFn x).getD j false)) := by
              rw [List.getElem?_append_right (by simp)]
              simp
            have h2 : (List.ofFn y ++ [g0.op.eval (g0.inputs.map fun j => (List.ofFn y).getD j false)])[9]?
                = some (g0.op.eval (g0.inputs.map fun j => (List.ofFn y).getD j false)) := by
              rw [List.getElem?_append_right (by simp)]
              simp
            rw [h1, h2]
            simp only [Option.getD_some]
            have hbx : g0.op.eval (g0.inputs.map fun j => (List.ofFn x).getD j false) = (x 0 || x 4) := hb x
            have hby : g0.op.eval (g0.inputs.map fun j => (List.ofFn y).getD j false) = (y 0 || y 4) := hb y
            rw [hbx, hby, hbxy]
          · have hgt : 9 < i := by omega
            rw [List.getElem?_eq_none (by simp [List.length_ofFn]; omega),
                List.getElem?_eq_none (by simp [List.length_ofFn]; omega)]
      obtain ⟨hlen1, hagree⟩ :=
        PEqualNP.Outside.L_meta_2016.fold_agree 0 rest hno_rest
          (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn x) g0) (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn y) g0)
          (by rw [PEqualNP.Outside.L_meta_2016.stepW_len, PEqualNP.Outside.L_meta_2016.stepW_len]; simp)
          hinit
      have heval : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
        simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
        rw [hwires x, hwires y]
        exact hagree C.output hout
      have hxfun := congr_fun hFun x
      have hyfun := congr_fun hFun y
      simp only [PEqualNP.MetaComplexity.circuitFun] at hxfun hyfun
      have hx1 : x1 x = true := by simp only [x1, x]; decide
      have hy1 : x1 y = false := by simp only [x1, y]; decide
      rw [hx1] at hxfun
      rw [hy1] at hyfun
      rw [heval, hyfun] at hxfun
      simp at hxfun
    · by_contra hno
      push_neg at hno
      have hno_rest : ∀ g ∈ rest, (4 : ℕ) ∉ g.inputs := by
        intro g hg
        exact hno g (by simpa [hgates] using hg)
      have hout : C.output ≠ 4 := by
        intro hout4
        have hcongr := congr_fun hFun (fun i : Fin 9 => decide (i = 4))
        simp only [PEqualNP.MetaComplexity.circuitFun] at hcongr
        have h0 : C.eval (List.ofFn (fun i : Fin 9 => decide (i = 4))) = true := by
          simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, hout4]
          rw [PEqualNP.Outside.L_meta_2016.wires_eq, PEqualNP.Outside.L_meta_2016.preserved C.gates (List.ofFn (fun i : Fin 9 => decide (i = 4))) 4 (by simp)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp
        have hx1e : x1 (fun i : Fin 9 => decide (i = 4)) = false := by
          decide
        rw [h0, hx1e] at hcongr
        exact absurd hcongr (by simp)
      let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)
      let y : Fin 9 → Bool := Function.update x 4 false
      have hx0 : x 0 = true := by decide
      have hy0 : y 0 = true := by
        simp only [y, Function.update_apply, if_neg (by decide : ¬ ((0 : Fin 9) = 4))]
        decide
      have hbxy : (x 0 || x 4) = (y 0 || y 4) := by
        have hy4 : y 4 = false := by simp [y]
        rw [hy4, hx0, hy0]; rfl
      have hinit : ∀ i, i ≠ 4 → (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn x) g0).getD i false =
          (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn y) g0).getD i false := by
        intro i hi
        simp only [PEqualNP.Outside.L_meta_2016.stepW]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        by_cases hlt : i < 9
        · rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_append_left (by simpa using hlt)]
          rw [List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hlt, dif_pos hlt]
          simp only [Option.getD_some]
          have hxy : x ⟨i, hlt⟩ = y ⟨i, hlt⟩ := by
            simp only [y, Function.update_apply]
            rw [if_neg (fun h => hi (by simpa using congrArg Fin.val h))]
          rw [hxy]
        · by_cases heq : i = 9
          · subst heq
            have h1 : (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun j => (List.ofFn x).getD j false)])[9]?
                = some (g0.op.eval (g0.inputs.map fun j => (List.ofFn x).getD j false)) := by
              rw [List.getElem?_append_right (by simp)]
              simp
            have h2 : (List.ofFn y ++ [g0.op.eval (g0.inputs.map fun j => (List.ofFn y).getD j false)])[9]?
                = some (g0.op.eval (g0.inputs.map fun j => (List.ofFn y).getD j false)) := by
              rw [List.getElem?_append_right (by simp)]
              simp
            rw [h1, h2]
            simp only [Option.getD_some]
            have hbx : g0.op.eval (g0.inputs.map fun j => (List.ofFn x).getD j false) = (x 0 || x 4) := hb x
            have hby : g0.op.eval (g0.inputs.map fun j => (List.ofFn y).getD j false) = (y 0 || y 4) := hb y
            rw [hbx, hby, hbxy]
          · have hgt : 9 < i := by omega
            rw [List.getElem?_eq_none (by simp [List.length_ofFn]; omega),
                List.getElem?_eq_none (by simp [List.length_ofFn]; omega)]
      obtain ⟨hlen1, hagree⟩ :=
        PEqualNP.Outside.L_meta_2016.fold_agree 4 rest hno_rest
          (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn x) g0) (PEqualNP.Outside.L_meta_2016.stepW (List.ofFn y) g0)
          (by rw [PEqualNP.Outside.L_meta_2016.stepW_len, PEqualNP.Outside.L_meta_2016.stepW_len]; simp)
          hinit
      have heval : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
        simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
        rw [hwires x, hwires y]
        exact hagree C.output hout
      have hxfun := congr_fun hFun x
      have hyfun := congr_fun hFun y
      simp only [PEqualNP.MetaComplexity.circuitFun] at hxfun hyfun
      have hx1 : x1 x = true := by simp only [x1, x]; decide
      have hy1 : x1 y = false := by simp only [x1, y]; decide
      rw [hx1] at hxfun
      rw [hy1] at hyfun
      rw [heval, hyfun] at hxfun
      simp at hxfun
