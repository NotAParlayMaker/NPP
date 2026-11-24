import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4671

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_singleton (g : Gate) (w : List Bool) :
    evalGates [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

def remapWire (n m : ℕ) (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else m + (i - n)

def remapGateInput (n m : ℕ) (f : Fin n → Fin m) (j i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val
  else if i < n + j then m + (i - n)
  else m + j

def remapCircuit (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) : Circuit :=
  { gates := C.gates.mapIdx fun j g => ⟨g.op, g.inputs.map (remapGateInput n m f j)⟩
    output := remapWire n m f C.output }

lemma remapWire_lt (n m s : ℕ) (f : Fin n → Fin m) (u : ℕ) (hu : u < n + s) :
    remapWire n m f u < m + s := by
  unfold remapWire
  split_ifs with h
  · have := (f ⟨u, h⟩).isLt
    omega
  · omega

lemma remapCircuit_size (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) :
    (remapCircuit n m f C).size = C.size := by
  simp [remapCircuit, Circuit.size]

lemma remapCircuit_monotone2 (n m : ℕ) (f : Fin n → Fin m) (C : Circuit)
    (hM : Monotone2 C) : Monotone2 (remapCircuit n m f C) := by
  intro g hg
  simp only [remapCircuit, List.mem_iff_getElem] at hg
  rcases hg with ⟨j, hj, rfl⟩
  simp only [List.length_mapIdx] at hj
  rw [List.getElem_mapIdx]
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hM _ hmem
  exact ⟨hop, by simp [hlen]⟩

lemma getD_append_left_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_end (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma remapCircuit_wires_take (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) (y : Fin m → Bool) :
    ∀ k ≤ C.gates.length,
      (∀ (i : ℕ) (hi : i < n),
        (evalGates ((remapCircuit n m f C).gates.take k) (List.ofFn y)).getD (f ⟨i, hi⟩).val false =
        (evalGates (C.gates.take k) (List.ofFn (y ∘ f))).getD i false) ∧
      (∀ j < k,
        (evalGates ((remapCircuit n m f C).gates.take k) (List.ofFn y)).getD (m + j) false =
        (evalGates (C.gates.take k) (List.ofFn (y ∘ f))).getD (n + j) false) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun j hj => by omega⟩
    intro i hi
    simp only [List.take_zero, evalGates, List.foldl_nil, List.getD_eq_getElem?_getD]
    have h1 : (List.ofFn y)[(f ⟨i, hi⟩).val]? = some (y (f ⟨i, hi⟩)) := by
      rw [List.getElem?_ofFn]
      simp [(f ⟨i, hi⟩).isLt]
    have h2 : (List.ofFn (y ∘ f))[i]? = some (y (f ⟨i, hi⟩)) := by
      rw [List.getElem?_ofFn]
      simp [hi]
    rw [h1, h2]
  | succ k ih =>
    intro hk
    have hklt : k < C.gates.length := by omega
    obtain ⟨ih_in, ih_g⟩ := ih (by omega)
    have htakeC : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
      List.take_succ_eq_append_getElem hklt
    have hlenD : (remapCircuit n m f C).gates.length = C.gates.length := by
      simp [remapCircuit]
    have hkltD : k < (remapCircuit n m f C).gates.length := by omega
    have htakeD : (remapCircuit n m f C).gates.take (k + 1) =
        (remapCircuit n m f C).gates.take k ++ [(remapCircuit n m f C).gates[k]] :=
      List.take_succ_eq_append_getElem hkltD
    have hgateD : (remapCircuit n m f C).gates[k] =
        ⟨(C.gates[k]).op, (C.gates[k]).inputs.map (remapGateInput n m f k)⟩ := by
      simp [remapCircuit]
    set wD := evalGates ((remapCircuit n m f C).gates.take k) (List.ofFn y)
    set wC := evalGates (C.gates.take k) (List.ofFn (y ∘ f))
    have hwD_len : wD.length = m + k := by
      rw [evalGates_length, List.length_ofFn, List.length_take]
      omega
    have hwC_len : wC.length = n + k := by
      rw [evalGates_length, List.length_ofFn, List.length_take]
      omega
    have hval : ((remapCircuit n m f C).gates[k]).op.eval
          (((remapCircuit n m f C).gates[k]).inputs.map fun i => wD.getD i false) =
        (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => wC.getD i false) := by
      rw [hgateD, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u _
      simp only [Function.comp_apply]
      unfold remapGateInput
      split_ifs with hu1 hu2
      · exact ih_in u hu1
      · have hjlt : u - n < k := by omega
        have hstep := ih_g (u - n) hjlt
        have hu_eq : n + (u - n) = u := by omega
        rwa [hu_eq] at hstep
      · rw [getD_ge_length wD (m + k) (by omega), getD_ge_length wC u (by omega)]
    have heqD : evalGates ((remapCircuit n m f C).gates.take (k + 1)) (List.ofFn y) =
        wD ++ [(C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => wC.getD i false)] := by
      rw [htakeD, evalGates_append, evalGates_singleton, hval]
    have heqC : evalGates (C.gates.take (k + 1)) (List.ofFn (y ∘ f)) =
        wC ++ [(C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => wC.getD i false)] := by
      rw [htakeC, evalGates_append, evalGates_singleton]
    rw [heqD, heqC]
    constructor
    · intro i hi
      have h1 : (f ⟨i, hi⟩).val < wD.length := by have := (f ⟨i, hi⟩).isLt; omega
      have h2 : i < wC.length := by omega
      rw [getD_append_left_lt _ _ _ h1, getD_append_left_lt _ _ _ h2]
      exact ih_in i hi
    · intro j hj
      by_cases hjk : j < k
      · rw [getD_append_left_lt _ _ _ (by omega), getD_append_left_lt _ _ _ (by omega)]
        exact ih_g j hjk
      · have hjeq : j = k := by omega
        subst hjeq
        rw [← hwD_len, ← hwC_len, getD_append_end, getD_append_end]

lemma remapCircuit_wire_eq (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) (y : Fin m → Bool)
    (u : ℕ) (hu : u < n + C.size) :
    ((remapCircuit n m f C).wires (List.ofFn y)).getD (remapWire n m f u) false =
    (C.wires (List.ofFn (y ∘ f))).getD u false := by
  have htake := remapCircuit_wires_take n m f C y C.gates.length (le_refl _)
  have hlenD : (remapCircuit n m f C).gates.length = C.gates.length := by
    simp [remapCircuit]
  have hC : C.gates.take C.gates.length = C.gates := List.take_length
  have hD : (remapCircuit n m f C).gates.take C.gates.length = (remapCircuit n m f C).gates := by
    rw [← hlenD]
    exact List.take_length
  rw [hC, hD] at htake
  obtain ⟨hin, hg⟩ := htake
  unfold remapWire
  split_ifs with h
  · exact hin u h
  · have hjlt : u - n < C.gates.length := by
      change u < n + C.gates.length at hu
      omega
    have hstep := hg (u - n) hjlt
    have hu_eq : n + (u - n) = u := by omega
    rwa [hu_eq] at hstep

end PEqualNP.Outside.L_meta_4671

theorem PEqualNP.Outside.L_meta_4671 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size = x4.size ∧ x9.output < x2 + x9.size ∧ x10 < x2 + x9.size ∧ ∀ (x11 : Fin x2 → Bool), x9.eval (List.ofFn x11) = x4.eval (List.ofFn (x11 ∘ x3)) ∧ (x9.wires (List.ofFn x11)).getD x10 Bool.false = (x4.wires (List.ofFn (x11 ∘ x3))).getD x5 Bool.false := by
  intro n m f C w hM hout hw
  refine ⟨PEqualNP.Outside.L_meta_4671.remapCircuit n m f C,
    PEqualNP.Outside.L_meta_4671.remapWire n m f w,
    PEqualNP.Outside.L_meta_4671.remapCircuit_monotone2 n m f C hM,
    PEqualNP.Outside.L_meta_4671.remapCircuit_size n m f C, ?_, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_4671.remapCircuit_size]
    exact PEqualNP.Outside.L_meta_4671.remapWire_lt n m C.size f C.output hout
  · rw [PEqualNP.Outside.L_meta_4671.remapCircuit_size]
    exact PEqualNP.Outside.L_meta_4671.remapWire_lt n m C.size f w hw
  · intro y
    exact ⟨PEqualNP.Outside.L_meta_4671.remapCircuit_wire_eq n m f C y C.output hout,
      PEqualNP.Outside.L_meta_4671.remapCircuit_wire_eq n m f C y w hw⟩
