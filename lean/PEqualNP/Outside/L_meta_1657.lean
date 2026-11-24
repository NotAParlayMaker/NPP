import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1657

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

def patchC (gates : List Gate) (j : ℕ) : Circuit :=
  ⟨gates.set j ⟨GateOp.or, []⟩, 0⟩

lemma patchC_size (gates : List Gate) (j : ℕ) : (patchC gates j).size = gates.length := by
  simp [patchC, Circuit.size]

lemma patchC_good (gates : List Gate) (j : Fin gates.length)
    (valid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j) :
    ∀ g ∈ (patchC gates j.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [patchC] using hk
  by_cases hkj : j.val = k
  · simp [patchC, hkj]
  · have same : (patchC gates j.val).gates[k] = gates[k] := by simp [patchC, hkj]
    rw [same]
    obtain ⟨hop, hfan⟩ := valid gates[k] (List.getElem_mem _)
    refine ⟨?_, hfan⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (unique ⟨k, hk'⟩ hop)).symm hkj

lemma patchC_false {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool) :
    value (patchC gates j.val) x (n + j.val) = false := by
  have h := gate_value (patchC gates j.val) x (n + j.val) (by omega)
    (by rw [patchC_size]; omega)
  simp only at h
  rw [h]
  simp [patchC, GateOp.eval]

lemma patchC_other {n : ℕ} (gates : List Gate) (j : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + j) :
    value (patchC gates j) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (patchC gates j) x r else false) := by
  have h := gate_value (patchC gates j) x w hn (by rw [patchC_size]; exact hw)
  simp only at h
  rw [h]
  have same : (patchC gates j).gates[w - n]'(by simp [patchC]; omega) =
      gates[w - n]'(by omega) := by
    simp only [patchC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [same]

lemma originalGateValue {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma patchEvalCongr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

lemma patchC_eq {n : ℕ} (gates : List Gate) (j : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (hjFalse : value ⟨gates, o⟩ x (n + j.val) = false) (w : ℕ) :
    value (patchC gates j.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h₁ := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h₂ := input_value (patchC gates j.val) x ⟨w, hn⟩
      simp only at h₁ h₂
      rw [h₁, h₂]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + j.val
      · rw [hne, hjFalse]
        exact patchC_false gates j x
      · rw [originalGateValue gates o x w (by omega) hw,
          patchC_other gates j.val x w (by omega) hw hne]
        apply patchEvalCongr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (patchC gates j.val) x w (by rw [patchC_size]; omega)]

lemma opMono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact h r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, h r hm hv⟩

lemma op_andor (gates : List Gate) (j : Fin gates.length)
    (valid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j)
    (k : ℕ) (hk : k < gates.length) (hkj : k ≠ j.val) :
    gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or := by
  rcases (valid gates[k] (List.getElem_mem _)).1 with hop | hop | hop
  · exact Or.inl hop
  · exact Or.inr hop
  · exact absurd (congrArg Fin.val (unique ⟨k, hk⟩ hop)) hkj

lemma patchC_le {n : ℕ} (gates : List Gate) (j : Fin gates.length) (o : ℕ)
    (valid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j)
    (x : Fin n → Bool) (w : ℕ) :
    value (patchC gates j.val) x w = true → value ⟨gates, o⟩ x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h₁ := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h₂ := input_value (patchC gates j.val) x ⟨w, hn⟩
      simp only at h₁ h₂
      intro hh
      rw [h₂] at hh
      rw [h₁]
      exact hh
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + j.val
      · rw [hne, patchC_false gates j x]
        intro hf
        exact absurd hf (by simp)
      · rw [originalGateValue gates o x w (by omega) hw,
          patchC_other gates j.val x w (by omega) hw hne]
        apply opMono _ (op_andor gates j valid unique (w - n) (by omega) (by omega))
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value (patchC gates j.val) x w (by rw [patchC_size]; omega)]
      intro hf
      exact absurd hf (by simp)

lemma patchC_reader {n : ℕ} (gates : List Gate) (j i : Fin gates.length)
    (wired : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ))
    (hmem : n + j.val ∈ (gates.get i).inputs) (hand : (gates.get i).op = GateOp.and)
    (x : Fin n → Bool) :
    value (patchC gates j.val) x (n + i.val) = false := by
  have hji : n + j.val < n + i.val := wired i _ hmem
  have hil := i.isLt
  have he := patchC_other gates j.val x (n + i.val) (by omega) (by omega) (by omega)
  simp only [Nat.add_sub_cancel_left] at he
  rw [he]
  change (gates.get i).op.eval ((gates.get i).inputs.map fun r =>
    if r < n + i.val then value (patchC gates j.val) x r else false) = false
  rw [hand]
  simp only [GateOp.eval]
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  have h3 := hall _ (List.mem_map.mpr ⟨n + j.val, hmem, rfl⟩)
  simp [hji, patchC_false gates j x] at h3

lemma patchC_agree {n : ℕ} (gates : List Gate) (j : Fin gates.length) (o : ℕ)
    (wired : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ))
    (hand : ∀ i : Fin gates.length, n + j.val ∈ (gates.get i).inputs →
      (gates.get i).op = GateOp.and)
    (x : Fin n → Bool)
    (hno : ∀ i : Fin gates.length, n + j.val ∈ (gates.get i).inputs →
      value ⟨gates, o⟩ x (n + i.val) = false)
    (w : ℕ) :
    w ≠ n + j.val → value (patchC gates j.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwj
    by_cases hn : w < n
    · have h₁ := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h₂ := input_value (patchC gates j.val) x ⟨w, hn⟩
      simp only at h₁ h₂
      rw [h₁, h₂]
    by_cases hw : w < n + gates.length
    · have hk : w - n < gates.length := by omega
      by_cases hmem : n + j.val ∈ (gates.get ⟨w - n, hk⟩).inputs
      · have h1 := hno ⟨w - n, hk⟩ hmem
        have h2 := patchC_reader gates j ⟨w - n, hk⟩ wired hmem (hand ⟨w - n, hk⟩ hmem) x
        have hwk : n + (w - n) = w := by omega
        simp only [hwk] at h1 h2
        rw [h1, h2]
      · rw [originalGateValue gates o x w (by omega) hw,
          patchC_other gates j.val x w (by omega) hw hwj]
        apply patchEvalCongr
        intro r hr'
        by_cases hr : r < w
        · have hrj : r ≠ n + j.val := by
            rintro rfl
            exact hmem hr'
          simpa [hr] using ih r hr hrj
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (patchC gates j.val) x w (by rw [patchC_size]; omega)]

lemma not_value {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (o : ℕ) (x : Fin n → Bool)
    (hop : (gates.get j).op = GateOp.not) (hlt : h < j)
    (hread : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r) :
    value ⟨gates, o⟩ x (n + j.val) = !(value ⟨gates, o⟩ x (n + h.val)) := by
  obtain ⟨r, hr⟩ := hread
  have hj : n + j.val < n + gates.length := by omega
  have hw : n + h.val < n + j.val := by exact Nat.add_lt_add_left hlt n
  have he := originalGateValue gates o x (n + j.val) (by omega) hj
  simp only [Nat.add_sub_cancel_left] at he
  rw [he]
  change (gates.get j).op.eval ((gates.get j).inputs.map fun w =>
    if w < n + j.val then value ⟨gates, o⟩ x w else false) = _
  rw [hop, hr]
  simp [hw, GateOp.eval]

end PEqualNP.Outside.L_meta_1657

open PEqualNP.Outside.L_meta_1657

theorem PEqualNP.Outside.L_meta_1657 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := by
  intro q N L va vb vc sa sb sc hq hN hcard hinter hjoin hnoncol h1 h2 h3 h4 h5 h6
    gates o j h valid wired hop unique hlt hread hcorrect hand ev ev' hev hev' hh hreaders
  have E : ∀ w x, ev w x = value ⟨gates, 0⟩ x w := fun w x => hev w x
  have E' : ∀ w x, ev' w x = value (patchC gates j.val) x w := fun w x => hev' w x
  have hC : ∀ (t : Fin N) (x : Fin N → Bool),
      value ⟨gates, 0⟩ x (o t) = decide (∃ v ∈ L t, x v = true) := fun t x => hcorrect t x
  have D : ∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false →
      ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧
        ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true := by
    intro t P hP hfalse
    by_contra hne
    push Not at hne
    have hno : ∀ i : Fin gates.length, N + j.val ∈ (gates.get i).inputs →
        value ⟨gates, 0⟩ (fun v : Fin N => decide (v = P)) (N + i.val) = false := by
      intro i hi
      have h7 := hne i hi
      rw [E] at h7
      simpa using h7
    have hoj : o t ≠ N + j.val := by
      intro heq
      have hlt2 : (L t ∪ {va, vb, vc}).card < (Finset.univ : Finset (Fin N)).card := by
        have hc1 : (L t ∪ {va, vb, vc}).card ≤
            (L t).card + ({va, vb, vc} : Finset (Fin N)).card := Finset.card_union_le _ _
        have hc2 : ({va, vb, vc} : Finset (Fin N)).card ≤ 3 := Finset.card_le_three
        rw [Finset.card_univ, Fintype.card_fin]
        have hc3 := hcard t
        have hq2 : 3 * 3 ≤ q * q := Nat.mul_le_mul hq hq
        have hq3 : q ^ 2 = q * q := sq q
        linarith
      have hex : ∃ p : Fin N, p ∉ L t ∪ {va, vb, vc} := by
        by_contra hall
        push Not at hall
        have hsub : (Finset.univ : Finset (Fin N)) ⊆ L t ∪ {va, vb, vc} := fun p _ => hall p
        have hle := Finset.card_le_card hsub
        omega
      obtain ⟨p, hp⟩ := hex
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      obtain ⟨hpL, hpa, hpb, hpc⟩ := hp
      have hz := hC t (fun v : Fin N => decide (v = p))
      rw [heq, not_value gates j h 0 _ hop hlt hread] at hz
      have hhp : value ⟨gates, 0⟩ (fun v : Fin N => decide (v = p)) (N + h.val) = false := by
        by_contra hcon
        have hcon' : ev (N + h.val) (fun v : Fin N => decide (v = p)) = true := by
          rw [E]
          simpa using hcon
        rcases (hh p).1 hcon' with r | r | r
        · exact hpa r
        · exact hpb r
        · exact hpc r
      rw [hhp] at hz
      have hdec : decide (∃ v ∈ L t, (fun v : Fin N => decide (v = p)) v = true) = false := by
        apply decide_eq_false
        rintro ⟨v, hv, hvp⟩
        have hvp' : v = p := by simpa using hvp
        exact hpL (hvp' ▸ hv)
      have hbad : (!false) = false := hz.trans hdec
      simp at hbad
    have hag := patchC_agree gates j 0 wired hand (fun v : Fin N => decide (v = P)) hno (o t) hoj
    rw [E', hag, hC] at hfalse
    have hT : decide (∃ v ∈ L t, (fun v : Fin N => decide (v = P)) v = true) = true :=
      decide_eq_true ⟨P, hP, by simp⟩
    exact Bool.false_ne_true (hfalse.symm.trans hT)
  refine ⟨?_, ?_, ?_, D, ?_⟩
  · intro w x hw
    rw [E]
    rw [E'] at hw
    exact patchC_le gates j 0 valid unique x w hw
  · intro w x hw
    rw [E] at hw
    rw [E, E']
    have hjF : value ⟨gates, 0⟩ x (N + j.val) = false := by
      simp [not_value gates j h 0 x hop hlt hread, hw]
    exact patchC_eq gates j 0 x hjF w
  · intro i x hi
    rw [E']
    exact patchC_reader gates j i wired hi (hand i hi) x
  · intro t v hv hvt
    rw [E']
    have hv' : v = va ∨ v = vb ∨ v = vc := by simpa using hv
    have hone : value (patchC gates j.val) (fun u : Fin N => decide (u = v)) (o t) = true := by
      by_contra hcon
      have hcon' : ev' (o t) (fun u : Fin N => decide (u = v)) = false := by
        rw [E']
        simpa using hcon
      obtain ⟨i, hi, hiT⟩ := D t v hvt hcon'
      obtain ⟨-, ha, hb, hc⟩ := hreaders i v hi hiT
      rcases hv' with r | r | r
      · exact ha r
      · exact hb r
      · exact hc r
    exact hone
