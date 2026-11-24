import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1645

-- wire evaluation helpers adapted from lean/PEqualNP/Outside/L_meta_1613.lean
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

lemma hmono {N : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) (hw : w < N + (j : ℕ)) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N
    · let p : Fin N := ⟨w, hn⟩
      change value ⟨gates, 0⟩ x p = true → value ⟨gates, 0⟩ y p = true
      simpa only [input_value] using hxy p
    · have hk : w - N < gates.length := by
        have := j.isLt
        omega
      have hwk : w = N + (w - N) := by omega
      rw [hwk]
      have hop : gates[w - N].op = GateOp.and ∨ gates[w - N].op = GateOp.or := by
        rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have h1 := hone ⟨w - N, hk⟩ h
          have h2 : w - N = (j : ℕ) := congrArg Fin.val h1
          omega
      exact gate_mono (n := N) ⟨gates, 0⟩ (w - N) hk hop x y fun r _ hlt => ih r (by omega) (by omega)

lemma monoD {N : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (D : (Fin N → Bool) → Prop)
    (hj : ∀ x, D x → value (⟨gates, 0⟩ : Circuit) x (N + (j : ℕ)) = true)
    (x y : Fin N → Bool) (hy : D y) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    value (⟨gates, 0⟩ : Circuit) x w = true → value (⟨gates, 0⟩ : Circuit) y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N
    · let p : Fin N := ⟨w, hn⟩
      change value ⟨gates, 0⟩ x p = true → value ⟨gates, 0⟩ y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < N + gates.length
    · have hk : w - N < gates.length := by omega
      have hwk : w = N + (w - N) := by omega
      by_cases hkj : w - N = (j : ℕ)
      · intro _
        rw [hwk, hkj]
        exact hj y hy
      · rw [hwk]
        have hop : gates[w - N].op = GateOp.and ∨ gates[w - N].op = GateOp.or := by
          rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · have h1 := hone ⟨w - N, hk⟩ h
            have h2 : w - N = (j : ℕ) := congrArg Fin.val h1
            exact absurd h2 hkj
        exact gate_mono (n := N) ⟨gates, 0⟩ (w - N) hk hop x y fun r _ hlt => ih r (by omega)
    · intro hv
      rw [missing_value (⟨gates, 0⟩ : Circuit) x w (by simp [Circuit.size]; omega)] at hv
      exact absurd hv (by simp)

end PEqualNP.Outside.L_meta_1645

theorem PEqualNP.Outside.L_meta_1645 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 hq hN hcard hint hcov hp01 hp0 hp1 gates o j h hg hwf hjnot hone hhj hjin hout ev hev he0 he1 heo hco
  have hevV : ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = PEqualNP.Outside.L_meta_1645.value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x w := by
    intro w x
    rw [hev]
    rfl
  simp only [hevV] at he0 he1 heo hco ⊢
  have hnotv : ∀ x : Fin N → Bool,
      PEqualNP.Outside.L_meta_1645.value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x (N + (j : ℕ)) =
        !(PEqualNP.Outside.L_meta_1645.value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x (N + (h : ℕ))) := by
    intro x
    have hx := PEqualNP.Outside.L_meta_1645.gate_value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x
      (N + (j : ℕ)) (by omega) (by simp [PEqualNP.CircuitLowerBounds.Circuit.size])
    simp only [Nat.add_sub_cancel_left] at hx
    obtain ⟨r, hr⟩ := hjin
    rw [List.get_eq_getElem] at hjnot hr
    rw [hx]
    have hlt : N + (h : ℕ) < N + (j : ℕ) := by omega
    simp only [hjnot, hr, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.headD_cons, hlt, ite_true]
  have hD : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) →
      PEqualNP.Outside.L_meta_1645.value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x (N + (h : ℕ)) = false ∧
      PEqualNP.Outside.L_meta_1645.value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x (N + (j : ℕ)) = true := by
    intro x hx
    have hf : PEqualNP.Outside.L_meta_1645.value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x (N + (h : ℕ)) = false := by
      by_contra hc
      have ht : PEqualNP.Outside.L_meta_1645.value (⟨gates, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x (N + (h : ℕ)) = true := by
        simpa using hc
      have := PEqualNP.Outside.L_meta_1645.hmono gates j hg hone x (fun v : Fin N => decide (v ∉ L i0))
        (fun v hv => by simpa using hx v hv) (N + (h : ℕ)) (by omega) ht
      rw [hco] at this
      exact absurd this (by simp)
    refine ⟨hf, ?_⟩
    rw [hnotv, hf]
    rfl
  refine ⟨hD, ?_, ?_, ?_, ?_⟩
  · intro w hw hw0 hw1
    have hf := heo w hw0 hw1
    refine ⟨hf, ?_⟩
    rw [hnotv, hf]
    rfl
  · rw [hnotv, he0]
    rfl
  · rw [hnotv, he1]
    rfl
  · intro w x y _ hy hxy
    exact PEqualNP.Outside.L_meta_1645.monoD gates j hg hone
      (fun z : Fin N → Bool => ∀ v : Fin N, z v = true → v ∉ L i0)
      (fun z hz => (hD z hz).2) x y hy hxy w
