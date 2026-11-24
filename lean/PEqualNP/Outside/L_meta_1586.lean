import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1586

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

lemma eval_eq {n : ℕ} (gates : List Gate) (u w : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = value ⟨gates, u⟩ x w := rfl

def Cl (N : ℕ) (gates : List Gate) (S : Set ℕ) : Prop :=
  ∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
    ∀ a ∈ (gates.get i).inputs, a ∈ S

lemma reach_step (N : ℕ) (gates : List Gate) (u w : ℕ)
    (hw : ∀ S : Set ℕ, u ∈ S → Cl N gates S → w ∈ S)
    (i : Fin gates.length) (hi : w = N + (i : ℕ)) (hop : (gates.get i).op = GateOp.or)
    (a : ℕ) (ha : a ∈ (gates.get i).inputs) :
    ∀ S : Set ℕ, u ∈ S → Cl N gates S → a ∈ S := by
  intro S hu hS
  exact hS i (hi ▸ hw S hu hS) hop a ha

lemma part1 (N : ℕ) (gates : List Gate) (u : ℕ) (x : Fin N → Bool)
    (hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hu : value ⟨gates, u⟩ x u = false) (Y : ℕ)
    (hY : ∀ S : Set ℕ, u ∈ S → Cl N gates S → Y ∈ S) : value ⟨gates, u⟩ x Y = false := by
  apply hY {w | value ⟨gates, u⟩ x w = false} hu
  intro i hi hop a ha
  simp only [Set.mem_ofPred_eq] at hi ⊢
  have hk : (i : ℕ) < (⟨gates, u⟩ : Circuit).gates.length := i.2
  have hop' : (⟨gates, u⟩ : Circuit).gates[(i : ℕ)].op = GateOp.or := hop
  have h := or_value (n := N) ⟨gates, u⟩ i hk hop' x
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have : value ⟨gates, u⟩ x (N + (i : ℕ)) = true := h.2 ⟨a, ha, (hwf i).2 a ha, hc⟩
  rw [hi] at this
  exact Bool.false_ne_true this

end PEqualNP.Outside.L_meta_1586

open PEqualNP.Outside.L_meta_1586

theorem PEqualNP.Outside.L_meta_1586 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hg hwf hu
  simp only [eval_eq gates u] at hu ⊢
  have P2 : ∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → Cl N gates S → (p : ℕ) ∈ S) → p ∈ L i0 := by
    intro p hp
    have h := part1 N gates u _ hwf hu p hp
    rw [input_value] at h
    simpa using h
  refine ⟨fun Y hY => part1 N gates u _ hwf hu Y hY, P2, ?_, ?_⟩
  · intro r _ hval
    have key : ∀ w : ℕ, (∀ S : Set ℕ, u ∈ S → Cl N gates S → w ∈ S) →
        value ⟨gates, u⟩ (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) w = true →
        ((∀ S : Set ℕ, u ∈ S → Cl N gates S → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → Cl N gates S → a ∈ S) ∧
          (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
          value ⟨gates, u⟩ (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) a = true) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hv
        by_cases hn : w < N
        · have hpL := P2 ⟨w, hn⟩ hw
          have hv' := hv
          change value ⟨gates, u⟩ (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) ((⟨w, hn⟩ : Fin N) : ℕ) = true at hv'
          rw [input_value] at hv'
          simp only [decide_eq_true_eq] at hv'
          rcases hv' with h1 | h1
          · exact absurd hpL h1
          · left
            have : w = (r : ℕ) := by rw [← h1]
            rw [← this]; exact hw
        by_cases hw2 : w < N + gates.length
        · have hk : w - N < gates.length := by omega
          have hwk : w = N + (w - N) := by omega
          rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
          · right
            exact ⟨w, hw, ⟨⟨w - N, hk⟩, hwk, hop⟩, hv⟩
          · have hv2 : value ⟨gates, u⟩ (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) (N + (w - N)) = true := by
              rw [← hwk]; exact hv
            obtain ⟨a, ha, hlt, hva⟩ := (or_value (n := N) ⟨gates, u⟩ (w - N) hk hop _).1 hv2
            exact ih a (by omega) (reach_step N gates u w hw ⟨w - N, hk⟩ hwk hop a ha) hva
        · rw [missing_value (n := N) ⟨gates, u⟩ _ w (show N + gates.length ≤ w by omega)] at hv
          exact absurd hv Bool.false_ne_true
    exact key u (fun S hu _ => hu) hval
  · intro a c hop _ hc _ r _ hv
    exact ((and_value (n := N) ⟨gates, u⟩ a a.2 hop _).1 hv c hc).2
