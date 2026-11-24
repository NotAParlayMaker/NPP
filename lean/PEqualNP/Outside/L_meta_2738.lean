import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2738

open PEqualNP.CircuitLowerBounds

-- Where a wire read by the gate at position k goes in the new circuit: the 10 inputs stay,
-- the wire of an earlier gate moves up by two, and a wire that does not exist yet (it reads
-- false) becomes the constant false input 10.
def rf (k a : ℕ) : ℕ := if a < 10 then a else if a < 10 + k then a + 2 else 10

-- The new gate, from the old operation and the moved wires. Wire 10 is false, wire 11 is true.
def ngL (op : GateOp) (l : List ℕ) : Gate :=
  match op, l with
  | GateOp.and, [] => ⟨GateOp.or, [10, 11]⟩
  | GateOp.and, [a] => ⟨GateOp.and, [a, 11]⟩
  | GateOp.and, [a, b] => if a = b then ⟨GateOp.and, [a, 11]⟩ else ⟨GateOp.and, [a, b]⟩
  | GateOp.or, [] => ⟨GateOp.and, [10, 11]⟩
  | GateOp.or, [a] => if a = 10 then ⟨GateOp.and, [10, 11]⟩ else ⟨GateOp.or, [a, 10]⟩
  | GateOp.or, [a, b] =>
      if a = b then (if a = 10 then ⟨GateOp.and, [10, 11]⟩ else ⟨GateOp.or, [a, 10]⟩)
      else ⟨GateOp.or, [a, b]⟩
  | GateOp.not, [] => ⟨GateOp.not, [10]⟩
  | GateOp.not, a :: _ => ⟨GateOp.not, [a]⟩
  | _, _ => ⟨GateOp.and, [10, 11]⟩

def ng (k : ℕ) (g : Gate) : Gate := ngL g.op (g.inputs.map (rf k))

def nm : List Gate → ℕ → List Gate
  | [], _ => []
  | g :: gs, k => ng k g :: nm gs (k + 1)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    ({ gates := gs, output := o } : Circuit).wires x = run gs x := rfl

def Inv (k : ℕ) (w w' : List Bool) : Prop :=
  w.length = 10 + k ∧ w'.length = 12 + k ∧ w'.getD 10 false = false ∧
    w'.getD 11 false = true ∧ ∀ a, w'.getD (rf k a) false = w.getD a false

theorem getD_lt {l t : List Bool} {i : ℕ} (h : i < l.length) :
    (l ++ t).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_last {l : List Bool} {b : Bool} {i : ℕ} (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst h
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {l : List Bool} {i : ℕ} (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem rf_lt (k a : ℕ) : rf k a < 12 + k := by
  unfold rf
  split_ifs <;> omega

theorem rf_ne (k a : ℕ) : rf k a ≠ 11 := by
  unfold rf
  split_ifs <;> omega

theorem ngL_eval (op : GateOp) (l : List ℕ) (w : List Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : l.length ≤ 2)
    (h10 : w.getD 10 false = false) (h11 : w.getD 11 false = true) :
    (ngL op l).op.eval ((ngL op l).inputs.map fun i => w.getD i false) =
      op.eval (l.map fun i => w.getD i false) := by
  rw [List.getD_eq_getElem?_getD] at h10 h11
  rcases hop with rfl | rfl | rfl
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [ngL, GateOp.eval, h10, h11]
    · simp [ngL, GateOp.eval, h11]
    · by_cases hab : a = b
      · subst hab
        simp [ngL, GateOp.eval, h11]
      · simp [ngL, GateOp.eval, hab]
    · simp at hl
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [ngL, GateOp.eval, h10, h11]
    · by_cases ha : a = 10
      · subst ha
        simp [ngL, GateOp.eval, h10, h11]
      · simp [ngL, GateOp.eval, ha, h10]
    · by_cases hab : a = b
      · subst hab
        by_cases ha : a = 10
        · subst ha
          simp [ngL, GateOp.eval, h10, h11]
        · simp [ngL, GateOp.eval, ha, h10]
      · simp [ngL, GateOp.eval, hab]
    · simp at hl
  · rcases l with _ | ⟨a, l⟩
    · simp [ngL, GateOp.eval, h10]
    · simp [ngL, GateOp.eval]

theorem ngL_shape (op : GateOp) (l : List ℕ) (hl : ∀ a ∈ l, a ≠ 11) :
    (∀ i ∈ (ngL op l).inputs, i ∈ l ∨ i = 10 ∨ i = 11) ∧ (ngL op l).inputs.Nodup ∧
    ((ngL op l).op = GateOp.not ∧ (ngL op l).inputs.length = 1 ∨
      (ngL op l).op ≠ GateOp.not ∧ (ngL op l).inputs.length = 2) ∧
    ((ngL op l).op = GateOp.and ∨ (ngL op l).op = GateOp.or ∨ (ngL op l).op = GateOp.not) := by
  cases op <;> rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl <;>
    simp only [ngL] <;> (try split_ifs) <;> simp_all <;> omega

theorem ng_shape (k : ℕ) (g : Gate) :
    (∀ i ∈ (ng k g).inputs, i < 12 + k) ∧ (ng k g).inputs.Nodup ∧
    ((ng k g).op = GateOp.not ∧ (ng k g).inputs.length = 1 ∨
      (ng k g).op ≠ GateOp.not ∧ (ng k g).inputs.length = 2) ∧
    ((ng k g).op = GateOp.and ∨ (ng k g).op = GateOp.or ∨ (ng k g).op = GateOp.not) := by
  have hne : ∀ a ∈ g.inputs.map (rf k), a ≠ 11 := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact rf_ne k b
  obtain ⟨h1, h2, h3, h4⟩ := ngL_shape g.op (g.inputs.map (rf k)) hne
  refine ⟨?_, h2, h3, h4⟩
  intro i hi
  rcases h1 i hi with h | h | h
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
    exact rf_lt k b
  · omega
  · omega

theorem step_inv {k : ℕ} {w w' : List Bool} (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hl : g.inputs.length ≤ 2)
    (h : Inv k w w') : Inv (k + 1) (step w g) (step w' (ng k g)) := by
  obtain ⟨hw, hw', h10, h11, hall⟩ := h
  have hval : (ng k g).op.eval ((ng k g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    have e : (g.inputs.map (rf k)).map (fun j => w'.getD j false) =
        g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => hall i)
    unfold ng
    rw [ngL_eval g.op (g.inputs.map (rf k)) w' hop (by simpa using hl) h10 h11, e]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [step, hw]
    omega
  · simp [step, hw']
    omega
  · unfold step
    rw [getD_lt (by omega)]
    exact h10
  · unfold step
    rw [getD_lt (by omega)]
    exact h11
  · intro a
    unfold step
    rw [hval]
    by_cases ha : a < 10
    · have e1 : rf (k + 1) a = a := by unfold rf; split_ifs <;> omega
      have e2 : rf k a = a := by unfold rf; split_ifs <;> omega
      have := hall a
      rw [e2] at this
      rw [e1, getD_lt (by omega), getD_lt (by omega), this]
    · by_cases hb : a < 10 + k
      · have e1 : rf (k + 1) a = a + 2 := by unfold rf; split_ifs <;> omega
        have e2 : rf k a = a + 2 := by unfold rf; split_ifs <;> omega
        have := hall a
        rw [e2] at this
        rw [e1, getD_lt (by omega), getD_lt (by omega), this]
      · by_cases hc : a = 10 + k
        · have e1 : rf (k + 1) a = a + 2 := by unfold rf; split_ifs <;> omega
          rw [e1, getD_last (by omega), getD_last (by omega)]
        · have e1 : rf (k + 1) a = 10 := by unfold rf; split_ifs <;> omega
          rw [e1, getD_lt (by omega), h10, getD_ge (by simp; omega)]

theorem run_inv : ∀ (gs : List Gate) (k : ℕ) (w w' : List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    Inv k w w' → Inv (k + gs.length) (run gs w) (run (nm gs k) w')
  | [], k, w, w', _, h => by simpa [run, nm] using h
  | g :: gs, k, w, w', hg, h => by
    have hg0 := hg g (List.mem_cons_self ..)
    have h1 := step_inv g hg0.1 hg0.2 h
    have h2 := run_inv gs (k + 1) (step w g) (step w' (ng k g))
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) h1
    have e : k + (g :: gs).length = k + 1 + gs.length := by simp; omega
    rw [e]
    exact h2

theorem nm_length : ∀ (gs : List Gate) (k : ℕ), (nm gs k).length = gs.length
  | [], _ => rfl
  | _ :: gs, k => by simp [nm, nm_length gs (k + 1)]

theorem nm_get : ∀ (gs : List Gate) (k i : ℕ) (h : i < (nm gs k).length),
    ∃ g, (nm gs k)[i] = ng (k + i) g
  | [], _, i, h => by simp [nm] at h
  | g :: gs, k, 0, _ => ⟨g, by simp [nm]⟩
  | g :: gs, k, i + 1, h => by
    have h' : i < (nm gs (k + 1)).length := by
      simp only [nm, List.length_cons] at h
      omega
    obtain ⟨g', hg'⟩ := nm_get gs (k + 1) i h'
    refine ⟨g', ?_⟩
    simp only [nm, List.getElem_cons_succ]
    rw [hg']
    congr 1
    omega

theorem nm_mem : ∀ (gs : List Gate) (k : ℕ) (g' : Gate), g' ∈ nm gs k → ∃ j g, g' = ng j g
  | [], _, _, h => by simp [nm] at h
  | g :: gs, k, g', h => by
    simp only [nm, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, g, h⟩
    · exact nm_mem gs (k + 1) g' h

end PEqualNP.Outside.L_meta_2738

theorem PEqualNP.Outside.L_meta_2738 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     x2 < x3 →       x3 < (10 : ℕ) + x1.length →         ∃ (x7 : List PEqualNP.CircuitLowerBounds.Gate) (x8 : ℕ) (x9 : ℕ),           x7.length ≤ x1.length ∧             x8 < (12 : ℕ) + x7.length ∧               x9 < (12 : ℕ) + x7.length ∧                 PEqualNP.MetaComplexity.FanInTwo { gates := x7, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧                   (∀ (x10 : Fin x7.length),                       have x11 : PEqualNP.CircuitLowerBounds.Gate := x7.get x10;                       (∀ x12 ∈ x11.inputs, x12 < (12 : ℕ) + ↑x10) ∧ x11.inputs.Nodup ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (1 : ℕ) ∨ x11.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (2 : ℕ))) ∧                     ∀ (x10 : List Bool), x10.length = (10 : ℕ) → ({ gates := x7, output := x8 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true]) || { gates := x7, output := x9 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true])) = ({ gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10 || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10) := by
  intro x1 x2 x3 hfan h23 h3
  have hg : ∀ g ∈ x1, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hfan g hg
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  refine ⟨PEqualNP.Outside.L_meta_2738.nm x1 0, PEqualNP.Outside.L_meta_2738.rf x1.length x2,
    PEqualNP.Outside.L_meta_2738.rf x1.length x3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_2738.nm_length]
  · rw [PEqualNP.Outside.L_meta_2738.nm_length]
    unfold PEqualNP.Outside.L_meta_2738.rf
    split_ifs <;> omega
  · rw [PEqualNP.Outside.L_meta_2738.nm_length]
    unfold PEqualNP.Outside.L_meta_2738.rf
    split_ifs <;> omega
  · intro g' hg'
    obtain ⟨j, g, rfl⟩ := PEqualNP.Outside.L_meta_2738.nm_mem x1 0 g' hg'
    obtain ⟨_, _, h3', h4'⟩ := PEqualNP.Outside.L_meta_2738.ng_shape j g
    refine ⟨?_, ?_⟩
    · rcases h4' with h | h | h <;> simp [h]
    · rcases h3' with h | h <;> omega
  · intro i
    obtain ⟨g, hg'⟩ := PEqualNP.Outside.L_meta_2738.nm_get x1 0 i.val i.isLt
    have e : (PEqualNP.Outside.L_meta_2738.nm x1 0).get i =
        PEqualNP.Outside.L_meta_2738.ng i.val g := by
      rw [List.get_eq_getElem, hg', Nat.zero_add]
    obtain ⟨s1, s2, s3, _⟩ := PEqualNP.Outside.L_meta_2738.ng_shape i.val g
    show (∀ x12 ∈ ((PEqualNP.Outside.L_meta_2738.nm x1 0).get i).inputs, x12 < 12 + ↑i) ∧ _ ∧ _
    rw [e]
    exact ⟨s1, s2, s3⟩
  · intro x hx
    have h0 : PEqualNP.Outside.L_meta_2738.Inv 0 x (x ++ [false, true]) := by
      refine ⟨by simp [hx], by simp [hx], ?_, ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [hx]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [hx]
      · intro a
        by_cases ha : a < 10
        · have e1 : PEqualNP.Outside.L_meta_2738.rf 0 a = a := by
            unfold PEqualNP.Outside.L_meta_2738.rf
            split_ifs <;> omega
          rw [e1, PEqualNP.Outside.L_meta_2738.getD_lt (by omega)]
        · have e1 : PEqualNP.Outside.L_meta_2738.rf 0 a = 10 := by
            unfold PEqualNP.Outside.L_meta_2738.rf
            split_ifs <;> omega
          rw [e1, PEqualNP.Outside.L_meta_2738.getD_ge (l := x) (by omega),
            List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          simp [hx]
    obtain ⟨_, _, _, _, hall⟩ :=
      PEqualNP.Outside.L_meta_2738.run_inv x1 0 x (x ++ [false, true]) hg h0
    rw [Nat.zero_add] at hall
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.Outside.L_meta_2738.wires_eq]
    rw [hall x2, hall x3]
