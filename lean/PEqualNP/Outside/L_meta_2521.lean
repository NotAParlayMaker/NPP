import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2521

open PEqualNP.CircuitLowerBounds

def step (X : Finset (Fin 9 → Bool)) (d : List (Finset (Fin 9 → Bool))) (g : Gate) :
    Finset (Fin 9 → Bool) :=
  match g.op, g.inputs with
  | GateOp.and, [] => X \ d.getD d.length ∅
  | GateOp.and, [a] => d.getD a ∅ ∩ d.getD a ∅
  | GateOp.and, [a, b] => d.getD a ∅ ∩ d.getD b ∅
  | GateOp.or, [] => d.getD d.length ∅ ∪ d.getD d.length ∅
  | GateOp.or, [a] => d.getD a ∅ ∪ d.getD a ∅
  | GateOp.or, [a, b] => d.getD a ∅ ∪ d.getD b ∅
  | GateOp.not, [] => X \ d.getD d.length ∅
  | GateOp.not, a :: _ => X \ d.getD a ∅
  | _, _ => d.getD 0 ∅ ∪ d.getD 0 ∅

lemma step_form (X : Finset (Fin 9 → Bool)) (d : List (Finset (Fin 9 → Bool))) (g : Gate) :
    ∃ a b : ℕ, step X d g = d.getD a ∅ ∪ d.getD b ∅ ∨ step X d g = d.getD a ∅ ∩ d.getD b ∅ ∨
      step X d g = X \ d.getD a ∅ := by
  unfold step
  split
  all_goals first
    | exact ⟨_, _, Or.inl rfl⟩
    | exact ⟨_, _, Or.inr (Or.inl rfl)⟩
    | exact ⟨_, 0, Or.inr (Or.inr rfl)⟩

def build (X : Finset (Fin 9 → Bool)) :
    List (Finset (Fin 9 → Bool)) → List Gate → List (Finset (Fin 9 → Bool))
  | _, [] => []
  | d, g :: gs => step X d g :: build X (d ++ [step X d g]) gs

lemma build_length (X : Finset (Fin 9 → Bool)) :
    ∀ (d : List (Finset (Fin 9 → Bool))) (gs : List Gate), (build X d gs).length = gs.length
  | _, [] => rfl
  | d, g :: gs => by simp [build, build_length X _ gs]

lemma build_form (X : Finset (Fin 9 → Bool)) :
    ∀ (gs : List Gate) (d : List (Finset (Fin 9 → Bool))) (j : ℕ), j < (build X d gs).length →
      ∃ a b : ℕ,
        (build X d gs).getD j ∅ = (d ++ List.take j (build X d gs)).getD a ∅ ∪
            (d ++ List.take j (build X d gs)).getD b ∅ ∨
        (build X d gs).getD j ∅ = (d ++ List.take j (build X d gs)).getD a ∅ ∩
            (d ++ List.take j (build X d gs)).getD b ∅ ∨
        (build X d gs).getD j ∅ = X \ (d ++ List.take j (build X d gs)).getD a ∅
  | [], d, j, h => by simp [build] at h
  | g :: gs, d, 0, _ => by simpa [build] using step_form X d g
  | g :: gs, d, j + 1, h => by
      have h' : j < (build X (d ++ [step X d g]) gs).length := by
        simp only [build, List.length_cons] at h
        omega
      simpa [build, List.append_assoc] using build_form X gs (d ++ [step X d g]) j h'

lemma step_eval (X : Finset (Fin 9 → Bool)) (x : Fin 9 → Bool) (hx : x ∈ X)
    (d : List (Finset (Fin 9 → Bool))) (w : List Bool)
    (hinv : ∀ i, w.getD i false = true ↔ x ∈ d.getD i ∅) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true ↔ x ∈ step X d g := by
  have hend : d.getD d.length ∅ = ∅ := List.getD_eq_default _ _ (le_refl _)
  have hinv' : ∀ i, w.getD i false = false ↔ x ∉ d.getD i ∅ := by
    intro i
    rw [← hinv i]
    simp
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [step, GateOp.eval]

lemma run (X : Finset (Fin 9 → Bool)) (x : Fin 9 → Bool) (hx : x ∈ X) :
    ∀ (gs : List Gate) (d : List (Finset (Fin 9 → Bool))) (w : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) →
      d.length = w.length →
      (∀ i, w.getD i false = true ↔ x ∈ d.getD i ∅) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          w).getD i false = true ↔ x ∈ (d ++ build X d gs).getD i ∅
  | [], d, w, _, _, hinv, i => by simpa [build] using hinv i
  | g :: gs, d, w, hg, hlen, hinv, i => by
      have hg0 := hg g (by simp)
      have key := step_eval X x hx d w hinv g hg0.1 hg0.2
      have hrest : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g'.inputs.length ≤ 2 := fun g' hg' => hg g' (by simp [hg'])
      have hinv2 : ∀ j, (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD j false
          = true ↔ x ∈ (d ++ [step X d g]).getD j ∅ := by
        intro j
        rcases lt_trichotomy j d.length with h | h | h
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ h]
          exact hinv j
        · subst h
          rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
          simpa [hlen] using key
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
          simp
      have := run X x hx gs (d ++ [step X d g]) _ hrest (by simp [hlen]) hinv2 i
      simpa [build, List.foldl_cons, List.append_assoc] using this

end PEqualNP.Outside.L_meta_2521

theorem PEqualNP.Outside.L_meta_2521 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ) → Bool)),   PEqualNP.MetaComplexity.FanInTwo x1 →     ∃ (x4 : List (Finset (Fin (9 : ℕ) → Bool))),       have x5 : ℕ → List (Finset (Fin (9 : ℕ) → Bool)) := fun (x5 : ℕ) => (List.ofFn fun (x6 : Fin (9 : ℕ)) => {x7 ∈ x2 | x7 x6 = Bool.true}) ++ [∅] ++ List.take x5 x4;       x4.length = x1.size ∧         (∀ x6 < x4.length,             have x8 : ℕ → Finset (Fin (9 : ℕ) → Bool) := fun (x8 : ℕ) => (x5 x6).getD x8 ∅;             ∃ (x9 : ℕ) (x10 : ℕ), x4.getD x6 ∅ = x8 x9 ∪ x8 x10 ∨ x4.getD x6 ∅ = x8 x9 ∩ x8 x10 ∨ x4.getD x6 ∅ = x2 \ x8 x9) ∧           ∀ x6 ∈ x2, x1.eval (List.ofFn x6 ++ [Bool.false]) = Bool.true ↔ x6 ∈ (x5 x4.length).getD x1.output ∅ := by
  intro C X hC
  refine ⟨PEqualNP.Outside.L_meta_2521.build X
    ((List.ofFn fun i : Fin 9 => {x7 ∈ X | x7 i = Bool.true}) ++ [∅]) C.gates, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_2521.build_length, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro j hj
    obtain ⟨a, b, h⟩ := PEqualNP.Outside.L_meta_2521.build_form X C.gates _ j hj
    exact ⟨a, b, by simpa only [List.append_assoc] using h⟩
  · intro x hx
    have hinit : ∀ i, (List.ofFn x ++ [Bool.false]).getD i false = true ↔
        x ∈ ((List.ofFn fun i : Fin 9 => X.filter (fun x7 : Fin 9 → Bool => x7 i = Bool.true)) ++ [∅]).getD i ∅ := by
      intro i
      rcases lt_trichotomy i 9 with h | h | h
      · rw [List.getD_append _ _ _ _ (by simp [h]), List.getD_append _ _ _ _ (by simp [h])]
        interval_cases i <;> simp [List.getD_eq_getElem?_getD, hx]
      · subst h
        simp [List.getD_eq_getElem?_getD]
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
        simp
    have hg : ∀ g ∈ C.gates,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        g.inputs.length ≤ 2 := hC
    have := PEqualNP.Outside.L_meta_2521.run X x hx C.gates _ _ hg (by simp) hinit C.output
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [this]
    simp
