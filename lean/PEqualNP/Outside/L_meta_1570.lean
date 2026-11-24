import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1570

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]




private theorem wiresFrom_input_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [getD_wiresFrom _ _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]


def val (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD w false

lemma raw (gs : List Gate) (x : Fin 13 → Bool) {w : ℕ} (h : w < 13) :
    val gs x w = x ⟨w,h⟩ := wiresFrom_input_val (⟨gs,0⟩ : Circuit) x h

lemma inside {gs : List Gate} {x : Fin 13 → Bool} {w : ℕ} (h : val gs x w = true) :
    w < 13 + gs.length := by
  by_contra! hb
  have hl : (wiresFrom gs (List.ofFn x)).length ≤ w := by
    simpa [length_wiresFrom] using hb
  unfold val at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at h
  contradiction


def line (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}
lemma geometry : ∀ t : Fin 13, t ≠ 0 →
    (0 ∉ line t ∨ 1 ∉ line t) ∧ ∃ v ∈ line 0, v ∉ line t := by decide +kernel

end PEqualNP.Outside.L_meta_1570

open PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L eqn gs o _ _ correct
  have lineEq : L = line := funext eqn
  subst L
  let single := fun (p v : Fin 13) => decide (v = p)
  let co := fun (t v : Fin 13) => decide (v ∉ line t)
  have a : val gs (single 0) (o 0) = true := by
    have h := correct 0 (single 0) (Or.inl (by simp [single]))
    exact h.trans (by decide +kernel)
  have b : val gs (single 1) (o 0) = true := by
    have h := correct 0 (single 1) (Or.inr (Or.inl (by simp [single])))
    exact h.trans (by decide +kernel)
  refine ⟨?_,inside a,a,b,?_,?_⟩
  · by_contra! h
    rw [raw _ _ h] at a b
    simp [single] at a b
    omega
  · have h := correct 0 (co 0) (Or.inr (Or.inr (by simp [co])))
    exact h.trans (by simp [co])
  · intro t ht
    obtain ⟨adm,v,hv,off⟩ := geometry t ht
    have ok : co t 0 = true ∨ co t 1 = true ∨ ∀ v ∉ line 0, co t v = true := by
      rcases adm with h | h
      · exact Or.inl (by simpa [co] using h)
      · exact Or.inr (Or.inl (by simpa [co] using h))
    exact (correct 0 (co t) ok).trans (decide_eq_true ⟨v,hv,by simpa [co] using off⟩)
