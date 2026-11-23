import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_735_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

def rg (phi : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map phi }

lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · simp [List.getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

def Rel (n n' : ℕ) (phi : ℕ → ℕ) (t : ℕ) (W W' : List Bool) : Prop :=
  W.length = n + t ∧ W'.length = n' + t ∧ ∀ i : ℕ, W'.getD (phi i) false = W.getD i false

lemma rel_step (n n' G : ℕ) (phi : ℕ → ℕ)
    (hphi : ∀ t : ℕ, t < G → ∀ i : ℕ, phi i = n' + t ↔ i = n + t)
    (t : ℕ) (ht : t < G) (W W' : List Bool) (g : Gate) (h : Rel n n' phi t W W') :
    Rel n n' phi (t + 1) (step W g) (step W' (rg phi g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (rg phi g).op.eval ((rg phi g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [rg, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro i
  simp only [step, hv]
  by_cases hi : i = n + t
  · have hp : phi i = W'.length := by rw [h2]; exact (hphi t ht i).2 hi
    have hi' : i = W.length := by rw [h1]; exact hi
    rw [hp, hi', getD_snoc_eq, getD_snoc_eq]
  · have hp : phi i ≠ W'.length := by
      rw [h2]; intro hc; exact hi ((hphi t ht i).1 hc)
    have hi' : i ≠ W.length := by rw [h1]; exact hi
    rw [getD_snoc_ne _ _ _ hp, getD_snoc_ne _ _ _ hi']
    exact h3 i

lemma rel_fold (n n' G : ℕ) (phi : ℕ → ℕ)
    (hphi : ∀ t : ℕ, t < G → ∀ i : ℕ, phi i = n' + t ↔ i = n + t) (gs : List Gate) :
    ∀ (t : ℕ) (W W' : List Bool), t + gs.length ≤ G → Rel n n' phi t W W' →
      Rel n n' phi (t + gs.length) (run gs W) (run (gs.map (rg phi)) W') := by
  induction gs with
  | nil => intro t W W' _ h; exact h
  | cons g gs ih =>
    intro t W W' ht h
    have ht' : t < G := by simp at ht; omega
    have key := ih (t + 1) _ _ (by simp at ht ⊢; omega) (rel_step n n' G phi hphi t ht' W W' g h)
    have hlen : t + (g :: gs).length = t + 1 + gs.length := by simp; omega
    rw [hlen]
    exact key

lemma main (n n' : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n) (he : StrictMono e)
    (hZ : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k) (gates : List Gate) :
    ∃ phi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
      (∀ k ∈ Z, x.getD (k : ℕ) false = false) →
      (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
      ∀ i : ℕ, (run (gates.map (rg phi)) x').getD (phi i) false = (run gates x).getD i false := by
  classical
  let phi : ℕ → ℕ := fun i =>
    if h : ∃ j : Fin n', (e j : ℕ) = i then ((Classical.choose h : Fin n') : ℕ)
    else if n ≤ i ∧ i < n + gates.length then n' + (i - n) else n' + gates.length
  have hphi1 : ∀ j : Fin n', phi (e j : ℕ) = (j : ℕ) := by
    intro j
    have h : ∃ j' : Fin n', (e j' : ℕ) = (e j : ℕ) := ⟨j, rfl⟩
    have hc := Classical.choose_spec h
    have hj : Classical.choose h = j := he.injective (Fin.ext hc)
    simp only [phi, dif_pos h, hj]
  have hphi2 : ∀ i : ℕ, (¬ ∃ j : Fin n', (e j : ℕ) = i) → n' ≤ phi i := by
    intro i h
    simp only [phi, dif_neg h]
    split <;> omega
  have hphi : ∀ t : ℕ, t < gates.length → ∀ i : ℕ, phi i = n' + t ↔ i = n + t := by
    intro t ht i
    by_cases h : ∃ j : Fin n', (e j : ℕ) = i
    · obtain ⟨j, rfl⟩ := h
      rw [hphi1 j]
      have h1 := j.isLt
      have h2 := (e j).isLt
      omega
    · simp only [phi, dif_neg h]
      split <;> omega
  refine ⟨phi, ?_⟩
  intro x x' hx hx' hxZ hxe i
  have hinit : Rel n n' phi 0 x x' := by
    refine ⟨by omega, by omega, ?_⟩
    intro i
    by_cases h : ∃ j : Fin n', (e j : ℕ) = i
    · obtain ⟨j, rfl⟩ := h
      rw [hphi1 j]
      exact (hxe j).symm
    · have hp := hphi2 i h
      rw [List.getD_eq_default _ _ (by omega)]
      by_cases hin : i < n
      · have hk : (⟨i, hin⟩ : Fin n) ∈ Z := by
          by_contra hk
          obtain ⟨j, hj⟩ := (hZ ⟨i, hin⟩).1 hk
          exact h ⟨j, by rw [hj]⟩
        exact (hxZ ⟨i, hin⟩ hk).symm
      · rw [List.getD_eq_default _ _ (by omega)]
  have key := rel_fold n n' gates.length phi hphi gates 0 x x' (by omega) hinit
  exact key.2.2 i

end PEqualNP.Outside.L_meta_735_aux

open PEqualNP.Outside.L_meta_735_aux in
theorem PEqualNP.Outside.L_meta_735 :
    ∀ (n n' : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k) → n' + Z.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ phi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ Z, x.getD (k : ℕ) false = false) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := 0 } x').getD (phi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := phi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' Z e he hZ _ gates
  obtain ⟨phi, hphi⟩ := main n n' Z e he hZ gates
  refine ⟨phi, ?_⟩
  intro x x' hx hx' hxZ hxe
  exact ⟨fun i => hphi x x' hx hx' hxZ hxe i, fun o => hphi x x' hx hx' hxZ hxe o⟩
