import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem eval_input (gates : List Gate) (N : ℕ) (f : Fin N → Bool) (w : ℕ) (hw : w < N) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn f) = f ⟨w, hw⟩ := by
  unfold Circuit.eval
  change (gates.foldl step (List.ofFn f)).getD w false = _
  rw [fold_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem two_pts {N : ℕ} (L : Fin N → Finset (Fin N))
    (hLL : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (a b l l' : Fin N) (hne : l ≠ l')
    (ha : a ∈ L l) (ha' : a ∈ L l') (hb : b ∈ L l) (hb' : b ∈ L l') : b = a :=
  Finset.card_le_one.mp (le_of_eq (hLL l l' hne)) b (Finset.mem_inter.mpr ⟨hb, hb'⟩) a
    (Finset.mem_inter.mpr ⟨ha, ha'⟩)

end PEqualNP.Outside.L_meta_1632

theorem PEqualNP.Outside.L_meta_1632 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ l l' : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p0 ∈ L l' ∧ p1 ∉ L l') → l ≠ l' → ∀ p ∈ L l, p ≠ p0 → p1 ∉ L l' ∧ p ∉ L l') ∧
    (∀ m m' : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p1 ∈ L m' ∧ p0 ∉ L m') → m ≠ m' → ∀ p ∈ L m, p ≠ p1 → p0 ∉ L m' ∧ p ∉ L m') ∧
    (∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → p0 ∉ L m) ∧ (∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → p1 ∉ L l) ∧
    (∀ M m : Fin N, (p0 ∉ L M ∧ p1 ∉ L M) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ p ∈ L M, p ∉ L m → p0 ∉ L m ∧ p ∉ L m) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∃ c : Fin N, L l ∩ L m = {c}) ∧
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      ∀ p t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t) := by
  intro q N L i0 p0 p1 _ _ _ hLL _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' hl hl' hne p hp hpp0
    refine ⟨hl'.2, ?_⟩
    intro hp'
    exact hpp0 (PEqualNP.Outside.L_meta_1632.two_pts L hLL p0 p l l' hne hl.1 hl'.1 hp hp')
  · intro m m' hm hm' hne p hp hpp1
    refine ⟨hm'.2, ?_⟩
    intro hp'
    exact hpp1 (PEqualNP.Outside.L_meta_1632.two_pts L hLL p1 p m m' hne hm.1 hm'.1 hp hp')
  · intro m hm
    exact hm.2
  · intro l hl
    exact hl.2
  · intro M m _ hm p _ hp
    exact ⟨hm.2, hp⟩
  · intro l m hl hm
    have hne : l ≠ m := by
      intro h
      rw [h] at hl
      exact hm.2 hl.1
    exact Finset.card_eq_one.mp (hLL l m hne)
  · intro gates _ _ _ p t
    rw [PEqualNP.Outside.L_meta_1632.eval_input gates N _ p p.isLt]
    simp
