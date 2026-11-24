import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

open PEqualNP.CircuitLowerBounds

theorem foldl_getD (gates : List Gate) : ∀ (x : List Bool) (i : ℕ), i < x.length →
    (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).getD i false
      = x.getD i false := by
  induction gates with
  | nil => intro x i _; rfl
  | cons g gs ih =>
    intro x i hi
    rw [List.foldl_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem two_pts {N : ℕ} (A B : Finset (Fin N)) (h : (A ∩ B).card = 1) (a b : Fin N)
    (ha : a ∈ A) (ha' : a ∈ B) (hb : b ∈ A) (hb' : b ∈ B) : a = b := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h
  have h1 : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, ha'⟩
  have h2 : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb, hb'⟩
  rw [hc, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

theorem eval_input (gates : List Gate) (x : List Bool) (p : ℕ) (hp : p < x.length) :
    Circuit.eval ⟨gates, p⟩ x = x.getD p false :=
  foldl_getD gates x p hp

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
  intro q N L i0 p0 p1 _ _ _ hint _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' hl hl' hne p hp hpne
    refine ⟨hl'.2, fun hp' => hpne ?_⟩
    exact PEqualNP.Outside.L_meta_1632.two_pts _ _ (hint l l' hne) p p0 hp hp' hl.1 hl'.1
  · intro l l' hl hl' hne p hp hpne
    refine ⟨hl'.2, fun hp' => hpne ?_⟩
    exact PEqualNP.Outside.L_meta_1632.two_pts _ _ (hint l l' hne) p p1 hp hp' hl.1 hl'.1
  · intro m hm; exact hm.2
  · intro l hl; exact hl.2
  · intro M m _ hm p _ hpm; exact ⟨hm.2, hpm⟩
  · intro l m hl hm
    have hne : l ≠ m := by
      rintro rfl
      exact hm.2 hl.1
    exact Finset.card_eq_one.mp (hint l m hne)
  · intro gates _ _ _ p t
    rw [PEqualNP.Outside.L_meta_1632.eval_input gates _ (p : ℕ) (by simp)]
    simp [List.getD_eq_getElem?_getD]
