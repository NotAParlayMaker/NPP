import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

open PEqualNP.CircuitLowerBounds

theorem wires_prefix (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD k false
      = x.getD k false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem inter_uniq {N : ℕ} (L : Fin N → Finset (Fin N))
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (i j : Fin N) (h : i ≠ j) (a b : Fin N)
    (ha : a ∈ L i) (ha' : a ∈ L j) (hb : b ∈ L i) (hb' : b ∈ L j) : a = b :=
  Finset.card_le_one.mp (hI i j h).le a (Finset.mem_inter.mpr ⟨ha, ha'⟩) b (Finset.mem_inter.mpr ⟨hb, hb'⟩)

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
  intro q N L i0 p0 p1 hq hN hL hI hP h01 h0 h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' hl hl' hne p hp hpp
    refine ⟨hl'.2, fun hp' => hpp ?_⟩
    exact PEqualNP.Outside.L_meta_1632.inter_uniq L hI l l' hne p p0 hp hp' hl.1 hl'.1
  · intro m m' hm hm' hne p hp hpp
    refine ⟨hm'.2, fun hp' => hpp ?_⟩
    exact PEqualNP.Outside.L_meta_1632.inter_uniq L hI m m' hne p p1 hp hp' hm.1 hm'.1
  · intro m hm
    exact hm.2
  · intro l hl
    exact hl.2
  · intro M m hM hm p hp hpm
    exact ⟨hm.2, hpm⟩
  · intro l m hl hm
    have hne : l ≠ m := by
      intro h
      subst h
      exact hm.2 hl.1
    exact Finset.card_eq_one.mp (hI l m hne)
  · intro gates hlegal hpos hearly p t
    have hp : (p : ℕ) < (List.ofFn (fun v : Fin N => decide (v ∉ L t))).length := by simp
    have hw := PEqualNP.Outside.L_meta_1632.wires_prefix gates
      (List.ofFn (fun v : Fin N => decide (v ∉ L t))) (p : ℕ) hp
    have he : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩
        (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = decide (p ∉ L t) := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [hw]
      simp [List.getD_eq_getElem?_getD]
    rw [he]
    simp
