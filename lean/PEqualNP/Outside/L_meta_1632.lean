import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1632

private lemma input_preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (Circuit.wires ⟨gs, i⟩ w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun j => w.getD j false)
    change (Circuit.wires ⟨gs, i⟩ (w ++ [b])).getD i false = _
    rw [ih (w ++ [b]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

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
  intro q N L i0 p0 p1 _ _ _ hmeet _ _ _ _
  have uniquePoint {a b u v : Fin N} (hab : a ≠ b)
      (hua : u ∈ L a) (hub : u ∈ L b) (hva : v ∈ L a) (hvb : v ∈ L b) : u = v := by
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hmeet a b hab)
    have eq_c {z : Fin N} (ha : z ∈ L a) (hb : z ∈ L b) : z = c := by
      have hz := Finset.mem_inter.mpr ⟨ha, hb⟩
      rwa [hc, Finset.mem_singleton] at hz
    exact (eq_c hua hub).trans (eq_c hva hvb).symm
  refine ⟨?_, ?_, fun _ h => h.2, fun _ h => h.2, ?_, ?_, ?_⟩
  · intro l l' h h' hne p hp hdiff
    exact ⟨h'.2, fun hp' => hdiff (uniquePoint hne hp hp' h.1 h'.1)⟩
  · intro m m' h h' hne p hp hdiff
    exact ⟨h'.2, fun hp' => hdiff (uniquePoint hne hp hp' h.1 h'.1)⟩
  · intro M m _ hm p _ hp
    exact ⟨hm.2, hp⟩
  · intro l m hl hm
    exact Finset.card_eq_one.mp (hmeet l m (fun heq => hm.2 (heq ▸ hl.1)))
  · intro gates _ _ _ p t
    unfold Circuit.eval
    rw [PEqualNP.Outside.L_meta_1632.input_preserved gates _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
