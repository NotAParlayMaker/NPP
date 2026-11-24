import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

private def runWires (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private theorem getD_runWires_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (runWires gs w).getD i false = w.getD i false := by
  induction gs with
  | nil =>
    intro w i _
    rfl
  | cons g gs ih =>
    intro w i hi
    have hlt : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp
      omega
    exact (ih _ i hlt).trans (List.getD_append _ _ _ _ hi)

private theorem eq_of_card_inter_eq_one {N : ℕ} {A B : Finset (Fin N)}
    (hcard : (A ∩ B).card = 1) {a b : Fin N}
    (haA : a ∈ A) (haB : a ∈ B) (hbA : b ∈ A) (hbB : b ∈ B) : a = b := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  have ha : a ∈ ({c} : Finset (Fin N)) := hc ▸ Finset.mem_inter.mpr ⟨haA, haB⟩
  have hb : b ∈ ({c} : Finset (Fin N)) := hc ▸ Finset.mem_inter.mpr ⟨hbA, hbB⟩
  rw [Finset.mem_singleton] at ha hb
  exact ha.trans hb.symm

private theorem eval_input_wire {N : ℕ} (L : Fin N → Finset (Fin N))
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (p t : Fin N) :
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩
      (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t := by
  let x : List Bool := List.ofFn (fun v : Fin N => decide (v ∉ L t))
  have hxlen : x.length = N := List.length_ofFn
  have hp : (p : ℕ) < x.length := by
    rw [hxlen]
    exact p.isLt
  have hev : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ x = x.getD (p : ℕ) false := by
    change (runWires gates x).getD (p : ℕ) false = x.getD (p : ℕ) false
    exact getD_runWires_lt gates x (p : ℕ) hp
  have hget : x.getD (p : ℕ) false = decide (p ∉ L t) := by
    rw [List.getD_eq_getElem _ _ hp]
    simp [x]
  rw [hev, hget]
  simp

theorem main_proof : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
  intro q N L i0 p0 p1 _ _ _ hinter _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' hl hl' hne p hp hpne
    refine ⟨hl'.2, fun hpl' => hpne ?_⟩
    exact eq_of_card_inter_eq_one (hinter l l' hne) hp hpl' hl.1 hl'.1
  · intro m m' hm hm' hne p hp hpne
    refine ⟨hm'.2, fun hpm' => hpne ?_⟩
    exact eq_of_card_inter_eq_one (hinter m m' hne) hp hpm' hm.1 hm'.1
  · exact fun _ hm => hm.2
  · exact fun _ hl => hl.2
  · exact fun _ _ _ hm _ _ hpm => ⟨hm.2, hpm⟩
  · intro l m hl hm
    have hne : l ≠ m := fun h => hm.2 (h ▸ hl.1)
    exact Finset.card_eq_one.mp (hinter l m hne)
  · intro gates _ _ _ p t
    exact eval_input_wire L gates p t

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
  exact PEqualNP.Outside.L_meta_1632.main_proof
