import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_4167_1_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_preserved (gs : List Gate) (init : List Bool) (k : ℕ) (hk : k < init.length) :
    (gs.foldl step init).getD k false = init.getD k false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step init g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma monotone2_of_fanInTwo_noNot (C : Circuit) (hF : FanInTwo C)
    (hNo : ∀ g ∈ C.gates, g.op ≠ GateOp.not) : Monotone2 C := by
  intro g hg
  obtain ⟨hop, hlen⟩ := hF g hg
  refine ⟨?_, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (hNo g hg)

lemma peel_first_gate (g : Gate) (tail : List Gate) (o : ℕ) (y : Fin 9 → Bool)
    (hg : (Circuit.wires ⟨g :: tail, o⟩ (List.ofFn y)).getD 9 false = (y 0 || y 2)) :
    Circuit.eval ⟨tail, o⟩ (List.ofFn y ++ [y 0 || y 2]) =
      Circuit.eval ⟨g :: tail, o⟩ (List.ofFn y) := by
  unfold Circuit.eval Circuit.wires
  change (tail.foldl step (List.ofFn y ++ [y 0 || y 2])).getD o false =
    (tail.foldl step (step (List.ofFn y) g)).getD o false
  have hstep : step (List.ofFn y) g = List.ofFn y ++ [y 0 || y 2] := by
    have hlen : (List.ofFn y).length = 9 := List.length_ofFn
    have h9 : (tail.foldl step (step (List.ofFn y) g)).getD 9 false = (y 0 || y 2) := hg
    rw [foldl_step_preserved tail (step (List.ofFn y) g) 9 (by simp [step, hlen])] at h9
    simpa [step, hlen] using h9
  rw [hstep]

end PEqualNP.Outside.R_meta_4167_1_aux

theorem PEqualNP.Outside.R_meta_4167_1
    (h1 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D → D.size = 14 →
      (∃ v ∈ ([4, 6, 7] : List ℕ), List.countP (fun g => g.inputs.contains v) D.gates ≤ 1) →
      ∃ y : Fin 9 → Bool,
        D.eval (List.ofFn y ++ [y 0 || y 2]) ≠
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun k =>
            y (Fin.ofNat 9 (k / 10)) && y (Fin.ofNat 9 (k % 10))))
    (h2 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D → D.size = 14 →
      (∀ v ∈ ([4, 6, 7] : List ℕ), List.countP (fun g => g.inputs.contains v) D.gates = 2) →
      ∃ y : Fin 9 → Bool,
        D.eval (List.ofFn y ++ [y 0 || y 2]) ≠
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun k =>
            y (Fin.ofNat 9 (k / 10)) && y (Fin.ofNat 9 (k % 10)))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → x2.size = (15 : ℕ) → (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1 := by
  intro x1 x2 hF hNo h9 hsz hcnt hfun
  have hM : PEqualNP.MetaComplexity.Monotone2 x2 :=
    PEqualNP.Outside.R_meta_4167_1_aux.monotone2_of_fanInTwo_noNot x2 hF hNo
  cases hgates : x2.gates with
  | nil =>
    have : x2.size = 0 := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgates]
    omega
  | cons g tail =>
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨tail, x2.output⟩
    have hD_mono : PEqualNP.MetaComplexity.Monotone2 D := by
      intro g' hg'
      exact hM g' (by rw [hgates]; exact List.mem_cons_of_mem _ hg')
    have hD_size : D.size = 14 := by
      have : x2.gates.length = 15 := hsz
      simp [D, PEqualNP.CircuitLowerBounds.Circuit.size, hgates] at this ⊢
      omega
    have hD_cnt : ∀ v ∈ ([4, 6, 7] : List ℕ),
        List.countP (fun g' => g'.inputs.contains v) D.gates ≤ 2 := by
      intro v hv
      have hidx : ∃ i : Fin 3, ![4, 6, 7] i = v := by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨0, rfl⟩
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact ⟨1, rfl⟩
          · rcases List.mem_cons.mp hv with rfl | hv
            · exact ⟨2, rfl⟩
            · contradiction
      obtain ⟨i, rfl⟩ := hidx
      have hi := hcnt i
      rw [hgates, List.countP_cons] at hi
      dsimp only [D]
      omega
    have heval : ∀ y : Fin 9 → Bool,
        D.eval (List.ofFn y ++ [y 0 || y 2]) = x2.eval (List.ofFn y) := by
      intro y
      have h9y := h9 y
      have hxeq : x2 = ⟨g :: tail, x2.output⟩ := by
        cases x2
        simp only at hgates
        rw [hgates]
      rw [hxeq] at h9y ⊢
      exact PEqualNP.Outside.R_meta_4167_1_aux.peel_first_gate g tail x2.output y h9y
    have hne : ∃ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 || y 2]) ≠ x1 y := by
      by_cases hle1 : ∃ v ∈ ([4, 6, 7] : List ℕ),
          List.countP (fun g' => g'.inputs.contains v) D.gates ≤ 1
      · exact h1 D hD_mono hD_size hle1
      · push Not at hle1
        have heq2 : ∀ v ∈ ([4, 6, 7] : List ℕ),
            List.countP (fun g' => g'.inputs.contains v) D.gates = 2 := by
          intro v hv
          have h1v := hle1 v hv
          have h2v := hD_cnt v hv
          omega
        exact h2 D hD_mono hD_size heq2
    obtain ⟨y, hy⟩ := hne
    apply hy
    rw [heval y]
    exact congrFun hfun y
