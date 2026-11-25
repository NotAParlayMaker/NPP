import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17110

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem foldl_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
    simp only [List.foldl_cons]
    rw [ht]
    simp

theorem wires_lt (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  obtain ⟨t, ht⟩ := foldl_prefix C.gates x
  unfold Circuit.wires
  rw [ht, List.getD_append _ _ _ _ hi]

theorem wires_first (C : Circuit) (g : Gate) (rest : List Gate) (h : C.gates = g :: rest)
    (x : List Bool) :
    (C.wires x).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  unfold Circuit.wires
  rw [h]
  simp only [List.foldl_cons]
  obtain ⟨t, ht⟩ := foldl_prefix rest (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
  rw [ht]
  simp

theorem rd_ge {n : ℕ} (y : Fin n → Bool) (a : ℕ) (h : n ≤ a) :
    (List.ofFn y).getD a false = false := by
  rw [List.getD_eq_default]
  simpa using h

theorem rd_lt {n : ℕ} (y : Fin n → Bool) (a : ℕ) (h : a < n) :
    (List.ofFn y).getD a false = y ⟨a, h⟩ := by
  simp [h]

theorem first_cases (n : ℕ) (C : Circuit) (hF : FanInTwo C) (g : Gate) (rest : List Gate)
    (hg : C.gates = g :: rest)
    (hnc : ∃ x y : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + 0) false ≠ (C.wires (List.ofFn y)).getD (n + 0) false)
    (hnew : ∀ i : ℕ, i < n + 0 → ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + 0) false) :
    ∃ i : Fin n,
      (∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = !(y i)) ∨
      (∃ j : Fin n, i < j ∧ ∀ y : Fin n → Bool,
        (C.wires (List.ofFn y)).getD n false = (y i && y j)) ∨
      (∃ j : Fin n, i < j ∧ ∀ y : Fin n → Bool,
        (C.wires (List.ofFn y)).getD n false = (y i || y j)) := by
  simp only [Nat.add_zero] at hnc hnew
  have hw : ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false
      = g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) := by
    intro y
    have := wires_first C g rest hg (List.ofFn y)
    rw [List.length_ofFn] at this
    exact this
  have nconst : ∀ c : Bool, ¬ ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = c := by
    intro c hc
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (by rw [hc x, hc y])
  have ncopy : ∀ a : ℕ, ∀ ha : a < n,
      ¬ ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = y ⟨a, ha⟩ := by
    intro a ha hc
    obtain ⟨x, hx⟩ := hnew a ha
    apply hx
    rw [hc x, wires_lt C _ a (by simpa using ha), rd_lt x a ha]
  obtain ⟨hop, hlen⟩ := hF g (by rw [hg]; exact List.mem_cons_self ..)
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hw
  rcases hop with rfl | rfl | rfl
  ·
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · exact (nconst true (fun y => by rw [hw]; rfl)).elim
    · by_cases ha : a < n
      · exact (ncopy a ha (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
      · exact (nconst false (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
    · by_cases ha : a < n
      · by_cases hb : b < n
        · rcases lt_trichotomy a b with hab | rfl | hab
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inl ⟨⟨b, hb⟩, Fin.mk_lt_mk.2 hab, fun y => by
              rw [hw]; simp [GateOp.eval, ha, hb]⟩)⟩
          · exact (ncopy a ha (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inl ⟨⟨a, ha⟩, Fin.mk_lt_mk.2 hab, fun y => by
              rw [hw]; simp [GateOp.eval, ha, hb, Bool.and_comm]⟩)⟩
        · exact (nconst false (fun y => by
            rw [hw]; simp [GateOp.eval, hb])).elim
      · exact (nconst false (fun y => by
          rw [hw]; simp [GateOp.eval, ha])).elim
    · simp at hlen
  ·
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · exact (nconst false (fun y => by rw [hw]; rfl)).elim
    · by_cases ha : a < n
      · exact (ncopy a ha (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
      · exact (nconst false (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
    · by_cases ha : a < n
      · by_cases hb : b < n
        · rcases lt_trichotomy a b with hab | rfl | hab
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inr ⟨⟨b, hb⟩, Fin.mk_lt_mk.2 hab, fun y => by
              rw [hw]; simp [GateOp.eval, ha, hb]⟩)⟩
          · exact (ncopy a ha (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inr ⟨⟨a, ha⟩, Fin.mk_lt_mk.2 hab, fun y => by
              rw [hw]; simp [GateOp.eval, ha, hb, Bool.or_comm]⟩)⟩
        · exact (ncopy a ha (fun y => by
            rw [hw]; simp [GateOp.eval, ha, hb])).elim
      · by_cases hb : b < n
        · exact (ncopy b hb (fun y => by
            rw [hw]; simp [GateOp.eval, ha, hb])).elim
        · exact (nconst false (fun y => by
            rw [hw]; simp [GateOp.eval, ha, hb])).elim
    · simp at hlen
  ·
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · exact (nconst true (fun y => by rw [hw]; rfl)).elim
    · by_cases ha : a < n
      · exact ⟨⟨a, ha⟩, Or.inl (fun y => by rw [hw]; simp [GateOp.eval, ha])⟩
      · exact (nconst true (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
    · by_cases ha : a < n
      · exact ⟨⟨a, ha⟩, Or.inl (fun y => by rw [hw]; simp [GateOp.eval, ha])⟩
      · exact (nconst true (fun y => by rw [hw]; simp [GateOp.eval, ha])).elim
    · simp at hlen

theorem assemble (f : (Fin 9 → Bool) → Bool)
    (hT : f (fun _ => true) = true) (hF : f (fun _ => false) = false)
    (hS : ∀ k : Fin 9, f (fun i => decide (i = k)) = false)
    (hred : ∀ C : Circuit, IsMinimalCircuit 9 C →
      (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) →
      (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧
      (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (hcase : ∀ C : Circuit, FanInTwo C → ∀ i : Fin 9,
      ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y i)) ∨
       (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
          (C.wires (List.ofFn y)).getD 9 false = (y i && y j)) ∨
       (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
          (C.wires (List.ofFn y)).getD 9 false = (y i || y j))) →
      circuitFun 9 C = f → 16 ≤ C.size)
    (t : ℕ) (ht : HasCircuitSize 9 f t) : 16 ≤ t := by
  classical
  obtain ⟨C, hCF, hCs, hCe⟩ := ht
  have hCf : circuitFun 9 C = f := funext hCe
  have hP : ∃ k, ∃ D : Circuit, FanInTwo D ∧ circuitFun 9 D = f ∧ D.size = k :=
    ⟨C.size, C, hCF, hCf, rfl⟩
  obtain ⟨M, hMF, hMf, hMk⟩ := Nat.find_spec hP
  have hmin : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = f → M.size ≤ D.size := by
    intro D hD hDf
    rw [hMk]
    exact Nat.find_min' hP ⟨D, hD, hDf, rfl⟩
  have hMC : M.size ≤ C.size := hmin C hCF hCf
  have hMmin : IsMinimalCircuit 9 M := ⟨hMF, fun D hD hDf => hmin D hD (hDf.trans hMf)⟩
  have hnc : ∃ x y : Fin 9 → Bool, circuitFun 9 M x ≠ circuitFun 9 M y :=
    ⟨fun _ => false, fun _ => true, by rw [hMf, hF, hT]; decide⟩
  obtain ⟨hA, hB⟩ := hred M hMmin hnc
  cases hg : M.gates with
  | nil =>
    exfalso
    have hw : ∀ x : Fin 9 → Bool, f x = (List.ofFn x).getD M.output false := by
      intro x
      rw [← hMf]
      show (M.wires (List.ofFn x)).getD M.output false = _
      unfold Circuit.wires
      rw [hg]
      rfl
    by_cases ho : M.output < 9
    · have h1 := hw (fun i => decide (i = ⟨M.output, ho⟩))
      rw [hS, rd_lt _ _ ho] at h1
      simp at h1
    · have h1 := hw (fun _ => true)
      rw [hT, rd_ge _ _ (by omega)] at h1
      exact Bool.noConfusion h1
  | cons g rest =>
    have hlen : 0 < M.gates.length := by simp [hg]
    obtain ⟨i, hi⟩ := first_cases 9 M hMF g rest hg (hA 0 hlen) (fun a ha => hB a 0 ha hlen)
    have := hcase M hMF i hi hMf
    omega

end PEqualNP.Outside.L_meta_17110

theorem PEqualNP.Outside.L_meta_17110 : ((∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) t → 16 ≤ t) := by
  intro hred h0 h1 h2 h3 h4 h5 h6 h7 h8 t ht
  refine PEqualNP.Outside.L_meta_17110.assemble _ (by decide) (by decide) (by decide)
    (fun C hm hn => ⟨(hred 9 C hm hn).1, (hred 9 C hm hn).2.1⟩) ?_ t ht
  intro C hC i
  fin_cases i
  · exact h0 C hC
  · exact h1 C hC
  · exact h2 C hC
  · exact h3 C hC
  · exact h4 C hC
  · exact h5 C hC
  · exact h6 C hC
  · exact h7 C hC
  · exact h8 C hC
