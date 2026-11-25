import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8233_aux

open PEqualNP.CircuitLowerBounds

def cg (N : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i N)⟩

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

theorem key {α : Type} (N : ℕ) (w : List α) (z : α) (h : w.length ≤ N) (i : ℕ) :
    w.getD (min i N) z = w.getD i z := by
  by_cases hi : i ≤ N
  · rw [Nat.min_eq_left hi]
  · have h1 : w.length ≤ min i N := by omega
    have h2 : w.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]

theorem fold (N : ℕ) (gs : List Gate) :
    ∀ w : List Bool, w.length + gs.length ≤ N →
      (gs.map (cg N)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
        = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w ∧
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        ≤ N := by
  induction gs with
  | nil => intro w h; exact ⟨rfl, by simpa using h⟩
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    have e : (cg N g).op.eval ((cg N g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [cg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact key N w false (by omega) i
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e]
    exact ih _ (by simp; omega)

theorem foldD (N : ℕ) (gs : List Gate) :
    ∀ d : List ℕ, d.length + gs.length ≤ N →
      (gs.map (cg N)).foldl (fun d g => d ++ [g.lineDegree d]) d
        = gs.foldl (fun d g => d ++ [g.lineDegree d]) d ∧
      (gs.foldl (fun d g => d ++ [g.lineDegree d]) d).length ≤ N := by
  induction gs with
  | nil => intro w h; exact ⟨rfl, by simpa using h⟩
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    have m : (g.inputs.map fun i => min i N).map (fun i => w.getD i 0)
        = g.inputs.map fun i => w.getD i 0 := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact key N w 0 (by omega) i
    have e : (cg N g).lineDegree w = g.lineDegree w := by
      unfold Gate.lineDegree
      simp only [cg]
      rw [m]
      by_cases hop : g.op = GateOp.and <;> simp [hop]
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e]
    exact ih _ (by simp; omega)

theorem gate_eq (g : Gate) (h1 : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (h2 : g.inputs.length ≤ 2) :
    ({ op := if isAnd g.op = true then GateOp.and else GateOp.or,
       inputs := List.filterMap (Option.map Fin.val)
         [g.inputs[0]?.map (fun i => (⟨min i 89, by omega⟩ : Fin 90)),
          g.inputs[1]?.map (fun i => (⟨min i 89, by omega⟩ : Fin 90))] } : Gate) = cg 89 g := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  simp only at h2
  simp only [cg]
  congr 1
  · rcases h1 with h | h <;> subst h <;> rfl
  · match ins, h2 with
    | [], _ => rfl
    | [a], _ => rfl
    | [a, b], _ => rfl
    | a :: b :: c :: l, h => simp at h

end PEqualNP.Outside.L_meta_8233_aux

open PEqualNP.Outside.L_meta_8233_aux in
theorem PEqualNP.Outside.L_meta_8233 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size < (64 : ℕ) →       ∃ (x4 : Fin (64 : ℕ)) (x5 : Fin (90 : ℕ)) (x6 : Fin ↑x4 → Bool) (x7 : Fin ↑x4 → Option (Fin (90 : ℕ))) (x8 : Fin ↑x4 → Option (Fin (90 : ℕ))),         have x9 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x9 : Fin ↑x4) => { op := if x6 x9 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.filterMap (Option.map Fin.val) [x7 x9, x8 x9] : PEqualNP.CircuitLowerBounds.Gate }, output := ↑x5 : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 ∧ ∀ (x10 : Finset ℕ), x9.lineDeg (26 : ℕ) x10 = x1.lineDeg (26 : ℕ) x10 := by
  intro C hM hs
  have hs2 : C.gates.length < 64 := hs
  refine ⟨⟨C.gates.length, hs2⟩, ⟨min C.output 89, by omega⟩,
    fun j => isAnd (C.gates[j.1]'j.2).op,
    fun j => (C.gates[j.1]'j.2).inputs[0]?.map (fun i => (⟨min i 89, by omega⟩ : Fin 90)),
    fun j => (C.gates[j.1]'j.2).inputs[1]?.map (fun i => (⟨min i 89, by omega⟩ : Fin 90)), ?_⟩
  have hg : (List.ofFn fun (j : Fin C.gates.length) =>
      ({ op := if isAnd (C.gates[j.1]'j.2).op = true then PEqualNP.CircuitLowerBounds.GateOp.and
              else PEqualNP.CircuitLowerBounds.GateOp.or,
         inputs := List.filterMap (Option.map Fin.val)
           [(C.gates[j.1]'j.2).inputs[0]?.map (fun i => (⟨min i 89, by omega⟩ : Fin 90)),
            (C.gates[j.1]'j.2).inputs[1]?.map (fun i => (⟨min i 89, by omega⟩ : Fin 90))] }
        : PEqualNP.CircuitLowerBounds.Gate)) = C.gates.map (cg 89) := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      have hm := hM _ (List.getElem_mem (l := C.gates) (n := n) (by simpa using h1))
      exact gate_eq _ hm.1 hm.2
  simp only []
  rw [hg]
  constructor
  · funext x
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
      PEqualNP.CircuitLowerBounds.Circuit.wires
    obtain ⟨h1, h2⟩ := fold 89 C.gates (List.ofFn x) (by simp; omega)
    simp only []
    rw [h1]
    exact key 89 _ false h2 C.output
  · intro m
    unfold PEqualNP.CircuitLowerBounds.Circuit.lineDeg PEqualNP.CircuitLowerBounds.Circuit.lineDegrees
    obtain ⟨h1, h2⟩ := foldD 89 C.gates ((List.range 26).map fun i => if i ∈ m then 1 else 0)
      (by simp; omega)
    simp only []
    rw [h1]
    exact key 89 _ 0 h2 C.output
