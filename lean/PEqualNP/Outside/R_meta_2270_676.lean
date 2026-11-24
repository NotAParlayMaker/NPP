import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2270_676 :
  (let pins := fun (g : Gate) => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let cert := fun (n : ℕ) (C : Circuit) (u v : Fin n) (Z D : Finset ℕ) =>
    (∀ j ∈ Z, ∃ g, C.gates[j]? = some g ∧
      (∀ w ∈ pins g, w < n+j) ∧
      ((g.op = .and ∧ ∃ w ∈ pins g, w = u.val ∨ w = v.val) ∨
       ∀ w ∈ pins g, w = u.val ∨ w = v.val ∨ ∃ k ∈ Z, k<j ∧ w=n+k)) ∧
    (∀ j ∈ D, ∃ g, C.gates[j]? = some g ∧
      ∃ w ∈ pins g, w = u.val ∨ w = v.val ∨ ∃ k ∈ Z, k<j ∧ w=n+k)
    ∀ n C u v Z D, FanInTwo C → cert n C u v Z D →
    (∃ x : Fin n → Bool, C.eval (List.ofFn (Function.update (Function.update x u false) v false)) = false) →
    ∃ E : Circuit, FanInTwo E ∧ E.size+D.card≤C.size ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        C.eval (List.ofFn (Function.update (Function.update x u false) v false))) →
  (let pins := fun (g : Gate) => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let cert := fun (n : ℕ) (C : Circuit) (u v : Fin n) (Z D : Finset ℕ) =>
    (∀ j ∈ Z, ∃ g, C.gates[j]? = some g ∧
      (∀ w ∈ pins g, w < n+j) ∧
      ((g.op = .and ∧ ∃ w ∈ pins g, w = u.val ∨ w = v.val) ∨
       ∀ w ∈ pins g, w = u.val ∨ w = v.val ∨ ∃ k ∈ Z, k<j ∧ w=n+k)) ∧
    (∀ j ∈ D, ∃ g, C.gates[j]? = some g ∧
      ∃ w ∈ pins g, w = u.val ∨ w = v.val ∨ ∃ k ∈ Z, k<j ∧ w=n+k)
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    ¬ G.Colorable 2 →
    (∀ a ∉ A, (G.neighborSet a).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) →
    IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
    (∀ u v, G.Adj u v → ∀ Z D, cert n C u v Z D → D.card ≤ 6) →
    ∃ u v, G.Adj u v ∧ ∃ E : Circuit, FanInTwo E ∧ E.size+7≤C.size ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        C.eval (List.ofFn (Function.update (Function.update x u false) v false))) →
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  intro bridge residual n G A f hnon hdeg hgirth hiso hedge hfun s hsize
  classical
  have hex : ∃ t : ℕ, HasCircuitSize n f t := ⟨s, hsize⟩
  obtain ⟨C, hfan, hbound, hval⟩ := Nat.find_spec hex
  have hCs : C.size ≤ s := hbound.trans (Nat.find_min' hex hsize)
  have hmin : IsMinimalCircuit n C := by
    refine ⟨hfan, ?_⟩
    intro E hE heq
    have hEs : HasCircuitSize n f E.size := by
      refine ⟨E, hE, le_rfl, ?_⟩
      intro x
      have hx := congrFun heq x
      change E.eval (List.ofFn x) = C.eval (List.ofFn x) at hx
      exact hx.trans (hval x)
    exact hbound.trans (Nat.find_min' hex hEs)
  have hf : circuitFun n C = NestedCover.graphFun G A := by
    funext x
    change C.eval (List.ofFn x) = (decide (∃ a ∈ A, x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    rw [hval x]
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using hfun x
  have done (u v : Fin n) (ha : G.Adj u v) (E : Circuit) (hE : FanInTwo E)
      (hs : E.size+7≤C.size)
      (he : ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        C.eval (List.ofFn (Function.update (Function.update x u false) v false))) :
      ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ G.Adj u v ∧
        ∃ t, t + 7 ≤ s ∧ HasCircuitSize n
          (fun x => f (Function.update (Function.update x u false) v false)) t := by
    exact ⟨u,v,hiso u v ha,hiso v u (G.adj_symm ha),ha,E.size,hs.trans hCs,
      E,hE,le_rfl,fun x => (he x).trans (hval _)⟩
  let pins := fun (g : Gate) => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let cert := fun (n : ℕ) (C : Circuit) (u v : Fin n) (Z D : Finset ℕ) =>
    (∀ j ∈ Z, ∃ g, C.gates[j]? = some g ∧
      (∀ w ∈ pins g, w < n+j) ∧
      ((g.op = .and ∧ ∃ w ∈ pins g, w = u.val ∨ w = v.val) ∨
       ∀ w ∈ pins g, w = u.val ∨ w = v.val ∨ ∃ k ∈ Z, k<j ∧ w=n+k)) ∧
    (∀ j ∈ D, ∃ g, C.gates[j]? = some g ∧
      ∃ w ∈ pins g, w = u.val ∨ w = v.val ∨ ∃ k ∈ Z, k<j ∧ w=n+k)
  by_cases hex : ∃ u v, G.Adj u v ∧ ∃ Z D, cert n C u v Z D ∧ 7≤D.card
  · obtain ⟨u,v,ha,Z,D,hcert,hd⟩ := hex
    have hzero : ∃ x : Fin n → Bool,
        C.eval (List.ofFn (Function.update (Function.update x u false) v false)) = false := by
      refine ⟨fun _ => false, ?_⟩
      have hp : Function.update (Function.update (fun _ : Fin n => false) u false) v false =
          (fun _ => false) := by
        funext i
        by_cases hv : i = v <;> by_cases hu : i = u <;> simp [hv,hu,Function.update_of_ne]
      rw [hp]
      have hh := congrFun hf (fun _ => false)
      change C.eval (List.ofFn (fun _ : Fin n => false)) =
        (decide (∃ a ∈ A, (false : Bool) = true) || decide (∃ u v, G.Adj u v ∧ (false : Bool) = true ∧ (false : Bool) = true)) at hh
      rw [hh]
      simp
    obtain ⟨E,hE,hsize,he⟩ := bridge n C u v Z D hfan hcert hzero
    exact done u v ha E hE (by omega) he
  · have hsmall (u v : Fin n) (ha : G.Adj u v) (Z D : Finset ℕ)
        (hc : cert n C u v Z D) : D.card ≤ 6 := by
      by_contra! h
      exact hex ⟨u,v,ha,Z,D,hc,by omega⟩
    obtain ⟨u,v,ha,E,hE,hs,he⟩ := residual n G A C hnon hdeg hgirth hiso hmin hf hsmall
    exact done u v ha E hE hs he
