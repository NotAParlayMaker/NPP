import Mathlib
import PEqualNP.Defs

-- On a fixed-input slice, gates with the same Boolean function can share one wire.
-- It suffices to consider least circuits in which every admissible pair loses at most seven distinct gate functions.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2268_172
    (merge : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n),
      PEqualNP.MetaComplexity.FanInTwo C →
      let fix := fun x : Fin n → Bool => Function.update (Function.update x u false) v false
      let val := fun (j : ℕ) (x : Fin n → Bool) => (C.wires (List.ofFn (fix x))).getD (n+j) false
      let base := insert (fun _ : Fin n → Bool => false) (Finset.univ.image fun (i : Fin n) (x : Fin n → Bool) => fix x i)
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (fix x)))
        (((Finset.range C.size).image val) \ base).card)
    (rigid : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      let f := PEqualNP.MetaComplexity.circuitFun n C
      G.Colorable 2 →
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) →
      (∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ t, PEqualNP.MetaComplexity.HasCircuitSize n f t → C.size ≤ t) →
      (∀ u v : Fin n, u ∉ A → v ∉ A → u ≠ v → ¬G.Adj u v →
        let fix := fun x : Fin n → Bool => Function.update (Function.update x u false) v false
        let val := fun (j : ℕ) (x : Fin n → Bool) => (C.wires (List.ofFn (fix x))).getD (n+j) false
        let base := insert (fun _ : Fin n → Bool => false) (Finset.univ.image fun (i : Fin n) (x : Fin n → Bool) => fix x i)
        C.size < (((Finset.range C.size).image val) \ base).card + 8) →
      ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬G.Adj u v ∧
        ∃ t, t+8 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n
          (fun x => f (Function.update (Function.update x u false) v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G A f hcolor hdeg hgirth hactive hedge hf s hs
  let good := fun k => PEqualNP.MetaComplexity.HasCircuitSize n f k
  have hex : ∃ k, good k := ⟨s,hs⟩
  obtain ⟨C,hfanin,hsize,hcompute⟩ := Nat.find_spec hex
  have minsize (t) (h : good t) : C.size ≤ t := hsize.trans (Nat.find_min' hex h)
  have hsC : C.size ≤ s := minsize s hs
  have heq : PEqualNP.MetaComplexity.circuitFun n C = f := funext hcompute
  let value := fun (u v : Fin n) (j : ℕ) (x : Fin n → Bool) =>
    (C.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD (n+j) false
  let base := fun (u v : Fin n) => insert (fun _ : Fin n → Bool => false)
    (Finset.univ.image fun (i : Fin n) (x : Fin n → Bool) => Function.update (Function.update x u false) v false i)
  let count := fun u v => (((Finset.range C.size).image (value u v)) \ base u v).card
  by_cases cut : ∃ u v, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬G.Adj u v ∧ count u v + 8 ≤ C.size
  · obtain ⟨u,v,hu,hv,hd,hn,hcut⟩ := cut
    refine ⟨u,v,hu,hv,hd,hn,count u v,hcut.trans hsC,?_⟩
    simpa only [hcompute] using merge n C u v hfanin
  · have hr (u v : Fin n) (hu : u ∉ A) (hv : v ∉ A) (hd : u ≠ v) (hn : ¬G.Adj u v) :
          C.size < count u v + 8 :=
        Nat.lt_of_not_ge (fun h => cut ⟨u,v,hu,hv,hd,hn,h⟩)
    obtain ⟨u,v,hu,hv,hd,hn,t,ht,hf'⟩ :=
      rigid n G A C hcolor hdeg hgirth hactive hedge (heq.symm ▸ hf) hfanin (heq.symm ▸ minsize) hr
    exact ⟨u,v,hu,hv,hd,hn,t,ht.trans hsC,by simpa only [heq] using hf'⟩
