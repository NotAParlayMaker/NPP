import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

-- Count the ordered pairs of distinct vertices that a single gate can serve.
-- Reuse the simultaneous compression child of R-meta-4111-617.
theorem PEqualNP.Outside.R_meta_3997_617
    (compress : ∀ (n : ℕ) (C : Circuit) (u v : Fin n) (S : Finset ℕ),
    FanInTwo C → (let W := fun (i : ℕ) (x : Fin n → Bool) => PEqualNP.LowMerge.wireVal C (List.ofFn (Function.update (Function.update x u false) v false)) i; ∀ j ∈ S, j < C.size ∧ ((∀ x, W (n+j) x = false) ∨ ∃ i < n+j, W (n+j) = W i)) →
    ∃ s, s + S.card ≤ C.size ∧ HasCircuitSize n
      (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) s)
    (average : ∀ (n m : ℕ) (T : Finset (Fin n)) (M : Fin m → Finset (Fin n)),
    7*T.offDiag.card < ∑ j, (T.offDiag.card - (T \ M j).offDiag.card) →
    ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧
      ∃ Q : Finset (Fin m), 8 ≤ Q.card ∧ ∀ j ∈ Q, u∈M j ∨ v∈M j)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    30 ≤ n → Even n → G.Colorable 2 → (∀ v, (G.neighborSet v).ncard = 3) →
    (∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n C → C.size+1 < 2*n →
    (∀ x : Fin n → Bool, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
    ∃ (T : Finset (Fin n)) (M : Fin C.size → Finset (Fin n)),
      (∀ a∈T, ∀ b∈T, ¬ G.Adj a b) ∧
      7*T.offDiag.card < ∑ j, (T.offDiag.card - (T \ M j).offDiag.card) ∧
      let W := fun (i : ℕ) (x : Fin n → Bool) => PEqualNP.LowMerge.wireVal C (List.ofFn x) i;
      ∀ j, ∀ v∈M j, (∀ x, x v=false → W (n+j.val) x=false) ∨
        ∃ i < n+j.val, ∀ x, x v=false → W (n+j.val) x = W i x) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x3 x10 = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), x11 + (1 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x11 → ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ≠ x15 ∧ ¬x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  intro n G f large even bip degree girth edge hFunction s small hSize
  classical
  have hex : ∃ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t := ⟨s, hSize⟩
  obtain ⟨D, hFanIn, hBound, hEval⟩ := Nat.find_spec hex
  have hDs : D.size ≤ s := hBound.trans (Nat.find_min' hex hSize)
  have hLeast : PEqualNP.MetaComplexity.IsMinimalCircuit n D := by
    refine ⟨hFanIn, ?_⟩
    intro E hEFanIn hEquivalent
    have hESize : PEqualNP.MetaComplexity.HasCircuitSize n f E.size := by
      refine ⟨E, hEFanIn, le_rfl, ?_⟩
      intro x
      exact (congrFun hEquivalent x).trans (hEval x)
    exact hBound.trans (Nat.find_min' hex hESize)
  have hDSemantics (x : Fin n → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [hEval x]
    exact hFunction x
  obtain ⟨T,M,independent,total,mark⟩ := charge n G D large even bip degree girth edge hLeast (by omega) hDSemantics
  obtain ⟨u,hu,v,hv,ne,Q,count,hits⟩ := average n D.size T M total
  let S := Q.map Fin.valEmbedding
  have ample : 8 ≤ S.card := by simpa only [S,Finset.card_map] using count
  have changes (k : ℕ) (hk : k∈S) : k<D.size ∧
      ((∀ x : Fin n → Bool, PEqualNP.LowMerge.wireVal D (List.ofFn (Function.update (Function.update x u false) v false)) (n+k)=false) ∨
       ∃ i < n+k, ∀ x : Fin n → Bool,
         PEqualNP.LowMerge.wireVal D (List.ofFn (Function.update (Function.update x u false) v false)) (n+k)=
         PEqualNP.LowMerge.wireVal D (List.ofFn (Function.update (Function.update x u false) v false)) i) := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hk
    refine ⟨j.isLt,?_⟩
    let pin := fun (x : Fin n → Bool) => Function.update (Function.update x u false) v false
    have liftOne (a : Fin n) (ha : a ∈ M j) (off : ∀ x, pin x a = false) :
        (∀ x, PEqualNP.LowMerge.wireVal D (List.ofFn (pin x)) (n+j.val)=false) ∨
        ∃ i < n+j.val, ∀ x, PEqualNP.LowMerge.wireVal D (List.ofFn (pin x)) (n+j.val)=
          PEqualNP.LowMerge.wireVal D (List.ofFn (pin x)) i := by
      rcases mark j a ha with zero|⟨i,lt,coincide⟩
      · exact Or.inl (fun x => zero (pin x) (off x))
      · exact Or.inr ⟨i,lt,fun x => coincide (pin x) (off x)⟩
    rcases hits j hj with left|right
    · exact liftOne u left (by simp [pin,Function.update_apply,ne])
    · exact liftOne v right (by simp [pin])
  obtain ⟨r,budget,cert⟩ := compress n D u v S hFanIn (by
    dsimp only
    intro k hk
    obtain ⟨kl,zero|⟨i,il,same⟩⟩ := changes k hk
    · exact ⟨kl,Or.inl zero⟩
    · exact ⟨kl,Or.inr ⟨i,il,funext same⟩⟩)
  refine ⟨u,v,ne,independent u hu v hv,r,by omega,?_⟩
  have eq : circuitFun n D = f := funext hEval
  simpa only [eq] using cert
