import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4095_1
    (packing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n)),
      7 ≤ G.egirth → (∀ v ∈ R, G.degree v = 3) →
      (∀ v ∈ R, ∀ w, G.Adj v w → w ∈ R) →
      ∃ I ⊆ R, G.IsIndepSet (I : Set (Fin n)) ∧ 5*R.card ≤ 14*I.card)
    (ports : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let R := Finset.univ \ A
      let read := fun w : ℕ => (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains w).length
      let rawCount := fun v : Fin n => read v.val
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) → (∀ v ∈ R, 2 ≤ rawCount v) →
      n+R.card + (R.filter fun v => 3 ≤ rawCount v).card + PEqualNP.NotBracket.notCount C +
        ((Finset.range C.size).filter fun j => 2 ≤ read (n+j) ∧ C.output ≠ n+j).card ≤ C.size+1)
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A T : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard=3) → (∀ u v, G.Adj u v → u∉A) →
      (∃ u v, G.Adj u v) → (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      G.edgeFinset.card+T.card+A.card ≤ C.size+1 →
      ∃ z ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => graphFun G A (Function.update x z false)) s)
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let R := Finset.univ \ A
      let b := C.size+1-(n+R.card)
      let reads := fun (g : Gate) (w : ℕ) => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains w
      let raw := fun v : Fin n => C.gates.filter fun g => reads g v.val
      let later := fun j => (C.gates.drop (j+1)).filter fun g => reads g (n+j)
      IsMinimalCircuit n C → circuitFun n C = graphFun G A → 7 ≤ G.egirth →
      (∀ v, G.degree v = if v ∈ R then 3 else 0) →
      (∀ v ∈ R, 2 ≤ (raw v).length ∧ (raw v).length ≤ 3 ∧
        ((raw v).length=3 → ∀ g ∈ raw v, g.op=.or)) →
      (∃ v ∈ R, ∃ g ∈ raw v, g.op=.and) →
      (∀ v ∈ R, ∀ j g, C.gates[j]?=some g → g.op=.and → reads g v.val →
        (∃ h ∈ raw v, h.op=.or) ∧ (later j).length ≤ 1 ∧ ∀ h ∈ later j, h.op=.or) →
      7*b < R.card → (∀ I ⊆ R, G.IsIndepSet (I : Set (Fin n)) → 2*(I.card+b) < R.card) →
      ∃ z ∈ R, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x z false)) s) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let eff := fun (g : Gate) => g.inputs.take (bif g.op.eval [false] then 1 else 2)
      let raw := fun (v : Fin n) => C.gates.filter fun g => (eff g).contains v.val
      let later := fun j => (C.gates.drop (j+1)).filter fun g => (eff g).contains (n+j)
      (∀ v ∉ A, (G.neighborSet v).ncard=3) → (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u∉A) → (∃ u v, G.Adj u v) → FanInTwo C → circuitFun n C=f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (raw v).length ∧ (raw v).length ≤ 3 ∧
        ((raw v).length=3 → ∀ g ∈ raw v, g.op=.or)) →
      (∃ v ∉ A, (raw v).length=2 ∧ ∃ g ∈ raw v, g.op=.and) →
      (∀ v ∉ A, ∀ j g, C.gates[j]?=some g → g.op=.and → (eff g).contains v.val →
        (∃ h ∈ raw v, h.op=.or) ∧ (later j).length ≤ 1 ∧ ∀ h ∈ later j, h.op=.or) →
      ∃ z ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x z false)) s := by
  classical
  intro n G inst A C f eff raw later cub girth apart has fan ev min read mixed shape
  let R := Finset.univ \ A
  let b := C.size+1-(n+R.card)
  have inR (v : Fin n) : v ∈ R ↔ v ∉ A := by simp [R]
  have least : IsMinimalCircuit n C := ⟨fan,fun D dFan dEval => min D.size
    ⟨D,dFan,le_rfl,fun x => congrFun (dEval.trans ev) x⟩⟩
  have cycle : 7 ≤ G.egirth := SimpleGraph.le_egirth.mpr (fun v w h => by exact_mod_cast girth v w h)
  have degree (v) (hv : v ∈ R) : G.degree v = 3 := by
    have h := cub v ((inR v).mp hv)
    rwa [←SimpleGraph.coe_neighborFinset,Set.ncard_coe_finset,SimpleGraph.card_neighborFinset_eq_degree] at h
  have allDeg (v) : G.degree v = if v ∈ R then 3 else 0 := by
    by_cases h : v ∈ R
    · simp only [h,ite_true,degree _ h]
    · rw [ite_eq_right h,←SimpleGraph.card_neighborFinset_eq_degree,Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w adj
      exact h ((inR v).mpr (apart v w (by simpa only [SimpleGraph.mem_neighborFinset] using adj)))
  have total := ports n G A C least ev apart has (fun v hv => (read v ((inR v).mp hv)).1)
  have base : n+R.card ≤ C.size+1 := by
    change n+R.card+_+_+_ ≤ _ at total
    omega
  have sizeEq : n+R.card+b = C.size+1 := by dsimp [b]; omega
  have cardR : R.card+A.card=n := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hand := G.sum_degrees_eq_twice_card_edges
  simp only [allDeg,Finset.sum_ite,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const_zero,
    add_zero,Finset.sum_const,smul_eq_mul] at hand
  by_contra fail
  have short (I : Finset (Fin n)) (sub : I ⊆ R) (ok : G.IsIndepSet (I : Set (Fin n))) :
      2*(I.card+b) < R.card := by
    by_contra! enough
    let T := R \ I
    have sz : T.card+I.card=R.card := Finset.card_sdiff_add_card_eq_card sub
    have cv (u v) (uv : G.Adj u v) : u ∈ T ∨ v ∈ T := by
      by_cases ui : u ∈ I
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨(inR v).mpr (apart v u uv.symm),fun vi => ok ui vi uv.ne uv⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨(inR u).mpr (apart u v uv),ui⟩)
    exact fail (stars n G A T C cub apart has cv (by omega))
  obtain ⟨I,sub,free,large⟩ := packing n G R cycle degree (fun _ _ w h => (inR w).mpr (apart _ _ h.symm))
  have gap := short I sub free
  obtain ⟨v,va,_,mix⟩ := mixed
  obtain ⟨z,zr,s,save,works⟩ := sparse n G A C least ev cycle allDeg
    (fun w hw => read w ((inR w).mp hw)) ⟨v,(inR v).mpr va,mix⟩
    (fun w hw => shape w ((inR w).mp hw)) (show 7*b<R.card by omega) short
  apply fail
  exact ⟨z,(inR z).mp zr,s,save,by simpa only [ev] using works⟩
