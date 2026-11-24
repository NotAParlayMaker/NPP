import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

-- The final operands are synthesized from minimal true supports. An independent
-- support at the left must contain a point of line zero. At the right its lines
-- must meet every pencil based on line zero. Dominated supports may be dropped.
theorem PEqualNP.Outside.R_meta_2608_714
    (realize : ∀ (n k a b : ℕ) (V : ℕ → Set (Fin n → Bool)),
      a < n+k → b < n+k → a ≠ b →
      (∀ i : Fin n, V i.val = {x | x i = true}) →
      (∀ j < k, ∃ u < n+j, ∃ v < n+j, u ≠ v ∧
        (V (n+j) = V u ∪ V v ∨ V (n+j) = V u ∩ V v)) →
      ∃ C : Circuit, C.size = k+1 ∧ IsAO2 n C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        C.output = n+k ∧ C.gates[k]? = some ⟨.and,[a,b]⟩ ∧
        ∀ i < n+k, ∀ x, wireValue C n x i = true ↔ x ∈ V i)
    (supports :
      let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let P := Fin.castAdd 13 (n := 13)
      let L := Fin.natAdd 13 (m := 13)
      let edges : Set (Finset (Fin 26)) := {s | ∃ p l, E p l ∧ s = {P p,L l}}
      let above := fun (F : Set (Finset (Fin 26))) (s : Finset (Fin 26)) => ∃ t ∈ F, t ⊆ s
      ∃ k ≤ 63, ∃ a < 26+k, ∃ b < 26+k, a ≠ b ∧
        ∃ F : ℕ → Set (Finset (Fin 26)),
        let U := fun i => {s | above (F i) s}
        (∀ i : Fin 26, U i.val = {s | i ∈ s}) ∧
        (∀ j < k, ∃ u < 26+j, ∃ v < 26+j, u ≠ v ∧
          (U (26+j) = U u ∪ U v ∨ U (26+j) = U u ∩ U v)) ∧
        edges ⊆ U a ∩ U b ∧
        (∀ s ∈ F a, above edges s ∨ ∃ p, E p 0 ∧ P p ∈ s) ∧
        ∀ s ∈ F b, above edges s ∨ ∀ p, E p 0 → ∃ l, E p l ∧ L l ∈ s) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  classical
  let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let P : Fin 13 → Fin 26 := Fin.castAdd 13
  let L : Fin 13 → Fin 26 := Fin.natAdd 13
  let edges : Set (Finset (Fin 26)) := {s | ∃ p l, E p l ∧ s = {P p,L l}}
  let above := fun (F : Set (Finset (Fin 26))) (s : Finset (Fin 26)) => ∃ t ∈ F, t ⊆ s
  obtain ⟨k,hk,a,ha,b,hb,hab,F,inputs,gates,accept,leftTerms,rightTerms⟩ := supports
  let U := fun i => {s | above (F i) s}
  let mask := fun (x : Fin 26 → Bool) => Finset.univ.filter (fun v => x v = true)
  let V := fun i => mask ⁻¹' U i
  have memMask (x : Fin 26 → Bool) (i : Fin 26) : i ∈ mask x ↔ x i = true := by simp [mask]
  have source (i : Fin 26) : V i.val = {x | x i = true} := by
    change mask ⁻¹' U i.val = _
    rw [show U i.val = {s | i ∈ s} from inputs i]
    exact Set.ext fun x => memMask x i
  have trace (j : ℕ) (hj : j < k) : ∃ u < 26+j, ∃ v < 26+j, u ≠ v ∧
      (V (26+j) = V u ∪ V v ∨ V (26+j) = V u ∩ V v) := by
    obtain ⟨u,hu,v,hv,huv,e⟩ := gates j hj
    refine ⟨u,hu,v,hv,huv,?_⟩
    rcases e with e | e
    · exact Or.inl (congrArg (fun S => mask ⁻¹' S) e)
    · exact Or.inr (congrArg (fun S => mask ⁻¹' S) e)
  obtain ⟨C,size,ao,dup,out,gate,eval⟩ := realize 26 k a b V ha hb hab source trace
  refine ⟨C,k,a,b,by omega,ao,dup,out,gate,?_,?_⟩
  · intro p l hpl
    let x := fun t : Fin 26 => decide (t = P p ∨ t = L l)
    have em : mask x = {P p,L l} := by
      ext t
      simp only [memMask, x, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    have good : mask x ∈ edges := ⟨p,l,hpl,em⟩
    exact ⟨(eval a ha x).2 (accept good).1, (eval b hb x).2 (accept good).2⟩
  · intro x hx
    have noEdge (s : Finset (Fin 26)) (hs : s ⊆ mask x) : ¬ above edges s := by
      intro h
      obtain ⟨t,ht,sub⟩ := h
      obtain ⟨p,l,inc,rfl⟩ := ht
      exact hx.1 ⟨p,l,inc,(memMask x (P p)).1 (hs (sub (by simp))),
        (memMask x (L l)).1 (hs (sub (by simp)))⟩
    by_cases hzero : x (13 : Fin 26) = true
    · simp only [hzero, ↓reduceIte]
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨s,hs,hsub⟩ := (eval a ha x).1 h
      obtain ⟨p,inc,hp⟩ := (leftTerms s hs).resolve_left (noEdge s hsub)
      exact hx.1 ⟨p,0,inc,(memMask x _).1 (hsub hp),hzero⟩
    · simp only [hzero, ↓reduceIte]
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨s,hs,hsub⟩ := (eval b hb x).1 h
      have cover := (rightTerms s hs).resolve_left (noEdge s hsub)
      have off (p : Fin 13) (inc : E p 0) : x (P p) ≠ true := by
        intro hp
        obtain ⟨l,hpl,hl⟩ := cover p inc
        exact hx.1 ⟨p,l,hpl,hp,(memMask x _).1 (hsub hl)⟩
      let z := Function.update x (L 0) true
      have hp_ne (p : Fin 13) : P p ≠ L 0 := by
        intro e
        have eq := congrArg Fin.val e
        change p.val = 13 at eq
        omega
      have hz : ¬ ∃ p l, E p l ∧ z (P p) = true ∧ z (L l) = true := by
        intro h
        obtain ⟨p,l,hpl,hp,hl⟩ := h
        rw [show z (P p) = x (P p) from Function.update_of_ne (hp_ne p) _ _] at hp
        by_cases el : l = 0
        · exact off p (el ▸ hpl) hp
        · have ne : L l ≠ L 0 := fun e => el (Fin.natAdd_injective 13 13 e)
          rw [show z (L l) = x (L l) from Function.update_of_ne ne _ _] at hl
          exact hx.1 ⟨p,l,hpl,hp,hl⟩
      have up : x ≤ z := by
        intro i
        by_cases e : i = L 0
        · subst i
          simp [z]
        · simp [z, Function.update_of_ne e]
      have back := hx.2 hz up (L 0)
      have hit : z (L 0) = true := Function.update_self _ _ _
      rw [hit] at back
      exact hzero (top_unique back)
