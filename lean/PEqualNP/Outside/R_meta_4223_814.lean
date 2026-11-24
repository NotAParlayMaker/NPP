import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4223_814
    (profile : ∀ (C : Circuit),
      let E : List (Fin 9 × Fin 9) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).map
        (fun d => (Fin.ofNat 9 (d/10), Fin.ofNat 9 (d%10)))
      let I (j : Fin C.size) := (C.gates.get j).inputs
      let W (x : Fin 9 → Bool) (u : ℕ) := (C.wires (List.ofFn x)).getD u false
      IsMinimalCircuit 9 C → IsAO2 9 C →
      (circuitFun 9 C = fun x => E.any fun e => x e.1 && x e.2) →
      ∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ (r : Fin C.size) (u : ℕ),
        (∀ j, v.val ∈ I j ↔ j=r) → (C.gates.get r).op = .or →
        u ∈ I r → u ≠ v.val →
        (∀ t : Fin 9, W (fun k => decide (k=t)) u = false) ∧
        ∃ e ∈ E, v ≠ e.1 ∧ v ≠ e.2 ∧
          let x (k : Fin 9) := decide (k=e.1 ∨ k=e.2)
          W x u = true ∧
          ({ C with gates := C.gates.set r.val ⟨.or,[v.val]⟩ } : Circuit).eval (List.ofFn x) = false)
    (residual : ∀ (C : Circuit),
      let E : List (Fin 9 × Fin 9) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).map
        (fun d => (Fin.ofNat 9 (d/10), Fin.ofNat 9 (d%10)))
      let I (j : Fin C.size) := (C.gates.get j).inputs
      let W (x : Fin 9 → Bool) (u : ℕ) := (C.wires (List.ofFn x)).getD u false
      IsMinimalCircuit 9 C → C.size ≤ 15 → IsAO2 9 C →
      (circuitFun 9 C = fun x => E.any fun e => x e.1 && x e.2) → (∀ j, (I j).Nodup) →
      (∀ v ∈ ([4,6,7] : List (Fin 9)), ∃ (r : Fin C.size) (u : ℕ),
        (∀ j, v.val ∈ I j ↔ j=r) ∧ (C.gates.get r).op = .or ∧
        u ∈ I r ∧ 9 ≤ u ∧ (∀ t : Fin 9, W (fun k => decide (k=t)) u = false) ∧
        ∃ e ∈ E, v ≠ e.1 ∧ v ≠ e.2 ∧
          let x (k : Fin 9) := decide (k=e.1 ∨ k=e.2)
          W x u = true ∧
          ({ C with gates := C.gates.set r.val ⟨.or,[v.val]⟩ } : Circuit).eval (List.ofFn x) = false) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∀ (x8 : Fin x1.size), (x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  intro C min size correct shape unique _separate noNot
  have hAO : IsAO2 9 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
      have h := (min.1 _ (List.get_mem C.gates j)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h.imp_right (fun ho => ho.resolve_right (noNot j))
    · intro j hj
      have eq : gateAt C j = C.gates.get ⟨j,hj⟩ := by
        change C.gates.getD j ⟨.or,[]⟩ = C.gates.get ⟨j,hj⟩
        simp [List.getD_eq_getElem?_getD, hj]
      rw [eq]
      exact (shape ⟨j,hj⟩).1
    · intro g hg
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hg
      exact ((shape j).2.2.resolve_left (fun h => noNot j h.1)).2
  refine residual C min size hAO correct (fun j => (shape j).2.1) ?_
  intro v hv
  obtain ⟨r,hr,hop⟩ := unique v hv
  have len := hAO.2.2 _ (List.get_mem C.gates r)
  obtain ⟨a,b,pins⟩ := List.length_eq_two.mp len
  have vmem := (hr r).2 rfl
  have differ : a ≠ b := by
    have nodup := (shape r).2.1
    simpa [pins] using nodup
  obtain ⟨u,umem,uv⟩ : ∃ u ∈ (C.gates.get r).inputs, u ≠ v.val := by
    rw [pins] at vmem ⊢
    simp only [List.mem_cons,List.not_mem_nil,or_false] at vmem ⊢
    rcases vmem with h|h
    · exact ⟨b,Or.inr rfl,h ▸ differ.symm⟩
    · exact ⟨a,Or.inl rfl,h ▸ differ⟩
  obtain ⟨hs,he⟩ := profile C min hAO correct v hv r u hr hop umem uv
  refine ⟨r,u,hr,hop,umem,?_,hs,he⟩
  by_contra! hu
  let t : Fin 9 := ⟨u,hu⟩
  have hf := hs t
  have prefixKeep (gs : List Gate) (l : List Bool) (i : ℕ) (hi : i < l.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) l).getD i false =
      l.getD i false := by
    induction gs generalizing l with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi
  change (C.wires (List.ofFn (fun k : Fin 9 => decide (k=t)))).getD u false = false at hf
  unfold Circuit.wires at hf
  rw [prefixKeep _ _ _ (by simpa using hu)] at hf
  have hget : (List.ofFn (fun k : Fin 9 => decide (k=t))).getD u false = true := by
    have hlt : u < (List.ofFn (fun k : Fin 9 => decide (k=t))).length := by
      simpa only [List.length_ofFn] using hu
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
    exact decide_eq_true rfl
  rw [hget] at hf
  contradiction
