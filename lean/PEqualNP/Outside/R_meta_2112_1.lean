import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2112_1
    (nine : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) 14)
    (eight : ∀ v ∈ ([4,6,7] : List (Fin 9)), ¬ HasCircuitSize 8
      (fun x => (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) (v.insertNth false x)) 12)
    (propagate : ∀ (C : Circuit) (v : Fin 9) (a : Fin C.size) (T : Finset (Fin C.size)),
      (∀ j ∈ T, a < j ∧ 9 + a.val ∈ (C.gates.get j).inputs) → FanInTwo C →
      (∀ j : Fin C.size, (C.gates.get j).op = .not → (C.gates.get j).inputs.length = 1) →
      v.val ∈ (C.gates.get a).inputs → (C.gates.get a).op ≠ .or →
      (∃ x : Fin 8 → Bool, C.eval (List.ofFn (v.insertNth false x)) = false) →
      ∃ D : Circuit, FanInTwo D ∧
        D.size + 1 + T.card ≤ C.size ∧
        ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (v.insertNth false x)))
    (terminal : ∀ (C : Circuit) (v : Fin 9) (a : Fin C.size),
      let r := fun w : Nat => Finset.univ.filter (fun j : Fin C.size => w ∈ (C.gates.get j).inputs)
      IsMinimalCircuit 9 C → C.size = 15 →
      (∀ j : Fin C.size, let g := C.gates.get j
        (∀ w ∈ g.inputs, w < 9 + j.val) ∧ g.inputs.Nodup ∧
          (g.op = .not ∧ g.inputs.length = 1 ∨ g.op ≠ .not ∧ g.inputs.length = 2)) →
      (∀ u ∈ ([4,6,7] : List (Fin 9)), (r u.val).Nonempty ∧ (r u.val).card ≤ 2 ∧
        ((r u.val).card = 2 → ∀ j ∈ r u.val, (C.gates.get j).op = .or)) →
      v ∈ ([4,6,7] : List (Fin 9)) → r v.val = {a} → (C.gates.get a).op ≠ .or →
      (r (9 + a.val)).card ≤ 1 → ∃ x, circuitFun 9 C x ≠ (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) x) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∃ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ x7 ∈ x2 x4 x6, (x4.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C h bad
  obtain ⟨minimal, size, computes, normal, degree⟩ := h
  obtain ⟨v, special, a, member, nonOr⟩ := bad
  let f := (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
  have evalF (x : Fin 9 → Bool) : circuitFun 9 C x = f x := by
    rw [congrFun computes x]
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  have hn : 15 ≤ C.size := by
    by_contra small
    exact nine ⟨C, minimal.1, by omega, evalF⟩
  let r := fun w : Nat => Finset.univ.filter (fun j : Fin C.size => w ∈ (C.gates.get j).inputs)
  change a ∈ r v.val at member
  have single : r v.val = {a} := by
    obtain ⟨_,hu,hor⟩ := degree v special
    change (r v.val).card ≤ 2 at hu
    have hn2 : (r v.val).card ≠ 2 := fun h2 => nonOr (hor h2 a member)
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨member, fun j hj =>
      Finset.card_le_one.mp (by omega) _ hj _ member⟩
  have zero : ∃ x : Fin 8 → Bool, C.eval (List.ofFn (v.insertNth false x)) = false := by
    refine ⟨fun _ => false, ?_⟩
    have z : v.insertNth false (fun _ : Fin 8 => false) = fun _ => false := by
      funext i
      exact v.succAboveCases (by simp) (fun j => by simp) i
    rw [z]
    exact evalF _
  have later : ∀ j ∈ r (9+a.val), a < j ∧ 9 + a.val ∈ (C.gates.get j).inputs := by
    intro j hm
    have hmem := (Finset.mem_filter.mp hm).2
    have hb := (normal j).1 _ hmem
    exact ⟨(show a.val < j.val by omega), hmem⟩
  obtain ⟨D,fan,save,same⟩ := propagate C v a _ later minimal.1 (fun j hj =>
    ((normal j).2.2.elim And.right (fun no => (no.1 hj).elim)))
    (Finset.mem_filter.mp member).2 nonOr zero
  have lo : 13 ≤ D.size := by
    by_contra small
    exact eight v special ⟨D,fan,by omega,fun x => (same x).trans (evalF _)⟩
  have consumers : (r (9+a.val)).card ≤ 1 := by omega
  obtain ⟨x,fail⟩ := terminal C v a minimal (by omega) normal degree special single nonOr consumers
  exact fail (evalF x)
