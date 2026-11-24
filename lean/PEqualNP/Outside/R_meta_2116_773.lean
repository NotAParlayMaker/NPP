import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2116_773
    (noRaw :
      let target := fun x : Fin 9 → Bool =>
            x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
              x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
              x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (C : Circuit) (u v : Fin 9) (i : Fin C.size),
        circuitFun 9 C = target → u ∈ ([4,6,7] : List (Fin 9)) → u ≠ v →
        (C.gates.get i).op = GateOp.or →
        (∀ j : Fin C.size, u.val ∈ (C.gates.get j).inputs ↔ j = i) →
        v.val ∉ (C.gates.get i).inputs)
    (firstPartner :
      let target := fun x : Fin 9 → Bool =>
            x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
              x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
              x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (C : Circuit) (u : Fin 9) (i z : Fin C.size),
        circuitFun 9 C = target → u ∈ ([4,6,7] : List (Fin 9)) → z.val = 0 →
        9 ∈ (C.gates.get i).inputs → 9 < 9 + i.val → (C.gates.get i).op = GateOp.or →
        (∀ k : Fin C.size, u.val ∈ (C.gates.get k).inputs → k = i) →
        ((C.gates.get z).op = GateOp.and ∨ (C.gates.get z).op = GateOp.or ∨
          (C.gates.get z).op = GateOp.not) →
        (C.gates.get z).inputs.Nodup →
        ((C.gates.get z).op = GateOp.not ∧ (C.gates.get z).inputs.length = 1 ∨
          (C.gates.get z).op ≠ GateOp.not ∧ (C.gates.get z).inputs.length = 2) →
        (∀ w ∈ (C.gates.get z).inputs, ∃ v : Fin 9, w = v.val ∧ v ∉ ([4,6,7] : List (Fin 9))) →
        (C.gates.get z).op = GateOp.and)
    (search :
      let target := fun x : Fin 9 → Bool =>
            x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
              x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
              x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (C : Circuit), IsMinimalCircuit 9 C → C.size ≤ 15 → circuitFun 9 C = target →
        (∀ i : Fin C.size, ∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) →
        (∀ i : Fin C.size,
          ((C.gates.get i).op = GateOp.not ∧ (C.gates.get i).inputs.length = 1) ∨
          ((C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length = 2 ∧ (C.gates.get i).inputs.Nodup)) →
        (∀ u ∈ ([4,6,7] : List (Fin 9)), ∃ (i : Fin C.size) (w : ℕ),
          9 ≤ w ∧ (C.gates.get i).op = GateOp.or ∧
          (C.gates.get i).inputs.Perm [u.val,w] ∧
          (∀ j : Fin C.size, u.val ∈ (C.gates.get j).inputs ↔ j = i) ∧
          (w = 9 → ∀ z : Fin C.size, z.val = 0 → (C.gates.get z).op = GateOp.and)) → False) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C model single
  obtain ⟨minimal, size, computes, shape, _⟩ := model
  have internals : ∀ u ∈ ([4,6,7] : List (Fin 9)), ∃ (i : Fin C.size) (w : ℕ),
      9 ≤ w ∧ (C.gates.get i).op = GateOp.or ∧ (C.gates.get i).inputs.Perm [u.val,w] ∧
        ∀ j : Fin C.size, u.val ∈ (C.gates.get j).inputs ↔ j = i := by
    intro u hu
    obtain ⟨card, op⟩ := single u hu
    let readers : Finset (Fin C.size) := Finset.univ.filter fun j => u.val ∈ (C.gates.get j).inputs
    change readers.card = 1 at card
    obtain ⟨i, eq⟩ := Finset.card_eq_one.mp card
    have hit : ∀ j : Fin C.size, u.val ∈ (C.gates.get j).inputs ↔ j = i := by
      intro j
      have same : j ∈ readers ↔ u.val ∈ (C.gates.get j).inputs := by simp [readers]
      rw [eq, Finset.mem_singleton] at same
      exact same.symm
    have hop : (C.gates.get i).op = GateOp.or := op i (by change i ∈ readers; rw [eq]; simp)
    have len : (C.gates.get i).inputs.length = 2 := by
      rcases (shape i).2.2 with ⟨e,_⟩ | ⟨_,h⟩
      · rw [hop] at e
        contradiction
      · exact h
    obtain ⟨a,b,listed⟩ := List.length_eq_two.mp len
    have different : a ≠ b := by
      have nodup := (shape i).2.1
      simpa [listed] using nodup
    have own : u.val = a ∨ u.val = b := by
      have h := (hit i).mpr rfl
      simpa [listed] using h
    have partner (w : ℕ) (ne : u.val ≠ w) (member : w ∈ (C.gates.get i).inputs) : 9 ≤ w := by
      by_contra! hw
      let v : Fin 9 := ⟨w,hw⟩
      have diff : u ≠ v := fun he => ne (congrArg Fin.val he)
      exact (noRaw C u v i computes hu diff hop hit) member
    rcases own with ea | eb
    · refine ⟨i,b,partner b (ea.trans_ne different) (by simp [listed]),hop,?_ ,hit⟩
      rw [listed,ea]
    · refine ⟨i,a,partner a (eb.trans_ne different.symm) (by simp [listed]),hop,?_ ,hit⟩
      rw [listed,eb]
      exact List.Perm.swap _ _ _

  refine search C minimal size computes (fun i => (shape i).1) ?_ ?_
  · intro i
    rcases (shape i).2 with ⟨nodup, read⟩
    rcases read with ⟨e,len⟩ | ⟨e,len⟩
    · exact Or.inl ⟨e,len⟩
    · exact Or.inr ⟨e,len,nodup⟩

  · intro u hu
    obtain ⟨i,w,hw,hop,hperm,hit⟩ := internals u hu
    refine ⟨i,w,hw,hop,hperm,hit,?_⟩
    intro ew z hz
    subst w
    have read9 : 9 ∈ (C.gates.get i).inputs := hperm.mem_iff.mpr (by simp)
    have basis : (C.gates.get z).op = GateOp.and ∨ (C.gates.get z).op = GateOp.or ∨
        (C.gates.get z).op = GateOp.not := by
      have h := (minimal.1 _ (List.get_mem C.gates z)).1
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    refine firstPartner C u i z computes hu hz read9 ((shape i).1 _ read9) hop
      (fun k h => (hit k).mp h) basis (shape z).2.1 (shape z).2.2 ?_
    intro t ht
    have raw : t < 9 := by simpa [hz] using (shape z).1 t ht
    let v : Fin 9 := ⟨t,raw⟩
    have core : v ∉ ([4,6,7] : List (Fin 9)) := by
      intro hs
      obtain ⟨k,r,hr,_,hp,only⟩ := internals v hs
      have kz := (only z).mp ht
      have read := hp.mem_iff.mpr (by simp : r ∈ [v.val,r])
      rw [← kz] at read
      have before := (shape z).1 r read
      omega
    exact ⟨v,rfl,core⟩
