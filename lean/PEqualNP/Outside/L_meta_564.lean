import PEqualNP.Defs

namespace Gap564
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private theorem fuel_stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (d e : ℕ) (i : Fin C.size) (hd : i.val < d) (he : i.val < e) :
    C.gateValFuel U d i = C.gateValFuel U e i := by
  induction d generalizing e i with
  | zero => omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      have side (B : Finset (Fin n)) (G : Finset (Fin C.size)) :
          sideTrue U B G i (C.gateValFuel U d) = sideTrue U B G i (C.gateValFuel U e) := by
        unfold sideTrue
        apply Bool.decide_congr
        apply or_congr Iff.rfl
        constructor <;> rintro ⟨j,hj,hji,hval⟩
        · exact ⟨j,hj,hji, (ih e j (by have := hji; omega) (by have := hji; omega)) ▸ hval⟩
        · exact ⟨j,hj,hji, (ih e j (by have := hji; omega) (by have := hji; omega)).symm ▸ hval⟩
      exact congrArg₂ Bool.and (side _ _) (side _ _)

end Gap564
namespace Gap564
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private inductive Live {n : ℕ} (C : AndCountCircuit n) : Fin C.size → Prop where
  | output {i} : i ∈ C.outGates → Live C i
  | left {k j} : Live C k → j ∈ C.leftGates k → Live C j
  | right {k j} : Live C k → j ∈ C.rightGates k → Live C j

end Gap564

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit Gap564 in
theorem PEqualNP.Outside.L_meta_564 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n),
    C.WellFormed →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
        C'.WellFormed ∧ C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
        (∀ i : Fin C'.size, i ∈ C'.outGates ∨
          ∃ k : Fin C'.size, i ∈ C'.leftGates k ∨ i ∈ C'.rightGates k) ∧
        ((∀ i : Fin C.size, ((C.leftVars i).Nonempty ∨ (C.leftGates i).Nonempty) ∧
            ((C.rightVars i).Nonempty ∨ (C.rightGates i).Nonempty)) →
          ∀ i : Fin C'.size, ((C'.leftVars i).Nonempty ∨ (C'.leftGates i).Nonempty) ∧
            ((C'.rightVars i).Nonempty ∨ (C'.rightGates i).Nonempty)) ∧
        ((∀ (i : Fin C.size) (v : Fin n), C.gateVal {v} i = false) →
          ∀ (i : Fin C'.size) (v : Fin n), C'.gateVal {v} i = false) := by
  classical
  intro n C hw
  let S := Finset.univ.filter (Live C)
  let e : Fin S.card ↪o Fin C.size := S.orderEmbOfFin rfl
  have kept (i : Fin S.card) : Live C (e i) :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl i)).2
  have original {j : Fin C.size} (h : Live C j) : ∃ i, e i = j := by
    have hj : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    rw [← S.image_orderEmbOfFin_univ rfl] at hj
    obtain ⟨i,_,hij⟩ := Finset.mem_image.mp hj
    exact ⟨i,hij⟩
  let pull (A : Finset (Fin C.size)) := Finset.univ.filter (fun i : Fin S.card => e i ∈ A)
  have mem {j : Fin S.card} {A : Finset (Fin C.size)} : j ∈ pull A ↔ e j ∈ A := by simp [pull]
  let D : AndCountCircuit n := {
    size := S.card
    leftVars := fun i => C.leftVars (e i)
    rightVars := fun i => C.rightVars (e i)
    leftGates := fun i => pull (C.leftGates (e i))
    rightGates := fun i => pull (C.rightGates (e i))
    outVars := C.outVars
    outGates := pull C.outGates }
  have hsize : D.size ≤ C.size := by
    have h := Finset.card_le_univ S
    simpa [D] using h
  have gateFuel (U : Finset (Fin n)) (d : ℕ) (i : Fin S.card) :
      D.gateValFuel U d i = C.gateValFuel U d (e i) := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      have side (B : Finset (Fin n)) (G : Finset (Fin C.size))
          (hclosed : ∀ j ∈ G, Live C j) :
          sideTrue U B (pull G) i (D.gateValFuel U d) =
            sideTrue U B G (e i) (C.gateValFuel U d) := by
        unfold sideTrue
        apply Bool.decide_congr
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨j,hj,hji,hv⟩
          exact ⟨e j,mem.mp hj,e.strictMono hji,(ih j).symm ▸ hv⟩
        · rintro ⟨j,hj,hji,hv⟩
          obtain ⟨j',rfl⟩ := original (hclosed j hj)
          exact ⟨j',mem.mpr hj,e.lt_iff_lt.mp hji,(ih j') ▸ hv⟩
      exact congrArg₂ Bool.and
        (side _ _ (fun _ h => Live.left (kept i) h))
        (side _ _ (fun _ h => Live.right (kept i) h))
  have gate (U : Finset (Fin n)) (i : Fin D.size) : D.gateVal U i = C.gateVal U (e i) := by
    unfold gateVal
    rw [fuel_stable D U D.size C.size i i.isLt (lt_of_lt_of_le i.isLt hsize)]
    exact gateFuel U C.size i
  refine ⟨D,?_,hsize,?_,?_,?_,?_⟩
  · intro i
    exact ⟨fun j hj => e.lt_iff_lt.mp ((hw (e i)).1 (e j) (mem.mp hj)),
      fun j hj => e.lt_iff_lt.mp ((hw (e i)).2 (e j) (mem.mp hj))⟩
  · intro U
    unfold eval
    apply Bool.decide_congr
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨i,hi,hv⟩
      exact ⟨e i,mem.mp hi,(gate U i).symm ▸ hv⟩
    · rintro ⟨j,hj,hv⟩
      obtain ⟨i,rfl⟩ := original (Live.output hj)
      exact ⟨i,mem.mpr hj,(gate U i) ▸ hv⟩
  · intro i
    have hi := kept i
    generalize hindex : e i = j at hi
    cases hi with
    | output h => exact Or.inl (mem.mpr (hindex ▸ h))
    | left hk hj =>
      obtain ⟨k,rfl⟩ := original hk
      exact Or.inr ⟨k,Or.inl (mem.mpr (hindex ▸ hj))⟩
    | right hk hj =>
      obtain ⟨k,rfl⟩ := original hk
      exact Or.inr ⟨k,Or.inr (mem.mpr (hindex ▸ hj))⟩
  · intro h i
    obtain ⟨hl,hr⟩ := h (e i)
    constructor
    · rcases hl with hvar|⟨j,hj⟩
      · exact Or.inl hvar
      · obtain ⟨k,rfl⟩ := original (Live.left (kept i) hj)
        exact Or.inr ⟨k,mem.mpr hj⟩
    · rcases hr with hvar|⟨j,hj⟩
      · exact Or.inl hvar
      · obtain ⟨k,rfl⟩ := original (Live.right (kept i) hj)
        exact Or.inr ⟨k,mem.mpr hj⟩
  · intro h i v
    exact (gate {v} i).trans (h (e i) v)
