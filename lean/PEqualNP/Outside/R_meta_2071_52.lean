import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_2071_52
    (boundaryCount : ∀ C : Circuit, C.size ≤ 64 → IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → 0 < andPairs 26 C →
      let V := fun (x : Fin 26 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
      let inc := fun p l : Fin 13 => p ∈ PEqualNP.HeptadCover.singerLines3 l
      let hit := fun x : Fin 26 → Bool => ∃ p l, inc p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      (∀ x, Minimal hit x → V x C.output = true) →
      (∀ x, Maximal (fun y => ¬ hit y) x → V x C.output = false) →
      (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧
        ∃ x, V x (26+j) = true ∧ V x C.output = false) →
      ∀ p l, inc p l →
      let a := (Fin.castAdd 13 p).val
      let b := (Fin.natAdd 13 l).val
      let cost := fun v => (scalarMults C 26 [a,b] v).getD C.output none
      cost b = some 1 ∨ cost a = some 1)
    (readOne : ∀ (n : ℕ) (C : Circuit) (s t : Fin n) (u v : ℕ) (d : ℕ → Bool),
      (u = s.val ∧ v = t.val ∨ u = t.val ∧ v = s.val) →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
          g.inputs = [a,b] ∧ a < n+j ∧ b < n+j) →
      (∀ i < n, d i = decide (i = t.val)) →
      let base := C.wires (List.ofFn fun i : Fin n => decide (i = s))
      (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (n+j) = ((base.getD a false && d b) || (d a && base.getD b false))) ∧
        (g.op = .or → d (n+j) = (d a || d b))) →
      (scalarMults C n [u,v] t.val).getD C.output none = some 1 → d C.output = true) : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  intro C p l leftTrace rightTrace limit gates correct nested dirty edge leftLaw rightLaw
  have model : IsAO2 26 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      exact (gates j g hj).1
    · intro j hj i hi
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
      have hg : C.gates[j]? = some g := by
        change C.gates[j]? = some (C.gates.getD j ⟨.or,[]⟩)
        rw [List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]
      change i ∈ g.inputs at hi
      obtain ⟨a,b,pins,_,ha,hb⟩ := (gates j g hg).2
      simp [pins] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨a,b,pins,_⟩ := (gates j g hj).2
      simp [pins]
  have distinct : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨a,b,pins,ne,_⟩ := (gates j g hj).2
    simp [pins,ne]
  have binary (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a < 26+j ∧ b < 26+j := by
    obtain ⟨kind,a,b,pins,_,ha,hb⟩ := gates j g hg
    exact ⟨kind,a,b,pins,ha,hb⟩
  have incidence : ∀ a b : Fin 13, a ∈ PEqualNP.HeptadCover.singerLines3 b ↔
      a-b ∈ ({0,1,3,9} : Finset (Fin 13)) := by
    intro a b
    have e : a.val + 13 - b.val = (13 - b.val) + a.val := by omega
    change a ∈ Finset.univ.filter (fun q : Fin 13 =>
      (q.val + 13 - b.val) % 13 ∈ ({0,1,3,9} : Finset ℕ)) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_sub, e]
    rfl
  have plane (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 13, a ∈ PEqualNP.HeptadCover.singerLines3 b ∧
        x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true := by
    simpa only [incidence] using correct x
  have costs := boundaryCount C limit model distinct nested
    (fun x h => (plane x).2 h.1)
    (fun x h => Bool.eq_false_iff.mpr fun yes => h.1 ((plane x).1 yes))
    dirty p l ((incidence p l).2 edge)
  let P := Fin.castAdd 13 p
  let L := Fin.natAdd 13 l
  rcases costs with hc | hc
  · left
    apply readOne 26 C P L P.val L.val leftTrace (Or.inl ⟨rfl,rfl⟩) binary _ leftLaw.2 hc
    intro i hi
    simpa [L,Nat.add_comm] using leftLaw.1 i hi
  · right
    apply readOne 26 C L P P.val L.val rightTrace (Or.inr ⟨rfl,rfl⟩) binary _ rightLaw.2 hc
    exact rightLaw.1
