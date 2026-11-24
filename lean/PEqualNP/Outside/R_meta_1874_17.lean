import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.LowMerge

-- Relabeling variables costs no gates. Projective symmetries put every ordered
-- pair of distinct quadrangles into one of seventeen positions.
theorem PEqualNP.Outside.R_meta_1874_17
    (rename : ∀ (σ τ : Equiv.Perm (Fin 13)) (C : Circuit),
      Monotone2 C → ReadsBack 26 C →
      ∃ (D : Circuit) (r : ℕ → ℕ), D.size = C.size ∧ Monotone2 D ∧ ReadsBack 26 D ∧
        (∀ w < 26 + C.size, r w < 26 + D.size) ∧
        ∀ (w : ℕ) (X Y : Finset (Fin 13)),
          wireVal D (incidenceInput (σ.finsetCongr X) (τ.finsetCongr Y)) (r w) =
          wireVal C (incidenceInput X Y) w)
    (orbit : ∀ Q R : Finset (Fin 13),
      IsQuadrangle singerLines3 Q → IsQuadrangle singerLines3 R → Q ≠ R →
      ∃ σ τ : Equiv.Perm (Fin 13),
        (∀ p l : Fin 13, p ∈ singerLines3 l ↔ σ p ∈ singerLines3 (τ l)) ∧
        (∀ X, IsQuadrangle singerLines3 X ↔ IsQuadrangle singerLines3 (σ.finsetCongr X)) ∧
        (∀ X, τ.finsetCongr (missLines singerLines3 X) = missLines singerLines3 (σ.finsetCongr X)) ∧
        σ.finsetCongr Q = {0, 1, 2, 5} ∧
        ∃ m ∈ ([71, 83, 195, 201, 275, 281, 664, 1049, 2067, 2185, 2248, 2632, 4163, 4233, 4289, 4737, 5312] : List ℕ),
          ∀ i : Fin 13, i ∈ σ.finsetCongr R ↔ m.testBit i.val = true)
    (anchored : ∀ (D : Circuit) (a b : ℕ), Monotone2 D → ReadsBack 26 D →
      a < 26 + D.size → b < 26 + D.size →
      let V := fun (w : ℕ) (X : Finset (Fin 13)) =>
        wireVal D (incidenceInput X (missLines singerLines3 X)) w
      let base : Finset (Fin 13) := {0, 1, 2, 5}
      RightOnIncidentPairs singerLines3 ⟨D.gates, a⟩ →
      RightOnIncidentPairs singerLines3 ⟨D.gates, b⟩ →
      (∀ X, IsQuadrangle singerLines3 X → V a X = false ∨ V b X = false) →
      (V a base = false ∧ V b base = true) →
      (∃ X, IsQuadrangle singerLines3 X ∧
        (∃ m ∈ ([71, 83, 195, 201, 275, 281, 664, 1049, 2067, 2185, 2248, 2632, 4163, 4233, 4289, 4737, 5312] : List ℕ),
          ∀ i : Fin 13, i ∈ X ↔ m.testBit i.val = true) ∧
        V b X = false ∧ V a X = true) → 63 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intro C a b hmon hback ha hb diff pos neg good V hpos hneg hfirst hsecond
  have incidence : ∀ p l : Fin 13, p - l ∈ diff ↔ p ∈ singerLines3 l := by decide
  have positive (p l : Fin 13) : incidenceInput {p} {l} = pos p l := by
    change (List.ofFn (fun u : Fin 13 => decide (u ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun v : Fin 13 => decide (v ∈ ({l} : Finset (Fin 13))))) =
      List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
    simp only [Finset.mem_singleton]
  have quad (X : Finset (Fin 13)) : good X ↔ IsQuadrangle singerLines3 X := by
    have filt (l : Fin 13) : X.filter (fun p => p - l ∈ diff) = X ∩ singerLines3 l := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter, incidence]
    change (X.card = 4 ∧ ∀ l, (X.filter (fun p => p - l ∈ diff)).card ≤ 2) ↔
      (X.card = 4 ∧ ∀ l, (X ∩ singerLines3 l).card ≤ 2)
    simp only [filt]
  have negative (X : Finset (Fin 13)) : incidenceInput X (missLines singerLines3 X) = neg X := by
    have misses (l : Fin 13) : l ∈ missLines singerLines3 X ↔ ∀ p ∈ X, p - l ∉ diff := by
      change (l ∈ Finset.univ.filter (fun v : Fin 13 => Disjoint (singerLines3 v) X)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right, incidence]
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 X))) =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin 13 => decide (∀ p ∈ X, p - l ∉ diff))
    simp only [misses]
  obtain ⟨Q, hQ, hQa, hQb⟩ := hfirst
  obtain ⟨R, hR, hRb, hRa⟩ := hsecond
  have different : Q ≠ R := by
    rintro rfl
    rw [hQa] at hRa
    exact (by decide : false ≠ true) hRa
  obtain ⟨σ, τ, hi, hquad, hmiss, hbase, hmask⟩ :=
    orbit Q R ((quad Q).mp hQ) ((quad R).mp hR) different
  obtain ⟨D, r, hsize, hmonoD, hbackD, hrange, hw⟩ := rename σ τ C hmon hback
  have negmap (w : ℕ) (X : Finset (Fin 13)) :
      wireVal D (incidenceInput (σ.finsetCongr X) (missLines singerLines3 (σ.finsetCongr X))) (r w) =
      V w (neg X) := by
    change wireVal D _ (r w) = wireVal C (neg X) w
    simpa only [hmiss, negative] using hw w X (missLines singerLines3 X)
  have both (p l : Fin 13) (hp : p ∈ singerLines3 l) :
      wireVal D (incidenceInput {p} {l}) (r a) = true ∧
      wireVal D (incidenceInput {p} {l}) (r b) = true := by
    obtain ⟨p, rfl⟩ := σ.surjective p
    obtain ⟨l, rfl⟩ := τ.surjective l
    have h := hpos p l ((incidence p l).mpr ((hi p l).mpr hp))
    have mapped (w : ℕ) : wireVal D (incidenceInput {σ p} {τ l}) (r w) = V w (pos p l) := by
      change wireVal D _ (r w) = wireVal C (pos p l) w
      simpa only [Equiv.finsetCongr_apply, Finset.map_singleton, Equiv.coe_toEmbedding, positive]
        using hw w {p} {l}
    exact ⟨(mapped a).trans h.1, (mapped b).trans h.2⟩
  rw [← hsize]
  apply anchored D (r a) (r b) hmonoD hbackD (hrange a ha) (hrange b hb)
    (fun l p hp => (both p l hp).1) (fun l p hp => (both p l hp).2)
  · intro Y hY
    obtain ⟨X, rfl⟩ := σ.finsetCongr.surjective Y
    rcases hneg X ((quad X).mpr ((hquad X).mpr hY)) with h | h
    · exact Or.inl ((negmap a X).trans h)
    · exact Or.inr ((negmap b X).trans h)
  · change wireVal D _ (r a) = false ∧ wireVal D _ (r b) = true
    rw [← hbase]
    exact ⟨(negmap a Q).trans hQa, (negmap b Q).trans hQb⟩
  · exact ⟨σ.finsetCongr R, (hquad R).mp ((quad R).mp hR), hmask,
      (negmap b R).trans hRb, (negmap a R).trans hRa⟩
