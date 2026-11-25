import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5278_678
    (packing :
    let E := incidences singerLines3
    ∀ (T : Finset ℕ) (H : ℕ → Finset (Fin 13 × Fin 13)),
      (∀ t ∈ T, H t ⊆ E) → (∀ e ∈ E, ∃ t ∈ T, e ∈ H t) →
      (∃ t ∈ T, ∃ a ∈ H t, ∃ b ∈ H t, a.1 ≠ b.1 ∧ a.2 ≠ b.2) ∨
      ((∀ t ∈ T, ∀ a ∈ H t, ∀ b ∈ H t, a.1 = b.1 ∨ a.2 = b.2) ∧
       ∃ U ⊆ T, 52 ≤ 3*T.card + U.card ∧ (∀ t ∈ U, ∀ u ∈ U, t ≠ u → Disjoint (H t) (H u)) ∧
         ∀ t ∈ U, (H t).card = 4))
    (large :
    let S := singerLines3
    let q := fun (Q : Finset (Fin 13)) => (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ missLines S Q))
    let qs := quadrangles S
    ∀ (C : Circuit) (T : Finset ℕ),
    let g := gateAt C
    let v := PEqualNP.LowMerge.wireVal C
    let E := incidences S
    let H := fun t : ℕ => E.filter (fun e => v (PEqualNP.LowMerge.pointLineInput 13 13 e.1 e.2) (26+t) = true)
    PEqualNP.TopForm.IsAO2 26 C → 38 ≤ C.size → C.size < 64 →
    (8 ≤ PEqualNP.ReadTwo.nAnd C ∧ 18 ≤ PEqualNP.ReadTwo.nOr C) →
    (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) → 2 ≤ PEqualNP.TopForm.andPairs 26 C →
    (∀ j < C.size, (g j).op = .and → ∀ a ∈ (g j).inputs,
      ∃ Q ∈ qs, v (q Q) (26+j) ≠ v (q Q) a) →
    (∀ t ∈ T, t < C.size ∧ (g t).op = .and ∧ ∀ Q ∈ qs, v (q Q) (26+t) = false) →
    2*T.card ≤ C.size+1 →
    (∀ x : List Bool, x.length = 26 → (C.eval x = true ↔ ∃ t ∈ T, v x (26+t) = true)) →
    (∀ e ∈ E, ∃ t ∈ T, e ∈ H t) →
    16 ≤ T.card →
    False)
    (crossed :
    let S := singerLines3
    let q := fun (Q : Finset (Fin 13)) => (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ missLines S Q))
    let qs := quadrangles S
    ∀ (C : Circuit) (T : Finset ℕ),
    let g := gateAt C
    let v := PEqualNP.LowMerge.wireVal C
    let E := incidences S
    let H := fun t : ℕ => E.filter (fun e => v (PEqualNP.LowMerge.pointLineInput 13 13 e.1 e.2) (26+t) = true)
    PEqualNP.TopForm.IsAO2 26 C → 38 ≤ C.size → C.size < 64 →
    (8 ≤ PEqualNP.ReadTwo.nAnd C ∧ 18 ≤ PEqualNP.ReadTwo.nOr C) →
    (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) → 2 ≤ PEqualNP.TopForm.andPairs 26 C →
    (∀ j < C.size, (g j).op = .and → ∀ a ∈ (g j).inputs,
      ∃ Q ∈ qs, v (q Q) (26+j) ≠ v (q Q) a) →
    (∀ t ∈ T, t < C.size ∧ (g t).op = .and ∧ ∀ Q ∈ qs, v (q Q) (26+t) = false) →
    2*T.card ≤ C.size+1 →
    (∀ x : List Bool, x.length = 26 → (C.eval x = true ↔ ∃ t ∈ T, v x (26+t) = true)) →
    (∀ e ∈ E, ∃ t ∈ T, e ∈ H t) →
    T.card ≤ 15 →
    (∃ t ∈ T, ∃ a ∈ H t, ∃ b ∈ H t, a.1 ≠ b.1 ∧ a.2 ≠ b.2) →
    False)
    (pencils :
    let S := singerLines3
    let q := fun (Q : Finset (Fin 13)) => (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ missLines S Q))
    let qs := quadrangles S
    ∀ (C : Circuit) (T : Finset ℕ),
    let g := gateAt C
    let v := PEqualNP.LowMerge.wireVal C
    let E := incidences S
    let H := fun t : ℕ => E.filter (fun e => v (PEqualNP.LowMerge.pointLineInput 13 13 e.1 e.2) (26+t) = true)
    PEqualNP.TopForm.IsAO2 26 C → 38 ≤ C.size → C.size < 64 →
    (8 ≤ PEqualNP.ReadTwo.nAnd C ∧ 18 ≤ PEqualNP.ReadTwo.nOr C) →
    (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) → 2 ≤ PEqualNP.TopForm.andPairs 26 C →
    (∀ j < C.size, (g j).op = .and → ∀ a ∈ (g j).inputs,
      ∃ Q ∈ qs, v (q Q) (26+j) ≠ v (q Q) a) →
    (∀ t ∈ T, t < C.size ∧ (g t).op = .and ∧ ∀ Q ∈ qs, v (q Q) (26+t) = false) →
    2*T.card ≤ C.size+1 →
    (∀ x : List Bool, x.length = 26 → (C.eval x = true ↔ ∃ t ∈ T, v x (26+t) = true)) →
    (∀ e ∈ E, ∃ t ∈ T, e ∈ H t) →
    T.card ≤ 15 →
    (∀ t ∈ T, ∀ a ∈ H t, ∀ b ∈ H t, a.1 = b.1 ∨ a.2 = b.2) →
    (∃ U ⊆ T, 7 ≤ U.card ∧ (∀ t ∈ U, ∀ u ∈ U, t ≠ u → Disjoint (H t) (H u)) ∧ ∀ t ∈ U, (H t).card = 4) →
    False) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;   have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;   PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (38 : ℕ) ≤ x3.size → x3.size < (64 : ℕ) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 → (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) → (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) → (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) → (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) → (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) → False := by
  intro q qs C T g v ao lo hi counts distinct nested active tops budget output cover
  let E := incidences singerLines3
  let H := fun t : ℕ => E.filter (fun e =>
    PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.pointLineInput 13 13 e.1 e.2) (26+t) = true)
  have cov (e) (he : e ∈ E) : ∃ t ∈ T, e ∈ H t := by
    obtain ⟨t,ht,hit⟩ := cover e.1 e.2 (Finset.mem_filter.mp he).2
    exact ⟨t,ht,Finset.mem_filter.mpr ⟨he,hit⟩⟩
  by_cases many : 16 ≤ T.card
  · exact large C T ao lo hi counts distinct nested active tops budget output cov many
  have small : T.card ≤ 15 := by omega
  rcases packing T H (fun t _ => Finset.filter_subset ..) cov with pair | stars
  · exact crossed C T ao lo hi counts distinct nested active tops budget output cov small pair
  · obtain ⟨U,sub,cap,dis,deg⟩ := stars.2
    exact pencils C T ao lo hi counts distinct nested active tops budget output cov small stars.1
      ⟨U,sub,by omega,dis,deg⟩
