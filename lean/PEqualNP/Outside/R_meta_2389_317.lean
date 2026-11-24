import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

-- On one fixed independent input, a circuit computing incidence must output false.
-- The remaining bound concerns minimum circuits with an internal AND true on that input.
theorem PEqualNP.Outside.R_meta_2389_317
    (dirty :
      let ok := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ C : Circuit, IsAO2 26 C → ok C → C.size < 64 →
        ∃ a b : Fin 26, C.eval (List.ofFn (pairInput a b)) = false ∧
          ∃ k < C.gates.length, (gateAt C k).op = .and ∧ gateVal 26 C k (pairInput a b) = true)
    (transport :
      let ok := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 26) (k : ℕ),
        PEqualNP.TopForm.IsAO2 26 C → ok C →
        C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) = false →
        k < C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.EdgeOwnership.gateVal 26 C k (PEqualNP.EdgeOwnership.pairInput a b) = true →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 26 D ∧ ok D ∧
          D.size=C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op =
            PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.gateVal 26 D k (fun i : Fin 26 => decide (i=0 ∨ i=1 ∨ i=15)) = true)
    (bound :
      let ok := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ D : Circuit, IsAO2 26 D → ok D →
        (∀ E : Circuit, IsAO2 26 E → ok E → D.size ≤ E.size) →
        (∃ k < D.gates.length, (gateAt D k).op = .and ∧
          gateVal 26 D k (fun i : Fin 26 => decide (i=0 ∨ i=1 ∨ i=15)) = true) →
        64 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  classical
  intro C hAO hC
  let ok := fun E : Circuit => ∀ x : Fin 26 → Bool, E.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let eligible := fun n : Nat => ∃ D : Circuit, IsAO2 26 D ∧ ok D ∧ D.size = n
  have existsSize : ∃ n, eligible n := ⟨C.size,C,hAO,hC,rfl⟩
  obtain ⟨M, hM, hok, hsize⟩ := Nat.find_spec existsSize
  have least (E : Circuit) (hE : IsAO2 26 E) (he : ok E) : M.size ≤ E.size := by
    rw [hsize]
    exact Nat.find_min' existsSize ⟨E,hE,he,rfl⟩
  have leC := least C hAO hC
  by_contra! bad
  obtain ⟨a,b,hn,k,hk,hop,hfire⟩ := dirty M hM hok (by omega)
  obtain ⟨D,hD,hd,ds,do',df⟩ := transport M a b k hM hok hn hk hop hfire
  have dmin (E : Circuit) (hE : IsAO2 26 E) (he : ok E) : D.size ≤ E.size :=
    ds.trans_le (least E hE he)
  have kD : k < D.gates.length := by
    change k < D.size
    rw [ds]
    exact hk
  have lb := bound D hD hd dmin ⟨k,kD,do',df⟩
  omega
