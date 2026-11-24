import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

-- An unsafe AND accepting at most one incidence flag has a canonical replacement.
-- The remaining task need only shorten circuits containing a gate outside that class.
theorem PEqualNP.Outside.R_meta_2389_41
    (counting : let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+13-v.val%13)%13 ∈ ([0,1,3,9] : List Nat))
      let ok := fun (C : Circuit) => IsAO2 26 C ∧ ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧
          x (Fin.natAdd 13 l) = true
      let good := fun (C : Circuit) => ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
        BelowF G C k ∨ (gammaE G C k).card ≤ 1
      ∀ C, ok C → good C → 64 ≤ C.size)
    (shortening : let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+13-v.val%13)%13 ∈ ([0,1,3,9] : List Nat))
      let ok := fun (C : Circuit) => IsAO2 26 C ∧ ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧
          x (Fin.natAdd 13 l) = true
      ∀ C, ok C → C.size < 64 →
        (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
          ¬ BelowF G C k ∧ 2 ≤ (gammaE G C k).card) →
        ∃ D, ok D ∧ D.size < C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  intro C ao computes
  classical
  let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+13-v.val%13)%13 ∈ ([0,1,3,9] : List Nat))
  let ok := fun (C : Circuit) => IsAO2 26 C ∧ ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧
          x (Fin.natAdd 13 l) = true
  let good := fun (C : Circuit) => ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
        BelowF G C k ∨ (gammaE G C k).card ≤ 1
  have count : ∀ A, ok A → good A → 64 ≤ A.size := counting
  have shrink : ∀ A, ok A → A.size < 64 →
      (∃ k < A.gates.length, (gateAt A k).op = GateOp.and ∧
        ¬ BelowF G A k ∧ 2 ≤ (gammaE G A k).card) →
      ∃ D, ok D ∧ D.size < A.size := shortening
  have Cok : ok C := ⟨ao, computes⟩
  have start : ∃ n : Nat, ∃ D : Circuit, ok D ∧ D.size = n := ⟨_,C,Cok,rfl⟩
  obtain ⟨A,hA,hs⟩ := Nat.find_spec start
  have leC := Nat.find_min' start (show ∃ D : Circuit, ok D ∧ D.size = C.size from ⟨C,Cok,rfl⟩)
  by_contra hn
  have small : A.size < 64 := by omega
  by_cases ha : good A
  · have lb := count A hA ha
    omega
  · change ¬ (∀ k < A.gates.length, (gateAt A k).op = GateOp.and →
        BelowF G A k ∨ (gammaE G A k).card ≤ 1) at ha
    obtain ⟨k, h⟩ := Classical.not_forall.mp ha
    have hk : k < A.gates.length := by
      by_contra hge
      exact h (fun hlt => False.elim (hge hlt))
    have hop : (gateAt A k).op = GateOp.and := by
      by_contra hnon
      exact h (fun _ heq => False.elim (hnon heq))
    have hb : ¬ BelowF G A k := fun hbelow => h (fun _ _ => Or.inl hbelow)
    have hcard : ¬ (gammaE G A k).card ≤ 1 := fun hle => h (fun _ _ => Or.inr hle)
    obtain ⟨D,hD,smaller⟩ := shrink A hA small ⟨k,hk,hop,hb,by omega⟩
    have least := Nat.find_min' start (show ∃ E : Circuit, ok E ∧ E.size = D.size from ⟨D,hD,rfl⟩)
    omega
