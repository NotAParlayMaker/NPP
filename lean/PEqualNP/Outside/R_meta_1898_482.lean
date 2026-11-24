import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each paid instruction is an AND of two arbitrary ORs of the available wires.
-- The compiler is the AND-count dual of the checked OR-count compiler L-meta-4053.
theorem PEqualNP.Outside.R_meta_1898_482
    (compile : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     ∃ (x4 : List (Finset ℕ × Finset ℕ)) (x5 : Finset ℕ),       x4.length = {x6 : Fin x2.gates.length | (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ∧         (∀ (x6 : ℕ) (x7 : x6 < x4.length), ∀ x8 ∈ x4[x6].1 ∪ x4[x6].2, x8 < x1 + (1 : ℕ) + x6) ∧           (∀ x6 ∈ x5, x6 < x1 + (1 : ℕ) + x4.length) ∧             ∀ (x6 : Fin x1 → Bool),               x2.eval (List.ofFn x6) =                 have x7 : List Bool := List.foldl (fun (x7 : List Bool) (x8 : Finset ℕ × Finset ℕ) => x7 ++ [Decidable.decide (∃ x9 ∈ x8.1, x7.getD x9 Bool.false = Bool.true) && Decidable.decide (∃ x9 ∈ x8.2, x7.getD x9 Bool.false = Bool.true)]) (List.ofFn x6 ++ [Bool.true]) x4;                 Decidable.decide (∃ x8 ∈ x5, x7.getD x8 Bool.false = Bool.true))
    (ten : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (10 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    (failure : let I := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
    let D := fun (P : Finset (Fin 13)) => Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ P, ¬ I p l)
    let X := fun (P L : Finset (Fin 13)) (i : Fin 26) => decide
      ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, i = Fin.natAdd 13 l)
    let val := fun (w : List Bool) (s : Finset ℕ) => decide (∃ i ∈ s, w.getD i false = true)
    ∀ (A : List (Finset ℕ × Finset ℕ)) (B : Finset ℕ),
      10 ≤ A.length → A.length ≤ 12 →
      (∀ k (h : k < A.length), ∀ i ∈ A[k].1 ∪ A[k].2, i < 27+k) →
      (∀ i ∈ B, i < 27+A.length) →
      let F := fun (x : Fin 26 → Bool) =>
        val (A.foldl (fun w a => w ++ [val w a.1 && val w a.2]) (List.ofFn x ++ [true])) B
      (∀ p l : Fin 13, I p l → F (X {p} {l}) = true) →
      ∃ P : Finset (Fin 13), (∀ p ∉ P, ∃ l ∈ D P, I p l) ∧
        (¬∃ l, ∀ p ∈ P, I p l) ∧ (¬∃ p, ∀ l ∈ D P, I p l) ∧ F (X P (D P)) = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C hm hp hn
  by_contra small
  obtain ⟨A, B, length, ordered, last, eval⟩ := compile 26 C hm
  have cost := ten C hm hp hn
  have floor : 10 ≤ A.length := by omega
  have cap : A.length ≤ 12 := by omega
  let I := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let D := fun (P : Finset (Fin 13)) => Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ P, ¬ I p l)
  let X := fun (P L : Finset (Fin 13)) (i : Fin 26) => decide
    ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, i = Fin.natAdd 13 l)
  let val := fun (w : List Bool) (s : Finset ℕ) => decide (∃ i ∈ s, w.getD i false = true)
  let F := fun (x : Fin 26 → Bool) =>
    val (A.foldl (fun w a => w ++ [val w a.1 && val w a.2]) (List.ofFn x ++ [true])) B
  have agrees (x : Fin 26 → Bool) : circuitFun 26 C x = F x := eval x
  have pos (p l : Fin 13) (h : I p l) : F (X {p} {l}) = true := by
    rw [← agrees]
    simpa only [X,Finset.mem_singleton,exists_eq_left] using hp p l h
  obtain ⟨P,closed,gp,gl,on⟩ := failure A B floor cap ordered last pos
  change F (X P (D P)) = true at on
  have dl (l : Fin 13) : l ∈ D P ↔ ∀ p ∈ P, ¬ I p l := by simp [D]
  have off := hn P (fun p h => by
    obtain ⟨l,hl,e⟩ := closed p h
    exact ⟨l,(dl l).mp hl,e⟩) ⟨gp,fun ex => ex.elim (fun p hp => gl ⟨p,fun l hl => hp l ((dl l).mp hl)⟩)⟩
  rw [← agrees] at on
  have eq : X P (D P) = fun i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p ∈ P, ¬ I p l) := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [X,decide_eq_true_eq]
    apply or_congr (Iff.rfl)
    constructor
    · rintro ⟨l,hl,e⟩
      exact ⟨l,e,(dl l).mp hl⟩
    · rintro ⟨l,e,hl⟩
      exact ⟨l,(dl l).mpr hl,e⟩
  rw [eq, off] at on
  contradiction
