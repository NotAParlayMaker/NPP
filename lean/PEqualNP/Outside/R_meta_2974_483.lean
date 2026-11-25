import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2974_483
  (rank : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit), 0<q → N=q^2+q+1 → (∀ l,Fintype.card {p // I p l}=q+1) → (∀ p r,p≠r → ∃! l,I p l ∧ I r l) → IsAO2 (N+N) C → (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q → (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) → let A : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧ circuitFun (N+N) C (fun i=>decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true
    let w := (C.gates.foldl (fun (d : List Nat) g => d ++ [(g.inputs.map (fun i => d.getD i 0)).sum+1]) (List.replicate (N+N) 0)).getD C.output 0
    A.card ≤ w)
  (sharing : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit), 0<q → IsAO2 (N+N) C → (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q → (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) → let A : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧ circuitFun (N+N) C (fun i=>decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true
    let w := (C.gates.foldl (fun (d : List Nat) g => d ++ [(g.inputs.map (fun i => d.getD i 0)).sum+1]) (List.replicate (N+N) 0)).getD C.output 0
    let v := (A.image Prod.fst).card+(A.image Prod.snd).card
    w ≤ 2^(C.size+1-v)*C.size)
  (finiteCase : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit), 0<q → N=q^2+q+1 → (∀ l,Fintype.card {p // I p l}=q+1) → (∀ p r,p≠r → ∃! l,I p l ∧ I r l) → IsAO2 (N+N) C → (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q → (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) → let A : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧ circuitFun (N+N) C (fun i=>decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true
    C.size ≤ 4526 → A.card ≤ 24*C.size)
  (highSharing : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit), 87≤q → N=q^2+q+1 → (∀ l,Fintype.card {p // I p l}=q+1) → (∀ p r,p≠r → ∃! l,I p l ∧ I r l) → IsAO2 (N+N) C → (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true}≤q → (¬∃ p l,I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) → let A : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧ circuitFun (N+N) C (fun i=>decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true
    let w := (C.gates.foldl (fun (d : List Nat) g => d ++ [(g.inputs.map (fun i => d.getD i 0)).sum+1]) (List.replicate (N+N) 0)).getD C.output 0
    let v := (A.image Prod.fst).card+(A.image Prod.snd).card
    let D := A.filter fun e => PEqualNP.ReadK.lineSingle C (N+N) (fun i=>decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧ PEqualNP.ReadK.lineSingle C (N+N) (fun i=>decide (i < N)) e.1.val (N+e.2.val)=false
    4526<C.size → 24*C.size<w → v+5≤C.size+1 → D.card ≤ 24*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  classical
  intro q N I inst C big ord degree join ao safe
  have hq : 0<q := by omega
  let A : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧ circuitFun (N+N) C (fun i=>decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true
  let w := (C.gates.foldl (fun (d : List Nat) g => d ++ [(g.inputs.map (fun i => d.getD i 0)).sum+1]) (List.replicate (N+N) 0)).getD C.output 0
  let v := (A.image Prod.fst).card+(A.image Prod.snd).card
  let D := A.filter fun e => PEqualNP.ReadK.lineSingle C (N+N) (fun i=>decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧ PEqualNP.ReadK.lineSingle C (N+N) (fun i=>decide (i < N)) e.1.val (N+e.2.val)=false
  have subset : D.card ≤ A.card := Finset.card_le_card (Finset.filter_subset ..)
  have hr : A.card≤w := rank q N I C hq ord degree join ao safe
  have hs : w≤2^(C.size+1-v)*C.size := sharing q N I C hq ao safe
  have total : D.card≤24*C.size := by
    by_cases sz : C.size≤4526
    · exact subset.trans (finiteCase q N I C hq ord degree join ao safe sz)
    by_cases hi : w≤24*C.size
    · exact subset.trans (hr.trans hi)
    have slack : v+5≤C.size+1 := by
      by_contra! no
      have exp : C.size+1-v≤4 := by omega
      have power := Nat.pow_le_pow_right (by decide : 0<2) exp
      exact hi (hs.trans (Nat.mul_le_mul_right C.size (power.trans (by decide))))
    exact highSharing q N I C big ord degree join ao safe (by omega) (by omega) slack
  rw [Fintype.card_subtype]
  simpa only [D,A,Finset.filter_filter,and_assoc] using total
