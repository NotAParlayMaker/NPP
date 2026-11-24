import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1683_67
    (pos : let r (n a b : Nat) (i : Fin 26) := n.testBit ((a*(i.val%13)+b)%13+13*(i.val/13)); let I (p l : Fin 13) := ∃ z∈([0,1,3,9] : List (Fin 13)),p=l+z; ∀ p l : Fin 13, I p l → ∃ n∈([8193,8194]:List Nat), ∃ a∈([1,3,9]:List Nat), ∃ b : Fin 13, (fun i : Fin 26 => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l))=r n a b.val)
    (neg : let r (n a b : Nat) (i : Fin 26) := n.testBit ((a*(i.val%13)+b)%13+13*(i.val/13)); let I (p l : Fin 13) := ∃ z∈([0,1,3,9] : List (Fin 13)),p=l+z; ∀ P : Finset (Fin 13),
  (∀ v : Fin 13, v∉P → ∃ w : Fin 13, (∀ p∈P, ¬I p w) ∧ I v w) →
  ((∃ c, ∀ p∈P, I p c) ∨ (∃ c, ∀ l, (∀ p∈P,¬I p l) → I c l)) →
  ∃ n∈([67100672,25018369,7962627,24444933,6815755,2179233,6291663,20971869,16779133,8191]:List Nat), ∃ a∈([1,3,9]:List Nat), ∃ b : Fin 13,
  (fun i : Fin 26 => decide ((∃ p∈P,i=Fin.castAdd 13 p) ∨ (∃ l : Fin 13, i=Fin.natAdd 13 l ∧ ∀ p∈P,¬I p l)))=r n a b.val)
    (synth : let r (n a b : Nat) (i : Fin 26) := n.testBit ((a*(i.val%13)+b)%13+13*(i.val/13)); ∃ C : Circuit, Monotone2 C ∧ C.size≤63 ∧ (∀ n∈([8193,8194]:List Nat), ∀ a∈([1,3,9]:List Nat), ∀ b : Fin 13, circuitFun 26 C (r n a b.val)=true) ∧
   (∀ n∈([67100672,25018369,7962627,24444933,6815755,2179233,6291663,20971869,16779133,8191]:List Nat), ∀ a∈([1,3,9]:List Nat), ∀ b : Fin 13, circuitFun 26 C (r n a b.val)=false)) : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  have eqv : ∀ p l : Fin 13, (∃ d∈({0,1,3,9}:Finset (Fin 13)),p=l+d) ↔
      (∃ d∈([0,1,3,9]:List (Fin 13)),p=l+d) := by decide +kernel
  obtain ⟨C,hm,sz,yes,no⟩ := synth
  refine ⟨C,hm,sz,?_,?_⟩
  · intro p l hit
    obtain ⟨n,hn,a,ha,b,eq⟩ := pos p l ((eqv p l).mp hit)
    rw [eq]; exact yes n hn a ha b
  · intro P cl de
    simp only [eqv] at cl de ⊢
    obtain ⟨n,hn,a,ha,b,eq⟩ := neg P cl de
    rw [eq]; exact no n hn a ha b
