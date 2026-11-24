import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- There are 52 true pairs and 234 false inputs indexed by four-point arcs.
-- The 18 masks represent the cyclic orbits of the arcs; bit p marks point p.
-- On these rows OR gates may be absorbed into arbitrary unions of old signals.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_1898_317
    (compile : ∀ (n r : ℕ) (rows : Fin r → Fin n → Bool) (C : Circuit)
    , Monotone2 C →
    let src : List (Fin r → Bool) := ⊤ :: List.ofFn (fun u : Fin n => fun i => rows i u)
    let O (p : List (Fin r → Bool)) (v : Fin r → Bool) :=
      ∃ S : Finset (Fin r → Bool), (∀ a ∈ S, a ∈ p) ∧ v = S.sup id
    ∃ fs : List (Fin r → Bool),
      fs.length ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.and}.ncard ∧
      O (src ++ fs) (fun i => C.eval (List.ofFn (rows i))) ∧
      ∀ j : Fin fs.length, let prev := src ++ fs.take j.val
        ∃ a b : Fin r → Bool, O prev a ∧ O prev b ∧ fs.get j = a ⊓ b)
    (geometry :
      let M : List ℕ := [29,39,71,77,83,85,101,105,135,141,195,201,275,281,297,329,337,549]
      let A (i : Fin 286) := (List.finRange 13).toFinset.filter fun p =>
        (M.getD (i.val/13-4) 0).testBit ((p.val + 13 - i.val % 13) % 13)
      let E (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      ∀ i : Fin 286, 4 ≤ i.val/13 → let S := A i
            let Z (l : Fin 13) := ∀ p ∈ S, ¬E p l
            (∀ p ∉ S, ∃ l, Z l ∧ E p l) ∧ (¬ ∃ l, ∀ p ∈ S, E p l) ∧ ¬ ∃ p, ∀ l, Z l → E p l)
    (finite :
      let M : List ℕ := [29,39,71,77,83,85,101,105,135,141,195,201,275,281,297,329,337,549]
      let A (i : Fin 286) := (List.finRange 13).toFinset.filter fun p =>
        (M.getD (i.val/13-4) 0).testBit ((p.val + 13 - i.val % 13) % 13)
      let E (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      let q (i : Fin 286) : Fin 13 := Fin.ofNat 13 i.val
      let rows (i : Fin 286) (k : Fin 26) :=
        if i.val/13 < 4 then decide (k = Fin.castAdd 13 (q i + ([0,1,3,9] : List (Fin 13)).getD (i.val/13) 0) ∨ k = Fin.natAdd 13 (q i))
        else decide ((∃ p ∈ A i, k = Fin.castAdd 13 p) ∨
          ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ p ∈ A i, ¬ E p l)
      let src : List (Fin 286 → Bool) := ⊤ :: List.ofFn (fun u : Fin 26 => fun i => rows i u)
      let O (p : List (Fin 286 → Bool)) (v : Fin 286 → Bool) := ∃ S : Finset (Fin 286 → Bool), (∀ a ∈ S, a ∈ p) ∧ v = S.sup id
      ∀ fs : List (Fin 286 → Bool), O (src ++ fs) (fun i => decide (i.val/13 < 4)) →
        (∀ j : Fin fs.length, let prev := src ++ fs.take j.val
          ∃ a b : Fin 286 → Bool, O prev a ∧ O prev b ∧ fs.get j = a ⊓ b) → 13 ≤ fs.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C hm hp hn
  let M : List ℕ := [29,39,71,77,83,85,101,105,135,141,195,201,275,281,297,329,337,549]
  let A (i : Fin 286) := (List.finRange 13).toFinset.filter fun p =>
    (M.getD (i.val/13-4) 0).testBit ((p.val + 13 - i.val % 13) % 13)
  let E (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  let q (i : Fin 286) : Fin 13 := Fin.ofNat 13 i.val
  let r (i : Fin 286) := q i + ([0,1,3,9] : List (Fin 13)).getD (i.val/13) 0
  let rows (i : Fin 286) (k : Fin 26) :=
    if i.val/13 < 4 then decide (k = Fin.castAdd 13 (r i) ∨ k = Fin.natAdd 13 (q i))
    else decide ((∃ p ∈ A i, k = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ p ∈ A i, ¬ E p l)
  have good (i : Fin 286) : C.eval (List.ofFn (rows i)) = decide (i.val/13 < 4) := by
    by_cases hi : i.val/13 < 4
    · have incident : E (r i) (q i) := by
        have h : i.val/13=0 ∨ i.val/13=1 ∨ i.val/13=2 ∨ i.val/13=3 := by omega
        rcases h with h|h|h|h <;> simp [E,r,h]
      have hit := hp (r i) (q i) incident
      change C.eval (List.ofFn (fun k : Fin 26 =>
        decide (k = Fin.castAdd 13 (r i) ∨ k = Fin.natAdd 13 (q i)))) = true at hit
      simpa only [rows,if_pos hi,decide_eq_true hi] using hit
    · obtain ⟨hmx,hpencil,hdual⟩ := geometry i (by omega)
      have reject := hn (A i) hmx ⟨hpencil,hdual⟩
      let nx : Fin 26 → Bool := fun k => decide ((∃ p ∈ A i, k = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ p ∈ A i, ¬ E p l)
      have hx : rows i = nx := by funext k; exact if_neg hi
      rw [hx,decide_eq_false hi]
      refine Eq.trans ?_ reject
      apply congrArg (fun v : Fin 26 → Bool => C.eval (List.ofFn v))
      funext k
      apply Bool.eq_iff_iff.mpr
      simp only [nx,E,decide_eq_true_eq]
  obtain ⟨fs,hsize,hout,hlegal⟩ := compile 26 286 rows C hm
  rw [show (fun i => C.eval (List.ofFn (rows i))) = (fun i : Fin 286 => decide (i.val/13<4)) from funext good] at hout
  exact (finite fs hout hlegal).trans hsize
