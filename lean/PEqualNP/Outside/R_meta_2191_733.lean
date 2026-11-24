import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2191_733
    (hCover : ∀ x : Fin 8 → Bool, ∃ k : BitVec 8, x = fun i => k.getLsbD i.val)
    (hRows :
        ∀ k : BitVec 8,
          let x : Fin 8 → Bool := fun i => k.getLsbD i.val
          let f := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
            x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
            x 5 && x 7 || x 7 && x 4
          f = (0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8 : BitVec 256).getLsbD k.toNat ∧
          (f || x 0 || x 3) = (0xfffffffffffffffaffffffffffffffeafffffffefffffffaffeeffeeffeaffea : BitVec 256).getLsbD k.toNat)
    (hBound :
      let F := fun (k : BitVec 8) => (0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8 : BitVec 256).getLsbD k.toNat
      let G := fun (k : BitVec 8) => (0xfffffffffffffffaffffffffffffffeafffffffefffffffaffeeffeeffeaffea : BitVec 256).getLsbD k.toNat
      ∀ (C D : Circuit) (o : ℕ) (c : Bool), FanInTwo C → FanInTwo D →
        C.size + D.size ≤ 13 → o < 8 + C.size →
        let v := fun (k : BitVec 8) => C.wires (List.ofFn fun i : Fin 8 => k.getLsbD i.val)
        let s := fun (k : BitVec 8) => (v k).getD o false
        (∀ i : Fin 8, (∃ k : BitVec 8, s k ≠ k.getLsbD i.val) ∧
          ∃ k : BitVec 8, s k ≠ !k.getLsbD i.val) →
        (∀ k, F k ≠ G k → s k = !c) →
        (∀ k, D.eval (v k ++ [s k]) = F k) →
        ∃ k, D.eval (v k ++ [c]) ≠ G k) :
have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   PEqualNP.MetaComplexity.FanInTwo x3 →     PEqualNP.MetaComplexity.FanInTwo x4 →       x3.size + x4.size ≤ (13 : ℕ) →         x5 < (8 : ℕ) + x3.size →           have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x3.wires (List.ofFn x11);           have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x5 Bool.false;           (∀ (x13 : Fin (8 : ℕ)), (x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => x14 x13) ∧ x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => !x14 x13) → (∀ (x14 : Fin (8 : ℕ) → Bool), x1 x14 ≠ x2 x14 → x12 x14 = !x6) → (∀ (x15 : Fin (8 : ℕ) → Bool), x4.eval (x11 x15 ++ [x12 x15]) = x1 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x4.eval (x11 x16 ++ [x6]) ≠ x2 x16
:= by
  classical
  intro f g C D o c hC hD hSize hWire v s hLiteral hSwitch hRun
  have literal (i : Fin 8) :
      (∃ k : BitVec 8, s (fun j => k.getLsbD j.val) ≠ k.getLsbD i.val) ∧
      (∃ k : BitVec 8, s (fun j => k.getLsbD j.val) ≠ !k.getLsbD i.val) := by
    constructor
    · by_contra! h
      apply (hLiteral i).1
      funext x
      obtain ⟨k, hx⟩ := hCover x
      rw [hx]
      exact h k
    · by_contra! h
      apply (hLiteral i).2
      funext x
      obtain ⟨k, hx⟩ := hCover x
      rw [hx]
      exact h k
  have changeWire (k : BitVec 8)
      (hk : (0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8 : BitVec 256).getLsbD k.toNat ≠
        (0xfffffffffffffffaffffffffffffffeafffffffefffffffaffeeffeeffeaffea : BitVec 256).getLsbD k.toNat) :
      s (fun i => k.getLsbD i.val) = !c := by
    apply hSwitch
    have h₁ : f (fun i => k.getLsbD i.val) = (0xfffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8 : BitVec 256).getLsbD k.toNat :=
      (hRows k).1
    have h₂ : g (fun i => k.getLsbD i.val) = (0xfffffffffffffffaffffffffffffffeafffffffefffffffaffeeffeeffeaffea : BitVec 256).getLsbD k.toNat :=
      (hRows k).2
    rwa [h₁, h₂]
  obtain ⟨k, hk⟩ := hBound C D o c hC hD hSize hWire literal changeWire
    (fun k => (hRun (fun i => k.getLsbD i.val)).trans (hRows k).1)
  exact ⟨fun i => k.getLsbD i.val, fun he => hk (he.trans (hRows k).2)⟩
