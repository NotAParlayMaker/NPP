import Mathlib.Tactic.ByContra
import PEqualNP.Defs

-- The binary lower bound and the signed compiler in L_meta_2681 already give
-- the first child: its final argument works verbatim with twelve as the bound.
-- At thirteen gates one extra source may be inverted, after it is available.
-- At fourteen gates only input zero has both polarities. With it fixed, the
-- circuit is monotone. The rows are the minimal true and maximal false inputs
-- of the two cofactors, with the sixteen positive rows first.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2683_29
    (small : ∀ (n : ℕ) (op : Fin n → Bool) (a b : Fin n → ℕ × Bool)
      (out : ℕ × Bool) (w : (Fin 9 → Bool) → ℕ → Bool), n ≤ 12 →
      (∀ j, (a j).1 < 10 + j.val ∧ (b j).1 < 10 + j.val) → out.1 < 10 + n →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let v := fun p : ℕ × Bool => w x p.1 ^^ p.2
        w x (10 + j.val) = if op j then v (a j) && v (b j) else v (a j) || v (b j)) →
      ∃ x, (w x out.1 ^^ out.2) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (one : let pack := fun f : Fin 512 → Bool => (BitVec.ofBoolListLE (List.ofFn f)).setWidth 512
      let v := fun i : Fin 9 => pack fun r => r.val.testBit i.val
      let base := 0 :: ~~~(0 : BitVec 512) :: ~~~(v 0) :: List.ofFn v
      let goal := pack fun r => ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any
        fun e => (r.val &&& e) == e
      ∀ (q : BitVec 512) (g : Fin 13 → BitVec 512),
        let pool := fun k => base ++ (List.ofFn g).take k
        let ok := fun k u => u ∈ pool k ∨ u = ~~~q ∧ q ∈ pool k
        (∀ j, ∃ a b, ok j.val a ∧ ok j.val b ∧ (g j = a &&& b ∨ g j = a ||| b)) →
          ¬ ok 13 goal)
    (mono : let base : List (BitVec 29) := [0,536870911,33489407,503381504,18022921,
        176694291,70599750,30017540,987296,107774216,359669808,427868608]
      ∀ g : Fin 14 → BitVec 29, let pool := fun k => base ++ (List.ofFn g).take k
        (∀ j, ∃ a ∈ pool j.val, ∃ b ∈ pool j.val, g j = a &&& b ∨ g j = a ||| b) →
          (65535 : BitVec 29) ∉ pool 14) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           (have x12 : ℕ × Bool → Prop := fun (x12 : ℕ × Bool) => x12.2 = Bool.true → x12.1 = (0 : ℕ) ∨ x12.1 = (9 : ℕ) ∨ x12.1 ∈ x6;             x12 x5 ∧ ∀ (x13 : Fin x1), x12 (x3 x13) ∧ x12 (x4 x13)) →             (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x7 x13 ↑x14 = x13 x14) →               (∀ (x14 : Fin (9 : ℕ) → Bool), x7 x14 (9 : ℕ) = Bool.false) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin x1),                     have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x7 x15 x17.1 ^^ x17.2;                     x7 x15 ((10 : ℕ) + ↑x16) = if x2 x16 = Bool.true then x17 (x3 x16) && x17 (x4 x16) else x17 (x3 x16) || x17 (x4 x16)) →                   ∃ (x16 : Fin (9 : ℕ) → Bool), (x7 x16 x5.1 ^^ x5.2) ≠ (x16 (0 : Fin (9 : ℕ)) && x16 (1 : Fin (9 : ℕ)) || x16 (1 : Fin (9 : ℕ)) && x16 (2 : Fin (9 : ℕ)) || x16 (2 : Fin (9 : ℕ)) && x16 (3 : Fin (9 : ℕ)) || x16 (3 : Fin (9 : ℕ)) && x16 (4 : Fin (9 : ℕ)) || x16 (4 : Fin (9 : ℕ)) && x16 (0 : Fin (9 : ℕ)) || x16 (0 : Fin (9 : ℕ)) && x16 (5 : Fin (9 : ℕ)) || x16 (1 : Fin (9 : ℕ)) && x16 (6 : Fin (9 : ℕ)) || x16 (2 : Fin (9 : ℕ)) && x16 (7 : Fin (9 : ℕ)) || x16 (3 : Fin (9 : ℕ)) && x16 (8 : Fin (9 : ℕ)) || x16 (5 : Fin (9 : ℕ)) && x16 (7 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ)) && x16 (8 : Fin (9 : ℕ)) || x16 (8 : Fin (9 : ℕ)) && x16 (5 : Fin (9 : ℕ))) := by
  intro n op a b out paid w _ budget reads outBound signs inputs zero gate
  by_cases short : n ≤ 12
  · exact small n op a b out w short reads outBound inputs zero gate
  by_contra! agrees
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let pack {d : ℕ} (f : Fin d → Bool) := (BitVec.ofBoolListLE (List.ofFn f)).setWidth d
  have bit {d : ℕ} (f : Fin d → Bool) (r : Fin d) : (pack f).getLsbD r.val = f r := by
    dsimp only [pack]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left r.isLt]
    simp [r.isLt]
  let word {d : ℕ} (x : Fin d → Fin 9 → Bool) (i : ℕ) := pack fun r => w (x r) i
  let gates {d : ℕ} (x : Fin d → Fin 9 → Bool) (j : Fin n) := word x (10 + j.val)
  let base {d : ℕ} (x : Fin d → Fin 9 → Bool) :=
    (0 : BitVec d) :: ~~~(0 : BitVec d) :: ~~~(pack fun r => x r 0) ::
      List.ofFn (fun i : Fin 9 => pack fun r => x r i)
  let pool {d : ℕ} (x : Fin d → Fin 9 → Bool) (k : ℕ) := base x ++ (List.ofFn (gates x)).take k
  let pin {d : ℕ} (x : Fin d → Fin 9 → Bool) (p : ℕ × Bool) :=
    if p.2 then ~~~(word x p.1) else word x p.1
  have bitPin {d : ℕ} (x : Fin d → Fin 9 → Bool) (p : ℕ × Bool) (r : Fin d) :
      (pin x p).getLsbD r.val = (w (x r) p.1 ^^ p.2) := by
    cases h : p.2 <;> simp only [pin, h, Bool.false_eq_true, ite_false, ite_true,
      BitVec.getLsbD_not, decide_eq_true r.isLt, Bool.true_and, word, bit,
      Bool.xor_false, Bool.xor_true]
  have wordIn {d : ℕ} (x : Fin d → Fin 9 → Bool) (i : Fin 9) :
      word x i.val = pack fun r => x r i := congrArg pack (funext fun r => inputs (x r) i)
  have wordZero {d : ℕ} (x : Fin d → Fin 9 → Bool) : word x 9 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    simpa [word, zero] using bit (fun j => w (x j) 9) ⟨r, hr⟩
  have wireMem {d : ℕ} (x : Fin d → Fin 9 → Bool) (k i : ℕ) (hk : k ≤ n) (hi : i < 10 + k) :
      word x i ∈ pool x k := by
    by_cases h : i < 9
    · apply List.mem_append_left
      rw [wordIn x ⟨i, h⟩]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_ofFn.mpr ⟨⟨i, h⟩, rfl⟩)))
    by_cases e : i = 9
    · subst i
      rw [wordZero]
      exact List.mem_append_left _ (List.mem_cons_self ..)
    · apply List.mem_append_right
      apply List.mem_take_iff_getElem.mpr
      refine ⟨i - 10, by simp; omega, ?_⟩
      simp only [List.getElem_ofFn, gates]
      rw [show 10 + (i - 10) = i by omega]
  have simulate {d : ℕ} (x : Fin d → Fin 9 → Bool) (ok : ℕ → BitVec d → Prop)
      (takeWire : ∀ k u, u ∈ pool x k → ok k u)
      (takeNeg : ∀ k i, k ≤ n → i < 10 + k → i ∈ paid → ok k (~~~(word x i))) :
      (∀ j, ∃ u v, ok j.val u ∧ ok j.val v ∧
        (gates x j = u &&& v ∨ gates x j = u ||| v)) ∧ ok n (pack fun r => F (x r)) := by
    have takePin (k : ℕ) (p : ℕ × Bool) (hk : k ≤ n) (hp : p.1 < 10 + k)
        (hs : p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid) : ok k (pin x p) := by
      cases pol : p.2
      · simpa only [pin, pol, Bool.false_eq_true, ite_false] using takeWire _ _ (wireMem x k p.1 hk hp)
      · simp only [pin, pol, ite_true]
        rcases hs pol with h | h | h
        · apply takeWire
          rw [h, show word x 0 = pack (fun r => x r 0) from wordIn x 0]
          exact List.mem_append_left _ (by simp [base])
        · apply takeWire
          rw [h, wordZero]
          exact List.mem_append_left _ (by simp [base])
        · exact takeNeg k p.1 hk hp h
    constructor
    · intro j
      refine ⟨pin x (a j), pin x (b j), takePin _ _ j.isLt.le (reads j).1 (signs.2 j).1,
        takePin _ _ j.isLt.le (reads j).2 (signs.2 j).2, ?_⟩
      cases h : op j
      · right
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        simpa only [gates, word, bit (fun t => w (x t) (10 + j.val)) ⟨r, hr⟩,
          BitVec.getLsbD_or, bitPin x (a j) ⟨r, hr⟩, bitPin x (b j) ⟨r, hr⟩, h,
          Bool.false_eq_true, ite_false] using gate (x ⟨r, hr⟩) j
      · left
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        simpa only [gates, word, bit (fun t => w (x t) (10 + j.val)) ⟨r, hr⟩,
          BitVec.getLsbD_and, bitPin x (a j) ⟨r, hr⟩, bitPin x (b j) ⟨r, hr⟩, h,
          ite_true] using gate (x ⟨r, hr⟩) j
    · have output : pin x out = pack fun r => F (x r) := by
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        rw [bitPin x out ⟨r, hr⟩, bit (fun t => F (x t)) ⟨r, hr⟩]
        exact agrees (x ⟨r, hr⟩)
      exact output ▸ takePin n out le_rfl outBound signs.1
  obtain h | h : n = 13 ∨ n = 14 := by omega
  · subst n
    let x := fun (r : Fin 512) (i : Fin 9) => r.val.testBit i.val
    obtain ⟨c, hc⟩ := Finset.card_le_one_iff_subset_singleton.mp (show paid.card ≤ 1 by omega)
    let q := word x c
    let ok := fun k (u : BitVec 512) => u ∈ pool x k ∨ u = ~~~q ∧ q ∈ pool x k
    obtain ⟨steps, found⟩ := simulate x ok (fun _ _ mem => Or.inl mem) (by
      intro k i hk hi mem
      have eq : i = c := Finset.mem_singleton.mp (hc mem)
      subst i
      exact Or.inr ⟨rfl, wireMem x k c hk hi⟩)
    have truth : ∀ r : Fin 512, F (x r) =
        ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun e => (r.val &&& e) == e) := by
      decide +kernel
    rw [funext truth] at found
    exact one q (gates x) steps found
  · subst n
    let rows : List ℕ := [6,12,24,66,132,160,264,288,320,3,13,17,33,133,265,321,
      42,50,104,116,138,200,208,276,402,69,201,261,385]
    let x := fun (r : Fin 29) (i : Fin 9) => (rows.getD r.val 0).testBit i.val
    have empty := Finset.card_eq_zero.mp (show paid.card = 0 by omega)
    obtain ⟨steps, found⟩ := simulate x (fun k u => u ∈ pool x k) (fun _ _ mem => mem) (by
      intro _ i _ _ mem
      simp [empty] at mem)
    have inputTable : base x = ([0,536870911,33489407,503381504,18022921,176694291,70599750,
        30017540,987296,107774216,359669808,427868608] : List (BitVec 29)) := by decide +kernel
    have targetTable : (pack fun r => F (x r)) = (65535 : BitVec 29) := by decide +kernel
    simp only [pool, inputTable, targetTable] at steps found
    apply mono (gates x) _ found
    intro j
    obtain ⟨u, v, hu, hv, huvo⟩ := steps j
    exact ⟨u, hu, v, hv, huvo⟩
