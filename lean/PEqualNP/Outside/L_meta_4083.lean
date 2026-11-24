import Mathlib
import PEqualNP.Defs

/-!
A cut of the wires of a circuit for the edge function of the Petersen graph carries at least as
many value patterns as the function has distinct rows across the matching cut of the inputs.

The wires in `A` are closed under reading, so they depend only on the inputs in `S`. Every other
wire is a function of the inputs outside `S` and of the wires of `B`. So the pattern on `B`
decides the row of the function, and the number of rows is counted for each of the 1024 sets `S`
by a kernel computation on bit masks.
-/

namespace PEqualNP.Outside.L_meta_4083

open PEqualNP.CircuitLowerBounds

/-- One evaluation step of a circuit. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (w : ℕ) :
    (W ++ [v]).getD w false = if w = W.length then v else W.getD w false := by
  rcases Nat.lt_trichotomy w W.length with h | h | h
  · rw [if_neg (Nat.ne_of_lt h), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h]
  · subst h
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
    simp
  · rw [if_neg (Nat.ne_of_gt h), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem getD_big (W : List Bool) (w : ℕ) (h : W.length ≤ w) : W.getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem step_length (W : List Bool) (g : Gate) : (step W g).length = W.length + 1 := by
  simp [step]

theorem foldl_prefix (gs : List Gate) : ∀ (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl step W).getD i false = W.getD i false := by
  induction gs with
  | nil =>
    intro W i _
    rfl
  | cons g gs ih =>
    intro W i hi
    rw [List.foldl_cons, ih (step W g) i (by rw [step_length]; omega)]
    show (W ++ [_]).getD i false = _
    rw [getD_snoc, if_neg (Nat.ne_of_lt hi)]

/-- Wires in a set closed under reading agree as soon as the base wires in it agree. -/
theorem closed_agree (A : ℕ → Prop) (gs : List Gate) : ∀ (W W' : List Bool),
    W.length = W'.length →
    (∀ w, A w → W.getD w false = W'.getD w false) →
    (∀ t (h : t < gs.length), A (W.length + t) → ∀ i ∈ gs[t].inputs, A i) →
    ∀ w, A w → (gs.foldl step W).getD w false = (gs.foldl step W').getD w false := by
  induction gs with
  | nil =>
    intro W W' _ hb _ w hw
    exact hb w hw
  | cons g gs ih =>
    intro W W' hl hb hg
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · rw [step_length, step_length, hl]
    · intro w hw
      show (W ++ [_]).getD w false = (W' ++ [_]).getD w false
      rw [getD_snoc, getD_snoc, ← hl]
      by_cases h2 : w = W.length
      · rw [if_pos h2, if_pos h2]
        have hv : (g.inputs.map fun i => W.getD i false) =
            (g.inputs.map fun i => W'.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact hb i (hg 0 (by simp) (by simpa [h2] using hw) i (by simpa using hi))
        rw [hv]
      · rw [if_neg h2, if_neg h2]
        exact hb w hw
    · intro t ht hA i hi
      have ht' : t + 1 < (g :: gs).length := by simpa using ht
      have hA' : A (W.length + (t + 1)) := by
        have e : W.length + (t + 1) = (step W g).length + t := by rw [step_length]; omega
        rw [e]
        exact hA
      exact hg (t + 1) ht' hA' i (by simpa using hi)

/-- Wires outside `A` agree as soon as the base wires outside `A` agree and the final wires
that lie in `A` and in `B` agree, when gates outside `A` read `A` only through `B`. -/
theorem outside_agree (A B : ℕ → Prop) (gs : List Gate) : ∀ (W W' : List Bool),
    W.length = W'.length →
    (∀ w, ¬ A w → W.getD w false = W'.getD w false) →
    (∀ w, A w → B w → (gs.foldl step W).getD w false = (gs.foldl step W').getD w false) →
    (∀ t (h : t < gs.length), ¬ A (W.length + t) → ∀ i ∈ gs[t].inputs, A i → B i) →
    ∀ w, ¬ A w → (gs.foldl step W).getD w false = (gs.foldl step W').getD w false := by
  induction gs with
  | nil =>
    intro W W' _ hb _ _ w hw
    exact hb w hw
  | cons g gs ih =>
    intro W W' hl hb hfin hg
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · rw [step_length, step_length, hl]
    · intro w hw
      show (W ++ [_]).getD w false = (W' ++ [_]).getD w false
      rw [getD_snoc, getD_snoc, ← hl]
      by_cases h2 : w = W.length
      · rw [if_pos h2, if_pos h2]
        have hv : (g.inputs.map fun i => W.getD i false) =
            (g.inputs.map fun i => W'.getD i false) := by
          apply List.map_congr_left
          intro i hi
          by_cases hAi : A i
          · have hBi : B i := hg 0 (by simp) (by simpa [h2] using hw) i (by simpa using hi) hAi
            by_cases hlt : i < W.length
            · rw [← foldl_prefix (g :: gs) W i hlt, ← foldl_prefix (g :: gs) W' i (hl ▸ hlt)]
              exact hfin i hAi hBi
            · rw [getD_big W i (by omega), getD_big W' i (by omega)]
          · exact hb i hAi
        rw [hv]
      · rw [if_neg h2, if_neg h2]
        exact hb w hw
    · exact hfin
    · intro t ht hA i hi
      have ht' : t + 1 < (g :: gs).length := by simpa using ht
      have hA' : ¬ A (W.length + (t + 1)) := by
        have e : W.length + (t + 1) = (step W g).length + t := by rw [step_length]; omega
        rw [e]
        exact hA
      exact hg (t + 1) ht' hA' i (by simpa using hi)

/-- The input list of the statement: the ten inputs and the negation of the first. -/
def inp (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]

theorem inp_length (x : Fin 10 → Bool) : (inp x).length = 11 := by simp [inp]

theorem inp_get (x : Fin 10 → Bool) (i : Fin 10) : (inp x).getD i false = x i := by
  show (List.ofFn x ++ [!x 0]).getD i false = x i
  rw [getD_snoc, if_neg (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos i.2]
  rfl

theorem inp_get10 (x : Fin 10 → Bool) : (inp x).getD 10 false = !x 0 := by
  show (List.ofFn x ++ [!x 0]).getD 10 false = !x 0
  rw [getD_snoc, if_pos (by simp)]

/-- The edge function of the statement. -/
def F (x : Fin 10 → Bool) : Bool :=
  decide (∃ (i : Fin 10) (j : Fin 10), x i = true ∧ x j = true ∧
    (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD ↑i 0).testBit ↑j = true)

/-- The input that follows `x` on `S` and `y` elsewhere. -/
def mix (S : Finset (Fin 10)) (x y : Fin 10 → Bool) : Fin 10 → Bool :=
  fun i => if i ∈ S then x i else y i

theorem card_image_le_of_factor {X P R : Type} [Fintype X] [DecidableEq P] [DecidableEq R]
    (p : X → P) (r : X → R) (h : ∀ x x', p x = p x' → r x = r x') :
    (Finset.univ.image r).card ≤ (Finset.univ.image p).card := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x0⟩⟩
  · simp
  · apply Finset.card_le_card_of_injOn
      (fun ρ => if hρ : ∃ x, r x = ρ then p hρ.choose else p x0)
    · intro ρ _
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      by_cases hρ : ∃ x, r x = ρ
      · exact ⟨hρ.choose, by rw [dif_pos hρ]⟩
      · exact ⟨x0, by rw [dif_neg hρ]⟩
    · intro ρ hρ ρ' hρ' he
      have h1 : ∃ x, r x = ρ := by simpa using hρ
      have h2 : ∃ x, r x = ρ' := by simpa using hρ'
      simp only [dif_pos h1, dif_pos h2] at he
      rw [← h1.choose_spec, ← h2.choose_spec]
      exact h _ _ he

/-- The pattern on the wires of `B` decides the row. -/
theorem rows_le (C : Circuit) (hC : ∀ x : Fin 10 → Bool, C.eval (inp x) = F x)
    (S : Finset (Fin 10)) (A B : Finset ℕ)
    (h1 : ∀ i : Fin 10, (i : ℕ) ∈ A ↔ i ∈ S) (h2 : 10 ∈ A ↔ (0 : Fin 10) ∈ S)
    (h3 : ∀ t : Fin C.size, ∀ i ∈ (C.gates.get t).inputs,
      (11 + (t : ℕ) ∈ A → i ∈ A) ∧ (11 + (t : ℕ) ∉ A → i ∈ A → i ∈ B))
    (h4 : C.output ∈ A → C.output ∈ B) :
    (Finset.univ.image (fun (x : Fin 10 → Bool) (y : Fin 10 → Bool) => F (mix S x y))).card ≤
      (Finset.univ.image (fun (x : Fin 10 → Bool) (w : ↥B) =>
        (C.wires (inp x)).getD (↑w) false)).card := by
  -- the wires of A only see the inputs of S
  have fact1 : ∀ (x y : Fin 10 → Bool) (w : ℕ), w ∈ A →
      (C.wires (inp x)).getD w false = (C.wires (inp (mix S x y))).getD w false := by
    intro x y
    rw [wires_eq, wires_eq]
    apply closed_agree (fun w => w ∈ A) C.gates (inp x) (inp (mix S x y))
    · rw [inp_length, inp_length]
    · intro w hw
      by_cases h10 : w < 10
      · have e1 := inp_get x ⟨w, h10⟩
        have e2 := inp_get (mix S x y) ⟨w, h10⟩
        have hS : (⟨w, h10⟩ : Fin 10) ∈ S := (h1 ⟨w, h10⟩).1 hw
        simp only [mix, if_pos hS] at e2
        exact e1.trans e2.symm
      · by_cases h11 : w = 10
        · subst h11
          rw [inp_get10, inp_get10]
          have hS : (0 : Fin 10) ∈ S := h2.1 hw
          simp only [mix, if_pos hS]
        · rw [getD_big _ w (by rw [inp_length]; omega), getD_big _ w (by rw [inp_length]; omega)]
    · intro t ht hA i hi
      rw [inp_length] at hA
      exact (h3 ⟨t, ht⟩ i hi).1 hA
  apply card_image_le_of_factor
  intro x x' hp
  have hB : ∀ w ∈ B, (C.wires (inp x)).getD w false = (C.wires (inp x')).getD w false := by
    intro w hw
    exact congrFun hp ⟨w, hw⟩
  funext y
  have hfin : ∀ w, w ∈ A → w ∈ B → (C.gates.foldl step (inp (mix S x y))).getD w false =
      (C.gates.foldl step (inp (mix S x' y))).getD w false := by
    intro w hA hBw
    rw [← wires_eq, ← wires_eq, ← fact1 x y w hA, ← fact1 x' y w hA]
    exact hB w hBw
  have hout := outside_agree (fun w => w ∈ A) (fun w => w ∈ B) C.gates
    (inp (mix S x y)) (inp (mix S x' y)) (by rw [inp_length, inp_length])
    (by
      intro w hw
      by_cases h10 : w < 10
      · have e1 := inp_get (mix S x y) ⟨w, h10⟩
        have e2 := inp_get (mix S x' y) ⟨w, h10⟩
        have hS : (⟨w, h10⟩ : Fin 10) ∉ S := fun h => hw ((h1 ⟨w, h10⟩).2 h)
        simp only [mix, if_neg hS] at e1 e2
        exact e1.trans e2.symm
      · by_cases h11 : w = 10
        · subst h11
          rw [inp_get10, inp_get10]
          have hS : (0 : Fin 10) ∉ S := fun h => hw (h2.2 h)
          simp only [mix, if_neg hS]
        · rw [getD_big _ w (by rw [inp_length]; omega), getD_big _ w (by rw [inp_length]; omega)])
    hfin
    (by
      intro t ht hA i hi
      rw [inp_length] at hA
      exact (h3 ⟨t, ht⟩ i hi).2 hA)
  show F (mix S x y) = F (mix S x' y)
  rw [← hC, ← hC]
  show (C.wires (inp (mix S x y))).getD C.output false =
    (C.wires (inp (mix S x' y))).getD C.output false
  rw [wires_eq, wires_eq]
  by_cases ho : C.output ∈ A
  · exact hfin C.output ho (h4 ho)
  · exact hout C.output ho

/-- The input whose true coordinates are the bits of `m`. -/
def toFun (m : ℕ) : Fin 10 → Bool := fun i => m.testBit i

/-- The edge function on a bit mask, by lists. -/
def eb (m : ℕ) : Bool :=
  (List.finRange 10).any fun i => (List.finRange 10).any fun j =>
    m.testBit i && (m.testBit j &&
      (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD ↑i 0).testBit ↑j)

theorem F_toFun (m : ℕ) : F (toFun m) = eb m := by
  rw [Bool.eq_iff_iff]
  simp [F, eb, toFun, List.any_eq_true]

/-- The truth table of the edge function: bit `m` is its value on the mask `m`. -/
def ET : ℕ := 179769313486231590772930519078902473361797697894230657273430081157732675805415574637631938330974342149254676239332264626717371455201768760401339708730060862467599309626786222646154322922921861021930833718980811068645458870467698626365512840652500019744054405992546613330590959325515380975353348937279334971592

theorem ET_ok : (List.range 1024).all (fun m => eb m == ET.testBit m) = true := by
  decide +kernel

theorem F_table (m : ℕ) (h : m < 1024) : F (toFun m) = ET.testBit m := by
  rw [F_toFun]
  have := List.all_eq_true.1 ET_ok m (List.mem_range.2 h)
  simpa using this

/-- The mask that follows `a` on `s` and `y` elsewhere. -/
def mixm (s a y : ℕ) : ℕ := (a &&& s) ||| (y &&& (1023 ^^^ s))

theorem bit1023 : ∀ i : Fin 10, (1023 : ℕ).testBit i = true := by decide

theorem mix_toFun (S : Finset (Fin 10)) (s : ℕ)
    (hs : ∀ i : Fin 10, s.testBit i = true ↔ i ∈ S) (a y : ℕ) :
    mix S (toFun a) (toFun y) = toFun (mixm s a y) := by
  funext i
  have h := hs i
  have h9 := bit1023 i
  by_cases hi : i ∈ S
  · have hb : s.testBit i = true := h.2 hi
    simp [mix, toFun, mixm, hi, hb, h9, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  · have hb : s.testBit i = false := by
      cases hc : s.testBit i
      · rfl
      · exact absurd (h.1 hc) hi
    simp [mix, toFun, mixm, hi, hb, h9, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]

theorem mixm_lt (s a y : ℕ) (hs : s < 1024) : mixm s a y < 1024 := by
  have hs' : s < 2 ^ 10 := hs
  have h1 : a &&& s < 2 ^ 10 := Nat.and_lt_two_pow a hs'
  have h2 : y &&& (1023 ^^^ s) < 2 ^ 10 :=
    Nat.and_lt_two_pow y (Nat.xor_lt_two_pow (by norm_num) hs')
  exact Nat.or_lt_two_pow h1 h2

/-- The values of a row on the test inputs (nothing, and each single vertex), packed in a
number. -/
def sgnOf (t : ℕ → Bool) : ℕ :=
  (t 0).toNat + 2 * (t 1).toNat + 4 * (t 2).toNat + 8 * (t 4).toNat + 16 * (t 8).toNat +
    32 * (t 16).toNat + 64 * (t 32).toNat + 128 * (t 64).toNat + 256 * (t 128).toNat +
    512 * (t 256).toNat + 1024 * (t 512).toNat

def sgn (s a : ℕ) : ℕ := sgnOf fun y => ET.testBit (mixm s a y)

/-- The count after seeing the row `v`: one more when its bit is not yet in `seen`. -/
def bump (seen c v : ℕ) : ℕ := if seen.testBit v = true then c else c + 1

/-- Scan the masks inside `s`, from `a` down to zero, keeping the rows seen as the bits of one
number and their count beside it, so the kernel computes with numbers only. -/
def scan (s : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, c => c
  | fuel + 1, a, seen, c =>
    if a = 0 then bump seen c (sgn s 0)
    else scan s fuel ((a - 1) &&& s) (seen ||| 2 ^ sgn s a) (bump seen c (sgn s a))

/-- A lower count of the distinct rows of the cut `s`. -/
def cnt (s : ℕ) : ℕ := scan s 1025 s 0 0

def pc (s : ℕ) : ℕ := ((List.finRange 10).filter fun i : Fin 10 => s.testBit (i : ℕ)).length

def table : List ℕ := [1, 2, 4, 6, 9, 12, 9, 9, 5, 3, 2]

theorem check : (List.range 1024).all (fun s => decide (table.getD (pc s) 0 ≤ cnt s)) = true := by
  decide +kernel

theorem bump_spec (seen c v : ℕ) (T : Finset ℕ) (h1 : ∀ w, seen.testBit w = true ↔ w ∈ T)
    (h2 : c = T.card) : bump seen c v = (insert v T).card := by
  by_cases hv : seen.testBit v = true
  · have e : bump seen c v = c := if_pos hv
    rw [e, Finset.insert_eq_of_mem ((h1 v).1 hv), h2]
  · have e : bump seen c v = c + 1 := if_neg hv
    rw [e, Finset.card_insert_of_notMem (fun h => hv ((h1 v).2 h)), h2]

theorem scan_spec (s : ℕ) : ∀ (fuel a seen c : ℕ) (T : Finset ℕ),
    (∀ w, seen.testBit w = true ↔ w ∈ T) → c = T.card → (∀ v ∈ T, ∃ b, sgn s b = v) →
    ∃ T' : Finset ℕ, scan s fuel a seen c = T'.card ∧ ∀ v ∈ T', ∃ b, sgn s b = v := by
  intro fuel
  induction fuel with
  | zero =>
    intro a seen c T _ h2 h3
    exact ⟨T, h2, h3⟩
  | succ fuel ih =>
    intro a seen c T h1 h2 h3
    have hins : ∀ b : ℕ, ∀ v ∈ insert (sgn s b) T, ∃ b', sgn s b' = v := by
      intro b v hv
      rcases Finset.mem_insert.1 hv with hv | hv
      · exact ⟨b, hv.symm⟩
      · exact h3 v hv
    by_cases ha : a = 0
    · have e : scan s (fuel + 1) a seen c = bump seen c (sgn s 0) := if_pos ha
      exact ⟨insert (sgn s 0) T, by rw [e, bump_spec seen c _ T h1 h2], hins 0⟩
    · have e : scan s (fuel + 1) a seen c =
          scan s fuel ((a - 1) &&& s) (seen ||| 2 ^ sgn s a) (bump seen c (sgn s a)) := if_neg ha
      rw [e]
      apply ih _ _ _ (insert (sgn s a) T)
      · intro w
        rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, Finset.mem_insert, h1 w]
        constructor
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl (by simpa using h : sgn s a = w).symm
        · rintro (h | h)
          · exact Or.inr (by simp [h])
          · exact Or.inl h
      · exact bump_spec seen c _ T h1 h2
      · exact hins a

/-- Every cut of the inputs has at least the tabled number of rows. -/
theorem rows_ge (S : Finset (Fin 10)) :
    table.getD S.card 0 ≤
      (Finset.univ.image (fun (x : Fin 10 → Bool) (y : Fin 10 → Bool) => F (mix S x y))).card := by
  obtain ⟨s, hs, hlt⟩ : ∃ s : ℕ, (∀ i : Fin 10, s.testBit i = true ↔ i ∈ S) ∧ s < 1024 := by
    refine ⟨Nat.ofBits fun i : Fin 10 => decide (i ∈ S), ?_, Nat.ofBits_lt_two_pow _⟩
    intro i
    rw [Nat.testBit_ofBits_lt _ _ i.2]
    simp
  have hcard : S.card = pc s := by
    have e : S = ((List.finRange 10).filter fun i : Fin 10 => s.testBit (i : ℕ)).toFinset := by
      ext i
      simp [hs]
    have e2 := List.toFinset_card_of_nodup
      ((List.nodup_finRange 10).filter fun i : Fin 10 => s.testBit (i : ℕ))
    rw [← e] at e2
    exact e2
  have hchk := List.all_eq_true.1 check s (List.mem_range.2 hlt)
  have hchk' : table.getD (pc s) 0 ≤ cnt s := by simpa using hchk
  rw [hcard]
  refine le_trans hchk' ?_
  obtain ⟨T, hT, hex⟩ := scan_spec s 1025 s 0 0 ∅ (by simp) (by simp) (by simp)
  have key : ∀ a : ℕ, sgnOf (fun y => F (mix S (toFun a) (toFun y))) = sgn s a := by
    intro a
    show _ = sgnOf _
    congr 1
    funext y
    rw [mix_toFun S s hs, F_table _ (mixm_lt s a y hlt)]
  show scan s 1025 s 0 0 ≤ _
  rw [hT]
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_image_le (f := fun r : (Fin 10 → Bool) → Bool => sgnOf fun y => r (toFun y)))
  intro v hv
  obtain ⟨a, ha⟩ := hex v hv
  rw [Finset.mem_image]
  refine ⟨fun y => F (mix S (toFun a) y), Finset.mem_image.2 ⟨toFun a, Finset.mem_univ _, rfl⟩, ?_⟩
  rw [← ha, ← key a]

end PEqualNP.Outside.L_meta_4083

theorem PEqualNP.Outside.L_meta_4083 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (10 : ℕ))]) = (fun (x3 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x4 : Fin (10 : ℕ)) (x5 : Fin (10 : ℕ)), x3 x4 = Bool.true ∧ x3 x5 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x4 (0 : ℕ)).testBit ↑x5 = Bool.true)) x2) → ∀ (x3 : Finset (Fin (10 : ℕ))) (x4 x5 : Finset ℕ), (∀ (x6 : Fin (10 : ℕ)), ↑x6 ∈ x4 ↔ x6 ∈ x3) → ((10 : ℕ) ∈ x4 ↔ (0 : Fin (10 : ℕ)) ∈ x3) → (∀ (x8 : Fin x1.size), ∀ x9 ∈ (x1.gates.get x8).inputs, ((11 : ℕ) + ↑x8 ∈ x4 → x9 ∈ x4) ∧ ((11 : ℕ) + ↑x8 ∉ x4 → x9 ∈ x4 → x9 ∈ x5)) → (x1.output ∈ x4 → x1.output ∈ x5) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x3.card (0 : ℕ) ≤ (Finset.image (fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ↥x5) => (x1.wires (List.ofFn x10 ++ [!x10 (0 : Fin (10 : ℕ))])).getD (↑x11) Bool.false) Finset.univ).card := by
  intro C hC S A B h1 h2 h3 h4
  exact le_trans (PEqualNP.Outside.L_meta_4083.rows_ge S)
    (PEqualNP.Outside.L_meta_4083.rows_le C hC S A B h1 h2 h3 h4)
