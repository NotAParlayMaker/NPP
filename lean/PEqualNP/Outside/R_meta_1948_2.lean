import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

-- An AND-depth rank bounds the number of inputs needed to certify truth.
-- Rank two at the output allows every needed test to use at most four inputs.
theorem PEqualNP.Outside.R_meta_1948_2 :
    (∃ (N : ℕ) (I : Fin N → Fin N → Prop), N = 257 ^ 2 + 257 + 1 ∧
      (∀ l : Fin N, Nat.card {p : Fin N // I p l} = 258) ∧
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)) →
    (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], N = 257 ^ 2 + 257 + 1 →
      (∀ l : Fin N, Nat.card {p : Fin N // I p l} = 258) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      ∃ (C : Circuit) (d : ℕ → ℕ), IsAO2 (N + N) C ∧ PEqualNP.ReadK.IsReadK (N + N) C 2 ∧
        100 * C.size < N * 257 ∧ d C.output ≤ 2 ∧
        (∀ j < C.gates.length, ∀ w ∈ (gateAt C j).inputs, d w ≤ d (N + N + j) ∧
          ((gateAt C j).op = GateOp.and → d w < d (N + N + j))) ∧
        (∀ S : Finset (Fin (N + N)), S.card ≤ 4 →
          circuitFun (N + N) C (fun w => decide (w ∈ S)) = decide
            (∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S))) →
    ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) := by
  classical
  rintro ⟨N, I, hN, hline, hpair⟩ construct lower
  obtain ⟨C, d, hAO, hread, hsmall, hd, hrank, htest⟩ := construct N I hN hline hpair
  let n := N + N
  let step (v : List Bool) (g : Gate) :=
    v ++ [g.op.eval (g.inputs.map fun w => v.getD w false)]
  let wires (gs : List Gate) (v : List Bool) := gs.foldl step v
  have wires_append (gs ts : List Gate) (v : List Bool) :
      wires (gs ++ ts) v = wires ts (wires gs v) := by
    simp [wires, List.foldl_append]
  have wires_prefix (gs : List Gate) (v : List Bool) :
      ∃ t : List Bool, wires gs v = v ++ t ∧ t.length = gs.length := by
    induction gs generalizing v with
    | nil => exact ⟨[], by simp [wires], rfl⟩
    | cons g gs ih =>
      obtain ⟨t, ht, hl⟩ := ih (step v g)
      refine ⟨g.op.eval (g.inputs.map fun w => v.getD w false) :: t, ?_, by simp [hl]⟩
      change wires gs (step v g) = _
      rw [ht]
      simp [step]
  have wires_length (gs : List Gate) (v : List Bool) :
      (wires gs v).length = v.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wires_prefix gs v
    rw [ht]
    simp [hl]
  have wires_earlier (gs : List Gate) (v : List Bool) (w : ℕ) (hw : w < v.length) :
      (wires gs v).getD w false = v.getD w false := by
    obtain ⟨t, ht, _⟩ := wires_prefix gs v
    rw [ht, List.getD_append _ _ _ _ hw]
  have list_split (gs : List Gate) (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
      ∃ pre post, gs = pre ++ g :: post ∧ pre.length = j := by
    induction gs generalizing j with
    | nil => simp at hg
    | cons head tail ih =>
      cases j with
      | zero =>
        simp at hg
        subst head
        exact ⟨[], tail, rfl, rfl⟩
      | succ j =>
        simp at hg
        obtain ⟨pre, post, he, hl⟩ := ih j hg
        exact ⟨head :: pre, post, congrArg (head :: ·) he, by simp [hl]⟩
  let V (w : ℕ) (x : Fin n → Bool) := (wires C.gates (List.ofFn x)).getD w false
  have gate_get (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    unfold gateAt
    exact List.getD_eq_getElem _ _ hj
  have input_wire (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
      V w x = x ⟨w, hw⟩ := by
    unfold V
    rw [wires_earlier _ _ _ (by simpa using hw)]
    simp [List.getD_eq_getElem?_getD, hw]
  have gate_wire (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
      V (n + j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map (fun w => V w x)) := by
    let g := gateAt C j
    have hg : C.gates[j]? = some g := by
      change C.gates[j]? = some (gateAt C j)
      rw [gate_get j hj]
      exact List.getElem?_eq_getElem hj
    obtain ⟨pre, post, hsplit, hlen⟩ := list_split _ j g hg
    let prev := wires pre (List.ofFn x)
    have hprev : prev.length = n + j := by simp [prev, wires_length, hlen]
    have hfull : wires C.gates (List.ofFn x) = wires post (step prev g) := by
      rw [hsplit, wires_append]
      rfl
    change V (n + j) x = g.op.eval (g.inputs.map (fun w => V w x))
    unfold V
    rw [hfull, wires_earlier _ _ _ (by simp [step, hprev])]
    have hlast : (step prev g).getD (n + j) false =
        g.op.eval (g.inputs.map (fun w => prev.getD w false)) := by
      rw [← hprev]
      simp [step]
    rw [hlast]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hlt : w < n + j := hAO.2.1 j hj w hw
    rw [wires_earlier post (step prev g) w (by simp [step, hprev]; omega)]
    exact (List.getD_append prev [_] false w (by simpa [hprev] using hlt)).symm
  have binary (j : ℕ) (hj : j < C.gates.length) :
      ∃ a b, (gateAt C j).inputs = [a, b] := by
    have hl : (gateAt C j).inputs.length = 2 := by
      rw [gate_get j hj]
      exact hAO.2.2 _ (List.getElem_mem hj)
    cases hi : (gateAt C j).inputs with
    | nil => simp [hi] at hl
    | cons a rest =>
      cases rest with
      | nil => simp [hi] at hl
      | cons b tail =>
        have he : tail = [] := by simpa [hi] using hl
        exact ⟨a, b, by simp [he]⟩
  have cert : ∀ w : ℕ, ∀ x : Fin n → Bool, V w x = true →
      ∃ S : Finset (Fin n), S.card ≤ 2 ^ d w ∧ (∀ i ∈ S, x i = true) ∧
        ∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) → V w y = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro x hx
      by_cases hw : w < n
      · refine ⟨{⟨w, hw⟩}, ?_, ?_, ?_⟩
        · simpa only [Finset.card_singleton] using (Nat.succ_le_of_lt (by positivity : 0 < 2 ^ d w))
        · intro i hi
          have hi' : i = ⟨w, hw⟩ := Finset.mem_singleton.mp hi
          rwa [hi', ← input_wire w hw x]
        · intro y hy
          exact (input_wire w hw y).trans (hy _ (by simp))
      · let j := w - n
        have hjw : n + j = w := by omega
        have hj : j < C.gates.length := by
          by_contra! hbad
          change (wires C.gates (List.ofFn x)).getD w false = true at hx
          rw [List.getD_eq_default _ _ (by
            rw [wires_length, List.length_ofFn]; omega)] at hx
          cases hx
        obtain ⟨a, b, hab⟩ := binary j hj
        have ha : a ∈ (gateAt C j).inputs := by simp [hab]
        have hb : b ∈ (gateAt C j).inputs := by simp [hab]
        have hla : a < w := by rw [← hjw]; exact hAO.2.1 j hj a ha
        have hlb : b < w := by rw [← hjw]; exact hAO.2.1 j hj b hb
        have hra := hrank j hj a ha
        have hrb := hrank j hj b hb
        change d a ≤ d (n + j) ∧ _ at hra
        change d b ≤ d (n + j) ∧ _ at hrb
        rw [hjw] at hra hrb
        have he (y : Fin n → Bool) :
            V w y = (gateAt C j).op.eval [V a y, V b y] := by
          conv_lhs => rw [← hjw, gate_wire j hj, hab]
          rfl
        have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
          rw [gate_get j hj]
          exact hAO.1 _ (List.getElem_mem hj)
        rcases hop with hop | hop
        · have hand (y : Fin n → Bool) : V w y = true ↔ V a y = true ∧ V b y = true := by
            rw [he, hop]
            change (V a y && (V b y && true)) = true ↔ _
            simp
          obtain ⟨A, hA, hAx, hAy⟩ := ih a hla x ((hand x).mp hx).1
          obtain ⟨B, hB, hBx, hBy⟩ := ih b hlb x ((hand x).mp hx).2
          refine ⟨A ∪ B, ?_, ?_, ?_⟩
          · have hwa : d a ≤ d w - 1 := by have := hra.2 hop; omega
            have hwb : d b ≤ d w - 1 := by have := hrb.2 hop; omega
            calc
              (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le _ _
              _ ≤ 2 ^ (d w - 1) + 2 ^ (d w - 1) :=
                Nat.add_le_add (hA.trans (Nat.pow_le_pow_right (by decide) hwa))
                  (hB.trans (Nat.pow_le_pow_right (by decide) hwb))
              _ = 2 ^ d w := by
                have hs : d w - 1 + 1 = d w := by have := hra.2 hop; omega
                conv_rhs => rw [← hs, Nat.pow_succ, Nat.mul_two]
          · intro i hi
            rcases Finset.mem_union.mp hi with ha' | hb'
            · exact hAx i ha'
            · exact hBx i hb'
          · intro y hy
            exact (hand y).mpr ⟨hAy y (fun i hi => hy i (Finset.mem_union_left _ hi)),
              hBy y (fun i hi => hy i (Finset.mem_union_right _ hi))⟩
        · have hor (y : Fin n → Bool) : V w y = true ↔ V a y = true ∨ V b y = true := by
            rw [he, hop]
            change (V a y || (V b y || false)) = true ↔ _
            simp
          rcases (hor x).mp hx with xa | xb
          · obtain ⟨A, hA, hxA, hyA⟩ := ih a hla x xa
            exact ⟨A, hA.trans (Nat.pow_le_pow_right (by decide) hra.1), hxA,
              fun y hy => (hor y).mpr (Or.inl (hyA y hy))⟩
          · obtain ⟨B, hB, hxB, hyB⟩ := ih b hlb x xb
            exact ⟨B, hB.trans (Nat.pow_le_pow_right (by decide) hrb.1), hxB,
              fun y hy => (hor y).mpr (Or.inr (hyB y hy))⟩
  have exactFun (z : Fin n → Bool) :
      circuitFun n C z = decide
        (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    constructor
    · intro hz
      obtain ⟨S, hS, hzS, lift⟩ := cert C.output z hz
      have hS4 : S.card ≤ 4 := hS.trans (Nat.pow_le_pow_right (by decide) hd)
      have htrue : circuitFun n C (fun i => decide (i ∈ S)) = true :=
        lift _ (fun i hi => decide_eq_true hi)
      rw [htest S hS4, decide_eq_true_eq] at htrue
      obtain ⟨p, l, hp, hpS, hlS⟩ := htrue
      exact ⟨p, l, hp, hzS _ hpS, hzS _ hlS⟩
    · rintro ⟨p, l, hp, hpz, hlz⟩
      let S : Finset (Fin n) := {Fin.castAdd N p, Fin.natAdd N l}
      have hS4 : S.card ≤ 4 := (Finset.card_insert_le _ _).trans (by simp)
      have htrue : circuitFun n C (fun i => decide (i ∈ S)) = true := by
        rw [htest S hS4, decide_eq_true_eq]
        exact ⟨p, l, hp, by simp [S], by simp [S]⟩
      obtain ⟨T, _, hTS, lift⟩ := cert C.output (fun i => decide (i ∈ S)) htrue
      apply lift z
      intro i hi
      have hiS := of_decide_eq_true (hTS i hi)
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hiS
      rcases hiS with h | h
      · rwa [h]
      · rwa [h]
  have hline' (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = 257 + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hline l
  exact (not_lt_of_ge (lower 257 N I C (by decide) hN hline' hpair hAO exactFun hread)) hsmall
