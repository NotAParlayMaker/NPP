import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_2862_aux

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

private theorem read_step_other (w : List Bool) (g : Gate) (i : ℕ) (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp [step]; omega), List.getD_eq_default _ _ (by omega)]

private theorem support (n : ℕ) (gs : List Gate)
    (hsize : ∀ g ∈ gs, g.inputs.length ≤ 2) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ T, x.getD i false = y.getD i false) →
        ∀ i ∈ S, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S, by simp, fun _ _ _ _ agree => agree⟩
  | append_singleton gs g ih =>
    have hg : g.inputs.length ≤ 2 := hsize g (by simp)
    let j := n + gs.length
    let P := if j ∈ S then S.erase j ∪ g.inputs.toFinset else S
    have earlier : ∀ i ∈ S, i ≠ j → i ∈ P := by
      intro i hi hne
      by_cases hj : j ∈ S <;> simp [P, hj, hi, hne]
    have pins : j ∈ S → ∀ i ∈ g.inputs, i ∈ P := by
      intro hj i hi
      simp [P, hj, hi]
    have growth : P.card ≤ S.card + 1 := by
      by_cases hj : j ∈ S
      · rw [show P = S.erase j ∪ g.inputs.toFinset by simp [P, hj]]
        have h := Finset.card_union_le (S.erase j) g.inputs.toFinset
        have h' := List.toFinset_card_le g.inputs
        have h'' := Finset.card_erase_add_one hj
        omega
      · simp [P, hj]
    obtain ⟨T, hT, reads⟩ := ih (fun a ha => hsize a (List.mem_append_left _ ha)) P
    refine ⟨T, by simp; omega, ?_⟩
    intro x y hx hy agree i hi
    have eq := reads x y hx hy agree
    have wx : (gs.foldl step x).length = j := by simp [run_length, hx, j]
    have wy : (gs.foldl step y).length = j := by simp [run_length, hy, j]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases he : i = j
    · have hi' : j ∈ S := he ▸ hi
      have vals : g.inputs.map (fun a => (gs.foldl step x).getD a false) =
          g.inputs.map (fun a => (gs.foldl step y).getD a false) :=
        List.map_congr_left (fun a ha => eq a (pins hi' a ha))
      rw [he]
      have atEnd (w : List Bool) (hw : w.length = j) :
          (step w g).getD j false = g.op.eval (g.inputs.map fun a => w.getD a false) := by
        rw [← hw]
        simp [step, List.getD_eq_getElem?_getD]
      rw [atEnd _ wx, atEnd _ wy, vals]
    · rw [read_step_other _ _ _ (by rwa [wx]), read_step_other _ _ _ (by rwa [wy])]
      exact eq i (earlier i hi he)

private theorem input_required {n : ℕ} (C : Circuit) (T : Finset ℕ)
    (stable : ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) → C.eval x = C.eval y)
    (a b : Fin n)
    (hp : circuitFun n C (fun k => decide (k = a ∨ k = b)) = true)
    (hn : circuitFun n C (fun k => decide (k = b)) = false) :
    a.val ∈ T := by
  classical
  by_contra hm
  let x : Fin n → Bool := fun k => decide (k = a ∨ k = b)
  let y : Fin n → Bool := fun k => decide (k = b)
  have eq : ∀ i ∈ T, (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro i hi
    by_cases hn' : i < n
    · have hne : (⟨i, hn'⟩ : Fin n) ≠ a := by
        intro he
        exact hm ((congrArg Fin.val he) ▸ hi)
      have hlen (f : Fin n → Bool) : i < (List.ofFn f).length := by simpa using hn'
      rw [List.getD_eq_getElem _ _ (hlen x), List.getD_eq_getElem _ _ (hlen y)]
      simp [x, y, hne, List.getElem_ofFn]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have e := stable (List.ofFn x) (List.ofFn y) List.length_ofFn List.length_ofFn eq
  change circuitFun n C x = circuitFun n C y at e
  rw [show circuitFun n C x = true from hp, show circuitFun n C y = false from hn] at e
  contradiction

end PEqualNP.Outside.L_meta_2862_aux

open PEqualNP.Outside.L_meta_2862_aux in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_2862 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x1 < (200 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hq' hN hlines hjoins hmono hpos hneg
  have hbig : 100 ≤ N := by omega
  obtain ⟨T, hT, stable⟩ := support (N + N) C.gates
    (fun g hg => (hmono g hg).2) {C.output}
  have eval_agree (x y : List Bool) (hx : x.length = N + N) (hy : y.length = N + N)
      (h : ∀ i ∈ T, x.getD i false = y.getD i false) : C.eval x = C.eval y :=
    stable x y hx hy h C.output (by simp)
  have separate (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro he
    have h := congrArg Fin.val he
    change p.val = N + l.val at h
    omega
  have pointOnly (p : Fin N) :
      circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p)) = false := by
    apply hneg
    · have hzero : Fintype.card {l : Fin N // decide (Fin.natAdd N l = Fin.castAdd N p) = true} = 0 := by
        rw [Fintype.card_subtype]
        simp only [decide_eq_true_eq]
        have he : Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = Fin.castAdd N p) = ∅ := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
          exact iff_false_intro (Ne.symm (separate p l))
        rw [he, Finset.card_empty]
      change Fintype.card {l : Fin N // decide (Fin.natAdd N l = Fin.castAdd N p) = true} ≤ q
      omega
    · rintro ⟨p',l,_,_,hl⟩
      exact (separate p l).symm (of_decide_eq_true hl)
  have lineOnly (l : Fin N) :
      circuitFun (N + N) C (fun k => decide (k = Fin.natAdd N l)) = false := by
    apply hneg
    · have he (v : Fin N) : decide (Fin.natAdd N v = Fin.natAdd N l) = true ↔ v = l := by
        rw [decide_eq_true_eq]
        constructor
        · intro h
          apply Fin.ext
          have hv := congrArg Fin.val h
          change N + v.val = N + l.val at hv
          omega
        · rintro rfl
          rfl
      change Fintype.card {v : Fin N // decide (Fin.natAdd N v = Fin.natAdd N l) = true} ≤ q
      rw [Fintype.card_subtype]
      have hs : Finset.univ.filter (fun v : Fin N => decide (Fin.natAdd N v = Fin.natAdd N l) = true) = {l} := by
        ext v
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using he v
      rw [hs, Finset.card_singleton]
      omega
    · rintro ⟨p,l',_,hp,_⟩
      exact separate p l (of_decide_eq_true hp)
  have pointWire (p : Fin N) : (Fin.castAdd N p).val ∈ T := by
    let r : Fin N := ⟨if p.val = 0 then 1 else 0, by split <;> omega⟩
    have hpr : p ≠ r := by
      intro h
      have he := congrArg Fin.val h
      change p.val = (if p.val = 0 then 1 else 0) at he
      split at he <;> omega
    obtain ⟨l, hl, _⟩ := hjoins p r hpr
    exact input_required C T eval_agree _ _ (hpos p l hl.1) (lineOnly l)
  have lineWire (l : Fin N) : (Fin.natAdd N l).val ∈ T := by
    have h : 0 < Fintype.card {p : Fin N // I p l} := by rw [hlines]; omega
    obtain ⟨p⟩ := Fintype.card_pos_iff.mp h
    apply input_required C T eval_agree (Fin.natAdd N l) (Fin.castAdd N p.val) _
      (pointOnly p.val)
    simpa only [or_comm] using hpos p.val l p.property
  have cover : Finset.range (N + N) ⊆ T := by
    intro i hi
    have bound : i < N + N := Finset.mem_range.mp hi
    refine Fin.addCases (motive := fun k => k.val ∈ T) pointWire lineWire ⟨i,bound⟩
  have hn := Finset.card_le_card cover
  rw [Finset.card_range] at hn
  have hsmall := Nat.mul_le_mul_left N (show q ≤ 199 by omega)
  change N * q ≤ 100 * C.gates.length
  simp only [Finset.card_singleton] at hT
  omega
