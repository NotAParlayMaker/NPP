import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4887

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_prefix (gs : List Gate) (inp : List Bool) : ∃ rest, gs.foldl step inp = inp ++ rest := by
  induction gs generalizing inp with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨rest, h⟩ := ih (step inp g)
    refine ⟨g.op.eval (g.inputs.map fun i => inp.getD i false) :: rest, ?_⟩
    rw [List.foldl_cons, h]
    simp only [step, List.append_assoc, List.singleton_append]

theorem foldl_length (gs : List Gate) (inp : List Bool) :
    (gs.foldl step inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem foldl_getD_lt (gs : List Gate) (inp : List Bool) (w : ℕ) (hw : w < inp.length) :
    (gs.foldl step inp).getD w false = inp.getD w false := by
  obtain ⟨rest, h⟩ := foldl_prefix gs inp
  rw [h, List.getD_append _ _ _ _ hw]

theorem getD_concat (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_getD_new (gs : List Gate) (inp : List Bool) (i : ℕ) (hi : i < gs.length) :
    (gs.foldl step inp).getD (inp.length + i) false =
      (gs[i]).op.eval ((gs[i]).inputs.map fun j => ((gs.take i).foldl step inp).getD j false) := by
  have hsplit := List.take_append_drop i gs
  rw [List.drop_eq_getElem_cons hi] at hsplit
  have hl : ((gs.take i).foldl step inp).length = inp.length + i := by
    rw [foldl_length, List.length_take]; omega
  conv_lhs => rw [← hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_getD_lt (gs.drop (i + 1)) (step ((gs.take i).foldl step inp) gs[i]) (inp.length + i)
    (by simp only [step, List.length_append, List.length_singleton, hl]; omega)]
  rw [← hl]
  exact getD_concat _ _

theorem foldl_getD_take (gs : List Gate) (inp : List Bool) (i j : ℕ) (hj : j < inp.length + i)
    (hi : i ≤ gs.length) :
    ((gs.take i).foldl step inp).getD j false = (gs.foldl step inp).getD j false := by
  conv_rhs => rw [← List.take_append_drop i gs, List.foldl_append]
  rw [foldl_getD_lt (gs.drop i) ((gs.take i).foldl step inp) j
    (by rw [foldl_length, List.length_take]; omega)]

end PEqualNP.Outside.L_meta_4887

open PEqualNP.Outside.L_meta_4887

theorem PEqualNP.Outside.L_meta_4887 : ∀ (x1 : ℕ) (x2 : List ((Fin x1 → Bool) → Bool)) (x3 : List (Bool → Set (Fin x1 → Bool))) (x4 : Bool → Set (Fin x1 → Bool)),   have x5 : List (Bool → Set (Fin x1 → Bool)) := List.map (fun (x5 : (Fin x1 → Bool) → Bool) (x6 : Bool) => {x7 : Fin x1 → Bool | x5 x7 = x6}) x2;   x4 ∈ x5 ++ x3 →     (∀ (x7 : Fin x3.length),         have x8 : List (Bool → Set (Fin x1 → Bool)) := x5 ++ List.take (↑x7) x3;         ∃ x9 ∈ x8, ∃ x10 ∈ x8, ∃ (x11 : Bool), ∀ (x12 : Bool), x3.get x7 x12 ⊆ if x12 = x11 then x9 x12 ∪ x10 x12 else x9 x12 ∩ x10 x12) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x3.length ∧ ∀ (x9 : Fin x1 → Bool) (x10 : Bool), x9 ∈ x4 x10 → x8.eval (List.map (fun (x12 : (Fin x1 → Bool) → Bool) => x12 x9) x2) = x10 := by
  intro n fs cs spec
  dsimp only
  intro hspec hchain
  classical
  set B := List.map (fun (f : (Fin n → Bool) → Bool) (b : Bool) => {x : Fin n → Bool | f x = b}) fs
    with hBdef
  have hB : B.length = fs.length := by simp [hBdef]
  have hpick : ∀ i : Fin cs.length, ∃ jp jq : ℕ, ∃ op : Bool, ∃ p q : Bool → Set (Fin n → Bool),
      jp < fs.length + i ∧ jq < fs.length + i ∧ (B ++ cs)[jp]? = some p ∧ (B ++ cs)[jq]? = some q ∧
      ∀ b, cs.get i b ⊆ (if b = op then p b ∪ q b else p b ∩ q b) := by
    intro i
    obtain ⟨p, hp, q, hq, op, hsub⟩ := hchain i
    have hpre : B ++ List.take (↑i) cs = List.take (fs.length + ↑i) (B ++ cs) := by
      rw [List.take_append, List.take_of_length_le (show B.length ≤ fs.length + ↑i by omega)]
      simp [hB]
    rw [hpre] at hp hq
    obtain ⟨jp, hjp⟩ := List.mem_iff_getElem?.1 hp
    obtain ⟨jq, hjq⟩ := List.mem_iff_getElem?.1 hq
    rw [List.getElem?_take] at hjp hjq
    by_cases h1 : jp < fs.length + ↑i
    · by_cases h2 : jq < fs.length + ↑i
      · rw [if_pos h1] at hjp
        rw [if_pos h2] at hjq
        exact ⟨jp, jq, op, p, q, h1, h2, hjp, hjq, hsub⟩
      · rw [if_neg h2] at hjq
        simp at hjq
    · rw [if_neg h1] at hjp
      simp at hjp
  choose jp jq op p q hjp hjq hp hq hsub using hpick
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hspec
  refine ⟨⟨List.ofFn fun i : Fin cs.length =>
    ⟨if op i then GateOp.or else GateOp.and, [jp i, jq i]⟩, k⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    refine ⟨?_, by simp⟩
    split_ifs <;> simp
  · simp [Circuit.size]
  · intro x b hx
    set gs : List Gate := List.ofFn fun i : Fin cs.length =>
      ⟨if op i then GateOp.or else GateOp.and, [jp i, jq i]⟩ with hgs
    set inp := List.map (fun (f : (Fin n → Bool) → Bool) => f x) fs with hinp
    have hilen : inp.length = fs.length := by simp [hinp]
    have key : ∀ w, ∀ e, (B ++ cs)[w]? = some e → ∀ c, x ∈ e c →
        (gs.foldl step inp).getD w false = c := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro e he c hc
        by_cases hw : w < fs.length
        · have hwl : w < inp.length := by omega
          rw [foldl_getD_lt gs inp w hwl]
          rw [List.getElem?_append_left (by omega), hBdef, List.getElem?_map,
            List.getElem?_eq_getElem hw] at he
          simp only [Option.map_some, Option.some.injEq] at he
          subst he
          simp only [Set.mem_setOf_eq] at hc
          rw [List.getD_eq_getElem?_getD, hinp, List.getElem?_map, List.getElem?_eq_getElem hw]
          simpa using hc
        · obtain ⟨i, rfl⟩ : ∃ i, w = fs.length + i := ⟨w - fs.length, by omega⟩
          rw [List.getElem?_append_right (by omega), hB] at he
          simp only [Nat.add_sub_cancel_left] at he
          have hi : i < cs.length := by
            by_contra h
            rw [List.getElem?_eq_none (by omega)] at he
            simp at he
          rw [List.getElem?_eq_getElem hi, Option.some.injEq] at he
          subst he
          have hgi : i < gs.length := by simp [hgs, hi]
          rw [← hilen, foldl_getD_new gs inp i hgi]
          have hget : gs[i] =
              ⟨if op ⟨i, hi⟩ then GateOp.or else GateOp.and, [jp ⟨i, hi⟩, jq ⟨i, hi⟩]⟩ := by
            simp [hgs]
          rw [hget]
          simp only [List.map_cons, List.map_nil]
          have hP := hjp ⟨i, hi⟩
          have hQ := hjq ⟨i, hi⟩
          rw [foldl_getD_take gs inp i (jp ⟨i, hi⟩) (by rw [hilen]; exact hP) hgi.le,
            foldl_getD_take gs inp i (jq ⟨i, hi⟩) (by rw [hilen]; exact hQ) hgi.le]
          have IP := ih _ (by simpa using hP) _ (hp ⟨i, hi⟩)
          have IQ := ih _ (by simpa using hQ) _ (hq ⟨i, hi⟩)
          have hs := hsub ⟨i, hi⟩ c (by simpa using hc)
          cases hop : op ⟨i, hi⟩
          · rw [hop] at hs
            rw [if_neg (by decide)]
            simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
            cases c
            · rw [if_pos rfl] at hs
              rcases hs with h | h
              · rw [IP false h, Bool.false_and]
              · rw [IQ false h, Bool.and_false]
            · rw [if_neg (by decide)] at hs
              rw [IP true hs.1, IQ true hs.2]
              rfl
          · rw [hop] at hs
            rw [if_pos rfl]
            simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
            cases c
            · rw [if_neg (by decide)] at hs
              rw [IP false hs.1, IQ false hs.2]
              rfl
            · rw [if_pos rfl] at hs
              rcases hs with h | h
              · rw [IP true h, Bool.true_or]
              · rw [IQ true h, Bool.or_true]
    exact key k spec hk b hx
