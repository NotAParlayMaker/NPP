import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, xs⟩ := g
  cases op <;> rfl

theorem wf_norm (gs : List Gate) : ∀ w : List Bool, wf (gs.map normGate) w = wf gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wf ((g :: gs).map normGate) w = wf (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

theorem merge_card' (s : Finset ℕ) (lab : ℕ → ℕ) (ca cb : ℕ) :
    (s.image lab).card ≤ (s.image (fun i => if lab i = cb then ca else lab i)).card + 1 := by
  classical
  have hsub : (s.image lab).erase cb ⊆ s.image (fun i => if lab i = cb then ca else lab i) := by
    intro d hd
    obtain ⟨hne, hd⟩ := Finset.mem_erase.1 hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hd
    exact Finset.mem_image.2 ⟨x, hx, by simp [hne]⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := s.image lab) (a := cb)
  omega

end PEqualNP.Outside.L_meta_3358

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3358 in
theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 := by
  intro C fan hsize a4 a5 h45 hn4 hn5
  classical
  let gs := C.gates.map normGate
  have glen : gs.length = C.gates.length := by simp [gs]
  have gget : ∀ j (hj : j < gs.length), gs[j] = normGate (C.gates[j]'(by omega)) := by
    intro j hj; simp [gs]
  let val : List Bool → ℕ → Bool := fun x i => (wf gs x).getD i false
  have hval : ∀ x, C.eval x = val x C.output := by
    intro x
    show (C.wires x).getD C.output false = (wf (C.gates.map normGate) x).getD C.output false
    rw [wf_norm]
    rfl
  have gateV : ∀ j (hj : j < gs.length) (x : List Bool), x.length = 17 →
      val x (17 + j) = gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < 17 + j then val x i else false) := by
    intro j hj x hx
    have g1 := gate_val gs x j hj
    rw [hx] at g1
    show (wf gs x).getD (17 + j) false = _
    rw [g1]
    congr 1
    apply List.map_congr_left
    intro i _
    split_ifs with hi
    · exact (wire_take gs x j i (by rw [hx]; exact hi) (le_of_lt hj)).symm
    · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, hx]; omega)]
  have lenOk : ∀ j (hj : j < gs.length), gs[j].inputs.length ≤ 2 ∧
      (gs[j].op = GateOp.not → gs[j].inputs.length ≤ 1) := by
    intro j hj
    rw [gget j hj]
    have hf := (fan _ (List.getElem_mem (show j < C.gates.length by omega))).2
    generalize C.gates[j]'(by omega) = g at hf ⊢
    obtain ⟨op, xs⟩ := g
    cases op <;> simp only [normGate] at hf ⊢
    case not => simp <;> omega
    all_goals exact ⟨hf, fun h => by cases h⟩
  have isNot : ∀ (a : Fin C.gates.length), (C.gates.get a).op = GateOp.not →
      (gs[a.val]'(by omega)).op = GateOp.not := by
    intro a ha
    rw [gget a.val (by omega), normGate_op]
    exact ha
  let cnt : ℕ → ℕ := fun j => ((Finset.range j).filter (fun i => i ≠ a4.val ∧ i ≠ a5.val)).card
  have key : ∀ j ≤ gs.length, ∃ (lab c : ℕ → ℕ),
      (∀ w < 17 + j, ∀ x x' : List Bool, x.length = 17 → x'.length = 17 →
        (∀ i < 17, lab i = c w → x.getD i false = x'.getD i false) → val x w = val x' w) ∧
      17 ≤ ((Finset.range 17).image lab).card + cnt j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨id, id, ?_, ?_⟩
      · intro w hw x x' hx hx' hag
        show (wf gs x).getD w false = (wf gs x').getD w false
        rw [wf_keep _ _ _ (by omega), wf_keep _ _ _ (by omega)]
        exact hag w (by omega) rfl
      · simp [cnt]
    | succ j ih =>
      intro hj
      obtain ⟨lab, c, hA, hB⟩ := ih (by omega)
      have hjl : j < gs.length := by omega
      by_cases hcase : ∃ a b, gs[j].inputs = [a, b] ∧ a < 17 + j ∧ b < 17 + j ∧ c a ≠ c b
      · obtain ⟨a, b, hab, ha, hb, hne⟩ := hcase
        have hjn : j ≠ a4.val ∧ j ≠ a5.val := by
          constructor
          · intro h
            subst h
            have h1 := (lenOk _ hjl).2 (isNot a4 hn4)
            rw [hab] at h1
            simp at h1
          · intro h
            subst h
            have h1 := (lenOk _ hjl).2 (isNot a5 hn5)
            rw [hab] at h1
            simp at h1
        refine ⟨fun i => if lab i = c b then c a else lab i,
          fun w => if w = 17 + j then c a else (if c w = c b then c a else c w), ?_, ?_⟩
        · intro w hw x x' hx hx' hag
          rcases (show w < 17 + j ∨ w = 17 + j by omega) with hlt | rfl
          · apply hA w hlt x x' hx hx'
            intro i hi hli
            apply hag i hi
            have hw' : w ≠ 17 + j := by omega
            simp only [hw', if_false, hli]
          · rw [gateV j hjl x hx, gateV j hjl x' hx', hab]
            have va : val x a = val x' a := by
              apply hA a ha x x' hx hx'
              intro i hi hli
              apply hag i hi
              simp [hli, hne]
            have vb : val x b = val x' b := by
              apply hA b hb x x' hx hx'
              intro i hi hli
              apply hag i hi
              simp [hli]
            simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, va, vb]
        · have hm := merge_card' (Finset.range 17) lab (c a) (c b)
          have hc : cnt (j + 1) = cnt j + 1 := by
            simp only [cnt, Finset.range_add_one, Finset.filter_insert, if_pos hjn]
            rw [Finset.card_insert_of_notMem (by simp)]
          omega
      · have hsame : ∀ i i', i ∈ gs[j].inputs → i' ∈ gs[j].inputs → i < 17 + j → i' < 17 + j →
            c i = c i' := by
          intro i i' hi hi' hl hl'
          have hlen := (lenOk j hjl).1
          rcases hI : gs[j].inputs with _ | ⟨u, _ | ⟨v, _ | ⟨d, t⟩⟩⟩
          · rw [hI] at hi; simp at hi
          · rw [hI] at hi hi'
            simp at hi hi'
            rw [hi, hi']
          · rw [hI] at hi hi'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hi'
            by_contra hne
            apply hcase
            rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
            · exact absurd rfl hne
            · exact ⟨i, i', hI, hl, hl', hne⟩
            · exact ⟨i', i, hI, hl', hl, fun h => hne h.symm⟩
            · exact absurd rfl hne
          · rw [hI] at hlen; simp at hlen
        let k : ℕ := if h : ∃ i ∈ gs[j].inputs, i < 17 + j then c (Classical.choose h) else 0
        have hk : ∀ i ∈ gs[j].inputs, i < 17 + j → c i = k := by
          intro i hi hl
          have hex : ∃ i ∈ gs[j].inputs, i < 17 + j := ⟨i, hi, hl⟩
          have e : k = c (Classical.choose hex) := dif_pos hex
          rw [e]
          obtain ⟨h1, h2⟩ := Classical.choose_spec hex
          exact hsame i _ hi h1 hl h2
        refine ⟨lab, fun w => if w = 17 + j then k else c w, ?_, ?_⟩
        · intro w hw x x' hx hx' hag
          rcases (show w < 17 + j ∨ w = 17 + j by omega) with hlt | rfl
          · apply hA w hlt x x' hx hx'
            intro i hi hli
            apply hag i hi
            have hw' : w ≠ 17 + j := by omega
            simp only [hw', if_false, hli]
          · rw [gateV j hjl x hx, gateV j hjl x' hx']
            congr 1
            apply List.map_congr_left
            intro i hi
            split_ifs with hl
            · apply hA i hl x x' hx hx'
              intro t ht hlt
              apply hag t ht
              simp only [if_true]
              rw [hlt, hk i hi hl]
            · rfl
        · have : cnt j ≤ cnt (j + 1) := by
            apply Finset.card_le_card
            intro t ht
            simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
            exact ⟨by omega, ht.2⟩
          omega
  obtain ⟨lab, c, hA, hB⟩ := key gs.length le_rfl
  have hcnt : cnt gs.length + 2 ≤ gs.length := by
    have hsub : (Finset.range gs.length).filter (fun i => i ≠ a4.val ∧ i ≠ a5.val) ⊆
        ((Finset.range gs.length).erase a4.val).erase a5.val := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      simp [ht.1, ht.2.1, ht.2.2]
    have h1 := Finset.card_le_card hsub
    have hne : a5.val ≠ a4.val := by
      intro h; exact absurd (Fin.ext h).symm (ne_of_lt h45)
    rw [Finset.card_erase_of_mem (by simp [hne]; omega), Finset.card_erase_of_mem (by simp; omega),
      Finset.card_range] at h1
    have : 2 ≤ gs.length := by have := a5.isLt; have : a4.val < a5.val := h45; omega
    show ((Finset.range gs.length).filter (fun i => i ≠ a4.val ∧ i ≠ a5.val)).card + 2 ≤ gs.length
    omega
  have hsz : gs.length ≤ 7 := by rw [glen]; exact hsize
  by_cases ho : C.output < 17 + gs.length
  · let X := (Finset.range 17).filter (fun i => lab i = c C.output)
    refine ⟨X, Finset.filter_subset _ _, ?_, ?_⟩
    · have hcomp : ((Finset.range 17).image lab).erase (c C.output) ⊆
          ((Finset.range 17) \ X).image lab := by
        intro d hd
        obtain ⟨hne, hd⟩ := Finset.mem_erase.1 hd
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
        exact Finset.mem_image.2 ⟨i, Finset.mem_sdiff.2 ⟨hi, fun hx => hne (Finset.mem_filter.1 hx).2⟩, rfl⟩
      have e1 := Finset.card_le_card hcomp
      have e2 := Finset.card_image_le (s := Finset.range 17 \ X) (f := lab)
      have e3 := Finset.pred_card_le_card_erase (s := (Finset.range 17).image lab) (a := c C.output)
      have e4 := Finset.card_sdiff_add_card_eq_card (show X ⊆ Finset.range 17 from Finset.filter_subset _ _)
      simp only [Finset.card_range] at e4
      omega
    · intro x x' hx hx' hag
      rw [hval, hval]
      exact hA C.output ho x x' hx hx'
        (fun i hi hli => hag i (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hli⟩))
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro x x' hx hx' _
    rw [hval, hval]
    show (wf gs x).getD C.output false = (wf gs x').getD C.output false
    rw [List.getD_eq_default _ _ (by rw [wf_len, hx]; omega),
      List.getD_eq_default _ _ (by rw [wf_len, hx']; omega)]
