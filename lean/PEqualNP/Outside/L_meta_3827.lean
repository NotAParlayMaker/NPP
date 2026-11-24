import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3827

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

def Rel (b : Bool) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ 0 < w.length ∧ (∀ i, i ≠ 0 → w.getD i false = w'.getD i false) ∧
    w'.getD 0 false = (b ^^ w.getD 0 false)

def Good (b : Bool) (len : ℕ) (g h : Gate) : Prop :=
  ∀ w w' : List Bool, w.length = len → Rel b w w' →
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      h.op.eval (h.inputs.map fun i => w'.getD i false)

theorem getD_snoc (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem rel_snoc {b : Bool} {w w' : List Bool} (a : Bool) (h : Rel b w w') :
    Rel b (w ++ [a]) (w' ++ [a]) := by
  obtain ⟨hl, hp, hne, h0⟩ := h
  refine ⟨by simp [hl], by simp, ?_, ?_⟩
  · intro i hi
    rw [getD_snoc, getD_snoc, ← hl, hne i hi]
  · rw [getD_snoc, getD_snoc, ← hl]
    simp only [hp, ite_true]
    exact h0

theorem fold_rel (b : Bool) : ∀ (gs hs : List Gate) (w w' : List Bool), gs.length = hs.length →
    (∀ i (hi : i < gs.length) (hi' : i < hs.length), Good b (w.length + i) gs[i] hs[i]) →
    Rel b w w' → Rel b (gs.foldl step w) (hs.foldl step w')
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | g :: gs, h :: hs, w, w', hl, hg, hr => by
    simp only [List.foldl_cons]
    have e := hg 0 (by simp) (by simp) w w' (by simp) hr
    simp only [List.getElem_cons_zero] at e
    have hr' : Rel b (step w g) (step w' h) := by
      unfold step
      rw [e]
      exact rel_snoc _ hr
    refine fold_rel b gs hs _ _ (by simpa using hl) ?_ hr'
    intro i hi hi'
    have := hg (i + 1) (by simp; omega) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    have hlen : (step w g).length = w.length + 1 := by simp [step]
    rw [hlen, show w.length + 1 + i = w.length + (i + 1) by omega]
    exact this

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false
  | [], _, _, _ => rfl
  | g :: gs, w, i, hi => by
    simp only [List.foldl_cons]
    rw [fold_prefix gs _ i (by simp [step]; omega)]
    unfold step
    exact List.getD_append _ _ _ _ hi

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

theorem transfer (b : Bool) (C D : Circuit) (xC xD : Fin 9 → Bool)
    (h0 : xD 0 = (b ^^ xC 0)) (hr : ∀ i : Fin 9, i ≠ 0 → xD i = xC i)
    (hlen : C.gates.length = D.gates.length)
    (hg : ∀ i (hi : i < C.gates.length) (hi' : i < D.gates.length),
      Good b (9 + i) C.gates[i] D.gates[i])
    (hout : C.output = D.output) (hout0 : C.output ≠ 0 ∨ b = false) :
    C.eval (List.ofFn xC) = D.eval (List.ofFn xD) := by
  have hinit : Rel b (List.ofFn xC) (List.ofFn xD) := by
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro i hi
      rw [getD_ofFn, getD_ofFn]
      split_ifs with h
      · exact (hr ⟨i, h⟩ (by intro e; exact hi (congrArg Fin.val e))).symm
      · rfl
    · rw [getD_ofFn, getD_ofFn, dif_pos (by norm_num), dif_pos (by norm_num)]
      exact h0
  have hfin := fold_rel b C.gates D.gates _ _ hlen
    (by intro i hi hi'; simpa using hg i hi hi') hinit
  obtain ⟨_, _, hne, hz⟩ := hfin
  unfold Circuit.eval
  rw [wires_eq, wires_eq, ← hout]
  rcases hout0 with h | h
  · exact hne _ h
  · by_cases ho : C.output = 0
    · rw [ho, hz, h]
      simp
    · exact hne _ ho

theorem fanin_set (C : Circuit) (j : ℕ) (g' : Gate) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hg : g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.FanInTwo ⟨C.gates.set j g', C.output⟩ := by
  intro g hgm
  rcases List.mem_or_eq_of_mem_set hgm with h | h
  · exact hC g h
  · rw [h]
    exact hg

theorem good_same (b : Bool) (len : ℕ) (g : Gate) (h : 0 ∉ g.inputs) : Good b len g g := by
  intro w w' _ hr
  obtain ⟨_, _, hne, _⟩ := hr
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hne i (fun e => h (e ▸ hi))

theorem repl (j : ℕ) (g : Gate)
    (hF : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h0 : 0 ∈ g.inputs)
    (hR : ¬ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ c, 0 < c ∧ c < 9 + j ∧ (g.inputs = [0, c] ∨ g.inputs = [c, 0]))) :
    ∃ g' : Gate, (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g'.inputs.length ≤ 2) ∧ Good true (9 + j) g g' := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hF
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen h0 hR
  -- the two replacement gates used below
  have gNot : (⟨GateOp.not, [0]⟩ : Gate).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (⟨GateOp.not, [0]⟩ : Gate).inputs.length ≤ 2 := by simp
  have gAnd : (⟨GateOp.and, [0]⟩ : Gate).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (⟨GateOp.and, [0]⟩ : Gate).inputs.length ≤ 2 := by simp
  have gFalse : (⟨GateOp.or, []⟩ : Gate).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (⟨GateOp.or, []⟩ : Gate).inputs.length ≤ 2 := by simp
  rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
  · simp at h0
  · -- one input, which is wire 0
    simp at h0
    subst h0
    rcases hop with rfl | rfl | rfl
    · refine ⟨⟨GateOp.not, [0]⟩, gNot, ?_⟩
      intro w w' _ hr
      obtain ⟨_, _, _, hz⟩ := hr
      simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hz]
    · refine ⟨⟨GateOp.not, [0]⟩, gNot, ?_⟩
      intro w w' _ hr
      obtain ⟨_, _, _, hz⟩ := hr
      simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hz]
    · refine ⟨⟨GateOp.and, [0]⟩, gAnd, ?_⟩
      intro w w' _ hr
      obtain ⟨_, _, _, hz⟩ := hr
      simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hz]
  · -- two inputs a, c
    simp at h0
    by_cases ha : a = 0
    · subst ha
      by_cases hc : c = 0
      · subst hc
        rcases hop with rfl | rfl | rfl
        · refine ⟨⟨GateOp.not, [0]⟩, gNot, ?_⟩
          intro w w' _ hr
          obtain ⟨_, _, _, hz⟩ := hr
          simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hz]
        · refine ⟨⟨GateOp.not, [0]⟩, gNot, ?_⟩
          intro w w' _ hr
          obtain ⟨_, _, _, hz⟩ := hr
          simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hz]
        · refine ⟨⟨GateOp.and, [0]⟩, gAnd, ?_⟩
          intro w w' _ hr
          obtain ⟨_, _, _, hz⟩ := hr
          simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hz]
      · rcases hop with rfl | rfl | rfl
        · have hcj : 9 + j ≤ c := by
            by_contra hh
            exact hR ⟨Or.inl rfl, c, by omega, by omega, Or.inl rfl⟩
          refine ⟨⟨GateOp.or, []⟩, gFalse, ?_⟩
          intro w w' hl _
          have : w.getD c false = false := List.getD_eq_default _ _ (by omega)
          simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, this]
        · have hcj : 9 + j ≤ c := by
            by_contra hh
            exact hR ⟨Or.inr rfl, c, by omega, by omega, Or.inl rfl⟩
          refine ⟨⟨GateOp.not, [0]⟩, gNot, ?_⟩
          intro w w' hl hr
          obtain ⟨_, _, _, hz⟩ := hr
          have : w.getD c false = false := List.getD_eq_default _ _ (by omega)
          simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, this, hz]
        · refine ⟨⟨GateOp.and, [0]⟩, gAnd, ?_⟩
          intro w w' _ hr
          obtain ⟨_, _, _, hz⟩ := hr
          simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hz]
    · have hc : c = 0 := by
        rcases h0 with h | h
        · exact absurd h.symm ha
        · exact h.symm
      subst hc
      rcases hop with rfl | rfl | rfl
      · have haj : 9 + j ≤ a := by
          by_contra hh
          exact hR ⟨Or.inl rfl, a, by omega, by omega, Or.inr rfl⟩
        refine ⟨⟨GateOp.or, []⟩, gFalse, ?_⟩
        intro w w' hl _
        have : w.getD a false = false := List.getD_eq_default _ _ (by omega)
        simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, this]
      · have haj : 9 + j ≤ a := by
          by_contra hh
          exact hR ⟨Or.inr rfl, a, by omega, by omega, Or.inr rfl⟩
        refine ⟨⟨GateOp.not, [0]⟩, gNot, ?_⟩
        intro w w' hl hr
        obtain ⟨_, _, _, hz⟩ := hr
        have : w.getD a false = false := List.getD_eq_default _ _ (by omega)
        simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, this, hz]
      · refine ⟨⟨GateOp.not, [a]⟩, by simp, ?_⟩
        intro w w' _ hr
        obtain ⟨_, _, hne, _⟩ := hr
        simp only [List.getD_eq_getElem?_getD] at *; simp [GateOp.eval, hne a ha]
  · simp at hlen

end PEqualNP.Outside.L_meta_3827

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3827

theorem PEqualNP.Outside.L_meta_3827 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : (Fin (9 : ℕ) → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) = x3 x7) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (14 : ℕ) ∧ ∀ (x9 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 x9 = x3 x9) ∨ ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (14 : ℕ) ∧ (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.inputs.contains (0 : ℕ)) x8.gates).length = (1 : ℕ) ∧ x9 < x8.gates.length ∧ (0 : ℕ) < x10 ∧ x10 < (9 : ℕ) + x9 ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).inputs = [(0 : ℕ), x10] ∧ ∀ (x11 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 fun (x12 : Fin (9 : ℕ)) => if x12 = (0 : Fin (9 : ℕ)) then !x11 (0 : Fin (9 : ℕ)) else x11 x12) = x3 x11 := by
  intro x1 x2 x3 hF hsize hread hcomp
  cases x2 with
  | false =>
    left
    refine ⟨x1, hF, hsize, fun x9 => ?_⟩
    rw [← hcomp x9]
    congr 1
    funext i
    split_ifs with h
    · subst h
      cases x9 0 <;> rfl
    · rfl
  | true =>
    have hcomp' : ∀ x : Fin 9 → Bool,
        PEqualNP.MetaComplexity.circuitFun 9 x1 (fun i => if i = 0 then !x 0 else x i) = x3 x := by
      intro x
      rw [← hcomp x]
      congr 1
      funext i
      split_ifs
      · cases x 0 <;> rfl
      · rfl
    by_cases ho : x1.output = 0
    · left
      refine ⟨⟨[⟨GateOp.not, [0]⟩], 9⟩, ?_, by simp [Circuit.size], ?_⟩
      · intro g hg
        simp at hg
        subst hg
        simp
      · intro x9
        rw [← hcomp' x9]
        unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
        rw [wires_eq, wires_eq, ho, fold_prefix _ _ 0 (by simp)]
        simp [step, GateOp.eval, getD_ofFn, getD_snoc]
    · by_cases hex : ∃ j, ∃ hj : j < x1.gates.length, 0 ∈ x1.gates[j].inputs
      · obtain ⟨j, hj, h0j⟩ := hex
        have hcnt : x1.gates.countP (fun g : Gate => g.inputs.contains 0) ≤ 1 := by
          rw [List.countP_eq_length_filter]
          exact hread
        have hpos : 0 < x1.gates.countP (fun g : Gate => g.inputs.contains 0) :=
          List.countP_pos_iff.2 ⟨x1.gates[j], List.getElem_mem hj, by simpa using h0j⟩
        have huniq : ∀ i (hi : i < x1.gates.length), i ≠ j → 0 ∉ x1.gates[i].inputs := by
          intro i hi hij hmem
          have hc := List.countP_set (p := fun g : Gate => g.inputs.contains 0)
            (a := (⟨GateOp.or, []⟩ : Gate)) hi
          have hpos2 : 0 < (x1.gates.set i ⟨GateOp.or, []⟩).countP
              (fun g : Gate => g.inputs.contains 0) := by
            refine List.countP_pos_iff.2 ⟨x1.gates[j], ?_, by simpa using h0j⟩
            have hj' : j < (x1.gates.set i ⟨GateOp.or, []⟩).length := by simpa using hj
            have := List.getElem_mem hj'
            rwa [List.getElem_set_ne hij] at this
          have hm : (x1.gates[i].inputs.contains 0) = true := by simpa using hmem
          have hz0 : ¬ ((⟨GateOp.or, []⟩ : Gate).inputs.contains 0 = true) := by decide
          rw [if_pos hm, if_neg hz0] at hc
          omega
        have hcount1 : (List.filter (fun x11 : Gate => x11.inputs.contains 0) x1.gates).length = 1 := by
          rw [← List.countP_eq_length_filter]
          omega
        have hgF := hF x1.gates[j] (List.getElem_mem hj)
        by_cases hR : (x1.gates[j].op = GateOp.and ∨ x1.gates[j].op = GateOp.or) ∧
            ∃ c, 0 < c ∧ c < 9 + j ∧ (x1.gates[j].inputs = [0, c] ∨ x1.gates[j].inputs = [c, 0])
        · obtain ⟨hop, c, hc0, hcj, hins⟩ := hR
          have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt x1 j = x1.gates[j] := by
            unfold PEqualNP.MetaComplexity.NestedCover.gateAt
            exact List.getD_eq_getElem _ _ hj
          rcases hins with hins | hins
          · right
            refine ⟨x1, j, c, hF, hsize, hcount1, hj, hc0, hcj, ?_, ?_, hcomp'⟩
            · rw [hgate]; exact hop
            · rw [hgate]; exact hins
          · right
            let g' : Gate := ⟨x1.gates[j].op, [0, c]⟩
            have hjs : j < (x1.gates.set j g').length := by simpa using hj
            have hgate' : PEqualNP.MetaComplexity.NestedCover.gateAt
                ⟨x1.gates.set j g', x1.output⟩ j = g' := by
              unfold PEqualNP.MetaComplexity.NestedCover.gateAt
              rw [List.getD_eq_getElem _ _ hjs]
              simp
            refine ⟨⟨x1.gates.set j g', x1.output⟩, j, c, ?_, ?_, ?_, hjs, hc0, hcj, ?_, ?_, ?_⟩
            · refine fanin_set x1 j g' hF ⟨?_, by simp [g']⟩
              rcases hop with h | h <;> simp [g', h]
            · simpa [Circuit.size] using hsize
            · show (List.filter (fun x11 : Gate => x11.inputs.contains 0) (x1.gates.set j g')).length = 1
              rw [← List.countP_eq_length_filter, List.countP_set hj]
              have hm : (x1.gates[j].inputs.contains 0) = true := by simpa using h0j
              have hg'0 : (g'.inputs.contains 0) = true := by simp [g']
              rw [if_pos hm, if_pos hg'0]
              omega
            · rw [hgate']; exact hop
            · rw [hgate']
            · intro x11
              rw [← hcomp' x11]
              unfold PEqualNP.MetaComplexity.circuitFun
              refine (transfer false x1 ⟨x1.gates.set j g', x1.output⟩ _ _ (by simp)
                (fun _ _ => rfl) (by simp) ?_ rfl (Or.inr rfl)).symm
              intro i hi hi'
              by_cases hij : i = j
              · subst hij
                simp only [List.getElem_set_self]
                intro w w' _ hr
                obtain ⟨_, _, hne, hz⟩ := hr
                rw [hins]
                rcases hop with h | h
                · simp only [List.getD_eq_getElem?_getD] at *; simp [g', h, GateOp.eval, hz, hne c (by omega), Bool.and_comm]
                · simp only [List.getD_eq_getElem?_getD] at *; simp [g', h, GateOp.eval, hz, hne c (by omega), Bool.or_comm]
              · simp only [List.getElem_set_ne (Ne.symm hij)]
                exact good_same _ _ _ (huniq i hi hij)
        · obtain ⟨g', hg'F, hgood⟩ := repl j x1.gates[j] hgF h0j hR
          left
          refine ⟨⟨x1.gates.set j g', x1.output⟩, fanin_set x1 j g' hF hg'F,
            by simpa [Circuit.size] using hsize, fun x9 => ?_⟩
          rw [← hcomp' x9]
          unfold PEqualNP.MetaComplexity.circuitFun
          refine (transfer true x1 ⟨x1.gates.set j g', x1.output⟩ _ x9 (by simp)
            (by intro i hi; simp [hi]) (by simp) ?_ rfl (Or.inl ho)).symm
          intro i hi hi'
          by_cases hij : i = j
          · subst hij
            simp only [List.getElem_set_self]
            exact hgood
          · simp only [List.getElem_set_ne (Ne.symm hij)]
            exact good_same _ _ _ (huniq i hi hij)
      · left
        refine ⟨x1, hF, hsize, fun x9 => ?_⟩
        rw [← hcomp' x9]
        unfold PEqualNP.MetaComplexity.circuitFun
        refine (transfer true x1 x1 _ x9 (by simp) (by intro i hi; simp [hi]) rfl ?_ rfl
          (Or.inl ho)).symm
        intro i hi _
        exact good_same _ _ _ (fun hm => hex ⟨i, hi, hm⟩)
