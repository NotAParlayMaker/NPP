import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj


def mw (a n w : ℕ) : ℕ := if w < a then w else n + w

def mapGate (a n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (mw a n)⟩

def mapC (a n : ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate a n), mw a n C.output⟩

lemma gateAt_mapC (a n : ℕ) (C : Circuit) (j : ℕ) :
    gateAt (mapC a n C) j = mapGate a n (gateAt C j) := by
  unfold gateAt mapC
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> simp [mapGate]

lemma mapC_val (a n : ℕ) (han : a ≤ n) (C : Circuit) (hRB : ReadsBack n C)
    (z : List Bool) (hz : z.length = n + n) (x : List Bool) (hx : x.length = n)
    (hxz : ∀ i < n, x.getD i false = z.getD (mw a n i) false) :
    ∀ w < n + C.gates.length, val (mapC a n C) z (mw a n w) = val C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · have hm : mw a n w < n + n := by unfold mw; split_ifs <;> omega
      rw [val_input (n := n + n) hz hm, val_input hx hwn, hxz w hwn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hj' : j < (mapC a n C).gates.length := by simp [mapC]; exact hj
      have e : mw a n (n + j) = n + n + j := by unfold mw; split_ifs <;> omega
      rw [e, val_gate hz hj', val_gate hx hj, gateAt_mapC]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt : i < n + j := hRB j hj i hi
      have hlt' : mw a n i < n + n + j := by unfold mw; split_ifs <;> omega
      simp only [Function.comp_apply, if_pos hlt, if_pos hlt']
      exact ih i hlt (by omega)

lemma mapC_AO2 (a n : ℕ) (han : a ≤ n) (C : Circuit) (hA : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 (n + n) (mapC a n C) := by
  obtain ⟨hAO, hRB, h2⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [mapC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hAO g0 hg0
  · intro j hj i hi
    have hj0 : j < C.gates.length := by simpa [mapC] using hj
    rw [gateAt_mapC] at hi
    simp only [mapGate, List.mem_map] at hi
    obtain ⟨i0, hi0, rfl⟩ := hi
    have := hRB j hj0 i0 hi0
    unfold mw; split_ifs <;> omega
  · intro g hg
    simp only [mapC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simp [mapGate, h2 g0 hg0]

lemma val_append (gs hs : List Gate) (o o' : ℕ) (z : List Bool) (i : ℕ)
    (hi : i < z.length + gs.length) :
    val ⟨gs ++ hs, o'⟩ z i = val ⟨gs, o⟩ z i := by
  change (List.foldl stepWire z (gs ++ hs)).getD i false = (List.foldl stepWire z gs).getD i false
  rw [List.foldl_append]
  exact foldl_getD_lt hs _ i (by rw [foldl_length]; exact hi)

lemma gateAt_append_left (gs hs : List Gate) (o : ℕ) (j : ℕ) (hj : j < gs.length) :
    gateAt (⟨gs ++ hs, o⟩ : Circuit) j = gateAt (⟨gs, o⟩ : Circuit) j := by
  simp only [gateAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

def step2 (m n : ℕ) (D : Circuit) (u v : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨GateOp.and, [u, n + v]⟩, ⟨GateOp.or, [D.output, m + D.gates.length]⟩],
    m + D.gates.length + 1⟩

lemma step2_len (m n : ℕ) (D : Circuit) (u v : ℕ) :
    (step2 m n D u v).gates.length = D.gates.length + 2 := by
  simp [step2]

lemma step2_eval (m n : ℕ) (D : Circuit) (u v : ℕ) (z : List Bool) (hz : z.length = m)
    (ho : D.output < m + D.gates.length) (hu : u < m) (hv : n + v < m) :
    (step2 m n D u v).eval z = (D.eval z || (z.getD u false && z.getD (n + v) false)) := by
  have hj1 : D.gates.length + 1 < (step2 m n D u v).gates.length := by rw [step2_len]; omega
  have hj0 : D.gates.length < (step2 m n D u v).gates.length := by rw [step2_len]; omega
  have g1 : gateAt (step2 m n D u v) (D.gates.length + 1) =
      ⟨GateOp.or, [D.output, m + D.gates.length]⟩ := by
    simp [gateAt, step2, List.getD_eq_getElem?_getD]
  have g0 : gateAt (step2 m n D u v) D.gates.length = ⟨GateOp.and, [u, n + v]⟩ := by
    simp [gateAt, step2, List.getD_eq_getElem?_getD]
  have v1 := val_gate (C := step2 m n D u v) hz hj1
  have v0 := val_gate (C := step2 m n D u v) hz hj0
  rw [g1] at v1
  rw [g0] at v0
  have eo : val (step2 m n D u v) z D.output = val D z D.output := by
    have := val_append D.gates [⟨GateOp.and, [u, n + v]⟩, ⟨GateOp.or, [D.output, m + D.gates.length]⟩]
      D.output (m + D.gates.length + 1) z D.output (by omega)
    exact this
  have eu : val (step2 m n D u v) z u = z.getD u false := val_input hz hu
  have ev : val (step2 m n D u v) z (n + v) = z.getD (n + v) false := val_input hz hv
  rw [eval_eq_val, eval_eq_val]
  change val (step2 m n D u v) z (m + D.gates.length + 1) = _
  rw [show m + D.gates.length + 1 = m + (D.gates.length + 1) by omega, v1]
  simp only [List.map_cons, List.map_nil, GateOp.eval]
  rw [if_pos (by omega), if_pos (by omega), eo, v0]
  simp only [List.map_cons, List.map_nil, GateOp.eval]
  rw [if_pos (by omega), if_pos (by omega), eu, ev]
  simp

lemma step2_AO2 (m n : ℕ) (D : Circuit) (u v : ℕ) (hA : PEqualNP.TopForm.IsAO2 m D)
    (ho : D.output < m + D.gates.length) (hu : u < m) (hv : n + v < m) :
    PEqualNP.TopForm.IsAO2 m (step2 m n D u v) := by
  obtain ⟨hAO, hRB, h2⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [step2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hAO g hg
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro j hj i hi
    rw [step2_len] at hj
    by_cases hjl : j < D.gates.length
    · have e : gateAt (step2 m n D u v) j = gateAt D j := gateAt_append_left _ _ _ j hjl
      rw [e] at hi
      have := hRB j hjl i hi
      omega
    · by_cases hje : j = D.gates.length
      · subst hje
        have g0 : gateAt (step2 m n D u v) D.gates.length = ⟨GateOp.and, [u, n + v]⟩ := by
          simp [gateAt, step2, List.getD_eq_getElem?_getD]
        rw [g0] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · have hje1 : j = D.gates.length + 1 := by omega
        subst hje1
        have g1 : gateAt (step2 m n D u v) (D.gates.length + 1) =
            ⟨GateOp.or, [D.output, m + D.gates.length]⟩ := by
          simp [gateAt, step2, List.getD_eq_getElem?_getD]
        rw [g1] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [step2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact h2 g hg
    · rfl
    · rfl

def extend (m n : ℕ) : List (ℕ × ℕ) → Circuit → Circuit
  | [], D => D
  | uv :: L, D => extend m n L (step2 m n D uv.1 uv.2)

lemma extend_spec (m n : ℕ) (hmn : n + n = m) :
    ∀ (L : List (ℕ × ℕ)) (D : Circuit), (∀ uv ∈ L, uv.1 < n ∧ uv.2 < n) →
      PEqualNP.TopForm.IsAO2 m D → D.output < m + D.gates.length →
      PEqualNP.TopForm.IsAO2 m (extend m n L D) ∧
        (extend m n L D).gates.length = D.gates.length + 2 * L.length ∧
        ∀ z : List Bool, z.length = m → (extend m n L D).eval z =
          (D.eval z || L.any (fun uv => z.getD uv.1 false && z.getD (n + uv.2) false)) := by
  intro L
  induction L with
  | nil =>
    intro D _ hA _
    refine ⟨hA, by simp [extend], ?_⟩
    intro z _
    simp [extend]
  | cons uv L ih =>
    intro D hL hA ho
    have huv := hL uv (List.mem_cons_self ..)
    have hu : uv.1 < m := by omega
    have hv : n + uv.2 < m := by omega
    have hA' := step2_AO2 m n D uv.1 uv.2 hA ho hu hv
    have ho' : (step2 m n D uv.1 uv.2).output < m + (step2 m n D uv.1 uv.2).gates.length := by
      rw [step2_len]; simp only [step2]; omega
    obtain ⟨r1, r2, r3⟩ := ih (step2 m n D uv.1 uv.2)
      (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hA' ho'
    refine ⟨r1, ?_, ?_⟩
    · simp only [extend]
      rw [r2, step2_len]
      simp only [List.length_cons]
      ring
    · intro z hz
      simp only [extend]
      rw [r3 z hz, step2_eval m n D uv.1 uv.2 z hz ho hu hv]
      simp only [List.any_cons, Bool.or_assoc]

lemma getD_ofFn' {k : ℕ} (f : Fin k → Bool) (i : ℕ) (hi : i < k) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma main (a b : ℕ) (S : Finset (Fin a × Fin b)) (C : Circuit) (hne : S.Nonempty)
    (hA : PEqualNP.TopForm.IsAO2 (a + b) C)
    (hf : ∀ x : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C x =
      decide (∃ (p : Fin a) (l : Fin b), (p, l) ∈ S ∧ x (Fin.castAdd b p) = true ∧
        x (Fin.natAdd a l) = true))
    (T : Finset (Fin (a + b) × Fin (a + b))) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (a + b + (a + b)) D ∧
      D.size ≤ C.size + 2 * T.card ∧
      ∀ z : Fin (a + b + (a + b)) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b + (a + b)) D z =
        decide (∃ (u v : Fin (a + b)), (u, v) ∈ Finset.image (fun (q : Fin a × Fin b) =>
          (Fin.castAdd b q.1, Fin.natAdd a q.2)) S ∪ T ∧
          z (Fin.castAdd (a + b) u) = true ∧ z (Fin.natAdd (a + b) v) = true) := by
  have han : a ≤ a + b := by omega
  have hRB := hA.2.1
  have hout : C.output < (a + b) + C.gates.length := by
    by_contra hcon
    obtain ⟨⟨p, l⟩, hpl⟩ := hne
    have h1 := hf (fun i => decide (i = Fin.castAdd b p ∨ i = Fin.natAdd a l))
    unfold PEqualNP.MetaComplexity.circuitFun at h1
    rw [eval_eq_val, val_ge (n := a + b) (by simp) (by omega)] at h1
    have h2 : decide (∃ (p' : Fin a) (l' : Fin b), (p', l') ∈ S ∧
        decide (Fin.castAdd b p' = Fin.castAdd b p ∨ Fin.castAdd b p' = Fin.natAdd a l) = true ∧
        decide (Fin.natAdd a l' = Fin.castAdd b p ∨ Fin.natAdd a l' = Fin.natAdd a l) = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨p, l, hpl, Or.inl rfl, Or.inr rfl⟩
    rw [← h1] at h2
    exact Bool.false_ne_true h2
  let L : List (ℕ × ℕ) := T.toList.map (fun q => (q.1.val, q.2.val))
  have hL : ∀ uv ∈ L, uv.1 < (a + b) ∧ uv.2 < (a + b) := by
    intro uv huv
    simp only [L, List.mem_map] at huv
    obtain ⟨q, _, rfl⟩ := huv
    exact ⟨q.1.isLt, q.2.isLt⟩
  have hA0 := mapC_AO2 a (a + b) han C hA
  have ho0 : (mapC a (a + b) C).output < (a + b) + (a + b) + (mapC a (a + b) C).gates.length := by
    simp only [mapC, List.length_map, mw]
    split_ifs <;> omega
  obtain ⟨r1, r2, r3⟩ := extend_spec ((a + b) + (a + b)) (a + b) rfl L (mapC a (a + b) C) hL hA0 ho0
  refine ⟨extend ((a + b) + (a + b)) (a + b) L (mapC a (a + b) C), r1, ?_, ?_⟩
  · unfold Circuit.size
    rw [r2]
    simp [L, mapC]
  · intro z
    unfold PEqualNP.MetaComplexity.circuitFun
    have hz : (List.ofFn z).length = (a + b) + (a + b) := by simp
    rw [r3 _ hz]
    let x : Fin (a + b) → Bool := fun i => (List.ofFn z).getD (mw a (a + b) i.val) false
    have hx : (List.ofFn x).length = (a + b) := by simp
    have hxz : ∀ i < (a + b), (List.ofFn x).getD i false = (List.ofFn z).getD (mw a (a + b) i) false := by
      intro i hi
      rw [getD_ofFn' x i hi]
    have hm : (mapC a (a + b) C).eval (List.ofFn z) = C.eval (List.ofFn x) := by
      rw [eval_eq_val, eval_eq_val]
      exact mapC_val a (a + b) han C hRB _ hz _ hx hxz C.output hout
    have hfx := hf x
    unfold PEqualNP.MetaComplexity.circuitFun at hfx
    rw [hm, hfx]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
      Finset.mem_union, Finset.mem_image, L, List.mem_map, Finset.mem_toList]
    have ep : ∀ p : Fin a, x (Fin.castAdd b p) = z (Fin.castAdd (a + b) (Fin.castAdd b p)) := by
      intro p
      simp only [x]
      have hp : mw a (a + b) (Fin.castAdd b p).val = p.val := by simp [mw]
      rw [hp, getD_ofFn' z p.val (by omega)]
      rfl
    have el : ∀ l : Fin b, x (Fin.natAdd a l) = z (Fin.natAdd (a + b) (Fin.natAdd a l)) := by
      intro l
      simp only [x]
      have hl : mw a (a + b) (Fin.natAdd a l).val = (a + b) + (a + l.val) := by simp [mw]
      rw [hl, getD_ofFn' z _ (by omega)]
      rfl
    have eu : ∀ u : Fin (a + b), (List.ofFn z).getD u.val false = z (Fin.castAdd (a + b) u) := by
      intro u
      rw [getD_ofFn' z u.val (by omega)]
      rfl
    have ev : ∀ v : Fin (a + b), (List.ofFn z).getD ((a + b) + v.val) false = z (Fin.natAdd (a + b) v) := by
      intro v
      rw [getD_ofFn' z _ (by omega)]
      rfl
    constructor
    · rintro (⟨p, l, hpl, h1, h2⟩ | ⟨uv, ⟨q, hq, rfl⟩, h1, h2⟩)
      · refine ⟨Fin.castAdd b p, Fin.natAdd a l, Or.inl ⟨(p, l), hpl, rfl⟩, ?_, ?_⟩
        · rw [← ep]; exact h1
        · rw [← el]; exact h2
      · refine ⟨q.1, q.2, Or.inr hq, ?_, ?_⟩
        · rw [← eu]; exact h1
        · rw [← ev]; exact h2
    · rintro ⟨u, v, (⟨q, hq, he⟩ | hT), h1, h2⟩
      · left
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨q.1, q.2, hq, by rw [ep]; exact h1, by rw [el]; exact h2⟩
      · right
        exact ⟨(u.val, v.val), ⟨(u, v), hT, rfl⟩, by rw [eu]; exact h1, by rw [ev]; exact h2⟩

end PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro a b S C hne hA hf n img T
  exact PEqualNP.Outside.L_meta_3264.main a b S C hne hA hf T
