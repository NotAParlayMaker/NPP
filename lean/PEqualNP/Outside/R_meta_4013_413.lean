import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4013_413
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (15 : ℕ) →
      ∃ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x) ≠
        (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) ||
         x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) ||
         x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) ||
         x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
         x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
         x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (11 : ℕ) →
      ∃ (x : Fin (8 : ℕ) → Bool), C.eval (List.ofFn x) ≠
        (x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ)) ||
         x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ)) || x (0 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ)) ||
         x (1 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
         x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
         x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))))
    (h3 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (18 : ℕ) →
      (16 : ℕ) + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (0 : ℕ)) ≤ C.size →
      (16 : ℕ) + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains (2 : ℕ)) ≤ C.size →
      (∀ v : Fin (10 : ℕ), (15 : ℕ) + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains v.val) ≤ C.size) →
      (12 : ℕ) + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).any (fun w => w == (0 : ℕ) || w == (2 : ℕ) || w == (10 : ℕ))) ≤ C.size →
      ∃ (x : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x ++ [x (0 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ))]) ≠
        (List.finRange (5 : ℕ)).any (fun i =>
          x (Fin.castAdd (5 : ℕ) i) && x (Fin.castAdd (5 : ℕ) (i + (1 : Fin (5 : ℕ)))) ||
          x (Fin.castAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) i) ||
          x (Fin.natAdd (5 : ℕ) i) && x (Fin.natAdd (5 : ℕ) (i + (2 : Fin (5 : ℕ)))))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → Function.Surjective x2 → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C0 pi hfan0 hsz0 _
  refine Classical.byContradiction fun hno => ?_
  let f10 : (Fin 10 → Bool) → Bool := fun x7 =>
    x7 0 && x7 1 || x7 1 && x7 2 || x7 2 && x7 3 || x7 3 && x7 4 || x7 4 && x7 0 ||
    x7 0 && x7 5 || x7 1 && x7 6 || x7 2 && x7 7 || x7 3 && x7 8 || x7 4 && x7 9 ||
    x7 5 && x7 7 || x7 7 && x7 9 || x7 9 && x7 6 || x7 6 && x7 8 || x7 8 && x7 5
  let fP9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let fH : (Fin 8 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  have hagree0 : ∀ x : Fin 10 → Bool,
      C0.eval (List.ofFn (x ∘ pi) ++ [x 0 || x 2]) = f10 x :=
    fun x => Classical.byContradiction fun hne => hno ⟨x, hne⟩
  let G5 : (Fin 10 → Bool) → Bool := fun x =>
    (List.finRange 5).any fun i =>
      x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
      x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
      x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))
  have hG5_eq : ∀ x : Fin 10 → Bool, G5 x = f10 x := by
    intro x
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) = f10 x
    simp only [Bool.or_false]
    dsimp [f10]
    ac_rfl
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have heval_run : ∀ (D : Circuit) (w : List Bool), D.eval w = (run D.gates w).getD D.output false :=
    fun _ _ => rfl
  have hsz_len : ∀ D : Circuit, D.size = D.gates.length := fun _ => rfl
  have hstep_len : ∀ (w : List Bool) (g : Gate), (step w g).length = w.length + 1 := by
    intro w g
    simp only [step, List.length_append, List.length_singleton]
  have hrun_cons : ∀ (g : Gate) (gs : List Gate) (w : List Bool), run (g :: gs) w = run gs (step w g) :=
    fun _ _ _ => rfl
  have hrun_append : ∀ (gs hs : List Gate) (w : List Bool), run (gs ++ hs) w = run hs (run gs w) :=
    fun gs hs w => List.foldl_append
  have hrun_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      rw [hrun_cons, ih, hstep_len, List.length_cons]
      omega
  have hrun_preserves : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), m < w.length →
      (run gs w).getD m false = w.getD m false := by
    intro gs
    induction gs with
    | nil => intro w m _; rfl
    | cons g gs ih =>
      intro w m hm
      rw [hrun_cons, ih _ _ (by rw [hstep_len]; omega)]
      exact List.getD_append _ _ _ _ hm
  have hgetD_append_len : ∀ {α : Type} (xs ys : List α) (d : α),
      (xs ++ ys).getD xs.length d = ys.getD 0 d := by
    intro α xs ys d
    rw [List.getD_append_right xs ys d xs.length (le_refl _), Nat.sub_self]
  let remap : ℕ → ℕ := fun i => if h : i < 10 then (pi ⟨i, h⟩).val else i
  let C : Circuit := ⟨C0.gates.map (fun g => ⟨g.op, g.inputs.map remap⟩), remap C0.output⟩
  have hfanC : FanInTwo C := by
    intro g hg
    rw [show C.gates = C0.gates.map (fun g => ⟨g.op, g.inputs.map remap⟩) from rfl, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    have hf0 := hfan0 g0 hg0
    exact ⟨hf0.1, by simp only [List.length_map]; exact hf0.2⟩
  have hszC : C.size ≤ 18 := by
    change (C0.gates.map (fun g : Gate => (⟨g.op, g.inputs.map remap⟩ : Gate))).length ≤ 18
    rw [List.length_map]
    exact hsz0
  have hgetFn10 : ∀ (x : Fin 10 → Bool) (ext : List Bool) (i : Fin 10),
      (List.ofFn x ++ ext).getD i.val false = x i := by
    intro x ext i
    have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hC_eval : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 2]) = C0.eval (List.ofFn (x ∘ pi) ++ [x 0 || x 2]) := by
    intro x
    let wA := List.ofFn x ++ [x 0 || x 2]
    let wB := List.ofFn (x ∘ pi) ++ [x 0 || x 2]
    have hlenA : wA.length = 11 := by
      simp only [wA, List.length_append, List.length_ofFn, List.length_singleton]
    have hlenB : wB.length = 11 := by
      simp only [wB, List.length_append, List.length_ofFn, List.length_singleton]
    have hinit_map : ∀ j, wB.getD j false = wA.getD (remap j) false := by
      intro j
      by_cases hj10 : j < 10
      · have hrm : remap j = (pi ⟨j, hj10⟩).val := by simp [remap, hj10]
        rw [hrm]
        have hjB : wB.getD j false = (x ∘ pi) ⟨j, hj10⟩ := hgetFn10 (x ∘ pi) _ ⟨j, hj10⟩
        have hjA : wA.getD (pi ⟨j, hj10⟩).val false = x (pi ⟨j, hj10⟩) := hgetFn10 x _ (pi ⟨j, hj10⟩)
        rw [hjB, hjA]
        rfl
      · by_cases hjeq : j = 10
        · subst hjeq
          have hrm : remap 10 = 10 := by simp [remap]
          rw [hrm]
          have h10A : wA.getD 10 false = (x 0 || x 2) := by
            dsimp [wA]
            rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn]
            rfl
          have h10B : wB.getD 10 false = (x 0 || x 2) := by
            dsimp [wB]
            rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn]
            rfl
          rw [h10A, h10B]
        · have hrm : remap j = j := by simp [remap, hj10]
          have hjb : wB.length ≤ j := by rw [hlenB]; omega
          have hja : wA.length ≤ j := by rw [hlenA]; omega
          rw [hrm, List.getD_eq_default wB false hjb, List.getD_eq_default wA false hja]
    have hremap_wire : ∀ (gs : List Gate) (u v : List Bool),
        u.length = v.length → 11 ≤ u.length →
        (∀ j, v.getD j false = u.getD (remap j) false) →
        ∀ m, (run gs v).getD m false = (run (gs.map (fun g => ⟨g.op, g.inputs.map remap⟩)) u).getD (remap m) false := by
      intro gs
      induction gs with
      | nil =>
        intro u v _ _ hmap m
        exact hmap m
      | cons g gs ih =>
        intro u v hlen hu hmap m
        let g' : Gate := ⟨g.op, g.inputs.map remap⟩
        have hstep_map : ∀ j, (step v g).getD j false = (step u g').getD (remap j) false := by
          intro j
          by_cases hj : j < v.length
          · have hrm_lt : remap j < u.length := by
              unfold remap
              split_ifs with hlt10
              · have := (pi ⟨j, hlt10⟩).isLt; omega
              · omega
            rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hrm_lt]
            exact hmap j
          · by_cases hjv : j = v.length
            · subst hjv
              have hrm : remap v.length = u.length := by
                unfold remap
                split_ifs with hlt10 <;> omega
              have hs1 : (step v g).getD v.length false = g.op.eval (g.inputs.map fun i => v.getD i false) :=
                hgetD_append_len v _ false
              have hs2 : (step u g').getD u.length false = g'.op.eval (g'.inputs.map fun i => u.getD i false) :=
                hgetD_append_len u _ false
              rw [hrm, hs1, hs2]
              change g.op.eval (g.inputs.map fun i => v.getD i false) =
                g.op.eval ((g.inputs.map remap).map fun i => u.getD i false)
              rw [List.map_map]
              have harg : (g.inputs.map fun i => v.getD i false) =
                  (g.inputs.map fun i => u.getD (remap i) false) := by
                apply List.map_congr_left
                intro i _
                exact hmap i
              rw [harg]
              rfl
            · have hrm_ge : (step u g').length ≤ remap j := by
                rw [hstep_len]
                unfold remap
                split_ifs with hlt10 <;> omega
              rw [List.getD_eq_default (step v g) false (by rw [hstep_len]; omega),
                List.getD_eq_default (step u g') false hrm_ge]
        exact ih (step u g') (step v g) (by rw [hstep_len, hstep_len, hlen]) (by rw [hstep_len]; omega) hstep_map m
    rw [heval_run, heval_run]
    exact (hremap_wire C0.gates wA wB (by omega) (by omega) hinit_map C0.output).symm
  have hagree : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) = G5 x := by
    intro x
    rw [hC_eval x, hagree0 x, ← hG5_eq x]
  let rot : Fin 5 → Fin 10 → Fin 10 := fun r k =>
    if k.val < 5 then Fin.ofNat 10 ((k.val + r.val) % 5)
    else Fin.ofNat 10 (5 + (k.val - 5 + r.val) % 5)
  let invRot : Fin 5 → Fin 5 := fun r => Fin.ofNat 5 ((5 - r.val) % 5)
  let tau : Fin 10 → Fin 10 := fun k =>
    if k.val < 5 then Fin.ofNat 10 (5 + (2 * k.val) % 5)
    else Fin.ofNat 10 ((2 * (k.val - 5)) % 5)
  let invTau : Fin 10 → Fin 10 := fun k =>
    if k.val < 5 then Fin.ofNat 10 (5 + (3 * k.val) % 5)
    else Fin.ofNat 10 ((3 * (k.val - 5)) % 5)
  let phiVal : ℕ → ℕ := fun k =>
    if k = 1 then 4 else if k = 4 then 1 else if k = 2 then 9 else
    if k = 9 then 2 else if k = 3 then 6 else if k = 6 then 3 else k
  let phi : Fin 10 → Fin 10 := fun k => Fin.ofNat 10 (phiVal k.val)
  let sigma : Fin 10 → Fin 10 → Fin 10 := fun v k =>
    if 5 ≤ v.val then rot (Fin.ofNat 5 (9 - v.val)) k
    else tau (rot (Fin.ofNat 5 ((7 - v.val) % 5)) k)
  let edgeList : List (Fin 10 × Fin 10) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
     (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  have hG5_edges : ∀ x : Fin 10 → Bool, G5 x = edgeList.any (fun e => x e.1 && x e.2) := by
    intro x
    rw [hG5_eq]
    dsimp [f10, edgeList]
    simp only [Bool.or_false, Bool.or_assoc]
  have hedge_pres : ∀ (f g : Fin 10 → Fin 10),
      (edgeList.all (fun e => edgeList.any (fun e' => (f e.1 == e'.1 && f e.2 == e'.2) || (f e.1 == e'.2 && f e.2 == e'.1)))) = true →
      (edgeList.all (fun e => edgeList.any (fun e' => (g e.1 == e'.1 && g e.2 == e'.2) || (g e.1 == e'.2 && g e.2 == e'.1)))) = true →
      (∀ k : Fin 10, f (g k) = k) →
      ∀ x : Fin 10 → Bool, G5 (x ∘ f) = G5 x := by
    intro f g hf hg hfg x
    rw [hG5_edges, hG5_edges]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [List.any_eq_true] at h ⊢
      rcases h with ⟨e, he, hev⟩
      rw [List.all_eq_true] at hf
      have he1 := hf e he
      rw [List.any_eq_true] at he1
      rcases he1 with ⟨e', he', heq⟩
      refine ⟨e', he', ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ hev.1, h2 ▸ hev.2⟩
      · exact ⟨h2 ▸ hev.2, h1 ▸ hev.1⟩
    · intro h
      rw [List.any_eq_true] at h ⊢
      rcases h with ⟨e', he', hev⟩
      rw [List.all_eq_true] at hg
      have he1 := hg e' he'
      rw [List.any_eq_true] at he1
      rcases he1 with ⟨e, he, heq⟩
      refine ⟨e, he, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by change x (f e.1) = true; rw [← h1, hfg e'.1]; exact hev.1,
               by change x (f e.2) = true; rw [← h2, hfg e'.2]; exact hev.2⟩
      · exact ⟨by change x (f e.1) = true; rw [← h2, hfg e'.2]; exact hev.2,
               by change x (f e.2) = true; rw [← h1, hfg e'.1]; exact hev.1⟩
  have hrot_pres : ∀ r : Fin 5,
      (edgeList.all (fun e => edgeList.any (fun e' => (rot r e.1 == e'.1 && rot r e.2 == e'.2) || (rot r e.1 == e'.2 && rot r e.2 == e'.1)))) = true := by
    dsimp only [rot, edgeList]
    decide
  have hrot_inv : ∀ (r : Fin 5) (k : Fin 10), rot r (rot (invRot r) k) = k := by
    dsimp only [rot, invRot]
    decide
  have hG5_rot : ∀ (r : Fin 5) (x : Fin 10 → Bool), G5 (x ∘ rot r) = G5 x :=
    fun r x => hedge_pres (rot r) (rot (invRot r)) (hrot_pres r) (hrot_pres (invRot r)) (hrot_inv r) x
  have htau_pres : (edgeList.all (fun e => edgeList.any (fun e' => (tau e.1 == e'.1 && tau e.2 == e'.2) || (tau e.1 == e'.2 && tau e.2 == e'.1)))) = true := by
    dsimp only [tau, edgeList]
    decide
  have hinvTau_pres : (edgeList.all (fun e => edgeList.any (fun e' => (invTau e.1 == e'.1 && invTau e.2 == e'.2) || (invTau e.1 == e'.2 && invTau e.2 == e'.1)))) = true := by
    dsimp only [invTau, edgeList]
    decide
  have htau_inv : ∀ k : Fin 10, tau (invTau k) = k := by
    dsimp only [tau, invTau]
    decide
  have hG5_tau : ∀ x : Fin 10 → Bool, G5 (x ∘ tau) = G5 x :=
    fun x => hedge_pres tau invTau htau_pres hinvTau_pres htau_inv x
  have hphi_pres : (edgeList.all (fun e => edgeList.any (fun e' => (phi e.1 == e'.1 && phi e.2 == e'.2) || (phi e.1 == e'.2 && phi e.2 == e'.1)))) = true := by
    dsimp only [phi, phiVal, edgeList]
    decide
  have hphi_inv : ∀ k : Fin 10, phi (phi k) = k := by
    dsimp only [phi, phiVal]
    decide
  have hG5_phi : ∀ x : Fin 10 → Bool, G5 (x ∘ phi) = G5 x :=
    fun x => hedge_pres phi phi hphi_pres hphi_pres hphi_inv x
  have hG5_sigma : ∀ (v : Fin 10) (x : Fin 10 → Bool), G5 (x ∘ sigma v) = G5 x := by
    intro v x
    by_cases hv : 5 ≤ v.val
    · have hsv : sigma v = rot (Fin.ofNat 5 (9 - v.val)) := by funext k; simp [sigma, hv]
      rw [hsv]
      exact hG5_rot _ x
    · have hsv : sigma v = tau ∘ rot (Fin.ofNat 5 ((7 - v.val) % 5)) := by
        funext k; simp [sigma, hv]
      rw [hsv]
      change G5 ((x ∘ tau) ∘ rot _) = G5 x
      rw [hG5_rot, hG5_tau]
  have hsigma_self : ∀ v : Fin 10, sigma v v = 9 := by
    dsimp only [sigma, rot, tau]
    decide
  have hsigma_lt : ∀ v k : Fin 10, k ≠ v → (sigma v k).val < 9 := by
    dsimp only [sigma, rot, tau]
    decide
  have hphi_0 : phi 0 = 0 := rfl
  have hphi_2 : phi 2 = 9 := rfl
  have hphi_lt9 : ∀ k : Fin 10, k ≠ 2 → (phi k).val < 9 := by
    dsimp only [phi, phiVal]
    decide
  have hphi_mid : ∀ k : Fin 10, k ≠ 0 → k ≠ 2 → 1 ≤ (phi k).val ∧ (phi k).val ≤ 8 := by
    dsimp only [phi, phiVal]
    decide
  have hG5_P9 : ∀ y : Fin 9 → Bool, G5 (Fin.lastCases false y) = fP9 y := by
    intro y
    rw [hG5_eq]
    dsimp [f10, fP9]
    have hl0 : Fin.lastCases false y (0 : Fin 10) = y 0 := Fin.lastCases_castSucc (0 : Fin 9)
    have hl1 : Fin.lastCases false y (1 : Fin 10) = y 1 := Fin.lastCases_castSucc (1 : Fin 9)
    have hl2 : Fin.lastCases false y (2 : Fin 10) = y 2 := Fin.lastCases_castSucc (2 : Fin 9)
    have hl3 : Fin.lastCases false y (3 : Fin 10) = y 3 := Fin.lastCases_castSucc (3 : Fin 9)
    have hl4 : Fin.lastCases false y (4 : Fin 10) = y 4 := Fin.lastCases_castSucc (4 : Fin 9)
    have hl5 : Fin.lastCases false y (5 : Fin 10) = y 5 := Fin.lastCases_castSucc (5 : Fin 9)
    have hl6 : Fin.lastCases false y (6 : Fin 10) = y 6 := Fin.lastCases_castSucc (6 : Fin 9)
    have hl7 : Fin.lastCases false y (7 : Fin 10) = y 7 := Fin.lastCases_castSucc (7 : Fin 9)
    have hl8 : Fin.lastCases false y (8 : Fin 10) = y 8 := Fin.lastCases_castSucc (8 : Fin 9)
    have hl9 : Fin.lastCases false y (9 : Fin 10) = false := Fin.lastCases_last
    rw [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9]
    simp only [Bool.and_false, Bool.false_and, Bool.or_false]
  have hlast_lt : ∀ (y : Fin 9 → Bool) (a : Fin 10) (ha : a.val < 9),
      Fin.lastCases false y a = y ⟨a.val, ha⟩ := fun y a ha =>
    (congrArg (Fin.lastCases false y) (Fin.ext rfl : a = (⟨a.val, ha⟩ : Fin 9).castSucc)).trans
      (Fin.lastCases_castSucc ⟨a.val, ha⟩)
  have hlast_9 : ∀ (y : Fin 9 → Bool) (a : Fin 10), a = 9 →
      Fin.lastCases false y a = false := fun y a ha =>
    (congrArg (Fin.lastCases false y) ha).trans Fin.lastCases_last
  let lift8 : (Fin 8 → Bool) → (Fin 10 → Bool) := fun y k =>
    if h : k.val = 0 ∨ k.val = 9 then false else y ⟨k.val - 1, by have := k.isLt; omega⟩
  have hG5_H8 : ∀ y : Fin 8 → Bool, G5 (lift8 y) = fH y := by
    intro y
    rw [hG5_eq]
    dsimp [f10, fH]
    have hl0 : lift8 y 0 = false := rfl
    have hl1 : lift8 y 1 = y 0 := rfl
    have hl2 : lift8 y 2 = y 1 := rfl
    have hl3 : lift8 y 3 = y 2 := rfl
    have hl4 : lift8 y 4 = y 3 := rfl
    have hl5 : lift8 y 5 = y 4 := rfl
    have hl6 : lift8 y 6 = y 5 := rfl
    have hl7 : lift8 y 7 = y 6 := rfl
    have hl8 : lift8 y 8 = y 7 := rfl
    have hl9 : lift8 y 9 = false := rfl
    rw [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9]
    simp only [Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
  let initW : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 2]
  have hinit_len : ∀ x, (initW x).length = 11 := by
    intro x
    change (List.ofFn x ++ [x 0 || x 2]).length = 11
    rw [List.length_append, List.length_ofFn]
    rfl
  have hinit_lt10 : ∀ (x : Fin 10 → Bool) (i : Fin 10), (initW x).getD i.val false = x i :=
    fun x i => hgetFn10 x _ i
  have hinit_10 : ∀ x : Fin 10 → Bool, (initW x).getD 10 false = (x 0 || x 2) := by
    intro x
    rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]), List.length_ofFn]
    rfl
  let effInputs (g : Gate) : List ℕ := cond (g.op.eval [false]) (g.inputs.take 1) g.inputs
  let evalVal : List Bool → Sum Bool ℕ → Bool := fun W v =>
    Sum.casesOn (motive := fun _ => Bool) v (fun b => b) (fun w => W.getD w false)
  let evalOne (nOut : ℕ) (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate) : Sum Bool ℕ × Option Gate :=
    GateOp.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.op
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl true, none) fun a t =>
        List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) t (env.getD a (Sum.inl false), none) fun b _ =>
          Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
            (fun ba => cond ba (env.getD b (Sum.inl false), none) (Sum.inl false, none))
            (fun wa => Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD b (Sum.inl false))
              (fun bb => cond bb (Sum.inr wa, none) (Sum.inl false, none))
              (fun wb => (Sum.inr (nOut + gs'.length), some ⟨GateOp.and, [wa, wb]⟩))))
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl false, none) fun a t =>
        List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) t (env.getD a (Sum.inl false), none) fun b _ =>
          Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
            (fun ba => cond ba (Sum.inl true, none) (env.getD b (Sum.inl false), none))
            (fun wa => Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD b (Sum.inl false))
              (fun bb => cond bb (Sum.inl true, none) (Sum.inr wa, none))
              (fun wb => (Sum.inr (nOut + gs'.length), some ⟨GateOp.or, [wa, wb]⟩))))
      (List.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) g.inputs (Sum.inl true, none) fun a _ =>
        Sum.casesOn (motive := fun _ => Sum Bool ℕ × Option Gate) (env.getD a (Sum.inl false))
          (fun b => (Sum.inl (!b), none))
          (fun wa => (Sum.inr (nOut + gs'.length), some ⟨GateOp.not, [wa]⟩)))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  let compileStep (nOut : ℕ) (st : List (Sum Bool ℕ) × List Gate) (g : Gate) : List (Sum Bool ℕ) × List Gate :=
    let r := evalOne nOut g st.1 st.2
    Option.casesOn (motive := fun _ => List (Sum Bool ℕ) × List Gate) r.2
      (st.1 ++ [r.1], st.2)
      (fun g' => (st.1 ++ [r.1], st.2 ++ [g']))
  let compileLoop (nOut : ℕ) : List Gate → List (Sum Bool ℕ) × List Gate → List (Sum Bool ℕ) × List Gate :=
    fun gs st => gs.foldl (compileStep nOut) st
  let fanOK : Gate → Prop := fun g =>
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
  have hcomp_step_props : ∀ (nOut : ℕ) (isZ : ℕ → Bool) (hisZ : ∀ w, isZ w = true → w < 11)
      (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate),
      fanOK g →
      11 ≤ env.length →
      (∀ w, isZ w = true → ∃ b, env.getD w (Sum.inl false) = Sum.inl b) →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      let st1 := compileStep nOut (env, gs') g
      (∃ ext1, st1.2 = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        ((effInputs g).any isZ = true → st1.2 = gs') ∧
        (∀ g' ∈ st1.2, fanOK g') ∧
        (∀ v ∈ st1.1, ∀ j, v = Sum.inr j → j < nOut + st1.2.length) ∧
        st1.1.length = env.length + 1 ∧
        (∀ w, isZ w = true → ∃ b, st1.1.getD w (Sum.inl false) = Sum.inl b) := by
    intro nOut isZ hisZ g env gs' hgfan hlen hZ hbound hfg
    cases g
    rename_i op ins
    let st1 := compileStep nOut (env, gs') ⟨op, ins⟩
    have hpres : ∀ m, m < env.length → st1.1.getD m (Sum.inl false) = env.getD m (Sum.inl false) := by
      intro m hm
      dsimp [st1, compileStep]
      cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> exact List.getD_append _ _ _ _ hm
    have hlen1 : st1.1.length = env.length + 1 := by
      dsimp [st1, compileStep]
      cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> simp
    have hZ' : ∀ w, isZ w = true → ∃ b, st1.1.getD w (Sum.inl false) = Sum.inl b := by
      intro w hw
      have hlt : w < env.length := by have := hisZ w hw; omega
      rw [hpres w hlt]
      exact hZ w hw
    have hnone_case : ∀ v_out : Sum Bool ℕ,
        (∀ j, v_out = Sum.inr j → j < nOut + gs'.length) →
        (∃ ext1, gs' = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        ((effInputs ⟨op, ins⟩).any isZ = true → gs' = gs') ∧
        (∀ g' ∈ gs', fanOK g') ∧
        (∀ v ∈ env ++ [v_out], ∀ j, v = Sum.inr j → j < nOut + gs'.length) := by
      intro v_out hv_bd
      refine ⟨⟨[], by simp⟩, fun _ => rfl, hfg, ?_⟩
      intro v hv j hj
      rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hbound v hv j hj
      · exact hv_bd j hj
    have hget_bound : ∀ a, ∀ j, env.getD a (Sum.inl false) = Sum.inr j → j < nOut + gs'.length := by
      intro a j ha
      by_cases hlt : a < env.length
      · rw [List.getD_eq_getElem _ _ hlt] at ha
        exact hbound _ (List.getElem_mem hlt) j ha
      · rw [List.getD_eq_default _ _ (by omega)] at ha
        cases ha
    have hcore :
        (∃ ext1, st1.2 = gs' ++ ext1 ∧ ext1.length ≤ 1) ∧
        ((effInputs ⟨op, ins⟩).any isZ = true → st1.2 = gs') ∧
        (∀ g' ∈ st1.2, fanOK g') ∧
        (∀ v ∈ st1.1, ∀ j, v = Sum.inr j → j < nOut + st1.2.length) := by
      rcases hgfan with ⟨hop, hilen⟩
      dsimp [st1, compileStep]
      rcases hop with rfl | rfl | rfl
      · -- and
        cases ins with
        | nil => exact hnone_case (Sum.inl true) (fun _ h => by cases h)
        | cons a t =>
          cases t with
          | nil => exact hnone_case (env.getD a (Sum.inl false)) (hget_bound a)
          | cons b r =>
            have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
            subst hr_nil
            have hrz_none : (effInputs ⟨GateOp.and, [a, b]⟩).any isZ = true →
                (evalOne nOut ⟨GateOp.and, [a, b]⟩ env gs').2 = none := by
              intro hrz
              change ([a, b].any isZ) = true at hrz
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hrz
              dsimp [evalOne]
              rcases hrz with ha | hb
              · obtain ⟨ba, hba⟩ := hZ a ha
                rw [hba]
                cases ba <;> cases env.getD b (Sum.inl false) with
                | inl bb => cases bb <;> rfl
                | inr _ => rfl
              · obtain ⟨bb, hbb⟩ := hZ b hb
                rw [hbb]
                cases env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> cases bb <;> rfl
                | inr _ => cases bb <;> rfl
            dsimp [evalOne]
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              cases ba
              · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
              · cases hgb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
                  · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
                | inr wb =>
                  exact hnone_case (Sum.inr wb) (fun j hj => by cases hj; exact hget_bound b wb hgb)
            | inr wa =>
              cases hgb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb
                · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
                · exact hnone_case (Sum.inr wa) (fun j hj => by cases hj; exact hget_bound a wa hga)
              | inr wb =>
                refine ⟨⟨[⟨GateOp.and, [wa, wb]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
                · intro hrz
                  have : ((Sum.inr (nOut + gs'.length) : Sum Bool ℕ), some (Gate.mk GateOp.and [wa, wb])).2 = none := by
                    have h' := hrz_none hrz
                    dsimp [evalOne] at h'
                    rw [hga, hgb] at h'
                    exact h'
                  cases this
                · intro g' hg'
                  rw [List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hfg g' hg'
                  · exact ⟨Or.inl rfl, by simp⟩
                · intro v hv j hj
                  rw [List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | rfl
                  · have := hbound v hv j hj
                    rw [List.length_append, List.length_singleton]
                    omega
                  · cases hj
                    rw [List.length_append, List.length_singleton]
                    omega
      · -- or
        cases ins with
        | nil => exact hnone_case (Sum.inl false) (fun _ h => by cases h)
        | cons a t =>
          cases t with
          | nil => exact hnone_case (env.getD a (Sum.inl false)) (hget_bound a)
          | cons b r =>
            have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
            subst hr_nil
            have hrz_none : (effInputs ⟨GateOp.or, [a, b]⟩).any isZ = true →
                (evalOne nOut ⟨GateOp.or, [a, b]⟩ env gs').2 = none := by
              intro hrz
              change ([a, b].any isZ) = true at hrz
              simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hrz
              dsimp [evalOne]
              rcases hrz with ha | hb
              · obtain ⟨ba, hba⟩ := hZ a ha
                rw [hba]
                cases ba <;> cases env.getD b (Sum.inl false) with
                | inl bb => cases bb <;> rfl
                | inr _ => rfl
              · obtain ⟨bb, hbb⟩ := hZ b hb
                rw [hbb]
                cases env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> cases bb <;> rfl
                | inr _ => cases bb <;> rfl
            dsimp [evalOne]
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              cases ba
              · cases hgb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · exact hnone_case (Sum.inl false) (fun _ h => by cases h)
                  · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
                | inr wb =>
                  exact hnone_case (Sum.inr wb) (fun j hj => by cases hj; exact hget_bound b wb hgb)
              · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
            | inr wa =>
              cases hgb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb
                · exact hnone_case (Sum.inr wa) (fun j hj => by cases hj; exact hget_bound a wa hga)
                · exact hnone_case (Sum.inl true) (fun _ h => by cases h)
              | inr wb =>
                refine ⟨⟨[⟨GateOp.or, [wa, wb]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
                · intro hrz
                  have : ((Sum.inr (nOut + gs'.length) : Sum Bool ℕ), some (Gate.mk GateOp.or [wa, wb])).2 = none := by
                    have h' := hrz_none hrz
                    dsimp [evalOne] at h'
                    rw [hga, hgb] at h'
                    exact h'
                  cases this
                · intro g' hg'
                  rw [List.mem_append, List.mem_singleton] at hg'
                  rcases hg' with hg' | rfl
                  · exact hfg g' hg'
                  · exact ⟨Or.inr (Or.inl rfl), by simp⟩
                · intro v hv j hj
                  rw [List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | rfl
                  · have := hbound v hv j hj
                    rw [List.length_append, List.length_singleton]
                    omega
                  · cases hj
                    rw [List.length_append, List.length_singleton]
                    omega
      · -- not
        cases ins with
        | nil => exact hnone_case (Sum.inl true) (fun _ h => by cases h)
        | cons a t =>
          have hrz_none : (effInputs ⟨GateOp.not, a :: t⟩).any isZ = true →
              (evalOne nOut ⟨GateOp.not, a :: t⟩ env gs').2 = none := by
            intro hrz
            change (([a]).any isZ) = true at hrz
            simp only [List.any_cons, List.any_nil, Bool.or_false] at hrz
            obtain ⟨ba, hba⟩ := hZ a hrz
            dsimp [evalOne]
            rw [hba]
          dsimp [evalOne]
          cases hga : env.getD a (Sum.inl false) with
          | inl ba =>
            exact hnone_case (Sum.inl (!ba)) (fun _ h => by cases h)
          | inr wa =>
            refine ⟨⟨[⟨GateOp.not, [wa]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
            · intro hrz
              have : ((Sum.inr (nOut + gs'.length) : Sum Bool ℕ), some (Gate.mk GateOp.not [wa])).2 = none := by
                have h' := hrz_none hrz
                dsimp [evalOne] at h'
                rw [hga] at h'
                exact h'
              cases this
            · intro g' hg'
              rw [List.mem_append, List.mem_singleton] at hg'
              rcases hg' with hg' | rfl
              · exact hfg g' hg'
              · exact ⟨Or.inr (Or.inr rfl), by simp⟩
            · intro v hv j hj
              rw [List.mem_append, List.mem_singleton] at hv
              rcases hv with hv | rfl
              · have := hbound v hv j hj
                rw [List.length_append, List.length_singleton]
                omega
              · cases hj
                rw [List.length_append, List.length_singleton]
                omega
    exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2, hlen1, hZ'⟩
  have hcomp_struct : ∀ (nOut : ℕ) (isZ : ℕ → Bool) (hisZ : ∀ w, isZ w = true → w < 11)
      (gs : List Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate),
      11 ≤ env.length →
      (∀ w, isZ w = true → ∃ b, env.getD w (Sum.inl false) = Sum.inl b) →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      (∀ g ∈ gs, fanOK g) →
      let res := compileLoop nOut gs (env, gs')
      (∃ ext, res.2 = gs' ++ ext) ∧
        (∀ g' ∈ res.2, fanOK g') ∧
        (∀ v ∈ res.1, ∀ j, v = Sum.inr j → j < nOut + res.2.length) ∧
        res.2.length + gs.countP (fun g => (effInputs g).any isZ) ≤ gs'.length + gs.length := by
    intro nOut isZ hisZ gs
    induction gs with
    | nil =>
      intro env gs' _ _ hbound hfg _
      refine ⟨⟨[], by dsimp [compileLoop]; simp⟩, hfg, hbound, ?_⟩
      change gs'.length + 0 ≤ gs'.length + 0
      exact le_refl _
    | cons g gs ih =>
      intro env gs' hlen hZ hbound hfg hgs
      have hgfan : fanOK g := hgs g List.mem_cons_self
      have hgs_tail : ∀ h ∈ gs, fanOK h := fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      obtain ⟨⟨ext1, hext1, hext1_len⟩, hrz1, hfg1, hbound1, hlen1, hZ'⟩ :=
        hcomp_step_props nOut isZ hisZ g env gs' hgfan hlen hZ hbound hfg
      obtain ⟨⟨ext2, hext2⟩, hfg2, hbound2, hcnt2⟩ :=
        ih (compileStep nOut (env, gs') g).1 (compileStep nOut (env, gs') g).2 (by omega) hZ' hbound1 hfg1 hgs_tail
      have hfold : compileLoop nOut (g :: gs) (env, gs') =
          compileLoop nOut gs ((compileStep nOut (env, gs') g).1, (compileStep nOut (env, gs') g).2) := rfl
      rw [hfold]
      refine ⟨⟨ext1 ++ ext2, by rw [hext2, hext1, List.append_assoc]⟩, hfg2, hbound2, ?_⟩
      rw [List.countP_cons, List.length_cons]
      by_cases hrzg : (effInputs g).any isZ = true
      · simp only [hrzg, ↓reduceIte]
        rw [hrz1 hrzg] at hcnt2 ⊢
        omega
      · simp only [hrzg, Bool.false_eq_true, ↓reduceIte]
        rw [hext1] at hcnt2 ⊢
        rw [List.length_append] at hcnt2
        omega
  have hcomp_step_sem : ∀ (nOut : ℕ) (y : Fin nOut → Bool) (g : Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate)
      (w WF : List Bool),
      fanOK g →
      env.length = w.length →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ k, k < nOut + (compileStep nOut (env, gs') g).2.length →
        WF.getD k false = (run (compileStep nOut (env, gs') g).2 (List.ofFn y)).getD k false) →
      (∀ m, evalVal WF (env.getD m (Sum.inl false)) = w.getD m false) →
      ∀ m, evalVal WF ((compileStep nOut (env, gs') g).1.getD m (Sum.inl false)) = (step w g).getD m false := by
    intro nOut y g env gs' w WF hgfan hlen hbound hWF hsem m
    cases g
    rename_i op ins
    let st1 := compileStep nOut (env, gs') ⟨op, ins⟩
    by_cases hm : m < w.length
    · have hm' : m < env.length := by omega
      have h1m : st1.1.getD m (Sum.inl false) = env.getD m (Sum.inl false) := by
        dsimp [st1, compileStep]
        cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> exact List.getD_append _ _ _ _ hm'
      rw [h1m, List.getD_append _ _ _ _ hm]
      exact hsem m
    · by_cases heq : m = w.length
      · subst heq
        have hw1 : (step w ⟨op, ins⟩).getD w.length false = op.eval (ins.map fun i => w.getD i false) :=
          hgetD_append_len w [op.eval (ins.map fun i => w.getD i false)] false
        have hs1 : st1.1.getD env.length (Sum.inl false) = (evalOne nOut ⟨op, ins⟩ env gs').1 := by
          dsimp [st1, compileStep]
          cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> exact hgetD_append_len env _ _
        change evalVal WF (st1.1.getD w.length (Sum.inl false)) = (step w ⟨op, ins⟩).getD w.length false
        rw [hw1, ← hlen, hs1]
        have hget_bound : ∀ a, ∀ j, env.getD a (Sum.inl false) = Sum.inr j → j < nOut + gs'.length := by
          intro a j ha
          by_cases hlt : a < env.length
          · rw [List.getD_eq_getElem _ _ hlt] at ha
            exact hbound _ (List.getElem_mem hlt) j ha
          · rw [List.getD_eq_default _ _ (by omega)] at ha
            cases ha
        rcases hgfan with ⟨hop, hilen⟩
        rcases hop with rfl | rfl | rfl
        · -- and
          cases ins with
          | nil => rfl
          | cons a t =>
            cases t with
            | nil =>
              dsimp [evalOne]
              rw [hsem a]
              change _ = GateOp.and.eval [w.getD a false]
              cases (w.getD a false) <;> rfl
            | cons b r =>
              have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
              subst hr_nil
              have hsa := hsem a
              have hsb := hsem b
              dsimp [evalOne]
              change _ = (w.getD a false && (w.getD b false && true))
              cases hga : env.getD a (Sum.inl false) <;> cases hgb : env.getD b (Sum.inl false) <;>
                rw [hga] at hsa <;> rw [hgb] at hsb
              · rename_i ba bb
                cases ba <;> cases bb <;> dsimp [evalVal] at hsa hsb ⊢ <;> rw [← hsa, ← hsb] <;> rfl
              · rename_i ba wb
                cases ba <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsa]; rfl
                · rw [← hsa, hsb]; cases (w.getD b false) <;> rfl
              · rename_i wa bb
                cases bb <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsb]; cases (w.getD a false) <;> rfl
                · rw [hsa, ← hsb]; cases (w.getD a false) <;> rfl
              · rename_i wa wb
                have hst1eq : (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2 = gs' ++ [⟨GateOp.and, [wa, wb]⟩] := by
                  dsimp [compileStep, evalOne]
                  rw [hga, hgb]
                have hlt1 : nOut + gs'.length < nOut + (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2.length := by
                  rw [hst1eq, List.length_append, List.length_singleton]; omega
                have hw0 := hWF (nOut + gs'.length) hlt1
                rw [hst1eq, hrun_append] at hw0
                have hlenrun : (run gs' (List.ofFn y)).length = nOut + gs'.length := by
                  rw [hrun_len, List.length_ofFn]
                have hw_eval : (run [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y))).getD (nOut + gs'.length) false =
                    ((run gs' (List.ofFn y)).getD wa false && ((run gs' (List.ofFn y)).getD wb false && true)) := by
                  rw [← hlenrun]
                  exact hgetD_append_len (run gs' (List.ofFn y)) _ false
                have hwa_bd := hget_bound a wa hga
                have hwb_bd := hget_bound b wb hgb
                have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                  have hwa1 : WF.getD wa false = (run (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2 (List.ofFn y)).getD wa false :=
                    hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwa1
                  have hp := hrun_preserves [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                  rw [hp] at hwa1
                  exact hwa1.symm
                have hwb_eq : (run gs' (List.ofFn y)).getD wb false = WF.getD wb false := by
                  have hwb1 : WF.getD wb false = (run (compileStep nOut (env, gs') ⟨GateOp.and, [a, b]⟩).2 (List.ofFn y)).getD wb false :=
                    hWF wb (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwb1
                  have hp := hrun_preserves [⟨GateOp.and, [wa, wb]⟩] (run gs' (List.ofFn y)) wb (by rw [hlenrun]; exact hwb_bd)
                  rw [hp] at hwb1
                  exact hwb1.symm
                dsimp [evalVal] at hsa hsb ⊢
                rw [hw0, hw_eval, hwa_eq, hwb_eq, hsa, hsb]
        · -- or
          cases ins with
          | nil => rfl
          | cons a t =>
            cases t with
            | nil =>
              dsimp [evalOne]
              rw [hsem a]
              change _ = GateOp.or.eval [w.getD a false]
              cases (w.getD a false) <;> rfl
            | cons b r =>
              have hr_nil : r = [] := by cases r with | nil => rfl | cons _ _ => simp at hilen
              subst hr_nil
              have hsa := hsem a
              have hsb := hsem b
              dsimp [evalOne]
              change _ = (w.getD a false || (w.getD b false || false))
              cases hga : env.getD a (Sum.inl false) <;> cases hgb : env.getD b (Sum.inl false) <;>
                rw [hga] at hsa <;> rw [hgb] at hsb
              · rename_i ba bb
                cases ba <;> cases bb <;> dsimp [evalVal] at hsa hsb ⊢ <;> rw [← hsa, ← hsb] <;> rfl
              · rename_i ba wb
                cases ba <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [← hsa, hsb]; cases (w.getD b false) <;> rfl
                · rw [← hsa]; rfl
              · rename_i wa bb
                cases bb <;> dsimp [evalVal, cond] at hsa hsb ⊢
                · rw [hsa, ← hsb]; cases (w.getD a false) <;> rfl
                · rw [← hsb]; cases (w.getD a false) <;> rfl
              · rename_i wa wb
                have hst1eq : (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2 = gs' ++ [⟨GateOp.or, [wa, wb]⟩] := by
                  dsimp [compileStep, evalOne]
                  rw [hga, hgb]
                have hlt1 : nOut + gs'.length < nOut + (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2.length := by
                  rw [hst1eq, List.length_append, List.length_singleton]; omega
                have hw0 := hWF (nOut + gs'.length) hlt1
                rw [hst1eq, hrun_append] at hw0
                have hlenrun : (run gs' (List.ofFn y)).length = nOut + gs'.length := by
                  rw [hrun_len, List.length_ofFn]
                have hw_eval : (run [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y))).getD (nOut + gs'.length) false =
                    ((run gs' (List.ofFn y)).getD wa false || ((run gs' (List.ofFn y)).getD wb false || false)) := by
                  rw [← hlenrun]
                  exact hgetD_append_len (run gs' (List.ofFn y)) _ false
                have hwa_bd := hget_bound a wa hga
                have hwb_bd := hget_bound b wb hgb
                have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                  have hwa1 : WF.getD wa false = (run (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2 (List.ofFn y)).getD wa false :=
                    hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwa1
                  have hp := hrun_preserves [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                  rw [hp] at hwa1
                  exact hwa1.symm
                have hwb_eq : (run gs' (List.ofFn y)).getD wb false = WF.getD wb false := by
                  have hwb1 : WF.getD wb false = (run (compileStep nOut (env, gs') ⟨GateOp.or, [a, b]⟩).2 (List.ofFn y)).getD wb false :=
                    hWF wb (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                  rw [hst1eq, hrun_append] at hwb1
                  have hp := hrun_preserves [⟨GateOp.or, [wa, wb]⟩] (run gs' (List.ofFn y)) wb (by rw [hlenrun]; exact hwb_bd)
                  rw [hp] at hwb1
                  exact hwb1.symm
                dsimp [evalVal] at hsa hsb ⊢
                rw [hw0, hw_eval, hwa_eq, hwb_eq, hsa, hsb]
        · -- not
          cases ins with
          | nil => rfl
          | cons a t =>
            have hsa := hsem a
            dsimp [evalOne]
            change _ = !(w.getD a false)
            cases hga : env.getD a (Sum.inl false) with
            | inl ba =>
              rw [hga] at hsa
              dsimp [evalVal] at hsa ⊢
              rw [hsa]
            | inr wa =>
              rw [hga] at hsa
              have hst1eq : (compileStep nOut (env, gs') ⟨GateOp.not, a :: t⟩).2 = gs' ++ [⟨GateOp.not, [wa]⟩] := by
                dsimp [compileStep, evalOne]
                rw [hga]
              have hlt1 : nOut + gs'.length < nOut + (compileStep nOut (env, gs') ⟨GateOp.not, a :: t⟩).2.length := by
                rw [hst1eq, List.length_append, List.length_singleton]; omega
              have hw0 := hWF (nOut + gs'.length) hlt1
              rw [hst1eq, hrun_append] at hw0
              have hlenrun : (run gs' (List.ofFn y)).length = nOut + gs'.length := by
                rw [hrun_len, List.length_ofFn]
              have hw_eval : (run [⟨GateOp.not, [wa]⟩] (run gs' (List.ofFn y))).getD (nOut + gs'.length) false =
                  !((run gs' (List.ofFn y)).getD wa false) := by
                rw [← hlenrun]
                exact hgetD_append_len (run gs' (List.ofFn y)) _ false
              have hwa_bd := hget_bound a wa hga
              have hwa_eq : (run gs' (List.ofFn y)).getD wa false = WF.getD wa false := by
                have hwa1 : WF.getD wa false = (run (compileStep nOut (env, gs') ⟨GateOp.not, a :: t⟩).2 (List.ofFn y)).getD wa false :=
                  hWF wa (by rw [hst1eq, List.length_append, List.length_singleton]; omega)
                rw [hst1eq, hrun_append] at hwa1
                have hp := hrun_preserves [⟨GateOp.not, [wa]⟩] (run gs' (List.ofFn y)) wa (by rw [hlenrun]; exact hwa_bd)
                rw [hp] at hwa1
                exact hwa1.symm
              dsimp [evalVal] at hsa ⊢
              rw [hw0, hw_eval, hwa_eq, hsa]
      · have hgt1 : st1.1.length ≤ m := by
          dsimp [st1, compileStep]
          cases (evalOne nOut ⟨op, ins⟩ env gs').2 <;> simp <;> omega
        have hgt2 : (step w ⟨op, ins⟩).length ≤ m := by
          rw [hstep_len]
          omega
        change evalVal WF (st1.1.getD m (Sum.inl false)) = (step w ⟨op, ins⟩).getD m false
        rw [List.getD_eq_default _ _ hgt1, List.getD_eq_default _ _ hgt2]
  have hcomp_sem : ∀ (nOut : ℕ) (isZ : ℕ → Bool) (hisZ : ∀ w, isZ w = true → w < 11)
      (y : Fin nOut → Bool) (gs : List Gate) (env : List (Sum Bool ℕ)) (gs' : List Gate) (w : List Bool),
      11 ≤ env.length →
      env.length = w.length →
      (∀ w', isZ w' = true → ∃ b, env.getD w' (Sum.inl false) = Sum.inl b) →
      (∀ v ∈ env, ∀ j, v = Sum.inr j → j < nOut + gs'.length) →
      (∀ g' ∈ gs', fanOK g') →
      (∀ g ∈ gs, fanOK g) →
      (∀ m, evalVal (run (compileLoop nOut gs (env, gs')).2 (List.ofFn y)) (env.getD m (Sum.inl false)) = w.getD m false) →
      ∀ m, evalVal (run (compileLoop nOut gs (env, gs')).2 (List.ofFn y)) ((compileLoop nOut gs (env, gs')).1.getD m (Sum.inl false)) =
        (run gs w).getD m false := by
    intro nOut isZ hisZ y gs
    induction gs with
    | nil =>
      intro env gs' w _ _ _ _ _ _ hsem m
      exact hsem m
    | cons g gs ih =>
      intro env gs' w hlen hwl hZ hbound hfg hgs hsem m
      have hgfan : fanOK g := hgs g List.mem_cons_self
      have hgs_tail : ∀ h ∈ gs, fanOK h := fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      obtain ⟨_, _, hfg1, hbound1, hlen1, hZ'⟩ :=
        hcomp_step_props nOut isZ hisZ g env gs' hgfan hlen hZ hbound hfg
      let st1 := compileStep nOut (env, gs') g
      have hstr_tail := hcomp_struct nOut isZ hisZ gs st1.1 st1.2 (by dsimp [st1]; omega) hZ' hbound1 hfg1 hgs_tail
      obtain ⟨ext2, hext2⟩ := hstr_tail.1
      have hfold : compileLoop nOut (g :: gs) (env, gs') = compileLoop nOut gs st1 := rfl
      rw [hfold]
      let WF := run (compileLoop nOut gs st1).2 (List.ofFn y)
      have hWF_pres : ∀ k, k < nOut + st1.2.length → WF.getD k false = (run st1.2 (List.ofFn y)).getD k false := by
        intro k hk
        change (run (compileLoop nOut gs st1).2 (List.ofFn y)).getD k false = _
        rw [hext2, hrun_append]
        exact hrun_preserves ext2 (run st1.2 (List.ofFn y)) k (by rw [hrun_len, List.length_ofFn]; exact hk)
      have hsem1 : ∀ k, evalVal WF (st1.1.getD k (Sum.inl false)) = (step w g).getD k false :=
        hcomp_step_sem nOut y g env gs' w WF hgfan hwl hbound hWF_pres hsem
      exact ih st1.1 st1.2 (step w g) (by change st1.1.length = env.length + 1 at hlen1; omega)
        (by rw [hstep_len, ← hwl]; exact hlen1)
        hZ' hbound1 hfg1 hgs_tail hsem1 m
  let mkEnv : (Fin 10 → Sum Bool ℕ) → Sum Bool ℕ → List (Sum Bool ℕ) := fun f e10 =>
    (List.finRange 10).map f ++ [e10]
  have hmkEnv_len : ∀ f e10, (mkEnv f e10).length = 11 := by
    intro f e10
    simp only [mkEnv, List.length_append, List.length_map, List.length_finRange, List.length_singleton]
  have hmkEnv_lt10 : ∀ f e10 (k : Fin 10), (mkEnv f e10).getD k.val (Sum.inl false) = f k := by
    intro f e10 k
    have hlt : k.val < ((List.finRange 10).map f).length := by simp
    rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_finRange]
    rfl
  have hmkEnv_10 : ∀ f e10, (mkEnv f e10).getD 10 (Sum.inl false) = e10 := by
    intro f e10
    have hlen : ((List.finRange 10).map f).length = 10 := by simp
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
    rfl
  have hmkEnv_bound : ∀ f e10 (b : ℕ),
      (∀ k : Fin 10, ∀ j, f k = Sum.inr j → j < b) →
      (∀ j, e10 = Sum.inr j → j < b) →
      ∀ v ∈ mkEnv f e10, ∀ j, v = Sum.inr j → j < b := by
    intro f e10 b hf he v hv j hj
    simp only [mkEnv, List.mem_append, List.mem_map, List.mem_finRange, List.mem_singleton] at hv
    rcases hv with ⟨k, _, rfl⟩ | rfl
    · exact hf k j hj
    · exact he j hj
  have compileLowerBound : ∀ (nOut bound : ℕ) (isZ : ℕ → Bool) (hisZ : ∀ w, isZ w = true → w < 11)
      (fT : (Fin nOut → Bool) → Bool) (y0 y1 : Fin nOut → Bool) (hne : fT y0 ≠ fT y1)
      (gs0 : List Gate) (hfg0 : ∀ g ∈ gs0, fanOK g)
      (env0 : List (Sum Bool ℕ)) (hlen0 : env0.length = 11)
      (hZ0 : ∀ w, isZ w = true → ∃ b, env0.getD w (Sum.inl false) = Sum.inl b)
      (hbnd0 : ∀ v ∈ env0, ∀ j, v = Sum.inr j → j < nOut + gs0.length)
      (liftIn : (Fin nOut → Bool) → (Fin 10 → Bool))
      (hG5_lift : ∀ y, G5 (liftIn y) = fT y)
      (hinit_lift : ∀ y (m : ℕ), m < 11 →
        evalVal (run gs0 (List.ofFn y)) (env0.getD m (Sum.inl false)) = (initW (liftIn y)).getD m false)
      (hlow : ∀ E : Circuit, FanInTwo E → E.size ≤ bound → ∃ y, E.eval (List.ofFn y) ≠ fT y),
      bound + 1 + C.gates.countP (fun g => (effInputs g).any isZ) ≤ gs0.length + C.size := by
    intro nOut bound isZ hisZ fT y0 y1 hne gs0 hfg0 env0 hlen0 hZ0 hbnd0 liftIn hG5_lift hinit_lift hlow
    let resC := compileLoop nOut C.gates (env0, gs0)
    have hCstr := hcomp_struct nOut isZ hisZ C.gates env0 gs0 (by omega) hZ0 hbnd0 hfg0 hfanC
    obtain ⟨ext, hext⟩ := hCstr.1
    have hsem0 : ∀ (y : Fin nOut → Bool) (m : ℕ),
        evalVal (run resC.2 (List.ofFn y)) (env0.getD m (Sum.inl false)) = (initW (liftIn y)).getD m false := by
      intro y m
      by_cases hm : m < 11
      · have hval : evalVal (run resC.2 (List.ofFn y)) (env0.getD m (Sum.inl false)) =
            evalVal (run gs0 (List.ofFn y)) (env0.getD m (Sum.inl false)) := by
          cases hvm : env0.getD m (Sum.inl false) with
          | inl b => rfl
          | inr j =>
            have hmem : Sum.inr j ∈ env0 := by
              rw [← hvm, List.getD_eq_getElem _ _ (by omega)]
              exact List.getElem_mem (by omega)
            have hj_lt := hbnd0 (Sum.inr j) hmem j rfl
            change (run resC.2 (List.ofFn y)).getD j false = (run gs0 (List.ofFn y)).getD j false
            rw [hext, hrun_append]
            exact hrun_preserves ext (run gs0 (List.ofFn y)) j (by rw [hrun_len, List.length_ofFn]; exact hj_lt)
        rw [hval, hinit_lift y m hm]
      · rw [List.getD_eq_default env0 (Sum.inl false) (by omega), List.getD_eq_default (initW (liftIn y)) false (by rw [hinit_len]; omega)]
    have hCsem : ∀ (y : Fin nOut → Bool) (m : ℕ),
        evalVal (run resC.2 (List.ofFn y)) (resC.1.getD m (Sum.inl false)) =
          (run C.gates (initW (liftIn y))).getD m false :=
      fun y => hcomp_sem nOut isZ hisZ y C.gates env0 gs0 (initW (liftIn y)) (by omega) (by rw [hinit_len]; omega)
        hZ0 hbnd0 hfg0 hfanC (hsem0 y)
    cases hout_val : resC.1.getD C.output (Sum.inl false) with
    | inl b =>
      have hconst : ∀ y : Fin nOut → Bool, fT y = b := by
        intro y
        have h1y := hCsem y C.output
        rw [hout_val] at h1y
        have h2y := hagree (liftIn y)
        rw [heval_run] at h2y
        change b = (run C.gates (initW (liftIn y))).getD C.output false at h1y
        rw [← hG5_lift y, ← h2y]
        exact h1y.symm
      exact False.elim (hne ((hconst y0).trans (hconst y1).symm))
    | inr outW =>
      let E : Circuit := ⟨resC.2, outW⟩
      have hfanE : FanInTwo E := hCstr.2.1
      have hge : bound + 1 ≤ resC.2.length := by
        refine Classical.byContradiction fun hlt => ?_
        have hle : E.size ≤ bound := by change resC.2.length ≤ bound; omega
        obtain ⟨y, hy⟩ := hlow E hfanE hle
        apply hy
        have h1y := hCsem y C.output
        rw [hout_val] at h1y
        have h2y := hagree (liftIn y)
        rw [heval_run] at h2y
        change (run resC.2 (List.ofFn y)).getD outW false = fT y
        exact h1y.trans (h2y.trans (hG5_lift y))
      have hcnt := hCstr.2.2.2
      change resC.2.length + C.gates.countP (fun g => (effInputs g).any isZ) ≤ gs0.length + C.gates.length at hcnt
      rw [hsz_len]
      omega
  have hcontains_eq : ∀ (w : ℕ),
      C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take (1 : ℕ)) g.inputs).contains w) =
      C.gates.countP (fun g => (effInputs g).any (fun x => x == w)) := by
    intro w
    apply List.countP_congr
    intro g _
    apply Bool.eq_iff_iff.mp
    change (effInputs g).contains w = (effInputs g).any (fun x => x == w)
    induction effInputs g with
    | nil => rfl
    | cons a l ih =>
      simp only [List.contains_cons, List.any_cons, ih]
      by_cases h : a = w
      · subst h; simp
      · have h1 : (a == w) = false := beq_false_of_ne h
        have h2 : (w == a) = false := beq_false_of_ne (Ne.symm h)
        simp [h1, h2]
  have hP9_ne : fP9 (fun _ => false) ≠ fP9 (fun j => decide (j = 0 ∨ j = 1)) := by decide
  have hH_ne : fH (fun _ => false) ≠ fH (fun j => decide (j = 0 ∨ j = 1)) := by decide
  have hgetFn9 : ∀ (y : Fin 9 → Bool) (ext : List Bool) (i : Fin 9),
      (List.ofFn y ++ ext).getD i.val false = y i := by
    intro y ext i
    have hi : i.val < (List.ofFn y).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  have hgetFn9_nil : ∀ (y : Fin 9 → Bool) (i : Fin 9), (List.ofFn y).getD i.val false = y i := fun y i => by
    simpa using hgetFn9 y [] i
  have hgetFn8 : ∀ (y : Fin 8 → Bool) (ext : List Bool) (i : Fin 8),
      (List.ofFn y ++ ext).getD i.val false = y i := by
    intro y ext i
    have hi : i.val < (List.ofFn y).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  -- Bound 1: 16 + d_0 ≤ C.size
  have hbd1 : 16 + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take 1) g.inputs).contains 0) ≤ C.size := by
    rw [hcontains_eq 0]
    let fenv : Fin 10 → Sum Bool ℕ := fun k =>
      if k = 0 then Sum.inl false else Sum.inr (sigma 0 k).val
    let env0 := mkEnv fenv (Sum.inr (sigma 0 2).val)
    have hbound1 := compileLowerBound 9 15 (fun x => x == 0)
      (fun w hw => by rw [beq_iff_eq] at hw; omega)
      fP9 (fun _ => false) (fun j => decide (j = 0 ∨ j = 1)) hP9_ne
      [] (fun _ h => by cases h) env0 (hmkEnv_len fenv _)
      (fun w hw => by
        rw [beq_iff_eq] at hw; subst hw
        refine ⟨false, ?_⟩
        rw [show (0 : ℕ) = (0 : Fin 10).val from rfl, hmkEnv_lt10 fenv _ 0]
        rfl)
      (hmkEnv_bound fenv _ (9 + ([] : List Gate).length)
        (fun k j hj => by
          dsimp [fenv] at hj
          split_ifs at hj with hk
          cases hj
          have := hsigma_lt 0 k hk
          simp only [List.length_nil, Nat.add_zero]
          exact this)
        (fun j hj => by cases hj; have := hsigma_lt 0 2 (by decide); simp; exact this))
      (fun y => (Fin.lastCases false y) ∘ sigma 0)
      (fun y => by change G5 (Fin.lastCases false y ∘ sigma 0) = fP9 y; rw [hG5_sigma, hG5_P9])
      (fun y m hm => by
        by_cases hm10 : m < 10
        · let k : Fin 10 := ⟨m, hm10⟩
          change evalVal (List.ofFn y) (env0.getD k.val (Sum.inl false)) = (initW ((Fin.lastCases false y) ∘ sigma 0)).getD k.val false
          rw [hmkEnv_lt10 fenv _ k, hinit_lt10]
          dsimp [fenv, evalVal]
          by_cases hk0 : k = 0
          · simp only [hk0, ↓reduceIte]
            change false = Fin.lastCases false y (sigma 0 0)
            exact (hlast_9 y (sigma 0 0) (hsigma_self 0)).symm
          · simp only [hk0, ↓reduceIte]
            have hlt9 : (sigma 0 k).val < 9 := hsigma_lt 0 k hk0
            have hk_eq : Fin.lastCases false y (sigma 0 k) = y ⟨(sigma 0 k).val, hlt9⟩ :=
              hlast_lt y (sigma 0 k) hlt9
            rw [hk_eq]
            exact hgetFn9 y [] ⟨(sigma 0 k).val, hlt9⟩
        · have hm_eq : m = 10 := by omega
          subst hm_eq
          change evalVal (List.ofFn y) (env0.getD 10 (Sum.inl false)) = (initW ((Fin.lastCases false y) ∘ sigma 0)).getD 10 false
          rw [hmkEnv_10, hinit_10]
          dsimp [evalVal]
          have h0f : Fin.lastCases false y (sigma 0 0) = false :=
            hlast_9 y (sigma 0 0) (hsigma_self 0)
          have hlt2 : (sigma 0 2).val < 9 := hsigma_lt 0 2 (by decide)
          have h2eq : Fin.lastCases false y (sigma 0 2) = y ⟨(sigma 0 2).val, hlt2⟩ :=
            hlast_lt y (sigma 0 2) hlt2
          change (List.ofFn y).getD (sigma 0 2).val false = (Fin.lastCases false y (sigma 0 0) || Fin.lastCases false y (sigma 0 2))
          rw [h0f, h2eq, Bool.false_or]
          exact hgetFn9 y [] ⟨(sigma 0 2).val, hlt2⟩)
      h1
    change 15 + 1 + _ ≤ 0 + C.size at hbound1
    omega
  -- Bound 2: 16 + d_2 ≤ C.size
  have hbd2 : 16 + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take 1) g.inputs).contains 2) ≤ C.size := by
    rw [hcontains_eq 2]
    let fenv : Fin 10 → Sum Bool ℕ := fun k =>
      if k = 2 then Sum.inl false else Sum.inr (phi k).val
    let env0 := mkEnv fenv (Sum.inr 0)
    have hbound2 := compileLowerBound 9 15 (fun x => x == 2)
      (fun w hw => by rw [beq_iff_eq] at hw; omega)
      fP9 (fun _ => false) (fun j => decide (j = 0 ∨ j = 1)) hP9_ne
      [] (fun _ h => by cases h) env0 (hmkEnv_len fenv _)
      (fun w hw => by
        rw [beq_iff_eq] at hw; subst hw
        refine ⟨false, ?_⟩
        rw [show (2 : ℕ) = (2 : Fin 10).val from rfl, hmkEnv_lt10 fenv _ 2]
        rfl)
      (hmkEnv_bound fenv _ (9 + ([] : List Gate).length)
        (fun k j hj => by
          dsimp [fenv] at hj
          split_ifs at hj with hk
          cases hj
          have := hphi_lt9 k hk
          simp only [List.length_nil, Nat.add_zero]
          exact this)
        (fun j hj => by cases hj; decide))
      (fun y => (Fin.lastCases false y) ∘ phi)
      (fun y => by change G5 (Fin.lastCases false y ∘ phi) = fP9 y; rw [hG5_phi, hG5_P9])
      (fun y m hm => by
        by_cases hm10 : m < 10
        · let k : Fin 10 := ⟨m, hm10⟩
          change evalVal (List.ofFn y) (env0.getD k.val (Sum.inl false)) = (initW ((Fin.lastCases false y) ∘ phi)).getD k.val false
          rw [hmkEnv_lt10 fenv _ k, hinit_lt10]
          dsimp [fenv, evalVal]
          by_cases hk2 : k = 2
          · simp only [hk2, ↓reduceIte]
            change false = Fin.lastCases false y (phi 2)
            exact (hlast_9 y (phi 2) hphi_2).symm
          · simp only [hk2, ↓reduceIte]
            have hlt9 : (phi k).val < 9 := hphi_lt9 k hk2
            have hk_eq : Fin.lastCases false y (phi k) = y ⟨(phi k).val, hlt9⟩ :=
              hlast_lt y (phi k) hlt9
            rw [hk_eq]
            exact hgetFn9 y [] ⟨(phi k).val, hlt9⟩
        · have hm_eq : m = 10 := by omega
          subst hm_eq
          change evalVal (List.ofFn y) (env0.getD 10 (Sum.inl false)) = (initW ((Fin.lastCases false y) ∘ phi)).getD 10 false
          rw [hmkEnv_10, hinit_10]
          dsimp [evalVal]
          have h0eq : Fin.lastCases false y (phi 0) = y 0 := by
            rw [hphi_0]
            exact Fin.lastCases_castSucc (0 : Fin 9)
          have h2f : Fin.lastCases false y (phi 2) = false :=
            hlast_9 y (phi 2) hphi_2
          change (List.ofFn y).getD 0 false = (Fin.lastCases false y (phi 0) || Fin.lastCases false y (phi 2))
          rw [h0eq, h2f, Bool.or_false]
          exact hgetFn9 y [] 0)
      h1
    change 15 + 1 + _ ≤ 0 + C.size at hbound2
    omega
  -- Bound 3: ∀ v : Fin 10, 15 + d_v ≤ C.size
  have hbd3 : ∀ v : Fin 10, 15 + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take 1) g.inputs).contains v.val) ≤ C.size := by
    intro v
    by_cases hv0 : v = 0
    · subst hv0
      have hv0val : (0 : Fin 10).val = 0 := rfl
      rw [hv0val]
      omega
    · by_cases hv2 : v = 2
      · subst hv2
        have hv2val : (2 : Fin 10).val = 2 := rfl
        rw [hv2val]
        omega
      · rw [hcontains_eq v.val]
        let gs0 : List Gate := [⟨GateOp.or, [(sigma v 0).val, (sigma v 2).val]⟩]
        let fenv : Fin 10 → Sum Bool ℕ := fun k =>
          if k = v then Sum.inl false else Sum.inr (sigma v k).val
        let env0 := mkEnv fenv (Sum.inr 9)
        have hgs0_fan : ∀ g ∈ gs0, fanOK g := by
          intro g hg
          rw [List.mem_singleton] at hg
          subst hg
          exact ⟨Or.inr (Or.inl rfl), by simp⟩
        have h0lt : (sigma v 0).val < 9 := hsigma_lt v 0 (fun h => hv0 h.symm)
        have h2lt : (sigma v 2).val < 9 := hsigma_lt v 2 (fun h => hv2 h.symm)
        have hbound3 := compileLowerBound 9 15 (fun x => x == v.val)
          (fun w hw => by rw [beq_iff_eq] at hw; have := v.isLt; omega)
          fP9 (fun _ => false) (fun j => decide (j = 0 ∨ j = 1)) hP9_ne
          gs0 hgs0_fan env0 (hmkEnv_len fenv _)
          (fun w hw => by
            rw [beq_iff_eq] at hw; subst hw
            refine ⟨false, ?_⟩
            rw [hmkEnv_lt10 fenv _ v]
            dsimp [fenv]
            simp)
          (hmkEnv_bound fenv _ (9 + gs0.length)
            (fun k j hj => by
              dsimp [fenv] at hj
              split_ifs at hj with hkv
              cases hj
              exact Nat.lt_succ_of_lt (hsigma_lt v k hkv))
            (fun j hj => by cases hj; simp [gs0]))
          (fun y => (Fin.lastCases false y) ∘ sigma v)
          (fun y => by change G5 (Fin.lastCases false y ∘ sigma v) = fP9 y; rw [hG5_sigma, hG5_P9])
          (fun y m hm => by
            by_cases hm10 : m < 10
            · let k : Fin 10 := ⟨m, hm10⟩
              change evalVal (run gs0 (List.ofFn y)) (env0.getD k.val (Sum.inl false)) =
                (initW ((Fin.lastCases false y) ∘ sigma v)).getD k.val false
              rw [hmkEnv_lt10 fenv _ k, hinit_lt10]
              dsimp [fenv, evalVal]
              by_cases hkv : k = v
              · simp only [hkv, ↓reduceIte]
                change false = Fin.lastCases false y (sigma v v)
                exact (hlast_9 y (sigma v v) (hsigma_self v)).symm
              · simp only [hkv, ↓reduceIte]
                have hlt9 : (sigma v k).val < 9 := hsigma_lt v k hkv
                have hk_eq : Fin.lastCases false y (sigma v k) = y ⟨(sigma v k).val, hlt9⟩ :=
                  hlast_lt y (sigma v k) hlt9
                rw [hk_eq, hrun_preserves gs0 (List.ofFn y) _ (by rw [List.length_ofFn]; exact hlt9)]
                exact hgetFn9 y [] ⟨(sigma v k).val, hlt9⟩
            · have hm_eq : m = 10 := by omega
              subst hm_eq
              change evalVal (run gs0 (List.ofFn y)) (env0.getD 10 (Sum.inl false)) =
                (initW ((Fin.lastCases false y) ∘ sigma v)).getD 10 false
              rw [hmkEnv_10, hinit_10]
              dsimp [evalVal]
              have hlen9 : (List.ofFn y).length = 9 := List.length_ofFn
              have hrun9 : (run gs0 (List.ofFn y)).getD 9 false =
                  GateOp.or.eval ([(sigma v 0).val, (sigma v 2).val].map fun i => (List.ofFn y).getD i false) := by
                have hst := hgetD_append_len (List.ofFn y)
                  [GateOp.or.eval ([(sigma v 0).val, (sigma v 2).val].map fun i => (List.ofFn y).getD i false)] false
                rw [hlen9] at hst
                exact hst
              have hor_val : GateOp.or.eval ([(sigma v 0).val, (sigma v 2).val].map fun i => (List.ofFn y).getD i false) =
                  (y ⟨(sigma v 0).val, h0lt⟩ || y ⟨(sigma v 2).val, h2lt⟩) := by
                rw [List.map_cons, List.map_cons, List.map_nil]
                change ([(List.ofFn y).getD (sigma v 0).val false, (List.ofFn y).getD (sigma v 2).val false].any id) = _
                rw [hgetFn9_nil y ⟨(sigma v 0).val, h0lt⟩, hgetFn9_nil y ⟨(sigma v 2).val, h2lt⟩]
                cases (y ⟨(sigma v 0).val, h0lt⟩) <;> cases (y ⟨(sigma v 2).val, h2lt⟩) <;> rfl
              have h0eq : Fin.lastCases false y (sigma v 0) = y ⟨(sigma v 0).val, h0lt⟩ :=
                hlast_lt y (sigma v 0) h0lt
              have h2eq : Fin.lastCases false y (sigma v 2) = y ⟨(sigma v 2).val, h2lt⟩ :=
                hlast_lt y (sigma v 2) h2lt
              change (run gs0 (List.ofFn y)).getD 9 false = (Fin.lastCases false y (sigma v 0) || Fin.lastCases false y (sigma v 2))
              rw [hrun9, hor_val, h0eq, h2eq])
          h1
        change 15 + 1 + _ ≤ gs0.length + C.size at hbound3
        have hgs0_len : gs0.length = 1 := rfl
        omega
  -- Bound 4: 12 + k_{0,2,10} ≤ C.size
  have hbd4 : 12 + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take 1) g.inputs).any (fun w => w == 0 || w == 2 || w == 10)) ≤ C.size := by
    let fenv : Fin 10 → Sum Bool ℕ := fun k =>
      if k = 0 ∨ k = 2 then Sum.inl false else Sum.inr ((phi k).val - 1)
    let env0 := mkEnv fenv (Sum.inl false)
    have hbound4 := compileLowerBound 8 11 (fun w => w == 0 || w == 2 || w == 10)
      (fun w hw => by
        simp only [Bool.or_eq_true, beq_iff_eq] at hw
        rcases hw with (rfl | rfl) | rfl <;> omega)
      fH (fun _ => false) (fun j => decide (j = 0 ∨ j = 1)) hH_ne
      [] (fun _ h => by cases h) env0 (hmkEnv_len fenv _)
      (fun w hw => by
        simp only [Bool.or_eq_true, beq_iff_eq] at hw
        rcases hw with (rfl | rfl) | rfl
        · refine ⟨false, ?_⟩
          rw [show (0 : ℕ) = (0 : Fin 10).val from rfl, hmkEnv_lt10 fenv _ 0]
          rfl
        · refine ⟨false, ?_⟩
          rw [show (2 : ℕ) = (2 : Fin 10).val from rfl, hmkEnv_lt10 fenv _ 2]
          rfl
        · refine ⟨false, ?_⟩
          rw [hmkEnv_10])
      (hmkEnv_bound fenv _ (8 + ([] : List Gate).length)
        (fun k j hj => by
          dsimp [fenv] at hj
          split_ifs at hj with hk
          cases hj
          have hk0 : k ≠ 0 := fun h => hk (Or.inl h)
          have hk2 : k ≠ 2 := fun h => hk (Or.inr h)
          have := (hphi_mid k hk0 hk2).2
          simp only [List.length_nil, Nat.add_zero]
          omega)
        (fun j hj => by cases hj))
      (fun y => lift8 y ∘ phi)
      (fun y => by change G5 (lift8 y ∘ phi) = fH y; rw [hG5_phi, hG5_H8])
      (fun y m hm => by
        by_cases hm10 : m < 10
        · let k : Fin 10 := ⟨m, hm10⟩
          change evalVal (List.ofFn y) (env0.getD k.val (Sum.inl false)) = (initW (lift8 y ∘ phi)).getD k.val false
          rw [hmkEnv_lt10 fenv _ k, hinit_lt10]
          dsimp [fenv, evalVal]
          by_cases hk02 : k = 0 ∨ k = 2
          · simp only [hk02, ↓reduceIte]
            rcases hk02 with hk0 | hk2
            · rw [hk0]; change false = lift8 y (phi 0); rw [hphi_0]; rfl
            · rw [hk2]; change false = lift8 y (phi 2); rw [hphi_2]; rfl
          · simp only [hk02, ↓reduceIte]
            have hk0 : k ≠ 0 := fun h => hk02 (Or.inl h)
            have hk2 : k ≠ 2 := fun h => hk02 (Or.inr h)
            have hmid := hphi_mid k hk0 hk2
            have hnot : ¬ ((phi k).val = 0 ∨ (phi k).val = 9) := by omega
            have hlift_eq : lift8 y (phi k) = y ⟨(phi k).val - 1, by omega⟩ := by
              dsimp [lift8]
              rw [dif_neg hnot]
            change (List.ofFn y).getD ((phi k).val - 1) false = lift8 y (phi k)
            rw [hlift_eq]
            exact hgetFn8 y [] ⟨(phi k).val - 1, by omega⟩
        · have hm_eq : m = 10 := by omega
          subst hm_eq
          change evalVal (List.ofFn y) (env0.getD 10 (Sum.inl false)) = (initW (lift8 y ∘ phi)).getD 10 false
          rw [hmkEnv_10, hinit_10]
          dsimp [evalVal]
          have h0f : lift8 y (phi 0) = false := by rw [hphi_0]; rfl
          have h2f : lift8 y (phi 2) = false := by rw [hphi_2]; rfl
          change false = (lift8 y (phi 0) || lift8 y (phi 2))
          rw [h0f, h2f]
          rfl)
      h2
    change 11 + 1 + C.gates.countP (fun g => (cond (g.op.eval [Bool.false]) (g.inputs.take 1) g.inputs).any (fun w => w == 0 || w == 2 || w == 10)) ≤ 0 + C.size at hbound4
    omega
  obtain ⟨x, hx⟩ := h3 C hfanC hszC hbd1 hbd2 hbd3 hbd4
  exact hx (hagree x)