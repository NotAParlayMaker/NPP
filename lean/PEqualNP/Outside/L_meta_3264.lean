import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    rw [hk]
    simp

theorem getD_ofFn {m : ℕ} (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem fold_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
    simp only [step]
    rw [getD_snoc, if_pos hi]

def mp (a n : ℕ) (i : ℕ) : ℕ := if i < a then i else n + i

def rl (a n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (mp a n)⟩

def Rel (a n : ℕ) (w' w : List Bool) : Prop :=
  w'.length = w.length + n ∧ n ≤ w.length ∧ a ≤ n ∧
    ∀ k, w'.getD (mp a n k) false = w.getD k false

theorem step_rel (a n : ℕ) (g : Gate) (w' w : List Bool) (h : Rel a n w' w) :
    Rel a n (step w' (rl a n g)) (step w g) := by
  obtain ⟨hl, hn, han, hk⟩ := h
  have hval : (rl a n g).op.eval ((rl a n g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [rl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hk i
  refine ⟨by simp [step, hl]; omega, by simp [step]; omega, han, fun k => ?_⟩
  simp only [step]
  rw [hval, getD_snoc, getD_snoc]
  have hkk := hk k
  by_cases hka : k < a
  · have e : mp a n k = k := by simp [mp, hka]
    rw [e] at hkk ⊢
    rw [if_pos (by omega), if_pos (by omega)]
    exact hkk
  · have e : mp a n k = n + k := by simp [mp, hka]
    rw [e] at hkk ⊢
    rw [hl]
    by_cases h1 : k < w.length
    · rw [if_pos (by omega), if_pos h1]
      exact hkk
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : k = w.length
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2]

theorem fold_rel (a n : ℕ) (gs : List Gate) : ∀ w' w : List Bool, Rel a n w' w →
    Rel a n ((gs.map (rl a n)).foldl step w') (gs.foldl step w) := by
  induction gs with
  | nil => intro w' w h; exact h
  | cons g gs ih =>
    intro w' w h
    exact ih _ _ (step_rel a n g w' w h)

theorem any_congr_mem {l : List (ℕ × ℕ)} {f g : ℕ × ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.any_cons]
    rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]

def extra (B c : ℕ) : List (ℕ × ℕ) → List Gate
  | [] => []
  | (u, v) :: L => ⟨GateOp.and, [u, v]⟩ :: ⟨GateOp.or, [c, B]⟩ :: extra (B + 2) (B + 1) L

def accIdx (B c : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => c
  | _ :: L => accIdx (B + 2) (B + 1) L

theorem extra_length (B c : ℕ) : ∀ L : List (ℕ × ℕ), (extra B c L).length = 2 * L.length
  | [] => rfl
  | (u, v) :: L => by
    simp only [extra, List.length_cons, extra_length (B + 2) (B + 1) L]
    ring

theorem extra_val : ∀ (L : List (ℕ × ℕ)) (B c : ℕ) (W : List Bool), W.length = B → c < B →
    (∀ p ∈ L, p.1 < B ∧ p.2 < B) →
    ((extra B c L).foldl step W).getD (accIdx B c L) false =
      (W.getD c false || L.any (fun p => W.getD p.1 false && W.getD p.2 false))
  | [], B, c, W, _, _, _ => by simp [extra, accIdx]
  | (u, v) :: L, B, c, W, hW, hc, hL => by
    have hu := (hL (u, v) (by simp)).1
    have hv := (hL (u, v) (by simp)).2
    simp only [extra, List.foldl_cons, accIdx]
    set x := (W.getD u false && W.getD v false) with hx
    have h1 : step W ⟨GateOp.and, [u, v]⟩ = W ++ [x] := by
      simp [step, GateOp.eval, hx]
    have h2 : step (W ++ [x]) ⟨GateOp.or, [c, B]⟩ = W ++ [x] ++ [W.getD c false || x] := by
      simp only [step, GateOp.eval, List.map_cons, List.map_nil]
      rw [getD_snoc, getD_snoc, if_pos (by omega), if_neg (by omega), if_pos hW.symm]
      simp
    rw [h1, h2]
    have hW2 : (W ++ [x] ++ [W.getD c false || x]).length = B + 2 := by simp [hW]
    have pre : ∀ i < B, (W ++ [x] ++ [W.getD c false || x]).getD i false = W.getD i false := by
      intro i hi
      rw [getD_snoc, if_pos (by simp; omega), getD_snoc, if_pos (by omega)]
    have last : (W ++ [x] ++ [W.getD c false || x]).getD (B + 1) false = (W.getD c false || x) := by
      rw [getD_snoc, if_neg (by simp; omega), if_pos (by simp; omega)]
    rw [extra_val L (B + 2) (B + 1) _ hW2 (by omega)
      (fun p hp => by have := hL p (by simp [hp]); omega), last]
    have hany : L.any (fun p => (W ++ [x] ++ [W.getD c false || x]).getD p.1 false &&
        (W ++ [x] ++ [W.getD c false || x]).getD p.2 false) =
        L.any (fun p => W.getD p.1 false && W.getD p.2 false) := by
      apply any_congr_mem
      intro p hp
      have hq := hL p (by simp [hp])
      rw [pre _ hq.1, pre _ hq.2]
    rw [hany, List.any_cons, hx]
    simp [Bool.or_assoc]

theorem accIdx_lt : ∀ (L : List (ℕ × ℕ)) (B c : ℕ), c < B → accIdx B c L < B + 2 * L.length
  | [], B, c, h => by simp [accIdx]; omega
  | _ :: L, B, c, _ => by
    simp only [accIdx, List.length_cons]
    have := accIdx_lt L (B + 2) (B + 1) (by omega)
    omega

theorem extra_reads : ∀ (L : List (ℕ × ℕ)) (B c : ℕ), c < B → (∀ p ∈ L, p.1 < B ∧ p.2 < B) →
    ∀ k < (extra B c L).length, ∀ i ∈ ((extra B c L).getD k ⟨GateOp.or, []⟩).inputs, i < B + k
  | [], B, c, _, _ => by intro k hk; simp [extra] at hk
  | (u, v) :: L, B, c, hc, hL => by
    have hu := (hL (u, v) (by simp)).1
    have hv := (hL (u, v) (by simp)).2
    intro k hk i hi
    match k, hk, hi with
    | 0, _, hi =>
      simp [extra] at hi
      rcases hi with rfl | rfl <;> omega
    | 1, _, hi =>
      simp [extra] at hi
      rcases hi with rfl | rfl <;> omega
    | k + 2, hk, hi =>
      have hk' : k < (extra (B + 2) (B + 1) L).length := by
        simp only [extra, List.length_cons] at hk
        omega
      have hi' : i ∈ ((extra (B + 2) (B + 1) L).getD k ⟨GateOp.or, []⟩).inputs := by
        simpa [extra] using hi
      have := extra_reads L (B + 2) (B + 1) (by omega)
        (fun p hp => by have := hL p (by simp [hp]); omega) k hk' i hi'
      omega

theorem extra_shape : ∀ (L : List (ℕ × ℕ)) (B c : ℕ), ∀ g ∈ extra B c L,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [], B, c => by intro g hg; simp [extra] at hg
  | (u, v) :: L, B, c => by
    intro g hg
    simp only [extra, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact extra_shape L (B + 2) (B + 1) g hg

theorem mp_lt (a n i : ℕ) (han : a ≤ n) (hi : i < n) : mp a n i < n + n := by
  unfold mp
  split_ifs <;> omega

end PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro x1 x2 x3 x4 hne hAO hf x8 x9 x10
  have hx8 : x8 = x1 + x2 := rfl
  obtain ⟨hAnd, hRB, hLen⟩ := hAO
  set s := x4.gates.length with hs
  set L : List (ℕ × ℕ) := x10.toList.map (fun pr => ((pr.1 : ℕ), x8 + (pr.2 : ℕ))) with hL
  set c := PEqualNP.Outside.L_meta_3264.mp x1 x8 x4.output with hcdef
  set B := x8 + x8 + s with hB
  have hwl : ∀ y : List Bool, (x4.wires y).length = y.length + s := by
    intro y
    rw [PEqualNP.Outside.L_meta_3264.wires_eq, PEqualNP.Outside.L_meta_3264.fold_length]
  have ho : x4.output < x8 + s := by
    obtain ⟨⟨p, l⟩, hpl⟩ := hne
    have h1 := hf (fun e => decide (e = Fin.castAdd x2 p ∨ e = Fin.natAdd x1 l))
    have h2 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4
        (fun e => decide (e = Fin.castAdd x2 p ∨ e = Fin.natAdd x1 l)) = true := by
      rw [h1, decide_eq_true_iff]
      exact ⟨p, l, hpl, by simp, by simp⟩
    by_contra hcon
    have h3 : (x4.wires (List.ofFn (fun e => decide (e = Fin.castAdd x2 p ∨ e = Fin.natAdd x1 l)))).getD
        x4.output false = false := by
      apply List.getD_eq_default
      rw [hwl]
      simp
      omega
    exact absurd h2 (by
      show ¬ (x4.wires _).getD x4.output false = true
      rw [h3]
      simp)
  have hc : c < B := by
    rw [hcdef]
    unfold PEqualNP.Outside.L_meta_3264.mp
    split_ifs <;> omega
  have hLb : ∀ p ∈ L, p.1 < B ∧ p.2 < B := by
    intro p hp
    rw [hL, List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    have h1 := q.1.isLt
    have h2 := q.2.isLt
    constructor <;> simp only <;> omega
  have hLlen : L.length = x10.card := by
    rw [hL, List.length_map, Finset.length_toList]
  refine ⟨⟨x4.gates.map (PEqualNP.Outside.L_meta_3264.rl x1 x8) ++
      PEqualNP.Outside.L_meta_3264.extra B c L, PEqualNP.Outside.L_meta_3264.accIdx B c L⟩,
    ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩ | hg
    · exact hAnd g' hg'
    · exact (PEqualNP.Outside.L_meta_3264.extra_shape L B c g hg).1
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    simp only [List.length_append, List.length_map] at hj
    by_cases hjs : j < s
    · have hjl : j < (x4.gates.map (PEqualNP.Outside.L_meta_3264.rl x1 x8)).length := by
        rw [List.length_map]
        exact hjs
      rw [List.getD_append _ _ _ _ hjl, List.getD_eq_getElem _ _ hjl, List.getElem_map] at hi
      simp only [PEqualNP.Outside.L_meta_3264.rl, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hg0 : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j = x4.gates[j] := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
        exact List.getD_eq_getElem _ _ hjs
      have := hRB j hjs i0 (by rw [hg0]; exact hi0)
      unfold PEqualNP.Outside.L_meta_3264.mp
      split_ifs <;> omega
    · have hjl : (x4.gates.map (PEqualNP.Outside.L_meta_3264.rl x1 x8)).length ≤ j := by
        simp [hs]
        omega
      rw [List.getD_append_right _ _ _ _ hjl] at hi
      have hk : j - (x4.gates.map (PEqualNP.Outside.L_meta_3264.rl x1 x8)).length <
          (PEqualNP.Outside.L_meta_3264.extra B c L).length := by
        simp only [List.length_map]
        omega
      have := PEqualNP.Outside.L_meta_3264.extra_reads L B c hc hLb _ hk i hi
      simp only [List.length_map] at this
      omega
  · intro g hg
    rw [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩ | hg
    · simp [PEqualNP.Outside.L_meta_3264.rl, hLen g' hg']
    · exact (PEqualNP.Outside.L_meta_3264.extra_shape L B c g hg).2
  · show (x4.gates.map _ ++ _).length ≤ _
    rw [List.length_append, List.length_map, PEqualNP.Outside.L_meta_3264.extra_length, hLlen]
    rfl
  · intro x12
    let z : Fin (x1 + x2) → Bool := fun u =>
      x12 ⟨PEqualNP.Outside.L_meta_3264.mp x1 x8 u, PEqualNP.Outside.L_meta_3264.mp_lt x1 x8 u
        (by omega) u.isLt⟩
    have hinit : PEqualNP.Outside.L_meta_3264.Rel x1 x8 (List.ofFn x12) (List.ofFn z) := by
      refine ⟨by simp; omega, by simp; omega, by omega, fun k => ?_⟩
      rw [PEqualNP.Outside.L_meta_3264.getD_ofFn, PEqualNP.Outside.L_meta_3264.getD_ofFn]
      by_cases hk : k < x1 + x2
      · rw [dif_pos (PEqualNP.Outside.L_meta_3264.mp_lt x1 x8 k (by omega) hk), dif_pos hk]
      · have e : PEqualNP.Outside.L_meta_3264.mp x1 x8 k = x8 + k := by
          simp [PEqualNP.Outside.L_meta_3264.mp]
          omega
        rw [dif_neg hk, dif_neg (by rw [e]; omega)]
    have hrel := PEqualNP.Outside.L_meta_3264.fold_rel x1 x8 x4.gates _ _ hinit
    set W' := (x4.gates.map (PEqualNP.Outside.L_meta_3264.rl x1 x8)).foldl
      PEqualNP.Outside.L_meta_3264.step (List.ofFn x12) with hW'
    have hW'len : W'.length = B := by
      rw [hrel.1, PEqualNP.Outside.L_meta_3264.fold_length]
      simp [hB]
      omega
    have hW'in : ∀ i (hi : i < x8 + x8), W'.getD i false = x12 ⟨i, hi⟩ := by
      intro i hi
      rw [hW', PEqualNP.Outside.L_meta_3264.fold_keep _ _ _ (by simp; omega),
        PEqualNP.Outside.L_meta_3264.getD_ofFn, dif_pos hi]
    show ((x4.gates.map (PEqualNP.Outside.L_meta_3264.rl x1 x8) ++
        PEqualNP.Outside.L_meta_3264.extra B c L).foldl PEqualNP.Outside.L_meta_3264.step
          (List.ofFn x12)).getD (PEqualNP.Outside.L_meta_3264.accIdx B c L) false = _
    rw [List.foldl_append, ← hW', PEqualNP.Outside.L_meta_3264.extra_val L B c W' hW'len hc hLb]
    have hA : W'.getD c false = true ↔ ∃ (p : Fin x1) (l : Fin x2), (p, l) ∈ x3 ∧
        x12 (Fin.castAdd x8 (Fin.castAdd x2 p)) = true ∧
        x12 (Fin.natAdd x8 (Fin.natAdd x1 l)) = true := by
      rw [hcdef, hrel.2.2.2 x4.output]
      have e := hf z
      change (x4.wires (List.ofFn z)).getD x4.output false = _ at e
      rw [PEqualNP.Outside.L_meta_3264.wires_eq] at e
      rw [e, decide_eq_true_iff]
      have ep : ∀ p : Fin x1, z (Fin.castAdd x2 p) = x12 (Fin.castAdd x8 (Fin.castAdd x2 p)) := by
        intro p
        show x12 _ = x12 _
        congr 1
        apply Fin.ext
        simp [PEqualNP.Outside.L_meta_3264.mp, p.isLt]
      have el : ∀ l : Fin x2, z (Fin.natAdd x1 l) = x12 (Fin.natAdd x8 (Fin.natAdd x1 l)) := by
        intro l
        show x12 _ = x12 _
        congr 1
        apply Fin.ext
        simp [PEqualNP.Outside.L_meta_3264.mp]
        omega
      simp only [ep, el]
    have hBq : (L.any fun p => W'.getD p.1 false && W'.getD p.2 false) = true ↔
        ∃ q ∈ x10, x12 (Fin.castAdd x8 q.1) = true ∧ x12 (Fin.natAdd x8 q.2) = true := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨p, hp, hv⟩
        rw [hL, List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        rw [Bool.and_eq_true] at hv
        simp only at hv
        refine ⟨q, Finset.mem_toList.mp hq, ?_, ?_⟩
        · rw [hW'in _ (by have := q.1.isLt; omega)] at hv
          exact hv.1
        · rw [hW'in (x8 + (q.2 : ℕ)) (by have := q.2.isLt; omega)] at hv
          exact hv.2
      · rintro ⟨q, hq, h1, h2⟩
        refine ⟨((q.1 : ℕ), x8 + (q.2 : ℕ)), ?_, ?_⟩
        · rw [hL, List.mem_map]
          exact ⟨q, Finset.mem_toList.mpr hq, rfl⟩
        · rw [Bool.and_eq_true]
          simp only
          rw [hW'in (q.1 : ℕ) (by have := q.1.isLt; omega),
            hW'in (x8 + (q.2 : ℕ)) (by have := q.2.isLt; omega)]
          exact ⟨h1, h2⟩
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true, hA, hBq, decide_eq_true_iff]
    simp only [x9, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨p, l, hpl, h1, h2⟩ | ⟨q, hq, h1, h2⟩)
      · exact ⟨_, _, Or.inl ⟨(p, l), hpl, rfl⟩, h1, h2⟩
      · exact ⟨q.1, q.2, Or.inr hq, h1, h2⟩
    · rintro ⟨a, b, hab | hab, h1, h2⟩
      · obtain ⟨⟨p, l⟩, hpl, he⟩ := hab
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact Or.inl ⟨p, l, hpl, h1, h2⟩
      · exact Or.inr ⟨(a, b), hab, h1, h2⟩
