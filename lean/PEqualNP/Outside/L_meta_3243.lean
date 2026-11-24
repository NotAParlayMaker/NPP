import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3243

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step of a circuit, as in `Circuit.wires`.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_app (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp [step]
    · simp [hl]

theorem getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_app_right {w t : List Bool} {i : ℕ} :
    (w ++ t).getD (w.length + i) false = t.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

theorem getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst h
  simpa using getD_app_right (w := l) (t := [b]) (i := 0)

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_app gs w
  rw [ht, List.length_append, hl]

theorem fold_keep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_app gs w
  rw [ht, getD_app_left h]

theorem any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.any_cons]
    rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]

-- The value of the chain wire `k` of a block.
def cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
  w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

theorem chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (k : ℕ) (hk : k ≤ rest.length) :
    (w ++ (List.range k).map (fun i => cv w v1 rest (i + 1))).getD
        ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false
      = cv w v1 rest k := by
  cases k with
  | zero =>
    simp only [List.getD_cons_zero]
    rw [getD_app_left (by omega)]
    simp [cv]
  | succ j =>
    have hj : j < rest.length := by omega
    have e1 : (v1 :: (List.range rest.length).map (fun j => B + j)).getD (j + 1) 0 = B + j := by
      simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hj]
    rw [e1, ← hw, getD_app_right]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < j + 1 by omega)]

theorem chain (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
    ∀ k ≤ rest.length,
      ((List.range k).map (fun i => (⟨GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
        step w = w ++ (List.range k).map (fun i => cv w v1 rest (i + 1)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    rw [List.append_assoc]
    congr 2
    have hkr : k < rest.length := by omega
    have hrk : rest.getD k 0 = rest[k] := by
      simp [List.getD_eq_getElem?_getD, hkr]
    have hlt : rest[k] < w.length := by rw [hw]; exact hrest _ (List.getElem_mem hkr)
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
    simp only [cv, List.take_succ, List.getElem?_eq_getElem hkr, Option.toList_some,
      List.any_append, List.any_cons, List.any_nil, List.any_cons, Bool.or_false, id]
    simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

theorem block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

theorem block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (hw : w.length = B) (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B)
    (hrest : ∀ u ∈ rest, u < B) :
    ((blockGates B a t v1 rest lead).foldl step w).getD
        (B + (blockGates B a t v1 rest lead).length - 1) false
      = if lead then (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))
        else (w.getD a false ||
          (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))) := by
  have hc := chain w B v1 rest hw hv1 hrest rest.length le_rfl
  have hr := chain_read w B v1 rest hw hv1 rest.length le_rfl
  have hcvr : cv w v1 rest rest.length = (w.getD v1 false || rest.any (fun u => w.getD u false)) := by
    simp [cv]
  set L := (List.range rest.length).map (fun i => cv w v1 rest (i + 1)) with hL
  have hLl : L.length = rest.length := by simp [hL]
  have htW : (w ++ L).getD t false = w.getD t false := getD_app_left (by omega)
  rw [block_length]
  cases lead with
  | true =>
    simp only [blockGates, ↓reduceIte, List.foldl_append, hc, List.foldl_cons, List.foldl_nil,
      step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
      rw [htW, hr, hcvr]
      simp
    · simp [hLl, hw]
  | false =>
    have ha' : a < B := ha rfl
    simp only [blockGates, Bool.false_eq_true, ↓reduceIte, List.foldl_append, hc, List.foldl_cons,
      List.foldl_nil, step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      rw [getD_app_left (by simp; omega), getD_app_left (by omega), getD_snoc']
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
        rw [htW, hr, hcvr]
        simp
      · simp [hLl, hw]
    · simp [hLl, hw]

theorem gates_length_false : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ), (∀ p ∈ own, p.2 ≠ []) →
    (coverGatesB B false a own).length =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length
  | [], _, _, _ => by simp [coverGatesB]
  | (t, []) :: os, B, a, h => by simp at h
  | (t, v1 :: rest) :: os, B, a, h => by
      have ih := gates_length_false os (B + (blockGates B a t v1 rest false).length)
        (B + (blockGates B a t v1 rest false).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      simp only [coverGatesB, List.length_append]
      rw [ih, block_length]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      simp
      omega

theorem circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (h : ∀ p ∈ own, p.2 ≠ []) :
    (coverCircuitB n own).size =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length - 1 := by
  match own with
  | [] => simp [coverCircuitB, Circuit.size, coverGatesB]
  | (t, l) :: os =>
    match l with
    | [] => exact False.elim (h (t, []) (by simp) rfl)
    | v1 :: rest =>
      have ih := gates_length_false os (n + (blockGates n 0 t v1 rest true).length)
        (n + (blockGates n 0 t v1 rest true).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      have hgl : (coverGatesB n true 0 ((t, v1 :: rest) :: os)).length =
          rest.length + 1 + ((os.map (fun p : ℕ × List ℕ => p.2.length)).sum + os.length) := by
        simp only [coverGatesB, List.length_append]
        rw [ih, block_length]
        simp
      have hnn : coverGatesB n true 0 ((t, v1 :: rest) :: os) ≠ [] := by
        intro h0
        have h1 := congrArg List.length h0
        rw [hgl] at h1
        simp at h1
      unfold coverCircuitB Circuit.size
      rw [if_neg hnn]
      simp only [hgl, List.map_cons, List.sum_cons, List.length_cons]
      omega

-- The target function on the input string `x`.
def F (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

theorem gates_nil_F (x : List Bool) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    coverGatesB B lead a own = [] → F x own = false
  | [], _, _, _, _ => rfl
  | (t, []) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      have := gates_nil_F x os B lead a h
      simp only [F, List.any_cons, List.any_nil, Bool.and_false, Bool.false_or] at this ⊢
      exact this
  | (t, v1 :: rest) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      cases lead <;> simp [blockGates] at h

theorem main (n : ℕ) (x : List Bool) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
      (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) → w.length = B → n ≤ B →
      (∀ i < n, w.getD i false = x.getD i false) → (lead = false → a < B) →
      coverGatesB B lead a own ≠ [] →
      ((coverGatesB B lead a own).foldl step w).getD
          (B + (coverGatesB B lead a own).length - 1) false
        = if lead then F x own else (w.getD a false || F x own)
  | [], _, _, _, _, _, _, _, _, _, hne => by simp [coverGatesB] at hne
  | (t, []) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, hne => by
      simp only [coverGatesB] at hne ⊢
      rw [main n x os B lead a w (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hw hnB hwx ha
        hne]
      simp [F]
  | (t, v1 :: rest) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, _ => by
      have hp := hown (t, v1 :: rest) (by simp)
      have ht : t < n := hp.1
      have hv1 : v1 < n := hp.2 v1 (by simp)
      have hrest : ∀ u ∈ rest, u < n := fun u hu => hp.2 u (by simp [hu])
      have hos : ∀ p ∈ os, p.1 < n ∧ ∀ u ∈ p.2, u < n :=
        fun p hp => hown p (List.mem_cons_of_mem _ hp)
      have hbv := block_val w B a t v1 rest lead hw ha (by omega) (by omega)
        (fun u hu => by have := hrest u hu; omega)
      have hrx : rest.any (fun u => w.getD u false) = rest.any (fun u => x.getD u false) :=
        any_congr_mem (fun u hu => hwx u (hrest u hu))
      rw [hrx, hwx t ht, hwx v1 hv1] at hbv
      set bg := blockGates B a t v1 rest lead with hbg
      have hm : 0 < bg.length := by rw [hbg, block_length]; omega
      set W1 := bg.foldl step w with hW1
      have hW1l : W1.length = B + bg.length := by rw [hW1, fold_length, hw]
      have hW1x : ∀ i < n, W1.getD i false = x.getD i false := by
        intro i hi
        rw [hW1, fold_keep bg w (by omega)]
        exact hwx i hi
      have hW1a : lead = false → W1.getD a false = w.getD a false := by
        intro hl
        rw [hW1, fold_keep bg w (by have := ha hl; omega)]
      have hcons : F x ((t, v1 :: rest) :: os) =
          ((x.getD t false && (x.getD v1 false || rest.any (fun u => x.getD u false))) || F x os) :=
        rfl
      rw [hcons]
      simp only [coverGatesB]
      rw [← hbg, List.foldl_append, ← hW1, List.length_append]
      by_cases hnil : coverGatesB (B + bg.length) false (B + bg.length - 1) os = []
      · have hF := gates_nil_F x os _ false _ hnil
        rw [hnil, List.foldl_nil, List.length_nil, Nat.add_zero, hbv]
        rw [hF]
        cases lead <;> simp
      · have ih := main n x os (B + bg.length) false (B + bg.length - 1) W1 hos hW1l (by omega)
          hW1x (fun _ => by omega) hnil
        have hidx : B + (bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length) - 1
            = B + bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length - 1 := by
          omega
        rw [hidx, ih, hbv]
        cases lead <;> simp [Bool.or_assoc]

theorem circuit_fun (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) (x : Fin n → Bool) :
    ((coverCircuitB n own).eval (List.ofFn x) = true ↔
      ∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) := by
  have hF : (∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) ↔ F (List.ofFn x) own = true := by
    simp [F, List.any_eq_true]
  rw [hF]
  unfold coverCircuitB Circuit.eval
  split_ifs with hnil
  · rw [gates_nil_F _ own n true 0 hnil, wires_eq]
    simp [List.getD_eq_getElem?_getD]
  · rw [wires_eq]
    simp only
    rw [main n (List.ofFn x) own n true 0 (List.ofFn x) h (by simp) le_rfl (fun _ _ => rfl)
      (by simp) hnil]
    simp

-- Reading the input string at the index of a `Fin`.
theorem eval_at {n : ℕ} (x : Fin n → Bool) (j : Fin n) :
    (List.ofFn x).getD ↑j false = x j := by
  simp [List.getD_eq_getElem?_getD]

-- The set of owners through which `x3` accepts, on either side.
theorem cover_iff (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) (x5 : List (ℕ × List ℕ))
    (hA : ∀ p ∈ x5, p.2 ≠ [] ∧ ((p.1 < x1 ∧ ∀ u ∈ p.2, x1 ≤ u ∧ u < x1 + x2) ∨
      (x1 ≤ p.1 ∧ p.1 < x1 + x2 ∧ ∀ u ∈ p.2, u < x1)))
    (hB : ∀ (a : Fin x1) (b : Fin x2),
      x3 a b ↔ ∃ p ∈ x5, (p.1 = ↑a ∧ x1 + ↑b ∈ p.2) ∨ (p.1 = x1 + ↑b ∧ ↑a ∈ p.2))
    (x : Fin (x1 + x2) → Bool) :
    (∃ p ∈ x5, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) ↔
      ∃ (a : Fin x1) (b : Fin x2), x3 a b ∧ x (Fin.castAdd x2 a) = true ∧
        x (Fin.natAdd x1 b) = true := by
  constructor
  · rintro ⟨p, hp, hpp, w, hw, hww⟩
    obtain ⟨-, hcase⟩ := hA p hp
    rcases hcase with ⟨hplt, hmem⟩ | ⟨hge, hlt2, hmem⟩
    · have hw1 : x1 ≤ w := (hmem w hw).1
      have hw2 : w < x1 + x2 := (hmem w hw).2
      set a : Fin x1 := ⟨p.1, hplt⟩ with ha
      set b : Fin x2 := ⟨w - x1, by omega⟩ with hb
      refine ⟨a, b, ?_, ?_, ?_⟩
      · rw [hB]
        refine ⟨p, hp, Or.inl ⟨?_, ?_⟩⟩
        · exact (congrArg Fin.val ha).symm
        · show x1 + ↑b ∈ p.2
          rw [show ↑b = w - x1 from congrArg Fin.val hb,
            show x1 + (w - x1) = w by omega]
          exact hw
      · rw [← eval_at x (Fin.castAdd x2 a)]
        show (List.ofFn x).getD p.1 false = true
        exact hpp
      · rw [← eval_at x (Fin.natAdd x1 b)]
        show (List.ofFn x).getD (x1 + ↑b) false = true
        rw [show ↑b = w - x1 from congrArg Fin.val hb,
          show x1 + (w - x1) = w by omega]
        exact hww
    · have hw1 : w < x1 := hmem w hw
      set a : Fin x1 := ⟨w, hw1⟩ with ha
      set b : Fin x2 := ⟨p.1 - x1, by omega⟩ with hb
      refine ⟨a, b, ?_, ?_, ?_⟩
      · rw [hB]
        refine ⟨p, hp, Or.inr ⟨?_, ?_⟩⟩
        · show p.1 = x1 + ↑b
          rw [show ↑b = p.1 - x1 from congrArg Fin.val hb]
          omega
        · show ↑a ∈ p.2
          rw [show ↑a = w from congrArg Fin.val ha]
          exact hw
      · rw [← eval_at x (Fin.castAdd x2 a)]
        show (List.ofFn x).getD w false = true
        exact hww
      · rw [← eval_at x (Fin.natAdd x1 b)]
        show (List.ofFn x).getD (x1 + ↑b) false = true
        rw [show ↑b = p.1 - x1 from congrArg Fin.val hb,
          show x1 + (p.1 - x1) = p.1 by omega]
        exact hpp
  · rintro ⟨a, b, h3, hx1, hx2⟩
    rcases (hB a b).mp h3 with ⟨p, hp, hpp | hpp⟩
    · obtain ⟨hp1, hmem⟩ := hpp
      refine ⟨p, hp, ?_, x1 + ↑b, hmem, ?_⟩
      · have hgd : (List.ofFn x).getD p.1 false = x (Fin.castAdd x2 a) := by
          rw [hp1]
          exact eval_at x (Fin.castAdd x2 a)
        rw [hgd]
        exact hx1
      · have hgd : (List.ofFn x).getD (x1 + ↑b) false = x (Fin.natAdd x1 b) := by
          rw [show x1 + ↑b = ↑(Fin.natAdd x1 b) from (Fin.val_natAdd x1 b).symm]
          exact eval_at x (Fin.natAdd x1 b)
        rw [hgd]
        exact hx2
    · obtain ⟨hp1, hmem⟩ := hpp
      refine ⟨p, hp, ?_, ↑a, hmem, ?_⟩
      · have hgd : (List.ofFn x).getD p.1 false = x (Fin.natAdd x1 b) := by
          rw [hp1, show x1 + ↑b = ↑(Fin.natAdd x1 b) from (Fin.val_natAdd x1 b).symm]
          exact eval_at x (Fin.natAdd x1 b)
        rw [hgd]
        exact hx2
      · have hgd : (List.ofFn x).getD ↑a false = x (Fin.castAdd x2 a) :=
          eval_at x (Fin.castAdd x2 a)
        rw [hgd]
        exact hx1

end PEqualNP.Outside.L_meta_3243

theorem PEqualNP.Outside.L_meta_3243 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  intro x1 x2 x3 x4 x5
  dsimp only
  intro hA hB
  have hown : ∀ p ∈ x5, p.1 < x1 + x2 ∧ ∀ u ∈ p.2, u < x1 + x2 := by
    intro p hp
    obtain ⟨-, hcase⟩ := hA p hp
    rcases hcase with ⟨hlt, hmem⟩ | ⟨hge, hlt, hmem⟩
    · exact ⟨by omega, fun u hu => by have := (hmem u hu).2; omega⟩
    · exact ⟨by omega, fun u hu => by have := hmem u hu; omega⟩
  constructor
  · exact PEqualNP.Outside.L_meta_3243.circuit_size (x1 + x2) x5
      (fun p hp => (hA p hp).1)
  · intro x10
    have hcirc := PEqualNP.Outside.L_meta_3243.circuit_fun (x1 + x2) x5 hown x10
    have hkey := PEqualNP.Outside.L_meta_3243.cover_iff x1 x2 x3 x5 hA hB x10
    show PEqualNP.CircuitLowerBounds.Circuit.eval (PEqualNP.MetaComplexity.coverCircuitB (x1 + x2) x5)
      (List.ofFn x10) = _
    by_cases hP : ∃ (a : Fin x1) (b : Fin x2), x3 a b ∧ x10 (Fin.castAdd x2 a) = true ∧
      x10 (Fin.natAdd x1 b) = true
    · rw [decide_eq_true hP]
      exact hcirc.mpr (hkey.mpr hP)
    · rw [decide_eq_false hP]
      cases hv : (PEqualNP.MetaComplexity.coverCircuitB (x1 + x2) x5).eval (List.ofFn x10)
      · rfl
      · exact absurd (hcirc.mp hv) (fun hq => hP (hkey.mp hq))
