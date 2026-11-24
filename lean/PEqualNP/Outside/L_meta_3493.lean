import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3493

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem block_shape (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    ∀ g ∈ blockGates B a t v1 rest lead,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  cases lead <;> simp [blockGates] at hg <;> rcases hg with ⟨i, _, rfl⟩ | rfl | rfl <;> simp

theorem gates_shape : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    ∀ g ∈ coverGatesB B lead a own,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [], _, _, _ => by intro g hg; simp [coverGatesB] at hg
  | (t, []) :: os, B, lead, a => by
      intro g hg
      simp only [coverGatesB] at hg
      exact gates_shape os B lead a g hg
  | (t, v1 :: rest) :: os, B, lead, a => by
      intro g hg
      simp only [coverGatesB, List.mem_append] at hg
      rcases hg with hg | hg
      · exact block_shape B a t v1 rest lead g hg
      · exact gates_shape os _ false _ g hg

theorem circuit_shape (n : ℕ) (own : List (ℕ × List ℕ)) :
    Monotone2 (coverCircuitB n own) ∧ ∀ g ∈ (coverCircuitB n own).gates, g.inputs.length = 2 := by
  have key : ∀ g ∈ (coverCircuitB n own).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    unfold coverCircuitB at hg
    split_ifs at hg with h
    · simp at hg
    · exact gates_shape own n true 0 g hg
  refine ⟨fun g hg => ?_, fun g hg => (key g hg).2⟩
  obtain ⟨hop, hlen⟩ := key g hg
  refine ⟨?_, by omega⟩
  rcases hop with h | h <;> simp [h]


theorem block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

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

theorem circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (hne : own ≠ [])
    (h : ∀ p ∈ own, p.2 ≠ []) :
    (coverCircuitB n own).size + 1 =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
  match own, hne, h with
  | (t, []) :: os, _, h => simp at h
  | (t, v1 :: rest) :: os, _, h =>
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


def dflt : Gate := ⟨GateOp.or, []⟩

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def isOrOp : GateOp → Bool
  | GateOp.or => true
  | _ => false

theorem isAndOp_iff (o : GateOp) : isAndOp o = true ↔ o = GateOp.and := by
  cases o <;> simp [isAndOp]

theorem isOrOp_iff (o : GateOp) : isOrOp o = true ↔ o = GateOp.or := by
  cases o <;> simp [isOrOp]

def fix (K : ℕ) (g : Gate) : Gate :=
  if isAndOp g.op && decide (g.inputs.headD 0 < K) then ⟨g.op, g.inputs.reverse⟩ else g

theorem fix_op (K : ℕ) (g : Gate) : (fix K g).op = g.op := by
  unfold fix; split_ifs <;> rfl

theorem fix_len (K : ℕ) (g : Gate) : (fix K g).inputs.length = g.inputs.length := by
  unfold fix; split_ifs <;> simp

theorem fix_mem (K : ℕ) (g : Gate) (i : ℕ) : i ∈ (fix K g).inputs ↔ i ∈ g.inputs := by
  unfold fix; split_ifs <;> simp

theorem fix_or (K : ℕ) (g : Gate) (h : g.op = GateOp.or) : fix K g = g := by
  unfold fix; rw [h]; simp [isAndOp]

theorem fix_dflt (K : ℕ) : fix K dflt = dflt := fix_or K dflt rfl

theorem fix_val (K : ℕ) (g : Gate) (w : List Bool) :
    (fix K g).op.eval ((fix K g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold fix
  split_ifs with h
  · simp only [Bool.and_eq_true, isAndOp_iff] at h
    simp only [h.1, GateOp.eval, List.map_reverse, List.all_reverse]
  · rfl

theorem fold_fix (K : ℕ) (G : List Gate) (w : List Bool) :
    (G.map (fix K)).foldl step w = G.foldl step w := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    unfold step
    rw [fix_val]

theorem getD_map_fix (K : ℕ) (G : List Gate) (j : ℕ) :
    (G.map (fix K)).getD j dflt = fix K (G.getD j dflt) := by
  rw [← fix_dflt K, List.getD_map, fix_dflt]

def pureW (G : List Gate) (n lo hi : ℕ) (w : ℕ) : Bool :=
  decide (lo ≤ w ∧ w < hi) ||
    (decide (n ≤ w ∧ w < n + G.length) &&
      (isOrOp (G.getD (w - n) dflt).op &&
        (G.getD (w - n) dflt).inputs.attach.all
          (fun i => if i.1 < w then pureW G n lo hi i.1 else false)))
termination_by w
decreasing_by assumption

theorem pureW_eq (G : List Gate) (n lo hi w : ℕ) : pureW G n lo hi w = (decide (lo ≤ w ∧ w < hi) ||
    (decide (n ≤ w ∧ w < n + G.length) &&
      (isOrOp (G.getD (w - n) dflt).op &&
        (G.getD (w - n) dflt).inputs.attach.all
          (fun i => if i.1 < w then pureW G n lo hi i.1 else false)))) := by
  rw [pureW]

theorem pureW_gate (G : List Gate) (n lo hi w : ℕ) (hn : n ≤ w) (hw : w < n + G.length)
    (hop : (G.getD (w - n) dflt).op = GateOp.or)
    (hin : ∀ i ∈ (G.getD (w - n) dflt).inputs, i < w ∧ pureW G n lo hi i = true) :
    pureW G n lo hi w = true := by
  rw [pureW_eq]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, isOrOp_iff]
  right
  refine ⟨⟨hn, hw⟩, hop, ?_⟩
  intro i _
  rw [if_pos (hin i.1 i.2).1]
  exact (hin i.1 i.2).2

theorem pureW_cases (G : List Gate) (n lo hi w : ℕ) (h : pureW G n lo hi w = true) :
    (lo ≤ w ∧ w < hi) ∨ (n ≤ w ∧ w < n + G.length ∧ (G.getD (w - n) dflt).op = GateOp.or ∧
      ∀ i ∈ (G.getD (w - n) dflt).inputs, i < w ∧ pureW G n lo hi i = true) := by
  rw [pureW_eq] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, isOrOp_iff] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3, h4⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, h2, h3, fun i hi => ?_⟩
    have := h4 ⟨i, hi⟩ (List.mem_attach _ _)
    simp only at this
    split_ifs at this with hlt
    exact ⟨hlt, this⟩

theorem pureW_append (G P : List Gate) (n lo hi w : ℕ) (hw : w < n + G.length) :
    pureW (G ++ P) n lo hi w = pureW G n lo hi w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [pureW_eq, pureW_eq G]
    by_cases hnw : n ≤ w
    · have hidx : (G ++ P).getD (w - n) dflt = G.getD (w - n) dflt := by
        rw [List.getD_append _ _ _ _ (by omega)]
      rw [hidx]
      have hall : ((G.getD (w - n) dflt).inputs.attach.all
          (fun i => if i.1 < w then pureW (G ++ P) n lo hi i.1 else false)) =
          ((G.getD (w - n) dflt).inputs.attach.all
          (fun i => if i.1 < w then pureW G n lo hi i.1 else false)) := by
        congr 1
        funext i
        split_ifs with hlt
        · exact ih i.1 hlt (by omega)
        · rfl
      rw [hall]
      simp only [List.length_append]
      congr 1
      have hlen : w < n + (G.length + P.length) := by omega
      simp [hnw, hlen, hw]
    · simp [hnw]

def prevW (B v1 : ℕ) (rest : List ℕ) (i : ℕ) : ℕ :=
  (v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0

theorem prevW_zero (B v1 : ℕ) (rest : List ℕ) : prevW B v1 rest 0 = v1 := rfl

theorem prevW_succ (B v1 : ℕ) (rest : List ℕ) (i : ℕ) (hi : i < rest.length) :
    prevW B v1 rest (i + 1) = B + i := by
  simp [prevW, List.getD_cons_succ, List.getD_eq_getElem?_getD, hi]

theorem block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

theorem block_get (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (k : ℕ)
    (hk : k < (blockGates B a t v1 rest lead).length) :
    (k < rest.length ∧ (blockGates B a t v1 rest lead)[k] =
        ⟨GateOp.or, [prevW B v1 rest k, rest.getD k 0]⟩) ∨
      (k = rest.length ∧ (blockGates B a t v1 rest lead)[k] =
        ⟨GateOp.and, [t, prevW B v1 rest rest.length]⟩) ∨
      (k = rest.length + 1 ∧ lead = false ∧ (blockGates B a t v1 rest lead)[k] =
        ⟨GateOp.or, [a, B + rest.length]⟩) := by
  have hl := block_len B a t v1 rest lead
  rcases Nat.lt_or_ge k rest.length with h | h
  · left
    refine ⟨h, ?_⟩
    simp only [blockGates]
    rw [List.getElem_append_left (by simpa using h)]
    simp [prevW]
  · rcases Nat.eq_or_lt_of_le h with h2 | h2
    · right; left
      subst h2
      refine ⟨rfl, ?_⟩
      simp only [blockGates]
      rw [List.getElem_append_right (by simp)]
      simp [prevW]
    · right; right
      have hk2 : k = rest.length + 1 := by cases lead <;> simp at hl <;> omega
      have hlead : lead = false := by
        cases lead
        · rfl
        · simp at hl; omega
      subst hk2; subst hlead
      refine ⟨rfl, rfl, ?_⟩
      simp only [blockGates]
      rw [List.getElem_append_right (by simp)]
      simp

theorem block_reads (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (ht : t < B) (hv : v1 < B)
    (hr : ∀ u ∈ rest, u < B) (ha : lead = false → a < B) (k : ℕ)
    (hk : k < (blockGates B a t v1 rest lead).length) :
    ∀ i ∈ ((blockGates B a t v1 rest lead)[k]).inputs, i < B + k := by
  intro i hi
  rcases block_get B a t v1 rest lead k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h2] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · cases k with
      | zero => rw [prevW_zero]; omega
      | succ j => rw [prevW_succ B v1 rest j (by omega)]; omega
    · have : rest.getD k 0 = rest[k] := by simp [List.getD_eq_getElem?_getD, h1]
      rw [this]
      have := hr _ (List.getElem_mem h1)
      omega
  · rw [h2] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · omega
    · cases hrl : rest.length with
      | zero => rw [prevW_zero]; omega
      | succ j => rw [prevW_succ B v1 rest j (by omega)]; omega
  · rw [h3] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := ha h2; omega
    · omega

theorem gates_reads (n : ℕ) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    n ≤ B → (∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) → (lead = false → a < B) →
    ∀ k (hk : k < (coverGatesB B lead a own).length),
      ∀ i ∈ ((coverGatesB B lead a own)[k]).inputs, i < B + k
  | [], _, _, _, _, _, _ => by intro k hk; simp [coverGatesB] at hk
  | (t, []) :: os, B, lead, a, hB, hown, ha => by
      intro k hk i hi
      simp only [coverGatesB] at hk hi
      exact gates_reads n os B lead a hB (fun p hp => hown p (List.mem_cons_of_mem _ hp)) ha k hk i hi
  | (t, v1 :: rest) :: os, B, lead, a, hB, hown, ha => by
      intro k hk i hi
      have h0 := hown (t, v1 :: rest) List.mem_cons_self
      simp only [coverGatesB] at hk hi
      by_cases hkb : k < (blockGates B a t v1 rest lead).length
      · rw [List.getElem_append_left hkb] at hi
        exact block_reads B a t v1 rest lead (by omega) (by have := h0.2 v1 (by simp); omega)
          (fun u hu => by have := h0.2 u (by simp [hu]); omega) ha k hkb i hi
      · rw [List.getElem_append_right (by omega)] at hi
        have hbl := block_len B a t v1 rest lead
        have := gates_reads n os (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) (by omega)
          (fun p hp => hown p (List.mem_cons_of_mem _ hp)) (fun _ => by omega)
          (k - (blockGates B a t v1 rest lead).length) (by simp only [List.length_append] at hk; omega) i hi
        omega

theorem pureW_side (G : List Gate) (n lo hi w : ℕ) (h : lo ≤ w ∧ w < hi) :
    pureW G n lo hi w = true := by
  rw [pureW_eq]; simp [h]

theorem getD_pre (pre Y : List Gate) (i : ℕ) :
    (pre ++ Y).getD (pre.length + i) dflt = Y.getD i dflt := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

theorem chain_step (G : List Gate) (n lo hi B v1 a t : ℕ) (rest : List ℕ) (lead : Bool)
    (pre X : List Gate) (hG : G = pre ++ (blockGates B a t v1 rest lead ++ X))
    (hpre : pre.length + n = B) (i : ℕ) (hil : i < rest.length)
    (hp : prevW B v1 rest i < B + i ∧ pureW G n lo hi (prevW B v1 rest i) = true)
    (hr : ∀ u ∈ rest, u < B ∧ pureW G n lo hi u = true) :
    pureW G n lo hi (B + i) = true := by
  have hbl := block_len B a t v1 rest lead
  have hki : i < (blockGates B a t v1 rest lead).length := by omega
  have hi' := hil
  have hget : G.getD (B + i - n) dflt = ⟨GateOp.or, [prevW B v1 rest i, rest.getD i 0]⟩ := by
    rw [hG, show B + i - n = pre.length + i by omega, getD_pre,
      List.getD_append _ _ _ _ hki, List.getD_eq_getElem _ _ hki]
    rcases block_get B a t v1 rest lead i hki with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h2
    · omega
    · omega
  have hlenG : B + i < n + G.length := by
    rw [hG]; simp only [List.length_append]; omega
  apply pureW_gate G n lo hi (B + i) (by omega) hlenG (by rw [hget])
  intro w hw
  rw [hget] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hp
  · have e : rest.getD i 0 = rest[i] := by simp [List.getD_eq_getElem?_getD, hil]
    rw [e]
    have := hr _ (List.getElem_mem hil)
    exact ⟨by omega, this.2⟩

theorem chain_pure (G : List Gate) (n lo hi B v1 a t : ℕ) (rest : List ℕ) (lead : Bool)
    (pre X : List Gate) (hG : G = pre ++ (blockGates B a t v1 rest lead ++ X))
    (hpre : pre.length + n = B) (hv : pureW G n lo hi v1 = true) (hvB : v1 < B)
    (hr : ∀ u ∈ rest, u < B ∧ pureW G n lo hi u = true) :
    ∀ i, i < rest.length → pureW G n lo hi (B + i) = true := by
  intro i
  induction i with
  | zero =>
    intro hi0
    exact chain_step G n lo hi B v1 a t rest lead pre X hG hpre 0 hi0
      (by rw [prevW_zero]; exact ⟨by omega, hv⟩) hr
  | succ j ih =>
    intro hj
    exact chain_step G n lo hi B v1 a t rest lead pre X hG hpre (j + 1) hj
      (by rw [prevW_succ B v1 rest j (by omega)]; exact ⟨by omega, ih (by omega)⟩) hr

theorem acc_pure (G : List Gate) (n lo hi B v1 a t : ℕ) (rest : List ℕ) (lead : Bool)
    (pre X : List Gate) (hG : G = pre ++ (blockGates B a t v1 rest lead ++ X))
    (hpre : pre.length + n = B) (hv : pureW G n lo hi v1 = true) (hvB : v1 < B)
    (hr : ∀ u ∈ rest, u < B ∧ pureW G n lo hi u = true) :
    pureW G n lo hi (prevW B v1 rest rest.length) = true := by
  cases hrl : rest.length with
  | zero => rw [prevW_zero]; exact hv
  | succ j =>
    rw [prevW_succ B v1 rest j (by omega)]
    exact chain_pure G n lo hi B v1 a t rest lead pre X hG hpre hv hvB hr j (by omega)

def OwnOk (n K : ℕ) (p : ℕ × List ℕ) : Prop :=
  (p.1 < K ∧ ∀ w ∈ p.2, K ≤ w ∧ w < n) ∨ (K ≤ p.1 ∧ p.1 < n ∧ ∀ w ∈ p.2, w < K)

def AndOk (G : List Gate) (n K : ℕ) (g : Gate) : Prop :=
  ∃ t acc, g.inputs = [t, acc] ∧
    ((t < K ∧ pureW G n K n acc = true) ∨ (K ≤ t ∧ t < n ∧ pureW G n 0 K acc = true))

theorem gates_and (n K : ℕ) (G : List Gate) (hK : K ≤ n) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ)
    (lead : Bool) (a : ℕ) (pre post : List Gate), G = pre ++ (coverGatesB B lead a own ++ post) →
    pre.length + n = B → (∀ p ∈ own, OwnOk n K p) →
    ∀ k (hk : k < (coverGatesB B lead a own).length),
      ((coverGatesB B lead a own)[k]).op = GateOp.and → AndOk G n K ((coverGatesB B lead a own)[k])
  | [], _, _, _, _, _, _, _, _ => by intro k hk; simp [coverGatesB] at hk
  | (t, []) :: os, B, lead, a, pre, post, hG, hpre, hown => by
      intro k hk hop
      simp only [coverGatesB] at hk hop ⊢
      simp only [coverGatesB] at hG
      exact gates_and n K G hK os B lead a pre post hG hpre
        (fun p hp => hown p (List.mem_cons_of_mem _ hp)) k hk hop
  | (t, v1 :: rest) :: os, B, lead, a, pre, post, hG, hpre, hown => by
      intro k hk hop
      have h0 := hown (t, v1 :: rest) List.mem_cons_self
      simp only [coverGatesB] at hk hop hG ⊢
      have hbl := block_len B a t v1 rest lead
      by_cases hkb : k < (blockGates B a t v1 rest lead).length
      · rw [List.getElem_append_left hkb] at hop ⊢
        have hG' : G = pre ++ (blockGates B a t v1 rest lead ++
            (coverGatesB (B + (blockGates B a t v1 rest lead).length) false
              (B + (blockGates B a t v1 rest lead).length - 1) os ++ post)) := by
          rw [hG, List.append_assoc]
        rcases block_get B a t v1 rest lead k hkb with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h3⟩
        · rw [h2] at hop; exact absurd hop (by simp)
        · rw [h2]
          refine ⟨t, prevW B v1 rest rest.length, rfl, ?_⟩
          rcases h0 with ⟨ht, hw⟩ | ⟨ht1, ht2, hw⟩
          · left
            refine ⟨ht, ?_⟩
            have hv := hw v1 (by simp)
            exact acc_pure G n K n B v1 a t rest lead pre _ hG' hpre
              (pureW_side G n K n v1 hv) (by omega)
              (fun u hu => ⟨by have := hw u (by simp [hu]); omega,
                pureW_side G n K n u (hw u (by simp [hu]))⟩)
          · right
            refine ⟨ht1, ht2, ?_⟩
            have hv := hw v1 (by simp)
            exact acc_pure G n 0 K B v1 a t rest lead pre _ hG' hpre
              (pureW_side G n 0 K v1 ⟨Nat.zero_le _, hv⟩) (by omega)
              (fun u hu => ⟨by have := hw u (by simp [hu]); omega,
                pureW_side G n 0 K u ⟨Nat.zero_le _, hw u (by simp [hu])⟩⟩)
        · rw [h3] at hop; exact absurd hop (by simp)
      · rw [List.getElem_append_right (by omega)] at hop ⊢
        have hG' : G = (pre ++ blockGates B a t v1 rest lead) ++
            (coverGatesB (B + (blockGates B a t v1 rest lead).length) false
              (B + (blockGates B a t v1 rest lead).length - 1) os ++ post) := by
          rw [hG]; simp only [List.append_assoc]
        exact gates_and n K G hK os _ false _ (pre ++ blockGates B a t v1 rest lead) post hG'
          (by simp only [List.length_append]; omega)
          (fun p hp => hown p (List.mem_cons_of_mem _ hp))
          (k - (blockGates B a t v1 rest lead).length) (by simp only [List.length_append] at hk; omega) hop

theorem getD_ofFn' (m : ℕ) (f : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def ptsL (x1 x2 : ℕ) (x5 : Finset (Fin (x1 + x2))) : List (Fin x1) :=
  (List.finRange x1).filter (fun p => decide (Fin.castAdd x2 p ∈ x5))

def lnsL (x1 x2 : ℕ) (x5 : Finset (Fin (x1 + x2))) : List (Fin x2) :=
  (List.finRange x2).filter (fun l => decide (Fin.natAdd x1 l ∈ x5))

def nbP (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I] (p : Fin x1) : List (Fin x2) :=
  (List.finRange x2).filter (fun l => decide (I p l))

def nbL (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I] (x5 : Finset (Fin (x1 + x2)))
    (l : Fin x2) : List (Fin x1) :=
  (List.finRange x1).filter (fun p => decide (I p l ∧ Fin.castAdd x2 p ∉ x5))

def own0 (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I] (x5 : Finset (Fin (x1 + x2))) :
    List (ℕ × List ℕ) :=
  (ptsL x1 x2 x5).map (fun p => (p.val, (nbP x1 x2 I p).map (fun l => x1 + l.val))) ++
    (lnsL x1 x2 x5).map (fun l => (x1 + l.val, (nbL x1 x2 I x5 l).map (fun p => p.val)))

def ownL (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I] (x5 : Finset (Fin (x1 + x2))) :
    List (ℕ × List ℕ) :=
  (own0 x1 x2 I x5).filter (fun o => !o.2.isEmpty)

theorem ownL_ok (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I]
    (x5 : Finset (Fin (x1 + x2))) : ∀ p ∈ ownL x1 x2 I x5, OwnOk (x1 + x2) x1 p := by
  intro p hp
  simp only [ownL, own0, List.mem_filter, List.mem_append, List.mem_map] at hp
  rcases hp.1 with ⟨q, _, rfl⟩ | ⟨q, _, rfl⟩
  · left
    refine ⟨q.isLt, fun w hw => ?_⟩
    simp only [List.mem_map] at hw
    obtain ⟨l, _, rfl⟩ := hw
    have := l.isLt
    omega
  · right
    refine ⟨by omega, by have := q.isLt; omega, fun w hw => ?_⟩
    simp only [List.mem_map] at hw
    obtain ⟨l, _, rfl⟩ := hw
    exact l.isLt

theorem ownL_ne (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I]
    (x5 : Finset (Fin (x1 + x2))) : ∀ p ∈ ownL x1 x2 I x5, p.2 ≠ [] := by
  intro p hp
  simp only [ownL, List.mem_filter, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
  exact hp.2

theorem ownL_bound (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I]
    (x5 : Finset (Fin (x1 + x2))) :
    ∀ p ∈ ownL x1 x2 I x5, p.1 < x1 + x2 ∧ ∀ w ∈ p.2, w < x1 + x2 := by
  intro p hp
  rcases ownL_ok x1 x2 I x5 p hp with ⟨h1, h2⟩ | ⟨_, h2, h3⟩
  · exact ⟨by omega, fun w hw => (h2 w hw).2⟩
  · exact ⟨h2, fun w hw => by have := h3 w hw; omega⟩

theorem len_own_le (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I]
    (x5 : Finset (Fin (x1 + x2))) : (ownL x1 x2 I x5).length ≤ x5.card := by
  have h1 : (ownL x1 x2 I x5).length ≤ (own0 x1 x2 I x5).length := List.length_filter_le _ _
  have hl : (own0 x1 x2 I x5).length =
      ((ptsL x1 x2 x5).map (Fin.castAdd x2) ++ (lnsL x1 x2 x5).map (Fin.natAdd x1)).length := by
    simp [own0]
  have hnd : ((ptsL x1 x2 x5).map (Fin.castAdd x2) ++ (lnsL x1 x2 x5).map (Fin.natAdd x1)).Nodup := by
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact (List.Nodup.filter _ (List.nodup_finRange x1)).map (Fin.castAdd_injective _ _)
    · exact (List.Nodup.filter _ (List.nodup_finRange x2)).map (Fin.natAdd_injective _ _)
    · intro a ha b hb hab
      simp only [List.mem_map] at ha hb
      obtain ⟨p, _, rfl⟩ := ha
      obtain ⟨l, _, rfl⟩ := hb
      have := congrArg Fin.val hab
      simp at this
      omega
  have hsub : ((ptsL x1 x2 x5).map (Fin.castAdd x2) ++ (lnsL x1 x2 x5).map (Fin.natAdd x1)).toFinset ⊆ x5 := by
    intro a ha
    simp only [List.mem_toFinset, List.mem_append, List.mem_map, ptsL, lnsL, List.mem_filter,
      decide_eq_true_eq] at ha
    rcases ha with ⟨p, ⟨_, hp⟩, rfl⟩ | ⟨l, ⟨_, hl⟩, rfl⟩
    · exact hp
    · exact hl
  have h3 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at h3
  omega

def edgesL (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I] (x5 : Finset (Fin (x1 + x2))) :
    List (Fin x1 × Fin x2) :=
  (ptsL x1 x2 x5).flatMap (fun p => (nbP x1 x2 I p).map (fun l => (p, l))) ++
    (lnsL x1 x2 x5).flatMap (fun l => (nbL x1 x2 I x5 l).map (fun p => (p, l)))

theorem sum_own_le (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I]
    (x5 : Finset (Fin (x1 + x2))) :
    ((ownL x1 x2 I x5).map (fun p : ℕ × List ℕ => p.2.length)).sum ≤ (PEqualNP.ReadTwo.incid I).card := by
  have h1 : ((ownL x1 x2 I x5).map (fun p : ℕ × List ℕ => p.2.length)).sum ≤
      ((own0 x1 x2 I x5).map (fun p : ℕ × List ℕ => p.2.length)).sum :=
    List.Sublist.sum_le_sum (List.Sublist.map _ List.filter_sublist) (fun _ _ => Nat.zero_le _)
  have h2 : ((own0 x1 x2 I x5).map (fun p : ℕ × List ℕ => p.2.length)).sum = (edgesL x1 x2 I x5).length := by
    simp [own0, edgesL, List.length_flatMap, Function.comp_def]
  have hnd : (edgesL x1 x2 I x5).Nodup := by
    unfold edgesL
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun p _ => (List.Nodup.filter _ (List.nodup_finRange x2)).map
        (fun a b h => by simpa using h), ?_⟩
      exact (List.Nodup.filter _ (List.nodup_finRange x1)).imp (fun {a b} hab => by
        intro e he he'
        simp only [List.mem_map] at he he'
        obtain ⟨l, _, rfl⟩ := he
        obtain ⟨l', _, hee⟩ := he'
        exact hab (congrArg Prod.fst hee).symm)
    · rw [List.nodup_flatMap]
      refine ⟨fun l _ => (List.Nodup.filter _ (List.nodup_finRange x1)).map
        (fun a b h => by simpa using h), ?_⟩
      exact (List.Nodup.filter _ (List.nodup_finRange x2)).imp (fun {a b} hab => by
        intro e he he'
        simp only [List.mem_map] at he he'
        obtain ⟨p, _, rfl⟩ := he
        obtain ⟨p', _, hee⟩ := he'
        exact hab (congrArg Prod.snd hee).symm)
    · intro e he e' he' hee
      subst hee
      simp only [List.mem_flatMap, List.mem_map, ptsL, lnsL, nbP, nbL, List.mem_filter,
        decide_eq_true_eq] at he he'
      obtain ⟨p, ⟨_, hp⟩, l, _, rfl⟩ := he
      obtain ⟨l', _, p', ⟨_, _, hp'⟩, he2⟩ := he'
      simp only [Prod.mk.injEq] at he2
      obtain ⟨rfl, rfl⟩ := he2
      exact hp' hp
  have hsub : (edgesL x1 x2 I x5).toFinset ⊆ PEqualNP.ReadTwo.incid I := by
    intro e he
    simp only [List.mem_toFinset, edgesL, List.mem_append, List.mem_flatMap, List.mem_map, ptsL,
      lnsL, nbP, nbL, List.mem_filter, decide_eq_true_eq] at he
    simp only [PEqualNP.ReadTwo.incid, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with ⟨p, _, l, ⟨_, hpl⟩, rfl⟩ | ⟨l, _, p, ⟨_, hpl, _⟩, rfl⟩
    · exact hpl
    · exact hpl
  have h3 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at h3
  omega

theorem gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = [] ∨ (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split_ifs <;> simp

theorem reads_C0 (n : ℕ) (own : List (ℕ × List ℕ)) (hb : ∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) :
    ∀ j (hj : j < (coverCircuitB n own).gates.length), ∀ i ∈ ((coverCircuitB n own).gates[j]).inputs,
      i < n + j := by
  intro j hj i hi
  rcases gates_eq n own with h | h
  · simp [h] at hj
  · simp only [h] at hj hi
    exact gates_reads n own n true 0 le_rfl hb (by simp) j hj i hi

theorem and_C0 (n K : ℕ) (hK : K ≤ n) (own : List (ℕ × List ℕ)) (hok : ∀ p ∈ own, OwnOk n K p) :
    ∀ j (hj : j < (coverCircuitB n own).gates.length),
      ((coverCircuitB n own).gates[j]).op = GateOp.and →
        AndOk (coverCircuitB n own).gates n K ((coverCircuitB n own).gates[j]) := by
  intro j hj hop
  rcases gates_eq n own with h | h
  · simp [h] at hj
  · simp only [h] at hj hop ⊢
    exact gates_and n K (coverGatesB n true 0 own) hK own n true 0 [] [] (by simp) (by simp) hok j hj hop

end PEqualNP.Outside.L_meta_3493

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3493

theorem PEqualNP.Outside.L_meta_3493 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : Finset (Fin (x1 + x2))), (∀ (x6 : Fin x1) (x7 : Fin x2), x3 x6 x7 → Fin.castAdd x2 x6 ∈ x5 ∨ Fin.natAdd x1 x7 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x7.size ≤ (PEqualNP.ReadTwo.incid x3).card + x5.card - (1 : ℕ) ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x1 + x2 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).inputs = [x13, x14] ∧ x13 ∈ x9 ∧ x14 ∈ x8 := by
  intro x1 x2 x3 _ x5 hcov
  have hK : x1 ≤ x1 + x2 := Nat.le_add_right _ _
  have hb := ownL_bound x1 x2 x3 x5
  have hshape := circuit_shape (x1 + x2) (ownL x1 x2 x3 x5)
  have hreads := reads_C0 (x1 + x2) (ownL x1 x2 x3 x5) hb
  have hand := and_C0 (x1 + x2) x1 hK (ownL x1 x2 x3 x5) (ownL_ok x1 x2 x3 x5)
  have hget : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt
      (⟨(coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates.map (fix x1),
        (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).output⟩ : Circuit) j =
      fix x1 ((coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates.getD j dflt) := by
    intro j
    exact getD_map_fix x1 _ j
  refine ⟨⟨(coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates.map (fix x1),
      (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).output⟩,
    (Finset.range (x1 + x2 + (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates.length)).filter
      (fun w => pureW (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates (x1 + x2) 0 x1 w = true),
    (Finset.range (x1 + x2 + (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates.length)).filter
      (fun w => pureW (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates (x1 + x2) x1 (x1 + x2) w = true),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      rw [fix_op]
      have := (hshape.1 g0 hg0).1
      simpa using this
    · intro j hj i hi
      rw [hget] at hi
      rw [fix_mem] at hi
      simp only [List.length_map] at hj
      rw [List.getD_eq_getElem _ _ hj] at hi
      exact hreads j hj i hi
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      rw [fix_len]
      exact hshape.2 g0 hg0
  · intro x
    have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2)
        (⟨(coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates.map (fix x1),
          (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).output⟩ : Circuit) x =
        (coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).eval (List.ofFn x) := by
      show (Circuit.wires _ _).getD _ _ = (Circuit.wires _ _).getD _ _
      rw [wires_eq, wires_eq]
      simp only
      rw [fold_fix]
    rw [hcf, Bool.eq_iff_iff, decide_eq_true_iff, circuit_fun (x1 + x2) _ hb x]
    have hpt : ∀ q : Fin x1, (List.ofFn x).getD q.val false = x (Fin.castAdd x2 q) := by
      intro q
      rw [getD_ofFn' _ _ _ (by have := q.isLt; omega)]
      rfl
    have hln : ∀ l : Fin x2, (List.ofFn x).getD (x1 + l.val) false = x (Fin.natAdd x1 l) := by
      intro l
      rw [getD_ofFn' _ _ _ (by have := l.isLt; omega)]
      rfl
    constructor
    · rintro ⟨p, hp, h1, w, hw, h2⟩
      simp only [ownL, own0, List.mem_filter, List.mem_append, List.mem_map] at hp
      rcases hp.1 with ⟨q, _, rfl⟩ | ⟨l, _, rfl⟩
      · simp only [List.mem_map, nbP, List.mem_filter, decide_eq_true_eq] at hw
        obtain ⟨l, ⟨_, hql⟩, rfl⟩ := hw
        exact ⟨q, l, hql, by rw [← hpt]; exact h1, by rw [← hln]; exact h2⟩
      · simp only [List.mem_map, nbL, List.mem_filter, decide_eq_true_eq] at hw
        obtain ⟨q, ⟨_, hql, _⟩, rfl⟩ := hw
        exact ⟨q, l, hql, by rw [← hpt]; exact h2, by rw [← hln]; exact h1⟩
    · rintro ⟨q, l, hql, h1, h2⟩
      by_cases hq : Fin.castAdd x2 q ∈ x5
      · refine ⟨(q.val, (nbP x1 x2 x3 q).map (fun l => x1 + l.val)), ?_, by rw [hpt]; exact h1,
          x1 + l.val, ?_, by rw [hln]; exact h2⟩
        · simp only [ownL, own0, List.mem_filter, List.mem_append, List.mem_map]
          refine ⟨Or.inl ⟨q, by simp [ptsL, hq], rfl⟩, ?_⟩
          simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, List.map_eq_nil_iff]
          intro he
          have : l ∈ nbP x1 x2 x3 q := by simp [nbP, hql]
          rw [he] at this
          simp at this
        · simp only [List.mem_map, nbP, List.mem_filter, decide_eq_true_eq]
          exact ⟨l, ⟨List.mem_finRange _, hql⟩, rfl⟩
      · have hl : Fin.natAdd x1 l ∈ x5 := (hcov q l hql).resolve_left hq
        refine ⟨(x1 + l.val, (nbL x1 x2 x3 x5 l).map (fun p => p.val)), ?_, by rw [hln]; exact h2,
          q.val, ?_, by rw [hpt]; exact h1⟩
        · simp only [ownL, own0, List.mem_filter, List.mem_append, List.mem_map]
          refine ⟨Or.inr ⟨l, by simp [lnsL, hl], rfl⟩, ?_⟩
          simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, List.map_eq_nil_iff]
          intro he
          have : q ∈ nbL x1 x2 x3 x5 l := by simp [nbL, hql, hq]
          rw [he] at this
          simp at this
        · simp only [List.mem_map, nbL, List.mem_filter, decide_eq_true_eq]
          exact ⟨q, ⟨List.mem_finRange _, hql, hq⟩, rfl⟩
  · show ((coverCircuitB (x1 + x2) (ownL x1 x2 x3 x5)).gates.map (fix x1)).length ≤ _
    rw [List.length_map]
    have hs := sum_own_le x1 x2 x3 x5
    have hl := len_own_le x1 x2 x3 x5
    by_cases hne : ownL x1 x2 x3 x5 = []
    · rw [hne]
      simp [coverCircuitB, coverGatesB]
    · have := circuit_size (x1 + x2) (ownL x1 x2 x3 x5) hne (ownL_ne x1 x2 x3 x5)
      simp only [Circuit.size] at this
      omega
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    rcases pureW_cases _ _ _ _ _ hw.2 with ⟨_, h⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · right
      refine ⟨w - (x1 + x2), by simp only [List.length_map]; omega, by omega, ?_, ?_⟩
      · rw [hget, fix_or _ _ h3]; exact h3
      · intro i hi
        rw [hget, fix_or _ _ h3] at hi
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := (h4 i hi).1; omega, (h4 i hi).2⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    rcases pureW_cases _ _ _ _ _ hw.2 with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · right
      refine ⟨w - (x1 + x2), by simp only [List.length_map]; omega, by omega, ?_, ?_⟩
      · rw [hget, fix_or _ _ h3]; exact h3
      · intro i hi
        rw [hget, fix_or _ _ h3] at hi
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := (h4 i hi).1; omega, (h4 i hi).2⟩
  · intro j hj hop
    simp only [List.length_map] at hj
    rw [hget, fix_op, List.getD_eq_getElem _ _ hj] at hop
    obtain ⟨t, acc, hin, hcase⟩ := hand j hj hop
    have hbt : t < x1 + x2 + j := hreads j hj t (by rw [hin]; simp)
    have hba : acc < x1 + x2 + j := hreads j hj acc (by rw [hin]; simp)
    rw [hget, List.getD_eq_getElem _ _ hj]
    rcases hcase with ⟨ht, hp⟩ | ⟨ht1, ht2, hp⟩
    · refine ⟨acc, t, ?_, ?_, ?_⟩
      · unfold fix
        rw [if_pos (by simp [hop, isAndOp, hin, ht])]
        simp [hin]
      · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, pureW_side _ _ _ _ _ ⟨Nat.zero_le _, ht⟩⟩
    · refine ⟨t, acc, ?_, ?_, ?_⟩
      · unfold fix
        rw [if_neg (by simp [hin]; omega)]
        exact hin
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, pureW_side _ _ _ _ _ ⟨ht1, ht2⟩⟩
      · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp⟩
