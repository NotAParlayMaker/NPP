import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2050
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- The cover evaluation and size lemmas are adapted from this project's
-- CoverCircB and CoverCircB2 modules.




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


def safeGate (N B : ℕ) (g : Gate) : Prop :=
  (∀ i ∈ g.inputs, i < B) ∧ (g.op = GateOp.and → ∃ i ∈ g.inputs, i < N)

def safe (N B : ℕ) : List Gate → Prop
  | [] => True
  | g :: gs => safeGate N B g ∧ safe N (B+1) gs

theorem append_safe {N B} (xs ys : List Gate) (hx : safe N B xs) (hy : safe N (B+xs.length) ys) :
    safe N B (xs++ys) := by
  induction xs generalizing B with
  | nil => simpa using hy
  | cons g xs ih =>
    exact ⟨hx.1,ih hx.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hy)⟩

theorem nth_safe {N B} {xs : List Gate} (h : safe N B xs) (j : ℕ) (hj : j < xs.length) :
    safeGate N (B+j) xs[j] := by
  induction xs generalizing B j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => exact h.1
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih h.2 j hj'

theorem range_safe {N B} (f : ℕ → Gate) (k : ℕ)
    (h : ∀ i < k, safeGate N (B+i) (f i)) : safe N B ((List.range k).map f) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [List.range_succ,List.map_append]
    apply append_safe
    · exact ih (fun i hi => h i (by omega))
    · exact ⟨by simpa using h k (by omega), trivial⟩

theorem chain_input (B v k i : ℕ) (hv : v < B) (hi : i ≤ k) :
    ((v :: (List.range k).map (fun j => B+j)).getD i 0) < B+i := by
  cases i with
  | zero => simpa using hv
  | succ i =>
    have h : i < k := by omega
    simp [List.getD_eq_getElem?_getD,h]

theorem block_safe (N B a t v : ℕ) (rest : List ℕ) (lead : Bool)
    (ht : t < N) (hN : N ≤ B) (hv : v < B) (hr : ∀ i ∈ rest, i < B)
    (ha : lead = false → a < B) : safe N B (blockGates B a t v rest lead) := by
  unfold blockGates
  apply append_safe
  · apply range_safe
    intro j hj
    refine ⟨?_,by simp⟩
    have h1 := chain_input B v rest.length j hv (by omega)
    have hm : rest.getD j 0 ∈ rest := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    have h2 := hr _ hm
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact h1
    · exact lt_of_lt_of_le h2 (Nat.le_add_right _ _)
  · simp only [List.length_map,List.length_range]
    refine ⟨⟨?_,?_⟩,?_⟩
    · have h1 := chain_input B v rest.length rest.length hv le_rfl
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · omega
      · exact h1
    · exact fun _ => ⟨t,by simp,ht⟩
    · cases lead with
      | true => trivial
      | false =>
        refine ⟨⟨?_,by simp⟩,trivial⟩
        have := ha rfl
        simp; omega


theorem all_safe (N B : ℕ) (lead : Bool) (a : ℕ) (os : List (ℕ × List ℕ))
    (hB : N+N ≤ B) (ha : lead = false → a < B)
    (own : ∀ z ∈ os, z.1 < N ∧ ∀ i ∈ z.2, i < N+N) :
    safe N B (coverGatesB B lead a os) := by
  induction os generalizing B lead a with
  | nil => trivial
  | cons z os ih =>
    obtain ⟨t,vs⟩ := z
    have hnow := own (t,vs) List.mem_cons_self
    have htail : ∀ z ∈ os, z.1 < N ∧ ∀ i ∈ z.2, i < N+N :=
      fun z h => own _ (List.mem_cons_of_mem _ h)
    cases vs with
    | nil => exact ih B lead a hB ha htail
    | cons v rest =>
      simp only [coverGatesB]
      apply append_safe
      · apply block_safe N B a t v rest lead hnow.1 (by omega) _ _ ha
        · exact lt_of_lt_of_le (hnow.2 v List.mem_cons_self) hB
        · exact fun i hi => lt_of_lt_of_le (hnow.2 i (List.mem_cons_of_mem _ hi)) hB
      · apply ih _ false _ (by omega) _ htail
        intro _
        have hpos : 0 < (blockGates B a t v rest lead).length := by
          simp [blockGates]
        omega

theorem degree_on_raw (C : Circuit) (N i : ℕ) (hi : i < N) :
    (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD i 0 = 0 := by
  let step := fun (w : List ℕ) (g : Gate) => w ++ [g.lineDegree w]
  have keep (gs : List Gate) (w : List ℕ) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j 0 = w.getD j 0 := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]
      · simp [step]; omega
  unfold Circuit.lineDegrees
  change (List.foldl step _ _).getD i 0 = _
  rw [keep]
  · have h : i < N+N := by omega
    simp [List.getD_eq_getElem?_getD,h,show ¬ N ≤ i by omega]
  · simp; omega


end PEqualNP.Outside.L_meta_2050

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2050

theorem PEqualNP.Outside.L_meta_2050 : ∀ (q271 N271 : ℕ) (I271 : Fin N271 → Fin N271 → Prop) [DecidableRel I271], 2 ≤ q271 → N271 = q271 ^ 2 + q271 + 1 → (∀ l271 : Fin N271, (Finset.univ.filter (fun p271 => I271 p271 l271)).card = q271 + 1) → (∀ pa271 pb271 : Fin N271, pa271 ≠ pb271 → ∃! lb271 : Fin N271, I271 pa271 lb271 ∧ I271 pb271 lb271) → ∃ C271 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g271 ∈ C271.gates, (g271.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g271.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g271.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N271 + N271) C271) ∧ (∀ j271 < C271.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i271 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).inputs, (C271.lineDegrees (N271 + N271) (Finset.Ico N271 (N271 + N271))).getD i271 0 = 0) ∨ (∀ h271 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).inputs, (C271.lineDegrees (N271 + N271) (Finset.range N271)).getD h271 0 = 0)) ∧ C271.size + 1 = (q271 + 2) * N271 ∧ (∀ x271 y271 : Fin N271 → Bool, PEqualNP.MetaComplexity.circuitFun (N271 + N271) C271 (Fin.append x271 y271) = decide (∃ p271x1 w271 : Fin N271, I271 p271x1 w271 ∧ x271 p271x1 = true ∧ y271 w271 = true)) := by
  intro q N I inst hq hN hcol hpair
  classical
  have hn1 : 1 < N := by nlinarith [sq_nonneg q]
  let row (p : Fin N) := (Finset.univ.filter (I p)).toList.map (fun l : Fin N => N + l.val)
  let entry (p : Fin N) : ℕ × List ℕ := (p.val,row p)
  let os := List.ofFn entry
  let C := coverCircuitB (N+N) os
  have rmem (p : Fin N) (w : ℕ) : w ∈ row p ↔ ∃ l : Fin N, I p l ∧ N+l.val=w := by
    simp [row]
  have own : ∀ z ∈ os, z.1 < N ∧ ∀ i ∈ z.2, i < N+N := by
    intro z hz
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hz
    refine ⟨p.isLt,?_⟩
    intro i hi
    obtain ⟨l,_,rfl⟩ := (rmem _ _).mp hi
    omega
  have own2 : ∀ z ∈ os, z.1 < N+N ∧ ∀ i ∈ z.2, i < N+N := by
    intro z hz
    exact ⟨by have := (own z hz).1; omega,(own z hz).2⟩
  have rowne (p : Fin N) : row p ≠ [] := by
    let p0 : Fin N := ⟨0,by omega⟩
    let p1 : Fin N := ⟨1,by omega⟩
    have h01 : p0 ≠ p1 := by intro h; have := congrArg Fin.val h; contradiction
    have ⟨t,ht⟩ : ∃ t : Fin N, p ≠ t := by
      by_cases h : p=p0
      · exact ⟨p1,h ▸ h01⟩
      · exact ⟨p0,h⟩
    obtain ⟨l,hl,_⟩ := hpair p t ht
    have hm := (rmem p _).mpr ⟨l,hl.1,rfl⟩
    rintro hh
    simpa [hh] using hm
  have osne : os ≠ [] := List.length_pos_iff.mp (by simp [os]; omega)
  have nonempty : ∀ z ∈ os, z.2 ≠ [] := by
    intro z hz
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hz
    exact rowne p
  have gates : C.gates = coverGatesB (N+N) true 0 os := by
    simp only [C,coverCircuitB]
    split_ifs with h
    · exact h.symm
    · rfl
  have hs : safe N (N+N) C.gates := by
    rw [gates]
    exact all_safe _ _ _ _ _ le_rfl (by simp) own
  have atj (j : ℕ) (hj : j < C.gates.length) :
      safeGate N (N+N+j) (NestedCover.gateAt C j) := by
    simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hj] using nth_safe hs j hj
  refine ⟨C,⟨?_,?_⟩,?_,?_,?_⟩
  · intro g hg
    rw [gates] at hg
    exact gates_shape _ _ _ _ g hg
  · intro j hj
    exact (atj j hj).1
  · intro j hj hAnd
    obtain ⟨i,hi,hn⟩ := (atj j hj).2 hAnd
    exact Or.inl ⟨i,hi,degree_on_raw C N i hn⟩
  · rw [show C = coverCircuitB (N+N) os from rfl,circuit_size _ _ osne nonempty]
    have sumrows : ∑ p : Fin N, (Finset.univ.filter (I p)).card = (q+1)*N := by
      calc
        _ = ∑ p : Fin N, ∑ l : Fin N, if I p l then 1 else 0 := by simp [Finset.sum_boole]
        _ = ∑ l : Fin N, ∑ p : Fin N, if I p l then 1 else 0 := Finset.sum_comm
        _ = _ := by simp [Finset.sum_boole,hcol,Nat.mul_comm]
    simp only [os,List.map_ofFn,List.sum_ofFn,List.length_ofFn,Function.comp_apply,entry,row,
      List.length_map,Finset.length_toList]
    rw [sumrows]
    ring
  · intro x y
    have left (p : Fin N) :
        (List.ofFn (Fin.append x y)).getD p.val false = x p := by
      rw [List.getD_eq_getElem _ _ (by simp <;> omega),List.getElem_ofFn]
      exact Fin.append_left x y p
    have right (l : Fin N) :
        (List.ofFn (Fin.append x y)).getD (N+l.val) false = y l := by
      rw [List.getD_eq_getElem _ _ (by simp <;> omega),List.getElem_ofFn]
      exact Fin.append_right x y l
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff]
    change (coverCircuitB (N+N) os).eval (List.ofFn (Fin.append x y)) = true ↔ _
    rw [circuit_fun _ _ own2]
    constructor
    · rintro ⟨z,hz,hx,w,hw,hwv⟩
      obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hz
      obtain ⟨l,hl,rfl⟩ := (rmem p w).mp hw
      exact ⟨p,l,hl,(left p).symm.trans hx,(right l).symm.trans hwv⟩
    · rintro ⟨p,l,hl,hx,hy⟩
      exact ⟨entry p,List.mem_ofFn.mpr ⟨p,rfl⟩,(left p).trans hx,N+l.val,
        (rmem p _).mpr ⟨l,hl,rfl⟩,(right l).trans hy⟩
