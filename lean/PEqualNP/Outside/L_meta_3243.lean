import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3243_aux

lemma block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

lemma gates_length_false : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ), (∀ p ∈ own, p.2 ≠ []) →
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

lemma circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (hne : own ≠ [])
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
      rw [ite_eq_right hnn]
      simp only [hgl, List.map_cons, List.sum_cons, List.length_cons]
      omega

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_app (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp [step]
    · simp [hl]

lemma getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

lemma getD_app_right {w t : List Bool} {i : ℕ} :
    (w ++ t).getD (w.length + i) false = t.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

lemma getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst h
  simp

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_app gs w
  rw [ht, List.length_append, hl]

lemma fold_keep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_app gs w
  rw [ht, getD_app_left h]

lemma any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.any_cons]
    rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]

def cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
  w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

lemma chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
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
      simp [List.getD_eq_getElem?_getD, hj]
    rw [e1, ← hw, getD_app_right]
    simp [List.getD_eq_getElem?_getD]

lemma chain (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
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
    simp only [GateOp.eval]
    rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
    simp only [cv, List.take_add_one,
      List.any_append, List.any_cons, List.any_nil, Bool.or_false, id]
    simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

lemma block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
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
      · simp only [List.all_cons, List.all_nil]
        rw [htW, hr, hcvr]
        simp
      · simp [hLl, hw]
    · simp [hLl, hw]

def F (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

lemma gates_nil_F (x : List Bool) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
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

lemma main (n : ℕ) (x : List Bool) :
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

lemma circuit_fun (n : ℕ) (own : List (ℕ × List ℕ))
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

lemma read_input {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

end PEqualNP.Outside.L_meta_3243_aux

open PEqualNP.Outside.L_meta_3243_aux

theorem PEqualNP.Outside.L_meta_3243 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  intro m n R inst own
  dsimp only
  intro hown hrel
  constructor
  · by_cases he : own = []
    · subst own
      rfl
    · have hs := circuit_size (m + n) own he (fun p hp => (hown p hp).1)
      omega
  · intro x
    have bounds : ∀ p ∈ own, p.1 < m + n ∧ ∀ w ∈ p.2, w < m + n := by
      intro p hp
      rcases (hown p hp).2 with ⟨hc, hw⟩ | ⟨_, hc, hw⟩
      · exact ⟨by omega, fun w h => (hw w h).2⟩
      · exact ⟨hc, fun w h => by have := hw w h; omega⟩
    change (coverCircuitB (m + n) own).eval (List.ofFn x) = _
    rw [Bool.eq_iff_iff, circuit_fun _ _ bounds, decide_eq_true_iff]
    have point (i : Fin m) : (List.ofFn x).getD i.val false = x (Fin.castAdd n i) :=
      read_input x (Fin.castAdd n i)
    have line (j : Fin n) : (List.ofFn x).getD (m + j.val) false = x (Fin.natAdd m j) :=
      read_input x (Fin.natAdd m j)
    constructor
    · rintro ⟨p, hp, hc, w, hw, hv⟩
      rcases (hown p hp).2 with ⟨hleft, hright⟩ | ⟨hlo, hhi, hleft⟩
      · obtain ⟨hlo, hhi⟩ := hright w hw
        let i : Fin m := ⟨p.1, hleft⟩
        let j : Fin n := ⟨w - m, by omega⟩
        have hj : m + j.val = w := by dsimp [j]; omega
        refine ⟨i, j, (hrel i j).2 ⟨p, hp, Or.inl ⟨rfl, hj ▸ hw⟩⟩, ?_, ?_⟩
        · rw [← point i]; exact hc
        · rwa [← line j, hj]
      · let i : Fin m := ⟨w, hleft w hw⟩
        let j : Fin n := ⟨p.1 - m, by omega⟩
        have hj : m + j.val = p.1 := by dsimp [j]; omega
        refine ⟨i, j, (hrel i j).2 ⟨p, hp, Or.inr ⟨hj.symm, hw⟩⟩, ?_, ?_⟩
        · rw [← point i]; exact hv
        · rwa [← line j, hj]
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨p, hp, h | h⟩ := (hrel i j).1 hij
      · refine ⟨p, hp, ?_, m + j.val, h.2, ?_⟩
        · rwa [h.1, point]
        · rwa [line]
      · refine ⟨p, hp, ?_, i.val, h.2, ?_⟩
        · rwa [h.1, line]
        · rwa [point]
