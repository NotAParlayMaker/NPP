import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3243

-- The wire list of a gate list started on the list w.
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_app (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length
  | [], w => by simp [run]
  | g :: gs, w => by rw [run_cons, run_len gs]; simp; omega

theorem run_pre : ∀ (gs : List Gate) (w : List Bool) (r : ℕ), r < w.length →
    (run gs w).getD r false = w.getD r false
  | [], _, _, _ => rfl
  | g :: gs, w, r, hr => by
    rw [run_cons, run_pre gs _ r (by simp; omega), List.getD_append _ _ _ _ hr]

theorem run_last (gs : List Gate) (g : Gate) (w : List Bool) :
    (run (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (run gs w).getD i false) := by
  rw [run_app, run_cons]
  have h := run_len gs w
  show ((run gs w) ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)]).getD _ false = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [h]

-- The OR chain of a block: wire B + i holds the OR of v1 and the first i + 1 later leaves.
def chainIn (B v1 k : ℕ) (i : ℕ) : ℕ := (v1 :: (List.range k).map (fun j => B + j)).getD i 0

def chain (B v1 : ℕ) (rest : List ℕ) (k : ℕ) : List Gate :=
  (List.range k).map fun i => ⟨GateOp.or, [chainIn B v1 rest.length i, rest.getD i 0]⟩

theorem chainIn_zero (B v1 k : ℕ) : chainIn B v1 k 0 = v1 := rfl

theorem chainIn_succ (B v1 k i : ℕ) (hi : i < k) : chainIn B v1 k (i + 1) = B + i := by
  simp [chainIn, List.getD_eq_getElem?_getD, hi]

theorem chain_run (B v1 : ℕ) (rest : List ℕ) (w : List Bool) (hw : w.length = B)
    (hv : v1 < B) (hr : ∀ r ∈ rest, r < B) :
    ∀ k ≤ rest.length, (run (chain B v1 rest k) w).length = B + k ∧
      ∀ i < k, (run (chain B v1 rest k) w).getD (B + i) false =
        (w.getD v1 false || (rest.take (i + 1)).any fun r => w.getD r false) := by
  intro k
  induction k with
  | zero => intro _; simp [chain, run, hw]
  | succ k ih =>
    intro hk
    obtain ⟨hl, hv'⟩ := ih (by omega)
    have hk' : k < rest.length := by omega
    have hsplit : chain B v1 rest (k + 1) = chain B v1 rest k ++
        [⟨GateOp.or, [chainIn B v1 rest.length k, rest.getD k 0]⟩] := by
      simp [chain, List.range_succ]
    have hrk : rest.getD k 0 < B := by
      rw [List.getD_eq_getElem _ _ hk']; exact hr _ (List.getElem_mem hk')
    have hcl : (chain B v1 rest k).length = k := by simp [chain]
    have hpre : ∀ r < B, (run (chain B v1 rest k) w).getD r false = w.getD r false :=
      fun r hrB => run_pre _ _ _ (by rw [hw]; exact hrB)
    rw [hsplit]
    refine ⟨by rw [run_len]; simp [hcl, hw], ?_⟩
    intro i hi
    by_cases hik : i < k
    · rw [run_app, run_pre _ _ _ (by rw [hl]; omega), hv' i hik]
    · rw [show i = k by omega]
      have h := run_last (chain B v1 rest k) ⟨GateOp.or, [chainIn B v1 rest.length k, rest.getD k 0]⟩ w
      rw [hw, hcl] at h
      rw [h]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [hpre _ hrk]
      cases k with
      | zero =>
        rw [chainIn_zero, hpre _ hv]
        have h0 : 0 < rest.length := by omega
        obtain ⟨r0, rs, rfl⟩ : ∃ r0 rs, rest = r0 :: rs := List.exists_cons_of_length_pos h0
        simp
      | succ k =>
        rw [chainIn_succ B v1 rest.length k (by omega), hv' k (by omega)]
        simp [List.take_succ, List.getElem?_eq_getElem hk', List.getD_eq_getElem _ _ hk', Bool.or_assoc]


-- One block: the OR chain, the AND with the owner, and the join with wire a unless it leads.
theorem block_eq (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    blockGates B a t v1 rest lead = chain B v1 rest rest.length ++
      (⟨GateOp.and, [t, chainIn B v1 rest.length rest.length]⟩ ::
        (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩])) := rfl

theorem block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  rw [block_eq]; cases lead <;> simp [chain]

def bval (w : List Bool) (st : ℕ × List ℕ) : Bool := w.getD st.1 false && st.2.any fun r => w.getD r false

theorem any_eq_of {α : Type} (l : List α) (p q : α → Bool) (h : ∀ r ∈ l, p r = q r) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x List.mem_cons_self, ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]

theorem block_run (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (w : List Bool) (hw : w.length = B)
    (ht : t < B) (hv : v1 < B) (hr : ∀ r ∈ rest, r < B) (ha : lead = false → a < B) :
    (run (blockGates B a t v1 rest lead) w).getD (B + (blockGates B a t v1 rest lead).length - 1) false =
      ((if lead then false else w.getD a false) || bval w (t, v1 :: rest)) := by
  obtain ⟨hl, hv'⟩ := chain_run B v1 rest w hw hv hr rest.length le_rfl
  have hcl : (chain B v1 rest rest.length).length = rest.length := by simp [chain]
  have hpre : ∀ r < B, (run (chain B v1 rest rest.length) w).getD r false = w.getD r false :=
    fun r hrB => run_pre _ _ _ (by rw [hw]; exact hrB)
  let gA : Gate := ⟨GateOp.and, [t, chainIn B v1 rest.length rest.length]⟩
  let gO : Gate := ⟨GateOp.or, [a, B + rest.length]⟩
  have hlast : (run (chain B v1 rest rest.length) w).getD (chainIn B v1 rest.length rest.length) false =
      (v1 :: rest).any fun r => w.getD r false := by
    rcases Nat.eq_zero_or_pos rest.length with h0 | hpos
    · have h0' : rest = [] := List.eq_nil_of_length_eq_zero h0
      have : chainIn B v1 rest.length rest.length = v1 := by simp [chainIn, h0]
      rw [this, hpre _ hv, h0']
      simp
    · have hc : chainIn B v1 rest.length rest.length = B + (rest.length - 1) := by
        have := chainIn_succ B v1 rest.length (rest.length - 1) (by omega)
        rwa [Nat.sub_add_cancel hpos] at this
      rw [hc, hv' _ (by omega), Nat.sub_add_cancel hpos, List.take_of_length_le le_rfl]
      simp
  have hand : (run (chain B v1 rest rest.length ++ [gA]) w).getD (B + rest.length) false =
      bval w (t, v1 :: rest) := by
    have h := run_last (chain B v1 rest rest.length) gA w
    rw [hw, hcl] at h
    rw [h]
    simp only [gA, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, bval]
    rw [hpre _ ht, hlast]
  have hal : (chain B v1 rest rest.length ++ [gA]).length = rest.length + 1 := by simp [hcl]
  cases lead
  · have hsplit : blockGates B a t v1 rest false = (chain B v1 rest rest.length ++ [gA]) ++ [gO] := by
      rw [block_eq]; simp [gA, gO]
    rw [hsplit]
    have h := run_last (chain B v1 rest rest.length ++ [gA]) gO w
    rw [hw, hal] at h
    have hidx : B + ((chain B v1 rest rest.length ++ [gA]) ++ [gO]).length - 1 = B + (rest.length + 1) := by
      simp [hcl]
    rw [hidx, h]
    simp only [gO, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false]
    rw [run_pre _ _ _ (by rw [hw]; exact ha rfl), hand]
    rfl
  · have hsplit : blockGates B a t v1 rest true = chain B v1 rest rest.length ++ [gA] := by
      rw [block_eq]; simp [gA]
    rw [hsplit, hal, show B + (rest.length + 1) - 1 = B + rest.length by omega, hand]
    simp

theorem cover_nil (B : ℕ) (lead : Bool) (a : ℕ) : ∀ own : List (ℕ × List ℕ),
    coverGatesB B lead a own = [] → ∀ st ∈ own, st.2 = []
  | [], _ => by simp
  | (t, []) :: os, h => by
    intro st hst
    simp only [coverGatesB] at h
    rcases List.mem_cons.mp hst with rfl | hs
    · rfl
    · exact cover_nil B lead a os h st hs
  | (t, v1 :: rest) :: os, h => by
    simp only [coverGatesB] at h
    rw [block_eq] at h
    simp at h

-- All blocks: the last wire is the earlier wire a (unless leading) or some owner block.
theorem cover_run (n : ℕ) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
    w.length = B → n ≤ B → (∀ st ∈ own, st.1 < n ∧ ∀ r ∈ st.2, r < n) → (lead = false → a < B) →
    coverGatesB B lead a own ≠ [] →
    (run (coverGatesB B lead a own) w).getD (B + (coverGatesB B lead a own).length - 1) false =
      ((if lead then false else w.getD a false) || own.any (bval w)) := by
  intro own
  induction own with
  | nil => intro B lead a w _ _ _ _ h; simp [coverGatesB] at h
  | cons st os ih =>
    intro B lead a w hw hn hst ha hne
    obtain ⟨t, ls⟩ := st
    match ls with
    | [] =>
      have := ih B lead a w hw hn (fun s hs => hst s (List.mem_cons_of_mem _ hs)) ha (by simpa [coverGatesB] using hne)
      simp only [coverGatesB] at this ⊢
      rw [this]; simp [bval]
    | v1 :: rest =>
      have h0 := hst (t, v1 :: rest) List.mem_cons_self
      have hblk := block_run B a t v1 rest lead w hw (by have := h0.1; omega)
        (by have := h0.2 v1 (by simp); omega) (fun r hr => by have := h0.2 r (by simp [hr]); omega) ha
      have hbll := block_len B a t v1 rest lead
      have hw'l : (run (blockGates B a t v1 rest lead) w).length = B + (blockGates B a t v1 rest lead).length := by
        rw [run_len, hw]
      have hsame : ∀ s ∈ os, bval (run (blockGates B a t v1 rest lead) w) s = bval w s := by
        intro s hs
        have h1 := hst s (List.mem_cons_of_mem _ hs)
        simp only [bval]
        rw [run_pre _ _ _ (by rw [hw]; omega)]
        congr 1
        exact any_eq_of _ _ _ (fun r hr => run_pre _ _ _ (by rw [hw]; have := h1.2 r hr; omega))
      simp only [coverGatesB]
      by_cases hrest : coverGatesB (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1) os = []
      · rw [hrest, List.append_nil, hblk]
        have hos : os.any (bval w) = false := by
          have hz := cover_nil _ _ _ os hrest
          rw [List.any_eq_false]
          intro s hs
          simp [bval, hz s hs]
        simp [hos, List.any_cons]
      · have ihr := ih _ false _ (run (blockGates B a t v1 rest lead) w) hw'l (by omega)
          (fun s hs => hst s (List.mem_cons_of_mem _ hs)) (fun _ => by omega) hrest
        rw [run_app]
        rw [show B + (blockGates B a t v1 rest lead ++ coverGatesB (B + (blockGates B a t v1 rest lead).length) false
            (B + (blockGates B a t v1 rest lead).length - 1) os).length - 1 =
          B + (blockGates B a t v1 rest lead).length + (coverGatesB (B + (blockGates B a t v1 rest lead).length) false
            (B + (blockGates B a t v1 rest lead).length - 1) os).length - 1 by simp; omega, ihr]
        simp only [if_false, Bool.false_eq_true, Bool.false_or, hblk, List.any_cons]
        rw [any_eq_of _ _ _ hsame]
        cases lead <;> simp [Bool.or_assoc]


theorem cover_len : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    (∀ st ∈ own, st.2 ≠ []) →
    (coverGatesB B lead a own).length + (if lead = true ∧ own ≠ [] then 1 else 0) =
      (own.map fun st => st.2.length).sum + own.length
  | [], _, _, _, _ => by simp [coverGatesB]
  | (t, []) :: os, _, _, _, h => absurd rfl (h (t, []) List.mem_cons_self)
  | (t, v1 :: rest) :: os, B, lead, a, h => by
    have ih := cover_len os (B + (blockGates B a t v1 rest lead).length) false
      (B + (blockGates B a t v1 rest lead).length - 1) (fun s hs => h s (List.mem_cons_of_mem _ hs))
    simp only [coverGatesB, List.length_append, block_len] at ih ⊢
    cases lead <;> simp at ih ⊢ <;> omega

theorem ofFn_getD {m : ℕ} (x : Fin m → Bool) (r : ℕ) (hr : r < m) : (List.ofFn x).getD r false = x ⟨r, hr⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_ofFn]

end PEqualNP.Outside.L_meta_3243

open PEqualNP.Outside.L_meta_3243 in
theorem PEqualNP.Outside.L_meta_3243 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  intro P L I _ own
  dsimp only
  intro hst hI
  have hne : ∀ st ∈ own, st.2 ≠ [] := fun st h => (hst st h).1
  have hb : ∀ st ∈ own, st.1 < P + L ∧ ∀ r ∈ st.2, r < P + L := by
    intro st h
    rcases (hst st h).2 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨by omega, fun r hr => (h2 r hr).2⟩
    · exact ⟨h2, fun r hr => by have := h3 r hr; omega⟩
  -- the function of the stars is the incidence function
  have hfun : ∀ x : Fin (P + L) → Bool, own.any (bval (List.ofFn x)) =
      decide (∃ (p : Fin P) (l : Fin L), I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff, List.any_eq_true]
    constructor
    · rintro ⟨⟨c, ls⟩, hm, hv⟩
      simp only [bval, Bool.and_eq_true, List.any_eq_true] at hv
      obtain ⟨hc, r, hr, hrv⟩ := hv
      rcases (hst _ hm).2 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · have hr2 := h2 r hr
        refine ⟨⟨c, h1⟩, ⟨r - P, by omega⟩, (hI _ _).mpr ⟨_, hm, Or.inl ⟨rfl, by simpa [show P + (r - P) = r by omega] using hr⟩⟩, ?_, ?_⟩
        · rw [ofFn_getD x c (by omega)] at hc; simpa using hc
        · rw [ofFn_getD x r (by omega)] at hrv
          have : (Fin.natAdd P ⟨r - P, by omega⟩ : Fin (P + L)) = ⟨r, by omega⟩ := by ext; simp; omega
          rw [this]; exact hrv
      · have hr3 := h3 r hr
        refine ⟨⟨r, hr3⟩, ⟨c - P, by omega⟩, (hI _ _).mpr ⟨_, hm, Or.inr ⟨by simp; omega, hr⟩⟩, ?_, ?_⟩
        · rw [ofFn_getD x r (by omega)] at hrv; simpa using hrv
        · rw [ofFn_getD x c (by omega)] at hc
          have : (Fin.natAdd P ⟨c - P, by omega⟩ : Fin (P + L)) = ⟨c, by omega⟩ := by ext; simp; omega
          rw [this]; exact hc
    · rintro ⟨p, l, hpl, hx1, hx2⟩
      obtain ⟨st, hm, hcase⟩ := (hI p l).mp hpl
      refine ⟨st, hm, ?_⟩
      simp only [bval, Bool.and_eq_true, List.any_eq_true]
      have e1 : (List.ofFn x).getD p false = true := by
        rw [ofFn_getD x p (by omega)]
        have : (⟨p, by omega⟩ : Fin (P + L)) = Fin.castAdd L p := by ext; simp
        rw [this]; exact hx1
      have e2 : (List.ofFn x).getD (P + l) false = true := by
        rw [ofFn_getD x (P + l) (by omega)]
        have : (⟨P + l, by omega⟩ : Fin (P + L)) = Fin.natAdd P l := by ext; simp
        rw [this]; exact hx2
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [h1]; exact e1, _, h2, e2⟩
      · exact ⟨by rw [h1]; exact e2, _, h2, e1⟩
  unfold coverCircuitB
  split_ifs with hg
  · -- no gate at all: no star, no incident pair
    have hown : own = [] := by
      cases own with
      | nil => rfl
      | cons st os =>
        exfalso
        exact hne st List.mem_cons_self (cover_nil _ _ _ (st :: os) hg st List.mem_cons_self)
    subst hown
    refine ⟨by simp [Circuit.size], fun x => ?_⟩
    rw [← hfun x]
    show (List.ofFn x).getD (P + L) false = _
    rw [List.getD_eq_default _ _ (by simp)]
    rfl
  · have hown : own ≠ [] := by rintro rfl; exact hg (by simp [coverGatesB])
    refine ⟨?_, fun x => ?_⟩
    · have := cover_len own (P + L) true 0 hne
      simp only [hown, ne_eq, not_false_eq_true, and_self, if_true] at this
      simp only [Circuit.size]
      omega
    · rw [← hfun x]
      have := cover_run (P + L) own (P + L) true 0 (List.ofFn x) (by simp) le_rfl hb (by simp) hg
      simp only [if_true, Bool.false_or] at this
      exact this
