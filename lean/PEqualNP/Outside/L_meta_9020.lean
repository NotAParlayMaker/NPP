import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9020

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




def pw (n i : ℕ) : ℕ := if i < n then i else 2 * i
def qw (n i : ℕ) : ℕ := if i < n then n + i else 2 * i + 1

def g1 (n k : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | .and, l => ⟨.and, l.map (pw n)⟩
  | .or, l => ⟨.or, l.map (pw n)⟩
  | _, [] => ⟨.and, []⟩
  | _, a :: _ => if a < n + k then ⟨.or, [qw n a]⟩ else ⟨.and, []⟩

def g2 (n k : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | .and, l => if l.all (fun i => decide (i < n + k)) then ⟨.or, l.map (qw n)⟩ else ⟨.and, []⟩
  | .or, l => ⟨.and, (l.filter (fun i => decide (i < n + k))).map (qw n)⟩
  | _, [] => ⟨.or, []⟩
  | _, a :: _ => if a < n + k then ⟨.or, [pw n a]⟩ else ⟨.or, []⟩

def ev (g : Gate) (V : ℕ → Bool) : Bool := g.op.eval (g.inputs.map V)

theorem and_dual (l : List ℕ) (V : ℕ → Bool) : GateOp.or.eval (l.map fun i => !V i) = !(GateOp.and.eval (l.map V)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [GateOp.eval] at ih ⊢; cases V a <;> simp [ih]

theorem or_dual (l : List ℕ) (V : ℕ → Bool) (m : ℕ) (hV : ∀ i, m ≤ i → V i = false) :
    GateOp.and.eval ((l.filter (fun i => decide (i < m))).map fun i => !V i) = !(GateOp.or.eval (l.map V)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a < m
    · simp only [List.filter_cons, h, decide_true, if_true]
      simp [GateOp.eval] at ih ⊢; cases V a <;> simp [ih]
    · simp only [List.filter_cons, h, decide_false]
      have := hV a (by omega)
      simp [GateOp.eval] at ih ⊢; simp [this, ih]

theorem e1 (n k : ℕ) (g : Gate) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not) (V W : ℕ → Bool)
    (hV : ∀ i, n + k ≤ i → V i = false) (hp : ∀ i, W (pw n i) = V i) (hq : ∀ i, i < n + k → W (qw n i) = !V i) :
    ev (g1 n k g) W = ev g V ∧ ev (g2 n k g) W = !ev g V := by
  obtain ⟨op, l⟩ := g
  have hP : (l.map (pw n)).map W = l.map V := by
    rw [List.map_map]; exact List.map_congr_left fun i _ => hp i
  rcases hg with h | h | h <;> simp only at h <;> subst h
  · refine ⟨?_, ?_⟩
    · simp only [g1, ev, hP]
    · simp only [g2]
      split_ifs with ha
      · have : (l.map (qw n)).map W = l.map fun i => !V i := by
          rw [List.map_map]
          refine List.map_congr_left fun i hi => hq i ?_
          have := List.all_eq_true.mp ha i hi
          simpa using this
        simp only [ev, this, and_dual]
      · have : ∃ a ∈ l, V a = false := by
          simp only [List.all_eq_true, not_forall] at ha
          obtain ⟨a, hal, hh⟩ := ha
          exact ⟨a, hal, hV a (by simpa using hh)⟩
        obtain ⟨a, hal, hva⟩ := this
        have : GateOp.and.eval (l.map V) = false := by
          simp only [GateOp.eval, List.all_eq_false]
          exact ⟨V a, List.mem_map_of_mem hal, by simp [hva]⟩
        simp only [ev, this]; rfl
  · refine ⟨?_, ?_⟩
    · simp only [g1, ev, hP]
    · have : ((l.filter (fun i => decide (i < n + k))).map (qw n)).map W = (l.filter (fun i => decide (i < n + k))).map fun i => !V i := by
        rw [List.map_map]
        refine List.map_congr_left fun i hi => hq i ?_
        have := (List.mem_filter.mp hi).2
        simpa using this
      simp only [g2, ev, this, or_dual l V (n + k) hV]
  · rcases l with _ | ⟨a, l⟩
    · exact ⟨rfl, rfl⟩
    · refine ⟨?_, ?_⟩
      · simp only [g1]
        split_ifs with ha
        · simp [ev, GateOp.eval, hq a ha]
        · simp [ev, GateOp.eval, hV a (by omega)]
      · simp only [g2]
        split_ifs with ha
        · simp [ev, GateOp.eval, hp a]
        · simp [ev, GateOp.eval, hV a (by omega)]

theorem mono1 (n k : ℕ) (g : Gate) (h : g.inputs.length ≤ 2) : ((g1 n k g).op = .and ∨ (g1 n k g).op = .or) ∧ (g1 n k g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  simp only at h
  cases op <;> rcases l with _ | ⟨a, l⟩ <;> simp only [g1] <;> (try split_ifs) <;> simp at h ⊢ <;> omega

theorem mono2 (n k : ℕ) (g : Gate) (h : g.inputs.length ≤ 2) : ((g2 n k g).op = .and ∨ (g2 n k g).op = .or) ∧ (g2 n k g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  simp only at h
  have hf : ∀ (l : List ℕ) p, l.length ≤ 2 → (l.filter p).length ≤ 2 := fun l p h => (List.length_filter_le _ _).trans h
  cases op with
  | and => simp only [g2]; split_ifs <;> simp <;> exact h
  | or => exact ⟨Or.inl rfl, by show (List.map _ _).length ≤ 2; rw [List.length_map]; exact hf _ _ h⟩
  | _ => rcases l with _ | ⟨a, l⟩ <;> simp only [g2] <;> (try split_ifs) <;> simp

theorem pwl (n k i : ℕ) (h : i < n + k) : pw n i < 2 * (n + k) := by unfold pw; split_ifs <;> omega
theorem qwl (n k i : ℕ) (h : i < n + k) : qw n i < 2 * (n + k) := by unfold qw; split_ifs <;> omega

theorem live2 (n k : ℕ) (g : Gate) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not) : ∀ i ∈ (g2 n k g).inputs, i < 2 * (n + k) := by
  obtain ⟨op, l⟩ := g
  intro i hi
  rcases hg with h | h | h <;> simp only at h <;> subst h
  · simp only [g2] at hi
    split_ifs at hi with ha
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have := List.all_eq_true.mp ha j hj
      exact qwl _ _ _ (by simpa using this)
    · simp at hi
  · simp only [g2] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := (List.mem_filter.mp hj).2
    exact qwl _ _ _ (by simpa using this)
  · rcases l with _ | ⟨a, l⟩
    · simp [g2] at hi
    · simp only [g2] at hi
      split_ifs at hi with ha
      · simp only [List.mem_singleton] at hi; subst hi; exact pwl _ _ _ ha
      · simp at hi

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := List.getD_eq_default _ _ h

theorem build (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    ∃ hs : List Gate, hs.length = 2 * gs.length ∧ (∀ h ∈ hs, (h.op = .and ∨ h.op = .or) ∧ h.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool,
        (∀ i, (run hs (List.ofFn x ++ List.ofFn fun i => !x i)).getD (pw n i) false = (run gs (List.ofFn x)).getD i false) ∧
        (∀ i, i < n + gs.length → (run hs (List.ofFn x ++ List.ofFn fun i => !x i)).getD (qw n i) false = !(run gs (List.ofFn x)).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], rfl, by simp, fun x => ⟨fun i => ?_, fun i hi => ?_⟩⟩
    · show (List.ofFn x ++ _).getD (pw n i) false = (List.ofFn x).getD i false
      by_cases h : i < n
      · rw [pw, if_pos h]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, h]
      · rw [pw, if_neg h, getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
    · have h : i < n := by simpa using hi
      show (List.ofFn x ++ _).getD (qw n i) false = !(List.ofFn x).getD i false
      rw [qw, if_pos h]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h]
  | append_singleton gs g ih =>
    obtain ⟨hs, hl, hm, hx⟩ := ih fun g' hg' => hgs g' (by simp [hg'])
    have hg := hgs g (by simp)
    refine ⟨hs ++ [g1 n gs.length g] ++ [g2 n gs.length g], by simp [hl]; omega, ?_, fun x => ?_⟩
    · intro h hh
      simp only [List.mem_append, List.mem_singleton] at hh
      rcases hh with (hh | hh) | hh
      · exact hm h hh
      · subst hh; exact mono1 _ _ _ hg.2
      · subst hh; exact mono2 _ _ _ hg.2
    · obtain ⟨h1, h2⟩ := hx x
      have lV : (run gs (List.ofFn x)).length = n + gs.length := by rw [run_length, List.length_ofFn]
      have lW : (run hs (List.ofFn x ++ List.ofFn fun i => !x i)).length = 2 * (n + gs.length) := by
        rw [run_length, List.length_append, List.length_ofFn, List.length_ofFn, hl]; omega
      rw [run_snoc, run_snoc, run_snoc]
      generalize run gs (List.ofFn x) = V at *
      generalize run hs (List.ofFn x ++ List.ofFn fun i => !x i) = W at *
      obtain ⟨E1, E2⟩ := e1 n gs.length g hg.1 (fun i => V.getD i false) (fun i => W.getD i false)
        (fun i hi => getD_ge _ _ (by omega)) h1 h2
      have E2' : (g2 n gs.length g).op.eval ((g2 n gs.length g).inputs.map fun i =>
          (W ++ [(g1 n gs.length g).op.eval ((g1 n gs.length g).inputs.map fun i => W.getD i false)]).getD i false) = !ev g (fun i => V.getD i false) := by
        rw [← E2]
        unfold ev
        congr 1
        refine List.map_congr_left fun i hi => getD_lt _ _ _ ?_
        rw [lW]
        exact live2 n gs.length g hg.1 i hi
      unfold ev at E1 E2'
      rw [E2', E1]
      generalize g.op.eval (g.inputs.map fun i => V.getD i false) = b
      have hP : ∀ i, i < n + gs.length → pw n i < W.length := fun i hi => by unfold pw; split_ifs <;> omega
      have hQ : ∀ i, i < n + gs.length → qw n i < W.length := fun i hi => by unfold qw; split_ifs <;> omega
      have tP : ∀ c d : Bool, (W ++ [c] ++ [d]).getD (2 * (n + gs.length)) false = c := by
        intro c d
        rw [getD_lt _ _ _ (by simp [lW]), ← lW, getD_at]
      have tQ : ∀ c d : Bool, (W ++ [c] ++ [d]).getD (2 * (n + gs.length) + 1) false = d := by
        intro c d
        have : 2 * (n + gs.length) + 1 = (W ++ [c]).length := by simp [lW]
        rw [this, getD_at]
      have lo : ∀ (c d : Bool) t, t < W.length → (W ++ [c] ++ [d]).getD t false = W.getD t false := by
        intro c d t ht
        rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ ht]
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · rcases Nat.lt_trichotomy i (n + gs.length) with h | h | h
        · rw [lo _ _ _ (hP i h), h1, getD_lt _ _ _ (by omega)]
        · subst h
          rw [pw, if_neg (by omega), tP, ← lV, getD_at]
        · rw [pw, if_neg (by omega), getD_ge _ _ (by simp [lW]; omega), getD_ge _ _ (by simp [lV]; omega)]
      · rw [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_or_ge i (n + gs.length) with h | h
        · rw [lo _ _ _ (hQ i h), h2 i h, getD_lt _ _ _ (by omega)]
        · have : i = n + gs.length := by omega
          subst this
          rw [qw, if_neg (by omega), tQ, ← lV, getD_at]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9020

theorem PEqualNP.Outside.L_meta_9020 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.Represents.HasLitSize n f (2 * s) := by
  rintro n s f ⟨C, hC, hs, hf⟩
  obtain ⟨hs', hl, hm, hx⟩ := PEqualNP.Outside.L_meta_9020.build n C.gates (fun g hg => ⟨by simpa using (hC g hg).1, (hC g hg).2⟩)
  refine ⟨⟨hs', PEqualNP.Outside.L_meta_9020.pw n C.output⟩, ?_, ?_, fun x => ?_⟩
  · intro h hh
    simpa using hm h hh
  · show hs'.length ≤ 2 * s
    have : C.gates.length ≤ s := hs
    omega
  · rw [← hf x]
    exact (hx x).1 C.output
