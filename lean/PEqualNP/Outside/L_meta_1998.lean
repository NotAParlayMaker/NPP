import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1998

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem ofFn_getD {α : Type} {n : ℕ} (x : Fin n → α) (dflt : α) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i dflt = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def F {α : Type} (step : Gate → List α → α) (gs : List Gate) (d : List α) : List α :=
  gs.foldl (fun d g => d ++ [step g d]) d

theorem F_append {α : Type} (step : Gate → List α → α) (a b : List Gate) (d : List α) :
    F step (a ++ b) d = F step b (F step a d) := by
  simp [F, List.foldl_append]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, w, i :: is => ⟨GateOp.or, [acc, i]⟩ :: chain w (w + 1) is

def cfin : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | _, w, _ :: is => cfin w (w + 1) is

theorem chain_len : ∀ (ins : List ℕ) (acc w : ℕ), (chain acc w ins).length = ins.length
  | [], _, _ => rfl
  | _ :: is, _, w => by simp [chain, chain_len is]

theorem chain_or : ∀ (ins : List ℕ) (acc w : ℕ), ∀ g ∈ chain acc w ins,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chain]
  | i :: is, acc, w => by
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact chain_or is w (w + 1) g hg

theorem chain_spec {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
    (hstep : ∀ (a b : ℕ) (d : List α),
      step ⟨GateOp.or, [a, b]⟩ d = op (d.getD a dflt) (d.getD b dflt))
    (ins : List ℕ) : ∀ (acc w : ℕ) (d : List α), d.length = w → acc < w → (∀ i ∈ ins, i < w) →
      (F step (chain acc w ins) d).length = w + ins.length ∧
      (∀ i < w, (F step (chain acc w ins) d).getD i dflt = d.getD i dflt) ∧
      (F step (chain acc w ins) d).getD (cfin acc w ins) dflt =
        ins.foldl (fun v i => op v (d.getD i dflt)) (d.getD acc dflt) ∧
      cfin acc w ins < w + ins.length := by
  induction ins with
  | nil =>
    intro acc w d hw hacc _
    refine ⟨by simp [chain, F, hw], fun i _ => by simp [chain, F], by simp [chain, F, cfin],
      by simpa [cfin] using hacc⟩
  | cons i is ih =>
    intro acc w d hw hacc hins
    have hi : i < w := hins i (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih w (w + 1) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d])
      (by simp [hw]) (by omega) (fun k hk => by have := hins k (by simp [hk]); omega)
    have hF : F step (chain acc w (i :: is)) d =
        F step (chain w (w + 1) is) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]) := by
      simp [F, chain]
    have hpre : ∀ k < w, (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD k dflt = d.getD k dflt :=
      fun k hk => List.getD_append _ _ _ _ (by omega)
    have hd : (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD w dflt =
        op (d.getD acc dflt) (d.getD i dflt) := by
      rw [List.getD_append_right _ _ _ _ (by omega), hstep]
      simp [hw]
    have hc : cfin acc w (i :: is) = cfin w (w + 1) is := by simp [cfin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF, h1]; simp only [List.length_cons]; omega
    · intro k hk; rw [hF, h2 k (by omega), hpre k hk]
    · rw [hF, hc, h3, hd, List.foldl_cons]
      exact List.foldl_ext _ _ _ (fun v k hk => by rw [hpre k (hins k (by simp [hk]))])
    · rw [hc]; simp only [List.length_cons]; omega

def wstep (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wstep_or (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.or, [a, b]⟩ d = (d.getD a false || d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem wstep_and (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.and, [a, b]⟩ d = (d.getD a false && d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem foldl_or (f : ℕ → Bool) : ∀ (l : List ℕ) (a : Bool),
    l.foldl (fun v i => v || f i) a = (a || l.any f)
  | [], a => by simp
  | i :: is, a => by simp [foldl_or f is, Bool.or_assoc]

theorem F_one {α : Type} (step : Gate → List α → α) (g : Gate) (d : List α) :
    F step [g] d = d ++ [step g d] := rfl

theorem F_len {α : Type} (step : Gate → List α → α) : ∀ (gs : List Gate) (d : List α),
    (F step gs d).length = d.length + gs.length
  | [], d => by simp [F]
  | g :: gs, d => by
    have h := F_len step gs (d ++ [step g d])
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem F_pre {α : Type} (step : Gate → List α → α) (dflt : α) :
    ∀ (gs : List Gate) (d : List α) (i : ℕ), i < d.length →
      (F step gs d).getD i dflt = d.getD i dflt
  | [], _, _, _ => rfl
  | g :: gs, d, i, hi => by
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, F_pre step dflt gs (d ++ [step g d]) i (by rw [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

def sstep {n : ℕ} (g : Gate) (s : List (Finset (Fin n))) : Finset (Fin n) :=
  g.inputs.foldr (fun w acc => s.getD w ∅ ∪ acc) ∅

theorem sstep_two {n : ℕ} (op : GateOp) (a b : ℕ) (s : List (Finset (Fin n))) :
    sstep ⟨op, [a, b]⟩ s = s.getD a ∅ ∪ s.getD b ∅ := by
  simp [sstep]

def Q {n : ℕ} (M : Finset (Fin n)) (d : List (Finset (Fin n))) (b : List Gate) : Prop :=
  ∀ j < b.length, (∀ i ∈ (b.getD j ⟨GateOp.or, []⟩).inputs, i < d.length + j) ∧
    ((b.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
      ∃ x y, (b.getD j ⟨GateOp.or, []⟩).inputs = [x, y] ∧
        (((F sstep b d).getD x ∅ ⊆ M ∧ Disjoint ((F sstep b d).getD y ∅) M) ∨
          (Disjoint ((F sstep b d).getD x ∅) M ∧ (F sstep b d).getD y ∅ ⊆ M)))

theorem Q_app {n : ℕ} (M : Finset (Fin n)) (d : List (Finset (Fin n))) (a b : List Gate)
    (ha : Q M d a) (hb : Q M (F sstep a d) b) : Q M d (a ++ b) := by
  intro j hj
  rcases Nat.lt_or_ge j a.length with h | h
  · rw [List.getD_append _ _ _ _ h]
    obtain ⟨h1, h2⟩ := ha j h
    refine ⟨h1, fun hand => ?_⟩
    obtain ⟨x, y, hi, hz⟩ := h2 hand
    refine ⟨x, y, hi, ?_⟩
    have hx := h1 x (by rw [hi]; simp)
    have hy := h1 y (by rw [hi]; simp)
    rw [F_append, F_pre sstep ∅ b (F sstep a d) x (by rw [F_len]; omega),
      F_pre sstep ∅ b (F sstep a d) y (by rw [F_len]; omega)]
    exact hz
  · rw [List.getD_append_right _ _ _ _ h]
    have hj2 : j - a.length < b.length := by
      rw [List.length_append] at hj; omega
    obtain ⟨h1, h2⟩ := hb (j - a.length) hj2
    refine ⟨fun i hi => ?_, fun hand => ?_⟩
    · have := h1 i hi
      rw [F_len] at this; omega
    · obtain ⟨x, y, hi, hz⟩ := h2 hand
      exact ⟨x, y, hi, by rw [F_append]; exact hz⟩

theorem Q_two {n : ℕ} (M : Finset (Fin n)) (d : List (Finset (Fin n))) (op : GateOp) (a b : ℕ)
    (ha : a < d.length) (hb : b < d.length)
    (h2 : op = GateOp.and → (d.getD a ∅ ⊆ M ∧ Disjoint (d.getD b ∅) M) ∨
      (Disjoint (d.getD a ∅) M ∧ d.getD b ∅ ⊆ M)) : Q M d [⟨op, [a, b]⟩] := by
  intro j hj
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  show (∀ i ∈ [a, b], i < d.length + 0) ∧
    (op = GateOp.and → ∃ x y, [a, b] = [x, y] ∧
      (((F sstep [⟨op, [a, b]⟩] d).getD x ∅ ⊆ M ∧
          Disjoint ((F sstep [⟨op, [a, b]⟩] d).getD y ∅) M) ∨
        (Disjoint ((F sstep [⟨op, [a, b]⟩] d).getD x ∅) M ∧
          (F sstep [⟨op, [a, b]⟩] d).getD y ∅ ⊆ M)))
  refine ⟨fun i hi => ?_, fun hand => ⟨a, b, rfl, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> omega
  · rw [F_one, List.getD_append _ _ _ _ ha, List.getD_append _ _ _ _ hb]
    exact h2 hand

theorem Q_chain {n : ℕ} (M : Finset (Fin n)) : ∀ (ins : List ℕ) (acc w : ℕ)
    (d : List (Finset (Fin n))), d.length = w → acc < w → (∀ i ∈ ins, i < w) →
    Q M d (chain acc w ins)
  | [], _, _, _, _, _, _ => by
    intro j hj
    simp [chain] at hj
  | i :: is, acc, w, d, hw, hacc, hins => by
    have e : chain acc w (i :: is) = [⟨GateOp.or, [acc, i]⟩] ++ chain w (w + 1) is := rfl
    rw [e]
    apply Q_app
    · exact Q_two M d GateOp.or acc i (by omega) (by have := hins i (by simp); omega)
        (fun h => by cases h)
    · exact Q_chain M is w (w + 1) _ (by simp [F_len, hw]) (by omega)
        (fun k hk => by have := hins k (by simp [hk]); omega)

theorem foldl_union_pred {n : ℕ} (p : Finset (Fin n) → Prop)
    (hp : ∀ A B, p A → p B → p (A ∪ B)) (g : ℕ → Finset (Fin n)) :
    ∀ (l : List ℕ) (a : Finset (Fin n)), p a → (∀ i ∈ l, p (g i)) →
      p (l.foldl (fun v i => v ∪ g i) a)
  | [], _, ha, _ => ha
  | i :: is, a, ha, h => by
    rw [List.foldl_cons]
    exact foldl_union_pred p hp g is _ (hp _ _ ha (h i (by simp)))
      (fun k hk => h k (by simp [hk]))

def blk (c h : ℕ) (t : List ℕ) (w : ℕ) : List Gate :=
  chain h w t ++ [⟨GateOp.and, [cfin h w t, c]⟩]

theorem blk_len (c h : ℕ) (t : List ℕ) (w : ℕ) : (blk c h t w).length = t.length + 1 := by
  simp [blk, chain_len]

theorem blk_shape (c h : ℕ) (t : List ℕ) (w : ℕ) :
    ∀ g ∈ blk c h t w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  unfold blk at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨a, b⟩ := chain_or _ _ _ g hg
    exact ⟨Or.inr a, b⟩
  · exact ⟨Or.inl rfl, rfl⟩

theorem blk_Q {n : ℕ} (M : Finset (Fin n)) (c h : ℕ) (t : List ℕ) (w : ℕ)
    (d : List (Finset (Fin n))) (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w)
    (hz : ((∀ i ∈ h :: t, d.getD i ∅ ⊆ M) ∧ Disjoint (d.getD c ∅) M) ∨
      ((∀ i ∈ h :: t, Disjoint (d.getD i ∅) M) ∧ d.getD c ∅ ⊆ M)) :
    Q M d (blk c h t w) := by
  obtain ⟨c1, c2, c3, c4⟩ := chain_spec sstep ∅ (fun u v => u ∪ v)
    (fun a b d => sstep_two GateOp.or a b d) t h w d hw h1 h2
  unfold blk
  apply Q_app _ _ _ _ (Q_chain M t h w d hw h1 h2)
  refine Q_two M _ GateOp.and _ _ (by rw [c1]; exact c4) (by rw [c1]; omega) (fun _ => ?_)
  rw [c3, c2 c h3]
  rcases hz with ⟨za, zb⟩ | ⟨za, zb⟩
  · exact Or.inl ⟨foldl_union_pred (fun A => A ⊆ M) (fun A B hA hB => Finset.union_subset hA hB)
      (fun i => d.getD i ∅) t _ (za h (by simp)) (fun i hi => za i (by simp [hi])), zb⟩
  · exact Or.inr ⟨foldl_union_pred (fun A => Disjoint A M)
      (fun A B hA hB => Finset.disjoint_union_left.mpr ⟨hA, hB⟩)
      (fun i => d.getD i ∅) t _ (za h (by simp)) (fun i hi => za i (by simp [hi])), zb⟩

theorem blk_val (c h : ℕ) (t : List ℕ) (w : ℕ) (d : List Bool)
    (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w) (h3 : c < w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false =
      ((d.getD h false || t.any fun i => d.getD i false) && d.getD c false) := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec wstep false (fun u v => u || v) wstep_or t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, wstep_and, c3, c2 _ h3, foldl_or (fun i => d.getD i false)]

theorem blk_iff (n c h : ℕ) (t : List ℕ) (w : ℕ) (d x : List Bool)
    (hw : d.length = w) (hpre : ∀ i < n, d.getD i false = x.getD i false)
    (h1 : h < n) (h2 : ∀ i ∈ t, i < n) (hl : c < n) (hNw : n ≤ w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false = true ↔
      (x.getD c false = true ∧ ∃ i ∈ h :: t, x.getD i false = true) := by
  rw [blk_val c h t w d hw (by omega) (fun i hi => by have := h2 i hi; omega) (by omega),
    Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, hpre h (by omega),
    hpre c (by omega)]
  constructor
  · rintro ⟨hh | ⟨i, hi, hh⟩, hy⟩
    · exact ⟨hy, h, by simp, hh⟩
    · exact ⟨hy, i, by simp [hi], by rw [← hpre i (h2 i hi)]; exact hh⟩
  · rintro ⟨hy, i, hi, hh⟩
    refine ⟨?_, hy⟩
    rcases List.mem_cons.mp hi with e | hi2
    · rw [e] at hh; exact Or.inl hh
    · exact Or.inr ⟨i, hi2, by rw [hpre i (h2 i hi2)]; exact hh⟩

def G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : List (ℕ × ℕ × List ℕ) → List Gate
  | [] => blk s0.1 s0.2.1 s0.2.2 n
  | s :: r => G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length) ++
      [⟨GateOp.or, [n + (G n s0 r).length - 1, n + (G n s0 r).length + s.2.2.length]⟩]

theorem G_pos (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r, 0 < (G n s0 r).length
  | [] => by simp [G, blk_len]
  | s :: r => by simp [G]

theorem G_len (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    (G n s0 r).length + 1 = (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum
  | [] => by simp [G, blk_len]
  | s :: r => by
    have ih := G_len n s0 r
    simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    omega

theorem G_shape (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    ∀ g ∈ G n s0 r, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [] => by
    intro g hg
    simp only [G] at hg
    exact blk_shape _ _ _ _ g hg
  | s :: r => by
    intro g hg
    simp only [G, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact G_shape n s0 r g hg
    · exact blk_shape _ _ _ _ g hg
    · exact ⟨Or.inr rfl, rfl⟩

def Ok {n : ℕ} (M : Finset (Fin n)) (d : List (Finset (Fin n))) (s : ℕ × ℕ × List ℕ) : Prop :=
  s.1 < n ∧ (∀ i ∈ s.2.1 :: s.2.2, i < n) ∧
    (((∀ i ∈ s.2.1 :: s.2.2, d.getD i ∅ ⊆ M) ∧ Disjoint (d.getD s.1 ∅) M) ∨
      ((∀ i ∈ s.2.1 :: s.2.2, Disjoint (d.getD i ∅) M) ∧ d.getD s.1 ∅ ⊆ M))

theorem G_Q {n : ℕ} (M : Finset (Fin n)) (d0 : List (Finset (Fin n))) (hd0 : d0.length = n)
    (s0 : ℕ × ℕ × List ℕ) (h0 : Ok M d0 s0) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, Ok M d0 s) → Q M d0 (G n s0 r)
  | [], _ => by
    simp only [G]
    exact blk_Q M s0.1 s0.2.1 s0.2.2 n d0 hd0 (h0.2.1 _ (by simp))
      (fun i hi => h0.2.1 i (by simp [hi])) h0.1 h0.2.2
  | s :: r, hr => by
    have ih := G_Q M d0 hd0 s0 h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F sstep (G n s0 r) d0).length = n + (G n s0 r).length := by
      rw [F_len, hd0]
    have hz : ∀ i, i < n → (F sstep (G n s0 r) d0).getD i ∅ = d0.getD i ∅ := by
      intro i hi
      exact F_pre sstep ∅ _ _ i (by rw [hd0]; exact hi)
    have hpos := G_pos n s0 r
    simp only [G]
    apply Q_app
    · apply Q_app _ _ _ _ ih
      refine blk_Q M s.1 s.2.1 s.2.2 _ _ hL (by have := hs.2.1 s.2.1 (by simp); omega)
        (fun i hi => by have := hs.2.1 i (by simp [hi]); omega) (by have := hs.1; omega) ?_
      rw [hz _ hs.1]
      rcases hs.2.2 with ⟨za, zb⟩ | ⟨za, zb⟩
      · exact Or.inl ⟨fun i hi => by rw [hz i (hs.2.1 i hi)]; exact za i hi, zb⟩
      · exact Or.inr ⟨fun i hi => by rw [hz i (hs.2.1 i hi)]; exact za i hi, zb⟩
    · exact Q_two M _ GateOp.or _ _
        (by rw [F_len, List.length_append, blk_len, hd0]; omega)
        (by rw [F_len, List.length_append, blk_len, hd0]; omega)
        (fun h => by cases h)

theorem G_val (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List Bool) (hx : x.length = n)
    (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      ((F wstep (G n s0 r) x).getD (n + (G n s0 r).length - 1) false = true ↔
        ∃ s ∈ s0 :: r, x.getD s.1 false = true ∧ ∃ i ∈ s.2.1 :: s.2.2, x.getD i false = true)
  | [], _ => by
    have e : n + (G n s0 []).length - 1 = n + s0.2.2.length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    rw [blk_iff n s0.1 s0.2.1 s0.2.2 n x x hx (fun i _ => rfl) (h0.2 _ (by simp))
      (fun i hi => h0.2 i (by simp [hi])) h0.1 (le_refl _)]
    constructor
    · intro a
      exact ⟨s0, by simp, a⟩
    · rintro ⟨s, hs, a⟩
      rw [List.mem_singleton.mp hs] at a
      exact a
  | s :: r, hr => by
    have ih := G_val n s0 x hx h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F wstep (G n s0 r) x).length = n + (G n s0 r).length := by
      rw [F_len, hx]
    have hpre : ∀ i < n, (F wstep (G n s0 r) x).getD i false = x.getD i false :=
      fun i hi => F_pre wstep false _ _ i (by omega)
    have hb := blk_iff n s.1 s.2.1 s.2.2 (n + (G n s0 r).length)
      (F wstep (G n s0 r) x) x hL hpre (hs.2 _ (by simp)) (fun i hi => hs.2 i (by simp [hi]))
      hs.1 (by omega)
    have hL2 : (F wstep (G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length))
        x).length = n + (G n s0 r).length + s.2.2.length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have hpos := G_pos n s0 r
    have e : n + (G n s0 (s :: r)).length - 1 =
        n + (G n s0 r).length + s.2.2.length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, wstep_or, Bool.or_eq_true]
    rw [F_append, F_pre wstep false _ _ (n + (G n s0 r).length - 1)
      (by rw [hL]; omega), ih, hb]
    constructor
    · rintro (⟨s', hs', a⟩ | a)
      · refine ⟨s', ?_, a⟩
        simp only [List.mem_cons] at hs' ⊢
        tauto
      · exact ⟨s, by simp, a⟩
    · rintro ⟨s', hs', a⟩
      simp only [List.mem_cons] at hs'
      rcases hs' with h | h | h
      · exact Or.inl ⟨s', by simp [h], a⟩
      · rw [h] at a
        exact Or.inr a
      · exact Or.inl ⟨s', by simp [h], a⟩

def d0 (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => ({i} : Finset (Fin n))

theorem d0_len (n : ℕ) : (d0 n).length = n := by
  simp [d0]

theorem d0_getD (n : ℕ) (v : Fin n) : (d0 n).getD v.val ∅ = {v} := by
  unfold d0
  rw [ofFn_getD _ ∅ v.val v.isLt]

theorem core (n : ℕ) (M : Finset (Fin n)) (s0 : ℕ × ℕ × List ℕ) (r : List (ℕ × ℕ × List ℕ))
    (h0 : Ok M (d0 n) s0) (hr : ∀ s ∈ r, Ok M (d0 n) s) :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      NestedCover.ReadsBack n C ∧
      (∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
        ∃ a c, (NestedCover.gateAt C j).inputs = [a, c] ∧
          ((PEqualNP.SyntacticMultilinear.support n C a ⊆ M ∧
              Disjoint (PEqualNP.SyntacticMultilinear.support n C c) M) ∨
            (Disjoint (PEqualNP.SyntacticMultilinear.support n C a) M ∧
              PEqualNP.SyntacticMultilinear.support n C c ⊆ M))) ∧
      C.size + 1 = (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum ∧
      ∀ x : List Bool, x.length = n → (C.eval x = true ↔
        ∃ s ∈ s0 :: r, x.getD s.1 false = true ∧
          ∃ i ∈ s.2.1 :: s.2.2, x.getD i false = true) := by
  have hQ := G_Q M (d0 n) (d0_len n) s0 h0 r hr
  refine ⟨⟨G n s0 r, n + (G n s0 r).length - 1⟩, G_shape n s0 r, ?_, ?_, G_len n s0 r, ?_⟩
  · show ∀ j < (G n s0 r).length,
      ∀ i ∈ ((G n s0 r).getD j ⟨GateOp.or, []⟩).inputs, i < n + j
    intro j hj i hi
    have := (hQ j hj).1 i hi
    rw [d0_len] at this
    exact this
  · intro j hj hand
    exact (hQ j hj).2 hand
  · intro x hx
    exact G_val n s0 x hx ⟨h0.1, h0.2.1⟩ r (fun s hs => ⟨(hr s hs).1, (hr s hs).2.1⟩)

theorem main0 (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (M T : Finset (Fin n))
    (hM : ∀ u v : Fin n, K.Adj u v → (u ∈ M ↔ v ∉ M))
    (hT : ∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) (hE : 0 < K.edgeFinset.card) :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      NestedCover.ReadsBack n C ∧
      (∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
        ∃ a c, (NestedCover.gateAt C j).inputs = [a, c] ∧
          ((PEqualNP.SyntacticMultilinear.support n C a ⊆ M ∧
              Disjoint (PEqualNP.SyntacticMultilinear.support n C c) M) ∨
            (Disjoint (PEqualNP.SyntacticMultilinear.support n C a) M ∧
              PEqualNP.SyntacticMultilinear.support n C c ⊆ M))) ∧
      C.size ≤ K.edgeFinset.card + T.card - 1 ∧
      circuitFun n C = NestedCover.graphFun K ∅ := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : Fin n → Finset (Fin n),
      ∀ v u, u ∈ A v ↔ (K.Adj v u ∧ (u ∈ T → v < u)) :=
    ⟨fun v => Finset.univ.filter (fun u => K.Adj v u ∧ (u ∈ T → v < u)), fun v u => by simp⟩
  obtain ⟨T2, hT2⟩ : ∃ T2 : Finset (Fin n), ∀ v, v ∈ T2 ↔ (v ∈ T ∧ (A v).Nonempty) :=
    ⟨T.filter (fun v => (A v).Nonempty), fun v => by simp⟩
  have hctr : ∀ u v, K.Adj u v →
      ∃ c w, c ∈ T2 ∧ w ∈ A c ∧ ((c = u ∧ w = v) ∨ (c = v ∧ w = u)) := by
    intro u v huv
    have hne : u ≠ v := K.ne_of_adj huv
    have key : ∀ c w, K.Adj c w → c ∈ T → (w ∈ T → c < w) → c ∈ T2 ∧ w ∈ A c := by
      intro c w hcw hc hlt
      have hw : w ∈ A c := (hA c w).mpr ⟨hcw, hlt⟩
      exact ⟨(hT2 c).mpr ⟨hc, ⟨w, hw⟩⟩, hw⟩
    by_cases hu : u ∈ T
    · by_cases hv : v ∈ T
      · rcases lt_or_gt_of_ne hne with h | h
        · obtain ⟨a, b⟩ := key u v huv hu (fun _ => h)
          exact ⟨u, v, a, b, Or.inl ⟨rfl, rfl⟩⟩
        · obtain ⟨a, b⟩ := key v u huv.symm hv (fun _ => h)
          exact ⟨v, u, a, b, Or.inr ⟨rfl, rfl⟩⟩
      · obtain ⟨a, b⟩ := key u v huv hu (fun h => absurd h hv)
        exact ⟨u, v, a, b, Or.inl ⟨rfl, rfl⟩⟩
    · have hv : v ∈ T := (hT u v huv).resolve_left hu
      obtain ⟨a, b⟩ := key v u huv.symm hv (fun h => absurd h hu)
      exact ⟨v, u, a, b, Or.inr ⟨rfl, rfl⟩⟩
  have hcount : ∑ v ∈ T2, (A v).card ≤ K.edgeFinset.card := by
    have h1 : (T2.sigma A).card = ∑ v ∈ T2, (A v).card := Finset.card_sigma _ _
    rw [← h1]
    refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      have hp' : p ∈ T2.sigma A := hp
      have hp2 := Finset.mem_sigma.mp hp'
      have hadj2 : K.Adj p.1 p.2 := ((hA _ _).mp hp2.2).1
      exact SimpleGraph.mem_edgeFinset.mpr hadj2
    · intro p hp q hq hpq
      have hp' : p ∈ T2.sigma A := hp
      have hq' : q ∈ T2.sigma A := hq
      obtain ⟨a, b⟩ := p
      obtain ⟨c, d⟩ := q
      have hp2 := Finset.mem_sigma.mp hp'
      have hq2 := Finset.mem_sigma.mp hq'
      have hpq' : s(a, b) = s(c, d) := hpq
      rcases Sym2.eq_iff.mp hpq' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · subst e1
        subst e2
        rfl
      · exfalso
        have ha : a ∈ T := ((hT2 a).mp hp2.1).1
        have hc : c ∈ T := ((hT2 c).mp hq2.1).1
        have l1 : a < b := ((hA a b).mp hp2.2).2 (by rw [e2]; exact hc)
        have l2 : c < d := ((hA c d).mp hq2.2).2 (by rw [← e1]; exact ha)
        rw [← e1, ← e2] at l2
        exact lt_asymm l1 l2
  obtain ⟨star, hstar1, hstar2⟩ : ∃ star : Fin n → ℕ × ℕ × List ℕ, (∀ v, (star v).1 = v.val) ∧
      ∀ v, (A v).Nonempty → (star v).2.1 :: (star v).2.2 = (A v).toList.map Fin.val := by
    refine ⟨fun v => (v.val, ((A v).toList.map Fin.val).headD 0,
      ((A v).toList.map Fin.val).tail), fun v => rfl, fun v hne => ?_⟩
    show ((A v).toList.map Fin.val).headD 0 :: ((A v).toList.map Fin.val).tail =
      (A v).toList.map Fin.val
    cases h : (A v).toList.map Fin.val with
    | nil =>
      exfalso
      have h2 : (A v).toList = [] := List.map_eq_nil_iff.mp h
      exact hne.ne_empty (Finset.toList_eq_nil.mp h2)
    | cons a t => rfl
  have hmemS : ∀ v ∈ T2, ∀ i, i ∈ (star v).2.1 :: (star v).2.2 ↔ ∃ u, u ∈ A v ∧ u.val = i := by
    intro v hv i
    rw [hstar2 v ((hT2 v).mp hv).2, List.mem_map]
    simp only [Finset.mem_toList]
  have hOk : ∀ v ∈ T2, Ok M (d0 n) (star v) := by
    intro v hv
    refine ⟨by rw [hstar1]; exact v.isLt, ?_, ?_⟩
    · intro i hi
      obtain ⟨u, _, rfl⟩ := (hmemS v hv i).mp hi
      exact u.isLt
    · rw [hstar1, d0_getD]
      by_cases hvM : v ∈ M
      · right
        refine ⟨fun i hi => ?_, Finset.singleton_subset_iff.mpr hvM⟩
        obtain ⟨u, hu, rfl⟩ := (hmemS v hv i).mp hi
        rw [d0_getD]
        exact Finset.disjoint_singleton_left.mpr ((hM v u ((hA v u).mp hu).1).mp hvM)
      · left
        refine ⟨fun i hi => ?_, Finset.disjoint_singleton_left.mpr hvM⟩
        obtain ⟨u, hu, rfl⟩ := (hmemS v hv i).mp hi
        rw [d0_getD]
        refine Finset.singleton_subset_iff.mpr ?_
        by_contra hcon
        exact hvM ((hM v u ((hA v u).mp hu).1).mpr hcon)
  have hadj : ∃ u v, K.Adj u v := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hE
    induction e using Sym2.ind with
    | h u v =>
      have hadj2 : K.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      exact ⟨u, v, hadj2⟩
  obtain ⟨u1, v1, huv1⟩ := hadj
  obtain ⟨c1, _, hc1, _, _⟩ := hctr u1 v1 huv1
  cases hl : T2.toList with
  | nil =>
    exfalso
    have : T2 = ∅ := Finset.toList_eq_nil.mp hl
    rw [this] at hc1
    simp at hc1
  | cons v0 r0 =>
    have hall : ∀ v, v ∈ v0 :: r0 ↔ v ∈ T2 := by
      intro v
      rw [← hl, Finset.mem_toList]
    have hv0 : v0 ∈ T2 := (hall v0).mp (by simp)
    obtain ⟨C, q1, q2, q3, q4, q5⟩ := core n M (star v0) (r0.map star) (hOk v0 hv0)
      (by
        intro s hs
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hs
        exact hOk v ((hall v).mp (by simp [hv])))
    refine ⟨C, q1, q2, q3, ?_, ?_⟩
    · have hlen : ∀ v ∈ T2, (star v).2.2.length + 2 = (A v).card + 1 := by
        intro v hv
        have := congrArg List.length (hstar2 v ((hT2 v).mp hv).2)
        simp only [List.length_cons, List.length_map, Finset.length_toList] at this
        omega
      have hsum : (star v0).2.2.length + 2 + ((r0.map star).map fun s => s.2.2.length + 2).sum =
          ∑ v ∈ T2, ((A v).card + 1) := by
        rw [← Finset.sum_map_toList, hl, List.map_cons, List.sum_cons, hlen v0 hv0, List.map_map]
        congr 2
        apply List.map_congr_left
        intro v hv
        exact hlen v ((hall v).mp (List.mem_cons_of_mem _ hv))
      rw [hsum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at q4
      have hcard : T2.card ≤ T.card := Finset.card_le_card (fun v hv => ((hT2 v).mp hv).1)
      omega
    · funext x
      have hev := q5 (List.ofFn x) (by simp)
      have gx : ∀ v : Fin n, (List.ofFn x).getD v.val false = x v :=
        fun v => ofFn_getD x false v.val v.isLt
      have hg : NestedCover.graphFun K ∅ x = true ↔
          ∃ u v, K.Adj u v ∧ x u = true ∧ x v = true := by
        simp [NestedCover.graphFun]
      rw [Bool.eq_iff_iff, hg]
      show C.eval (List.ofFn x) = true ↔ _
      rw [hev]
      constructor
      · rintro ⟨s, hs, hc, i, hi, hxi⟩
        have hs' : s ∈ List.map star (v0 :: r0) := hs
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hs'
        have hv2 := (hall v).mp hv
        obtain ⟨u, hu, rfl⟩ := (hmemS v hv2 i).mp hi
        rw [hstar1, gx v] at hc
        rw [gx u] at hxi
        exact ⟨v, u, ((hA v u).mp hu).1, hc, hxi⟩
      · rintro ⟨u, v, huv, hxu, hxv⟩
        obtain ⟨c, w, hc, hw, hcw⟩ := hctr u v huv
        have hxc : x c = true := by
          rcases hcw with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1]; exact hxu
          · rw [e1]; exact hxv
        have hxw : x w = true := by
          rcases hcw with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e2]; exact hxv
          · rw [e2]; exact hxu
        have hsm : star c ∈ List.map star (v0 :: r0) :=
          List.mem_map.mpr ⟨c, (hall c).mpr hc, rfl⟩
        refine ⟨star c, hsm, ?_, w.val, (hmemS c hc w.val).mpr ⟨w, hw, rfl⟩, ?_⟩
        · rw [hstar1, gx c]; exact hxc
        · rw [gx w]; exact hxw


theorem main : ∀ (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (M T : Finset (Fin n)), (∀ u v : Fin n, K.Adj u v → (u ∈ M ↔ v ∉ M)) → (∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) → 0 < K.edgeFinset.card → PEqualNP.CrossAnd.CrossProfileLE n K M (K.edgeFinset.card + T.card - 1) 0 := by
  intro n K inst M T hM hT hE
  obtain ⟨C, q1, q2, q3, q4, q5⟩ := main0 n K M T hM hT hE
  refine ⟨C, fun g hg => (q1 g hg).1, fun g hg => ⟨?_, le_of_eq (q1 g hg).2⟩,
    fun x => congrFun q5 x, q4, ?_⟩
  · rcases (q1 g hg).1 with h | h <;> simp [h]
  · rw [Nat.le_zero]
    unfold PEqualNP.CrossAnd.crossCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hcross
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    obtain ⟨hand, -, hc⟩ := hcross
    obtain ⟨a, c, hin, hsup⟩ := q3 j hj' hand
    have ha : a < n + j := q2 j hj' a (by rw [hin]; simp)
    have hc' : c < n + j := q2 j hj' c (by rw [hin]; simp)
    have ea : PEqualNP.SyntacticMultilinear.operandSupport n C j a =
        PEqualNP.SyntacticMultilinear.support n C a := by
      simp [PEqualNP.SyntacticMultilinear.operandSupport, ha]
    have ec : PEqualNP.SyntacticMultilinear.operandSupport n C j c =
        PEqualNP.SyntacticMultilinear.support n C c := by
      simp [PEqualNP.SyntacticMultilinear.operandSupport, hc']
    rw [hin] at hc
    have hc2 : ((PEqualNP.SyntacticMultilinear.operandSupport n C j a ∩ M).Nonempty ∧
        (PEqualNP.SyntacticMultilinear.operandSupport n C j c ∩ M).Nonempty) ∨
        ((PEqualNP.SyntacticMultilinear.operandSupport n C j a \ M).Nonempty ∧
          (PEqualNP.SyntacticMultilinear.operandSupport n C j c \ M).Nonempty) := hc
    rw [ea, ec] at hc2
    rcases hc2 with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    · rcases hsup with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Finset.disjoint_left.mp h2 (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
      · exact Finset.disjoint_left.mp h1 (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
    · rcases hsup with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact (Finset.mem_sdiff.mp hx).2 (h1 (Finset.mem_sdiff.mp hx).1)
      · exact (Finset.mem_sdiff.mp hy).2 (h2 (Finset.mem_sdiff.mp hy).1)

end PEqualNP.Outside.L_meta_1998

theorem PEqualNP.Outside.L_meta_1998 : ∀ (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (M T : Finset (Fin n)), (∀ u v : Fin n, K.Adj u v → (u ∈ M ↔ v ∉ M)) → (∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) → 0 < K.edgeFinset.card → PEqualNP.CrossAnd.CrossProfileLE n K M (K.edgeFinset.card + T.card - 1) 0 := by
  exact PEqualNP.Outside.L_meta_1998.main
