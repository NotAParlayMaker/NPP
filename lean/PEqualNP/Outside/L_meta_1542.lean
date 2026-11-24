import Mathlib
import PEqualNP.Defs

/-!
L-meta-1542: a wire of an AND/OR fan-in-two list that fires on two singletons from a
q-point subset of a line must fire on the complement of every other line.

Proof idea (desk-952-batch5 A5): AND/OR circuits are monotone, so a wire true on `{a}`
is true on every input with `a` set. Two distinct points of a line cannot both lie on
another line of a linear space, so on the complement of any other line at least one of
`a`, `b` is true.
-/

namespace PEqualNP.Outside.L_meta_1542_aux
open PEqualNP.CircuitLowerBounds

/-- Running values of a gate list (same fold as `Circuit.wires`). -/
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

/-- Pointwise order on bit lists, read through `getD`. -/
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [ite_eq_left h1] at ht ⊢; exact ih t ht
    · rw [ite_eq_right h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [ite_eq_left h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [ite_eq_right h2] at ht; simp at ht

theorem ofFn_getD {n : ℕ} (z : Fin n → Bool) (i : ℕ) :
    (List.ofFn z).getD i false = if h : i < n then z ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dite_eq_left h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simp; omega)]

theorem eval_mono_ofFn {n : ℕ} (gates : List Gate) (out : ℕ)
    (hm : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hle : ∀ p, x p = true → y p = true)
    (h : Circuit.eval ⟨gates, out⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, out⟩ (List.ofFn y) = true := by
  have hl : (List.ofFn x).length = (List.ofFn y).length := by simp
  have hxy : Le (List.ofFn x) (List.ofFn y) := by
    intro i hi
    rw [ofFn_getD x i] at hi
    rw [ofFn_getD y i]
    by_cases hi' : i < n
    · simpa [dite_eq_left hi'] using hle ⟨i, hi'⟩ (by simpa [dite_eq_left hi'] using hi)
    · simp [dite_eq_right hi'] at hi
  have mono := W_mono gates hm (List.ofFn x) (List.ofFn y) hl hxy out
  simpa [Circuit.eval, Circuit.wires, W] using mono h

/-- Two distinct points of one line cannot both lie on a different line. -/
theorem not_both_on_other {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 s a b : Fin N)
    (hmeet : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (ha : a ∈ L i0) (hb : b ∈ L i0) (hab : a ≠ b) (hs : s ≠ i0)
    (has : a ∈ L s) : b ∉ L s := by
  intro hbs
  have hne : i0 ≠ s := Ne.symm hs
  have hcard := hmeet i0 s hne
  have hsub : ({a, b} : Finset (Fin N)) ⊆ L i0 ∩ L s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨ha, has⟩
    · exact Finset.mem_inter.mpr ⟨hb, hbs⟩
  have hab_card : ({a, b} : Finset (Fin N)).card = 2 := by
    simp [Finset.card_insert_of_notMem, hab]
  have : 2 ≤ (L i0 ∩ L s).card := hab_card ▸ Finset.card_le_card hsub
  omega

theorem singleton_le_complement {N : ℕ} (a : Fin N) (S : Finset (Fin N)) (ha : a ∉ S) :
    ∀ p : Fin N, (fun v : Fin N => decide (v = a)) p = true →
      (fun v : Fin N => decide (v ∉ S)) p = true := by
  intro p hp
  simp only [decide_eq_true_eq] at hp ⊢
  subst hp
  exact ha

end PEqualNP.Outside.L_meta_1542_aux

open PEqualNP.Outside.L_meta_1542_aux
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1542 :
    ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = q →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (a b : Fin N),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    a ∈ T0 → b ∈ T0 → a ≠ b →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩
      (List.ofFn (fun v : Fin N => decide (v = a))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩
      (List.ofFn (fun v : Fin N => decide (v = b))) = true →
    ∀ s : Fin N, s ≠ i0 →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin N => decide (v ∉ L s))) = true := by
  intro q N L i0 T0 _hq _hN _hcard hmeet _hjoin hTsub _hTcard gates out a b hops haT hbT hab hea heb s hs
  have ha : a ∈ L i0 := hTsub haT
  have hb : b ∈ L i0 := hTsub hbT
  have hm : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hops g hg).1
  by_cases has : a ∈ L s
  · have hbn : b ∉ L s := not_both_on_other L i0 s a b hmeet ha hb hab hs has
    exact eval_mono_ofFn gates out hm _ _ (singleton_le_complement b (L s) hbn) heb
  · exact eval_mono_ofFn gates out hm _ _ (singleton_le_complement a (L s) has) hea
