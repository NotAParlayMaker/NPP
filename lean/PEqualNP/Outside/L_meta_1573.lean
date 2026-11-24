import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1573

open PEqualNP.CircuitLowerBounds

-- adapted from L_meta_1319 (W, W_snoc, W_length, getD_snoc, Le, eval_mono, W_mono)
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
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

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
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht


def L0 (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

theorem fin1 : ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)),
    ∀ p ∈ L0 l, ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l' ≠ l →
    (∃ v, v ∈ L0 m ∧ (v = p ∨ (p ≠ 0 ∧ v = 1))) →
    ∀ v, (v = p ∨ (p ≠ 0 ∧ v = 1)) → v ∉ L0 l' := by
  unfold L0; decide

theorem fin2 : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
    ∀ p ∈ L0 m, ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m' ≠ m →
    (∃ v, v ∈ L0 l ∧ (v = p ∨ (p ≠ 1 ∧ v = 0))) →
    ∀ v, (v = p ∨ (p ≠ 1 ∧ v = 0)) → v ∉ L0 m' := by
  unfold L0; decide

theorem mono (gates : List Gate) (g : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (f h : Fin 13 → Bool) (hfh : ∀ v, f v = true → h v = true)
    (hf : Circuit.eval ⟨gates, g⟩ (List.ofFn f) = true) :
    Circuit.eval ⟨gates, g⟩ (List.ofFn h) = true := by
  have key := W_mono gates (fun g' hg' => (hg g' hg').1) (List.ofFn f) (List.ofFn h)
    (by simp) (by
      intro i hi
      by_cases hi13 : i < 13
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
        simp [hi13] at hi ⊢
        exact hfh _ hi
      · simp only [List.getD_eq_getElem?_getD] at hi
        rw [List.getElem?_eq_none (by simp; omega)] at hi
        simp at hi) g
  exact key hf

end PEqualNP.Outside.L_meta_1573

theorem PEqualNP.Outside.L_meta_1573 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false → (∃ p ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) →
      ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l' ≠ l → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l'))) = true) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → (∃ p ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) →
      ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m' ≠ m → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m'))) = true) := by
  intro L hL gates g hg
  have hL' : L = PEqualNP.Outside.L_meta_1573.L0 := funext hL
  subst hL'
  have mono' := PEqualNP.Outside.L_meta_1573.mono gates g hg
  constructor
  · intro m hm l hl hf hex l' hl' hne
    obtain ⟨p, hp, ht⟩ := hex
    have hmeet : ∃ v, v ∈ PEqualNP.Outside.L_meta_1573.L0 m ∧ (v = p ∨ (p ≠ 0 ∧ v = 1)) := by
      by_contra hcon
      push_neg at hcon
      have := mono' _ (fun v => decide (v ∉ PEqualNP.Outside.L_meta_1573.L0 m)) (by
        intro v hv
        have := hcon v
        by_cases h1 : v ∈ PEqualNP.Outside.L_meta_1573.L0 m
        · have hv' : v = p ∨ (p ≠ 0 ∧ v = 1) := by simpa using hv
          rcases hv' with h | ⟨h2, h3⟩
          · exact absurd h (this h1).1
          · exact absurd h3 ((this h1).2 h2)
        · simp [h1]) ht
      rw [hf] at this; exact Bool.false_ne_true this
    exact mono' _ (fun v => decide (v ∉ PEqualNP.Outside.L_meta_1573.L0 l')) (by
      intro v hv
      have := PEqualNP.Outside.L_meta_1573.fin1 m hm l hl p hp l' hl' hne hmeet v (by simpa using hv)
      simpa using this) ht
  · intro l hl m hm hf hex m' hm' hne
    obtain ⟨p, hp, ht⟩ := hex
    have hmeet : ∃ v, v ∈ PEqualNP.Outside.L_meta_1573.L0 l ∧ (v = p ∨ (p ≠ 1 ∧ v = 0)) := by
      by_contra hcon
      push_neg at hcon
      have := mono' _ (fun v => decide (v ∉ PEqualNP.Outside.L_meta_1573.L0 l)) (by
        intro v hv
        have := hcon v
        by_cases h1 : v ∈ PEqualNP.Outside.L_meta_1573.L0 l
        · have hv' : v = p ∨ (p ≠ 1 ∧ v = 0) := by simpa using hv
          rcases hv' with h | ⟨h2, h3⟩
          · exact absurd h (this h1).1
          · exact absurd h3 ((this h1).2 h2)
        · simp [h1]) ht
      rw [hf] at this; exact Bool.false_ne_true this
    exact mono' _ (fun v => decide (v ∉ PEqualNP.Outside.L_meta_1573.L0 m')) (by
      intro v hv
      have := PEqualNP.Outside.L_meta_1573.fin2 l hl m hm p hp m' hm' hne hmeet v (by simpa using hv)
      simpa using this) ht
