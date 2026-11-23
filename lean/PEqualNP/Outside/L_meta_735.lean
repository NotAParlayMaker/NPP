import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_735

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def remap (phi : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map phi }

lemma append_read (a : List Bool) (v : Bool) (i : ℕ) :
    (a ++ [v]).getD i false = if i = a.length then v else a.getD i false := by
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = a.length
    · simp [he]
    · rw [if_neg he, List.getD_eq_default [v] false (by simp; omega),
        List.getD_eq_default a false (by omega)]

lemma extend_agrees (a b : List Bool) (v : Bool) (phi : ℕ → ℕ)
    (hread : ∀ i, b.getD (phi i) false = a.getD i false)
    (hslot : ∀ i, phi i = b.length ↔ i = a.length) :
    ∀ i, (b ++ [v]).getD (phi i) false = (a ++ [v]).getD i false := by
  intro i
  simp only [append_read, hslot i, hread i]

lemma fold_agrees (gs : List Gate) (a b : List Bool) (phi : ℕ → ℕ)
    (hread : ∀ i, b.getD (phi i) false = a.getD i false)
    (hslots : ∀ k < gs.length, ∀ i, phi i = b.length + k ↔ i = a.length + k) :
    ∀ i, ((gs.map (remap phi)).foldl step b).getD (phi i) false =
      (gs.foldl step a).getD i false := by
  induction gs generalizing a b with
  | nil => simpa using hread
  | cons g gs ih =>
    have heval : (remap phi g).op.eval
        ((remap phi g).inputs.map (fun i => b.getD i false)) =
        g.op.eval (g.inputs.map (fun i => a.getD i false)) := by
      simp only [remap, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hread i
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · unfold step
      rw [heval]
      exact extend_agrees a b _ phi hread (by simpa using hslots 0 (by simp))
    · intro k hk i
      have h := hslots (k + 1) (by simp only [List.length_cons]; omega) i
      simpa only [step, List.length_append, List.length_singleton, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

noncomputable def reindex (n n' G : ℕ) (e : Fin n' → Fin n) (i : ℕ) : ℕ :=
  if h : ∃ j : Fin n', (e j : ℕ) = i then (Classical.choose h).val
  else if n ≤ i ∧ i < n + G then n' + (i - n) else n' + G

lemma reindex_slot (n n' G : ℕ) (e : Fin n' → Fin n)
    (k : ℕ) (hk : k < G) (i : ℕ) :
    reindex n n' G e i = n' + k ↔ i = n + k := by
  unfold reindex
  split_ifs with h hmid
  · have hj := Classical.choose_spec h
    have h1 := (Classical.choose h).isLt
    have h2 := (e (Classical.choose h)).isLt
    omega
  · omega
  · omega

lemma initial_agrees (n n' G : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n)
    (hcover : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k)
    (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n')
    (hz : ∀ k ∈ Z, x.getD (k : ℕ) false = false)
    (he : ∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) :
    ∀ i, x'.getD (reindex n n' G e i) false = x.getD i false := by
  intro i
  unfold reindex
  split_ifs with h hmid
  · have hj := Classical.choose_spec h
    simpa only [hj] using (he (Classical.choose h)).symm
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · rw [List.getD_eq_default _ _ (by omega)]
    by_cases hi : i < n
    · have hmem : (⟨i, hi⟩ : Fin n) ∈ Z := by
        by_contra hn
        obtain ⟨j, hj⟩ := (hcover ⟨i, hi⟩).mp hn
        exact h ⟨j, congrArg Fin.val hj⟩
      exact (hz ⟨i, hi⟩ hmem).symm
    · rw [List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_735

theorem PEqualNP.Outside.L_meta_735 : ∀ (n n' : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k) → n' + Z.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ phi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ Z, x.getD (k : ℕ) false = false) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := 0 } x').getD (phi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := phi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' Z e _hmono hcover _hcard gates
  refine ⟨PEqualNP.Outside.L_meta_735.reindex n n' gates.length e, ?_⟩
  intro x x' hx hx' hz he
  have hw := PEqualNP.Outside.L_meta_735.fold_agrees gates x x'
    (PEqualNP.Outside.L_meta_735.reindex n n' gates.length e)
    (PEqualNP.Outside.L_meta_735.initial_agrees n n' gates.length Z e hcover x x' hx hx' hz he)
    (by
      intro k hk i
      simpa only [hx, hx'] using
        PEqualNP.Outside.L_meta_735.reindex_slot n n' gates.length e k hk i)
  constructor
  · exact hw
  · intro o
    exact hw o
