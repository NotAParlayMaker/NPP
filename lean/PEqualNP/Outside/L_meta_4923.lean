import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4923

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

theorem supp_main (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) :
    ∃ L : List (Finset (Fin n)), L.length ≤ C.size ∧
      (∀ w : ℕ, (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn fun q : Fin n => decide (q = p))).getD w false = true)).card ≤ 1 ∨
        (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn fun q : Fin n => decide (q = p))).getD w false = true)) ∈ L) ∧
      ∀ (k : ℕ) (s : Finset (Fin n)), L[k]? = some s → ∃ a b : Finset (Fin n), s = a ∪ b ∧
        (a.card ≤ 1 ∨ a ∈ List.take k L) ∧ (b.card ≤ 1 ∨ b ∈ List.take k L) := by
  classical
  let e : Fin n → List Bool := fun p => List.ofFn fun q : Fin n => decide (q = p)
  have he : ∀ p, (e p).length = n := fun p => by simp [e]
  let val : Fin n → ℕ → Bool := fun p w => (wiresFrom C.gates (e p)).getD w false
  let supp : ℕ → Finset (Fin n) := fun w => Finset.univ.filter (fun p : Fin n => val p w = true)
  have hmem : ∀ w p, p ∈ supp w ↔ val p w = true := fun w p => by simp [supp]
  have hlow : ∀ w, w < n → (supp w).card ≤ 1 := by
    intro w hw
    have hsub : supp w ⊆ {⟨w, hw⟩} := by
      intro p hp
      rw [hmem] at hp
      have h1 : val p w = (e p).getD w false := getD_wiresFrom_lt C.gates (e p) w (by rw [he]; exact hw)
      rw [h1] at hp
      have h2 : (e p).getD w false = decide ((⟨w, hw⟩ : Fin n) = p) := by
        simp [e, List.getD_eq_getElem?_getD, hw]
      rw [h2] at hp
      rw [Finset.mem_singleton]
      exact (of_decide_eq_true hp).symm
    exact (Finset.card_le_card hsub).trans (by simp)
  have hgate : ∀ k (hk : k < C.gates.length) p, val p (n + k) =
      ((C.gates[k]).inputs.map fun i => if i < n + k then val p i else false).any id := by
    intro k hk p
    have h := getD_wiresFrom_gate C.gates (e p) k hk
    rw [he] at h
    have hop := (hC _ (List.getElem_mem hk)).1
    rw [hop] at h
    exact h
  let part : ℕ → ℕ → Finset (Fin n) := fun k i => if i < n + k then supp i else ∅
  let L : List (Finset (Fin n)) := (List.range C.gates.length).map fun k => supp (n + k)
  have hpart : ∀ k, k ≤ C.gates.length → ∀ i, (part k i).card ≤ 1 ∨ part k i ∈ List.take k L := by
    intro k hk i
    by_cases h1 : i < n + k
    · by_cases h2 : i < n
      · left
        simp only [part, h1, ite_true]
        exact hlow i h2
      · right
        simp only [part, h1, ite_true]
        have htake : List.take k L = (List.range k).map fun j => supp (n + j) := by
          simp only [L, List.map_take.symm, List.take_range, min_eq_left hk]
        rw [htake, List.mem_map]
        refine ⟨i - n, List.mem_range.mpr (by omega), ?_⟩
        congr 1
        omega
    · left
      simp [part, h1]
  refine ⟨L, by simp [L, Circuit.size], ?_, ?_⟩
  · intro w
    show (supp w).card ≤ 1 ∨ supp w ∈ L
    by_cases h1 : w < n
    · exact Or.inl (hlow w h1)
    · by_cases h2 : w < n + C.gates.length
      · right
        simp only [L, List.mem_map]
        refine ⟨w - n, List.mem_range.mpr (by omega), ?_⟩
        congr 1
        omega
      · left
        have hemp : supp w = ∅ := by
          ext p
          rw [hmem]
          have : val p w = false := by
            apply List.getD_eq_default
            rw [length_wiresFrom, he]
            omega
          simp [this]
        simp [hemp]
  · intro k s hks
    have hk : k < C.gates.length := by
      have := (List.getElem?_eq_some_iff.mp hks).1
      simpa [L] using this
    have hs : s = supp (n + k) := by
      have h := (List.getElem?_eq_some_iff.mp hks).2
      simpa [L] using h.symm
    have hlen := (hC _ (List.getElem_mem hk)).2
    have hval := hgate k hk
    rcases hin : C.gates[k].inputs with _ | ⟨i, _ | ⟨j, _ | ⟨l, t⟩⟩⟩
    · refine ⟨∅, ∅, ?_, Or.inl (by simp), Or.inl (by simp)⟩
      rw [hs]
      ext p
      rw [hmem, hval p, hin]
      simp
    · refine ⟨part k i, ∅, ?_, hpart k (Nat.le_of_lt hk) i, Or.inl (by simp)⟩
      rw [hs]
      ext p
      rw [hmem, hval p, hin]
      by_cases h1 : i < n + k <;> simp [part, h1, hmem]
    · refine ⟨part k i, part k j, ?_, hpart k (Nat.le_of_lt hk) i, hpart k (Nat.le_of_lt hk) j⟩
      rw [hs]
      ext p
      rw [hmem, hval p, hin]
      by_cases h1 : i < n + k <;> by_cases h2 : j < n + k <;> simp [part, h1, h2, hmem]
    · rw [hin] at hlen
      simp at hlen

end PEqualNP.Outside.L_meta_4923

theorem PEqualNP.Outside.L_meta_4923 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x3 ∈ x2.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs.length ≤ (2 : ℕ)) →     ∃ (x4 : List (Finset (Fin x1))),       x4.length ≤ x2.size ∧         (∀ (x5 : ℕ),             have x6 : Finset (Fin x1) := {x6 : Fin x1 | (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 = x6))).getD x5 Bool.false = Bool.true};             x6.card ≤ (1 : ℕ) ∨ x6 ∈ x4) ∧           ∀ (x5 : ℕ) (x6 : Finset (Fin x1)), x4[x5]? = Option.some x6 → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x1)), x6 = x8 ∪ x9 ∧ (x8.card ≤ (1 : ℕ) ∨ x8 ∈ List.take x5 x4) ∧ (x9.card ≤ (1 : ℕ) ∨ x9 ∈ List.take x5 x4) := by
  intro x1 x2 hC
  exact PEqualNP.Outside.L_meta_4923.supp_main x1 x2 hC
