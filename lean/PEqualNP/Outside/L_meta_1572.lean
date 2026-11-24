import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572

open PEqualNP.CircuitLowerBounds

private def wire (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (Circuit.mk gates w).eval (List.ofFn x)

private def wires (gates : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gates 0).wires x

private theorem wires_append (as bs : List Gate) (x : List Bool) :
    wires (as ++ bs) x = wires bs (wires as x) := by
  simp [wires, Circuit.wires, List.foldl_append]

private theorem wires_length (gates : List Gate) (x : List Bool) :
    (wires gates x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp [wires, Circuit.wires]
  | cons g gs ih =>
    simp only [wires, Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

private theorem wires_keep (gates : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wires gates x).getD w false = x.getD w false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [wires, Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

private theorem wires_take (gates : List Gate) (x : List Bool) {k w : ℕ}
    (hk : k ≤ gates.length) (hw : w < x.length + k) :
    (wires gates x).getD w false = (wires (gates.take k) x).getD w false := by
  conv_lhs => rw [← List.take_append_drop k gates, wires_append]
  apply wires_keep
  simpa [wires_length, List.length_take, Nat.min_eq_left hk] using hw

private theorem wire_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    wire gates v.val x = x v := by
  change (wires gates (List.ofFn x)).getD v.val false = _
  rw [wires_keep _ _ _ (by simp [v.isLt])]
  simp [List.getD_eq_getElem?_getD, v.isLt]

private theorem wire_outside (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : wire gates w x = false := by
  change (wires gates (List.ofFn x)).getD w false = _
  apply List.getD_eq_default
  simpa [wires_length] using hw

private theorem wire_gate (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : Fin gates.length)
    (hback : ∀ a ∈ (gates.get i).inputs, a < n + i.val) :
    wire gates (n + i.val) x =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => wire gates a x) := by
  let xs := List.ofFn x
  have hlen : xs.length = n := List.length_ofFn
  have hprefix : (wires (gates.take i.val) xs).length = n + i.val := by
    rw [wires_length, hlen, List.length_take, Nat.min_eq_left i.isLt.le]
  change (wires gates xs).getD (n + i.val) false = _
  rw [wires_take gates xs (k := i.val + 1) i.isLt (by rw [hlen]; omega),
    List.take_succ_eq_append_getElem i.isLt, wires_append]
  have happend (b : Bool) :
      ((wires (gates.take i.val) xs) ++ [b]).getD (n + i.val) false = b := by
    rw [← hprefix]
    simp [List.getD_eq_getElem?_getD]
  change ((wires (gates.take i.val) xs) ++ [_]).getD (n + i.val) false = _
  rw [happend]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (wires_take gates xs i.isLt.le (by rw [hlen]; exact hback a ha)).symm

private theorem wire_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : Fin gates.length)
    (hback : ∀ a ∈ (gates.get i).inputs, a < n + i.val) (hop : (gates.get i).op = GateOp.or) :
    wire gates (n + i.val) x = true ↔ ∃ a ∈ (gates.get i).inputs, wire gates a x = true := by
  rw [wire_gate gates x i hback, hop]
  simp [GateOp.eval, List.any_map, List.any_eq_true]

private theorem wire_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : Fin gates.length)
    (hback : ∀ a ∈ (gates.get i).inputs, a < n + i.val) (hop : (gates.get i).op = GateOp.and) :
    wire gates (n + i.val) x = true ↔ ∀ a ∈ (gates.get i).inputs, wire gates a x = true := by
  rw [wire_gate gates x i hback, hop]
  simp [GateOp.eval, List.all_map, List.all_eq_true]

private theorem wire_cases (gates : List Gate) (n w : ℕ) :
    w < n ∨ (∃ i : Fin gates.length, w = n + i.val) ∨ n + gates.length ≤ w := by
  by_cases hi : w < n
  · exact Or.inl hi
  by_cases hg : w < n + gates.length
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, show w = n + (w - n) by omega⟩)
  · exact Or.inr (Or.inr (by omega))

private theorem wire_mono (gates : List Gate) {n : ℕ} (x y : Fin n → Bool)
    (hops : ∀ i : Fin gates.length, (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or)
    (hback : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val)
    (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    wire gates w x = true → wire gates w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases wire_cases gates n w with hv | ⟨i, rfl⟩ | hout
    · let v : Fin n := ⟨w, hv⟩
      exact (wire_input gates y v).trans (hxy v ((wire_input gates x v).symm.trans hw))
    · rcases hops i with hand | hor
      · apply (wire_and gates y i (hback i) hand).2
        intro a ha
        exact ih a (hback i a ha) ((wire_and gates x i (hback i) hand).1 hw a ha)
      · obtain ⟨a, ha, hax⟩ := (wire_or gates x i (hback i) hor).1 hw
        exact (wire_or gates y i (hback i) hor).2 ⟨a, ha, ih a (hback i a ha) hax⟩
    · rw [wire_outside gates x w hout] at hw
      contradiction

private def orDescendant (gates : List Gate) (n root w : ℕ) : Prop :=
  ∀ S : Set ℕ, root ∈ S →
    (∀ i : Fin gates.length, n + i.val ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) → w ∈ S

private theorem descendant_false (gates : List Gate) {n : ℕ} (root w : ℕ) (x : Fin n → Bool)
    (hback : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val)
    (hroot : wire gates root x = false) (hw : orDescendant gates n root w) :
    wire gates w x = false := by
  apply hw {a | wire gates a x = false} hroot
  intro i hi hor a ha
  change wire gates (n + i.val) x = false at hi
  change wire gates a x = false
  cases hax : wire gates a x with
  | false => rfl
  | true =>
    have := (wire_or gates x i (hback i) hor).2 ⟨a, ha, hax⟩
    rw [hi] at this
    contradiction

private theorem reaches_and (gates : List Gate) {n : ℕ} (root : ℕ) (x : Fin n → Bool)
    (hops : ∀ i : Fin gates.length, (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or)
    (hback : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val)
    (hin : ∀ v : Fin n, orDescendant gates n root v.val → x v = false)
    (htrue : wire gates root x = true) :
    ∃ w, orDescendant gates n root w ∧
      (∃ i : Fin gates.length, w = n + i.val ∧ (gates.get i).op = GateOp.and) ∧
      wire gates w x = true := by
  suffices step : ∀ w, orDescendant gates n root w → wire gates w x = true → _ by
    exact step root (fun _ h _ => h) htrue
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hd hw
    rcases wire_cases gates n w with hv | ⟨i, rfl⟩ | hout
    · let v : Fin n := ⟨w, hv⟩
      have he := (wire_input gates x v).trans (hin v hd)
      rw [he] at hw
      contradiction
    · rcases hops i with hand | hor
      · exact ⟨n + i.val, hd, ⟨i, rfl, hand⟩, hw⟩
      · obtain ⟨a, ha, hax⟩ := (wire_or gates x i (hback i) hor).1 hw
        exact ih a (hback i a ha) (fun S hs hc => hc i (hd S hs hc) hor a ha) hax
    · rw [wire_outside gates x w hout] at hw
      contradiction

private def testInput (a b p : Fin 13) (v : Fin 13) : Bool :=
  decide (v = p ∨ (p ≠ a ∧ v = b))

private def line (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

private theorem one_off_left : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (1 : Fin 13) ∉ line l := by
  decide

private theorem zero_off_right : ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (0 : Fin 13) ∉ line m := by
  decide

private theorem test_reaches_and (gates : List Gate) (root : ℕ) (A B : Finset (Fin 13))
    (a b c : Fin 13) (haB : a ∉ B) (hbA : b ∉ A) (hAB : A ∩ B = {c})
    (hops : ∀ i : Fin gates.length, (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or)
    (hback : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < 13 + i.val)
    (hA : wire gates root (fun v => decide (v ∉ A)) = false)
    (hB : wire gates root (fun v => decide (v ∉ B)) = false)
    (ht : 2 ≤ (A.filter fun p => wire gates root (testInput a b p) = true).card) :
    ∃ w, orDescendant gates 13 root w ∧
      (∃ i : Fin gates.length, w = 13 + i.val ∧ (gates.get i).op = GateOp.and) ∧
      ∃ p ∈ A, p ≠ a ∧ p ≠ c ∧ wire gates w (testInput a b p) = true := by
  obtain ⟨p, hp, q, hq, hne⟩ := Finset.one_lt_card.1 (show 1 < _ from ht)
  have hex : ∃ p ∈ A.filter (fun z => wire gates root (testInput a b z) = true), p ≠ c := by
    by_cases hpc : p = c
    · exact ⟨q, hq, by simpa [hpc, ne_comm] using hne⟩
    · exact ⟨p, hp, hpc⟩
  obtain ⟨p, hp, hpc⟩ := hex
  obtain ⟨hpA, htrue⟩ := Finset.mem_filter.1 hp
  have hpa : p ≠ a := by
    intro hpa
    subst p
    have hcontra := wire_mono gates (testInput a b a) (fun v => decide (v ∉ B))
      hops hback (fun v hv => by
        have : v = a := by simpa [testInput] using hv
        simpa [this] using haB) root htrue
    rw [hB] at hcontra
    contradiction
  have hpB : p ∉ B := by
    intro hpB
    have hc : p ∈ A ∩ B := Finset.mem_inter.2 ⟨hpA, hpB⟩
    rw [hAB] at hc
    exact hpc (Finset.mem_singleton.1 hc)
  have hin (v : Fin 13) (hd : orDescendant gates 13 root v.val) : testInput a b p v = false := by
    have hvA := (wire_input gates (fun u => decide (u ∉ A)) v).symm.trans
      (descendant_false gates root v.val _ hback hA hd)
    have hvB := (wire_input gates (fun u => decide (u ∉ B)) v).symm.trans
      (descendant_false gates root v.val _ hback hB hd)
    have hva : v ∈ A := by simpa using hvA
    have hvb : v ∈ B := by simpa using hvB
    have hvp : v ≠ p := fun h => hpB (h ▸ hvb)
    have hvb' : v ≠ b := fun h => hbA (h ▸ hva)
    simp [testInput, hvp, hvb']
  obtain ⟨w, hd, hand, hw⟩ := reaches_and gates root (testInput a b p) hops hback hin htrue
  exact ⟨w, hd, hand, p, hpA, hpa, hpc, hw⟩

end PEqualNP.Outside.L_meta_1572

open PEqualNP.Outside.L_meta_1572 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hleg hwf hl hm hmeet hleft hright
  have hlines : L = line := by
    funext t
    exact hL t
  subst L
  have hops (i : Fin gates.length) := (hleg (gates.get i) (List.get_mem gates i)).1
  have hback (i : Fin gates.length) := (hwf i).2
  constructor
  · exact test_reaches_and gates g (line l) (line m) 0 1 c (zero_off_right m hm)
      (one_off_left l hl) hmeet hops hback hleft hright
  · exact test_reaches_and gates g (line m) (line l) 1 0 c (one_off_left l hl)
      (zero_off_right m hm) ((Finset.inter_comm _ _).trans hmeet) hops hback hright hleft
