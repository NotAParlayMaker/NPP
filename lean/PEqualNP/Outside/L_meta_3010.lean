import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010_aux

open CircuitLowerBounds MetaComplexity TopForm

private def wire (p : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if hi : i < 14 then (p ⟨i, hi⟩).val else i

private lemma wire_inj (p : Equiv.Perm (Fin 14)) : Function.Injective (wire p) := by
  intro i j hij
  by_cases hi : i < 14 <;> by_cases hj : j < 14
  · have h : p ⟨i, hi⟩ = p ⟨j, hj⟩ := Fin.ext (by simpa [wire, hi, hj] using hij)
    exact congrArg Fin.val (p.injective h)
  · have h : (p ⟨i, hi⟩).val < 14 := (p ⟨i, hi⟩).isLt
    simp only [wire, dite_eq_left hi, dite_eq_right hj] at hij
    omega
  · have h : (p ⟨j, hj⟩).val < 14 := (p ⟨j, hj⟩).isLt
    simp only [wire, dite_eq_right hi, dite_eq_left hj] at hij
    omega
  · simpa [wire, hi, hj] using hij

private def finWire (p : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨wire p i, by
    by_cases h : i.val < 14
    · rw [wire, dite_eq_left h]
      exact Nat.lt_trans (p ⟨i, h⟩).isLt (by decide)
    · simp [wire, h]⟩

private lemma finWire_eq (p : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (finWire p i).val = if i.val < 14 then (p (Fin.ofNat 14 i.val)).val else 14 := by
  by_cases h : i.val < 14
  · have he : (Fin.ofNat 14 i.val) = ⟨i.val, h⟩ := Fin.ext (Nat.mod_eq_of_lt h)
    simp only [finWire, wire, dite_eq_left h, ite_eq_left h, he]
  · have he : i.val = 14 := by have := i.isLt; omega
    change wire p i.val = _
    rw [wire, dite_eq_right h, ite_eq_right h]
    exact he

private lemma ofFn_get (x : Fin 14 → Bool) (i : Fin 14) :
    (List.ofFn x).getD i false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

private lemma get_wire (p : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) (z : List Bool)
    (i : ℕ) : (List.ofFn x ++ z).getD (wire p i) false =
      (List.ofFn (x ∘ p) ++ z).getD i false := by
  by_cases h : i < 14
  · rw [wire, dite_eq_left h, List.getD_append _ _ _ _ (by simp),
      List.getD_append _ _ _ _ (by simpa using h)]
    exact (ofFn_get x (p ⟨i, h⟩)).trans (ofFn_get (x ∘ p) ⟨i, h⟩).symm
  · rw [wire, dite_eq_right h, List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp only [List.length_ofFn]

private def mappedGate (p : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire p)⟩

private def mappedCircuit (p : Equiv.Perm (Fin 14)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mappedGate p), wire p C.output⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma run_mapped (p : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool)
    (gs : List Gate) (z : List Bool) :
    ∃ u : List Bool,
      (gs.map (mappedGate p)).foldl step (List.ofFn x ++ z) = List.ofFn x ++ u ∧
      gs.foldl step (List.ofFn (x ∘ p) ++ z) = List.ofFn (x ∘ p) ++ u := by
  induction gs generalizing z with
  | nil => exact ⟨z, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ p) ++ z).getD i false)
    have hval :
        (g.inputs.map (wire p)).map (fun i => (List.ofFn x ++ z).getD i false) =
          g.inputs.map (fun i => (List.ofFn (x ∘ p) ++ z).getD i false) := by
      simp only [List.map_map, Function.comp_def, get_wire]
    obtain ⟨u, hu, hu'⟩ := ih (z ++ [v])
    refine ⟨u, ?_, ?_⟩
    · simpa only [List.map_cons, List.foldl_cons, step, mappedGate, hval, List.append_assoc]
        using hu
    · simpa only [List.foldl_cons, step, List.append_assoc] using hu'

private lemma eval_mapped (p : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool)
    (C : Circuit) (z : List Bool) :
    (mappedCircuit p C).eval (List.ofFn x ++ z) =
      C.eval (List.ofFn (x ∘ p) ++ z) := by
  obtain ⟨u, hu, hu'⟩ := run_mapped p x C.gates z
  change ((C.gates.map (mappedGate p)).foldl step (List.ofFn x ++ z)).getD
    (wire p C.output) false = (C.gates.foldl step (List.ofFn (x ∘ p) ++ z)).getD C.output false
  rw [hu, hu', get_wire]

private lemma mono_mapped (p : Equiv.Perm (Fin 14)) (C : Circuit)
    (hC : Monotone2 C) : Monotone2 (mappedCircuit p C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [mappedGate] using hC g' hg'

private def AO (o : GateOp) : Prop := o = GateOp.and ∨ o = GateOp.or

private lemma ao_comm {o : GateOp} (ho : AO o) (s t : Bool) :
    o.eval [s, t] = o.eval [t, s] := by
  rcases ho with rfl | rfl <;> cases s <;> cases t <;> rfl

private lemma ao_sorted {α : Type} [LinearOrder α] {o : GateOp} (ho : AO o)
    (a b : α) (f : α → Bool) :
    o.eval [f (min a b), f (max a b)] = o.eval [f a, f b] := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact ao_comm ho _ _

private def initial (x : Fin 14 → Bool) (a b : Fin 14) (o : GateOp) : List Bool :=
  List.ofFn x ++ [o.eval [x a, x b]]

private def extendedInput (x : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15)
    (o q : GateOp) : List Bool :=
  let w := initial x a b o
  w ++ [q.eval [w.getD c false, w.getD d false]]

private def Valid (F : (Fin 14 → Bool) → Bool) (a b : Fin 14) (c d : Fin 15) : Prop :=
  a ≠ b ∧ c ≠ d ∧ ∃ o q C, AO o ∧ AO q ∧ Monotone2 C ∧ C.size ≤ 24 ∧
    ∀ x, C.eval (extendedInput x a b c d o q) = F x

private lemma valid_mapped (F : (Fin 14 → Bool) → Bool)
    (a b : Fin 14) (c d : Fin 15) (p : Equiv.Perm (Fin 14))
    (hp : ∀ x, F (x ∘ p) = F x) (h : Valid F a b c d) :
    Valid F (p a) (p b) (finWire p c) (finWire p d) := by
  obtain ⟨hab, hcd, o, q, C, ho, hq, hC, hsize, heval⟩ := h
  have hne : finWire p c ≠ finWire p d := fun h =>
    hcd (Fin.ext (wire_inj p (congrArg Fin.val h)))
  refine ⟨fun h => hab (p.injective h), hne, o, q, mappedCircuit p C,
    ho, hq, mono_mapped p C hC, ?_, ?_⟩
  · simpa [Circuit.size, mappedCircuit] using hsize
  · intro x
    let z := [o.eval [x (p a), x (p b)]]
    have hfirst : initial x (p a) (p b) o = List.ofFn x ++ z := rfl
    have hfirst' : initial (x ∘ p) a b o = List.ofFn (x ∘ p) ++ z := rfl
    have hv (i : Fin 15) : (initial x (p a) (p b) o).getD (finWire p i) false =
        (initial (x ∘ p) a b o).getD i false := by
      rw [hfirst, hfirst']
      exact get_wire p x z i
    rw [extendedInput, hv c, hv d, hfirst, List.append_assoc, eval_mapped,
      ← List.append_assoc, ← hfirst']
    exact (heval (x ∘ p)).trans (hp x)

private lemma sorted_lt {α : Type} [LinearOrder α] {a b : α} (hne : a ≠ b) :
    min a b < max a b := by
  rcases lt_or_gt_of_ne hne with h | h
  · simpa [min_eq_left h.le, max_eq_right h.le] using h
  · simpa [min_eq_right h.le, max_eq_left h.le] using h

private lemma valid_sorted (F : (Fin 14 → Bool) → Bool) (a b : Fin 14) (c d : Fin 15)
    (h : Valid F a b c d) : Valid F (min a b) (max a b) (min c d) (max c d) := by
  obtain ⟨hab, hcd, o, q, C, ho, hq, hC, hs, he⟩ := h
  refine ⟨ne_of_lt (sorted_lt hab), ne_of_lt (sorted_lt hcd), o, q, C, ho, hq, hC, hs, ?_⟩
  intro x
  have hw : initial x (min a b) (max a b) o = initial x a b o := by
    simp only [initial, ao_sorted ho a b x]
  simp only [extendedInput, hw, ao_sorted hq c d (fun i => (initial x a b o).getD i false)]
  exact he x

private def rank (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

private lemma rank_sorted (a b : Fin 14) (c d : Fin 15) :
    rank (min a b) (max a b) (min c d) (max c d) = rank a b c d := by
  simp only [rank,
    min_eq_left (min_le_max (a := a.val) (b := b.val)),
    max_eq_right (min_le_max (a := a.val) (b := b.val)),
    min_eq_left (min_le_max (a := c.val) (b := d.val)),
    max_eq_right (min_le_max (a := c.val) (b := d.val))]

private lemma list_pair {l : List ℕ} (h : l.length = 2) : ∃ a b, l = [a, b] :=
  ⟨_, _, List.eq_getElem_of_length_eq_two l h⟩

private lemma has_valid (F : (Fin 14 → Bool) → Bool) (C : Circuit) (hC : IsAO2 14 C)
    (hn : ∀ g ∈ C.gates, g.inputs.Nodup) (h2 : 2 ≤ C.size) (h26 : C.size ≤ 26)
    (he : ∀ x, C.eval (List.ofFn x) = F x) : ∃ a b c d, Valid F a b c d := by
  rcases C with ⟨_ | ⟨g, _ | ⟨q, gs⟩⟩, out⟩
  · simp [Circuit.size] at h2
  · simp [Circuit.size] at h2
  have hg : g ∈ (⟨g :: q :: gs, out⟩ : Circuit).gates := by simp
  have hq : q ∈ (⟨g :: q :: gs, out⟩ : Circuit).gates := by simp
  obtain ⟨a, b, hab⟩ := list_pair (hC.2.2 g hg)
  obtain ⟨c, d, hcd⟩ := list_pair (hC.2.2 q hq)
  have h0 : ∀ i ∈ g.inputs, i < 14 := hC.2.1 0 (by simp)
  have h1 : ∀ i ∈ q.inputs, i < 15 := hC.2.1 1 (by simp)
  have ha : a < 14 := h0 a (by simp [hab])
  have hb : b < 14 := h0 b (by simp [hab])
  have hc : c < 15 := h1 c (by simp [hcd])
  have hd : d < 15 := h1 d (by simp [hcd])
  have hne1 : a ≠ b := by simpa [hab] using hn g hg
  have hne2 : c ≠ d := by simpa [hcd] using hn q hq
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩,
    fun h => hne1 (congrArg Fin.val h), fun h => hne2 (congrArg Fin.val h),
    g.op, q.op, ⟨gs, out⟩, hC.1 g hg, hC.1 q hq, ?_, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ (⟨g :: q :: gs, out⟩ : Circuit).gates := by simp [ht]
    have hop := hC.1 t ht'
    exact ⟨by simpa using hop, le_of_eq (hC.2.2 t ht')⟩
  · change gs.length ≤ 24
    simp only [Circuit.size, List.length_cons] at h26
    omega
  · intro x
    have hga : (List.ofFn x).getD a false = x ⟨a, ha⟩ := ofFn_get x ⟨a, ha⟩
    have hgb : (List.ofFn x).getD b false = x ⟨b, hb⟩ := ofFn_get x ⟨b, hb⟩
    simpa only [Circuit.eval, Circuit.wires, List.foldl_cons, hab, hcd,
      List.map_cons, List.map_nil, hga, hgb, extendedInput, initial] using he x

end PEqualNP.Outside.L_meta_3010_aux

open PEqualNP.Outside.L_meta_3010_aux

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro F C hC hn h2 h26 hE
  classical
  let achievable (k : ℕ) : Prop :=
    ∃ (a b : Fin 14) (c d : Fin 15), Valid F a b c d ∧ rank a b c d = k
  obtain ⟨a₀, b₀, c₀, d₀, h₀⟩ := has_valid F C hC hn h2 h26 hE
  have hex : ∃ k, achievable k := ⟨rank a₀ b₀ c₀ d₀, a₀, b₀, c₀, d₀, h₀, rfl⟩
  obtain ⟨a, b, c, d, h, hr⟩ := Nat.find_spec hex
  have hs := valid_sorted F a b c d h
  have hWitness := hs
  obtain ⟨_, _, o, q, D, ho, hq, hmono, hsize, hEval⟩ := hWitness
  refine ⟨min a b, max a b, min c d, max c d, o, q, D,
    sorted_lt h.1, sorted_lt h.2.1, ho, hq, ?_, hmono, hsize, hEval⟩
  intro p hp
  have heq := (rank_sorted a b c d).trans hr
  have hnext := valid_mapped F (min a b) (max a b) (min c d) (max c d) p hp hs
  have hmin := Nat.find_min' hex
    (show achievable (rank (p (min a b)) (p (max a b)) (finWire p (min c d))
      (finWire p (max c d))) from ⟨_, _, _, _, hnext, rfl⟩)
  rw [← heq] at hmin
  rw [finWire_eq p (min c d), finWire_eq p (max c d)] at hmin
  exact hmin
