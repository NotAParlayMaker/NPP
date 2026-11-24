import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def step (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op.eval (g.inputs.map fun i => wires.getD i false)]

theorem length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem length_wires {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  change (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length
  simp [length_run]

theorem run_preserves_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem read_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (C.gates.foldl step (List.ofFn x)).getD i.val false = x i
  rw [run_preserves_input _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem read_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega), List.getD_append _ _ _ _ h]
  · subst i
    rw [ite_eq_left rfl, List.getD_append_right _ _ _ _ le_rfl]
    simp
  · rw [ite_eq_right (by omega), List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

-- Original inputs use the embedding. Gate wires keep their offsets past the inputs.
def renameWire {n m : ℕ} (embed : Fin n → Fin m) (i : ℕ) : ℕ :=
  if hi : i < n then (embed ⟨i, hi⟩).val else m + (i - n)

theorem renameWire_lt {n m : ℕ} (embed : Fin n → Fin m) {i k : ℕ}
    (hi : i < n + k) : renameWire embed i < m + k := by
  unfold renameWire
  split
  · have := (embed ⟨i, by assumption⟩).isLt
    omega
  · omega

theorem renameWire_boundary {n m : ℕ} (embed : Fin n → Fin m) (i k : ℕ) :
    renameWire embed i = m + k ↔ i = n + k := by
  unfold renameWire
  split
  · have := (embed ⟨i, by assumption⟩).isLt
    omega
  · omega

def renameGate {n m : ℕ} (embed : Fin n → Fin m) (g : Gate) : Gate :=
  {g with inputs := g.inputs.map (renameWire embed)}

def rename {n m : ℕ} (embed : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate embed), renameWire embed C.output⟩

theorem rename_size {n m : ℕ} (embed : Fin n → Fin m) (C : Circuit) :
    (rename embed C).size = C.size := by simp [rename, Circuit.size]

theorem rename_AO {n m : ℕ} (embed : Fin n → Fin m) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 m (rename embed C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨original, hm, rfl⟩ := List.mem_map.mp hg
    exact h.1 original hm
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [rename] using hj
    have hg : gateAt (rename embed C) j = renameGate embed (gateAt C j) := by
      simp [gateAt, rename, hj']
    rw [hg] at hi
    obtain ⟨wire, hm, rfl⟩ := List.mem_map.mp hi
    exact renameWire_lt embed (h.2.1 j hj' wire hm)
  · intro g hg
    obtain ⟨original, hm, rfl⟩ := List.mem_map.mp hg
    simpa [renameGate] using h.2.2 original hm

theorem rename_run {n m : ℕ} (embed : Fin n → Fin m) (gs : List Gate)
    (u v : List Bool) (k : ℕ) (hu : u.length = n + k) (hv : v.length = m + k)
    (h : ∀ i, u.getD i false = v.getD (renameWire embed i) false) :
    ∀ i, (gs.foldl step u).getD i false =
      ((gs.map (renameGate embed)).foldl step v).getD (renameWire embed i) false := by
  induction gs generalizing u v k with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    refine ih _ _ (k + 1) (by simp [step, hu, Nat.add_assoc])
      (by simp [step, hv, Nat.add_assoc]) ?_
    intro i
    have he : (renameWire embed i = v.length) ↔ i = u.length := by
      rw [hu, hv, renameWire_boundary]
    simp only [step, read_snoc, he, renameGate, List.map_map, Function.comp_def, h]

theorem rename_value {n m : ℕ} (embed : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    circuitFun m (rename embed C) x = circuitFun n C (fun i => x (embed i)) := by
  let u := List.ofFn (fun i => x (embed i))
  let v := List.ofFn x
  have h : ∀ i, u.getD i false = v.getD (renameWire embed i) false := by
    intro i
    by_cases hi : i < n
    · simp [u, v, renameWire, hi, List.getD_eq_getElem?_getD, (embed ⟨i, hi⟩).isLt]
    · rw [List.getD_eq_default _ _ (by simp [u]; omega),
        List.getD_eq_default _ _ (by simp [v, renameWire, hi])]
  exact (rename_run embed C.gates u v 0 (by simp [u]) (by simp [v]) h C.output).symm

-- The new gate becomes the output wire and leaves the earlier wires intact.
def appendGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.size⟩

theorem append_size (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (appendGate n C op a b).size = C.size + 1 := by simp [appendGate, Circuit.size]

theorem append_AO (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (h : IsAO2 n C) (hop : op = .and ∨ op = .or)
    (ha : a < n + C.size) (hb : b < n + C.size) : IsAO2 n (appendGate n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendGate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 g hg
    · exact hop
  · intro j hj i hi
    by_cases hj' : j < C.gates.length
    · have hg : gateAt (appendGate n C op a b) j = gateAt C j :=
        List.getD_append _ _ _ _ hj'
      rw [hg] at hi
      exact h.2.1 j hj' i hi
    · have hindex : j = C.gates.length := by simp [appendGate] at hj; omega
      subst j
      have hg : gateAt (appendGate n C op a b) C.gates.length = ⟨op, [a, b]⟩ := by
        simp [gateAt, appendGate]
      rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendGate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.2.2 g hg
    · rfl

theorem appended_wires {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    (appendGate n C op a b).wires (List.ofFn x) =
      step (C.wires (List.ofFn x)) ⟨op, [a, b]⟩ := by
  simp only [appendGate, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem append_value {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    circuitFun n (appendGate n C op a b) x =
      op.eval [(C.wires (List.ofFn x)).getD a false, (C.wires (List.ofFn x)).getD b false] := by
  unfold circuitFun Circuit.eval
  rw [appended_wires]
  change (step (C.wires (List.ofFn x)) ⟨op, [a, b]⟩).getD (n + C.size) false = _
  rw [← length_wires C x]
  simp [step]

theorem extend_edge {n : ℕ} (C : Circuit) (a b : Fin n) (h : IsAO2 n C)
    (hout : C.output < n + C.size) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size + 2 ∧ D.output < n + D.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = (circuitFun n C x || (x a && x b)) := by
  let A := appendGate n C .and a b
  let D := appendGate n A .or C.output (n + C.size)
  have hA : A.size = C.size + 1 := append_size _ _ _ _ _
  have hAout : A.output = n + C.size := rfl
  have hAao : IsAO2 n A :=
    append_AO _ _ _ _ _ h (Or.inl rfl) (by have := a.isLt; omega) (by have := b.isLt; omega)
  have hD : D.size = C.size + 2 := by
    change (appendGate n A .or C.output (n + C.size)).size = _
    rw [append_size, hA]
  have hDout : D.output = n + A.size := rfl
  have hDao : IsAO2 n D :=
    append_AO n A .or C.output (n + C.size) hAao (Or.inr rfl) (by omega) (by omega)
  refine ⟨D, hDao, hD, by omega, ?_⟩
  intro x
  have hp : (A.wires (List.ofFn x)).getD C.output false = circuitFun n C x := by
    change ((appendGate n C .and a b).wires (List.ofFn x)).getD C.output false = _
    rw [appended_wires]
    exact List.getD_append _ _ _ _ (by rwa [length_wires])
  have ha : circuitFun n A x = (x a && x b) := by
    change circuitFun n (appendGate n C .and a b) x = _
    rw [append_value, read_input, read_input]
    simp [GateOp.eval]
  change circuitFun n (appendGate n A .or C.output (n + C.size)) x = _
  rw [append_value, hp, ← hAout]
  change GateOp.or.eval [circuitFun n C x, circuitFun n A x] = _
  simp [ha, GateOp.eval]

def edgeValue {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Fin (n + n) → Bool) : Bool :=
  decide (∃ a b : Fin n, (a, b) ∈ edges ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)

theorem add_edges {n : ℕ} (base extra : Finset (Fin n × Fin n)) (C : Circuit)
    (h : IsAO2 (n + n) C) (hout : C.output < n + n + C.size)
    (hc : ∀ x, circuitFun (n + n) C x = edgeValue base x) :
    ∃ D : Circuit, IsAO2 (n + n) D ∧ D.size ≤ C.size + 2 * extra.card ∧
      D.output < n + n + D.size ∧ ∀ x, circuitFun (n + n) D x = edgeValue (base ∪ extra) x := by
  induction extra using Finset.induction_on with
  | empty => exact ⟨C, h, by simp, hout, by simpa using hc⟩
  | @insert p edges hp ih =>
    obtain ⟨A, hA, hsA, hoA, heA⟩ := ih
    obtain ⟨D, hD, hsD, hoD, heD⟩ :=
      extend_edge A (Fin.castAdd n p.1) (Fin.natAdd n p.2) hA hoA
    have hs : D.size ≤ C.size + 2 * (insert p edges).card := by
      rw [Finset.card_insert_of_notMem hp]
      omega
    refine ⟨D, hD, hs, hoD, ?_⟩
    intro x
    rw [heD, heA]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, edgeValue, decide_eq_true_eq,
      Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (⟨a, b,hab, hxa, hxb⟩ | ⟨ha, hb⟩)
      · exact ⟨a, b,hab.imp_right Or.inr,hxa,hxb⟩
      · exact ⟨p.1,p.2,Or.inr (Or.inl (Prod.eta p)),ha, hb⟩
    · rintro ⟨a, b,(hab | hab | hab),ha, hb⟩
      · exact Or.inl ⟨a, b,Or.inl hab,ha, hb⟩
      · obtain ⟨hpa,hpb⟩ := Prod.mk.inj hab
        exact Or.inr ⟨hpa ▸ ha,hpb ▸ hb⟩
      · exact Or.inl ⟨a, b,Or.inr hab,ha, hb⟩

def splitEmbed (p q : ℕ) : Fin (p + q) → Fin ((p + q)+(p + q)) :=
  Fin.addCases (fun i => Fin.castAdd (p + q) (Fin.castAdd q i))
    (fun j => Fin.natAdd (p + q) (Fin.natAdd p j))

end PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
     x3.Nonempty →
       PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →
         (∀ (x7 : Fin (x1 + x2) → Bool),
           PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 =
             Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2),
               (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧
               x7 (Fin.natAdd x1 x9) = Bool.true)) →
           let x8 : ℕ := x1 + x2;
           have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) :=
             Finset.image (fun (x9 : Fin x1 × Fin x2) =>
               (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;
           ∀ (x10 : Finset (Fin x8 × Fin x8)),
             ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
               PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧
                 ∀ (x12 : Fin (x8 + x8) → Bool),
                   PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 =
                     Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)),
                       (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧
                       x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro p q edges C hnon hAO hval
  dsimp only
  intro extras
  let n := p + q
  let embed := splitEmbed p q
  let base : Finset (Fin n × Fin n) :=
    edges.image (fun e => (Fin.castAdd q e.1, Fin.natAdd p e.2))
  let A := rename embed C
  have hc : ∀ x, circuitFun (n + n) A x = edgeValue base x := by
    intro x
    change circuitFun (n + n) (rename embed C) x = _
    rw [rename_value, hval]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, edgeValue]
    constructor
    · rintro ⟨a, b,he, ha, hb⟩
      refine ⟨Fin.castAdd q a, Fin.natAdd p b, Finset.mem_image_of_mem _ he, ?_, ?_⟩
      · simpa [embed, splitEmbed] using ha
      · simpa [embed, splitEmbed] using hb
    · rintro ⟨a, b,he, ha, hb⟩
      obtain ⟨⟨i, j⟩, hij, he⟩ := Finset.mem_image.mp he
      obtain ⟨hi, hj⟩ := Prod.mk.inj he
      subst a
      subst b
      exact ⟨i, j,hij, by simpa [embed, splitEmbed] using ha, by simpa [embed, splitEmbed] using hb⟩
  have hout : C.output < n + C.size := by
    by_contra! h
    let allTrue : Fin (p + q) → Bool := fun _ => true
    have hone : circuitFun n C allTrue = true := by
      rw [hval]
      obtain ⟨⟨a, b⟩, hab⟩ := hnon
      exact decide_eq_true ⟨a, b,hab,rfl,rfl⟩
    change (C.wires (List.ofFn allTrue)).getD C.output false = true at hone
    rw [List.getD_eq_default _ _ (by rwa [length_wires])] at hone
    cases hone
  have hsize : A.size = C.size := rename_size _ _
  have hAout : A.output < n + n + A.size := by
    rw [hsize]
    exact renameWire_lt embed hout
  obtain ⟨D, hD, hs, _, hvalue⟩ := add_edges base extras A (rename_AO embed C hAO) hAout hc
  exact ⟨D, hD, hsize ▸ hs, hvalue⟩
