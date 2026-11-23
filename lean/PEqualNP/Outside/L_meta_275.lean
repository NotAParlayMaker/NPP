import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta275

abbrev Mask := Finset (Fin 7)

def target : Fin 4 → Mask := ![{0,1,2},{0,3,4},{0,5,6},{1,3,5}]

private theorem target_card (i : Fin 4) : (target i).card = 3 := by
  revert i
  decide

private theorem pair_determines_target (p : Mask) (hp : p.card = 2) {i j : Fin 4}
    (hi : p ⊆ target i) (hj : p ⊆ target j) : i = j := by
  by_contra hij
  have hcross : ∀ a b : Fin 4, a ≠ b → (target a ∩ target b).card ≤ 1 := by decide
  have hs : p ⊆ target i ∩ target j := fun x hx => Finset.mem_inter.mpr ⟨hi hx, hj hx⟩
  have hle := (Finset.card_le_card hs).trans (hcross i j hij)
  omega

private theorem obstruction (H : Finset Mask) (hh : H.card ≤ 3)
    (hw : ∀ i : Fin 4, ∃ x y : Mask,
      (x.card ≤ 1 ∨ x ∈ H ∨ ∃ j : Fin 4, x = target j) ∧
      (y.card ≤ 1 ∨ y ∈ H ∨ ∃ j : Fin 4, y = target j) ∧
      x ≠ target i ∧ y ≠ target i ∧ (x ∪ y = target i ∨ x ∩ y = target i)) : False := by
  classical
  let P := H.filter (fun u => u.card = 2)
  let K := H.filter (fun u => 4 ≤ u.card)
  let pick (u : Mask) : Fin 4 :=
    if h : ∃ i, u ⊆ target i then Classical.choose h else 0
  let cover := (P.image (fun u => target (pick u))) ∪
    ((K.powersetCard 2).image (fun s : Finset Mask => s.inf id))
  have hmem (i : Fin 4) : target i ∈ cover := by
    obtain ⟨x,y,hx,hy,hx_ne,hy_ne,h⟩ := hw i
    have source (z : Mask) (hz : z.card ≤ 1 ∨ z ∈ H ∨ ∃ j, z = target j)
        (hlo : 2 ≤ z.card) (hne : z.card ≠ 3) : z ∈ H := by
      rcases hz with ht | hm | ⟨j,rfl⟩
      · omega
      · exact hm
      · exact (hne (target_card j)).elim
    have hcard := target_card i
    rcases h with h | h
    · have hxs : x ⊆ target i := h ▸ Finset.subset_union_left
      have hys : y ⊆ target i := h ▸ Finset.subset_union_right
      have hxc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hxs,hx_ne⟩)
      have hyc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hys,hy_ne⟩)
      have hsize := Finset.card_union_le x y
      rw [h] at hsize
      have use_pair (u : Mask) (hu : u.card = 2) (hs : u ⊆ target i)
          (hm : u ∈ H) : target i ∈ cover := by
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨u, Finset.mem_filter.mpr ⟨hm,hu⟩, ?_⟩
        have hit : ∃ j, u ⊆ target j := ⟨i,hs⟩
        dsimp only [pick]
        rw [dite_eq_left hit, pair_determines_target u hu (Classical.choose_spec hit) hs]
      by_cases hxx : x.card = 2
      · exact use_pair x hxx hxs (source x hx (by omega) (by omega))
      · have hyy : y.card = 2 := by omega
        exact use_pair y hyy hys (source y hy (by omega) (by omega))
    · have hxs : target i ⊆ x := h ▸ Finset.inter_subset_left
      have hys : target i ⊆ y := h ▸ Finset.inter_subset_right
      have hxc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hxs,Ne.symm hx_ne⟩)
      have hyc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hys,Ne.symm hy_ne⟩)
      have hxK : x ∈ K := Finset.mem_filter.mpr ⟨source x hx (by omega) (by omega), by omega⟩
      have hyK : y ∈ K := Finset.mem_filter.mpr ⟨source y hy (by omega) (by omega), by omega⟩
      have hxy : x ≠ y := by
        intro e
        subst y
        exact hx_ne (by simpa using h)
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨{x,y}, Finset.mem_powersetCard.mpr ⟨?_, by simp [hxy]⟩, ?_⟩
      · intro z hz
        rcases (by simpa using hz : z = x ∨ z = y) with rfl | rfl <;> assumption
      · simpa using h
  have hall : (Finset.univ.image target) ⊆ cover := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact hmem i
  have hfour : (Finset.univ.image target).card = 4 := by decide
  have hcount := Finset.card_le_card hall
  have hu := Finset.card_union_le (P.image (fun u => target (pick u)))
    ((K.powersetCard 2).image (fun s : Finset Mask => s.inf id))
  have hp := Finset.card_image_le (s := P) (f := fun u => target (pick u))
  have hk := Finset.card_image_le (s := K.powersetCard 2) (f := fun s : Finset Mask => s.inf id)
  have hbound : 4 ≤ P.card + K.card.choose 2 := by
    change (Finset.univ.image target).card ≤
      (P.image (fun u => target (pick u)) ∪
        (K.powersetCard 2).image (fun s : Finset Mask => s.inf id)).card at hcount
    rw [Finset.card_powersetCard] at hk
    omega
  have hdis : Disjoint P K := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h1 : x.card = 2 := (Finset.mem_filter.mp hx).2
    have h2 : 4 ≤ x.card := (Finset.mem_filter.mp hy).2
    omega
  have hboth : P ∪ K ⊆ H := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hle := (Finset.card_le_card hboth).trans hh
  rw [Finset.card_union_of_disjoint hdis] at hle
  have small_count : ∀ a b : Fin 4, a.val + b.val ≤ 3 → a.val + b.val.choose 2 ≤ 3 := by decide
  have hsmall : P.card + K.card.choose 2 ≤ 3 :=
    small_count ⟨P.card, by omega⟩ ⟨K.card, by omega⟩ hle
  omega

open PEqualNP.CircuitLowerBounds

private def hits275 (p : Fin 7) (v : Mask) : Bool := decide (p ∈ v)

private def isAnd275 : GateOp → Bool
  | .and => true
  | _ => false

private def step275 (w : List Mask) (g : Gate) : Mask :=
  let x := w.getD (g.inputs.getD 0 0) ∅
  let y := w.getD (g.inputs.getD 1 0) ∅
  if isAnd275 g.op then x ∩ y else x ∪ y

private def outs275 : List Gate → List Mask → List Mask
  | [], _ => []
  | g :: gs, w => step275 w g :: outs275 gs (w ++ [step275 w g])

private def base275 : List Mask := List.ofFn fun p : Fin 7 => {p}

private def boolRun275 (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private theorem getMask275 (w : List Mask) (i : ℕ) : w.getD i ∅ = ∅ ∨ w.getD i ∅ ∈ w := by
  by_cases hi : i < w.length
  · right
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · left
    exact List.getD_eq_default _ _ (by omega)

private theorem mapGet275 (p : Fin 7) (w : List Mask) (i : ℕ) :
    (w.map (hits275 p)).getD i false = hits275 p (w.getD i ∅) := by
  by_cases hi : i < w.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [hits275]

private theorem evalStep275 (p : Fin 7) (w : List Mask) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    g.op.eval (g.inputs.map fun i => (w.map (hits275 p)).getD i false) =
    hits275 p (step275 w g) := by
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hg.2
  simp only [he, List.map_cons, List.map_nil, mapGet275]
  rcases hg.1 with hand | hor
  · simp [step275, he, hand, GateOp.eval, isAnd275, hits275]
  · simp [step275, he, hor, GateOp.eval, isAnd275, hits275]

private theorem evalRun275 (p : Fin 7) (gs : List Gate) (w : List Mask)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    boolRun275 gs (w.map (hits275 p)) = (w ++ outs275 gs w).map (hits275 p) := by
  induction gs generalizing w with
  | nil => simp [boolRun275, outs275]
  | cons g gs ih =>
    have hs := evalStep275 p w g (hg _ List.mem_cons_self)
    change boolRun275 gs (w.map (hits275 p) ++ [_]) = _
    rw [hs]
    have he := ih (w ++ [step275 w g]) (fun t ht => hg t (List.mem_cons_of_mem _ ht))
    simpa [outs275, List.append_assoc] using he

private theorem gatesLen275 (gs : List Gate) (w : List Mask) : (outs275 gs w).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [outs275, ih]

private theorem baseSmall275 (x : Mask) (hx : x ∈ base275) : x.card ≤ 1 := by
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hx
  simp

private theorem first275 (z : Mask) (nz : z ≠ ∅) (U : Finset Mask)
    (gs : List Gate) (w : List Mask) (hn : z ∉ w)
    (hw : ∀ x ∈ w, x.card ≤ 1 ∨ x ∈ U)
    (hu : ∀ x ∈ outs275 gs w, x ∈ U) (hz : z ∈ outs275 gs w) :
    ∃ x y : Mask, (x.card ≤ 1 ∨ x ∈ U) ∧ (y.card ≤ 1 ∨ y ∈ U) ∧
      x ≠ z ∧ y ≠ z ∧ (x ∪ y = z ∨ x ∩ y = z) := by
  induction gs generalizing w with
  | nil => simp [outs275] at hz
  | cons g gs ih =>
    let v := step275 w g
    have hv : v ∈ U := hu _ List.mem_cons_self
    by_cases he : v = z
    · have get (i : ℕ) : (w.getD i ∅).card ≤ 1 ∨ w.getD i ∅ ∈ U := by
        rcases getMask275 w i with h | h
        · rw [h]; simp
        · exact hw _ h
      have ne (i : ℕ) : w.getD i ∅ ≠ z := by
        intro eq
        rcases getMask275 w i with h | h
        · exact nz (eq.symm.trans h)
        · exact hn (eq ▸ h)
      refine ⟨_, _, get (g.inputs.getD 0 0), get (g.inputs.getD 1 0),
        ne _, ne _, ?_⟩
      by_cases hop : isAnd275 g.op = true
      · right
        simpa [v, step275, hop] using he
      · left
        simpa [v, step275, hop] using he
    · apply ih (w ++ [v])
      · simp [Ne.symm he, hn]
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hw _ hx
        · have : x = v := by simpa using hx
          exact Or.inr (this ▸ hv)
      · exact fun x hx => hu x (List.mem_cons_of_mem _ hx)
      · exact (List.mem_cons.mp hz).resolve_left (Ne.symm he)

private theorem bridge275 (C : Circuit) (o : Fin 4 → ℕ) (hs : C.size ≤ 7)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (hout : ∀ i : Fin 4, ∀ p : Fin 7,
      (C.wires (List.ofFn (fun q : Fin 7 => decide (q = p)))).getD (o i) false = true ↔
      p ∈ target i) :
    ∃ H : Finset Mask, H.card ≤ 3 ∧ ∀ i : Fin 4, ∃ x y : Mask,
      (x.card ≤ 1 ∨ x ∈ H ∨ ∃ j : Fin 4, x = target j) ∧
      (y.card ≤ 1 ∨ y ∈ H ∨ ∃ j : Fin 4, y = target j) ∧
      x ≠ target i ∧ y ≠ target i ∧ (x ∪ y = target i ∨ x ∩ y = target i) := by
  classical
  let outs := outs275 C.gates base275
  let U := outs.toFinset
  let T := Finset.univ.image target
  have htSize : ∀ i, (target i).card = 3 := by decide
  have ht : T.card = 4 := by decide
  have val (p : Fin 7) : C.wires (List.ofFn fun q : Fin 7 => decide (q = p)) =
      (base275 ++ outs).map (hits275 p) := by
    have hbase : List.ofFn (fun q : Fin 7 => decide (q = p)) = base275.map (hits275 p) := by
      simp [base275, hits275, eq_comm]
    change boolRun275 C.gates _ = _
    rw [hbase]
    exact evalRun275 _ _ _ hg
  have occurs (i : Fin 4) : target i ∈ outs := by
    have eqv : (base275 ++ outs).getD (o i) ∅ = target i := by
      ext p
      have e := hout i p
      rw [val, mapGet275] at e
      simpa [hits275] using e
    rcases getMask275 (base275 ++ outs) (o i) with h | h
    · have hz : target i = ∅ := eqv.symm.trans h
      have := htSize i
      simp [hz] at this
    · rw [eqv, List.mem_append] at h
      exact h.resolve_left (fun hh => by have := baseSmall275 _ hh; rw [htSize] at this; omega)
  have sub : T ⊆ U := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (occurs i)
  have hU : U.card ≤ 7 := by
    have h := outs.toFinset_card_le
    have hl : outs.length = C.gates.length := gatesLen275 _ _
    change outs.toFinset.card ≤ 7
    change C.gates.length ≤ 7 at hs
    omega
  refine ⟨U \ T, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset sub, ht]
    omega
  · intro i
    have hn : target i ∉ base275 := fun h => by
      have := baseSmall275 _ h
      rw [htSize] at this
      omega
    have nz : target i ≠ ∅ := fun h => by have := htSize i; simp [h] at this
    obtain ⟨x,y,hx,hy,hxz,hyz,hop⟩ := first275 (target i) nz U C.gates base275 hn
      (fun a ha => Or.inl (baseSmall275 _ ha)) (fun a ha => List.mem_toFinset.mpr ha) (occurs i)
    have classify (a : Mask) (ha : a.card ≤ 1 ∨ a ∈ U) :
        a.card ≤ 1 ∨ a ∈ U \ T ∨ ∃ j : Fin 4, a = target j := by
      rcases ha with small | hu
      · exact Or.inl small
      · by_cases h : a ∈ T
        · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
          exact Or.inr (Or.inr ⟨j, hj.symm⟩)
        · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hu,h⟩))
    exact ⟨x,y,classify _ hx,classify _ hy,hxz,hyz,hop⟩

end PEqualNP.Outside.Meta275

open PEqualNP.Outside.Meta275

theorem PEqualNP.Outside.L_meta_275 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 4 → ℕ), C.size ≤ 7 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 4, (∀ p : Fin 7, (C.wires (List.ofFn (fun q : Fin 7 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i) ∧ ∀ x : Fin 7 → Bool, (Finset.univ.filter (fun q : Fin 7 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hs, hg, hout⟩
  obtain ⟨H, hh, hw⟩ := bridge275 C o hs hg (fun i => (hout i).1)
  exact obstruction H hh hw
