import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3063

open PEqualNP.CircuitLowerBounds

def grow {α β : Type*} (f : List α → β → α) (gs : List β) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem grow_append {α β : Type*} (f : List α → β → α)
    (gs hs : List β) (w : List α) :
    grow f (gs ++ hs) w = grow f hs (grow f gs w) := by
  simp [grow, List.foldl_append]

theorem grow_prefix {α β : Type*} (f : List α → β → α) (gs : List β) :
    ∀ w : List α, ∃ t : List α, grow f gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [grow], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    change grow f gs (w ++ [f w g]) = w ++ f w g :: t
    rw [ht]
    simp

theorem grow_length {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) :
    (grow f gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := grow_prefix f gs w
  rw [ht]
  simp [hl]

theorem grow_getD_lt {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (i : ℕ) (d : α) (h : i < w.length) :
    (grow f gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := grow_prefix f gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem grow_gate {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j : ℕ) (hj : j < gs.length) :
    (grow f gs w).getD (w.length + j) d = f (grow f (gs.take j) w) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set A := grow f (gs.take j) w with hA
  have hAl : A.length = w.length + j := by
    rw [hA, grow_length]
    simp
    omega
  have hw : grow f gs w = grow f (gs.drop (j + 1)) (A ++ [f A gs[j]]) := by
    conv_lhs => rw [hsplit]
    rw [grow_append]
    rfl
  rw [hw, grow_getD_lt _ _ _ _ _ (by simp [hAl]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp [hAl]

theorem grow_take_read {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j i : ℕ) (hj : j ≤ gs.length) :
    (grow f (gs.take j) w).getD i d =
      if i < w.length + j then (grow f gs w).getD i d else d := by
  have hlen : (grow f (gs.take j) w).length = w.length + j := by
    rw [grow_length, List.length_take, Nat.min_eq_left hj]
  by_cases hi : i < w.length + j
  · rw [ite_eq_left hi]
    conv_rhs => rw [← List.take_append_drop j gs, grow_append]
    exact (grow_getD_lt _ _ _ _ _ (by omega)).symm
  · rw [ite_eq_right hi]
    apply List.getD_eq_default
    omega

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq_grow (C : Circuit) (x : List Bool) :
    C.wires x = grow gateValue C.gates x := rfl

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := grow_getD_lt _ _ _ _ _ hi

theorem wires_gate (C : Circuit) (x : List Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  rw [wires_eq_grow, grow_gate _ _ _ _ _ hj]
  unfold gateValue
  congr 1
  apply List.map_congr_left
  intro i _
  exact grow_take_read _ _ _ _ j i (Nat.le_of_lt hj)

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]

theorem wire_rb (C : Circuit) (N : ℕ) (x : List Bool) (hx : x.length = N)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
          fun i => (C.wires x).getD i false) := by
  subst hx
  rw [wires_gate C x j hj, gateAt_eq C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  simp [this]

def uv (N e : ℕ) : List Bool := (List.range N).map (fun t => decide (t = e))

theorem uv_length (N e : ℕ) : (uv N e).length = N := by simp [uv]

theorem uv_getD (N e t : ℕ) (ht : t < N) : (uv N e).getD t false = decide (t = e) := by
  simp [uv, List.getD_eq_getElem?_getD, ht]

def V (C : Circuit) (N w : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun e => (C.wires (uv N e)).getD w false = true)

theorem V_input (C : Circuit) (N w : ℕ) (hw : w < N) : V C N w = {w} := by
  ext e
  simp only [V, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  rw [wires_input C _ w (by rw [uv_length]; exact hw), uv_getD N e w hw]
  constructor
  · rintro ⟨_, h⟩
    exact (of_decide_eq_true h).symm
  · rintro rfl
    exact ⟨hw, by simp⟩

theorem V_or (C : Circuit) (N : ℕ) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (j : ℕ) (hj : j < C.gates.length) (u v : ℕ)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or)
    (hin : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [u, v]) :
    V C N (N + j) = V C N u ∪ V C N v := by
  ext e
  simp only [V, Finset.mem_filter, Finset.mem_range, Finset.mem_union]
  rw [wire_rb C N _ (uv_length N e) hrb j hj, hop, hin]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    Bool.or_false, id, Bool.or_eq_true]
  tauto

theorem V_rect (C : Circuit) (N w : ℕ) (S : Finset ℕ) (hS : ∀ e ∈ S, e < N)
    (hall : ∀ x : List Bool, x.length = N →
      ((C.wires x).getD w false = true ↔ ∃ e ∈ S, x.getD e false = true)) :
    V C N w = S := by
  ext e
  simp only [V, Finset.mem_filter, Finset.mem_range]
  rw [hall _ (uv_length N e)]
  constructor
  · rintro ⟨_, e', he', h⟩
    rw [uv_getD N e e' (hS e' he')] at h
    have := of_decide_eq_true h
    subst this
    exact he'
  · intro he
    exact ⟨hS e he, e, he, by rw [uv_getD N e e (hS e he)]; simp⟩

theorem getD_L {n m : ℕ} (F : Fin n → Bool) (G : Fin m → Bool) (p : Fin n) :
    (List.ofFn F ++ List.ofFn G).getD p.val false = F p := by
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem getD_R {n m : ℕ} (F : Fin n → Bool) (G : Fin m → Bool) (l : Fin m) :
    (List.ofFn F ++ List.ofFn G).getD (n + l.val) false = G l := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem uf (N0 s : ℕ) (V : ℕ → Finset ℕ) (hin : ∀ w < N0, V w = {w})
    (hor : ∀ j < s, ∃ u v, u < N0 + j ∧ v < N0 + j ∧ V (N0 + j) = V u ∪ V v)
    (Z U : Finset ℕ) : ∀ N, N ≤ s → ∀ W : Finset ℕ, (∀ w ∈ W, w < N0 + N ∧ V w ⊆ Z) →
      ((W.biUnion V) ∩ U).card ≤ W.card +
        ((Finset.range N).filter (fun j => V (N0 + j) ⊆ Z ∧ 2 ≤ (V (N0 + j) ∩ U).card)).card := by
  intro N
  induction N with
  | zero =>
    intro _ W hW
    have h1 : ((W.biUnion V) ∩ U).card ≤ W.card := by
      calc ((W.biUnion V) ∩ U).card ≤ (W.biUnion V).card := Finset.card_le_card Finset.inter_subset_left
        _ ≤ ∑ w ∈ W, (V w).card := Finset.card_biUnion_le
        _ = ∑ w ∈ W, 1 := Finset.sum_congr rfl (fun w hw => by
            rw [hin w (by have := (hW w hw).1; omega)]; simp)
        _ = W.card := by simp
    omega
  | succ N ih =>
    intro hN W hW
    have hF : ((Finset.range (N + 1)).filter (fun j => V (N0 + j) ⊆ Z ∧ 2 ≤ (V (N0 + j) ∩ U).card)).card
        = ((Finset.range N).filter (fun j => V (N0 + j) ⊆ Z ∧ 2 ≤ (V (N0 + j) ∩ U).card)).card +
          (if V (N0 + N) ⊆ Z ∧ 2 ≤ (V (N0 + N) ∩ U).card then 1 else 0) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    by_cases hmem : N0 + N ∈ W
    · obtain ⟨u, v, hu, hv, hV⟩ := hor N (by omega)
      have hZ0 := (hW _ hmem).2
      have hcW : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hmem⟩
      have hce := Finset.card_erase_of_mem hmem
      by_cases h2 : 2 ≤ (V (N0 + N) ∩ U).card
      · have hW' : ∀ w ∈ (W.erase (N0 + N)) ∪ {u, v}, w < N0 + N ∧ V w ⊆ Z := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · obtain ⟨hne, hw⟩ := Finset.mem_erase.1 hw
            exact ⟨by have := (hW w hw).1; omega, (hW w hw).2⟩
          · rcases Finset.mem_insert.1 hw with rfl | hw
            · exact ⟨hu, fun x hx => hZ0 (by rw [hV]; exact Finset.mem_union_left _ hx)⟩
            · rw [Finset.mem_singleton] at hw
              subst hw
              exact ⟨hv, fun x hx => hZ0 (by rw [hV]; exact Finset.mem_union_right _ hx)⟩
        have hsub : (W.biUnion V) ∩ U ⊆ (((W.erase (N0 + N)) ∪ {u, v}).biUnion V) ∩ U := by
          intro x hx
          rw [Finset.mem_inter, Finset.mem_biUnion] at hx ⊢
          obtain ⟨⟨w, hw, hxw⟩, hxU⟩ := hx
          refine ⟨?_, hxU⟩
          by_cases hwe : w = N0 + N
          · subst hwe
            rw [hV] at hxw
            rcases Finset.mem_union.1 hxw with h | h
            · exact ⟨u, by simp, h⟩
            · exact ⟨v, by simp, h⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwe, hw⟩), hxw⟩
        have hc1 := Finset.card_le_card hsub
        have hc2 := ih (by omega) _ hW'
        have hc3 : ((W.erase (N0 + N)) ∪ {u, v}).card ≤ (W.erase (N0 + N)).card + 2 := by
          calc _ ≤ (W.erase (N0 + N)).card + ({u, v} : Finset ℕ).card := Finset.card_union_le _ _
            _ ≤ _ := by have := Finset.card_le_two (a := u) (b := v); omega
        rw [hF, ite_eq_left_iff.mpr (fun h => absurd ⟨hZ0, h2⟩ h)]
        omega
      · have hW' : ∀ w ∈ W.erase (N0 + N), w < N0 + N ∧ V w ⊆ Z := by
          intro w hw
          obtain ⟨hne, hw⟩ := Finset.mem_erase.1 hw
          exact ⟨by have := (hW w hw).1; omega, (hW w hw).2⟩
        have hsub : (W.biUnion V) ∩ U ⊆ (((W.erase (N0 + N)).biUnion V) ∩ U) ∪ (V (N0 + N) ∩ U) := by
          intro x hx
          rw [Finset.mem_inter, Finset.mem_biUnion] at hx
          obtain ⟨⟨w, hw, hxw⟩, hxU⟩ := hx
          by_cases hwe : w = N0 + N
          · subst hwe
            exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hxw, hxU⟩)
          · exact Finset.mem_union_left _ (Finset.mem_inter.2
              ⟨Finset.mem_biUnion.2 ⟨w, Finset.mem_erase.2 ⟨hwe, hw⟩, hxw⟩, hxU⟩)
        have hc1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hc2 := ih (by omega) _ hW'
        have hF2 := hF
        split_ifs at hF2 <;> omega
    · have hW' : ∀ w ∈ W, w < N0 + N ∧ V w ⊆ Z := by
        intro w hw
        have hne : w ≠ N0 + N := fun h => hmem (h ▸ hw)
        exact ⟨by have := (hW w hw).1; omega, (hW w hw).2⟩
      have := ih (by omega) W hW'
      split_ifs at hF <;> omega




open Finset


variable {n m k : ℕ} (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))

def Qp (p : Fin n) : Finset (Fin k) :=
  univ.filter (fun i => p ∈ A i ∧ 2 ≤ (B i).card ∧ ∀ l ∈ B i, inc p l = true)

def Ql (l : Fin m) : Finset (Fin k) :=
  univ.filter (fun i => l ∈ B i ∧ 2 ≤ (A i).card ∧ ∀ p ∈ A i, inc p l = true)

def Ol (l : Fin m) : Finset (Fin k) :=
  univ.filter (fun i => B i = {l} ∧ 2 ≤ (A i).card ∧ ¬ ∀ p ∈ A i, inc p l = true)

def Sg : Finset (Fin k) := univ.filter (fun i => (A i).card = 1 ∧ (B i).card = 1)

def SP (p : Fin n) : Finset (Fin m) := univ.filter (fun l => ∃ i ∈ Qp inc A B p, l ∈ B i)

def TL (l : Fin m) : Finset (Fin n) := univ.filter (fun p => ∃ i ∈ Ql inc A B l, p ∈ A i)

def Xs : Finset (Fin n) := univ.filter (fun x => ∃ j, A j = {x} ∧ ¬ ∀ l ∈ B j, inc x l = true)

def R1 (l : Fin m) : Finset (Fin n) :=
  univ.filter (fun p => inc p l = true ∧ p ∈ Xs inc A B ∧ p ∉ TL inc A B l ∧ ∃ i ∈ Ol inc A B l, p ∈ A i)

def Dset : Finset (Fin k) := univ.filter (fun t =>
  (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
  (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))

theorem cover (Acc : Finset (Fin n × Fin m))
    (S1 : ∀ (p : Fin n) (i j : Fin k), i ≠ j → p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true))
    (S2 : ∀ (l : Fin m) (i j : Fin k), i ≠ j → l ∈ B i → l ∈ B j →
      (∀ p ∈ A i, inc p l = true) ∨ (∀ p ∈ A j, inc p l = true))
    (hAcc : ∀ q ∈ Acc, inc q.1 q.2 = true ∧
      ∃ i j : Fin k, i ≠ j ∧ q.1 ∈ A i ∧ q.2 ∈ B i ∧ q.1 ∈ A j ∧ q.2 ∈ B j) :
    Acc.card ≤ (∑ p, (SP inc A B p).card) + (∑ l, (TL inc A B l).card) +
      (∑ l, (R1 inc A B l).card) + (Sg A B).card := by
  have hsub : Acc ⊆ (((univ.biUnion fun p => ({p} : Finset (Fin n)) ×ˢ SP inc A B p) ∪
      (univ.biUnion fun l => TL inc A B l ×ˢ ({l} : Finset (Fin m)))) ∪
      (univ.biUnion fun l => R1 inc A B l ×ˢ ({l} : Finset (Fin m)))) ∪
      ((Sg A B).biUnion fun i => A i ×ˢ B i) := by
    rintro ⟨p, l⟩ hq
    obtain ⟨hinc, i1, j1, hne, h1, h2, h3, h4⟩ := hAcc _ hq
    simp only at hinc h1 h2 h3 h4
    by_cases hP : l ∈ SP inc A B p
    · simp [hP]
    by_cases hT : p ∈ TL inc A B l
    · simp [hT]
    by_cases hS : ∃ i ∈ Sg A B, p ∈ A i ∧ l ∈ B i
    · obtain ⟨i, hi, hpi, hli⟩ := hS
      refine mem_union_right _ (mem_biUnion.2 ⟨i, hi, mem_product.2 ⟨hpi, hli⟩⟩)
    refine mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨l, mem_univ _, ?_⟩))
    refine mem_product.2 ⟨?_, mem_singleton_self _⟩
    have kP : ∀ i, p ∈ A i → l ∈ B i → (∀ l' ∈ B i, inc p l' = true) → (B i).card ≤ 1 := by
      intro i hpi hli hpen
      by_contra hc
      exact hP (mem_filter.2 ⟨mem_univ _, i, mem_filter.2 ⟨mem_univ _, hpi, by omega, hpen⟩, hli⟩)
    have kL : ∀ i, p ∈ A i → l ∈ B i → (∀ p' ∈ A i, inc p' l = true) → (A i).card ≤ 1 := by
      intro i hpi hli hpen
      by_contra hc
      exact hT (mem_filter.2 ⟨mem_univ _, i, mem_filter.2 ⟨mem_univ _, hli, by omega, hpen⟩, hpi⟩)
    have kS : ∀ i, p ∈ A i → l ∈ B i → ¬ ((A i).card = 1 ∧ (B i).card = 1) := by
      intro i hpi hli hc
      exact hS ⟨i, mem_filter.2 ⟨mem_univ _, hc⟩, hpi, hli⟩
    obtain ⟨i, hiA, hiB, hipen⟩ : ∃ i, p ∈ A i ∧ l ∈ B i ∧ ∀ l' ∈ B i, inc p l' = true := by
      rcases S1 p i1 j1 hne h1 h3 with h | h
      · exact ⟨i1, h1, h2, h⟩
      · exact ⟨j1, h3, h4, h⟩
    obtain ⟨j, hjA, hjB, hjran⟩ : ∃ j, p ∈ A j ∧ l ∈ B j ∧ ∀ p' ∈ A j, inc p' l = true := by
      rcases S2 l i1 j1 hne h2 h4 with h | h
      · exact ⟨i1, h1, h2, h⟩
      · exact ⟨j1, h3, h4, h⟩
    have hBi1 : (B i).card = 1 := le_antisymm (kP i hiA hiB hipen) (card_pos.2 ⟨l, hiB⟩)
    have hAi : 2 ≤ (A i).card := by
      have := card_pos.2 ⟨p, hiA⟩
      by_contra h
      exact kS i hiA hiB ⟨by omega, hBi1⟩
    have hAj1 : (A j).card = 1 := le_antisymm (kL j hjA hjB hjran) (card_pos.2 ⟨p, hjA⟩)
    have hBj : 2 ≤ (B j).card := by
      have := card_pos.2 ⟨l, hjB⟩
      by_contra h
      exact kS j hjA hjB ⟨hAj1, by omega⟩
    have hBi : B i = {l} := by
      obtain ⟨a, ha⟩ := card_eq_one.1 hBi1
      rw [ha] at hiB ⊢
      rw [mem_singleton.1 hiB]
    have hAj : A j = {p} := by
      obtain ⟨a, ha⟩ := card_eq_one.1 hAj1
      rw [ha] at hjA ⊢
      rw [mem_singleton.1 hjA]
    refine mem_filter.2 ⟨mem_univ _, hinc, ?_, hT, i, ?_, hiA⟩
    · refine mem_filter.2 ⟨mem_univ _, j, hAj, fun h => ?_⟩
      have := kP j hjA hjB h
      omega
    · refine mem_filter.2 ⟨mem_univ _, hBi, hAi, fun h => ?_⟩
      have := kL i hiA hiB h
      omega
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  refine add_le_add ((card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans
    (add_le_add ?_ ?_)) ?_)) ?_
  · refine card_biUnion_le.trans (le_of_eq (sum_congr rfl fun p _ => ?_))
    simp
  · refine card_biUnion_le.trans (le_of_eq (sum_congr rfl fun p _ => ?_))
    simp
  · refine card_biUnion_le.trans (le_of_eq (sum_congr rfl fun p _ => ?_))
    simp
  · refine card_biUnion_le.trans (le_of_eq ?_)
    rw [card_eq_sum_ones]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨_, h1, h2⟩ := mem_filter.1 hi
    rw [card_product, h1, h2]





open Finset

theorem ufapp (N0 s : ℕ) (V : ℕ → Finset ℕ) (hin : ∀ w < N0, V w = {w})
    (hor : ∀ j < s, ∃ u v, u < N0 + j ∧ v < N0 + j ∧ V (N0 + j) = V u ∪ V v)
    {ι : Type*} [DecidableEq ι] (Q : Finset ι) (c : ι → ℕ) (Z U : Finset ℕ)
    (hc : ∀ i ∈ Q, c i < N0 + s ∧ V (c i) ⊆ Z) (hU : ∀ e ∈ U, ∃ i ∈ Q, e ∈ V (c i)) :
    U.card ≤ Q.card + ((range s).filter (fun j => V (N0 + j) ⊆ Z ∧ 2 ≤ (V (N0 + j) ∩ U).card)).card := by
  have h := uf N0 s V hin hor Z U s le_rfl (Q.image c) (by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hw
    exact hc i hi)
  have hsub : U ⊆ ((Q.image c).biUnion V) ∩ U := by
    intro e he
    obtain ⟨i, hi, hei⟩ := hU e he
    exact mem_inter.2 ⟨mem_biUnion.2 ⟨c i, mem_image_of_mem _ hi, hei⟩, he⟩
  have := card_image_le (s := Q) (f := c)
  have := card_le_card hsub
  omega



def ZP (p : Fin n) : Finset ℕ := (SP inc A B p).image (fun l => n + l.val)
def ZL (l : Fin m) : Finset ℕ := (TL inc A B l).image (fun p => p.val)
def Z1 (l : Fin m) : Finset ℕ := ((Ol inc A B l).biUnion A).image (fun p => p.val)
def U1 (l : Fin m) : Finset ℕ := (R1 inc A B l).image (fun p => p.val)

def GS (s : ℕ) (V : ℕ → Finset ℕ) (Z U : Finset ℕ) : Finset ℕ :=
  (range s).filter (fun j => V (n + m + j) ⊆ Z ∧ 2 ≤ (V (n + m + j) ∩ U).card)

theorem SP_inc (p : Fin n) (l : Fin m) (h : l ∈ SP inc A B p) : inc p l = true := by
  obtain ⟨_, i, hi, hl⟩ := mem_filter.1 h
  exact (mem_filter.1 hi).2.2.2 l hl

theorem TL_inc (p : Fin n) (l : Fin m) (h : p ∈ TL inc A B l) : inc p l = true := by
  obtain ⟨_, i, hi, hp⟩ := mem_filter.1 h
  exact (mem_filter.1 hi).2.2.2 p hp

theorem gs_two {s : ℕ} {V : ℕ → Finset ℕ} {Z U : Finset ℕ} {j : ℕ}
    (h : j ∈ GS (n := n) (m := m) s V Z U) :
    ∃ e1 e2, e1 ≠ e2 ∧ e1 ∈ V (n + m + j) ∧ e1 ∈ U ∧ e1 ∈ Z ∧ e2 ∈ V (n + m + j) ∧ e2 ∈ U ∧ e2 ∈ Z := by
  obtain ⟨_, hZ, h2⟩ := mem_filter.1 h
  obtain ⟨e1, e2, h1, h2', hne⟩ := one_lt_card_iff.1 (by omega : 1 < (V (n + m + j) ∩ U).card)
  rw [mem_inter] at h1 h2'
  exact ⟨e1, e2, hne, h1.1, h1.2, hZ h1.1, h2'.1, h2'.2, hZ h2'.1⟩

theorem gs_sub {s : ℕ} {V : ℕ → Finset ℕ} {Z U : Finset ℕ} {j : ℕ}
    (h : j ∈ GS (n := n) (m := m) s V Z U) : V (n + m + j) ⊆ Z := (mem_filter.1 h).2.1

theorem xlemma
    (S1 : ∀ (p : Fin n) (i j : Fin k), i ≠ j → p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true))
    (x : Fin n) (l : Fin m) (hx : x ∈ Xs inc A B) (i : Fin k) (hi : i ∈ Ol inc A B l)
    (hxi : x ∈ A i) : inc x l = true := by
  obtain ⟨_, j, hAj, hnp⟩ := mem_filter.1 hx
  obtain ⟨_, hBi, hAi, _⟩ := mem_filter.1 hi
  have hne : i ≠ j := by
    rintro rfl
    rw [hAj] at hAi
    simp at hAi
  rcases S1 x i j hne hxi (by rw [hAj]; exact mem_singleton_self _) with h | h
  · exact h l (by rw [hBi]; exact mem_singleton_self _)
  · exact absurd h hnp

theorem gates_le (s : ℕ) (V : ℕ → Finset ℕ)
    (hlin : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    (S1 : ∀ (p : Fin n) (i j : Fin k), i ≠ j → p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true)) :
    (∑ p, (GS (n := n) (m := m) s V (ZP inc A B p) (ZP inc A B p)).card) +
      (∑ l, (GS (n := n) (m := m) s V (ZL inc A B l) (ZL inc A B l)).card) +
      (∑ l, (GS (n := n) (m := m) s V (Z1 inc A B l) (U1 inc A B l)).card) ≤ s := by
  set GPx := fun p => GS (n := n) (m := m) s V (ZP inc A B p) (ZP inc A B p) with hGP
  set GLx := fun l => GS (n := n) (m := m) s V (ZL inc A B l) (ZL inc A B l) with hGL
  set G1x := fun l => GS (n := n) (m := m) s V (Z1 inc A B l) (U1 inc A B l) with hG1
  -- membership decoders
  have dP : ∀ e p, e ∈ ZP inc A B p → ∃ l, e = n + l.val ∧ inc p l = true := by
    intro e p he
    obtain ⟨l, hl, rfl⟩ := mem_image.1 he
    exact ⟨l, rfl, SP_inc inc A B p l hl⟩
  have dL : ∀ e l, e ∈ ZL inc A B l → ∃ p : Fin n, e = p.val ∧ p ∈ TL inc A B l := by
    intro e l he
    obtain ⟨p, hp, rfl⟩ := mem_image.1 he
    exact ⟨p, rfl, hp⟩
  have d1 : ∀ e l, e ∈ U1 inc A B l → ∃ p : Fin n, e = p.val ∧ p ∈ R1 inc A B l := by
    intro e l he
    obtain ⟨p, hp, rfl⟩ := mem_image.1 he
    exact ⟨p, rfl, hp⟩
  have dZ1 : ∀ e l, e ∈ Z1 inc A B l → ∃ p : Fin n, e = p.val ∧ ∃ i ∈ Ol inc A B l, p ∈ A i := by
    intro e l he
    obtain ⟨p, hp, rfl⟩ := mem_image.1 he
    obtain ⟨i, hi, hpi⟩ := mem_biUnion.1 hp
    exact ⟨p, rfl, i, hi, hpi⟩
  have hPd : (↑(univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint GPx := by
    intro p _ p' _ hpp
    refine disjoint_left.2 fun j hj hj' => ?_
    obtain ⟨e1, e2, hne, h1V, h1U, _, h2V, h2U, _⟩ := gs_two hj
    have hZ' := gs_sub hj'
    obtain ⟨l1, rfl, hi1⟩ := dP _ _ h1U
    obtain ⟨l2, rfl, hi2⟩ := dP _ _ h2U
    obtain ⟨l1', he1, hi1'⟩ := dP _ _ (hZ' h1V)
    obtain ⟨l2', he2, hi2'⟩ := dP _ _ (hZ' h2V)
    have e1 : l1 = l1' := Fin.ext (by omega)
    have e2 : l2 = l2' := Fin.ext (by omega)
    subst e1 e2
    exact hlin p p' l1 l2 hpp (fun h => hne (by rw [h])) hi1 hi1' hi2 hi2'
  have hLd : (↑(univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint GLx := by
    intro l _ l' _ hll
    refine disjoint_left.2 fun j hj hj' => ?_
    obtain ⟨e1, e2, hne, h1V, h1U, _, h2V, h2U, _⟩ := gs_two hj
    have hZ' := gs_sub hj'
    obtain ⟨p1, rfl, hp1⟩ := dL _ _ h1U
    obtain ⟨p2, rfl, hp2⟩ := dL _ _ h2U
    obtain ⟨p1', he1, hp1'⟩ := dL _ _ (hZ' h1V)
    obtain ⟨p2', he2, hp2'⟩ := dL _ _ (hZ' h2V)
    have e1 : p1 = p1' := Fin.ext he1
    have e2 : p2 = p2' := Fin.ext he2
    subst e1 e2
    exact hlin p1 p2 l l' (fun h => hne (by rw [h])) hll (TL_inc inc A B _ _ hp1)
      (TL_inc inc A B _ _ hp2) (TL_inc inc A B _ _ hp1') (TL_inc inc A B _ _ hp2')
  have h1d : (↑(univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G1x := by
    intro l _ l' _ hll
    refine disjoint_left.2 fun j hj hj' => ?_
    obtain ⟨e1, e2, hne, h1V, h1U, _, h2V, h2U, _⟩ := gs_two hj
    have hZ' := gs_sub hj'
    obtain ⟨p1, rfl, hp1⟩ := d1 _ _ h1U
    obtain ⟨p2, rfl, hp2⟩ := d1 _ _ h2U
    obtain ⟨p1', he1, i1, hi1, hpi1⟩ := dZ1 _ _ (hZ' h1V)
    obtain ⟨p2', he2, i2, hi2, hpi2⟩ := dZ1 _ _ (hZ' h2V)
    have e1 : p1 = p1' := Fin.ext he1
    have e2 : p2 = p2' := Fin.ext he2
    subst e1 e2
    obtain ⟨_, hinc1, hX1, _⟩ := mem_filter.1 hp1
    obtain ⟨_, hinc2, hX2, _⟩ := mem_filter.1 hp2
    exact hlin p1 p2 l l' (fun h => hne (by rw [h])) hll hinc1 hinc2
      (xlemma inc A B S1 p1 l' hX1 i1 hi1 hpi1) (xlemma inc A B S1 p2 l' hX2 i2 hi2 hpi2)
  have hPL : Disjoint (univ.biUnion GPx) (univ.biUnion GLx) := by
    refine disjoint_left.2 fun j hj hj' => ?_
    obtain ⟨p, _, hj⟩ := mem_biUnion.1 hj
    obtain ⟨l, _, hj'⟩ := mem_biUnion.1 hj'
    obtain ⟨e1, _, _, h1V, h1U, _, _⟩ := gs_two hj
    obtain ⟨l1, rfl, _⟩ := dP _ _ h1U
    obtain ⟨p1, he, _⟩ := dL _ _ (gs_sub hj' h1V)
    have := p1.isLt
    omega
  have hP1 : Disjoint (univ.biUnion GPx) (univ.biUnion G1x) := by
    refine disjoint_left.2 fun j hj hj' => ?_
    obtain ⟨p, _, hj⟩ := mem_biUnion.1 hj
    obtain ⟨l, _, hj'⟩ := mem_biUnion.1 hj'
    obtain ⟨e1, _, _, h1V, h1U, _, _⟩ := gs_two hj
    obtain ⟨l1, rfl, _⟩ := dP _ _ h1U
    obtain ⟨p1, he, _⟩ := dZ1 _ _ (gs_sub hj' h1V)
    have := p1.isLt
    omega
  have hL1 : Disjoint (univ.biUnion GLx) (univ.biUnion G1x) := by
    refine disjoint_left.2 fun j hj hj' => ?_
    obtain ⟨l, _, hj⟩ := mem_biUnion.1 hj
    obtain ⟨l', _, hj'⟩ := mem_biUnion.1 hj'
    obtain ⟨e1, e2, hne, h1V, h1U, _, h2V, h2U, _⟩ := gs_two hj'
    have hZ := gs_sub hj
    obtain ⟨p1, rfl, hp1⟩ := d1 _ _ h1U
    obtain ⟨p2, rfl, hp2⟩ := d1 _ _ h2U
    obtain ⟨p1', he1, hq1⟩ := dL _ _ (hZ h1V)
    obtain ⟨p2', he2, hq2⟩ := dL _ _ (hZ h2V)
    have e1 : p1 = p1' := Fin.ext he1
    have e2 : p2 = p2' := Fin.ext he2
    subst e1 e2
    obtain ⟨_, hinc1, _, hT1, _⟩ := mem_filter.1 hp1
    obtain ⟨_, hinc2, _, _, _⟩ := mem_filter.1 hp2
    by_cases hll : l = l'
    · subst hll
      exact hT1 hq1
    · exact hlin p1 p2 l l' (fun h => hne (by rw [h])) hll (TL_inc inc A B _ _ hq1)
        (TL_inc inc A B _ _ hq2) hinc1 hinc2
  rw [← card_biUnion hPd, ← card_biUnion hLd, ← card_biUnion h1d,
    ← card_union_of_disjoint hPL, ← card_union_of_disjoint (disjoint_union_left.2 ⟨hP1, hL1⟩)]
  refine (card_le_card ?_).trans (card_range s).le
  intro j hj
  simp only [mem_union, mem_biUnion] at hj
  rcases hj with (⟨_, _, hj⟩ | ⟨_, _, hj⟩) | ⟨_, _, hj⟩ <;> exact (mem_filter.1 hj).1





open Finset

theorem dsum {k : ℕ} {α : Type*} [Fintype α] (F : α → Finset (Fin k)) :
    ∑ a, (F a).card = ∑ i, (univ.filter (fun a => i ∈ F a)).card := by
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← card_filter, filter_mem_eq_inter, univ_inter]

theorem rects_le {n m k : ℕ} (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n))
    (B : Fin k → Finset (Fin m))
    (hlin : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False) :
    (∑ p, (Qp inc A B p).card) + (∑ l, (Ql inc A B l).card) + (∑ l, (Ol inc A B l).card) +
      (Sg A B).card ≤ k + (Dset inc A B).card := by
  have hSg : (Sg A B).card = ∑ i, if i ∈ Sg A B then 1 else 0 := by
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  have hDs : (Dset inc A B).card = ∑ i, if i ∈ Dset inc A B then 1 else 0 := by
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  rw [dsum (Qp inc A B), dsum (Ql inc A B), dsum (Ol inc A B), hSg, hDs]
  have hk : k + (∑ i, if i ∈ Dset inc A B then 1 else 0) =
      ∑ i : Fin k, (1 + if i ∈ Dset inc A B then 1 else 0) := by
    rw [sum_add_distrib]; simp
  rw [hk, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  set cP := (univ.filter (fun p => i ∈ Qp inc A B p)).card with hcP
  set cL := (univ.filter (fun l => i ∈ Ql inc A B l)).card with hcL
  set cO := (univ.filter (fun l => i ∈ Ol inc A B l)).card with hcO
  have bP : cP ≤ 1 := by
    refine card_le_one.2 fun p hp p' hp' => ?_
    by_contra hne
    obtain ⟨_, _, h2, hpen⟩ := mem_filter.1 (mem_filter.1 hp).2
    obtain ⟨_, _, _, hpen'⟩ := mem_filter.1 (mem_filter.1 hp').2
    obtain ⟨l1, l2, h1, h2', hl⟩ := one_lt_card_iff.1 (by omega : 1 < (B i).card)
    exact hlin p p' l1 l2 hne hl (hpen l1 h1) (hpen' l1 h1) (hpen l2 h2') (hpen' l2 h2')
  have bL : cL ≤ 1 := by
    refine card_le_one.2 fun l hl l' hl' => ?_
    by_contra hne
    obtain ⟨_, _, h2, hran⟩ := mem_filter.1 (mem_filter.1 hl).2
    obtain ⟨_, _, _, hran'⟩ := mem_filter.1 (mem_filter.1 hl').2
    obtain ⟨p1, p2, h1, h2', hp⟩ := one_lt_card_iff.1 (by omega : 1 < (A i).card)
    exact hlin p1 p2 l l' hp hne (hran p1 h1) (hran p2 h2') (hran' p1 h1) (hran' p2 h2')
  have bO : cO ≤ 1 := by
    refine card_le_one.2 fun l hl l' hl' => ?_
    obtain ⟨_, h1, _⟩ := mem_filter.1 (mem_filter.1 hl).2
    obtain ⟨_, h1', _⟩ := mem_filter.1 (mem_filter.1 hl').2
    rw [h1] at h1'
    exact singleton_inj.1 h1'
  have getP : 1 ≤ cP → ∃ p, p ∈ A i ∧ 2 ≤ (B i).card ∧ ∀ l ∈ B i, inc p l = true := by
    intro h
    obtain ⟨p, hp⟩ := card_pos.1 (by omega : 0 < cP)
    exact ⟨p, (mem_filter.1 (mem_filter.1 hp).2).2⟩
  have getL : 1 ≤ cL → ∃ l, l ∈ B i ∧ 2 ≤ (A i).card ∧ ∀ p ∈ A i, inc p l = true := by
    intro h
    obtain ⟨l, hl⟩ := card_pos.1 (by omega : 0 < cL)
    exact ⟨l, (mem_filter.1 (mem_filter.1 hl).2).2⟩
  have getO : 1 ≤ cO → ∃ l, B i = {l} ∧ 2 ≤ (A i).card ∧ ¬ ∀ p ∈ A i, inc p l = true := by
    intro h
    obtain ⟨l, hl⟩ := card_pos.1 (by omega : 0 < cO)
    exact ⟨l, (mem_filter.1 (mem_filter.1 hl).2).2⟩
  have hPO : 1 ≤ cP → 1 ≤ cO → False := by
    intro h1 h2
    obtain ⟨_, _, hB, _⟩ := getP h1
    obtain ⟨_, hB', _⟩ := getO h2
    rw [hB'] at hB
    simp at hB
  have hLO : 1 ≤ cL → 1 ≤ cO → False := by
    intro h1 h2
    obtain ⟨l, hl, _, hran⟩ := getL h1
    obtain ⟨l', hB', _, hnr⟩ := getO h2
    rw [hB', mem_singleton] at hl
    subst hl
    exact hnr hran
  have hPS : 1 ≤ cP → i ∈ Sg A B → False := by
    intro h1 h2
    obtain ⟨_, _, hB, _⟩ := getP h1
    have := (mem_filter.1 h2).2.2
    omega
  have hLS : 1 ≤ cL → i ∈ Sg A B → False := by
    intro h1 h2
    obtain ⟨_, _, hA, _⟩ := getL h1
    have := (mem_filter.1 h2).2.1
    omega
  have hOS : 1 ≤ cO → i ∈ Sg A B → False := by
    intro h1 h2
    obtain ⟨_, _, hA, _⟩ := getO h1
    have := (mem_filter.1 h2).2.1
    omega
  have hPLD : 1 ≤ cP → 1 ≤ cL → i ∈ Dset inc A B := by
    intro h1 h2
    obtain ⟨p, _, hB, hpen⟩ := getP h1
    obtain ⟨l, hl, hA, hran⟩ := getL h2
    exact mem_filter.2 ⟨mem_univ _, ⟨p, hB, hpen⟩, ⟨l, hl, hA, hran⟩⟩
  by_cases hS : i ∈ Sg A B <;> by_cases hD : i ∈ Dset inc A B <;> simp only [hS, hD, ite_true, ite_false]
  all_goals
    first
    | omega
    | (rcases Nat.lt_or_ge cP 1 with h1 | h1 <;> rcases Nat.lt_or_ge cL 1 with h2 | h2 <;>
        rcases Nat.lt_or_ge cO 1 with h3 | h3 <;> first
          | omega
          | exact absurd (hPO h1 h3) id
          | exact absurd (hLO h2 h3) id
          | exact absurd (hPS h1 hS) id
          | exact absurd (hLS h2 hS) id
          | exact absurd (hOS h3 hS) id
          | exact absurd (hPLD h1 h2) hD)




open Finset
open PEqualNP.CircuitLowerBounds

theorem bound (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
  (hlin : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False)
  (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C)
  (hsize : C.size = s + k + T)
  (hor : ∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2)
  (hrect : ∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true)))
  (heval : ∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true))
  (hsound : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) :
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + (Dset inc A B).card := by
  have hgl : C.gates.length = s + k + T := hsize
  have hin : ∀ w < n + m, V C (n + m) w = {w} := fun w hw => V_input C (n + m) w hw
  have hor' : ∀ j < s, ∃ u v, u < n + m + j ∧ v < n + m + j ∧
      V C (n + m) (n + m + j) = V C (n + m) u ∪ V C (n + m) v := by
    intro j hj
    obtain ⟨hop, hlen⟩ := hor j hj
    obtain ⟨u, v, huv⟩ := List.length_eq_two.1 hlen
    have hu := hrb j (by omega) u (by rw [huv]; simp)
    have hv := hrb j (by omega) v (by rw [huv]; simp)
    exact ⟨u, v, hu, hv, V_or C (n + m) hrb j (by omega) u v hop huv⟩
  have hVa : ∀ i, V C (n + m) (a i) = (A i).image (fun p => p.val) := by
    intro i
    refine V_rect C (n + m) (a i) _ (fun e he => ?_) (fun x hx => ?_)
    · obtain ⟨p, _, rfl⟩ := mem_image.1 he
      have := p.isLt
      omega
    · rw [((hrect i).2.2.2.2.2.2 x hx).1]
      simp only [decide_eq_true_eq, mem_image]
      constructor
      · rintro ⟨pa, hpa, h⟩
        exact ⟨_, ⟨pa, hpa, rfl⟩, h⟩
      · rintro ⟨_, ⟨pa, hpa, rfl⟩, h⟩
        exact ⟨pa, hpa, h⟩
  have hVb : ∀ i, V C (n + m) (b i) = (B i).image (fun l => n + l.val) := by
    intro i
    refine V_rect C (n + m) (b i) _ (fun e he => ?_) (fun x hx => ?_)
    · obtain ⟨l, _, rfl⟩ := mem_image.1 he
      have := l.isLt
      omega
    · rw [((hrect i).2.2.2.2.2.2 x hx).2]
      simp only [decide_eq_true_eq, mem_image]
      constructor
      · rintro ⟨lb, hlb, h⟩
        exact ⟨_, ⟨lb, hlb, rfl⟩, h⟩
      · rintro ⟨_, ⟨lb, hlb, rfl⟩, h⟩
        exact ⟨lb, hlb, h⟩
  have fire : ∀ (i : Fin k) (F : Fin n → Bool) (G : Fin m → Bool),
      (C.wires (List.ofFn F ++ List.ofFn G)).getD (n + m + s + i.val) false = true ↔
        (∃ p ∈ A i, F p = true) ∧ (∃ l ∈ B i, G l = true) := by
    intro i F G
    have hx : (List.ofFn F ++ List.ofFn G).length = n + m := by simp
    obtain ⟨_, _, _, _, hop, hinp, hw⟩ := hrect i
    have h := wire_rb C (n + m) _ hx hrb (s + i.val) (by have := i.isLt; omega)
    rw [show n + m + s + i.val = n + m + (s + i.val) by omega, h, hop, hinp]
    obtain ⟨hwa, hwb⟩ := hw _ hx
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true, Bool.and_eq_true, hwa, hwb, getD_L, getD_R, decide_eq_true_eq]
  have evalT : ∀ (F : Fin n → Bool) (G : Fin m → Bool),
      C.eval (List.ofFn F ++ List.ofFn G) = true ↔ ∃ i1 j1 : Fin k, i1 < j1 ∧
        ((∃ p ∈ A i1, F p = true) ∧ (∃ l ∈ B i1, G l = true)) ∧
        ((∃ p ∈ A j1, F p = true) ∧ (∃ l ∈ B j1, G l = true)) := by
    intro F G
    rw [heval _ (by simp), decide_eq_true_eq]
    simp only [fire]
  have S1 : ∀ (p : Fin n) (i j : Fin k), i ≠ j → p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true) := by
    intro p i j hij hpi hpj
    by_contra hc
    simp only [not_or, not_forall, Bool.not_eq_true] at hc
    obtain ⟨⟨l1, hl1, h1⟩, ⟨l2, hl2, h2⟩⟩ := hc
    have hs := hsound {p} {l1, l2} (Or.inl ⟨card_singleton p, card_le_two⟩) (by
      intro p' hp' l hl
      rw [mem_singleton] at hp'
      subst hp'
      rcases mem_insert.1 hl with rfl | hl
      · exact h1
      · rw [mem_singleton] at hl; subst hl; exact h2)
    have ht : C.eval (List.ofFn (fun u : Fin n => decide (u ∈ ({p} : Finset (Fin n)))) ++
        List.ofFn (fun v : Fin m => decide (v ∈ ({l1, l2} : Finset (Fin m))))) = true := by
      rw [evalT]
      have fi : (∃ p' ∈ A i, decide (p' ∈ ({p} : Finset (Fin n))) = true) ∧
          (∃ l ∈ B i, decide (l ∈ ({l1, l2} : Finset (Fin m))) = true) :=
        ⟨⟨p, hpi, by simp⟩, ⟨l1, hl1, by simp⟩⟩
      have fj : (∃ p' ∈ A j, decide (p' ∈ ({p} : Finset (Fin n))) = true) ∧
          (∃ l ∈ B j, decide (l ∈ ({l1, l2} : Finset (Fin m))) = true) :=
        ⟨⟨p, hpj, by simp⟩, ⟨l2, hl2, by simp⟩⟩
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨i, j, h, fi, fj⟩
      · exact ⟨j, i, h, fj, fi⟩
    rw [hs] at ht
    exact Bool.false_ne_true ht
  have S2 : ∀ (l : Fin m) (i j : Fin k), i ≠ j → l ∈ B i → l ∈ B j →
      (∀ p ∈ A i, inc p l = true) ∨ (∀ p ∈ A j, inc p l = true) := by
    intro l i j hij hli hlj
    by_contra hc
    simp only [not_or, not_forall, Bool.not_eq_true] at hc
    obtain ⟨⟨p1, hp1, h1⟩, ⟨p2, hp2, h2⟩⟩ := hc
    have hs := hsound {p1, p2} {l} (Or.inr ⟨card_le_two, card_singleton l⟩) (by
      intro p' hp' l' hl'
      rw [mem_singleton] at hl'
      subst hl'
      rcases mem_insert.1 hp' with rfl | hp'
      · exact h1
      · rw [mem_singleton] at hp'; subst hp'; exact h2)
    have ht : C.eval (List.ofFn (fun u : Fin n => decide (u ∈ ({p1, p2} : Finset (Fin n)))) ++
        List.ofFn (fun v : Fin m => decide (v ∈ ({l} : Finset (Fin m))))) = true := by
      rw [evalT]
      have fi : (∃ p' ∈ A i, decide (p' ∈ ({p1, p2} : Finset (Fin n))) = true) ∧
          (∃ l' ∈ B i, decide (l' ∈ ({l} : Finset (Fin m))) = true) :=
        ⟨⟨p1, hp1, by simp⟩, ⟨l, hli, by simp⟩⟩
      have fj : (∃ p' ∈ A j, decide (p' ∈ ({p1, p2} : Finset (Fin n))) = true) ∧
          (∃ l' ∈ B j, decide (l' ∈ ({l} : Finset (Fin m))) = true) :=
        ⟨⟨p2, hp2, by simp⟩, ⟨l, hlj, by simp⟩⟩
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨i, j, h, fi, fj⟩
      · exact ⟨j, i, h, fj, fi⟩
    rw [hs] at ht
    exact Bool.false_ne_true ht
  set Acc := ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++
        List.ofFn (fun v : Fin m => decide (v = q.2))) = true)) with hAccdef
  have hAcc : ∀ q ∈ Acc, inc q.1 q.2 = true ∧
      ∃ i j : Fin k, i ≠ j ∧ q.1 ∈ A i ∧ q.2 ∈ B i ∧ q.1 ∈ A j ∧ q.2 ∈ B j := by
    intro q hq
    obtain ⟨_, hinc, he⟩ := mem_filter.1 hq
    refine ⟨hinc, ?_⟩
    obtain ⟨i1, j1, hlt, ⟨⟨p, hp, hpe⟩, ⟨l, hl, hle⟩⟩, ⟨⟨p', hp', hpe'⟩, ⟨l', hl', hle'⟩⟩⟩ :=
      (evalT _ _).1 he
    simp only [decide_eq_true_eq] at hpe hle hpe' hle'
    subst hpe hle
    subst hpe' hle'
    exact ⟨i1, j1, ne_of_lt hlt, hp, hl, hp', hl'⟩
  have hc := cover inc A B Acc S1 S2 hAcc
  have hg := gates_le inc A B s (V C (n + m)) hlin S1
  have hr := rects_le inc A B hlin
  have hSP : ∀ p, (SP inc A B p).card ≤ (Qp inc A B p).card +
      (GS (n := n) (m := m) s (V C (n + m)) (ZP inc A B p) (ZP inc A B p)).card := by
    intro p
    have h := ufapp (n + m) s (V C (n + m)) hin hor' (Qp inc A B p) b (ZP inc A B p) (ZP inc A B p)
      (by
        intro i hi
        refine ⟨(hrect i).2.2.2.1, ?_⟩
        rw [hVb]
        intro e he
        obtain ⟨l, hl, rfl⟩ := mem_image.1 he
        exact mem_image.2 ⟨l, mem_filter.2 ⟨mem_univ _, i, hi, hl⟩, rfl⟩)
      (by
        intro e he
        obtain ⟨l, hl, rfl⟩ := mem_image.1 he
        obtain ⟨_, i, hi, hli⟩ := mem_filter.1 hl
        exact ⟨i, hi, by rw [hVb]; exact mem_image_of_mem _ hli⟩)
    have hinj : (ZP inc A B p).card = (SP inc A B p).card :=
      card_image_of_injective _ (fun x y h => Fin.ext (Nat.add_left_cancel h))
    rw [← hinj]
    exact h
  have hTL : ∀ l, (TL inc A B l).card ≤ (Ql inc A B l).card +
      (GS (n := n) (m := m) s (V C (n + m)) (ZL inc A B l) (ZL inc A B l)).card := by
    intro l
    have h := ufapp (n + m) s (V C (n + m)) hin hor' (Ql inc A B l) a (ZL inc A B l) (ZL inc A B l)
      (by
        intro i hi
        refine ⟨(hrect i).2.2.1, ?_⟩
        rw [hVa]
        intro e he
        obtain ⟨p, hp, rfl⟩ := mem_image.1 he
        exact mem_image.2 ⟨p, mem_filter.2 ⟨mem_univ _, i, hi, hp⟩, rfl⟩)
      (by
        intro e he
        obtain ⟨p, hp, rfl⟩ := mem_image.1 he
        obtain ⟨_, i, hi, hpi⟩ := mem_filter.1 hp
        exact ⟨i, hi, by rw [hVa]; exact mem_image_of_mem _ hpi⟩)
    have hinj : (ZL inc A B l).card = (TL inc A B l).card :=
      card_image_of_injective _ (fun x y h => Fin.ext h)
    rw [← hinj]
    exact h
  have hR1 : ∀ l, (R1 inc A B l).card ≤ (Ol inc A B l).card +
      (GS (n := n) (m := m) s (V C (n + m)) (Z1 inc A B l) (U1 inc A B l)).card := by
    intro l
    have h := ufapp (n + m) s (V C (n + m)) hin hor' (Ol inc A B l) a (Z1 inc A B l) (U1 inc A B l)
      (by
        intro i hi
        refine ⟨(hrect i).2.2.1, ?_⟩
        rw [hVa]
        intro e he
        obtain ⟨p, hp, rfl⟩ := mem_image.1 he
        exact mem_image.2 ⟨p, mem_biUnion.2 ⟨i, hi, hp⟩, rfl⟩)
      (by
        intro e he
        obtain ⟨p, hp, rfl⟩ := mem_image.1 he
        obtain ⟨_, _, _, _, i, hi, hpi⟩ := mem_filter.1 hp
        exact ⟨i, hi, by rw [hVa]; exact mem_image_of_mem _ hpi⟩)
    have hinj : (U1 inc A B l).card = (R1 inc A B l).card :=
      card_image_of_injective _ (fun x y h => Fin.ext h)
    rw [← hinj]
    exact h
  have s1 := sum_le_sum (fun p (_ : p ∈ (univ : Finset (Fin n))) => hSP p)
  have s2 := sum_le_sum (fun l (_ : l ∈ (univ : Finset (Fin m))) => hTL l)
  have s3 := sum_le_sum (fun l (_ : l ∈ (univ : Finset (Fin m))) => hR1 l)
  rw [sum_add_distrib] at s1 s2 s3
  omega

end PEqualNP.Outside.L_meta_3063

theorem PEqualNP.Outside.L_meta_3063 : ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
  (∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False) →
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  C.size = s + k + T → 1 ≤ k →
  (∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) →
  (∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true))) →
  (∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true)) →
  (∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) →
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ∧
  (k ≤ T + 1 →
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun r => inc r.1 r.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = r.1)) ++ List.ofFn (fun v : Fin m => decide (v = r.2))) = true)).card
    ≤ C.size + 1) := by
  intro n m inc C s k T a b A B hlin _ hrb hsize _ hor hrect heval hsound
  have h := PEqualNP.Outside.L_meta_3063.bound n m inc C s k T a b A B hlin hrb hsize hor hrect heval hsound
  have hd : (PEqualNP.Outside.L_meta_3063.Dset inc A B).card ≤ k := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun t =>
      (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
      (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))
    simpa [PEqualNP.Outside.L_meta_3063.Dset] using this
  refine ⟨h, fun hk => ?_⟩
  rw [hsize]
  omega
