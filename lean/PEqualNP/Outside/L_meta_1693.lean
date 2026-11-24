import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1693
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]


def WP (kN : ℕ → ℕ) (c : ℕ) (base : ℕ → Prop) (w : ℕ) : Prop :=
  base w ∨ ∃ j, w = 26 + j ∧ kN j = c

theorem orlin (ins : ℕ → List ℕ) (kN : ℕ → ℕ) (c0 : ℕ) (base : ℕ → Prop) (f : ℕ → Bool)
    (F : Fin 13 → ℕ → Bool) (c : Fin 13 → Bool)
    (hbase : ∀ w, base w → (f w = true ↔ ∃ p, c p = true ∧ F p w = true))
    (hf : ∀ j, kN j = c0 → (f (26 + j) = true ↔ ∃ w ∈ ins j, f w = true))
    (hF : ∀ j, kN j = c0 → ∀ p, (F p (26 + j) = true ↔ ∃ w ∈ ins j, F p w = true))
    (hin : ∀ j, kN j = c0 → ∀ w ∈ ins j, WP kN c0 base w ∧ w < 26 + j) :
    ∀ w, WP kN c0 base w → (f w = true ↔ ∃ p, c p = true ∧ F p w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro (hb | ⟨j, rfl, hj⟩)
    · exact hbase w hb
    · rw [hf j hj]
      constructor
      · rintro ⟨u, hu, h⟩
        obtain ⟨hxu, hlt⟩ := hin j hj u hu
        obtain ⟨p, hp, hF'⟩ := (ih u hlt hxu).1 h
        exact ⟨p, hp, (hF j hj p).2 ⟨u, hu, hF'⟩⟩
      · rintro ⟨p, hp, h⟩
        obtain ⟨u, hu, h'⟩ := (hF j hj p).1 h
        exact ⟨u, hu, (ih u (hin j hj u hu).2 (hin j hj u hu).1).2 ⟨p, hp, h'⟩⟩

def cnt (kN : ℕ → ℕ) (c0 : ℕ) (SX : ℕ → Finset (Fin 13)) (L : Finset (Fin 13)) (m : ℕ) : ℕ :=
  ((Finset.range m).filter
    (fun j => kN j = c0 ∧ SX (26 + j) ⊆ L ∧ 2 ≤ (SX (26 + j)).card)).card

theorem cnt_mono (kN : ℕ → ℕ) (c0 : ℕ) (SX : ℕ → Finset (Fin 13)) (L : Finset (Fin 13)) (m : ℕ) :
    cnt kN c0 SX L m ≤ cnt kN c0 SX L (m + 1) := by
  unfold cnt
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (Nat.le_succ m)

theorem cnt_succ (kN : ℕ → ℕ) (c0 : ℕ) (SX : ℕ → Finset (Fin 13)) (L : Finset (Fin 13)) (m : ℕ)
    (h : kN m = c0 ∧ SX (26 + m) ⊆ L ∧ 2 ≤ (SX (26 + m)).card) :
    cnt kN c0 SX L (m + 1) = cnt kN c0 SX L m + 1 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
  simp

theorem botW (ins : ℕ → List ℕ) (kN : ℕ → ℕ) (c0 : ℕ) (base : ℕ → Prop)
    (SX : ℕ → Finset (Fin 13)) (L : Finset (Fin 13))
    (hfan : ∀ j, (ins j).length ≤ 2)
    (hb : ∀ w, base w → w < 26 ∧ (SX w).card ≤ 1)
    (hg : ∀ j, kN j = c0 → SX (26 + j) = (ins j).toFinset.biUnion SX)
    (hin : ∀ j, kN j = c0 → ∀ w ∈ ins j, WP kN c0 base w ∧ w < 26 + j) :
    ∀ (m : ℕ) (W : Finset ℕ), (∀ w ∈ W, WP kN c0 base w ∧ w < 26 + m ∧ SX w ⊆ L) →
      (W.biUnion SX).card ≤ W.card + cnt kN c0 SX L m := by
  intro m
  induction m with
  | zero =>
    intro W hW
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ => 1) ?_) (by simp)
    intro w hw
    obtain ⟨hwp, hlt, _⟩ := hW w hw
    rcases hwp with hb' | ⟨j, rfl, _⟩
    · exact (hb w hb').2
    · omega
  | succ m ih =>
    intro W hW
    have hmono := cnt_mono kN c0 SX L m
    by_cases hm : 26 + m ∈ W
    · obtain ⟨hwp, _, hsub⟩ := hW _ hm
      have hk : kN m = c0 := by
        rcases hwp with hb' | ⟨j, hj, hk⟩
        · have := (hb _ hb').1
          omega
        · have : j = m := by omega
          subst this
          exact hk
      have hA := hg m hk
      have key : ∀ I : Finset ℕ, I ⊆ (ins m).toFinset → SX (26 + m) ⊆ I.biUnion SX →
          (W.biUnion SX).card ≤ (W.erase (26 + m)).card + I.card + cnt kN c0 SX L m := by
        intro I hI hcov
        have h1 := ih (W.erase (26 + m) ∪ I) (by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
            obtain ⟨a1, a2, a3⟩ := hW w hw
            exact ⟨a1, by omega, a3⟩
          · have hw' := List.mem_toFinset.mp (hI hw)
            obtain ⟨a1, a2⟩ := hin m hk w hw'
            refine ⟨a1, a2, ?_⟩
            refine subset_trans ?_ hsub
            rw [hA]
            exact Finset.subset_biUnion_of_mem SX (hI hw))
        have h2 : W.biUnion SX ⊆ (W.erase (26 + m) ∪ I).biUnion SX := by
          intro p hp
          rw [Finset.mem_biUnion] at hp ⊢
          obtain ⟨w, hw, hp⟩ := hp
          by_cases hwm : w = 26 + m
          · subst hwm
            have := hcov hp
            rw [Finset.mem_biUnion] at this
            obtain ⟨u, hu, hp'⟩ := this
            exact ⟨u, Finset.mem_union_right _ hu, hp'⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), hp⟩
        have h3 := Finset.card_le_card h2
        have h4 := Finset.card_union_le (W.erase (26 + m)) I
        omega
      have he := Finset.card_erase_of_mem hm
      have hpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hm⟩
      by_cases h2 : 2 ≤ (SX (26 + m)).card
      · have hc := cnt_succ kN c0 SX L m ⟨hk, hsub, h2⟩
        have := key (ins m).toFinset (Finset.Subset.refl _) (le_of_eq hA)
        have h4 := List.toFinset_card_le (ins m)
        have h5 := hfan m
        omega
      · rcases Finset.eq_empty_or_nonempty (SX (26 + m)) with he0 | ⟨p, hp⟩
        · have := key ∅ (Finset.empty_subset _) (by rw [he0]; exact Finset.empty_subset _)
          simp only [Finset.card_empty] at this
          omega
        · have hp' := hp
          rw [hA, Finset.mem_biUnion] at hp'
          obtain ⟨u, hu, hpu⟩ := hp'
          have := key {u} (Finset.singleton_subset_iff.mpr hu) (by
            intro q hq
            have hle : (SX (26 + m)).card ≤ 1 := by omega
            have hqp : q = p := Finset.card_le_one.mp hle q hq p hp
            subst hqp
            simpa using hpu)
          simp only [Finset.card_singleton] at this
          omega
    · have := ih W (by
        intro w hw
        obtain ⟨a1, a2, a3⟩ := hW w hw
        refine ⟨a1, ?_, a3⟩
        have : w ≠ 26 + m := fun e => hm (e ▸ hw)
        omega)
      omega

theorem topW (ins : ℕ → List ℕ) (kN : ℕ → ℕ)
    (v : (Fin 13 → Bool) → (Fin 13 → Bool) → ℕ → Bool)
    (hfan : ∀ j, (ins j).length ≤ 2)
    (h3 : ∀ j, kN j = 3 → ∀ w ∈ ins j,
      (∃ j', w = 26 + j' ∧ (kN j' = 2 ∨ kN j' = 3)) ∧ w < 26 + j)
    (hor : ∀ j, kN j = 3 → ∀ x y, (v x y (26 + j) = true ↔ ∃ w ∈ ins j, v x y w = true)) :
    ∀ (m : ℕ) (W : Finset ℕ), (∀ w ∈ W, ∃ j, w = 26 + j ∧ j < m ∧ (kN j = 2 ∨ kN j = 3)) →
      ∃ S : Finset ℕ, (∀ s ∈ S, kN s = 2) ∧
        (∀ x y, (∃ w ∈ W, v x y w = true) ↔ ∃ s ∈ S, v x y (26 + s) = true) ∧
        S.card ≤ W.card + ((Finset.range m).filter (fun j => kN j = 3)).card := by
  intro m
  induction m with
  | zero =>
    intro W hW
    refine ⟨∅, by simp, ?_, by simp⟩
    intro x y
    constructor
    · rintro ⟨w, hw, _⟩
      obtain ⟨j, _, hj, _⟩ := hW w hw
      omega
    · rintro ⟨s, hs, _⟩
      simp at hs
  | succ m ih =>
    intro W hW
    have hmono : ((Finset.range m).filter (fun j => kN j = 3)).card ≤
        ((Finset.range (m + 1)).filter (fun j => kN j = 3)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_succ m)))
    by_cases hm : 26 + m ∈ W
    · have he := Finset.card_erase_of_mem hm
      have hpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hm⟩
      have hkm : kN m = 2 ∨ kN m = 3 := by
        obtain ⟨j, hj, _, hk⟩ := hW _ hm
        have : j = m := by omega
        subst this
        exact hk
      have herase : ∀ w ∈ W.erase (26 + m),
          ∃ j, w = 26 + j ∧ j < m ∧ (kN j = 2 ∨ kN j = 3) := by
        intro w hw
        obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
        obtain ⟨j, hj, hjm, hk⟩ := hW w hw
        exact ⟨j, hj, by omega, hk⟩
      rcases hkm with hk2 | hk3
      · obtain ⟨S, hS1, hS2, hS3⟩ := ih (W.erase (26 + m)) herase
        refine ⟨insert m S, ?_, ?_, ?_⟩
        · intro s hs
          rcases Finset.mem_insert.mp hs with hsm | hs
          · rw [hsm]; exact hk2
          · exact hS1 s hs
        · intro x y
          constructor
          · rintro ⟨w, hw, hv⟩
            by_cases hwm : w = 26 + m
            · rw [hwm] at hv
              exact ⟨m, Finset.mem_insert_self _ _, hv⟩
            · obtain ⟨s, hs, hv'⟩ := (hS2 x y).1 ⟨w, Finset.mem_erase.mpr ⟨hwm, hw⟩, hv⟩
              exact ⟨s, Finset.mem_insert_of_mem hs, hv'⟩
          · rintro ⟨s, hs, hv⟩
            rcases Finset.mem_insert.mp hs with hsm | hs
            · rw [hsm] at hv
              exact ⟨_, hm, hv⟩
            · obtain ⟨w, hw, hv'⟩ := (hS2 x y).2 ⟨s, hs, hv⟩
              exact ⟨w, Finset.mem_of_mem_erase hw, hv'⟩
        · have := Finset.card_insert_le m S
          omega
      · have hc : ((Finset.range (m + 1)).filter (fun j => kN j = 3)).card =
            ((Finset.range m).filter (fun j => kN j = 3)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert, if_pos hk3,
            Finset.card_insert_of_notMem (by simp)]
        obtain ⟨S, hS1, hS2, hS3⟩ := ih (W.erase (26 + m) ∪ (ins m).toFinset) (by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact herase w hw
          · obtain ⟨⟨j, hj, hk⟩, hlt⟩ := h3 m hk3 w (List.mem_toFinset.mp hw)
            exact ⟨j, hj, by omega, hk⟩)
        refine ⟨S, hS1, ?_, ?_⟩
        · intro x y
          rw [← hS2 x y]
          constructor
          · rintro ⟨w, hw, hv⟩
            by_cases hwm : w = 26 + m
            · rw [hwm] at hv
              obtain ⟨u, hu, hv'⟩ := (hor m hk3 x y).1 hv
              exact ⟨u, Finset.mem_union_right _ (List.mem_toFinset.mpr hu), hv'⟩
            · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), hv⟩
          · rintro ⟨w, hw, hv⟩
            rcases Finset.mem_union.mp hw with hw | hw
            · exact ⟨w, Finset.mem_of_mem_erase hw, hv⟩
            · exact ⟨_, hm, (hor m hk3 x y).2 ⟨w, List.mem_toFinset.mp hw, hv⟩⟩
        · have h4 := Finset.card_union_le (W.erase (26 + m)) (ins m).toFinset
          have h5 := List.toFinset_card_le (ins m)
          have h6 := hfan m
          omega
    · obtain ⟨S, hS1, hS2, hS3⟩ := ih W (by
        intro w hw
        obtain ⟨j, hj, hjm, hk⟩ := hW w hw
        have : w ≠ 26 + m := fun e => hm (e ▸ hw)
        exact ⟨j, hj, by omega, hk⟩)
      exact ⟨S, hS1, hS2, by omega⟩

def pts (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def lns (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

theorem mem_pts (p l : Fin 13) : p ∈ pts l ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  unfold pts
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_lns (l p : Fin 13) : l ∈ lns p ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  unfold lns
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem g_pts : ∀ l : Fin 13, (pts l).card = 4 := by decide +kernel

theorem g_lns : ∀ p : Fin 13, (lns p).card = 4 := by decide +kernel

theorem g_ll : ∀ l l' : Fin 13, l ≠ l' → (pts l ∩ pts l').card ≤ 1 := by decide +kernel

theorem g_pp : ∀ p p' : Fin 13, p ≠ p' → (lns p ∩ lns p').card ≤ 1 := by decide +kernel

def Q0 (d : Fin 13) : Finset (Fin 13) :=
  ([∅, ∅, {2, 4, 5, 6}, ∅, {2, 4, 5, 6}, {2, 4, 5, 6}, {2, 4, 5, 6}, {2, 4, 7, 8}, {2, 4, 5, 8},
    ∅, {2, 5, 6, 10}, {2, 4, 6, 11}, {2, 4, 5, 12}] : List (Finset (Fin 13))).getD d.val ∅

def Qf (p l : Fin 13) : Finset (Fin 13) := (Q0 (p - l)).image (fun r => r + l)

theorem g_quad : ∀ p l : Fin 13, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    (Qf p l).card = 4 ∧
    (∀ k : Fin 13, ((Qf p l).filter
      (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ Qf p l ∧ ∀ r ∈ Qf p l, r - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  decide +kernel

theorem sum_card_le {α : Type} [DecidableEq α] (T : Finset α) (f : Fin 13 → Finset α)
    (hsub : ∀ l, f l ⊆ T) (hd : ∀ l l', l ≠ l' → Disjoint (f l) (f l')) :
    ∑ l, (f l).card ≤ T.card := by
  rw [← Finset.card_biUnion (fun l _ l' _ h => hd l l' h)]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun l _ => hsub l))

theorem cnt_sum (kN : ℕ → ℕ) (c0 : ℕ) (SX : ℕ → Finset (Fin 13)) (n : ℕ)
    (Lf : Fin 13 → Finset (Fin 13)) (hL : ∀ l l', l ≠ l' → (Lf l ∩ Lf l').card ≤ 1) :
    ∑ l, cnt kN c0 SX (Lf l) n ≤ ((Finset.range n).filter (fun j => kN j = c0)).card := by
  unfold cnt
  apply sum_card_le
  · intro l j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.1⟩
  · intro l l' hne
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_filter] at hj hj'
    have h1 := Finset.card_le_card (Finset.subset_inter hj.2.2.1 hj'.2.2.1)
    have h2 := hL l l' hne
    omega

theorem side (ins : ℕ → List ℕ) (kN : ℕ → ℕ) (c0 : ℕ) (base : ℕ → Prop)
    (SX : ℕ → Finset (Fin 13)) (n : ℕ)
    (hfan : ∀ j, (ins j).length ≤ 2)
    (hb : ∀ w, base w → w < 26 ∧ (SX w).card ≤ 1)
    (hg : ∀ j, kN j = c0 → SX (26 + j) = (ins j).toFinset.biUnion SX)
    (hin : ∀ j, kN j = c0 → ∀ w ∈ ins j, WP kN c0 base w ∧ w < 26 + j)
    (hk : ∀ j, kN j = c0 → j < n)
    (S : Finset ℕ) (a : ℕ → ℕ) (ha : ∀ s ∈ S, WP kN c0 base (a s))
    (L : Finset (Fin 13)) (hL : L.card = 4)
    (T : Finset ℕ) (hT : T ⊆ S) (hTL : ∀ s ∈ T, SX (a s) ⊆ L) :
    5 * (T.biUnion (fun s => SX (a s))).card ≤ 4 * cnt kN c0 SX L n + 8 * T.card := by
  have h1 := botW ins kN c0 base SX L hfan hb hg hin n (T.image a) (by
    intro w hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨ha s (hT hs), ?_, hTL s hs⟩
    rcases ha s (hT hs) with hb' | ⟨j, hj, hkj⟩
    · have := (hb _ hb').1
      omega
    · have := hk j hkj
      omega)
  rw [Finset.image_biUnion] at h1
  have h2 := Finset.card_image_le (s := T) (f := a)
  have h3 : (T.biUnion fun s => SX (a s)).card ≤ 4 :=
    hL ▸ Finset.card_le_card (Finset.biUnion_subset.mpr hTL)
  rcases Nat.eq_zero_or_pos T.card with h | h
  · rw [Finset.card_eq_zero.mp h]
    simp
  · omega

def SlF (S : Finset ℕ) (A B : ℕ → Finset (Fin 13)) (l : Fin 13) : Finset ℕ :=
  S.filter (fun s => B s = {l} ∧ A s ⊆ pts l)

def SpF (S : Finset ℕ) (A B : ℕ → Finset (Fin 13)) (p : Fin 13) : Finset ℕ :=
  S.filter (fun s => A s = {p} ∧ 2 ≤ (B s).card ∧ B s ⊆ lns p)

theorem comb (S : Finset ℕ) (A B : ℕ → Finset (Fin 13)) (GX GY : Fin 13 → ℕ)
    (hinc : ∀ s ∈ S, ∀ p ∈ A s, ∀ l ∈ B s, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))
    (hcov : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      ∃ s ∈ S, p ∈ A s ∧ l ∈ B s)
    (hGX : ∀ l (T : Finset ℕ), T ⊆ S → (∀ s ∈ T, A s ⊆ pts l) →
      5 * (T.biUnion A).card ≤ 4 * GX l + 8 * T.card)
    (hGY : ∀ p (T : Finset ℕ), T ⊆ S → (∀ s ∈ T, B s ⊆ lns p) →
      5 * (T.biUnion B).card ≤ 4 * GY p + 8 * T.card) :
    260 ≤ 4 * ∑ l, GX l + 4 * ∑ p, GY p + 8 * S.card := by
  have hU : ∀ l, 5 * ((SlF S A B l).biUnion A).card ≤ 4 * GX l + 8 * (SlF S A B l).card :=
    fun l => hGX l _ (Finset.filter_subset _ _) (fun s hs => (Finset.mem_filter.mp hs).2.2)
  have hV : ∀ p, 5 * ((SpF S A B p).biUnion B).card ≤ 4 * GY p + 8 * (SpF S A B p).card :=
    fun p => hGY p _ (Finset.filter_subset _ _) (fun s hs => (Finset.mem_filter.mp hs).2.2.2)
  have e1 : ∑ l, (SlF S A B l).card = (Finset.univ.biUnion (SlF S A B)).card := by
    refine (Finset.card_biUnion ?_).symm
    intro l _ l' _ hne
    show Disjoint (SlF S A B l) (SlF S A B l')
    rw [Finset.disjoint_left]
    intro s hs hs'
    have h1 := (Finset.mem_filter.mp hs).2.1
    have h2 := (Finset.mem_filter.mp hs').2.1
    rw [h1] at h2
    exact hne (Finset.singleton_injective h2)
  have e2 : ∑ p, (SpF S A B p).card = (Finset.univ.biUnion (SpF S A B)).card := by
    refine (Finset.card_biUnion ?_).symm
    intro p _ p' _ hne
    show Disjoint (SpF S A B p) (SpF S A B p')
    rw [Finset.disjoint_left]
    intro s hs hs'
    have h1 := (Finset.mem_filter.mp hs).2.1
    have h2 := (Finset.mem_filter.mp hs').2.1
    rw [h1] at h2
    exact hne (Finset.singleton_injective h2)
  have hS : ∑ l, (SlF S A B l).card + ∑ p, (SpF S A B p).card ≤ S.card := by
    rw [e1, e2]
    have hd : Disjoint (Finset.univ.biUnion (SlF S A B)) (Finset.univ.biUnion (SpF S A B)) := by
      rw [Finset.disjoint_left]
      intro s hs hs'
      rw [Finset.mem_biUnion] at hs hs'
      obtain ⟨l, _, hl⟩ := hs
      obtain ⟨p, _, hp⟩ := hs'
      have h1 := (Finset.mem_filter.mp hl).2.1
      have h2 := (Finset.mem_filter.mp hp).2.2.1
      rw [h1, Finset.card_singleton] at h2
      omega
    rw [← Finset.card_union_of_disjoint hd]
    apply Finset.card_le_card
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rw [Finset.mem_biUnion] at hs
      obtain ⟨l, _, hl⟩ := hs
      exact (Finset.mem_filter.mp hl).1
    · rw [Finset.mem_biUnion] at hs
      obtain ⟨p, _, hp⟩ := hs
      exact (Finset.mem_filter.mp hp).1
  have hflag : ∀ l : Fin 13, 4 ≤ ((SlF S A B l).biUnion A).card +
      (Finset.univ.filter (fun p => l ∈ (SpF S A B p).biUnion B)).card := by
    intro l
    rw [← g_pts l]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro p hp
    rw [mem_pts] at hp
    obtain ⟨s, hs, hpa, hlb⟩ := hcov p l hp
    by_cases hc : 2 ≤ (B s).card
    · apply Finset.mem_union_right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨s, ?_, hlb⟩
      rw [SpF, Finset.mem_filter]
      refine ⟨hs, ?_, hc, ?_⟩
      · rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hpa, ?_⟩
        intro p' hp'
        by_contra hne
        have h1 := g_pp p' p hne
        have hsub : B s ⊆ lns p' ∩ lns p := by
          intro l' hl'
          rw [Finset.mem_inter, mem_lns, mem_lns]
          exact ⟨hinc s hs p' hp' l' hl', hinc s hs p hpa l' hl'⟩
        have h2 := Finset.card_le_card hsub
        omega
      · intro l' hl'
        rw [mem_lns]
        exact hinc s hs p hpa l' hl'
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨s, ?_, hpa⟩
      rw [SlF, Finset.mem_filter]
      refine ⟨hs, ?_, ?_⟩
      · rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hlb, ?_⟩
        intro l' hl'
        exact Finset.card_le_one.mp (by omega) l' hl' l hlb
      · intro p' hp'
        rw [mem_pts]
        exact hinc s hs p' hp' l hlb
  have hdc : ∑ l, (Finset.univ.filter (fun p => l ∈ (SpF S A B p).biUnion B)).card =
      ∑ p, ((SpF S A B p).biUnion B).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.card_filter]
    congr 1
    ext l
    simp
  have s1 := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 13))) => hflag l)
  rw [Finset.sum_add_distrib, hdc] at s1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at s1
  have s2 := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 13))) => hU l)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at s2
  have s3 := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin 13))) => hV p)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at s3
  omega

def SXs (v : (Fin 13 → Bool) → (Fin 13 → Bool) → ℕ → Bool) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => v (fun u => decide (u = p)) (fun _ => false) w = true)

def SYs (v : (Fin 13 → Bool) → (Fin 13 → Bool) → ℕ → Bool) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => v (fun _ => false) (fun u => decide (u = l)) w = true)

theorem mem_SXs (v : (Fin 13 → Bool) → (Fin 13 → Bool) → ℕ → Bool) (w : ℕ) (p : Fin 13) :
    p ∈ SXs v w ↔ v (fun u => decide (u = p)) (fun _ => false) w = true := by
  unfold SXs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_SYs (v : (Fin 13 → Bool) → (Fin 13 → Bool) → ℕ → Bool) (w : ℕ) (l : Fin 13) :
    l ∈ SYs v w ↔ v (fun _ => false) (fun u => decide (u = l)) w = true := by
  unfold SYs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem core (ins : ℕ → List ℕ) (kN : ℕ → ℕ) (n out : ℕ)
    (v : (Fin 13 → Bool) → (Fin 13 → Bool) → ℕ → Bool)
    (hfan : ∀ j, (ins j).length ≤ 2)
    (hlt : ∀ j, ∀ w ∈ ins j, w < 26 + j)
    (hk : ∀ j, kN j < 4 ↔ j < n)
    (hvx : ∀ x y (p : Fin 13), v x y p.val = x p)
    (hvy : ∀ x y (l : Fin 13), v x y (13 + l.val) = y l)
    (hor : ∀ j, kN j < 4 → kN j ≠ 2 → ∀ x y,
      (v x y (26 + j) = true ↔ ∃ w ∈ ins j, v x y w = true))
    (h0 : ∀ j, kN j = 0 → ∀ w ∈ ins j, WP kN 0 (fun w => w < 13) w)
    (h1 : ∀ j, kN j = 1 → ∀ w ∈ ins j, WP kN 1 (fun w => 13 ≤ w ∧ w < 26) w)
    (h2 : ∀ j, kN j = 2 → ∃ a b, WP kN 0 (fun w => w < 13) a ∧
      WP kN 1 (fun w => 13 ≤ w ∧ w < 26) b ∧
      ∀ x y, (v x y (26 + j) = true ↔ v x y a = true ∧ v x y b = true))
    (h3 : ∀ j, kN j = 3 → ∀ w ∈ ins j, ∃ j', w = 26 + j' ∧ (kN j' = 2 ∨ kN j' = 3))
    (hout : ∃ j, out = 26 + j ∧ (kN j = 2 ∨ kN j = 3))
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      v (fun u => decide (u = p)) (fun u => decide (u = l)) out = true)
    (hrej : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter
        (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      v (fun u => decide (u ∈ Q))
        (fun u => decide (∀ r ∈ Q, r - u ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) out = false) :
    64 ≤ n := by
  have hinX : ∀ j, kN j = 0 → ∀ w ∈ ins j, WP kN 0 (fun w => w < 13) w ∧ w < 26 + j :=
    fun j hj w hw => ⟨h0 j hj w hw, hlt j w hw⟩
  have hinY : ∀ j, kN j = 1 → ∀ w ∈ ins j,
      WP kN 1 (fun w => 13 ≤ w ∧ w < 26) w ∧ w < 26 + j :=
    fun j hj w hw => ⟨h1 j hj w hw, hlt j w hw⟩
  have hX : ∀ x y w, WP kN 0 (fun w => w < 13) w →
      (v x y w = true ↔ ∃ p, x p = true ∧ p ∈ SXs v w) := by
    intro x y w hw
    have := orlin ins kN 0 (fun w => w < 13) (v x y)
      (fun p => v (fun u => decide (u = p)) (fun _ => false)) x (by
        intro w hw
        have e1 : v x y w = x ⟨w, hw⟩ := hvx x y ⟨w, hw⟩
        have e2 : ∀ p : Fin 13, v (fun u => decide (u = p)) (fun _ => false) w =
            decide ((⟨w, hw⟩ : Fin 13) = p) := fun p => hvx _ _ ⟨w, hw⟩
        simp only [e1, e2, decide_eq_true_eq]
        constructor
        · intro h
          exact ⟨_, h, rfl⟩
        · rintro ⟨p, hp, rfl⟩
          exact hp)
      (fun j hj => hor j (by omega) (by omega) x y)
      (fun j hj p => hor j (by omega) (by omega) _ _) hinX w hw
    simp only [mem_SXs]
    exact this
  have hY : ∀ x y w, WP kN 1 (fun w => 13 ≤ w ∧ w < 26) w →
      (v x y w = true ↔ ∃ l, y l = true ∧ l ∈ SYs v w) := by
    intro x y w hw
    have := orlin ins kN 1 (fun w => 13 ≤ w ∧ w < 26) (v x y)
      (fun l => v (fun _ => false) (fun u => decide (u = l))) y (by
        intro w hw
        have hw' : w - 13 < 13 := by omega
        have hw2 : 13 + (w - 13) = w := by omega
        have e1 : v x y w = y ⟨w - 13, hw'⟩ := by
          have := hvy x y ⟨w - 13, hw'⟩
          simp only [hw2] at this
          exact this
        have e2 : ∀ l : Fin 13, v (fun _ => false) (fun u => decide (u = l)) w =
            decide ((⟨w - 13, hw'⟩ : Fin 13) = l) := by
          intro l
          have := hvy (fun _ => false) (fun u => decide (u = l)) ⟨w - 13, hw'⟩
          simp only [hw2] at this
          exact this
        simp only [e1, e2, decide_eq_true_eq]
        constructor
        · intro h
          exact ⟨_, h, rfl⟩
        · rintro ⟨p, hp, rfl⟩
          exact hp)
      (fun j hj => hor j (by omega) (by omega) x y)
      (fun j hj p => hor j (by omega) (by omega) _ _) hinY w hw
    simp only [mem_SYs]
    exact this
  have hbX : ∀ w, (fun w => w < 13) w → w < 26 ∧ (SXs v w).card ≤ 1 := by
    intro w hw
    have hw' : w < 13 := hw
    refine ⟨by omega, ?_⟩
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [mem_SXs] at hp hq
    have e2 : ∀ p : Fin 13, v (fun u => decide (u = p)) (fun _ => false) w =
        decide ((⟨w, hw'⟩ : Fin 13) = p) := fun p => hvx _ _ ⟨w, hw'⟩
    rw [e2, decide_eq_true_eq] at hp hq
    rw [← hp, ← hq]
  have hbY : ∀ w, (fun w => 13 ≤ w ∧ w < 26) w → w < 26 ∧ (SYs v w).card ≤ 1 := by
    intro w hw
    have hw0 : 13 ≤ w ∧ w < 26 := hw
    have hw' : w - 13 < 13 := by omega
    have hw2 : 13 + (w - 13) = w := by omega
    refine ⟨by omega, ?_⟩
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [mem_SYs] at hp hq
    have e2 : ∀ l : Fin 13, v (fun _ => false) (fun u => decide (u = l)) w =
        decide ((⟨w - 13, hw'⟩ : Fin 13) = l) := by
      intro l
      have := hvy (fun _ => false) (fun u => decide (u = l)) ⟨w - 13, hw'⟩
      simp only [hw2] at this
      exact this
    rw [e2, decide_eq_true_eq] at hp hq
    rw [← hp, ← hq]
  have hgX : ∀ j, kN j = 0 → SXs v (26 + j) = (ins j).toFinset.biUnion (SXs v) := by
    intro j hj
    ext p
    rw [mem_SXs, hor j (by omega) (by omega), Finset.mem_biUnion]
    constructor
    · rintro ⟨w, hw, h⟩
      exact ⟨w, List.mem_toFinset.mpr hw, (mem_SXs v w p).2 h⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w, List.mem_toFinset.mp hw, (mem_SXs v w p).1 h⟩
  have hgY : ∀ j, kN j = 1 → SYs v (26 + j) = (ins j).toFinset.biUnion (SYs v) := by
    intro j hj
    ext p
    rw [mem_SYs, hor j (by omega) (by omega), Finset.mem_biUnion]
    constructor
    · rintro ⟨w, hw, h⟩
      exact ⟨w, List.mem_toFinset.mpr hw, (mem_SYs v w p).2 h⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w, List.mem_toFinset.mp hw, (mem_SYs v w p).1 h⟩
  obtain ⟨S, hS2, hSiff, hScard⟩ := topW ins kN v hfan
    (fun j hj w hw => ⟨h3 j hj w hw, hlt j w hw⟩)
    (fun j hj => hor j (by omega) (by omega)) n {out} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      subst hw
      obtain ⟨j, hj, hkj⟩ := hout
      exact ⟨j, hj, (hk j).1 (by omega), hkj⟩)
  simp only [Finset.mem_singleton, exists_eq_left, Finset.card_singleton] at hSiff hScard
  choose! a b ha hb hab using h2
  have rect : ∀ s, kN s = 2 → ∀ x y, (v x y (26 + s) = true ↔
      (∃ p, x p = true ∧ p ∈ SXs v (a s)) ∧ ∃ l, y l = true ∧ l ∈ SYs v (b s)) := by
    intro s hs x y
    rw [hab s hs x y, hX x y _ (ha s hs), hY x y _ (hb s hs)]
  have hinc : ∀ s ∈ S, ∀ p ∈ SXs v (a s), ∀ l ∈ SYs v (b s),
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    intro s hs p hp l hl
    by_contra hn
    obtain ⟨hq1, hq2, hq3, hq4⟩ := g_quad p l hn
    have hr := hrej (Qf p l) hq1 hq2
    have ht := (hSiff (fun u => decide (u ∈ Qf p l))
      (fun u => decide (∀ r ∈ Qf p l, r - u ∉ ({0, 1, 3, 9} : Finset (Fin 13))))).2
      ⟨s, hs, (rect s (hS2 s hs) _ _).2
        ⟨⟨p, decide_eq_true hq3, hp⟩, l, decide_eq_true hq4, hl⟩⟩
    exact Bool.false_ne_true (hr.symm.trans ht)
  have hcov : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      ∃ s ∈ S, p ∈ SXs v (a s) ∧ l ∈ SYs v (b s) := by
    intro p l h
    obtain ⟨s, hs, hv⟩ := (hSiff _ _).1 (hacc p l h)
    obtain ⟨⟨p', hp', hpa⟩, ⟨l', hl', hlb⟩⟩ := (rect s (hS2 s hs) _ _).1 hv
    have ep : p' = p := of_decide_eq_true hp'
    have el : l' = l := of_decide_eq_true hl'
    rw [ep] at hpa
    rw [el] at hlb
    exact ⟨s, hs, hpa, hlb⟩
  have hkX : ∀ j, kN j = 0 → j < n := fun j hj => (hk j).1 (by omega)
  have hkY : ∀ j, kN j = 1 → j < n := fun j hj => (hk j).1 (by omega)
  have hc := comb S (fun s => SXs v (a s)) (fun s => SYs v (b s))
    (fun l => cnt kN 0 (SXs v) (pts l) n) (fun p => cnt kN 1 (SYs v) (lns p) n) hinc hcov
    (fun l T hT hTL => side ins kN 0 (fun w => w < 13) (SXs v) n hfan hbX hgX hinX hkX S a
      (fun s hs => ha s (hS2 s hs)) (pts l) (g_pts l) T hT hTL)
    (fun p T hT hTL => side ins kN 1 (fun w => 13 ≤ w ∧ w < 26) (SYs v) n hfan hbY hgY hinY hkY
      S b (fun s hs => hb s (hS2 s hs)) (lns p) (g_lns p) T hT hTL)
  have hK0 := cnt_sum kN 0 (SXs v) n pts g_ll
  have hK1 := cnt_sum kN 1 (SYs v) n lns g_pp
  have hK2 : S.card ≤ ((Finset.range n).filter (fun j => kN j = 2)).card := by
    apply Finset.card_le_card
    intro s hs
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(hk s).1 (by have := hS2 s hs; omega), hS2 s hs⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (s := Finset.range n) (t := Finset.range 4)
    (f := kN) (by
      intro j hj
      have hj' : j < n := Finset.mem_range.1 (Finset.mem_coe.1 hj)
      exact Finset.mem_coe.2 (Finset.mem_range.2 ((hk j).2 hj')))
  rw [Finset.card_range] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  omega

def kNf (gates : List Gate) (kind : Fin gates.length → Fin 4) (j : ℕ) : ℕ :=
  if h : j < gates.length then (kind ⟨j, h⟩).val else 4

def insf (gates : List Gate) (j : ℕ) : List ℕ :=
  if h : j < gates.length then gates[j].inputs else []

def vf (gates : List Gate) (x y : Fin 13 → Bool) (w : ℕ) : Bool :=
  val gates w (Fin.append x y)

theorem kNf_lt (gates : List Gate) (kind : Fin gates.length → Fin 4) (j : ℕ)
    (h : j < gates.length) : kNf gates kind j = (kind ⟨j, h⟩).val := by
  rw [kNf, dif_pos h]

theorem kconv (gates : List Gate) (kind : Fin gates.length → Fin 4) (c : Fin 4)
    (j' : Fin gates.length) (h : kind j' = c) : kNf gates kind j'.val = c.val := by
  rw [kNf_lt gates kind j'.val j'.isLt]
  exact congrArg Fin.val h

theorem kconv' (gates : List Gate) (kind : Fin gates.length → Fin 4) (c : Fin 4) (j : ℕ)
    (h : j < gates.length) (hk : kNf gates kind j = c.val) : kind ⟨j, h⟩ = c := by
  apply Fin.ext
  rw [← kNf_lt gates kind j h]
  exact hk

theorem fin4 : ∀ t : Fin 4, t.val ≠ 2 → t = 0 ∨ t = 1 ∨ t = 3 := by decide

theorem glue : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ) (kind : Fin gates.length → Fin 4), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ i : Fin gates.length, (kind i = 0 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ w ∈ (gates.get i).inputs, (w < 13 ∨ ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ kind j = 0)) ∧ (kind i = 1 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ w ∈ (gates.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ kind j = 1)) ∧ (kind i = 2 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ a b : ℕ, ((gates.get i).inputs = [a, b] ∨ (gates.get i).inputs = [b, a]) ∧ (a < 13 ∨ ∃ j : Fin gates.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧ ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gates.length, b = 26 + (j : ℕ) ∧ kind j = 1)) ∧ (kind i = 3 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ w ∈ (gates.get i).inputs, ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))) → (∃ j : Fin gates.length, out = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  intro gates out kind hop hlt hkind hout hacc hrej
  have hk : ∀ j, kNf gates kind j < 4 ↔ j < gates.length := by
    intro j
    constructor
    · intro hh
      by_contra hn
      rw [kNf, dif_neg hn] at hh
      omega
    · intro h
      rw [kNf_lt gates kind j h]
      exact (kind ⟨j, h⟩).isLt
  have hlt' : ∀ j, ∀ w ∈ insf gates j, w < 26 + j := by
    intro j w hw
    by_cases h : j < gates.length
    · rw [insf, dif_pos h] at hw
      exact hlt ⟨j, h⟩ w hw
    · rw [insf, dif_neg h] at hw
      simp at hw
  refine core (insf gates) (kNf gates kind) gates.length out (vf gates) ?_ hlt' hk ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  · intro j
    by_cases h : j < gates.length
    · rw [insf, dif_pos h]
      exact (hop _ (List.getElem_mem h)).2
    · rw [insf, dif_neg h]
      simp
  · intro x y p
    unfold vf
    rw [val_input gates _ p.val (by have := p.isLt; omega)]
    exact Fin.append_left x y p
  · intro x y l
    unfold vf
    rw [val_input gates _ (13 + l.val) (by have := l.isLt; omega)]
    exact Fin.append_right x y l
  · intro j hj4 hj2 x y
    have h : j < gates.length := (hk j).1 hj4
    have hopj : gates[j].op = GateOp.or := by
      have hk' := kNf_lt gates kind j h
      obtain ⟨c0, c1, c2, c3⟩ := hkind ⟨j, h⟩
      rw [hk'] at hj2
      rcases fin4 _ hj2 with e | e | e
      · exact (c0 e).1
      · exact (c1 e).1
      · exact (c3 e).1
    have hv : (val gates (26 + j) (Fin.append x y) = true ↔
        ∃ i ∈ gates[j].inputs, i < 26 + j ∧ val gates i (Fin.append x y) = true) :=
      val_or gates (Fin.append x y) j h hopj
    unfold vf
    rw [insf, dif_pos h, hv]
    constructor
    · rintro ⟨i, hi, _, hv'⟩
      exact ⟨i, hi, hv'⟩
    · rintro ⟨i, hi, hv'⟩
      exact ⟨i, hi, hlt ⟨j, h⟩ i hi, hv'⟩
  · intro j hj w hw
    have h : j < gates.length := (hk j).1 (by omega)
    rw [insf, dif_pos h] at hw
    have e := kconv' gates kind 0 j h hj
    rcases ((hkind ⟨j, h⟩).1 e).2 w hw with h' | ⟨j', hj', hk'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨j'.val, hj', kconv gates kind 0 j' hk'⟩
  · intro j hj w hw
    have h : j < gates.length := (hk j).1 (by omega)
    rw [insf, dif_pos h] at hw
    have e := kconv' gates kind 1 j h hj
    rcases ((hkind ⟨j, h⟩).2.1 e).2 w hw with h' | ⟨j', hj', hk'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨j'.val, hj', kconv gates kind 1 j' hk'⟩
  · intro j hj
    have h : j < gates.length := (hk j).1 (by omega)
    have e := kconv' gates kind 2 j h hj
    obtain ⟨hopj, a, b, hab, ha, hb⟩ := (hkind ⟨j, h⟩).2.2.1 e
    have hab' : gates[j].inputs = [a, b] ∨ gates[j].inputs = [b, a] := hab
    refine ⟨a, b, ?_, ?_, ?_⟩
    · rcases ha with h' | ⟨j', hj', hk'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨j'.val, hj', kconv gates kind 0 j' hk'⟩
    · rcases hb with h' | ⟨j', hj', hk'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨j'.val, hj', kconv gates kind 1 j' hk'⟩
    · intro x y
      have hv : (val gates (26 + j) (Fin.append x y) = true ↔
          ∀ i ∈ gates[j].inputs, i < 26 + j ∧ val gates i (Fin.append x y) = true) :=
        val_and gates (Fin.append x y) j h hopj
      have hmem : ∀ i, i ∈ gates[j].inputs ↔ i = a ∨ i = b := by
        intro i
        rcases hab' with e' | e'
        · rw [e']
          simp
        · rw [e']
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact or_comm
      have hla : a < 26 + j := hlt ⟨j, h⟩ a ((hmem a).2 (Or.inl rfl))
      have hlb : b < 26 + j := hlt ⟨j, h⟩ b ((hmem b).2 (Or.inr rfl))
      unfold vf
      rw [hv]
      constructor
      · intro H
        exact ⟨(H a ((hmem a).2 (Or.inl rfl))).2, (H b ((hmem b).2 (Or.inr rfl))).2⟩
      · rintro ⟨H1, H2⟩ i hi
        rcases (hmem i).1 hi with e' | e'
        · rw [e']
          exact ⟨hla, H1⟩
        · rw [e']
          exact ⟨hlb, H2⟩
  · intro j hj w hw
    have h : j < gates.length := (hk j).1 (by omega)
    rw [insf, dif_pos h] at hw
    have e := kconv' gates kind 3 j h hj
    obtain ⟨j', hj', hk'⟩ := ((hkind ⟨j, h⟩).2.2.2 e).2 w hw
    exact ⟨j'.val, hj', hk'.imp (kconv gates kind 2 j') (kconv gates kind 3 j')⟩
  · obtain ⟨j, hj, hk'⟩ := hout
    exact ⟨j.val, hj, hk'.imp (kconv gates kind 2 j) (kconv gates kind 3 j)⟩
  · intro p l h
    have := hacc p l h
    rw [eval_eq, ← List.ofFn_fin_append] at this
    exact this
  · intro Q h1 h2
    have := hrej Q h1 h2
    rw [eval_eq, ← List.ofFn_fin_append] at this
    exact this

end PEqualNP.Outside.L_meta_1693

theorem PEqualNP.Outside.L_meta_1693 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ) (kind : Fin gates.length → Fin 4), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ i : Fin gates.length, (kind i = 0 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ w ∈ (gates.get i).inputs, (w < 13 ∨ ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ kind j = 0)) ∧ (kind i = 1 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ w ∈ (gates.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ kind j = 1)) ∧ (kind i = 2 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ a b : ℕ, ((gates.get i).inputs = [a, b] ∨ (gates.get i).inputs = [b, a]) ∧ (a < 13 ∨ ∃ j : Fin gates.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧ ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gates.length, b = 26 + (j : ℕ) ∧ kind j = 1)) ∧ (kind i = 3 → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ w ∈ (gates.get i).inputs, ∃ j : Fin gates.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))) → (∃ j : Fin gates.length, out = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  exact PEqualNP.Outside.L_meta_1693.glue
