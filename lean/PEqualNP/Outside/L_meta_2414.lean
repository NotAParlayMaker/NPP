import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2414


def St (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (ra rb : ℕ) : Prop :=
  ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs

theorem r_le (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∀ a b, Relation.ReflTransGen (St n C) a b → a ≤ b := by
  intro a b h
  induction h with
  | refl => exact le_refl _
  | tail _ hs ih => exact le_trans ih (le_of_lt hs.1)

theorem r_last (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∀ a b, Relation.ReflTransGen (St n C) a b → a = b ∨ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
  intro a b h
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, _, hs⟩
  · exact Or.inl h1.symm
  · obtain ⟨_, rj, h1, h2, h3, _⟩ := hs
    exact Or.inr ⟨rj, h1, h2, h3⟩

theorem r_dec (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∀ m rj, Relation.ReflTransGen (St n C) m (n + rj) → m = n + rj ∨
      ∃ c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs, Relation.ReflTransGen (St n C) m c := by
  intro m rj h
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hmc, hs⟩
  · exact Or.inl h1.symm
  · obtain ⟨_, rj2, h1, h2, h3, h4⟩ := hs
    have h5 : rj2 = rj := by omega
    subst h5
    exact Or.inr ⟨c, h4, hmc⟩

theorem count {α : Type} [DecidableEq α] (L : ℕ → Finset α) (Rr : ℕ → ℕ → Prop) (isOr : ℕ → Prop)
    (hle : ∀ a b, Rr a b → a ≤ b) (hrefl : ∀ a, Rr a a)
    (htrans : ∀ a b c, Rr a b → Rr b c → Rr a c)
    (hleaf : ∀ w, ¬ isOr w → (L w).card ≤ 2)
    (hor : ∀ w, isOr w → ∃ p q, p < w ∧ q < w ∧ L w ⊆ L p ∪ L q ∧ Rr p w ∧ Rr q w) :
    ∀ N, ∀ W : Finset ℕ, (∀ w ∈ W, w < N) → ∀ B : Finset ℕ,
      (∀ g, isOr g → 3 ≤ (L g).card → (∃ r ∈ W, Rr g r) → g ∈ B) →
      (W.biUnion L).card ≤ 2 * (W.card + B.card) := by
  intro N
  induction N with
  | zero =>
    intro W hW B _
    have hWe : W = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by have := hW w hw; omega)
    subst hWe
    simp
  | succ N ih =>
    intro W hW B hB
    by_cases hN : N ∈ W
    · by_cases hbig : 3 ≤ (L N).card
      · have hisor : isOr N := by
          by_contra h
          have := hleaf N h
          omega
        obtain ⟨p, q, hp, hq, hsub, hRp, hRq⟩ := hor N hisor
        have hNB : N ∈ B := hB N hisor hbig ⟨N, hN, hrefl N⟩
        have h1 := ih (insert p (insert q (W.erase N))) (by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | rfl | ⟨hne, hw⟩
            · exact hp
            · exact hq
            · have := hW w hw
              omega) (B.erase N) (by
            intro g hg hg3 ⟨r, hr, hgr⟩
            simp only [Finset.mem_insert, Finset.mem_erase] at hr
            have hgle := hle g r hgr
            rcases hr with rfl | rfl | ⟨hne, hr⟩
            · exact Finset.mem_erase.mpr ⟨by omega, hB g hg hg3 ⟨N, hN, htrans _ _ _ hgr hRp⟩⟩
            · exact Finset.mem_erase.mpr ⟨by omega, hB g hg hg3 ⟨N, hN, htrans _ _ _ hgr hRq⟩⟩
            · have := hW r hr
              exact Finset.mem_erase.mpr ⟨by omega, hB g hg hg3 ⟨r, hr, hgr⟩⟩)
        have hsubU : W.biUnion L ⊆ (insert p (insert q (W.erase N))).biUnion L := by
          intro x hx
          rw [Finset.mem_biUnion] at hx ⊢
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hwN : w = N
          · rw [hwN] at hxw
            rcases Finset.mem_union.mp (hsub hxw) with h | h
            · exact ⟨p, by simp, h⟩
            · exact ⟨q, by simp, h⟩
          · exact ⟨w, by simp [hwN, hw], hxw⟩
        have hc1 := Finset.card_le_card hsubU
        have hc2 : (insert p (insert q (W.erase N))).card ≤ (W.erase N).card + 2 := by
          have a1 := Finset.card_insert_le p (insert q (W.erase N))
          have a2 := Finset.card_insert_le q (W.erase N)
          omega
        have hc3 := Finset.card_erase_of_mem hN
        have hc4 := Finset.card_erase_of_mem hNB
        have hc5 : 0 < W.card := Finset.card_pos.mpr ⟨N, hN⟩
        have hc6 : 0 < B.card := Finset.card_pos.mpr ⟨N, hNB⟩
        omega
      · have h1 := ih (W.erase N) (by
            intro w hw
            have h2 := Finset.mem_erase.mp hw
            have := hW w h2.2
            omega) B (by
            intro g hg hg3 ⟨r, hr, hgr⟩
            exact hB g hg hg3 ⟨r, (Finset.mem_erase.mp hr).2, hgr⟩)
        have hsubU : W.biUnion L ⊆ L N ∪ (W.erase N).biUnion L := by
          intro x hx
          rw [Finset.mem_biUnion] at hx
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hwN : w = N
          · rw [hwN] at hxw
            exact Finset.mem_union_left _ hxw
          · exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwN, hw⟩, hxw⟩)
        have hc1 := Finset.card_le_card hsubU
        have hc2 := Finset.card_union_le (L N) ((W.erase N).biUnion L)
        have hc3 := Finset.card_erase_of_mem hN
        have hc5 : 0 < W.card := Finset.card_pos.mpr ⟨N, hN⟩
        omega
    · exact ih W (by
        intro w hw
        have := hW w hw
        have hne : w ≠ N := by
          rintro rfl
          exact hN hw
        omega) B hB


theorem big : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ 2 * (roots.card + {jb : ℕ | jb < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jb).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jb) r2) ∧ 3 ≤ ({x3 : α | ∃ m3 ∈ labelled, R m3 (n + jb) ∧ x3 ∈ lab m3}).ncard}.ncard) := by
  intro n C α S roots labelled lab hAO R hR hlab hS
  have hR2 : R = Relation.ReflTransGen (PEqualNP.Outside.L_meta_2414.St n C) := hR
  clear hR
  subst hR2
  classical
  obtain ⟨L, mem_L⟩ : ∃ L : ℕ → Finset α, ∀ w x, x ∈ L w ↔ ∃ m ∈ labelled,
      Relation.ReflTransGen (PEqualNP.Outside.L_meta_2414.St n C) m w ∧ x ∈ lab m := by
    refine ⟨fun w => (labelled.filter (fun m =>
      Relation.ReflTransGen (PEqualNP.Outside.L_meta_2414.St n C) m w)).biUnion lab, ?_⟩
    intro w x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨m, ⟨hm, hr⟩, hx⟩
      exact ⟨m, hm, hr, hx⟩
    · rintro ⟨m, hm, hr, hx⟩
      exact ⟨m, ⟨hm, hr⟩, hx⟩
  have hleaf : ∀ w, ¬ (∃ rj, w = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (L w).card ≤ 2 := by
    intro w hnot
    by_cases hw : w ∈ labelled
    · have hsub : L w ⊆ lab w := by
        intro x hx
        obtain ⟨m, hm, hmw, hxm⟩ := (mem_L w x).mp hx
        rcases PEqualNP.Outside.L_meta_2414.r_last n C m w hmw with h | h
        · rw [← h]
          exact hxm
        · exact absurd h hnot
      exact le_trans (Finset.card_le_card hsub) (hlab w hw).2
    · have hsub : L w ⊆ ∅ := by
        intro x hx
        obtain ⟨m, hm, hmw, hxm⟩ := (mem_L w x).mp hx
        rcases PEqualNP.Outside.L_meta_2414.r_last n C m w hmw with h | h
        · rw [h] at hm
          exact absurd hm hw
        · exact absurd h hnot
      rw [Finset.subset_empty.mp hsub]
      simp
  have hor : ∀ w, (∃ rj, w = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∃ p q, p < w ∧ q < w ∧ L w ⊆ L p ∪ L q ∧
        Relation.ReflTransGen (PEqualNP.Outside.L_meta_2414.St n C) p w ∧
        Relation.ReflTransGen (PEqualNP.Outside.L_meta_2414.St n C) q w := by
    rintro w ⟨rj, rfl, hlt, hop⟩
    have hmemg : PEqualNP.MetaComplexity.NestedCover.gateAt C rj ∈ C.gates := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem _
    have hlen := hAO.2.2 _ hmemg
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
    have hpm : p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs := by
      rw [hpq]
      simp
    have hqm : q ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs := by
      rw [hpq]
      simp
    have hp : p < n + rj := hAO.2.1 rj hlt p hpm
    have hq : q < n + rj := hAO.2.1 rj hlt q hqm
    refine ⟨p, q, hp, hq, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨m, hm, hmw, hxm⟩ := (mem_L _ x).mp hx
      rcases PEqualNP.Outside.L_meta_2414.r_dec n C m rj hmw with h | ⟨c, hc, hmc⟩
      · rcases (hlab m hm).1 with h2 | ⟨j, hj, _, hand⟩
        · omega
        · have hjj : j = rj := by omega
          subst hjj
          exact absurd (hop.symm.trans hand) (by intro h3; cases h3)
      · rw [hpq] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact Finset.mem_union_left _ ((mem_L _ x).mpr ⟨m, hm, hmc, hxm⟩)
        · exact Finset.mem_union_right _ ((mem_L _ x).mpr ⟨m, hm, hmc, hxm⟩)
    · exact Relation.ReflTransGen.single ⟨hp, rj, rfl, hlt, hop, hpm⟩
    · exact Relation.ReflTransGen.single ⟨hq, rj, rfl, hlt, hop, hqm⟩
  have key : ∀ T : Set ℕ, (∀ jb, jb < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C jb).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∃ r2 ∈ roots, Relation.ReflTransGen (PEqualNP.Outside.L_meta_2414.St n C) (n + jb) r2) →
      3 ≤ (L (n + jb)).card → jb ∈ T) → T.Finite → S.card ≤ 2 * (roots.card + T.ncard) := by
    intro T hT hfin
    have hcount := PEqualNP.Outside.L_meta_2414.count L
      (Relation.ReflTransGen (PEqualNP.Outside.L_meta_2414.St n C))
      (fun w => ∃ rj, w = n + rj ∧ rj < C.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (PEqualNP.Outside.L_meta_2414.r_le n C) (fun a => Relation.ReflTransGen.refl)
      (fun a b c h1 h2 => Relation.ReflTransGen.trans h1 h2) hleaf hor
      (roots.sup id + 1) roots (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
      (hfin.toFinset.image (fun j => n + j)) (by
        rintro g ⟨rj, rfl, hlt, hop⟩ hg3 hr
        exact Finset.mem_image.mpr ⟨rj, hfin.mem_toFinset.mpr (hT rj hlt hop hr hg3), rfl⟩)
    have hSsub : S ⊆ roots.biUnion L := by
      intro a ha
      obtain ⟨r, hr, m1, hm1, hR1, ha1⟩ := hS a ha
      exact Finset.mem_biUnion.mpr ⟨r, hr, (mem_L r a).mpr ⟨m1, hm1, hR1, ha1⟩⟩
    have h1 := Finset.card_le_card hSsub
    have h2 : (hfin.toFinset.image (fun j => n + j)).card ≤ T.ncard := by
      rw [Set.ncard_eq_toFinset_card T hfin]
      exact Finset.card_image_le
    omega
  refine key _ ?_ ?_
  · intro jb h1 h2 h3 h4
    refine ⟨h1, h2, h3, ?_⟩
    refine le_of_le_of_eq h4 ?_
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    rw [Finset.mem_coe, mem_L]
    rfl
  · exact Set.Finite.subset (Set.finite_lt_nat C.gates.length) (fun j hj => hj.1)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem eval_eq (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    circuitFun n C x = val C.gates C.output x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    val gs (n + k) x = true ↔ ∀ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs w x = x ⟨w, hw⟩ := by
  rw [val, fd_keep stB false gs _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def Rr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)

theorem or_path (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ) (h : Rr n C a b) :
    val C.gates a x = true → val C.gates b x = true := by
  unfold Rr at h
  induction h with
  | refl => exact id
  | tail _ hs ih =>
    intro ha
    obtain ⟨hlt, rj, rfl, hj, hop, hin⟩ := hs
    rw [gateAt_eq C rj hj] at hop hin
    exact (val_or C.gates x rj hj hop).2 ⟨_, hin, hlt, ih ha⟩

theorem wires_eq (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = val C.gates w x := rfl

theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim


theorem Rr_trans (n : ℕ) (C : Circuit) (a b c : ℕ) (h1 : Rr n C a b) (h2 : Rr n C b c) : Rr n C a c := by
  unfold Rr at *
  exact Relation.ReflTransGen.trans h1 h2

theorem keyK (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (hC : IsAO2 n C) (hpn : ∀ p2 : Fin N, pw p2 < n)
    (hS : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false)
    (t mm : ℕ) (p' : Fin N) (l : Fin M) (hR : Rr n C t mm)
    (hout : ∀ z : Fin n → Bool, (∃ h : pw p' < n, z ⟨pw p', h⟩ = true) →
      (C.wires (List.ofFn z)).getD mm false = true → circuitFun n C z = true)
    (hdirt : ∀ pz : Fin N, ¬ I pz l → ∃ (P : Finset (Fin N)) (Y : Finset (Fin M)),
      P.card ≤ 1 ∧ Y.card ≤ 2 ∧ (∀ a ∈ insert pz P, ∀ y ∈ Y, ¬ I a y) ∧
      (C.wires (List.ofFn (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)))).getD t false = true) :
    I p' l := by
  by_contra hn
  obtain ⟨P, Y, hP, hY, hno, hw⟩ := hdirt p' hn
  have hz := hS (insert p' P) Y (le_trans (Finset.card_insert_le _ _) (by omega)) hY hno
  have hm := wires_mono C hC.1
    (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw))
    (fun k : Fin n => decide (k.val ∈ (insert p' P).image pw ∪ Y.image lw))
    (by
      intro k hk
      have hk2 := of_decide_eq_true hk
      apply decide_eq_true
      rcases Finset.mem_union.1 hk2 with h | h
      · exact Finset.mem_union_left _ (Finset.image_subset_image (Finset.subset_insert _ _) h)
      · exact Finset.mem_union_right _ h) t hw
  have hm1 := (wires_eq C (fun k : Fin n => decide (k.val ∈ (insert p' P).image pw ∪ Y.image lw)) t).symm.trans hm
  have hm2 := or_path n C _ t mm hR hm1
  have hm3 := (wires_eq C (fun k : Fin n => decide (k.val ∈ (insert p' P).image pw ∪ Y.image lw)) mm).trans hm2
  have h := hout _ ⟨hpn p', decide_eq_true (Finset.mem_union_left _
    (Finset.mem_image_of_mem pw (Finset.mem_insert_self _ _)))⟩ hm3
  rw [hz] at h
  exact Bool.false_ne_true h

theorem clash (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (hpn : ∀ p2 : Fin N, pw p2 < n)
    (hS : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false)
    (p p' : Fin N) (g : ℕ) (hg : Rr n C (pw p) g)
    (hout : ∀ z : Fin n → Bool, (∃ h : pw p' < n, z ⟨pw p', h⟩ = true) →
      (C.wires (List.ofFn z)).getD g false = true → circuitFun n C z = true) : False := by
  have hz := hS {p, p'} ∅ Finset.card_le_two (by simp) (by simp)
  have h1 : val C.gates (pw p) (fun k3 : Fin n => decide (k3.val ∈
      ({p, p'} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw)) = true := by
    rw [val_input _ _ _ (hpn p)]
    exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_image_of_mem pw (by simp)))
  have h2 := or_path n C _ (pw p) g hg h1
  have h3 := (wires_eq C (fun k3 : Fin n => decide (k3.val ∈
      ({p, p'} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw)) g).trans h2
  have h := hout _ ⟨hpn p', decide_eq_true (Finset.mem_union_left _
    (Finset.mem_image_of_mem pw (by simp)))⟩ h3
  rw [hz] at h
  exact Bool.false_ne_true h

theorem two_lab {β γ : Type} [DecidableEq γ] (F : Finset β) (key : β → ℕ) (out : β → γ) (s0 s1 : ℕ)
    (h : ∀ e ∈ F, ∀ e' ∈ F, key e = key e' → out e = out e')
    (hs : ∀ e ∈ F, key e = s0 ∨ key e = s1) : (F.image out).card ≤ 2 := by
  by_contra hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 (not_le.1 hcon)
  obtain ⟨ea, hea, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨eb, heb, rfl⟩ := Finset.mem_image.1 hb
  obtain ⟨ec, hec, rfl⟩ := Finset.mem_image.1 hc
  rcases hs ea hea with h1 | h1 <;> rcases hs eb heb with h2 | h2 <;> rcases hs ec hec with h3 | h3 <;>
    first
      | exact hab (h ea hea eb heb (h1.trans h2.symm))
      | exact hac (h ea hea ec hec (h1.trans h3.symm))
      | exact hbc (h eb heb ec hec (h2.trans h3.symm))

theorem img_le {β γ δ : Type} [DecidableEq γ] [DecidableEq δ] (X : Finset β) (r : β → γ) (s : β → δ)
    (h : ∀ e ∈ X, ∀ e' ∈ X, s e = s e' → r e = r e') : (X.image r).card ≤ (X.image s).card := by
  have e1 : (X.image (fun e => (s e, r e))).image Prod.snd = X.image r := Finset.image_image
  have e3 : (X.image (fun e => (s e, r e))).image Prod.fst = X.image s := Finset.image_image
  have h1 : (X.image r).card ≤ (X.image (fun e => (s e, r e))).card := by
    rw [← e1]
    exact Finset.card_image_le
  have h2 : ((X.image (fun e => (s e, r e))).image Prod.fst).card =
      (X.image (fun e => (s e, r e))).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    have hxy2 : s e = s e' := hxy
    exact Prod.ext hxy2 (h e he e' he' hxy2)
  rw [e3] at h2
  omega

theorem slot_eq (x0 x1 a b a' b' : ℕ) (h : (x0 = a ∧ x1 = b) ∨ (x0 = b ∧ x1 = a))
    (h' : (x0 = a' ∧ x1 = b') ∨ (x0 = b' ∧ x1 = a')) (hf : x0 = a ↔ x0 = a') : a = a' ∧ b = b' := by
  by_cases hx : x0 = a
  · have hx' := hf.1 hx
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> refine ⟨?_, ?_⟩ <;> omega
  · have hx' : ¬ x0 = a' := fun h5 => hx (hf.2 h5)
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> refine ⟨?_, ?_⟩ <;> omega

theorem slot_clash (x0 x1 a b a' b' : ℕ) (h : (x0 = a ∧ x1 = b) ∨ (x0 = b ∧ x1 = a))
    (h' : (x0 = a' ∧ x1 = b') ∨ (x0 = b' ∧ x1 = a')) (hf : x0 = a ↔ x0 = a') : a = a' :=
  (slot_eq x0 x1 a b a' b' h h' hf).1

theorem two_filters (len : ℕ) (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ j, P j → Q j → False) :
    ((Finset.range len).filter P).card + ((Finset.range len).filter Q).card ≤ len := by
  have h0 : (Finset.range len).filter P ∩ (Finset.range len).filter Q = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_left.2
      (fun j hj hj' => h j (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hj').2))
  have h1 := Finset.card_union_add_card_inter ((Finset.range len).filter P) ((Finset.range len).filter Q)
  rw [h0, Finset.card_empty] at h1
  have h2 : ((Finset.range len).filter P ∪ (Finset.range len).filter Q).card ≤ (Finset.range len).card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  rw [Finset.card_range] at h2
  omega

theorem sum_disj {ι : Type} (s : Finset ι) (Bs : ι → Set ℕ) (T : Set ℕ) (hT : T.Finite)
    (hsub : ∀ i ∈ s, Bs i ⊆ T)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, ∀ x, x ∈ Bs i → x ∈ Bs j → i = j) :
    ∑ i ∈ s, (Bs i).ncard ≤ T.ncard := by
  classical
  have h1 : ∀ i ∈ s, (Bs i).ncard = (hT.toFinset.filter (fun x => x ∈ Bs i)).card := by
    intro i hi
    have e1 : Bs i = ↑(hT.toFinset.filter (fun x => x ∈ Bs i)) := by
      ext x
      rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨fun hx => ⟨hsub i hi hx, hx⟩, fun hx => hx.2⟩
    exact (congrArg Set.ncard e1).trans (Set.ncard_coe_finset _)
  rw [Finset.sum_congr rfl h1, ← Finset.card_sigma, Set.ncard_eq_toFinset_card T hT]
  refine Finset.card_le_card_of_injOn (fun x => x.2) ?_ ?_
  · intro x hx
    have hx2 := Finset.mem_sigma.1 (Finset.mem_coe.1 hx)
    exact Finset.mem_coe.2 (Finset.mem_filter.1 hx2.2).1
  · intro x hx y hy hxy
    have hx2 := Finset.mem_sigma.1 (Finset.mem_coe.1 hx)
    have hy2 := Finset.mem_sigma.1 (Finset.mem_coe.1 hy)
    have hx3 := (Finset.mem_filter.1 hx2.2).2
    have hy3 := (Finset.mem_filter.1 hy2.2).2
    have hxy2 : x.2 = y.2 := hxy
    rw [hxy2] at hx3
    have hij := hdis x.1 hx2.1 y.1 hy2.1 y.2 hx3 hy3
    exact Sigma.ext hij (heq_of_eq hxy2)

theorem sum_roots {N M : ℕ} (B : Finset (Fin N × Fin M)) (root : Fin N × Fin M → ℕ) (s : Finset (Fin N)) :
    ∑ p ∈ s, ((B.filter (fun e => e.1 = p)).image root).card ≤
      (B.image (fun e => (e.1, root e))).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun x => (x.1, x.2)) ?_ ?_
  · intro x hx
    have hx2 := Finset.mem_sigma.1 (Finset.mem_coe.1 hx)
    obtain ⟨e, he, hre⟩ := Finset.mem_image.1 hx2.2
    have he2 := Finset.mem_filter.1 he
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨e, he2.1, Prod.ext he2.2 hre⟩)
  · intro x hx y hy hxy
    have h1 : x.1 = y.1 := congrArg Prod.fst hxy
    have h2 : x.2 = y.2 := congrArg Prod.snd hxy
    exact Sigma.ext h1 (heq_of_eq h2)

def Bg (n : ℕ) (C : Circuit) {N M : ℕ} (B : Finset (Fin N × Fin M)) (root lg : Fin N × Fin M → ℕ)
    (p : Fin N) : Set ℕ :=
  {jb : ℕ | jb < C.gates.length ∧ (gateAt C jb).op = GateOp.or ∧
    (∃ r2 ∈ (B.filter (fun e => e.1 = p)).image root, Rr n C (n + jb) r2) ∧
    3 ≤ ({x3 : Fin M | ∃ m3 ∈ B.image (fun e => n + lg e), Rr n C m3 (n + jb) ∧
      x3 ∈ (B.filter (fun e => n + lg e = m3)).image Prod.snd}).ncard}

theorem layer (n N M : ℕ) (I : Fin N → Fin M → Prop) (C : Circuit) (hC : IsAO2 n C)
    (h4 : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (B : Finset (Fin N × Fin M)) (root lg : Fin N × Fin M → ℕ)
    (hand : ∀ e ∈ B, lg e < C.gates.length ∧ (gateAt C (lg e)).op = GateOp.and)
    (hreach : ∀ e ∈ B, Rr n C (n + lg e) (root e))
    (hlab2 : ∀ w : ℕ, ((B.filter (fun e => n + lg e = w)).image Prod.snd).card ≤ 2)
    (hK : ∀ e ∈ B, ∀ e' ∈ B, Rr n C (n + lg e) (root e') → I e'.1 e.2) :
    B.card ≤ 2 * ((B.image (fun e => (e.1, root e))).card +
      {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard) := by
  have hper : ∀ p : Fin N, (B.filter (fun e => e.1 = p)).card ≤
      2 * (((B.filter (fun e => e.1 = p)).image root).card + (Bg n C B root lg p).ncard) := by
    intro p
    have hb := big n C (Fin M) ((B.filter (fun e => e.1 = p)).image Prod.snd)
      ((B.filter (fun e => e.1 = p)).image root) (B.image (fun e => n + lg e))
      (fun w => (B.filter (fun e => n + lg e = w)).image Prod.snd) hC (Rr n C) rfl
      (by
        intro m hm
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hm
        exact ⟨Or.inr ⟨lg e, rfl, (hand e he).1, (hand e he).2⟩, hlab2 _⟩)
      (by
        intro a ha
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ha
        have heB := (Finset.mem_filter.1 he).1
        exact ⟨root e, Finset.mem_image_of_mem _ he, n + lg e, Finset.mem_image_of_mem _ heB,
          hreach e heB, Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨heB, rfl⟩, rfl⟩⟩)
    have hcard : ((B.filter (fun e => e.1 = p)).image Prod.snd).card =
        (B.filter (fun e => e.1 = p)).card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      have hx2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      have hy2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
      exact Prod.ext (hx2.trans hy2.symm) hxy
    rw [hcard] at hb
    exact hb
  have hI : ∀ (jb m3 : ℕ) (x3 : Fin M), Rr n C m3 (n + jb) →
      x3 ∈ (B.filter (fun e => n + lg e = m3)).image Prod.snd →
      ∀ e' ∈ B, Rr n C (n + jb) (root e') → I e'.1 x3 := by
    intro jb m3 x3 hR3 hx3 e' he' hRe'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx3
    obtain ⟨heB, hem⟩ := Finset.mem_filter.1 he
    refine hK e heB e' he' (Rr_trans n C _ _ _ ?_ hRe')
    rw [hem]
    exact hR3
  have hdis : ∀ p ∈ B.image Prod.fst, ∀ p' ∈ B.image Prod.fst, ∀ x,
      x ∈ Bg n C B root lg p → x ∈ Bg n C B root lg p' → p = p' := by
    intro p _ p' _ jb h1 h2
    by_contra hne
    obtain ⟨_, _, ⟨r, hr, hRr⟩, h3⟩ := h1
    obtain ⟨_, _, ⟨r', hr', hRr'⟩, _⟩ := h2
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨e1, he1, rfl⟩ := Finset.mem_image.1 hr'
    obtain ⟨he0B, he0p⟩ := Finset.mem_filter.1 he0
    obtain ⟨he1B, he1p⟩ := Finset.mem_filter.1 he1
    obtain ⟨a, b, ⟨ma, _, hRa, hxa⟩, ⟨mb, _, hRb, hxb⟩, hab⟩ :=
      (Set.one_lt_ncard_iff (Set.toFinite _)).1 (lt_of_lt_of_le (by norm_num) h3)
    have i1 := hI jb ma a hRa hxa e0 he0B hRr
    have i2 := hI jb ma a hRa hxa e1 he1B hRr'
    have i3 := hI jb mb b hRb hxb e0 he0B hRr
    have i4 := hI jb mb b hRb hxb e1 he1B hRr'
    rw [he0p] at i1 i3
    rw [he1p] at i2 i4
    exact h4 p p' a b hne hab ⟨i1, i2, i3, i4⟩
  have hT : ({jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_lt_nat C.gates.length) (fun j hj => hj.1)
  have hsub : ∀ p ∈ B.image Prod.fst, Bg n C B root lg p ⊆
      {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} :=
    fun p _ jb h => ⟨h.1, h.2.1⟩
  have hsum1 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := B) (t := B.image Prod.fst)
    (fun x hx => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx)))
  have hsum2 : ∑ p ∈ B.image Prod.fst, (B.filter (fun e => e.1 = p)).card ≤
      ∑ p ∈ B.image Prod.fst, 2 * (((B.filter (fun e => e.1 = p)).image root).card +
        (Bg n C B root lg p).ncard) :=
    Finset.sum_le_sum (fun p _ => hper p)
  have hsum3 := le_trans (le_of_eq hsum1) hsum2
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum3
  have hr := sum_roots B root (B.image Prod.fst)
  have ho := sum_disj (B.image Prod.fst) (Bg n C B root lg) _ hT hsub hdis
  omega

theorem main (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)) (Rd G m Mg d m2 S Sy : Fin N × Fin M → ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (hpn : ∀ p2 : Fin N, pw p2 < n) (h4 : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) (hS : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) (hA : ∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧ {x1 : Fin N | Rr n C (pw x1) (G e)} = {e.1} ∧ ((Mg e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (d e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (m2 e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (m2 e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (d e)))) ∧ Rr n C (n + Mg e) (m e) ∧ (∃ o : ℕ, ((S e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = o) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = o ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧ {y2 : Fin M | Rr n C (lw y2) (Sy e)} = {e.2} ∧ Rr n C (n + S e) (m2 e) ∧ (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) → (C.wires (List.ofFn z3)).getD ((m e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z3 = true) ∧ (∀ z4 : Fin n → Bool, (∃ h4 : pw e.1 < n, z4 ⟨pw e.1, h4⟩ = true) → (C.wires (List.ofFn z4)).getD ((m2 e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z4 = true) ∧ (C.wires (List.ofFn (fun k7 : Fin n => decide (k7.val = pw e.1)))).getD ((d e)) false = true ∧ (∀ pz5 : Fin N, ¬ I pz5 e.2 → ∃ (P5 : Finset (Fin N)) (Y5 : Finset (Fin M)), P5.card ≤ 1 ∧ Y5.card ≤ 2 ∧ (∀ a5 ∈ insert pz5 P5, ∀ m5 ∈ Y5, ¬ I a5 m5) ∧ (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val ∈ P5.image pw ∪ Y5.image lw)))).getD ((n + Mg e)) false = true) ∧ (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)), P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧ (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) : A.card ≤ 4 * C.size := by
  classical
  have K2 : ∀ e ∈ A, ∀ e' ∈ A, Rr n C (n + S e) (m2 e') → I e'.1 e.2 := by
    intro e he e' he' hR
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdS⟩ := hA e he
    obtain ⟨_, _, _, _, _, _, _, _, _, hout2, _, _, _⟩ := hA e' he'
    exact keyK n N M pw lw I C hC hpn hS (n + S e) (m2 e') e'.1 e.2 hR hout2 hdS
  have K1 : ∀ e ∈ A, ∀ e' ∈ A, Rr n C (n + Mg e) (m e') → I e'.1 e.2 := by
    intro e he e' he' hR
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hdM, _⟩ := hA e he
    obtain ⟨_, _, _, _, _, _, _, _, hout1, _, _, _, _⟩ := hA e' he'
    exact keyK n N M pw lw I C hC hpn hS (n + Mg e) (m e') e'.1 e.2 hR hout1 hdM
  have hpair : ∀ e ∈ A, ∀ e' ∈ A, m2 e = m2 e' → e.1 ≠ e'.1 → e.2 = e'.2 := by
    intro e he e' he' hb hne
    by_contra hl
    obtain ⟨hI1, _, _, _, _, _, _, hSm, _⟩ := hA e he
    obtain ⟨hI2, _, _, _, _, _, _, hSm', _⟩ := hA e' he'
    have i2 : I e'.1 e.2 := K2 e he e' he' (by rw [← hb]; exact hSm)
    have i3 : I e.1 e'.2 := K2 e' he' e he (by rw [hb]; exact hSm')
    exact h4 e.1 e'.1 e.2 e'.2 hne hl ⟨hI1, i2, i3, hI2⟩
  obtain ⟨A1, hA1⟩ : ∃ A1 : Finset (Fin N × Fin M), ∀ e, e ∈ A1 ↔
      (e ∈ A ∧ ∀ e' ∈ A, m2 e' = m2 e → e'.1 = e.1) :=
    ⟨A.filter (fun e => ∀ e' ∈ A, m2 e' = m2 e → e'.1 = e.1), fun e => Finset.mem_filter⟩
  have hA1sub : A1 ⊆ A := fun e he => ((hA1 e).1 he).1
  have hA2 : ∀ e ∈ A \ A1, e ∈ A ∧ ∃ e' ∈ A, m2 e' = m2 e ∧ e'.1 ≠ e.1 := by
    intro e he
    obtain ⟨heA, hn⟩ := Finset.mem_sdiff.1 he
    refine ⟨heA, ?_⟩
    by_contra hcon
    apply hn
    refine (hA1 e).2 ⟨heA, fun e' he' hb => ?_⟩
    by_contra h2
    exact hcon ⟨e', he', hb, h2⟩
  have hline : ∀ e1 ∈ A \ A1, ∀ e2 ∈ A \ A1, m2 e1 = m2 e2 → e1.2 = e2.2 := by
    intro e1 he1 e2 he2 hb
    obtain ⟨he1A, e', he', hb', hne'⟩ := hA2 e1 he1
    obtain ⟨he2A, _⟩ := hA2 e2 he2
    by_cases hp : e1.1 = e2.1
    · have t1 : e1.2 = e'.2 := hpair e1 he1A e' he' hb'.symm (Ne.symm hne')
      have t2 : e2.2 = e'.2 := hpair e2 he2A e' he' (hb.symm.trans hb'.symm)
        (fun h => hne' (h.symm.trans hp.symm))
      exact t1.trans t2.symm
    · exact hpair e1 he1A e2 he2A hb hp
  have L2 := layer n N M I C hC h4 A1 m2 S
    (fun e he => by
      obtain ⟨_, _, _, _, _, ⟨o, hlt, hop, _⟩, _⟩ := hA e ((hA1 e).1 he).1
      exact ⟨hlt, hop⟩)
    (fun e he => by
      obtain ⟨_, _, _, _, _, _, _, hSm, _⟩ := hA e ((hA1 e).1 he).1
      exact hSm)
    (by
      intro w
      refine two_lab (A1.filter (fun e => n + S e = w)) Sy Prod.snd
        ((gateAt C (w - n)).inputs.getD 0 0) ((gateAt C (w - n)).inputs.getD 1 0) ?_ ?_
      · intro e he e' he' hk
        have heA := ((hA1 e).1 (Finset.mem_filter.1 he).1).1
        have heA' := ((hA1 e').1 (Finset.mem_filter.1 he').1).1
        obtain ⟨_, _, _, _, _, _, hSy, _⟩ := hA e heA
        obtain ⟨_, _, _, _, _, _, hSy', _⟩ := hA e' heA'
        rw [hk] at hSy
        exact Set.singleton_injective (hSy.symm.trans hSy')
      · intro e he
        have heA := ((hA1 e).1 (Finset.mem_filter.1 he).1).1
        have hw : S e = w - n := by
          have := (Finset.mem_filter.1 he).2
          omega
        obtain ⟨_, _, _, _, _, ⟨o, _, _, hsl⟩, _⟩ := hA e heA
        rw [hw] at hsl
        rcases hsl with ⟨h0, _⟩ | ⟨_, h1⟩
        · exact Or.inl h0.symm
        · exact Or.inr h1.symm)
    (fun e he e' he' hR => K2 e ((hA1 e).1 he).1 e' ((hA1 e').1 he').1 hR)
  have L1 := layer n N M I C hC h4 (A \ A1) m Mg
    (fun e he => by
      obtain ⟨_, _, _, ⟨hlt, hop, _⟩, _⟩ := hA e (Finset.mem_sdiff.1 he).1
      exact ⟨hlt, hop⟩)
    (fun e he => by
      obtain ⟨_, _, _, _, hMm, _⟩ := hA e (Finset.mem_sdiff.1 he).1
      exact hMm)
    (by
      intro w
      refine two_lab ((A \ A1).filter (fun e => n + Mg e = w)) m2 Prod.snd
        ((gateAt C (w - n)).inputs.getD 0 0) ((gateAt C (w - n)).inputs.getD 1 0) ?_ ?_
      · intro e he e' he' hk
        exact hline e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1 hk
      · intro e he
        have heA := (Finset.mem_sdiff.1 (Finset.mem_filter.1 he).1).1
        have hw : Mg e = w - n := by
          have := (Finset.mem_filter.1 he).2
          omega
        obtain ⟨_, _, _, ⟨_, _, hsl⟩, _⟩ := hA e heA
        rw [hw] at hsl
        rcases hsl with ⟨_, h1⟩ | ⟨h0, _⟩
        · exact Or.inr h1.symm
        · exact Or.inl h0.symm)
    (fun e he e' he' hR => K1 e (Finset.mem_sdiff.1 he).1 e' (Finset.mem_sdiff.1 he').1 hR)
  have R2 : (A1.image (fun e => (e.1, m2 e))).card ≤
      (A1.image (fun e => (Mg e, decide ((gateAt C (Mg e)).inputs.getD 0 0 = m2 e)))).card := by
    apply img_le
    intro e he e' he' hs
    have heA := ((hA1 e).1 he).1
    have heA' := ((hA1 e').1 he').1
    have hg : Mg e = Mg e' := congrArg Prod.fst hs
    have hf := decide_eq_decide.1 (congrArg Prod.snd hs)
    obtain ⟨_, _, _, ⟨_, _, hsl⟩, _⟩ := hA e heA
    obtain ⟨_, _, _, ⟨_, _, hsl'⟩, _⟩ := hA e' heA'
    rw [← hg] at hsl' hf
    have hm := (slot_eq _ _ (m2 e) (d e) (m2 e') (d e') hsl.symm hsl'.symm hf).1
    exact Prod.ext (((hA1 e').1 he').2 e heA hm) hm
  have R1 : ((A \ A1).image (fun e => (e.1, m e))).card ≤
      ((A \ A1).image (fun e => (Rd e, decide ((gateAt C (Rd e)).inputs.getD 0 0 = G e)))).card := by
    apply img_le
    intro e he e' he' hs
    have heA := (Finset.mem_sdiff.1 he).1
    have heA' := (Finset.mem_sdiff.1 he').1
    have hg : Rd e = Rd e' := congrArg Prod.fst hs
    have hf := decide_eq_decide.1 (congrArg Prod.snd hs)
    obtain ⟨_, ⟨_, _, hsl⟩, hG, _⟩ := hA e heA
    obtain ⟨_, ⟨_, _, hsl'⟩, hG', _⟩ := hA e' heA'
    rw [← hg] at hsl' hf
    obtain ⟨hGG, hmm⟩ := slot_eq _ _ (G e) (m e) (G e') (m e') hsl hsl' hf
    rw [hGG] at hG
    exact Prod.ext (Set.singleton_injective (hG.symm.trans hG')) hmm
  have hdisj : (A1.image (fun e => (Mg e, decide ((gateAt C (Mg e)).inputs.getD 0 0 = m2 e)))) ∩
      ((A \ A1).image (fun e => (Rd e, decide ((gateAt C (Rd e)).inputs.getD 0 0 = G e)))) = ∅ := by
    apply Finset.disjoint_iff_inter_eq_empty.1
    apply Finset.disjoint_left.2
    intro x hx hx'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨e', he', hs⟩ := Finset.mem_image.1 hx'
    have heA := ((hA1 e).1 he).1
    have heA' := (Finset.mem_sdiff.1 he').1
    have hg : Rd e' = Mg e := congrArg Prod.fst hs
    have hf := decide_eq_decide.1 (congrArg Prod.snd hs)
    obtain ⟨_, _, _, ⟨_, _, hsl⟩, _, _, _, _, _, hout2, _⟩ := hA e heA
    obtain ⟨_, ⟨_, _, hsl'⟩, hG', _⟩ := hA e' heA'
    rw [hg] at hsl' hf
    have hGm := (slot_eq _ _ (G e') (m e') (m2 e) (d e) hsl' hsl.symm hf).1
    have hreach : Rr n C (pw e'.1) (G e') := by
      have hmem : e'.1 ∈ {x1 : Fin N | Rr n C (pw x1) (G e')} := by
        rw [hG']
        exact rfl
      exact hmem
    rw [hGm] at hreach
    exact clash n N M pw lw I C hpn hS e'.1 e.1 (m2 e) hreach hout2
  have hTsub : (A1.image (fun e => (Mg e, decide ((gateAt C (Mg e)).inputs.getD 0 0 = m2 e)))) ∪
      ((A \ A1).image (fun e => (Rd e, decide ((gateAt C (Rd e)).inputs.getD 0 0 = G e)))) ⊆
      ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)) ×ˢ
        (Finset.univ : Finset Bool) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨_, _, _, ⟨hlt, hop, _⟩, _⟩ := hA e ((hA1 e).1 he).1
      exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hop⟩, Finset.mem_univ _⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨_, ⟨hlt, hop, _⟩, _⟩ := hA e (Finset.mem_sdiff.1 he).1
      exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hop⟩, Finset.mem_univ _⟩
  have hc1 := Finset.card_union_add_card_inter
    (A1.image (fun e => (Mg e, decide ((gateAt C (Mg e)).inputs.getD 0 0 = m2 e))))
    ((A \ A1).image (fun e => (Rd e, decide ((gateAt C (Rd e)).inputs.getD 0 0 = G e))))
  rw [hdisj, Finset.card_empty] at hc1
  have hc2 := Finset.card_le_card hTsub
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc2
  have hOR : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard =
      ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp
  have hAO := two_filters C.gates.length (fun j => (gateAt C j).op = GateOp.and)
    (fun j => (gateAt C j).op = GateOp.or) (fun j h1 h2 => by
      rw [h1] at h2
      cases h2)
  have hsplit := Finset.card_sdiff_add_card_eq_card hA1sub
  show A.card ≤ 4 * C.gates.length
  omega

end PEqualNP.Outside.L_meta_2414

theorem PEqualNP.Outside.L_meta_2414 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)) (Rd G m Mg d m2 S Sy : Fin N × Fin M → ℕ), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧ {x1 : Fin N | R (pw x1) (G e)} = {e.1} ∧ ((Mg e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (d e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (m2 e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (m2 e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (d e)))) ∧ R (n + Mg e) (m e) ∧ (∃ o : ℕ, ((S e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = o) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = o ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧ {y2 : Fin M | R (lw y2) (Sy e)} = {e.2} ∧ R (n + S e) (m2 e) ∧ (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) → (C.wires (List.ofFn z3)).getD ((m e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z3 = true) ∧ (∀ z4 : Fin n → Bool, (∃ h4 : pw e.1 < n, z4 ⟨pw e.1, h4⟩ = true) → (C.wires (List.ofFn z4)).getD ((m2 e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z4 = true) ∧ (C.wires (List.ofFn (fun k7 : Fin n => decide (k7.val = pw e.1)))).getD ((d e)) false = true ∧ (∀ pz5 : Fin N, ¬ I pz5 e.2 → ∃ (P5 : Finset (Fin N)) (Y5 : Finset (Fin M)), P5.card ≤ 1 ∧ Y5.card ≤ 2 ∧ (∀ a5 ∈ insert pz5 P5, ∀ m5 ∈ Y5, ¬ I a5 m5) ∧ (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val ∈ P5.image pw ∪ Y5.image lw)))).getD ((n + Mg e)) false = true) ∧ (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)), P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧ (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) → A.card ≤ 4 * C.size := by
  intro n N M pw lw I C A Rd G m Mg d m2 S Sy hC _ _ _ hpn _ h4 hS R hR hA
  subst hR
  exact PEqualNP.Outside.L_meta_2414.main n N M pw lw I C A Rd G m Mg d m2 S Sy hC hpn h4 hS hA
