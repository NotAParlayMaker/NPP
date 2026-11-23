import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1375

open PEqualNP.CircuitLowerBounds

def pt {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def ind {n : ℕ} (F : Finset (Fin n)) : Fin n → Bool := fun q => decide (q ∈ F)

def Tset {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val (pt p) w = true)

def GateOK {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (t : ℕ) : Prop :=
  (∀ x, val x t = false) ∨ (∀ x, val x t = true) ∨ ∃ a b, a < t ∧ b < t ∧
    ((∀ x, val x t = (val x a && val x b)) ∨ (∀ x, val x t = (val x a || val x b)))

def Priv {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S S0 : Finset (Fin n)) (w : ℕ) : Prop :=
  Tset val w \ S0 ⊆ S ∧
    (2 ≤ (Tset val w \ S0).card ∨ (Tset val w ⊆ S ∧ 2 ≤ (Tset val w).card))

def Cov {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (L : Finset ℕ) (w : ℕ) : Prop :=
  ∀ p ∈ Tset val w, ∃ l ∈ L, p ∈ Tset val l

def Pp {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S0 F : Finset (Fin n)) (L : Finset ℕ)
    (w : ℕ) : Prop :=
  F = ∅ → ∀ l ∈ L, ∀ c ∈ Tset val l, c ∉ S0 → c ∈ Tset val w →
    (∀ l' ∈ L, c ∈ Tset val l' → l' = l) → ∀ p ∈ Tset val l, p ∈ S0 → p ∈ Tset val w

def Stat {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S0 F : Finset (Fin n)) (L : Finset ℕ)
    (w : ℕ) : Prop :=
  val (ind F) w = true ∨ (Cov val L w ∧ Pp val S0 F L w)

lemma mem_Tset {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (w : ℕ) (p : Fin n) :
    p ∈ Tset val w ↔ val (pt p) w = true := by
  simp [Tset]

lemma mono {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (hg : ∀ t, n ≤ t → GateOK val t) :
    ∀ w x y, (∀ q, x q = true → y q = true) → val x w = true → val y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro x y hxy hx
    by_cases hw : w < n
    · have h1 := hin x ⟨w, hw⟩
      have h2 := hin y ⟨w, hw⟩
      simp only at h1 h2
      rw [h2]
      rw [h1] at hx
      exact hxy _ hx
    · rcases hg w (not_lt.mp hw) with h0 | h1 | ⟨a, b, ha, hb, h | h⟩
      · rw [h0] at hx
        exact absurd hx (by simp)
      · exact h1 y
      · rw [h] at hx
        rw [h]
        simp only [Bool.and_eq_true] at hx ⊢
        exact ⟨ih a ha x y hxy hx.1, ih b hb x y hxy hx.2⟩
      · rw [h] at hx
        rw [h]
        simp only [Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (ih a ha x y hxy hx)
        · exact Or.inr (ih b hb x y hxy hx)

lemma tset_input {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (w : ℕ) (hw : w < n) :
    (Tset val w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_Tset] at ha hb
  have h1 := hin (pt a) ⟨w, hw⟩
  have h2 := hin (pt b) ⟨w, hw⟩
  simp only at h1 h2
  rw [h1] at ha
  rw [h2] at hb
  simp only [pt, decide_eq_true_eq] at ha hb
  rw [← ha, ← hb]

lemma ind_empty_le {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hmono : ∀ w x y, (∀ q, x q = true → y q = true) → val x w = true → val y w = true)
    (w : ℕ) (h : val (ind (∅ : Finset (Fin n))) w = true) (p : Fin n) :
    p ∈ Tset val w := by
  rw [mem_Tset]
  refine hmono w _ _ ?_ h
  intro q hq
  simp [ind] at hq

lemma stat_mono {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hmono : ∀ w x y, (∀ q, x q = true → y q = true) → val x w = true → val y w = true)
    (S0 F F' : Finset (Fin n)) (L L' : Finset ℕ) (w : ℕ) (hF : F ⊆ F') (hL : L ⊆ L')
    (h : Stat val S0 F L w) : Stat val S0 F' L' w := by
  rcases h with h | ⟨hc, hp⟩
  · left
    refine hmono w _ _ ?_ h
    intro q hq
    simp only [ind, decide_eq_true_eq] at hq ⊢
    exact hF hq
  · right
    refine ⟨fun p hpw => ?_, ?_⟩
    · obtain ⟨l, hl, hpl⟩ := hc p hpw
      exact ⟨l, hL hl, hpl⟩
    · intro hF' l hl c hcl hc0 hcw huniq p hpl hp0
      have hFe : F = ∅ := Finset.subset_empty.mp (hF' ▸ hF)
      obtain ⟨l0, hl0, hcl0⟩ := hc c hcw
      have hll : l0 = l := huniq l0 (hL hl0) hcl0
      rw [hll] at hl0
      exact hp hFe l hl0 c hcl hc0 hcw (fun l' hl' hcl' => huniq l' (hL hl') hcl') p hpl hp0

lemma pp_part {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hmono : ∀ w x y, (∀ q, x q = true → y q = true) → val x w = true → val y w = true)
    (S0 F : Finset (Fin n)) (L : Finset ℕ) (w : ℕ) (h : Stat val S0 F L w) (hF : F = ∅)
    (l : ℕ) (hl : l ∈ L) (c : Fin n) (hcl : c ∈ Tset val l) (hc0 : c ∉ S0)
    (hcw : c ∈ Tset val w) (huniq : ∀ l' ∈ L, c ∈ Tset val l' → l' = l)
    (p : Fin n) (hpl : p ∈ Tset val l) (hp0 : p ∈ S0) : p ∈ Tset val w := by
  rcases h with h | ⟨_, hp⟩
  · rw [hF] at h
    exact ind_empty_le val hmono w h p
  · exact hp hF l hl c hcl hc0 hcw huniq p hpl hp0

lemma and_stat {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hmono : ∀ w x y, (∀ q, x q = true → y q = true) → val x w = true → val y w = true)
    (S0 F : Finset (Fin n)) (L : Finset ℕ) (t a b : ℕ)
    (h : ∀ x, val x t = (val x a && val x b))
    (ha : Stat val S0 F L a) (hb : Stat val S0 F L b) : Stat val S0 F L t := by
  have hT : ∀ p, p ∈ Tset val t ↔ p ∈ Tset val a ∧ p ∈ Tset val b := by
    intro p
    simp only [mem_Tset]
    rw [h]
    simp
  have hcov : Cov val L a ∨ Cov val L b → Stat val S0 F L t := by
    intro hc
    right
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases hc with hc | hc
      · exact hc p ((hT p).mp hp).1
      · exact hc p ((hT p).mp hp).2
    · intro hF l hl c hcl hc0 hcw huniq p hpl hp0
      rw [hT] at hcw ⊢
      exact ⟨pp_part val hmono S0 F L a ha hF l hl c hcl hc0 hcw.1 huniq p hpl hp0,
        pp_part val hmono S0 F L b hb hF l hl c hcl hc0 hcw.2 huniq p hpl hp0⟩
  rcases ha with ha1 | ha2
  · rcases hb with hb1 | hb2
    · left
      rw [h, ha1, hb1]
      rfl
    · exact hcov (Or.inr hb2.1)
  · exact hcov (Or.inl ha2.1)

lemma or_stat {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (S0 F : Finset (Fin n)) (L : Finset ℕ) (t a b : ℕ)
    (h : ∀ x, val x t = (val x a || val x b))
    (ha : Stat val S0 F L a) (hb : Stat val S0 F L b) : Stat val S0 F L t := by
  have hT : ∀ p, p ∈ Tset val t ↔ p ∈ Tset val a ∨ p ∈ Tset val b := by
    intro p
    simp only [mem_Tset]
    rw [h]
    simp
  rcases ha with ha1 | ha2
  · left
    rw [h, ha1]
    rfl
  · rcases hb with hb1 | hb2
    · left
      rw [h, hb1]
      simp
    · right
      refine ⟨fun p hp => ?_, ?_⟩
      · rcases (hT p).mp hp with hp | hp
        · exact ha2.1 p hp
        · exact hb2.1 p hp
      · intro hF l hl c hcl hc0 hcw huniq p hpl hp0
        rw [hT] at hcw ⊢
        rcases hcw with hcw | hcw
        · exact Or.inl (ha2.2 hF l hl c hcl hc0 hcw huniq p hpl hp0)
        · exact Or.inr (hb2.2 hF l hl c hcl hc0 hcw huniq p hpl hp0)

open Classical in
lemma core {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hmono : ∀ w x y, (∀ q, x q = true → y q = true) → val x w = true → val y w = true)
    (hg : ∀ t, n ≤ t → GateOK val t) (hsmall : ∀ t, t < n → (Tset val t).card ≤ 1)
    (S S0 : Finset (Fin n)) :
    ∀ t, ∀ W : Finset ℕ, W ⊆ Finset.range t →
      ∃ (F : Finset (Fin n)) (L : Finset ℕ), Disjoint F S ∧ Disjoint F S0 ∧
        F.card + L.card ≤ W.card + ((Finset.range t).filter (fun w => Priv val S S0 w)).card ∧
        (∀ l ∈ L, Tset val l \ S0 ⊆ S ∧ ¬ Priv val S S0 l) ∧
        ∀ w ∈ W, Stat val S0 F L w := by
  intro t
  induction t with
  | zero =>
    intro W hW
    refine ⟨∅, ∅, by simp, by simp, by simp, by simp, ?_⟩
    intro w hw
    have := hW hw
    simp at this
  | succ t ih =>
    intro W hW
    have hcnt : ((Finset.range t).filter (fun w => Priv val S S0 w)).card ≤
        ((Finset.range (t + 1)).filter (fun w => Priv val S S0 w)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_succ t)))
    by_cases htW : t ∈ W
    swap
    · have hW' : W ⊆ Finset.range t := by
        intro w hw
        have h1 := hW hw
        rw [Finset.mem_range] at h1 ⊢
        have : w ≠ t := by
          rintro rfl
          exact htW hw
        omega
      obtain ⟨F, L, hd, hd0, hc, hleaf, hall⟩ := ih W hW'
      exact ⟨F, L, hd, hd0, by omega, hleaf, hall⟩
    · have hW0 : W.erase t ⊆ Finset.range t := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have h1 := hW hw.2
        rw [Finset.mem_range] at h1 ⊢
        have := hw.1
        omega
      have hW0c : (W.erase t).card + 1 = W.card := Finset.card_erase_add_one htW
      by_cases hpriv : Priv val S S0 t
      · have hfc : ((Finset.range (t + 1)).filter (fun w => Priv val S S0 w)).card =
            ((Finset.range t).filter (fun w => Priv val S S0 w)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left_of_eq_true _ _ (eq_true hpriv),
            Finset.card_insert_of_notMem (by simp)]
        have h2 : 2 ≤ (Tset val t).card := by
          rcases hpriv.2 with h | h
          · exact h.trans (Finset.card_le_card Finset.sdiff_subset)
          · exact h.2
        have hnt : n ≤ t := by
          by_contra hlt
          have := hsmall t (not_le.mp hlt)
          omega
        rcases hg t hnt with h0 | h1 | ⟨a, b, ha, hb, hop⟩
        · exfalso
          have hE : Tset val t = ∅ := by
            ext p
            simp [mem_Tset, h0]
          rw [hE] at h2
          simp at h2
        · obtain ⟨F, L, hd, hd0, hc, hleaf, hall⟩ := ih _ hW0
          refine ⟨F, L, hd, hd0, by omega, hleaf, ?_⟩
          intro w hw
          by_cases hwt : w = t
          · rw [hwt]
            exact Or.inl (h1 _)
          · exact hall w (Finset.mem_erase.mpr ⟨hwt, hw⟩)
        · have hsub : insert a (insert b (W.erase t)) ⊆ Finset.range t := by
            intro w hw
            rw [Finset.mem_insert, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact Finset.mem_range.mpr ha
            · exact Finset.mem_range.mpr hb
            · exact hW0 hw
          obtain ⟨F, L, hd, hd0, hc, hleaf, hall⟩ := ih _ hsub
          have hcard : (insert a (insert b (W.erase t))).card ≤ (W.erase t).card + 2 := by
            have h1 := Finset.card_insert_le a (insert b (W.erase t))
            have h2 := Finset.card_insert_le b (W.erase t)
            omega
          refine ⟨F, L, hd, hd0, by omega, hleaf, ?_⟩
          intro w hw
          by_cases hwt : w = t
          · rw [hwt]
            have ha' := hall a (by simp)
            have hb' := hall b (by simp)
            rcases hop with h | h
            · exact and_stat val hmono S0 F L t a b h ha' hb'
            · exact or_stat val S0 F L t a b h ha' hb'
          · refine hall w ?_
            rw [Finset.mem_insert, Finset.mem_insert]
            exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hwt, hw⟩))
      · obtain ⟨F, L, hd, hd0, hc, hleaf, hall⟩ := ih _ hW0
        by_cases hsub : Tset val t \ S0 ⊆ S
        · refine ⟨F, insert t L, hd, hd0, ?_, ?_, ?_⟩
          · have := Finset.card_insert_le t L
            omega
          · intro l hl
            rw [Finset.mem_insert] at hl
            rcases hl with rfl | hl
            · exact ⟨hsub, hpriv⟩
            · exact hleaf l hl
          · intro w hw
            by_cases hwt : w = t
            · rw [hwt]
              right
              refine ⟨fun p hp => ⟨t, Finset.mem_insert_self t L, hp⟩, ?_⟩
              intro _ l _ c _ _ hcw huniq p hpl _
              have := huniq t (Finset.mem_insert_self t L) hcw
              rw [this]
              exact hpl
            · exact stat_mono val hmono S0 F F L (insert t L) w (Finset.Subset.refl F)
                (Finset.subset_insert t L) (hall w (Finset.mem_erase.mpr ⟨hwt, hw⟩))
        · obtain ⟨p, hpT, hpS⟩ := Finset.not_subset.mp hsub
          rw [Finset.mem_sdiff] at hpT
          have hpv : val (pt p) t = true := (mem_Tset val t p).mp hpT.1
          refine ⟨insert p F, L, ?_, ?_, ?_, hleaf, ?_⟩
          · rw [Finset.disjoint_insert_left]
            exact ⟨hpS, hd⟩
          · rw [Finset.disjoint_insert_left]
            exact ⟨hpT.2, hd0⟩
          · have := Finset.card_insert_le p F
            omega
          · intro w hw
            by_cases hwt : w = t
            · left
              rw [hwt]
              refine hmono t (pt p) (ind (insert p F)) ?_ hpv
              intro q hq
              simp only [pt, ind, decide_eq_true_eq, Finset.mem_insert] at hq ⊢
              exact Or.inl hq
            · exact stat_mono val hmono S0 F (insert p F) L L w (Finset.subset_insert p F)
                (Finset.Subset.refl L) (hall w (Finset.mem_erase.mpr ⟨hwt, hw⟩))

lemma cover_card {n : ℕ} (A : Finset (Fin n)) (L : Finset ℕ) (G : ℕ → Finset (Fin n))
    (hG : ∀ l ∈ L, (G l).card ≤ 1) (hA : A ⊆ L.biUnion G) : A.card ≤ L.card := by
  calc A.card ≤ (L.biUnion G).card := Finset.card_le_card hA
    _ ≤ ∑ l ∈ L, (G l).card := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ L, 1 := Finset.sum_le_sum hG
    _ = L.card := by simp

lemma fold_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp
    omega

lemma fold_prefix (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons]
    exact (List.prefix_append w _).trans (ih _)

lemma getD_prefix {w l : List Bool} (h : w <+: l) {i : ℕ} (hi : i < w.length) :
    l.getD i false = w.getD i false := by
  obtain ⟨r, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length :=
  fold_len C.gates x

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = (C.gates[j]).op.eval
      ((C.gates[j]).inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hpl : ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + j := by
    rw [fold_len, List.length_take, min_eq_left hj.le]
  have hfull : C.wires x = (C.gates.drop (j + 1)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)]) := by
    conv_lhs => rw [Circuit.wires, hsplit, List.foldl_append, List.foldl_cons]
  have hp1 := fold_prefix (C.gates.drop (j + 1)) (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)])
  rw [← hfull] at hp1
  have hp0 := (List.prefix_append _ _).trans hp1
  rw [getD_prefix hp1 (by rw [List.length_append, hpl]; simp)]
  rw [← hpl, List.getD_append_right _ _ _ _ le_rfl]
  simp only [Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · rw [hpl, ite_eq_left_of_eq_true _ _ (eq_true hi)]
    exact (getD_prefix hp0 (by rw [hpl]; exact hi)).symm
  · rw [hpl, ite_eq_right_of_eq_false _ _ (eq_false hi)]
    exact List.getD_eq_default _ _ (by rw [hpl]; omega)

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_prefix (fold_prefix C.gates x) hi

open Classical in
lemma main (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m)
    (hSc : ∀ i : Fin m, (S i).card = q + 1)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hprom : ∀ (w : Fin m) (x : Fin n → Bool),
      ((∀ v ∈ S i0, x v = false) ∨ (∃ p ∈ S i0, ∀ v : Fin n, x v = decide (v = p))) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    m * q ≤ gates.length := by
  set C : Circuit := ⟨gates, 0⟩ with hC
  set val : (Fin n → Bool) → ℕ → Bool := fun x w => (C.wires (List.ofFn x)).getD w false
    with hval
  have hCg : C.gates = gates := rfl
  have hin : ∀ x (i : Fin n), val x i = x i := by
    intro x i
    simp only [hval]
    rw [wires_input C _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have hdead : ∀ x t, n + gates.length ≤ t → val x t = false := by
    intro x t ht
    simp only [hval]
    exact List.getD_eq_default _ _ (by rw [wires_len]; simpa using ht)
  have hg : ∀ t, n ≤ t → GateOK val t := by
    intro t ht
    by_cases htG : n + gates.length ≤ t
    · exact Or.inl (fun x => hdead x t htG)
    · have hj : t - n < gates.length := by omega
      obtain ⟨hop, hlen⟩ := hgates _ (List.getElem_mem hj)
      have key : ∀ x, val x t = (gates[t - n]).op.eval
          ((gates[t - n]).inputs.map fun i => if i < t then val x i else false) := by
        intro x
        have h := wires_gate C (List.ofFn x) (t - n) hj
        simp only [List.length_ofFn] at h
        have e : n + (t - n) = t := by omega
        rw [e] at h
        exact h
      rcases hinp : (gates[t - n]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
      · rw [hinp] at key
        rcases hop with hop | hop
        · exact Or.inr (Or.inl (fun x => by rw [key x, hop]; simp [GateOp.eval]))
        · exact Or.inl (fun x => by rw [key x, hop]; simp [GateOp.eval])
      · rw [hinp] at key
        by_cases ha : a < t
        · refine Or.inr (Or.inr ⟨a, a, ha, ha, Or.inr (fun x => ?_)⟩)
          rw [key x]
          rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha]
        · refine Or.inl (fun x => ?_)
          rw [key x]
          rcases hop with hop | hop <;> simp [hop, GateOp.eval, ha]
      · rw [hinp] at key
        by_cases ha : a < t <;> by_cases hb : b < t <;> rcases hop with hop | hop
        · exact Or.inr (Or.inr ⟨a, b, ha, hb, Or.inl (fun x => by
            rw [key x]; simp [hop, GateOp.eval, ha, hb])⟩)
        · exact Or.inr (Or.inr ⟨a, b, ha, hb, Or.inr (fun x => by
            rw [key x]; simp [hop, GateOp.eval, ha, hb])⟩)
        · exact Or.inl (fun x => by rw [key x]; simp [hop, GateOp.eval, ha, hb])
        · exact Or.inr (Or.inr ⟨a, a, ha, ha, Or.inr (fun x => by
            rw [key x]; simp [hop, GateOp.eval, ha, hb])⟩)
        · exact Or.inl (fun x => by rw [key x]; simp [hop, GateOp.eval, ha, hb])
        · exact Or.inr (Or.inr ⟨b, b, hb, hb, Or.inr (fun x => by
            rw [key x]; simp [hop, GateOp.eval, ha, hb])⟩)
        · exact Or.inl (fun x => by rw [key x]; simp [hop, GateOp.eval, ha, hb])
        · exact Or.inl (fun x => by rw [key x]; simp [hop, GateOp.eval, ha, hb])
      · rw [hinp] at hlen
        simp at hlen
  have hmono := mono val hin hg
  have hsmall : ∀ t, t < n → (Tset val t).card ≤ 1 := fun t ht => tset_input val hin t ht
  have hev : ∀ (w : Fin m) (x : Fin n → Bool),
      ((∀ v ∈ S i0, x v = false) ∨ (∃ p ∈ S i0, ∀ v : Fin n, x v = decide (v = p))) →
      val x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x hx => hprom w x hx
  have hT : ∀ i : Fin m, Tset val (out i) = S i := by
    intro i
    ext p
    rw [mem_Tset]
    have hx : (∀ v ∈ S i0, pt p v = false) ∨ (∃ p' ∈ S i0, ∀ v : Fin n, pt p v = decide (v = p')) := by
      by_cases hp : p ∈ S i0
      · exact Or.inr ⟨p, hp, fun v => rfl⟩
      · left
        intro v hv
        simp only [pt, decide_eq_false_iff_not]
        rintro rfl
        exact hp hv
    rw [hev i (pt p) hx]
    simp [pt]
  have hfalse : ∀ (i : Fin m) (F : Finset (Fin n)), Disjoint F (S i) → Disjoint F (S i0) →
      val (ind F) (out i) = false := by
    intro i F hd hd0
    rw [hev i (ind F) (Or.inl (fun v hv => by
      simp only [ind, decide_eq_false_iff_not]
      exact fun hvF => Finset.disjoint_left.mp hd0 hvF hv))]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv
    simp only [ind, decide_eq_true_eq]
    exact fun hvF => Finset.disjoint_left.mp hd hvF hv
  have hbound : ∀ i : Fin m, q ≤ ((Finset.Ico n (n + gates.length)).filter
      (fun w => Priv val (S i) (S i0) w)).card := by
    intro i
    obtain ⟨F, L, hd, hd0, hc, hleaf, hall⟩ :=
      core val hmono hg hsmall (S i) (S i0) (out i + 1) {out i} (by simp)
    have hle : ((Finset.range (out i + 1)).filter (fun w => Priv val (S i) (S i0) w)).card ≤
        ((Finset.Ico n (n + gates.length)).filter (fun w => Priv val (S i) (S i0) w)).card := by
      apply Finset.card_le_card
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨?_, hw.2⟩
      have h2 : 2 ≤ (Tset val w).card := by
        rcases hw.2.2 with h | h
        · exact h.trans (Finset.card_le_card Finset.sdiff_subset)
        · exact h.2
      rw [Finset.mem_Ico]
      constructor
      · by_contra hlt
        have := hsmall w (not_le.mp hlt)
        omega
      · by_contra hge
        have hE : Tset val w = ∅ := by
          ext p
          simp [mem_Tset, hdead _ w (not_lt.mp hge)]
        rw [hE] at h2
        simp at h2
    rw [Finset.card_singleton] at hc
    have hkey : q + 1 ≤ F.card + L.card := by
      rcases hall (out i) (by simp) with h | ⟨hcov, hpp⟩
      · rw [hfalse i F hd hd0] at h
        exact absurd h (by simp)
      · have hcov' : ∀ p ∈ S i, ∃ l ∈ L, p ∈ Tset val l := by
          intro p hp
          exact hcov p (by rw [hT]; exact hp)
        have hG1 : ∀ l ∈ L, (Tset val l \ S i0).card ≤ 1 := by
          intro l hl
          by_contra hgt
          exact (hleaf l hl).2 ⟨(hleaf l hl).1, Or.inl (by omega)⟩
        by_cases hi : S i = S i0
        · have hG : ∀ l ∈ L, (Tset val l).card ≤ 1 := by
            intro l hl
            have hsub := (hleaf l hl).1
            have hin0 : Tset val l ⊆ S i := by
              intro p hp
              by_contra hpS
              have : p ∈ Tset val l \ S i0 := Finset.mem_sdiff.mpr ⟨hp, by rw [← hi]; exact hpS⟩
              exact hpS (hsub this)
            by_contra hgt
            exact (hleaf l hl).2 ⟨hsub, Or.inr ⟨hin0, by omega⟩⟩
          have hA : S i ⊆ L.biUnion (fun l => Tset val l) := by
            intro p hp
            obtain ⟨l, hl, hpl⟩ := hcov' p hp
            exact Finset.mem_biUnion.mpr ⟨l, hl, hpl⟩
          have := cover_card (S i) L (fun l => Tset val l) hG hA
          have := hSc i
          omega
        · have hne : i ≠ i0 := by
            rintro rfl
            exact hi rfl
          have hcap := hS i i0 hne
          have hsd := Finset.card_sdiff_add_card_inter (S i) (S i0)
          have hSi := hSc i
          have hA : ∀ L' : Finset ℕ, (∀ p ∈ S i \ S i0, ∃ l ∈ L', p ∈ Tset val l) →
              L' ⊆ L → (S i \ S i0).card ≤ L'.card := by
            intro L' hc' hsub
            refine cover_card (S i \ S i0) L' (fun l => Tset val l \ S i0)
              (fun l hl => hG1 l (hsub hl)) ?_
            intro p hp
            obtain ⟨l, hl, hpl⟩ := hc' p hp
            exact Finset.mem_biUnion.mpr ⟨l, hl,
              Finset.mem_sdiff.mpr ⟨hpl, (Finset.mem_sdiff.mp hp).2⟩⟩
          have hAL := hA L (fun p hp => hcov' p (Finset.mem_sdiff.mp hp).1) (Finset.Subset.refl L)
          by_contra hlt
          have hF0 : F = ∅ := Finset.card_eq_zero.mp (by omega)
          have hcap1 : 0 < (S i ∩ S i0).card := by omega
          obtain ⟨pi, hpi⟩ := Finset.card_pos.mp hcap1
          rw [Finset.mem_inter] at hpi
          obtain ⟨l0, hl0, hpl0⟩ := hcov' pi hpi.1
          have herase : ∀ l1 ∈ L, (∀ p ∈ S i \ S i0, ∃ l ∈ L.erase l1, p ∈ Tset val l) → False := by
            intro l1 hl1 hc'
            have h1 := hA (L.erase l1) hc' (Finset.erase_subset l1 L)
            have h2 := Finset.card_erase_add_one hl1
            omega
          have hex : ∃ c, c ∈ Tset val l0 ∧ c ∉ S i0 := by
            by_contra hno
            refine herase l0 hl0 ?_
            intro p hp
            obtain ⟨l, hl, hpl⟩ := hcov' p (Finset.mem_sdiff.mp hp).1
            refine ⟨l, Finset.mem_erase.mpr ⟨?_, hl⟩, hpl⟩
            rintro rfl
            exact hno ⟨p, hpl, (Finset.mem_sdiff.mp hp).2⟩
          obtain ⟨c, hcl0, hc0⟩ := hex
          have hcS : c ∈ S i := (hleaf l0 hl0).1 (Finset.mem_sdiff.mpr ⟨hcl0, hc0⟩)
          have huniq : ∀ l' ∈ L, c ∈ Tset val l' → l' = l0 := by
            intro l' hl' hcl'
            by_contra hne'
            refine herase l' hl' ?_
            intro p hp
            obtain ⟨l, hl, hpl⟩ := hcov' p (Finset.mem_sdiff.mp hp).1
            by_cases hll : l = l'
            · have hpc : p = c := by
                have h1 := hG1 l' hl'
                rw [Finset.card_le_one] at h1
                exact h1 p (Finset.mem_sdiff.mpr ⟨hll ▸ hpl, (Finset.mem_sdiff.mp hp).2⟩) c
                  (Finset.mem_sdiff.mpr ⟨hcl', hc0⟩)
              rw [hpc]
              exact ⟨l0, Finset.mem_erase.mpr ⟨fun h => hne' h.symm, hl0⟩, hcl0⟩
            · exact ⟨l, Finset.mem_erase.mpr ⟨hll, hl⟩, hpl⟩
          have hP := hpp hF0 l0 hl0 c hcl0 hc0 (by rw [hT]; exact hcS) huniq
          have hsub0 : Tset val l0 ⊆ S i := by
            intro p hp
            by_cases hp0 : p ∈ S i0
            · have := hP p hp hp0
              rw [hT] at this
              exact this
            · exact (hleaf l0 hl0).1 (Finset.mem_sdiff.mpr ⟨hp, hp0⟩)
          have h2 : 2 ≤ (Tset val l0).card := by
            have : 1 < (Tset val l0).card :=
              Finset.one_lt_card.mpr ⟨c, hcl0, pi, hpl0, fun h => hc0 (h ▸ hpi.2)⟩
            omega
          exact (hleaf l0 hl0).2 ⟨(hleaf l0 hl0).1, Or.inr ⟨hsub0, h2⟩⟩
    omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint
      ((Finset.Ico n (n + gates.length)).filter (fun w => Priv val (S i) (S i0) w))
      ((Finset.Ico n (n + gates.length)).filter (fun w => Priv val (S j) (S i0) w)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    rw [Finset.mem_filter] at hwi hwj
    have h3 := hS i j hij
    rcases hwi.2.2 with h | h
    · have h1 : Tset val w \ S i0 ⊆ S i ∩ S j := Finset.subset_inter hwi.2.1 hwj.2.1
      have h2 := Finset.card_le_card h1
      omega
    · rcases hwj.2.2 with h' | h'
      · have h1 : Tset val w \ S i0 ⊆ S i ∩ S j := Finset.subset_inter hwi.2.1 hwj.2.1
        have h2 := Finset.card_le_card h1
        omega
      · have h1 : Tset val w ⊆ S i ∩ S j := Finset.subset_inter h.1 h'.1
        have h2 := Finset.card_le_card h1
        have := h.2
        omega
  calc m * q = ∑ _i : Fin m, q := by simp
    _ ≤ ∑ i : Fin m, ((Finset.Ico n (n + gates.length)).filter
        (fun w => Priv val (S i) (S i0) w)).card :=
        Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Finset.univ.biUnion (fun i : Fin m => (Finset.Ico n (n + gates.length)).filter
        (fun w => Priv val (S i) (S i0) w))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_biUnion] at hw
        obtain ⟨i, _, hw⟩ := hw
        exact (Finset.mem_filter.mp hw).1
    _ = gates.length := by
        rw [Nat.card_Ico]
        omega

end PEqualNP.Outside.L_meta_1375

theorem PEqualNP.Outside.L_meta_1375 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      ((∀ v ∈ S i0, x v = false) ∨ (∃ p ∈ S i0, ∀ v : Fin n, x v = decide (v = p))) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    m * q ≤ gates.length := by
  intro q n m S i0 _ hSc hS gates out hgates hprom
  exact PEqualNP.Outside.L_meta_1375.main q n m S i0 hSc hS gates out hgates hprom
