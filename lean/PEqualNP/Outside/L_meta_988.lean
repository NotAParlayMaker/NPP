import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_988

open PEqualNP.CircuitLowerBounds
open Classical

def GateOK {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (t : ℕ) : Prop :=
  (∀ x, val x t = false) ∨ (∀ x, val x t = true) ∨ ∃ a b, a < t ∧ b < t ∧
    ((∀ x, val x t = (val x a && val x b)) ∨ (∀ x, val x t = (val x a || val x b)))

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

def ey {n : ℕ} (y : Finset (Fin n)) (p : Fin n) : Fin n → Bool :=
  fun v => decide (v ∈ y ∨ v = p)

def Guard {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S y : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (∀ q ∈ y, x q = true) → val x w = true → ∃ p ∈ S, x p = true

noncomputable def Q {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S y : Finset (Fin n))
    (w : ℕ) : Finset (Fin n) :=
  S.filter (fun p => val (ey y p) w = true)

noncomputable def Bs {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S y : Finset (Fin n))
    (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun w => Guard val S y w ∧ 2 ≤ (Q val S y w).card)

lemma guard_of_le {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S y : Finset (Fin n))
    (w c : ℕ) (hw : Guard val S y w) (h : ∀ x, val x c = true → val x w = true) :
    Guard val S y c := fun x hx hc => hw x hx (h x hc)

lemma guard_y {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S y : Finset (Fin n))
    (hSy : Disjoint y S) (w : ℕ) (hw : Guard val S y w) :
    val (fun v => decide (v ∈ y)) w = false := by
  by_contra h
  obtain ⟨p, hp, hx⟩ := hw (fun v => decide (v ∈ y)) (fun q hq => by simp [hq]) (by simpa using h)
  exact Finset.disjoint_left.mp hSy (by simpa using hx) hp

lemma q_input {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (S y : Finset (Fin n))
    (hSy : Disjoint y S) (w : ℕ) (hwn : w < n) (hw : Guard val S y w) :
    (Q val S y w).card ≤ 1 := by
  have h0 := guard_y val S y hSy w hw
  rw [hin _ ⟨w, hwn⟩] at h0
  rw [Finset.card_le_one]
  have key : ∀ p ∈ Q val S y w, p = ⟨w, hwn⟩ := by
    intro p hp
    simp only [Q, Finset.mem_filter] at hp
    have h1 := hp.2
    rw [hin _ ⟨w, hwn⟩] at h1
    simp only [ey, decide_eq_true_eq] at h1
    simp only [decide_eq_false_iff_not] at h0
    rcases h1 with h1 | h1
    · exact absurd h1 h0
    · exact h1.symm
  intro a ha b hb
  rw [key a ha, key b hb]

lemma q_dead {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S y : Finset (Fin n)) (w : ℕ)
    (h : ∀ x, val x w = false) : Q val S y w = ∅ := by
  ext p
  simp [Q, h]

lemma core {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (hg : ∀ t, n ≤ t → GateOK val t)
    (S y : Finset (Fin n)) (hSy : Disjoint y S) :
    ∀ k (W : Finset ℕ), (∀ w ∈ W, w < k ∧ Guard val S y w) →
      (W.biUnion (Q val S y)).card ≤ W.card + (Bs val S y k).card := by
  intro k
  induction k with
  | zero =>
    intro W hW
    have : W = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro hw
      exact absurd (hW w hw).1 (Nat.not_lt_zero _)
    subst this
    simp
  | succ k ih =>
    intro W hW
    have hBsub : Bs val S y k ⊆ Bs val S y (k + 1) := by
      apply Finset.filter_subset_filter
      intro w
      simp only [Finset.mem_range]
      omega
    have hBmono := Finset.card_le_card hBsub
    by_cases hk : k ∈ W
    · have hGk := (hW k hk).2
      have hWe : ∀ w ∈ W.erase k, w < k ∧ Guard val S y w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hcardE : (W.erase k).card + 1 = W.card := Finset.card_erase_add_one hk
      have herase : (W.biUnion (Q val S y)).card ≤
          ((W.erase k).biUnion (Q val S y)).card + (Q val S y k).card := by
        conv_lhs => rw [← Finset.insert_erase hk]
        rw [Finset.biUnion_insert]
        refine (Finset.card_union_le _ _).trans ?_
        omega
      have ihE := ih (W.erase k) hWe
      by_cases hQ : (Q val S y k).card ≤ 1
      · omega
      · push Not at hQ
        have hBk : (Bs val S y (k + 1)).card = (Bs val S y k).card + 1 := by
          have : Bs val S y (k + 1) = insert k (Bs val S y k) := by
            simp only [Bs]
            rw [Finset.range_add_one, Finset.filter_insert]
            simp [hGk, hQ]
          rw [this, Finset.card_insert_of_notMem]
          simp [Bs]
        by_cases hkn : k < n
        · have := q_input val hin S y hSy k hkn hGk
          omega
        have hrep : ∃ W' : Finset ℕ, (∀ w ∈ W', w < k ∧ Guard val S y w) ∧
            W'.card ≤ W.card + 1 ∧ W.biUnion (Q val S y) ⊆ W'.biUnion (Q val S y) := by
          rcases hg k (not_lt.mp hkn) with h0 | h1 | ⟨a, b, ha, hb, hand | hor⟩
          · rw [q_dead val S y k h0] at hQ
            simp at hQ
          · have := guard_y val S y hSy k hGk
            rw [h1] at this
            exact absurd this (by simp)
          · have hc : ∃ c, c < k ∧ Guard val S y c ∧ ∀ x, val x k = true → val x c = true := by
              by_contra hno
              have hA : ¬ Guard val S y a := fun hga =>
                hno ⟨a, ha, hga, fun x hx => by rw [hand] at hx; simp at hx; exact hx.1⟩
              have hB : ¬ Guard val S y b := fun hgb =>
                hno ⟨b, hb, hgb, fun x hx => by rw [hand] at hx; simp at hx; exact hx.2⟩
              simp only [Guard, not_forall, not_exists, not_and] at hA hB
              obtain ⟨xa, hya, hva, hsa⟩ := hA
              obtain ⟨xb, hyb, hvb, hsb⟩ := hB
              have hxa : ∀ q, xa q = true → (xa q || xb q) = true := by
                intro q h; simp [h]
              have hxb : ∀ q, xb q = true → (xa q || xb q) = true := by
                intro q h; simp [h]
              have hk1 : val (fun q => xa q || xb q) k = true := by
                rw [hand]
                simp only [Bool.and_eq_true]
                exact ⟨mono val hin hg a xa _ hxa hva, mono val hin hg b xb _ hxb hvb⟩
              obtain ⟨p, hp, hxp⟩ := hGk _ (fun q hq => by simp [hya q hq]) hk1
              simp only [Bool.or_eq_true] at hxp
              rcases hxp with h | h
              · exact hsa p hp h
              · exact hsb p hp h
            obtain ⟨c, hck, hgc, hkc⟩ := hc
            refine ⟨insert c (W.erase k), ?_, ?_, ?_⟩
            · intro w hw
              rw [Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact ⟨hck, hgc⟩
              · exact hWe w hw
            · have := Finset.card_insert_le c (W.erase k)
              omega
            · intro p hp
              simp only [Finset.mem_biUnion] at hp ⊢
              obtain ⟨w, hw, hpw⟩ := hp
              by_cases hwk : w = k
              · subst hwk
                refine ⟨c, Finset.mem_insert_self _ _, ?_⟩
                simp only [Q, Finset.mem_filter] at hpw ⊢
                exact ⟨hpw.1, hkc _ hpw.2⟩
              · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwk, hw⟩), hpw⟩
          · have hga : Guard val S y a :=
              guard_of_le val S y k a hGk (fun x hx => by rw [hor]; simp [hx])
            have hgb : Guard val S y b :=
              guard_of_le val S y k b hGk (fun x hx => by rw [hor]; simp [hx])
            refine ⟨insert a (insert b (W.erase k)), ?_, ?_, ?_⟩
            · intro w hw
              simp only [Finset.mem_insert] at hw
              rcases hw with rfl | rfl | hw
              · exact ⟨ha, hga⟩
              · exact ⟨hb, hgb⟩
              · exact hWe w hw
            · have h1 := Finset.card_insert_le a (insert b (W.erase k))
              have h2 := Finset.card_insert_le b (W.erase k)
              omega
            · intro p hp
              simp only [Finset.mem_biUnion] at hp ⊢
              obtain ⟨w, hw, hpw⟩ := hp
              by_cases hwk : w = k
              · subst hwk
                simp only [Q, Finset.mem_filter] at hpw
                rw [hor] at hpw
                simp only [Bool.or_eq_true] at hpw
                rcases hpw.2 with h | h
                · exact ⟨a, by simp, by simp [Q, hpw.1, h]⟩
                · exact ⟨b, by simp, by simp [Q, hpw.1, h]⟩
              · exact ⟨w, by simp [hwk, hw], hpw⟩
        obtain ⟨W', hW', hc', hsub⟩ := hrep
        have := ih W' hW'
        have := Finset.card_le_card hsub
        omega
    · have hW' : ∀ w ∈ W, w < k ∧ Guard val S y w := by
        intro w hw
        have := hW w hw
        refine ⟨?_, this.2⟩
        have : w ≠ k := fun h => hk (h ▸ hw)
        omega
      have := ih W hW'
      omega

lemma share {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (hg : ∀ t, n ≤ t → GateOK val t)
    (Si Sj yi yj : Finset (Fin n)) (hij : (Si ∩ Sj).card ≤ 1) (hj : Disjoint yj Sj) (w : ℕ)
    (hgj : Guard val Sj yj w) (hq : 2 ≤ (Q val Si yi w).card) : ¬ Disjoint yi Sj := by
  have hex : ∃ p ∈ Q val Si yi w, p ∉ Sj := by
    by_contra hno
    push Not at hno
    have hsub : Q val Si yi w ⊆ Si ∩ Sj := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, hno p hp⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp, hpj⟩ := hex
  have hv := (Finset.mem_filter.mp hp).2
  have hx : val (fun v => ey yi p v || decide (v ∈ yj)) w = true :=
    mono val hin hg w _ _ (fun q h => by simp [h]) hv
  obtain ⟨q, hqS, hq1⟩ := hgj _ (fun q hq => by simp [hq]) hx
  simp only [ey, Bool.or_eq_true, decide_eq_true_eq] at hq1
  intro hdis
  rcases hq1 with (h | h) | h
  · exact Finset.disjoint_left.mp hdis h hqS
  · exact hpj (h ▸ hqS)
  · exact Finset.disjoint_left.mp hj h hqS

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

end PEqualNP.Outside.L_meta_988

open PEqualNP.Outside.L_meta_988 PEqualNP.CircuitLowerBounds Classical

theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  intro n m D S y C o hS hy hgates h4 h5 h6
  set val : (Fin n → Bool) → ℕ → Bool := fun x w => (C.wires (List.ofFn x)).getD w false
    with hval
  have hin : ∀ x (i : Fin n), val x i = x i := by
    intro x i
    simp only [hval]
    rw [wires_input C _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have hdead : ∀ x t, n + C.gates.length ≤ t → val x t = false := by
    intro x t ht
    simp only [hval]
    exact List.getD_eq_default _ _ (by rw [wires_len]; simpa using ht)
  have hg : ∀ t, n ≤ t → GateOK val t := by
    intro t ht
    by_cases htG : n + C.gates.length ≤ t
    · exact Or.inl (fun x => hdead x t htG)
    · have hj : t - n < C.gates.length := by omega
      obtain ⟨hop, hlen⟩ := hgates _ (List.getElem_mem hj)
      have key : ∀ x, val x t = (C.gates[t - n]).op.eval
          ((C.gates[t - n]).inputs.map fun i => if i < t then val x i else false) := by
        intro x
        have h := wires_gate C (List.ofFn x) (t - n) hj
        simp only [List.length_ofFn] at h
        have e : n + (t - n) = t := by omega
        rw [e] at h
        simpa [hval] using h
      generalize hl : (C.gates[t - n]).inputs = l at key hlen
      generalize (C.gates[t - n]).op = op at key hop
      match l, hlen with
      | [], _ =>
        rcases hop with rfl | rfl
        · exact Or.inr (Or.inl (fun x => by rw [key x]; simp [GateOp.eval]))
        · exact Or.inl (fun x => by rw [key x]; simp [GateOp.eval])
      | [a], _ =>
        by_cases ha : a < t <;> rcases hop with rfl | rfl
        all_goals simp only [ha, ↓reduceIte, GateOp.eval, List.map] at key
        · exact Or.inr (Or.inr ⟨a, a, ha, ha, Or.inl (fun x => by rw [key x]; simp)⟩)
        · exact Or.inr (Or.inr ⟨a, a, ha, ha, Or.inr (fun x => by rw [key x]; simp)⟩)
        · exact Or.inl (fun x => by rw [key x]; simp)
        · exact Or.inl (fun x => by rw [key x]; simp)
      | [a, b], _ =>
        by_cases ha : a < t <;> by_cases hb : b < t <;> rcases hop with rfl | rfl
        all_goals simp only [ha, hb, ↓reduceIte, GateOp.eval, List.map] at key
        · exact Or.inr (Or.inr ⟨a, b, ha, hb, Or.inl (fun x => by rw [key x]; simp)⟩)
        · exact Or.inr (Or.inr ⟨a, b, ha, hb, Or.inr (fun x => by rw [key x]; simp)⟩)
        · exact Or.inl (fun x => by rw [key x]; simp)
        · exact Or.inr (Or.inr ⟨a, a, ha, ha, Or.inr (fun x => by rw [key x]; simp)⟩)
        · exact Or.inl (fun x => by rw [key x]; simp)
        · exact Or.inr (Or.inr ⟨b, b, hb, hb, Or.inr (fun x => by rw [key x]; simp)⟩)
        · exact Or.inl (fun x => by rw [key x]; simp)
        · exact Or.inl (fun x => by rw [key x]; simp)
      | _ :: _ :: _ :: _, hlen => simp at hlen
  set I := Finset.Ico n (n + C.gates.length) with hI
  set P : Fin m → ℕ → Prop := fun i w =>
    Guard val (S i) (y i) w ∧ 2 ≤ (Q val (S i) (y i) w).card with hP
  have hbound : ∀ i : Fin m, (S i).card ≤ 1 + (I.filter (P i)).card := by
    intro i
    have hG : Guard val (S i) (y i) (o i) := fun x _ hx => h4 i x hx
    have hc := core val hin hg (S i) (y i) (hy i) (o i + 1) {o i}
      (by intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact ⟨by omega, hG⟩)
    rw [Finset.singleton_biUnion, Finset.card_singleton] at hc
    have hQ : Q val (S i) (y i) (o i) = S i := by
      apply Finset.filter_true_of_mem
      intro p hp
      exact h5 i p hp
    rw [hQ] at hc
    have hsub : Bs val (S i) (y i) (o i + 1) ⊆ I.filter (P i) := by
      intro w hw
      simp only [Bs, Finset.mem_filter] at hw
      rw [Finset.mem_filter]
      refine ⟨?_, hw.2⟩
      rw [hI, Finset.mem_Ico]
      constructor
      · by_contra hlt
        have := q_input val hin (S i) (y i) (hy i) w (not_le.mp hlt) hw.2.1
        omega
      · by_contra hge
        rw [q_dead val (S i) (y i) w (fun x => hdead x w (not_lt.mp hge))] at hw
        simp at hw
    have := Finset.card_le_card hsub
    omega
  have hcol : ∀ w ∈ I, (Finset.univ.filter (fun i : Fin m => P i w)).card ≤ D := by
    intro w _
    apply h6
    intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    exact share val hin hg (S i) (S j) (y i) (y j) (hS i j hij) (hy j) w hj.2.1 hi.2.2
  calc ∑ i : Fin m, (S i).card
      ≤ ∑ i : Fin m, (1 + (I.filter (P i)).card) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = m + ∑ i : Fin m, (I.filter (P i)).card := by
        rw [Finset.sum_add_distrib]
        simp
    _ = m + ∑ w ∈ I, (Finset.univ.filter (fun i : Fin m => P i w)).card := by
        congr 1
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ m + ∑ w ∈ I, D := by
        have := Finset.sum_le_sum hcol
        omega
    _ = D * C.gates.length + m := by
        rw [Finset.sum_const, smul_eq_mul, hI, Nat.card_Ico]
        rw [show n + C.gates.length - n = C.gates.length by omega]
        ring
