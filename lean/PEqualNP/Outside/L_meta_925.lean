import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds

def ind {n : ℕ} (F : Finset (Fin n)) : Fin n → Bool := fun q => decide (q ∈ F)

def GateOK {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (t : ℕ) : Prop :=
  (∀ x, val x t = false) ∨
  (∀ x, val x t = true) ∨
  ∃ a b, a < t ∧ b < t ∧
    ((∀ x, val x t = (val x a && val x b)) ∨ (∀ x, val x t = (val x a || val x b)))

def IsSpec {n m : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (S : Fin m → Finset (Fin n))
    (w : Fin m) (t : ℕ) : Prop :=
  n ≤ t ∧ val (ind (S w)) t = true ∧ ∀ v : Fin m, v ≠ w → val (ind (S v)) t = false

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
        cases hx
      · rw [h1]
      · rw [h] at hx ⊢
        simp only [Bool.and_eq_true] at hx ⊢
        exact ⟨ih a ha x y hxy hx.1, ih b hb x y hxy hx.2⟩
      · rw [h] at hx ⊢
        simp only [Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (ih a ha x y hxy hx)
        · exact Or.inr (ih b hb x y hxy hx)

lemma core {n m : ℕ} [DecidableEq (Fin m)] (val : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x (i : Fin n), val x i = x i) (hg : ∀ t, n ≤ t → GateOK val t)
    (S : Fin m → Finset (Fin n)) (w : Fin m) [DecidablePred (IsSpec val S w)] :
    ∀ t, ∀ W : Finset ℕ, W ⊆ Finset.range t → (∀ u ∈ W, val (ind (S w)) u = true) →
      ∃ (J : Finset (Fin m)) (D : Finset (Fin n)),
        w ∉ J ∧ D ⊆ S w ∧
        J.card + D.card ≤ W.card + ((Finset.range t).filter (IsSpec val S w)).card ∧
        ∀ u ∈ W, val (ind (D ∪ J.biUnion S)) u = true := by
  intro t
  induction t with
  | zero =>
    intro W hW _
    refine ⟨∅, ∅, by simp, by simp, by simp, ?_⟩
    intro u hu
    have := hW hu
    simp at this
  | succ t ih =>
    intro W hW htrue
    have hcnt : ((Finset.range t).filter (IsSpec val S w)).card ≤
        ((Finset.range (t + 1)).filter (IsSpec val S w)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_succ t)))
    by_cases htW : t ∈ W
    swap
    · have hW' : W ⊆ Finset.range t := by
        intro u hu
        have h1 := hW hu
        rw [Finset.mem_range] at h1 ⊢
        have : u ≠ t := fun h => htW (h ▸ hu)
        omega
      obtain ⟨J, D, hwJ, hDS, hc, hall⟩ := ih W hW' htrue
      exact ⟨J, D, hwJ, hDS, by omega, hall⟩
    · have hW0 : W.erase t ⊆ Finset.range t := by
        intro u hu
        rw [Finset.mem_erase] at hu
        have h1 := hW hu.2
        rw [Finset.mem_range] at h1 ⊢
        omega
      have htrue0 : ∀ u ∈ W.erase t, val (ind (S w)) u = true :=
        fun u hu => htrue u (Finset.mem_of_mem_erase hu)
      have hW0c : (W.erase t).card + 1 = W.card := Finset.card_erase_add_one htW
      have htSw : val (ind (S w)) t = true := htrue t htW
      by_cases hlt : t < n
      · obtain ⟨J, D, hwJ, hDS, hc, hall⟩ := ih (W.erase t) hW0 htrue0
        let p : Fin n := ⟨t, hlt⟩
        have hpSw : p ∈ S w := by
          have h1 := hin (ind (S w)) p
          simp only [p] at h1
          rw [h1] at htSw
          simpa [ind] using htSw
        refine ⟨J, insert p D, hwJ, Finset.insert_subset_iff.mpr ⟨hpSw, hDS⟩, ?_, ?_⟩
        · have := Finset.card_insert_le p D
          omega
        · intro u hu
          by_cases hut : u = t
          · subst hut
            have h1 := hin (ind (insert p D ∪ J.biUnion S)) p
            simp only [p] at h1
            rw [h1]
            simp [ind]
          · refine mono val hin hg u (ind (D ∪ J.biUnion S)) (ind (insert p D ∪ J.biUnion S)) ?_
              (hall u (Finset.mem_erase.mpr ⟨hut, hu⟩))
            intro q hq
            simp only [ind, decide_eq_true_eq, Finset.mem_union, Finset.mem_insert] at hq ⊢
            rcases hq with hq | hq
            · exact Or.inl (Or.inr hq)
            · exact Or.inr hq
      · have hnt : n ≤ t := not_lt.mp hlt
        by_cases hdrop : ∃ v : Fin m, v ≠ w ∧ val (ind (S v)) t = true
        · obtain ⟨v, hvw, htv⟩ := hdrop
          obtain ⟨J, D, hwJ, hDS, hc, hall⟩ := ih (W.erase t) hW0 htrue0
          refine ⟨insert v J, D, ?_, hDS, ?_, ?_⟩
          · simp [Ne.symm hvw, hwJ]
          · have := Finset.card_insert_le v J
            omega
          · intro u hu
            by_cases hut : u = t
            · subst hut
              refine mono val hin hg u (ind (S v)) (ind (D ∪ (insert v J).biUnion S)) ?_ htv
              intro q hq
              simp only [ind, decide_eq_true_eq, Finset.mem_union, Finset.mem_biUnion,
                Finset.mem_insert] at hq ⊢
              exact Or.inr ⟨v, Or.inl rfl, hq⟩
            · refine mono val hin hg u (ind (D ∪ J.biUnion S))
                (ind (D ∪ (insert v J).biUnion S)) ?_ (hall u (Finset.mem_erase.mpr ⟨hut, hu⟩))
              intro q hq
              simp only [ind, decide_eq_true_eq, Finset.mem_union, Finset.mem_biUnion,
                Finset.mem_insert] at hq ⊢
              rcases hq with hq | ⟨v', hv', hq⟩
              · exact Or.inl hq
              · exact Or.inr ⟨v', Or.inr hv', hq⟩
        · push Not at hdrop
          have hspec : IsSpec val S w t :=
            ⟨hnt, htSw, fun v hv => Bool.eq_false_iff.mpr (hdrop v hv)⟩
          have hfc : ((Finset.range (t + 1)).filter (IsSpec val S w)).card =
              ((Finset.range t).filter (IsSpec val S w)).card + 1 := by
            rw [Finset.range_add_one, Finset.filter_insert, if_pos hspec,
              Finset.card_insert_of_notMem (by simp)]
          rcases hg t hnt with h0 | h1 | ⟨a, b, ha, hb, hop⟩
          · rw [h0] at htSw
            cases htSw
          · obtain ⟨J, D, hwJ, hDS, hc, hall⟩ := ih (W.erase t) hW0 htrue0
            refine ⟨J, D, hwJ, hDS, by omega, ?_⟩
            intro u hu
            by_cases hut : u = t
            · subst hut; exact h1 _
            · exact hall u (Finset.mem_erase.mpr ⟨hut, hu⟩)
          · rcases hop with hand | hor
            · have hta : val (ind (S w)) a = true := by
                have := htSw; rw [hand] at this; exact (Bool.and_eq_true _ _).mp this |>.1
              have htb : val (ind (S w)) b = true := by
                have := htSw; rw [hand] at this; exact (Bool.and_eq_true _ _).mp this |>.2
              let W1 := insert a (insert b (W.erase t))
              have hW1 : W1 ⊆ Finset.range t := by
                intro u hu
                simp only [W1, Finset.mem_insert] at hu
                rcases hu with rfl | rfl | hu
                · exact Finset.mem_range.mpr ha
                · exact Finset.mem_range.mpr hb
                · exact hW0 hu
              have htrue1 : ∀ u ∈ W1, val (ind (S w)) u = true := by
                intro u hu
                simp only [W1, Finset.mem_insert] at hu
                rcases hu with rfl | rfl | hu
                · exact hta
                · exact htb
                · exact htrue0 u hu
              obtain ⟨J, D, hwJ, hDS, hc, hall⟩ := ih W1 hW1 htrue1
              have hcard1 : W1.card ≤ (W.erase t).card + 2 := by
                have h1 : W1.card ≤ (insert b (W.erase t)).card + 1 :=
                  Finset.card_insert_le a (insert b (W.erase t))
                have h2 := Finset.card_insert_le b (W.erase t)
                omega
              refine ⟨J, D, hwJ, hDS, by omega, ?_⟩
              intro u hu
              by_cases hut : u = t
              · subst hut
                rw [hand, Bool.and_eq_true]
                exact ⟨hall a (by simp [W1]), hall b (by simp [W1])⟩
              · exact hall u (by simp [W1, Finset.mem_erase.mpr ⟨hut, hu⟩])
            · have htab : val (ind (S w)) a = true ∨ val (ind (S w)) b = true := by
                have := htSw; rw [hor] at this; exact (Bool.or_eq_true _ _).mp this
              rcases htab with hta | htb
              · let W1 := insert a (W.erase t)
                have hW1 : W1 ⊆ Finset.range t := by
                  intro u hu
                  simp only [W1, Finset.mem_insert] at hu
                  rcases hu with rfl | hu
                  · exact Finset.mem_range.mpr ha
                  · exact hW0 hu
                have htrue1 : ∀ u ∈ W1, val (ind (S w)) u = true := by
                  intro u hu
                  simp only [W1, Finset.mem_insert] at hu
                  rcases hu with rfl | hu
                  · exact hta
                  · exact htrue0 u hu
                obtain ⟨J, D, hwJ, hDS, hc, hall⟩ := ih W1 hW1 htrue1
                have hcard1 : W1.card ≤ (W.erase t).card + 1 := Finset.card_insert_le a (W.erase t)
                refine ⟨J, D, hwJ, hDS, by omega, ?_⟩
                intro u hu
                by_cases hut : u = t
                · subst hut
                  rw [hor, Bool.or_eq_true]
                  exact Or.inl (hall a (by simp [W1]))
                · exact hall u (by simp [W1, Finset.mem_erase.mpr ⟨hut, hu⟩])
              · let W1 := insert b (W.erase t)
                have hW1 : W1 ⊆ Finset.range t := by
                  intro u hu
                  simp only [W1, Finset.mem_insert] at hu
                  rcases hu with rfl | hu
                  · exact Finset.mem_range.mpr hb
                  · exact hW0 hu
                have htrue1 : ∀ u ∈ W1, val (ind (S w)) u = true := by
                  intro u hu
                  simp only [W1, Finset.mem_insert] at hu
                  rcases hu with rfl | hu
                  · exact htb
                  · exact htrue0 u hu
                obtain ⟨J, D, hwJ, hDS, hc, hall⟩ := ih W1 hW1 htrue1
                have hcard1 : W1.card ≤ (W.erase t).card + 1 := Finset.card_insert_le b (W.erase t)
                refine ⟨J, D, hwJ, hDS, by omega, ?_⟩
                intro u hu
                by_cases hut : u = t
                · subst hut
                  rw [hor, Bool.or_eq_true]
                  exact Or.inr (hall b (by simp [W1]))
                · exact hall u (by simp [W1, Finset.mem_erase.mpr ⟨hut, hu⟩])

lemma card_biUnion_sets {n m q : ℕ} [DecidableEq (Fin m)] (S : Fin m → Finset (Fin n))
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (J : Finset (Fin m)) :
    (J.biUnion S).card ≤ J.card * q + 1 := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ha, Nat.add_mul, Nat.one_mul]
    by_cases hJ : J.Nonempty
    · obtain ⟨b, hb⟩ := hJ
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      have h1 : (S a ∩ S b).card = 1 := hinter a b hab
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (S a ∩ S b).card)
      have hp' : p ∈ S a ∩ J.biUnion S := by
        rw [Finset.mem_inter] at hp ⊢
        exact ⟨hp.1, Finset.mem_biUnion.mpr ⟨b, hb, hp.2⟩⟩
      have hpos : 1 ≤ (S a ∩ J.biUnion S).card := Finset.card_pos.mpr ⟨p, hp'⟩
      have hu := Finset.card_union_add_card_inter (S a) (J.biUnion S)
      have hsa := hcard a
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hJ]
      simp [hcard a]

lemma card_inter_biUnion_le {n m : ℕ} [DecidableEq (Fin m)] (S : Fin m → Finset (Fin n))
    (w : Fin m) (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (J : Finset (Fin m)) (hwJ : w ∉ J) :
    ((J.biUnion S) ∩ S w).card ≤ J.card := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
    have haw : a ≠ w := fun h => hwJ (h ▸ Finset.mem_insert_self a J)
    have hwJ' : w ∉ J := fun h => hwJ (Finset.mem_insert_of_mem h)
    rw [Finset.biUnion_insert, Finset.union_inter_distrib_right,
      Finset.card_insert_of_notMem ha]
    have h1 := Finset.card_union_le (S a ∩ S w) (J.biUnion S ∩ S w)
    have h2 := hinter a w haw
    have h3 := ih hwJ'
    omega

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
  · rw [hpl, if_pos hi]
    exact (getD_prefix hp0 (by rw [hpl]; exact hi)).symm
  · rw [hpl, if_neg hi]
    exact List.getD_eq_default _ _ (by rw [hpl]; omega)

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_prefix (fold_prefix C.gates x) hi

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hcard hinter gates out hgates heval c hcq hcqK
  by_cases hc0 : c = 0
  · subst hc0; simp
  have hc1 : 1 ≤ c := Nat.pos_of_ne_zero hc0
  let C0 : Circuit := ⟨gates, 0⟩
  let val : (Fin n → Bool) → ℕ → Bool := fun x t => (C0.wires (List.ofFn x)).getD t false
  have hval : ∀ x t, (C0.wires (List.ofFn x)).getD t false = val x t := fun _ _ => rfl
  have hin : ∀ x (i : Fin n), val x i = x i := by
    intro x i
    simp only [val]
    rw [wires_input C0 _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have hdead : ∀ x t, n + gates.length ≤ t → val x t = false := by
    intro x t ht
    simp only [val]
    exact List.getD_eq_default _ _ (by rw [wires_len]; simpa [C0] using ht)
  have hg : ∀ t, n ≤ t → GateOK val t := by
    intro t ht
    by_cases htG : n + gates.length ≤ t
    · exact Or.inl (fun x => hdead x t htG)
    · have hj : t - n < C0.gates.length := by simp [C0]; omega
      obtain ⟨hop, hlen⟩ := hgates _ (List.getElem_mem hj)
      have key : ∀ x, val x t = (C0.gates[t - n]).op.eval
          ((C0.gates[t - n]).inputs.map fun i => if i < t then val x i else false) := by
        intro x
        have h := wires_gate C0 (List.ofFn x) (t - n) hj
        simp only [List.length_ofFn] at h
        have e : n + (t - n) = t := by omega
        rw [e] at h
        simpa [val] using h
      rcases hli : (C0.gates[t - n]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, r⟩⟩⟩
      · rcases hop with hop | hop
        · exact Or.inr (Or.inl (fun x => by rw [key x, hli, hop]; rfl))
        · exact Or.inl (fun x => by rw [key x, hli, hop]; rfl)
      · by_cases ha : a < t
        · exact Or.inr (Or.inr ⟨a, a, ha, ha, Or.inr (fun x => by
            rw [key x, hli]; rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval])⟩)
        · rcases hop with hop | hop
          · exact Or.inl (fun x => by rw [key x, hli, hop]; simp [ha, GateOp.eval])
          · exact Or.inl (fun x => by rw [key x, hli, hop]; simp [ha, GateOp.eval])
      · by_cases ha : a < t <;> by_cases hb : b < t <;> rcases hop with hop | hop
        · exact Or.inr (Or.inr ⟨a, b, ha, hb, Or.inl (fun x => by
            rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])⟩)
        · exact Or.inr (Or.inr ⟨a, b, ha, hb, Or.inr (fun x => by
            rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])⟩)
        · exact Or.inl (fun x => by rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])
        · exact Or.inr (Or.inr ⟨a, a, ha, ha, Or.inr (fun x => by
            rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])⟩)
        · exact Or.inl (fun x => by rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])
        · exact Or.inr (Or.inr ⟨b, b, hb, hb, Or.inr (fun x => by
            rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])⟩)
        · exact Or.inl (fun x => by rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])
        · exact Or.inl (fun x => by rw [key x, hli, hop]; simp [ha, hb, GateOp.eval])
      · rw [hli] at hlen; simp at hlen
  have hfilter_ind : ∀ F : Finset (Fin n),
      Finset.univ.filter (fun i : Fin n => ind F i = true) = F := by
    intro F; ext i; simp [ind]
  have hbound : ∀ w : Fin m, c ≤ ((Finset.Ico n (n + gates.length)).filter
      (IsSpec val S w)).card := by
    intro w
    have hSwK : (S w).card ≤ K := by
      have := hcard w
      nlinarith
    have hout_true : val (ind (S w)) (out w) = true := by
      have h := heval w (ind (S w)) (by rw [hfilter_ind]; exact hSwK)
      change val (ind (S w)) (out w) = _ at h
      rw [h]
      simp [ind]
    obtain ⟨J, D, hwJ, hDS, hc, hall⟩ :=
      core val hin hg S w (out w + 1) {out w} (by simp)
        (fun u hu => by rw [Finset.mem_singleton.mp hu]; exact hout_true)
    have hle : ((Finset.range (out w + 1)).filter (IsSpec val S w)).card ≤
        ((Finset.Ico n (n + gates.length)).filter (IsSpec val S w)).card := by
      apply Finset.card_le_card
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      refine ⟨?_, ht.2⟩
      rw [Finset.mem_Ico]
      refine ⟨ht.2.1, ?_⟩
      by_contra hge
      have hfalse := hdead (ind (S w)) t (not_lt.mp hge)
      rw [ht.2.2.1] at hfalse
      cases hfalse
    rw [Finset.card_singleton] at hc
    by_contra hltc
    have hJD : J.card + D.card ≤ c := by omega
    let P := D ∪ J.biUnion S
    have hPcard : P.card ≤ K := by
      have h1 : P.card ≤ D.card + (J.biUnion S).card := Finset.card_union_le D (J.biUnion S)
      have h2 := card_biUnion_sets S hcard hinter J
      have h3 : D.card ≤ D.card * q := Nat.le_mul_of_pos_right _ (by omega)
      have h4 : (D.card + J.card) * q ≤ c * q := Nat.mul_le_mul_right q (by omega)
      have h5 : D.card * q + J.card * q = (D.card + J.card) * q := (Nat.add_mul _ _ _).symm
      omega
    have hPout : val (ind P) (out w) = true := hall (out w) (by simp)
    have hPeval := heval w (ind P) (by rw [hfilter_ind]; exact hPcard)
    change val (ind P) (out w) = _ at hPeval
    rw [hPout] at hPeval
    have hSwP : S w ⊆ P := by
      have hdec : decide (∀ v ∈ S w, ind P v = true) = true := hPeval.symm
      rw [decide_eq_true_iff] at hdec
      intro v hv
      have := hdec v hv
      simpa [ind] using this
    have hSwInter : S w ⊆ (D ∩ S w) ∪ (J.biUnion S ∩ S w) := by
      intro v hv
      have hvP := hSwP hv
      rw [ ← Finset.union_inter_distrib_right]
      exact Finset.mem_inter.mpr ⟨hvP, hv⟩
    have h6 := Finset.card_le_card hSwInter
    have h7 := Finset.card_union_le (D ∩ S w) (J.biUnion S ∩ S w)
    have h8 : (D ∩ S w).card ≤ D.card := Finset.card_le_card Finset.inter_subset_left
    have h9 := card_inter_biUnion_le S w hinter J hwJ
    have h10 := hcard w
    omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint
      ((Finset.Ico n (n + gates.length)).filter (IsSpec val S i))
      ((Finset.Ico n (n + gates.length)).filter (IsSpec val S j)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro t hti htj
    rw [Finset.mem_filter] at hti htj
    have hfalse := hti.2.2.2 j (Ne.symm hij)
    rw [htj.2.2.1] at hfalse
    cases hfalse
  calc m * c
      = ∑ _ : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, ((Finset.Ico n (n + gates.length)).filter (IsSpec val S w)).card :=
        Finset.sum_le_sum (fun w _ => hbound w)
    _ = (Finset.univ.biUnion (fun w : Fin m => (Finset.Ico n (n + gates.length)).filter
        (IsSpec val S w))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro t ht
        rw [Finset.mem_biUnion] at ht
        obtain ⟨w, _, ht⟩ := ht
        exact (Finset.mem_filter.mp ht).1
    _ = gates.length := by
        rw [Nat.card_Ico]
        omega
