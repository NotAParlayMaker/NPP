import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572

open PEqualNP.CircuitLowerBounds

def Lstd (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def coLine (t : Fin 13) : Fin 13 → Bool := fun v => decide (v ∉ Lstd t)

def tst (z o p : Fin 13) : Fin 13 → Bool :=
  fun v => decide (v = p ∨ (p ≠ z ∧ v = o))

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def evalW (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) : Bool :=
  Circuit.eval ⟨gs, w⟩ (List.ofFn x)

lemma evalW_eq_wiresOf (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) :
    evalW gs w x = (wiresOf gs (List.ofFn x)).getD w false := rfl

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresOf (g :: gs) x =
      wiresOf gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  simp [wiresOf, List.foldl_append]

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    · exact getD_append_left x _ i false hi
    · simp; omega

lemma evalW_input (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : w < 13) :
    evalW gs w x = x ⟨w, hw⟩ := by
  rw [evalW_eq_wiresOf, wiresOf_getD_lt]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]
  · simp [hw]

lemma evalW_ge_len (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : 13 + gs.length ≤ w) :
    evalW gs w x = false := by
  rw [evalW_eq_wiresOf]
  have hlen : (wiresOf gs (List.ofFn x)).length = 13 + gs.length := by
    rw [wiresOf_length, List.length_ofFn]
  have hge : (wiresOf gs (List.ofFn x)).length ≤ w := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]

lemma evalW_gate (gs : List Gate) (x : Fin 13 → Bool) (j : Fin gs.length) :
    evalW gs (13 + (j : ℕ)) x =
      (gs.get j).op.eval
        ((gs.get j).inputs.map fun i => if i < 13 + (j : ℕ) then evalW gs i x else false) := by
  have hsplit : gs = gs.take (j : ℕ) ++ [gs.get j] ++ gs.drop ((j : ℕ) + 1) := by
    have h1 := (List.take_append_drop (j : ℕ) gs).symm
    have h2 : gs.drop (j : ℕ) = gs.get j :: gs.drop ((j : ℕ) + 1) := by
      rw [← List.getElem_cons_drop j.isLt]
      rfl
    exact h1.trans (by rw [h2]; simp)
  set p := gs.take (j : ℕ)
  set g := gs.get j
  set q := gs.drop ((j : ℕ) + 1)
  have hplen : p.length = (j : ℕ) := List.length_take_of_le (Nat.le_of_lt j.isLt)
  have hwp_len : (wiresOf p (List.ofFn x)).length = 13 + (j : ℕ) := by
    rw [wiresOf_length, List.length_ofFn, hplen]
  have hprefix_eq : ∀ i, i < 13 + (j : ℕ) →
      (wiresOf p (List.ofFn x)).getD i false = (wiresOf gs (List.ofFn x)).getD i false := by
    intro i hi
    have hw_eq : wiresOf gs (List.ofFn x) = wiresOf ([g] ++ q) (wiresOf p (List.ofFn x)) := by
      rw [← wiresOf_append, ← List.append_assoc, ← hsplit]
    rw [hw_eq]
    exact (wiresOf_getD_lt ([g] ++ q) (wiresOf p (List.ofFn x)) i (by omega)).symm
  have hmap : (g.inputs.map fun i => (wiresOf p (List.ofFn x)).getD i false) =
      (g.inputs.map fun i => if i < 13 + (j : ℕ) then evalW gs i x else false) := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < 13 + (j : ℕ)
    · simp only [hi, ↓reduceIte, evalW_eq_wiresOf]
      exact hprefix_eq i hi
    · simp only [hi, ↓reduceIte]
      have hge : (wiresOf p (List.ofFn x)).length ≤ i := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
  rw [evalW_eq_wiresOf]
  have hw_eq : wiresOf gs (List.ofFn x) = wiresOf q (wiresOf [g] (wiresOf p (List.ofFn x))) := by
    rw [← wiresOf_append, ← wiresOf_append, ← List.append_assoc, ← hsplit]
  rw [hw_eq, wiresOf_getD_lt q]
  · rw [wiresOf_cons, wiresOf_nil]
    rw [getD_append_right (wiresOf p (List.ofFn x)) _ (13 + (j : ℕ)) false (by omega)]
    rw [hwp_len, Nat.sub_self, hmap]
    rfl
  · rw [wiresOf_cons, wiresOf_nil, List.length_append, hwp_len]
    simp

lemma evalW_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true) :
    ∀ w : ℕ, evalW gs w x = true → evalW gs w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwx
    by_cases h13 : w < 13
    · rw [evalW_input gs x w h13] at hwx
      rw [evalW_input gs y w h13]
      exact hxy ⟨w, h13⟩ hwx
    · by_cases hlt : w < 13 + gs.length
      · let j : Fin gs.length := ⟨w - 13, by omega⟩
        have hj : 13 + (j : ℕ) = w := by dsimp [j]; omega
        rw [← hj] at hwx ⊢
        rw [evalW_gate gs x j] at hwx
        rw [evalW_gate gs y j]
        rcases hgs _ (List.get_mem gs j) with hand | hor
        · rw [hand] at hwx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hwx ⊢
          intro i hi
          have hix := hwx i hi
          by_cases hilt : i < 13 + (j : ℕ)
          · simp only [hilt, ↓reduceIte] at hix ⊢
            exact ih i (by omega) hix
          · simp [hilt] at hix
        · rw [hor] at hwx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hwx ⊢
          obtain ⟨_, ⟨i, hi, rfl⟩, hix⟩ := hwx
          refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
          by_cases hilt : i < 13 + (j : ℕ)
          · simp only [hilt, ↓reduceIte] at hix ⊢
            exact ih i (by omega) hix
          · simp [hilt] at hix
      · rw [evalW_ge_len gs x w (by omega)] at hwx
        exact Bool.noConfusion hwx

lemma find_atom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x1 x2 x3 : Fin 13 → Bool)
    (hno : ∀ v : Fin 13, x1 v = false → x2 v = false → x3 v = true → False) :
    ∀ w : ℕ,
      evalW gs w x1 = false →
      evalW gs w x2 = false →
      evalW gs w x3 = true →
      ∃ Y : ℕ,
        (∀ S : Set ℕ, w ∈ S →
          (∀ i : Fin gs.length, 13 + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
            ∀ a ∈ (gs.get i).inputs, a ∈ S) → Y ∈ S) ∧
        (∃ i : Fin gs.length, Y = 13 + (i : ℕ) ∧ (gs.get i).op = GateOp.and) ∧
        evalW gs Y x3 = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hc0 hct hts
    by_cases h13 : w < 13
    · exfalso
      rw [evalW_input gs x1 w h13] at hc0
      rw [evalW_input gs x2 w h13] at hct
      rw [evalW_input gs x3 w h13] at hts
      exact hno _ hc0 hct hts
    · by_cases hlt : w < 13 + gs.length
      · let j : Fin gs.length := ⟨w - 13, by omega⟩
        have hj : 13 + (j : ℕ) = w := by dsimp [j]; omega
        rcases hgs _ (List.get_mem gs j) with hand | hor
        · exact ⟨w, fun S hw _ => hw, ⟨j, hj.symm, hand⟩, hts⟩
        · have hc0' := hc0
          have hct' := hct
          have hts' := hts
          rw [← hj] at hc0' hct' hts'
          rw [evalW_gate gs x1 j, hor] at hc0'
          rw [evalW_gate gs x2 j, hor] at hct'
          rw [evalW_gate gs x3 j, hor] at hts'
          simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hc0' hct'
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hts'
          obtain ⟨_, ⟨a, ha_mem, rfl⟩, ha_ts⟩ := hts'
          have ha_lt : a < 13 + (j : ℕ) := by
            by_contra h
            simp [h] at ha_ts
          simp only [ha_lt, ↓reduceIte] at ha_ts
          have ha_c0 : evalW gs a x1 = false := by
            have h := hc0' a ha_mem
            simp only [ha_lt, ↓reduceIte] at h
            cases hv : evalW gs a x1
            · rfl
            · exact absurd hv h
          have ha_ct : evalW gs a x2 = false := by
            have h := hct' a ha_mem
            simp only [ha_lt, ↓reduceIte] at h
            cases hv : evalW gs a x2
            · rfl
            · exact absurd hv h
          obtain ⟨Y, hreach, handY, hYts⟩ := ih a (by omega) ha_c0 ha_ct ha_ts
          refine ⟨Y, ?_, handY, hYts⟩
          intro S hwS hclosed
          apply hreach S _ hclosed
          exact hclosed j (by rw [hj]; exact hwS) hor a ha_mem
      · exfalso
        rw [evalW_ge_len gs x3 w (by omega)] at hts
        exact Bool.noConfusion hts

lemma half (gates : List Gate) (g : ℕ) (l m c z o : Fin 13)
    (hgs : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hz : z ∉ Lstd m) (ho : o ∉ Lstd l) (hc : Lstd l ∩ Lstd m = {c})
    (h1 : evalW gates g (coLine l) = false)
    (h2 : evalW gates g (coLine m) = false)
    (hcard : 2 ≤ ((Lstd l).filter (fun p => evalW gates g (tst z o p) = true)).card) :
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      ∃ p ∈ Lstd l, p ≠ z ∧ p ≠ c ∧ evalW gates Y (tst z o p) = true := by
  obtain ⟨p, hpA, hpc⟩ := Finset.exists_mem_ne (Nat.lt_of_succ_le hcard) c
  rw [Finset.mem_filter] at hpA
  obtain ⟨hpl, hpt⟩ := hpA
  have hpz : p ≠ z := by
    rintro rfl
    have hmono : evalW gates g (coLine m) = true := by
      apply evalW_mono gates hgs (tst p o p) (coLine m) _ g hpt
      intro v hv
      simp only [tst, decide_eq_true_eq] at hv
      simp only [coLine, decide_eq_true_eq]
      rcases hv with rfl | ⟨h0, _⟩
      · exact hz
      · exact absurd rfl h0
    rw [h2] at hmono
    exact Bool.noConfusion hmono
  have hno : ∀ v : Fin 13, coLine l v = false → coLine m v = false → tst z o p v = true →
      False := by
    intro v hv1 hv2 hv3
    simp only [coLine, decide_eq_false_iff_not, not_not] at hv1 hv2
    simp only [tst, decide_eq_true_eq] at hv3
    have hvc : v = c := by
      have : v ∈ Lstd l ∩ Lstd m := Finset.mem_inter.mpr ⟨hv1, hv2⟩
      rw [hc] at this
      exact Finset.mem_singleton.mp this
    rcases hv3 with rfl | ⟨_, rfl⟩
    · exact hpc hvc
    · exact ho hv1
  obtain ⟨Y, hreach, handY, hY⟩ := find_atom gates hgs _ _ _ hno g h1 h2 hpt
  exact ⟨Y, hreach, handY, p, hpl, hpz, hpc, hY⟩

lemma facts1 (l : Fin 13) (hl : l ∈ ({4, 10, 12} : Finset (Fin 13))) : (1 : Fin 13) ∉ Lstd l := by
  revert l; decide

lemma facts0 (m : Fin 13) (hm : m ∈ ({1, 5, 11} : Finset (Fin 13))) : (0 : Fin 13) ∉ Lstd m := by
  revert m; decide

end PEqualNP.Outside.L_meta_1572

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hgs _ hl hm hc h1 h2
  have hLeq : L = PEqualNP.Outside.L_meta_1572.Lstd := funext hL
  subst hLeq
  have hgs' : ∀ x ∈ gates, x.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      x.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun x hx => (hgs x hx).1
  have hc' : PEqualNP.Outside.L_meta_1572.Lstd m ∩ PEqualNP.Outside.L_meta_1572.Lstd l = {c} := by
    rw [Finset.inter_comm]; exact hc
  constructor
  · intro hcard
    exact PEqualNP.Outside.L_meta_1572.half gates g l m c 0 1 hgs'
      (PEqualNP.Outside.L_meta_1572.facts0 m hm) (PEqualNP.Outside.L_meta_1572.facts1 l hl)
      hc h1 h2 hcard
  · intro hcard
    exact PEqualNP.Outside.L_meta_1572.half gates g m l c 1 0 hgs'
      (PEqualNP.Outside.L_meta_1572.facts1 l hl) (PEqualNP.Outside.L_meta_1572.facts0 m hm)
      hc' h2 h1 hcard
