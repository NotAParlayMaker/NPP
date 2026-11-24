import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1572

-- The wire evaluation identities follow the project proofs in L_meta_537 and L_meta_738.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]




private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp


private theorem gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj


private theorem wiresFrom_getElem_gate {gs : List Gate} {w : List Bool} {j : ℕ}
    (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append]
  set W := wiresFrom (gs.take j) w
  have hW : W.length = w.length + j := by
    simp [W, length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hstep : wiresFrom (gs[j] :: gs.drop (j + 1)) W =
      wiresFrom (gs.drop (j + 1)) (W ++ [(gs[j]).op.eval ((gs[j]).inputs.map fun i => W.getD i false)]) := rfl
  rw [hstep, getD_wiresFrom _ _ _ (by simp [hW]), ← hW, getD_snoc_eq]

private theorem wiresFrom_getD_take_eq {gs : List Gate} {w : List Bool} {j i : ℕ}
    (hj : j < gs.length) (hi : i < w.length + j) :
    (wiresFrom (gs.take j) w).getD i false = (wiresFrom gs w).getD i false := by
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    simp [length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  conv_rhs => rw [hsplit, wiresFrom_append]
  exact (getD_wiresFrom (gs.drop j) (wiresFrom (gs.take j) w) i (by omega)).symm

private theorem wiresFrom_gate_eval_rb {n : ℕ} {C : Circuit} (hrb : ReadsBack n C)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) :
    (wiresFrom C.gates (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => (wiresFrom C.gates (List.ofFn x)).getD i false) := by
  have h1 := wiresFrom_getElem_gate (gs := C.gates) (w := List.ofFn x) hj
  simp only [List.length_ofFn] at h1
  have hga : gateAt C j = C.gates[j] := gateAt_eq_getElem hj
  rw [hga, h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := hrb j hj i (hga ▸ hi)
  exact wiresFrom_getD_take_eq hj (by simp; exact hilt)

private theorem wiresFrom_input_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [getD_wiresFrom _ _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]


lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f g : ℕ → Bool)
    (hfg : ∀ a ∈ l, f a = true → g a = true) (h : op.eval (l.map f) = true) :
    op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h ⊢
    rintro _ ⟨a, ha, rfl⟩
    exact hfg a ha (h _ ⟨a, ha, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, h2⟩ := h
    exact ⟨_, ⟨a, ha, rfl⟩, hfg a ha h2⟩



def val (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD w false

lemma raw (gs : List Gate) (x : Fin 13 → Bool) {w : ℕ} (h : w < 13) :
    val gs x w = x ⟨w,h⟩ := wiresFrom_input_val (⟨gs,0⟩ : Circuit) x h

lemma inside {gs : List Gate} {x : Fin 13 → Bool} {w : ℕ} (h : val gs x w = true) :
    w < 13 + gs.length := by
  by_contra! hb
  have hl : (wiresFrom gs (List.ofFn x)).length ≤ w := by
    simpa [length_wiresFrom] using hb
  unfold val at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at h
  contradiction

lemma atGate {gs : List Gate} (readBack : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs,
    a < 13+i.val) (x : Fin 13 → Bool) (i : Fin gs.length) :
    val gs x (13+i.val) = (gs.get i).op.eval ((gs.get i).inputs.map (val gs x)) := by
  let C : Circuit := ⟨gs,0⟩
  have rb : ReadsBack 13 C := by
    intro j hj a ha
    rw [gateAt_eq_getElem hj] at ha
    exact readBack ⟨j,hj⟩ a ha
  have e := wiresFrom_gate_eval_rb rb x (j := i.val) i.isLt
  rw [gateAt_eq_getElem (C := C) i.isLt] at e
  exact e

lemma monotoneWire {gs : List Gate}
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (rb : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 13+i.val)
    (x y : Fin 13 → Bool) (xy : ∀ v, x v = true → y v = true) :
    ∀ w, val gs x w = true → val gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h : w < 13
    · rw [raw _ _ h] at hw ⊢
      exact xy _ hw
    have hwlt := inside hw
    let i : Fin gs.length := ⟨w-13,by omega⟩
    have he : w = 13+i.val := by dsimp [i]; omega
    rw [he, atGate rb] at hw ⊢
    exact eval_mono _ (legal _ (List.get_mem _ _)) _ _ _
      (fun a ha => ih a (by simpa [← he] using rb i a ha)) hw

def line (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}

def reach (gs : List Gate) (root w : ℕ) : Prop :=
  ∀ S : Set ℕ, root ∈ S →
    (∀ i : Fin gs.length, 13+i.val ∈ S → (gs.get i).op = GateOp.or →
      ∀ a ∈ (gs.get i).inputs, a ∈ S) → w ∈ S

lemma orTrue {gs : List Gate} (rb : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs,
    a < 13+i.val) (i : Fin gs.length) (op : (gs.get i).op = GateOp.or)
    (x : Fin 13 → Bool) : val gs x (13+i.val) = true ↔
    ∃ a ∈ (gs.get i).inputs, val gs x a = true := by
  rw [atGate rb, op]
  simp [GateOp.eval, List.any_map]


def co (A : Finset (Fin 13)) (v : Fin 13) : Bool := decide (v ∉ A)
def probe (a b p v : Fin 13) : Bool := decide (v=p ∨ (p≠a ∧ v=b))

lemma geometryL : ∀ l ∈ ({4,10,12} : Finset (Fin 13)), (1 : Fin 13) ∉ line l := by decide +kernel
lemma geometryM : ∀ m ∈ ({1,5,11} : Finset (Fin 13)), (0 : Fin 13) ∉ line m := by decide +kernel

lemma side (gs : List Gate) (g : Nat) (a b c : Fin 13) (A B : Finset (Fin 13))
    (basis : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or)
    (rb : ∀ i : Fin gs.length, ∀ v ∈ (gs.get i).inputs, v < 13+i.val)
    (ha : a ∉ B) (hb : b ∉ A) (common : A ∩ B = {c})
    (hA : val gs (co A) g = false) (hB : val gs (co B) g = false)
    (hc : 2 ≤ (A.filter (fun p => val gs (probe a b p) g = true)).card) :
    ∃ Y, reach gs g Y ∧ (∃ i : Fin gs.length, Y = 13+i.val ∧ (gs.get i).op = GateOp.and) ∧
      ∃ p ∈ A, p ≠ a ∧ p ≠ c ∧ val gs (probe a b p) Y = true := by
  classical
  obtain ⟨s, hsA, hsc, hs⟩ : ∃ s ∈ A, s ≠ c ∧ val gs (probe a b s) g = true := by
    by_contra! no
    have sub : (A.filter (fun p => val gs (probe a b p) g = true)) ⊆ ({c} : Finset _) := by
      intro p hp
      obtain ⟨hpA,hp⟩ := Finset.mem_filter.mp hp
      by_contra hn
      have hpc : p ≠ c := by simpa using hn
      simpa [hp] using no p hpA hpc
    have h := Finset.card_le_card sub
    simp at h
    omega
  have hsa : s ≠ a := by
    rintro rfl
    have le : ∀ v, probe s b s v = true → co B v = true := by
      intro v hv
      simp [probe] at hv
      simpa [co,hv] using ha
    have h := monotoneWire basis rb _ _ le g hs
    simp [hB] at h
  let Good := fun w => reach gs g w ∧ val gs (co A) w = false ∧
    val gs (co B) w = false ∧ val gs (probe a b s) w = true
  have ex : ∃ w, Good w := ⟨g, (fun _ h _ => h), hA, hB, hs⟩
  let w := Nat.find ex
  obtain ⟨hr,h0,hT,hyes⟩ := Nat.find_spec ex
  change reach gs g w at hr
  change val gs _ w = false at h0 hT
  change val gs _ w = true at hyes
  have big : ¬ w < 13 := by
    intro hw
    rw [raw _ _ hw] at h0 hT hyes
    simp only [co, decide_eq_false_iff_not, not_not] at h0 hT
    have eqc : (⟨w,hw⟩ : Fin 13) = c := Finset.mem_singleton.mp
      (common ▸ (Finset.mem_inter.mpr ⟨h0,hT⟩) : (⟨w,hw⟩ : Fin 13) ∈ ({c} : Finset _))
    rcases (of_decide_eq_true hyes : (⟨w,hw⟩ : Fin 13) = s ∨ s ≠ a ∧ (⟨w,hw⟩ : Fin 13) = b) with e | e
    · exact hsc (e.symm.trans eqc)
    · exact hb (e.2 ▸ h0)
  have lim := inside hyes
  let i : Fin gs.length := ⟨w-13,by omega⟩
  have he : w = 13+i.val := by dsimp [i]; omega
  rcases basis (gs.get i) (List.get_mem _ _) with ha | ho
  · exact ⟨w, hr, ⟨i,he,ha⟩, s, hsA, hsa, hsc, hyes⟩
  · rw [he] at hr h0 hT hyes
    obtain ⟨a,ham,hay⟩ := (orTrue rb i ho _).mp hyes
    have off (x) (hx : val gs x (13+i.val) = false) : val gs x a = false := by
      cases h : val gs x a with
      | false => rfl
      | true =>
        have := (orTrue rb i ho x).mpr ⟨a,ham,h⟩
        simp [hx] at this
    have hgood : Good a := ⟨fun S hg hc => hc i (hr S hg hc) ho a ham, off _ h0, off _ hT, hay⟩
    exact False.elim (Nat.find_min ex (by change a < w; rw [he]; exact rb i a ham) hgood)

end PEqualNP.Outside.L_meta_1572

open PEqualNP.Outside.L_meta_1572

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L eqn gs g l m c legal valid hl hm hi hL hM
  have basis := fun k (hk : k ∈ gs) => (legal k hk).1
  have rb := fun i : Fin gs.length => (valid i).2
  have ha : (0 : Fin 13) ∉ L m := by rw [eqn]; exact geometryM m hm
  have hb : (1 : Fin 13) ∉ L l := by rw [eqn]; exact geometryL l hl
  exact ⟨side gs g 0 1 c (L l) (L m) basis rb ha hb hi hL hM,
    side gs g 1 0 c (L m) (L l) basis rb hb ha ((Finset.inter_comm (L m) (L l)).trans hi) hM hL⟩
