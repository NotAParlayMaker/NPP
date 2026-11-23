import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782_aux

open PEqualNP.CircuitLowerBounds

private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl wiresStep x := rfl

private lemma foldl_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma getD_append_left (w1 w2 : List Bool) (u : ℕ) (hu : u < w1.length) :
    (w1 ++ w2).getD u false = w1.getD u false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]

private lemma getD_ge_length (w : List Bool) (u : ℕ) (hu : w.length ≤ u) :
    w.getD u false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hu]

private lemma foldl_getD_lt (gs : List Gate) :
    ∀ (w : List Bool) (u : ℕ), u < w.length →
      (gs.foldl wiresStep w).getD u false = w.getD u false := by
  induction gs with
  | nil => intro w u _; rfl
  | cons g gs ih =>
    intro w u hu
    have hu' : u < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.foldl_cons, ih (wiresStep w g) u hu', wiresStep, getD_append_left _ _ _ hu]

private lemma foldl_getD_ge (gs : List Gate) (w : List Bool) (u : ℕ)
    (hu : w.length + gs.length ≤ u) :
    (gs.foldl wiresStep w).getD u false = false := by
  apply getD_ge_length
  rw [foldl_length]
  exact hu

private lemma foldl_getD_gate (gs : List Gate) :
    ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl wiresStep w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun u =>
          if u < w.length + j then (gs.foldl wiresStep w).getD u false else false) := by
  induction gs with
  | nil => intro w j hj; cases hj
  | cons g gs ih =>
    intro w j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      have hlen : w.length < (wiresStep w g).length := by
        simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_getD_lt gs (wiresStep w g) w.length hlen]
      have hlast : (wiresStep w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [wiresStep, List.getD_eq_getElem?_getD]
      rw [hlast]
      congr 1
      apply List.map_congr_left
      intro u _
      by_cases hu : u < w.length
      · simp only [hu, ↓reduceIte]
        have hu' : u < (wiresStep w g).length := by omega
        rw [foldl_getD_lt gs (wiresStep w g) u hu', wiresStep, getD_append_left _ _ _ hu]
      · simp only [hu, ↓reduceIte]
        exact getD_ge_length w u (Nat.le_of_not_lt hu)
    | succ j =>
      have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
      have hidx : w.length + (j + 1) = (wiresStep w g).length + j := by
        simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
        omega
      simp only [List.foldl_cons, List.getElem_cons_succ, hidx]
      exact ih (wiresStep w g) j hj'

private lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ k (hk1 : k < l1.length) (hk2 : k < l2.length), l1[k] = true → l2[k] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨k, hk2, rfl⟩
    have hk1 : k < l1.length := by omega
    exact hle k hk1 hk2 (h1 _ (List.getElem_mem hk1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    rcases h1 with ⟨b, hb, rfl⟩
    rcases List.mem_iff_getElem.mp hb with ⟨k, hk1, hkval⟩
    have hk2 : k < l2.length := by omega
    exact ⟨l2[k], List.getElem_mem hk2, hle k hk1 hk2 hkval⟩

private lemma foldl_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ u, w1.getD u false = true → w2.getD u false = true) →
      ∀ u, (gs.foldl wiresStep w1).getD u false = true →
        (gs.foldl wiresStep w2).getD u false = true := by
  induction gs with
  | nil =>
    intro w1 w2 _ hle u hu
    exact hle u hu
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hgm : g.op = GateOp.and ∨ g.op = GateOp.or := hmono g (by simp)
    have hgsm : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (by simp [hg'])
    apply ih hgsm (wiresStep w1 g) (wiresStep w2 g)
    · simp [wiresStep, hlen]
    · intro u hu
      by_cases hlt : u < w1.length
      · have hlt2 : u < w2.length := by omega
        rw [wiresStep, getD_append_left _ _ _ hlt2]
        rw [wiresStep, getD_append_left _ _ _ hlt] at hu
        exact hle u hu
      · by_cases heq : u = w1.length
        · subst heq
          have h1 : (wiresStep w1 g).getD w1.length false =
              g.op.eval (g.inputs.map fun i => w1.getD i false) := by
            simp [wiresStep, List.getD_eq_getElem?_getD]
          have h2 : (wiresStep w2 g).getD w1.length false =
              g.op.eval (g.inputs.map fun i => w2.getD i false) := by
            rw [hlen]
            simp [wiresStep, List.getD_eq_getElem?_getD]
          rw [h1] at hu
          rw [h2]
          apply gateOp_eval_mono g.op hgm
            (g.inputs.map fun i => w1.getD i false)
            (g.inputs.map fun i => w2.getD i false) (by simp)
          · intro k hk1 hk2 hval
            simp only [List.getElem_map] at hval ⊢
            exact hle _ hval
          · exact hu
        · have hge : (wiresStep w1 g).length ≤ u := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ _ hge] at hu
          cases hu

private def wireVal (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private def unitInput {n : ℕ} (a : Fin n) : Fin n → Bool :=
  fun b => decide (b = a)

private def singleSet (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n => wireVal C (unitInput a) w = true)

private lemma wireVal_mono (C : Circuit) {n : ℕ}
    (hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hle : ∀ a : Fin n, x a = true → y a = true)
    (w : ℕ) (hw : wireVal C x w = true) : wireVal C y w = true := by
  apply foldl_mono C.gates hmono (List.ofFn x) (List.ofFn y) (by simp) _ w hw
  intro u hu
  by_cases hlt : u < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true,
      Option.getD_some] at hu ⊢
    exact hle ⟨u, hlt⟩ hu
  · have hge : (List.ofFn x).length ≤ u := by simp; omega
    rw [getD_ge_length _ _ hge] at hu
    cases hu

private lemma singleSet_lt_card (C : Circuit) (n : ℕ) (w : ℕ) (hw : w < n) :
    (singleSet C n w).card ≤ 1 := by
  have hsub : singleSet C n w ⊆ {⟨w, hw⟩} := by
    intro a ha
    have ha' : wireVal C (unitInput a) w = true := (Finset.mem_filter.mp ha).2
    simp only [wireVal, wires_eq_foldl] at ha'
    have hlt : w < (List.ofFn (unitInput a)).length := by simp [hw]
    rw [foldl_getD_lt C.gates _ w hlt] at ha'
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true,
      Option.getD_some, unitInput, decide_eq_true_eq] at ha'
    simp only [Finset.mem_singleton]
    exact ha'.symm
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma singleSet_ge_card (C : Circuit) (n : ℕ) (w : ℕ) (hw : n + C.size ≤ w) :
    (singleSet C n w).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro a ha
  have ha' : wireVal C (unitInput a) w = true := (Finset.mem_filter.mp ha).2
  simp only [wireVal, wires_eq_foldl] at ha'
  have hge : (List.ofFn (unitInput a)).length + C.gates.length ≤ w := by
    simp only [List.length_ofFn]
    exact hw
  rw [foldl_getD_ge C.gates _ w hge] at ha'
  cases ha'

private def opIsAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

private def gateInput0 (C : Circuit) (n : ℕ) (w : ℕ) : ℕ :=
  if h : n ≤ w ∧ w < n + C.size then
    (C.gates[w - n]'(by unfold Circuit.size at h; omega)).inputs.getD 0 0
  else 0

private def gateInput1 (C : Circuit) (n : ℕ) (w : ℕ) : ℕ :=
  if h : n ≤ w ∧ w < n + C.size then
    (C.gates[w - n]'(by unfold Circuit.size at h; omega)).inputs.getD 1 0
  else 0

private def gateIsAnd (C : Circuit) (n : ℕ) (w : ℕ) : Bool :=
  if h : n ≤ w ∧ w < n + C.size then
    opIsAnd (C.gates[w - n]'(by unfold Circuit.size at h; omega)).op
  else false

private lemma wireVal_gate_eq (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hnw : n ≤ w) (hwlt : w < n + C.size)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    let u := gateInput0 C n w
    let v := gateInput1 C n w
    let vu := if u < w then wireVal C x u else false
    let vv := if v < w then wireVal C x v else false
    wireVal C x w = if gateIsAnd C n w then vu && vv else vu || vv := by
  have hj : w - n < C.gates.length := by unfold Circuit.size at hwlt; omega
  have hwj : n + (w - n) = w := by omega
  have hgm := hgates (C.gates[w - n]) (List.getElem_mem hj)
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hg := foldl_getD_gate C.gates (List.ofFn x) (w - n) hj
  rw [hlen, hwj] at hg
  have hu_eq : gateInput0 C n w = (C.gates[w - n]).inputs.getD 0 0 := by
    simp [gateInput0, hnw, hwlt]
  have hv_eq : gateInput1 C n w = (C.gates[w - n]).inputs.getD 1 0 := by
    simp [gateInput1, hnw, hwlt]
  have hand_eq : gateIsAnd C n w = opIsAnd (C.gates[w - n]).op := by
    simp [gateIsAnd, hnw, hwlt]
  change (C.gates.foldl wiresStep (List.ofFn x)).getD w false = _
  rw [hg, hu_eq, hv_eq, hand_eq]
  rcases hlist : (C.gates[w - n]).inputs with _ | ⟨u, _ | ⟨v, l⟩⟩
  · simp [hlist] at hgm
  · simp [hlist] at hgm
  · cases l with
    | nil =>
      rcases hgm.1 with hand | hor
      · rw [hand]
        simp [GateOp.eval, opIsAnd, wireVal, wires_eq_foldl]
      · rw [hor]
        simp [GateOp.eval, opIsAnd, wireVal, wires_eq_foldl]
    | cons _ _ =>
      simp [hlist] at hgm

private def isPriv (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) : Bool :=
  decide (n ≤ w ∧ w < n + C.size ∧ singleSet C n w ⊆ Si ∧ 2 ≤ (singleSet C n w).card)

private lemma isPriv_iff (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    isPriv C n Si w = true ↔
      n ≤ w ∧ w < n + C.size ∧ singleSet C n w ⊆ Si ∧ 2 ≤ (singleSet C n w).card := by
  simp [isPriv]

private def lab (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) : Bool :=
  if isPriv C n Si w then
    let u := gateInput0 C n w
    let v := gateInput1 C n w
    let lu := if _ : u < w then lab C n Si u else false
    let lv := if _ : v < w then lab C n Si v else false
    if gateIsAnd C n w then lu && lv else lu || lv
  else
    decide (¬ singleSet C n w ⊆ Si)
termination_by w

private lemma lab_eq_exit (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ)
    (hnp : isPriv C n Si w = false) :
    lab C n Si w = decide (¬ singleSet C n w ⊆ Si) := by
  rw [lab]
  simp [hnp]

private lemma lab_eq_priv (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ)
    (hp : isPriv C n Si w = true) :
    lab C n Si w =
      let u := gateInput0 C n w
      let v := gateInput1 C n w
      let lu := if u < w then lab C n Si u else false
      let lv := if v < w then lab C n Si v else false
      if gateIsAnd C n w then lu && lv else lu || lv := by
  rw [lab]
  simp only [hp, ↓reduceIte]
  rfl

private def reach (ch : ℕ → Finset ℕ) (hdec : ∀ w v, v ∈ ch w → v < w) (w : ℕ) : Finset ℕ :=
  insert w ((ch w).attach.biUnion fun ⟨u, _hu⟩ => reach ch hdec u)
termination_by w
decreasing_by exact hdec w u _hu

private lemma reach_eq (ch : ℕ → Finset ℕ) (hdec : ∀ w v, v ∈ ch w → v < w) (w : ℕ) :
    reach ch hdec w = insert w ((ch w).biUnion (reach ch hdec)) := by
  conv_lhs => rw [reach]
  congr 1
  ext x
  simp

private lemma mem_reach_self (ch : ℕ → Finset ℕ) (hdec : ∀ w v, v ∈ ch w → v < w) (w : ℕ) :
    w ∈ reach ch hdec w := by
  rw [reach_eq]
  exact Finset.mem_insert_self w _

private lemma reach_sub_of_mem_ch (ch : ℕ → Finset ℕ) (hdec : ∀ w v, v ∈ ch w → v < w)
    (w u : ℕ) (hu : u ∈ ch w) :
    reach ch hdec u ⊆ reach ch hdec w := by
  intro x hx
  rw [reach_eq]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hx⟩)

private lemma reach_has_parent (ch : ℕ → Finset ℕ) (hdec : ∀ w v, v ∈ ch w → v < w)
    (P : ℕ → Bool) (hchP : ∀ w, P w = false → ch w = ∅) :
    ∀ r v, v ∈ reach ch hdec r → v ≠ r →
      ∃ w ∈ (reach ch hdec r).filter (fun y => P y = true), v ∈ ch w := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro v hv hne
    rw [reach_eq] at hv
    rcases Finset.mem_insert.mp hv with rfl | hmem
    · exact absurd rfl hne
    · rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hvu⟩
      have hPr : P r = true := by
        cases h : P r
        · rw [hchP r h] at hu
          exact absurd hu (Finset.notMem_empty u)
        · rfl
      by_cases heq : v = u
      · subst heq
        exact ⟨r, Finset.mem_filter.mpr ⟨mem_reach_self ch hdec r, hPr⟩, hu⟩
      · rcases ih u (hdec r u hu) v hvu heq with ⟨w, hw, hvw⟩
        rcases Finset.mem_filter.mp hw with ⟨hwu, hPw⟩
        exact ⟨w, Finset.mem_filter.mpr ⟨reach_sub_of_mem_ch ch hdec r u hu hwu, hPw⟩, hvw⟩

private lemma leaf_count_le (ch : ℕ → Finset ℕ) (hdec : ∀ w v, v ∈ ch w → v < w)
    (P : ℕ → Bool)
    (hchP : ∀ w, P w = false → ch w = ∅)
    (hcard : ∀ w, (ch w).card ≤ 2)
    (r : ℕ) (hr : P r = true) :
    ((reach ch hdec r).filter (fun w => P w = false)).card ≤
      ((reach ch hdec r).filter (fun w => P w = true)).card + 1 := by
  set R := reach ch hdec r
  set W := R.filter (fun w => P w = true)
  set L := R.filter (fun w => P w = false)
  have hrW : r ∈ W := Finset.mem_filter.mpr ⟨mem_reach_self ch hdec r, hr⟩
  have hdisj : Disjoint (W.erase r) L := by
    rw [Finset.disjoint_left]
    intro x hxW hxL
    have h1 : P x = true := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hxW)).2
    have h2 : P x = false := (Finset.mem_filter.mp hxL).2
    rw [h1] at h2
    cases h2
  have hsub : W.erase r ∪ L ⊆ W.biUnion ch := by
    intro v hv
    have hvR : v ∈ R := by
      rcases Finset.mem_union.mp hv with h1 | h2
      · exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase h1)).1
      · exact (Finset.mem_filter.mp h2).1
    have hne : v ≠ r := by
      rcases Finset.mem_union.mp hv with h1 | h2
      · exact (Finset.mem_erase.mp h1).1
      · intro hvr
        subst hvr
        have h2' : P v = false := (Finset.mem_filter.mp h2).2
        rw [hr] at h2'
        cases h2'
    rcases reach_has_parent ch hdec P hchP r v hvR hne with ⟨w, hw, hvw⟩
    exact Finset.mem_biUnion.mpr ⟨w, hw, hvw⟩
  have h1 : (W.erase r).card + L.card ≤ (W.biUnion ch).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  have h2 : (W.biUnion ch).card ≤ 2 * W.card := by
    calc (W.biUnion ch).card
        ≤ ∑ w ∈ W, (ch w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ W, 2 := Finset.sum_le_sum fun w _ => hcard w
      _ = 2 * W.card := by simp [Nat.mul_comm]
  have h3 : (W.erase r).card + 1 = W.card := Finset.card_erase_add_one hrW
  omega

private def chTrue (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) : Finset ℕ :=
  if isPriv C n Si w && lab C n Si w then
    let u := gateInput0 C n w
    let v := gateInput1 C n w
    if gateIsAnd C n w then
      (if u < w then {u} else ∅) ∪ (if v < w then {v} else ∅)
    else
      if u < w ∧ lab C n Si u = true then {u}
      else if v < w ∧ lab C n Si v = true then {v}
      else ∅
  else ∅

private lemma chTrue_dec (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w x : ℕ)
    (hx : x ∈ chTrue C n Si w) : x < w := by
  unfold chTrue at hx
  by_cases h1 : (isPriv C n Si w && lab C n Si w) = true
  · simp only [h1, ↓reduceIte] at hx
    by_cases h2 : gateIsAnd C n w = true
    · simp only [h2, ↓reduceIte, Finset.mem_union] at hx
      rcases hx with hu | hv
      · by_cases hlt : gateInput0 C n w < w
        · simp only [hlt, ↓reduceIte, Finset.mem_singleton] at hu; omega
        · simp [hlt] at hu
      · by_cases hlt : gateInput1 C n w < w
        · simp only [hlt, ↓reduceIte, Finset.mem_singleton] at hv; omega
        · simp [hlt] at hv
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hx
      by_cases ha : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = true
      · simp [ha] at hx; omega
      · simp only [ha, ↓reduceIte] at hx
        by_cases hb : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = true
        · simp [hb] at hx; omega
        · simp [hb] at hx
  · simp [h1] at hx

private lemma chTrue_card (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    (chTrue C n Si w).card ≤ 2 := by
  unfold chTrue
  by_cases h1 : (isPriv C n Si w && lab C n Si w) = true
  · simp only [h1, ↓reduceIte]
    by_cases h2 : gateIsAnd C n w = true
    · simp only [h2, ↓reduceIte]
      have ha : (if gateInput0 C n w < w then ({gateInput0 C n w} : Finset ℕ) else ∅).card ≤ 1 := by
        by_cases hlt : gateInput0 C n w < w <;> simp [hlt]
      have hb : (if gateInput1 C n w < w then ({gateInput1 C n w} : Finset ℕ) else ∅).card ≤ 1 := by
        by_cases hlt : gateInput1 C n w < w <;> simp [hlt]
      exact (Finset.card_union_le _ _).trans (by omega)
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases ha : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = true
      · simp [ha]
      · by_cases hb : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = true <;> simp [ha, hb]
  · simp [h1]

private lemma chTrue_exit (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ)
    (hnp : isPriv C n Si w = false) : chTrue C n Si w = ∅ := by
  simp [chTrue, hnp]

private lemma reach_chTrue_lab (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) :
    ∀ w x, lab C n Si w = true → x ∈ reach (chTrue C n Si) (chTrue_dec C n Si) w →
      lab C n Si x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x hlw hx
    rw [reach_eq] at hx
    rcases Finset.mem_insert.mp hx with rfl | hmem
    · exact hlw
    · rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hxu⟩
      have hlu : lab C n Si u = true := by
        cases hpriv : isPriv C n Si w
        · rw [chTrue_exit C n Si w hpriv] at hu
          exact absurd hu (Finset.notMem_empty u)
        · have hlab := lab_eq_priv C n Si w hpriv
          rw [hlw] at hlab
          unfold chTrue at hu
          simp only [hpriv, hlw, Bool.and_self, ↓reduceIte] at hu
          by_cases hand : gateIsAnd C n w = true
          · simp only [hand, ↓reduceIte] at hu hlab
            have hboth := Bool.and_eq_true_iff.mp hlab.symm
            have h1 : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = true := by
              by_cases hlt : gateInput0 C n w < w
              · exact ⟨hlt, by simpa [hlt] using hboth.1⟩
              · simp [hlt] at hboth
            have h2 : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = true := by
              by_cases hlt : gateInput1 C n w < w
              · exact ⟨hlt, by simpa [hlt] using hboth.2⟩
              · simp [hlt] at hboth
            simp only [h1.1, h2.1, ↓reduceIte, Finset.mem_union, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact h1.2
            · exact h2.2
          · simp only [hand, Bool.false_eq_true, ↓reduceIte] at hu
            by_cases ha : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = true
            · simp [ha] at hu; subst hu; exact ha.2
            · simp only [ha, ↓reduceIte] at hu
              by_cases hb : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = true
              · simp [hb] at hu; subst hu; exact hb.2
              · simp [hb] at hu
      exact ih u (chTrue_dec C n Si w u hu) x hlu hxu

private lemma reach_chTrue_eval (C : Circuit) {n : ℕ} (Si : Finset (Fin n))
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : Fin n → Bool) :
    ∀ w, lab C n Si w = true →
      (∀ z ∈ (reach (chTrue C n Si) (chTrue_dec C n Si) w).filter (fun y => isPriv C n Si y = false),
        wireVal C x z = true) →
      wireVal C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlw hleaves
    cases hpriv : isPriv C n Si w
    · exact hleaves w (Finset.mem_filter.mpr ⟨mem_reach_self _ _ w, hpriv⟩)
    · rcases (isPriv_iff C n Si w).mp hpriv with ⟨hnw, hwlt, _, _⟩
      have hveq := wireVal_gate_eq C x w hnw hwlt hgates
      have hlab := lab_eq_priv C n Si w hpriv
      rw [hlw] at hlab
      rw [hveq]
      by_cases hand : gateIsAnd C n w = true
      · simp only [hand, ↓reduceIte] at hlab ⊢
        have hboth := Bool.and_eq_true_iff.mp hlab.symm
        have h1 : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = true := by
          by_cases hlt : gateInput0 C n w < w
          · exact ⟨hlt, by simpa [hlt] using hboth.1⟩
          · simp [hlt] at hboth
        have h2 : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = true := by
          by_cases hlt : gateInput1 C n w < w
          · exact ⟨hlt, by simpa [hlt] using hboth.2⟩
          · simp [hlt] at hboth
        have hmem1 : gateInput0 C n w ∈ chTrue C n Si w := by
          simp [chTrue, hpriv, hlw, hand, h1.1]
        have hmem2 : gateInput1 C n w ∈ chTrue C n Si w := by
          simp [chTrue, hpriv, hlw, hand, h2.1]
        have hev1 : wireVal C x (gateInput0 C n w) = true :=
          ih (gateInput0 C n w) h1.1 h1.2 fun z hz =>
            hleaves z (Finset.mem_filter.mpr
              ⟨reach_sub_of_mem_ch _ _ w _ hmem1 (Finset.mem_filter.mp hz).1,
                (Finset.mem_filter.mp hz).2⟩)
        have hev2 : wireVal C x (gateInput1 C n w) = true :=
          ih (gateInput1 C n w) h2.1 h2.2 fun z hz =>
            hleaves z (Finset.mem_filter.mpr
              ⟨reach_sub_of_mem_ch _ _ w _ hmem2 (Finset.mem_filter.mp hz).1,
                (Finset.mem_filter.mp hz).2⟩)
        simp [h1.1, h2.1, hev1, hev2]
      · simp only [hand, Bool.false_eq_true, ↓reduceIte] at hlab ⊢
        have hor := Bool.or_eq_true_iff.mp hlab.symm
        by_cases h1 : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = true
        · have hmem1 : gateInput0 C n w ∈ chTrue C n Si w := by
            simp [chTrue, hpriv, hlw, hand, h1]
          have hev1 : wireVal C x (gateInput0 C n w) = true :=
            ih (gateInput0 C n w) h1.1 h1.2 fun z hz =>
              hleaves z (Finset.mem_filter.mpr
                ⟨reach_sub_of_mem_ch _ _ w _ hmem1 (Finset.mem_filter.mp hz).1,
                  (Finset.mem_filter.mp hz).2⟩)
          simp [h1.1, hev1]
        · have h2 : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = true := by
            rcases hor with hl | hr
            · exfalso
              by_cases hlt : gateInput0 C n w < w
              · exact h1 ⟨hlt, by simpa [hlt] using hl⟩
              · simp [hlt] at hl
            · by_cases hlt : gateInput1 C n w < w
              · exact ⟨hlt, by simpa [hlt] using hr⟩
              · simp [hlt] at hr
          have hmem2 : gateInput1 C n w ∈ chTrue C n Si w := by
            simp [chTrue, hpriv, hlw, hand, h1, h2]
          have hev2 : wireVal C x (gateInput1 C n w) = true :=
            ih (gateInput1 C n w) h2.1 h2.2 fun z hz =>
              hleaves z (Finset.mem_filter.mpr
                ⟨reach_sub_of_mem_ch _ _ w _ hmem2 (Finset.mem_filter.mp hz).1,
                  (Finset.mem_filter.mp hz).2⟩)
          simp [h2.1, hev2]

private def chFalse (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) : Finset ℕ :=
  if isPriv C n Si w && !lab C n Si w then
    let u := gateInput0 C n w
    let v := gateInput1 C n w
    if gateIsAnd C n w then
      if u < w ∧ lab C n Si u = false then {u}
      else if v < w ∧ lab C n Si v = false then {v}
      else ∅
    else
      (if u < w then {u} else ∅) ∪ (if v < w then {v} else ∅)
  else ∅

private lemma chFalse_dec (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w x : ℕ)
    (hx : x ∈ chFalse C n Si w) : x < w := by
  unfold chFalse at hx
  by_cases h1 : (isPriv C n Si w && !lab C n Si w) = true
  · simp only [h1, ↓reduceIte] at hx
    by_cases h2 : gateIsAnd C n w = true
    · simp only [h2, ↓reduceIte] at hx
      by_cases ha : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = false
      · simp [ha] at hx; omega
      · simp only [ha, ↓reduceIte] at hx
        by_cases hb : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = false
        · simp [hb] at hx; omega
        · simp [hb] at hx
    · simp only [h2, Bool.false_eq_true, ↓reduceIte, Finset.mem_union] at hx
      rcases hx with hu | hv
      · by_cases hlt : gateInput0 C n w < w
        · simp only [hlt, ↓reduceIte, Finset.mem_singleton] at hu; omega
        · simp [hlt] at hu
      · by_cases hlt : gateInput1 C n w < w
        · simp only [hlt, ↓reduceIte, Finset.mem_singleton] at hv; omega
        · simp [hlt] at hv
  · simp [h1] at hx

private lemma chFalse_card (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    (chFalse C n Si w).card ≤ 2 := by
  unfold chFalse
  by_cases h1 : (isPriv C n Si w && !lab C n Si w) = true
  · simp only [h1, ↓reduceIte]
    by_cases h2 : gateIsAnd C n w = true
    · simp only [h2, ↓reduceIte]
      by_cases ha : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = false
      · simp [ha]
      · by_cases hb : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = false <;> simp [ha, hb]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      have ha : (if gateInput0 C n w < w then ({gateInput0 C n w} : Finset ℕ) else ∅).card ≤ 1 := by
        by_cases hlt : gateInput0 C n w < w <;> simp [hlt]
      have hb : (if gateInput1 C n w < w then ({gateInput1 C n w} : Finset ℕ) else ∅).card ≤ 1 := by
        by_cases hlt : gateInput1 C n w < w <;> simp [hlt]
      exact (Finset.card_union_le _ _).trans (by omega)
  · simp [h1]

private lemma chFalse_exit (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ)
    (hnp : isPriv C n Si w = false) : chFalse C n Si w = ∅ := by
  simp [chFalse, hnp]

private lemma reach_chFalse_lab (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) :
    ∀ w x, lab C n Si w = false → x ∈ reach (chFalse C n Si) (chFalse_dec C n Si) w →
      lab C n Si x = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x hlw hx
    rw [reach_eq] at hx
    rcases Finset.mem_insert.mp hx with rfl | hmem
    · exact hlw
    · rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hxu⟩
      have hlu : lab C n Si u = false := by
        cases hpriv : isPriv C n Si w
        · rw [chFalse_exit C n Si w hpriv] at hu
          exact absurd hu (Finset.notMem_empty u)
        · have hlab := lab_eq_priv C n Si w hpriv
          rw [hlw] at hlab
          unfold chFalse at hu
          simp only [hpriv, hlw, Bool.not_false, Bool.and_self, ↓reduceIte] at hu
          by_cases hand : gateIsAnd C n w = true
          · simp only [hand, ↓reduceIte] at hu
            by_cases ha : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = false
            · simp [ha] at hu; subst hu; exact ha.2
            · simp only [ha, ↓reduceIte] at hu
              by_cases hb : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = false
              · simp [hb] at hu; subst hu; exact hb.2
              · simp [hb] at hu
          · simp only [hand, Bool.false_eq_true, ↓reduceIte] at hu hlab
            have hboth := Bool.or_eq_false_iff.mp hlab.symm
            rcases Finset.mem_union.mp hu with h0 | h0
            · by_cases hlt : gateInput0 C n w < w
              · simp only [hlt, ↓reduceIte, Finset.mem_singleton] at h0; subst h0
                simpa [hlt] using hboth.1
              · simp [hlt] at h0
            · by_cases hlt : gateInput1 C n w < w
              · simp only [hlt, ↓reduceIte, Finset.mem_singleton] at h0; subst h0
                simpa [hlt] using hboth.2
              · simp [hlt] at h0
      exact ih u (chFalse_dec C n Si w u hu) x hlu hxu

private lemma reach_chFalse_cover (C : Circuit) {n : ℕ} (Si : Finset (Fin n))
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w, lab C n Si w = false →
      singleSet C n w ⊆
        ((reach (chFalse C n Si) (chFalse_dec C n Si) w).filter (fun y => isPriv C n Si y = false)).biUnion
          (singleSet C n) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlw a ha
    cases hpriv : isPriv C n Si w
    · exact Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_filter.mpr ⟨mem_reach_self _ _ w, hpriv⟩, ha⟩
    · rcases (isPriv_iff C n Si w).mp hpriv with ⟨hnw, hwlt, _, _⟩
      have ha_val : wireVal C (unitInput a) w = true := (Finset.mem_filter.mp ha).2
      have hveq := wireVal_gate_eq C (unitInput a) w hnw hwlt hgates
      rw [ha_val] at hveq
      have hlab := lab_eq_priv C n Si w hpriv
      rw [hlw] at hlab
      by_cases hand : gateIsAnd C n w = true
      · simp only [hand, ↓reduceIte] at hveq hlab
        have hboth_val := Bool.and_eq_true_iff.mp hveq.symm
        have hu_lt : gateInput0 C n w < w := by
          by_contra hge; simp [hge] at hboth_val
        have hv_lt : gateInput1 C n w < w := by
          by_contra hge; simp [hge] at hboth_val
        have hau : a ∈ singleSet C n (gateInput0 C n w) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa [hu_lt] using hboth_val.1⟩
        have hav : a ∈ singleSet C n (gateInput1 C n w) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa [hv_lt] using hboth_val.2⟩
        simp only [hu_lt, hv_lt, ↓reduceIte] at hlab
        have hfl := Bool.and_eq_false_iff.mp hlab.symm
        by_cases h1 : gateInput0 C n w < w ∧ lab C n Si (gateInput0 C n w) = false
        · have hmem1 : gateInput0 C n w ∈ chFalse C n Si w := by
            simp [chFalse, hpriv, hlw, hand, h1]
          have hcov := ih (gateInput0 C n w) h1.1 h1.2 hau
          rcases Finset.mem_biUnion.mp hcov with ⟨z, hz, haz⟩
          exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr
            ⟨reach_sub_of_mem_ch _ _ w _ hmem1 (Finset.mem_filter.mp hz).1,
              (Finset.mem_filter.mp hz).2⟩, haz⟩
        · have h2 : gateInput1 C n w < w ∧ lab C n Si (gateInput1 C n w) = false := by
            rcases hfl with hlu | hlv
            · exact absurd ⟨hu_lt, hlu⟩ h1
            · exact ⟨hv_lt, hlv⟩
          have hmem2 : gateInput1 C n w ∈ chFalse C n Si w := by
            simp [chFalse, hpriv, hlw, hand, h1, h2]
          have hcov := ih (gateInput1 C n w) h2.1 h2.2 hav
          rcases Finset.mem_biUnion.mp hcov with ⟨z, hz, haz⟩
          exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr
            ⟨reach_sub_of_mem_ch _ _ w _ hmem2 (Finset.mem_filter.mp hz).1,
              (Finset.mem_filter.mp hz).2⟩, haz⟩
      · simp only [hand, Bool.false_eq_true, ↓reduceIte] at hveq hlab
        have hboth_f := Bool.or_eq_false_iff.mp hlab.symm
        rcases Bool.or_eq_true_iff.mp hveq.symm with hl | hr
        · have hu_lt : gateInput0 C n w < w := by
            by_contra hge; simp [hge] at hl
          have hlu : lab C n Si (gateInput0 C n w) = false := by simpa [hu_lt] using hboth_f.1
          have hau : a ∈ singleSet C n (gateInput0 C n w) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa [hu_lt] using hl⟩
          have hmem1 : gateInput0 C n w ∈ chFalse C n Si w := by
            simp [chFalse, hpriv, hlw, hand, hu_lt]
          have hcov := ih (gateInput0 C n w) hu_lt hlu hau
          rcases Finset.mem_biUnion.mp hcov with ⟨z, hz, haz⟩
          exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr
            ⟨reach_sub_of_mem_ch _ _ w _ hmem1 (Finset.mem_filter.mp hz).1,
              (Finset.mem_filter.mp hz).2⟩, haz⟩
        · have hv_lt : gateInput1 C n w < w := by
            by_contra hge; simp [hge] at hr
          have hlv : lab C n Si (gateInput1 C n w) = false := by simpa [hv_lt] using hboth_f.2
          have hav : a ∈ singleSet C n (gateInput1 C n w) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa [hv_lt] using hr⟩
          have hmem2 : gateInput1 C n w ∈ chFalse C n Si w := by
            simp [chFalse, hpriv, hlw, hand, hv_lt]
          have hcov := ih (gateInput1 C n w) hv_lt hlv hav
          rcases Finset.mem_biUnion.mp hcov with ⟨z, hz, haz⟩
          exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr
            ⟨reach_sub_of_mem_ch _ _ w _ hmem2 (Finset.mem_filter.mp hz).1,
              (Finset.mem_filter.mp hz).2⟩, haz⟩

private def privGates (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun j : Fin C.size =>
    singleSet C n (n + j.val) ⊆ Si ∧ 2 ≤ (singleSet C n (n + j.val)).card)

private lemma privFilter_card_le (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (R : Finset ℕ) :
    (R.filter (fun w => isPriv C n Si w = true)).card ≤ (privGates C n Si).card := by
  by_cases hsz : C.size = 0
  · have hemp : R.filter (fun w => isPriv C n Si w = true) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rcases (isPriv_iff C n Si w).mp (Finset.mem_filter.mp hw).2 with ⟨h1, h2, _, _⟩
      omega
    rw [hemp]
    simp
  · have hpos : 0 < C.size := Nat.pos_of_ne_zero hsz
    let g : ℕ → Fin C.size := fun w =>
      if h : n ≤ w ∧ w < n + C.size then ⟨w - n, by omega⟩ else ⟨0, hpos⟩
    have hmaps : ∀ w ∈ R.filter (fun y => isPriv C n Si y = true), g w ∈ privGates C n Si := by
      intro w hw
      rcases (isPriv_iff C n Si w).mp (Finset.mem_filter.mp hw).2 with ⟨h1, h2, h3, h4⟩
      have hgw : g w = ⟨w - n, by omega⟩ := by simp [g, h1, h2]
      rw [hgw]
      have hadd : n + (w - n) = w := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hadd] using h3, by simpa [hadd] using h4⟩
    have hinj : Set.InjOn g ↑(R.filter (fun y => isPriv C n Si y = true)) := by
      intro w1 hw1 w2 hw2 heq
      rcases (isPriv_iff C n Si w1).mp (Finset.mem_filter.mp hw1).2 with ⟨h11, h12, _, _⟩
      rcases (isPriv_iff C n Si w2).mp (Finset.mem_filter.mp hw2).2 with ⟨h21, h22, _, _⟩
      simp only [g, h11, h12, h21, h22, and_self, ↓reduceDIte, Fin.mk.injEq] at heq
      omega
    exact Finset.card_le_card_of_injOn g hmaps hinj

private lemma per_output_bound (n k : ℕ) (Si : Finset (Fin n)) (C : Circuit)
    (oi ci : ℕ)
    (h2 : 2 ≤ (singleSet C n oi).card)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hsub : singleSet C n oi ⊆ Si)
    (hprom : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ Si, x q = false) → wireVal C x oi = false)
    (hck : ci ≤ k)
    (hcA : ci + 1 ≤ (singleSet C n oi).card) :
    ci ≤ (privGates C n Si).card := by
  have hge : n ≤ oi := by
    by_contra hlt
    have := singleSet_lt_card C n oi (Nat.lt_of_not_ge hlt)
    omega
  have hlt : oi < n + C.size := by
    by_contra hge2
    have := singleSet_ge_card C n oi (Nat.le_of_not_lt hge2)
    omega
  have hpriv : isPriv C n Si oi = true := (isPriv_iff C n Si oi).mpr ⟨hge, hlt, hsub, h2⟩
  cases hlab : lab C n Si oi with
  | true =>
    set R := reach (chTrue C n Si) (chTrue_dec C n Si) oi
    set W := R.filter (fun w => isPriv C n Si w = true)
    set L := R.filter (fun w => isPriv C n Si w = false)
    have hLle : L.card ≤ W.card + 1 :=
      leaf_count_le (chTrue C n Si) (chTrue_dec C n Si) (isPriv C n Si)
        (chTrue_exit C n Si) (chTrue_card C n Si) oi hpriv
    have hWle : W.card ≤ (privGates C n Si).card := privFilter_card_le C n Si R
    have hex : ∀ z ∈ L, ∃ q : Fin n, q ∈ singleSet C n z ∧ q ∉ Si := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzR, hnp⟩
      have hlz : lab C n Si z = true := reach_chTrue_lab C n Si oi z hlab hzR
      rw [lab_eq_exit C n Si z hnp, decide_eq_true_eq] at hlz
      rw [Finset.not_subset] at hlz
      exact hlz
    classical
    let pick : ℕ → Finset (Fin n) := fun z =>
      if h : ∃ q : Fin n, q ∈ singleSet C n z ∧ q ∉ Si then {Classical.choose h} else ∅
    let X : Finset (Fin n) := L.biUnion pick
    let x : Fin n → Bool := fun q => decide (q ∈ X)
    have hXcard : X.card ≤ L.card := by
      calc X.card
          ≤ ∑ z ∈ L, (pick z).card := Finset.card_biUnion_le
        _ ≤ ∑ _z ∈ L, 1 := Finset.sum_le_sum fun z _ => by
            dsimp [pick]
            split_ifs <;> simp
        _ = L.card := by simp
    have hXdisj : ∀ q ∈ Si, x q = false := by
      intro q hq
      simp only [x, decide_eq_false_iff_not]
      intro hqX
      rcases Finset.mem_biUnion.mp hqX with ⟨z, _, hqp⟩
      dsimp [pick] at hqp
      split_ifs at hqp with h
      · simp only [Finset.mem_singleton] at hqp
        subst hqp
        exact (Classical.choose_spec h).2 hq
      · exact Finset.notMem_empty q hqp
    have hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g hg => (hgates g hg).1
    have hval_leaves : ∀ z ∈ L, wireVal C x z = true := by
      intro z hz
      have h := hex z hz
      let q := Classical.choose h
      have hqspec := Classical.choose_spec h
      have hqX : q ∈ X := by
        refine Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩
        simp [pick, h, q]
      have hunit : wireVal C (unitInput q) z = true := (Finset.mem_filter.mp hqspec.1).2
      apply wireVal_mono C hmono (unitInput q) x _ z hunit
      intro b hb
      simp only [unitInput, decide_eq_true_eq] at hb
      subst hb
      simp [x, hqX]
    have hoi_true : wireVal C x oi = true :=
      reach_chTrue_eval C Si hgates x oi hlab hval_leaves
    have hxcard_eq : (Finset.univ.filter (fun q : Fin n => x q = true)).card = X.card := by
      congr 1
      ext q
      simp [x]
    have hklt : k < X.card := by
      by_contra hle
      have hle' : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k := by
        rw [hxcard_eq]
        exact Nat.le_of_not_lt hle
      have hf := hprom x hle' hXdisj
      rw [hoi_true] at hf
      cases hf
    omega
  | false =>
    set R := reach (chFalse C n Si) (chFalse_dec C n Si) oi
    set W := R.filter (fun w => isPriv C n Si w = true)
    set L := R.filter (fun w => isPriv C n Si w = false)
    have hLle : L.card ≤ W.card + 1 :=
      leaf_count_le (chFalse C n Si) (chFalse_dec C n Si) (isPriv C n Si)
        (chFalse_exit C n Si) (chFalse_card C n Si) oi hpriv
    have hWle : W.card ≤ (privGates C n Si).card := privFilter_card_le C n Si R
    have hcov : singleSet C n oi ⊆ L.biUnion (singleSet C n) :=
      reach_chFalse_cover C Si hgates oi hlab
    have hsmall : ∀ z ∈ L, (singleSet C n z).card ≤ 1 := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzR, hnp⟩
      have hlz : lab C n Si z = false := reach_chFalse_lab C n Si oi z hlab hzR
      rw [lab_eq_exit C n Si z hnp, decide_eq_false_iff_not, not_not] at hlz
      by_cases hlt1 : z < n
      · exact singleSet_lt_card C n z hlt1
      · by_cases hge2 : n + C.size ≤ z
        · rw [singleSet_ge_card C n z hge2]; omega
        · by_contra hgt
          have hp : isPriv C n Si z = true :=
            (isPriv_iff C n Si z).mpr ⟨Nat.le_of_not_lt hlt1, Nat.lt_of_not_ge hge2, hlz, by omega⟩
          rw [hp] at hnp
          cases hnp
    have hAle : (singleSet C n oi).card ≤ L.card := by
      calc (singleSet C n oi).card
          ≤ (L.biUnion (singleSet C n)).card := Finset.card_le_card hcov
        _ ≤ ∑ z ∈ L, (singleSet C n z).card := Finset.card_biUnion_le
        _ ≤ ∑ _z ∈ L, 1 := Finset.sum_le_sum hsmall
        _ = L.card := by simp
    omega

private lemma privGates_disjoint (C : Circuit) (n m : ℕ) (S : Fin m → Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) (fun i => privGates C n (S i)) := by
  intro i _ j _ hij
  change Disjoint (privGates C n (S i)) (privGates C n (S j))
  rw [Finset.disjoint_left]
  intro g hgi hgj
  have h1 := (Finset.mem_filter.mp hgi).2
  have h2 := (Finset.mem_filter.mp hgj).2
  have hsub : singleSet C n (n + g.val) ⊆ S i ∩ S j :=
    Finset.subset_inter h1.1 h2.1
  have hle := (Finset.card_le_card hsub).trans (hinter i j hij)
  omega

end PEqualNP.Outside.L_meta_782_aux

open PEqualNP.Outside.L_meta_782_aux in
theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hinter h2 hgates hsub hprom hck hcA
  have hper : ∀ i : Fin m, c i ≤ (privGates C n (S i)).card := by
    intro i
    apply per_output_bound n k (S i) C (o i) (c i)
    · exact h2 i
    · exact hgates
    · intro p hp
      exact hsub i p (Finset.mem_filter.mp hp).2
    · exact hprom i
    · exact hck i
    · exact hcA i
  calc ∑ i : Fin m, c i
      ≤ ∑ i : Fin m, (privGates C n (S i)).card := Finset.sum_le_sum fun i _ => hper i
    _ = (Finset.univ.biUnion (fun i : Fin m => privGates C n (S i))).card :=
        (Finset.card_biUnion (privGates_disjoint C n m S hinter)).symm
    _ ≤ (Finset.univ : Finset (Fin C.size)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = C.size := by simp
