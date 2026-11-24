import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1518

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

abbrev Valid (C : Circuit) :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

abbrev Cold {n : ℕ} (C : Circuit) (mark : ℕ) (x : Fin n → Bool) :=
  value C x mark = false

lemma parents_mono {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i = j)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    let i : Fin C.size := ⟨w - n, by omega⟩
    ∃ P : Finset ℕ, P.card ≤ 2 ∧
      (n + j.val ∈ (C.gates.get i).inputs → P.card ≤ 1) ∧ (∀ r ∈ P, r < w) ∧
      ∀ x y : Fin n → Bool, Cold C (n + j.val) x → Cold C (n + j.val) y →
        (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let i : Fin C.size := ⟨w - n, by omega⟩
  let g := C.gates.get i
  obtain ⟨hop, hlen⟩ := valid g (List.get_mem ..)
  let mark := n + j.val
  let P := (g.inputs.toFinset.erase mark).filter (· < w)
  have bound := Finset.card_filter_le (g.inputs.toFinset.erase mark) (· < w)
  have max := List.toFinset_card_le g.inputs |>.trans hlen
  refine ⟨P, bound.trans ((Finset.card_le_card (Finset.erase_subset ..)).trans max), ?_, ?_, ?_⟩
  · intro read
    have h : mark ∈ g.inputs.toFinset := List.mem_toFinset.mpr read
    have e := Finset.card_erase_add_one h
    change P.card ≤ 1
    change P.card ≤ _ at bound
    omega
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y cx cy step hx
    rcases hop with hop | hop | hop
    all_goals try
      have same : w = n + j.val := by
        have e := congrArg Fin.val (unique i hop)
        change w - n = j.val at e
        omega
      rw [same] at hx
      exact (Bool.false_ne_true (cx.symm.trans hx)).elim
    all_goals
      have hr (r : ℕ) (hin : r ∈ g.inputs) :
          (if r < w then value C x r else false) = true →
          (if r < w then value C y r else false) = true := by
        by_cases lt : r < w
        · by_cases eq : r = mark
          · subst r; simp [lt, mark, cx]
          · simpa only [ite_eq_left lt] using step r
              (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨eq, List.mem_toFinset.mpr hin⟩, lt⟩)
        · simp [lt]
      have gx := gate_value C x w hn hw
      have gy := gate_value C y w hn hw
      change value C x w = g.op.eval _ at gx
      change value C y w = g.op.eval _ at gy
      rw [gx] at hx
      rw [gy]
    · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
      exact fun z hz => hr z hz (hx z hz)
    · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
      obtain ⟨z, hz, yes⟩ := hx
      exact ⟨z, hz, hr z hz yes⟩

lemma mono {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i = j)
    (x y : Fin n → Bool) (cx : Cold C (n + j.val) x) (cy : Cold C (n + j.val) y)
    (le : ∀ p, x p = true → y p = true) (w : ℕ) : value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases small : w < n
    · let p : Fin n := ⟨w, small⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using le p
    by_cases end' : w < n + C.size
    · obtain ⟨P, _, _, lt, step⟩ := parents_mono C valid j unique w (by omega) end'
      exact step x y cx cy fun r hr => ih r (lt r hr)
    · simp [missing_value C x w (by omega)]

theorem row_mono {n : ℕ} (gs : List Gate) (j : Fin gs.length)
    (valid : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (unique : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (x y : Fin n → Bool)
    (cx : (Circuit.mk gs (n + j.val)).eval (List.ofFn x) = false)
    (cy : (Circuit.mk gs (n + j.val)).eval (List.ofFn y) = false)
    (le : ∀ v, x v = true → y v = true) (w : ℕ) :
    (Circuit.mk gs w).eval (List.ofFn x) = true → (Circuit.mk gs w).eval (List.ofFn y) = true :=
  mono ⟨gs, w⟩ valid j unique x y cx cy le w

lemma mono_lt {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i = j)
    (x y : Fin n → Bool) (le : ∀ p, x p = true → y p = true) (w : ℕ) (hw : w < n + j.val) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases small : w < n
    · let p : Fin n := ⟨w, small⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using le p
    · have end' : w < n + C.size := by have := j.isLt; omega
      let i : Fin C.size := ⟨w - n, by omega⟩
      let g := C.gates.get i
      obtain ⟨hop, _⟩ := valid g (List.get_mem ..)
      have hnot : g.op ≠ GateOp.not := by
        intro hn
        have e := congrArg Fin.val (unique i hn)
        change w - n = j.val at e
        omega
      have hr (r : ℕ) (hin : r ∈ g.inputs) :
          (if r < w then value C x r else false) = true →
          (if r < w then value C y r else false) = true := by
        by_cases lt : r < w
        · simpa only [ite_eq_left lt] using ih r lt (by omega)
        · simp [lt]
      intro hx
      have gx := gate_value C x w (by omega) end'
      have gy := gate_value C y w (by omega) end'
      change value C x w = g.op.eval _ at gx
      change value C y w = g.op.eval _ at gy
      rw [gx] at hx
      rw [gy]
      rcases hop with hop | hop | hop
      · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
        exact fun z hz => hr z hz (hx z hz)
      · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
        obtain ⟨z, hz, yes⟩ := hx
        exact ⟨z, hz, hr z hz yes⟩
      · exact False.elim (hnot hop)

lemma not_eval_eq (gates : List Gate) (j h : Fin gates.length)
    (hop : (gates.get j).op = GateOp.not) (hhj : h < j)
    (hin : ∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r)
    (x : Fin 13 → Bool) :
    Circuit.eval ⟨gates, 13 + (j : ℕ)⟩ (List.ofFn x) =
      !(Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn x)) := by
  let C : Circuit := ⟨gates, 0⟩
  have hlt : 13 + j.val < 13 + C.size := by change 13 + j.val < 13 + gates.length; omega
  have gv := gate_value C x (13 + j.val) (by omega) hlt
  change value C x (13 + j.val) = _ at gv
  obtain ⟨r, hr⟩ := hin
  have hget : C.gates[13 + j.val - 13]'(by unfold Circuit.size at hlt; omega) = gates.get j := by
    simp [C]
  rw [hget, hop, hr] at gv
  have hhj' : 13 + (h : ℕ) < 13 + j.val := by
    change h.val < j.val at hhj
    omega
  simp only [GateOp.eval, List.map_cons, ite_eq_left hhj', List.headD_cons] at gv
  exact gv

lemma parents_neg {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i = j)
    (neg : Fin n → Bool) (_cneg : Cold C (n + j.val) neg)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (vw : value C neg w = false) :
    let i : Fin C.size := ⟨w - n, by omega⟩
    ∃ P : Finset ℕ, P.card ≤ 2 ∧
      ((C.gates.get i).op ≠ GateOp.or ∨ n + j.val ∈ (C.gates.get i).inputs → P.card ≤ 1) ∧
      (∀ r ∈ P, r < w) ∧
      ∀ x : Fin n → Bool, Cold C (n + j.val) x →
        (∀ r ∈ P, value C x r = true → value C neg r = true) →
        value C x w = true → value C neg w = true := by
  let i : Fin C.size := ⟨w - n, by omega⟩
  let g := C.gates.get i
  obtain ⟨hop, hlen⟩ := valid g (List.get_mem ..)
  rcases hop with hop | hop | hop
  · have gx := gate_value C neg w hn hw
    change value C neg w = g.op.eval (g.inputs.map fun r => if r < w then value C neg r else false) at gx
    rw [vw, hop] at gx
    have hex : ∃ r0 ∈ g.inputs, (if r0 < w then value C neg r0 else false) = false := by
      by_contra! hall
      have htrue : (g.inputs.map fun r => if r < w then value C neg r else false).all id = true :=
        List.all_eq_true.mpr (by simpa using fun r hr => Bool.eq_true_of_not_eq_false (hall r hr))
      change false = (g.inputs.map fun r => if r < w then value C neg r else false).all id at gx
      rw [htrue] at gx
      exact Bool.false_ne_true gx
    obtain ⟨r0, hr0, hfalse⟩ := hex
    by_cases hlt : r0 < w
    · refine ⟨{r0}, by simp, fun _ => by simp, fun r hr => by simpa [Finset.mem_singleton.mp hr] using hlt, ?_⟩
      intro x _ step hx
      have gx' := gate_value C x w hn hw
      change value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) at gx'
      rw [hx, hop] at gx'
      change true = (g.inputs.map fun r => if r < w then value C x r else false).all id at gx'
      have hxall : ∀ r ∈ g.inputs, (if r < w then value C x r else false) = true := fun r hr =>
        (List.all_eq_true.mp gx'.symm) _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      have hxr0 := hxall r0 hr0
      rw [ite_eq_left hlt] at hxr0
      have hnr0 := step r0 (Finset.mem_singleton_self r0) hxr0
      rw [ite_eq_left hlt, hnr0] at hfalse
      exact Bool.noConfusion hfalse
    · refine ⟨∅, by simp, fun _ => by simp, fun _ hr => by simp at hr, ?_⟩
      intro x _ _ hx
      have gx' := gate_value C x w hn hw
      change value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) at gx'
      rw [hx, hop] at gx'
      change true = (g.inputs.map fun r => if r < w then value C x r else false).all id at gx'
      have hxall : ∀ r ∈ g.inputs, (if r < w then value C x r else false) = true := fun r hr =>
        (List.all_eq_true.mp gx'.symm) _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      have hxr0 := hxall r0 hr0
      rw [ite_eq_right hlt] at hxr0
      exact Bool.noConfusion hxr0
  · let mark := n + j.val
    let P := (g.inputs.toFinset.erase mark).filter (· < w)
    have bound := Finset.card_filter_le (g.inputs.toFinset.erase mark) (· < w)
    have max := List.toFinset_card_le g.inputs |>.trans hlen
    refine ⟨P, bound.trans ((Finset.card_le_card (Finset.erase_subset ..)).trans max), ?_, ?_, ?_⟩
    · intro hcond
      rcases hcond with hne | read
      · exact False.elim (hne hop)
      · have h : mark ∈ g.inputs.toFinset := List.mem_toFinset.mpr read
        have e := Finset.card_erase_add_one h
        change P.card ≤ 1
        change P.card ≤ _ at bound
        omega
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro x cx step hx
      have gx := gate_value C x w hn hw
      have gy := gate_value C neg w hn hw
      change value C x w = g.op.eval _ at gx
      change value C neg w = g.op.eval _ at gy
      rw [gx, hop] at hx
      rw [gy, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
      obtain ⟨z, hz, yes⟩ := hx
      by_cases lt : z < w
      · rw [ite_eq_left lt] at yes
        by_cases eq : z = mark
        · subst z
          exfalso
          exact Bool.false_ne_true (cx.symm.trans yes)
        · refine ⟨z, hz, ?_⟩
          rw [ite_eq_left lt]
          exact step z (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨eq, List.mem_toFinset.mpr hz⟩, lt⟩) yes
      · rw [ite_eq_right lt] at yes
        exact Bool.noConfusion yes
  · have same : w = n + j.val := by
      have e := congrArg Fin.val (unique i hop)
      change w - n = j.val at e
      omega
    refine ⟨∅, by simp, fun _ => by simp, fun _ hr => by simp at hr, ?_⟩
    intro x cx _ hx
    rw [same] at hx
    exact False.elim (Bool.false_ne_true (cx.symm.trans hx))

lemma cut_neg {n : ℕ} (C : Circuit) (mark : ℕ) (neg : Fin n → Bool) (G paid : Finset ℕ)
    (parents : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ paid → P.card ≤ 1) ∧
      (∀ r ∈ P, r < w) ∧ ∀ x : Fin n → Bool, Cold C mark x →
        (∀ r ∈ P, value C x r = true → value C neg r = true) → value C x w = true → value C neg w = true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + ((G ∩ paid).filter (· < t)).card ∧
      ∀ x : Fin n → Bool, Cold C mark x →
        (∀ w ∈ B, value C x w = true → value C neg w = true) →
        ∀ w ∈ F, value C x w = true → value C neg w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    have increases : ((G ∩ paid).filter (· < t)).card ≤ ((G ∩ paid).filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases expand : t ∈ F ∧ t ∈ G
    · obtain ⟨P, lim, free, lt, step⟩ := parents t expand.2
      let F' := F.erase t ∪ P
      have smaller : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have ne := (Finset.mem_erase.mp hw).1
          have := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact lt w hw
      obtain ⟨B, dis, size, chains⟩ := ih F' smaller
      refine ⟨B, dis, ?_, ?_⟩
      · have union := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at union
        have old := Finset.card_erase_add_one expand.1
        by_cases hp : t ∈ paid
        · have eq : (G ∩ paid).filter (· < t + 1) = insert t ((G ∩ paid).filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨inc, bound⟩
              by_cases ne : w = t
              · exact Or.inl ne
              · exact Or.inr ⟨inc, by omega⟩
            · rintro (rfl | ⟨inc, bound⟩)
              · exact ⟨Finset.mem_inter.mpr ⟨expand.2, hp⟩, by omega⟩
              · exact ⟨inc, by omega⟩
          rw [eq, Finset.card_insert_of_notMem (by simp)]
          omega
        · have := free hp
          omega
      · intro x cx hxy w hw
        by_cases eq : w = t
        · subst w
          exact step x cx fun r hr => chains x cx hxy r (Finset.mem_union_right _ hr)
        · exact chains x cx hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq, hw⟩))
    · have smaller : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have ne : w ≠ t := fun e => expand ⟨e ▸ hw, e ▸ hg⟩
        have := hF w hw hg
        omega
      obtain ⟨B, dis, size, chains⟩ := ih F smaller
      exact ⟨B, dis, by omega, chains⟩

theorem row_or {n : ℕ} (gs : List Gate) (j : Fin gs.length)
    (valid : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (unique : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (S T : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (o : ℕ)
    (sep : ∀ p ∈ T, R p ∩ S = {p})
    (cneg : (Circuit.mk gs (n + j.val)).eval (List.ofFn (fun v => decide (v ∉ S))) = false)
    (cpos : ∀ p ∈ T, (Circuit.mk gs (n + j.val)).eval (List.ofFn (fun v => decide (v ∈ R p))) = false)
    (hneg : (Circuit.mk gs o).eval (List.ofFn (fun v => decide (v ∉ S))) = false)
    (hpos : ∀ p ∈ T, (Circuit.mk gs o).eval (List.ofFn (fun v => decide (v ∈ R p))) = true) :
    ∃ A : Finset (Fin gs.length), T.card - 1 ≤ A.card ∧ ∀ i ∈ A,
      (gs.get i).op = GateOp.or ∧
      ¬ (j < i ∧ n + j.val ∈ (gs.get i).inputs) ∧
      (Circuit.mk gs (n + i.val)).eval (List.ofFn (fun v => decide (v ∉ S))) = false ∧
      2 ≤ (T.filter (fun p => (Circuit.mk gs (n + i.val)).eval (List.ofFn (fun v => decide (v ∈ R p))) = true)).card := by
  classical
  let C : Circuit := ⟨gs, o⟩
  let neg (v : Fin n) := decide (v ∉ S)
  let pos (p v : Fin n) := decide (v ∈ R p)
  let hits (w : ℕ) := T.filter (fun p => value C (pos p) w = true)
  let clean (w : ℕ) := value C neg w = false ∧ 2 ≤ (hits w).card
  let G := (Finset.Ico n (n + gs.length)).filter clean
  let A := Finset.univ.filter (fun i : Fin gs.length =>
    (gs.get i).op = GateOp.or ∧
    ¬ (j < i ∧ n + j.val ∈ (gs.get i).inputs) ∧ clean (n + i.val))
  let paid := A.image (fun i => n + i.val)
  have isGate (w : ℕ) (c : clean w) : n ≤ w ∧ w < n + gs.length := by
    obtain ⟨zero, big⟩ := c
    constructor
    · by_contra! lt
      let a : Fin n := ⟨w, lt⟩
      have aa : a ∈ S := by
        change value C neg a = false at zero
        simpa [input_value, neg] using zero
      have sub : hits w ⊆ {a} := by
        intro p hp
        obtain ⟨hpt, hw⟩ := Finset.mem_filter.mp hp
        change value C (pos p) a = true at hw
        have yes : a ∈ R p := by simpa [input_value, pos] using hw
        have both : a ∈ R p ∩ S := Finset.mem_inter.mpr ⟨yes, aa⟩
        rw [sep p hpt, Finset.mem_singleton] at both
        simpa only [Finset.mem_singleton] using both.symm
      have bound := Finset.card_le_card sub
      simp only [Finset.card_singleton] at bound
      omega
    · by_contra! high
      have none : hits w = ∅ := by
        ext p
        simp [hits, missing_value C (pos p) w high]
      simp [none] at big
  have step (w : ℕ) (hw : w ∈ G) : ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ paid → P.card ≤ 1) ∧
      (∀ r ∈ P, r < w) ∧ ∀ x : Fin n → Bool, Cold C (n + j.val) x →
        (∀ r ∈ P, value C x r = true → value C neg r = true) → value C x w = true → value C neg w = true := by
    obtain ⟨bounds, c⟩ := Finset.mem_filter.mp hw
    obtain ⟨low, high⟩ := Finset.mem_Ico.mp bounds
    let i : Fin gs.length := ⟨w - n, by omega⟩
    have idx : n + i.val = w := by dsimp [i]; omega
    obtain ⟨P, size, read, less, chain⟩ := parents_neg C valid j unique neg cneg w low high c.1
    refine ⟨P, size, ?_, less, chain⟩
    intro free
    apply read
    by_cases hop : (gs.get i).op = GateOp.or
    · right
      by_contra no
      apply free
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hop, ?_, ?_⟩, idx⟩
      · exact fun e => no e.2
      · rw [idx]
        exact c
    · exact Or.inl hop
  obtain ⟨B, dis, size, chain⟩ := cut_neg C (n + j.val) neg G paid step (n + gs.length) {o}
    (fun w _ hg => (Finset.mem_Ico.mp (Finset.mem_filter.mp hg).1).2)
  let parts (w : ℕ) := if value C neg w = false then hits w else ∅
  have small (w : ℕ) (hb : w ∈ B) : (parts w).card ≤ 1 := by
    by_cases zero : value C neg w = false
    · simp only [parts, ite_eq_left zero]
      by_contra! big
      have c : clean w := ⟨zero, by omega⟩
      exact Finset.disjoint_left.mp dis hb (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (isGate w c), c⟩)
    · simp [parts, zero]
  have cover : T ⊆ B.biUnion parts := by
    intro p hp
    by_contra no
    have implication (w : ℕ) (hb : w ∈ B) (yes : value C (pos p) w = true) : value C neg w = true := by
      cases zero : value C neg w with
      | true => rfl
      | false =>
        exfalso
        exact no (Finset.mem_biUnion.mpr ⟨w, hb, by simp [parts, zero, hits, hp, yes]⟩)
    have bad := chain (pos p) (cpos p hp) implication o (Finset.mem_singleton_self o) (hpos p hp)
    exact Bool.false_ne_true (hneg.symm.trans bad)
  have bound := (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul B parts 1 small)
  have use := (Finset.card_filter_le (G ∩ paid) (· < n + gs.length)).trans
    ((Finset.card_le_card (Finset.inter_subset_right (s₁ := G) (s₂ := paid))).trans Finset.card_image_le)
  simp only [Finset.card_singleton] at size
  simp only [mul_one] at bound
  exact ⟨A, by omega, fun _ hi => (Finset.mem_filter.mp hi).2⟩

def L0 (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

lemma L0_card : ∀ t : Fin 13, (L0 t).card = 4 := by decide

lemma L0_inter : ∀ a b : Fin 13, a ≠ b → (L0 a ∩ L0 b).card ≤ 1 := by decide

def cycRel (t u v a b : Fin 13) : Prop :=
  (a = t ∧ b = u) ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = t)

lemma cycRel_anti (t u v : Fin 13) (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v) :
    ∀ a b : Fin 13, cycRel t u v a b → ¬ cycRel t u v b a := by
  intro a b hab hba
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hba with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact htu h1.symm
  · exact htv h2
  · exact huv h1
  · exact htv h1.symm
  · exact huv h1.symm
  · exact htu h2.symm
  · exact huv h2.symm
  · exact htu h1
  · exact htv h1

def pick (L : Fin 13 → Finset (Fin 13)) (t u v i : Fin 13) : Fin 13 :=
  if t ∈ L i then v else if u ∈ L i then t else if v ∈ L i then u else t

lemma pick_mem_B (L : Fin 13 → Finset (Fin 13)) (t u v i : Fin 13) :
    pick L t u v i ∈ ({t, u, v} : Finset (Fin 13)) := by
  unfold pick
  split_ifs <;> simp

lemma pick_not_mem (L : Fin 13 → Finset (Fin 13)) (s t u v i : Fin 13)
    (htL : t ∈ L s) (_huL : u ∈ L s) (hvL : v ∈ L s)
    (_htu : t ≠ u) (_huv : u ≠ v) (htv : t ≠ v)
    (hint : (L i ∩ L s).card ≤ 1) :
    pick L t u v i ∉ L i := by
  unfold pick
  by_cases ht : t ∈ L i
  · rw [ite_eq_left ht]
    intro hv
    have hsub : ({t, v} : Finset (Fin 13)) ⊆ L i ∩ L s := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨ht, htL⟩
      · exact Finset.mem_inter.mpr ⟨hv, hvL⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair htv] at hc
    omega
  · by_cases hu : u ∈ L i
    · rw [ite_eq_right ht, ite_eq_left hu]
      exact ht
    · by_cases hv : v ∈ L i
      · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_left hv]
        exact hu
      · rw [ite_eq_right ht, ite_eq_right hu, ite_eq_right hv]
        exact ht

lemma pick_cyc (L : Fin 13 → Finset (Fin 13)) (s t u v i : Fin 13)
    (htL : t ∈ L s) (huL : u ∈ L s) (hvL : v ∈ L s)
    (hint : (L i ∩ L s).card ≤ 1) :
    ∀ y ∈ L i ∩ ({t, u, v} : Finset (Fin 13)), cycRel t u v (pick L t u v i) y := by
  intro y hy
  obtain ⟨hyi, hyB⟩ := Finset.mem_inter.mp hy
  have hyS : y ∈ L s := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyB
    rcases hyB with rfl | rfl | rfl <;> assumption
  unfold pick
  by_cases ht : t ∈ L i
  · simp only [ht, ite_true]
    have heq : y = t := by
      by_contra hne
      have hsub : ({t, y} : Finset (Fin 13)) ⊆ L i ∩ L s := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨ht, htL⟩
        · exact Finset.mem_inter.mpr ⟨hyi, hyS⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hne)] at hc
      omega
    subst heq
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · by_cases hu : u ∈ L i
    · simp only [ht, ite_false, hu, ite_true]
      have heq : y = u := by
        by_contra hne
        have hsub : ({u, y} : Finset (Fin 13)) ⊆ L i ∩ L s := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hu, huL⟩
          · exact Finset.mem_inter.mpr ⟨hyi, hyS⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair (Ne.symm hne)] at hc
        omega
      subst heq
      exact Or.inl ⟨rfl, rfl⟩
    · by_cases hv : v ∈ L i
      · simp only [ht, ite_false, hu, hv, ite_true]
        have heq : y = v := by
          by_contra hne
          have hsub : ({v, y} : Finset (Fin 13)) ⊆ L i ∩ L s := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hv, hvL⟩
            · exact Finset.mem_inter.mpr ⟨hyi, hyS⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair (Ne.symm hne)] at hc
          omega
        subst heq
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hyB
        rcases hyB with rfl | rfl | rfl
        · exact False.elim (ht hyi)
        · exact False.elim (hu hyi)
        · exact False.elim (hv hyi)

def T_set (L : Fin 13 → Finset (Fin 13)) (s t u v i : Fin 13) : Finset (Fin 13) :=
  if i = s then {t, u, v} else L i

def R_set (L : Fin 13 → Finset (Fin 13)) (t u v i p : Fin 13) : Finset (Fin 13) :=
  if p ∈ ({t, u, v} : Finset (Fin 13)) then {p} else {p, pick L t u v i}

lemma T_sub_L (L : Fin 13 → Finset (Fin 13)) (s t u v : Fin 13)
    (htL : t ∈ L s) (huL : u ∈ L s) (hvL : v ∈ L s) (i : Fin 13) :
    T_set L s t u v i ⊆ L i := by
  unfold T_set
  split_ifs with h
  · subst h
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  · exact Finset.Subset.refl _

lemma R_sep (L : Fin 13 → Finset (Fin 13)) (s t u v : Fin 13)
    (htL : t ∈ L s) (huL : u ∈ L s) (hvL : v ∈ L s)
    (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v)
    (hinter : ∀ a b : Fin 13, a ≠ b → (L a ∩ L b).card ≤ 1)
    (i : Fin 13) (p : Fin 13) (hp : p ∈ T_set L s t u v i) :
    R_set L t u v i p ∩ L i = {p} := by
  have hpL : p ∈ L i := T_sub_L L s t u v htL huL hvL i hp
  unfold R_set
  split_ifs with hpB
  · exact Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hpL)
  · have his : i ≠ s := by
      intro e
      subst e
      exact hpB (by simpa [T_set] using hp)
    have hnot : pick L t u v i ∉ L i :=
      pick_not_mem L s t u v i htL huL hvL htu huv htv (hinter i s his)
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hyL⟩
      · rfl
      · exact False.elim (hnot hyL)
    · rintro rfl
      exact ⟨Or.inl rfl, hpL⟩

lemma R_has_B (L : Fin 13 → Finset (Fin 13)) (t u v i p : Fin 13) :
    ∃ b ∈ ({t, u, v} : Finset (Fin 13)), b ∈ R_set L t u v i p := by
  unfold R_set
  split_ifs with hpB
  · exact ⟨p, hpB, Finset.mem_singleton_self p⟩
  · exact ⟨pick L t u v i, pick_mem_B L t u v i, by simp⟩

lemma R_separated (L : Fin 13 → Finset (Fin 13)) (s t u v : Fin 13)
    (htL : t ∈ L s) (huL : u ∈ L s) (hvL : v ∈ L s)
    (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v)
    (hinter : ∀ a b : Fin 13, a ≠ b → (L a ∩ L b).card ≤ 1)
    (i₁ i₂ : Fin 13) (_ : i₁ ≠ i₂) :
    ¬ ((∃ p₁ ∈ T_set L s t u v i₁ \ L i₂, (R_set L t u v i₁ p₁ ∩ L i₂).Nonempty) ∧
       (∃ p₂ ∈ T_set L s t u v i₂ \ L i₁, (R_set L t u v i₂ p₂ ∩ L i₁).Nonempty)) := by
  rintro ⟨⟨p₁, hp₁, x₁, hx₁⟩, ⟨p₂, hp₂, x₂, hx₂⟩⟩
  rw [Finset.mem_sdiff] at hp₁ hp₂
  rw [Finset.mem_inter] at hx₁ hx₂
  have hp₁B : p₁ ∉ ({t, u, v} : Finset (Fin 13)) := by
    intro hB
    have hR : R_set L t u v i₁ p₁ = {p₁} := by simp [R_set, hB]
    rw [hR, Finset.mem_singleton] at hx₁
    exact hp₁.2 (hx₁.1 ▸ hx₁.2)
  have hp₂B : p₂ ∉ ({t, u, v} : Finset (Fin 13)) := by
    intro hB
    have hR : R_set L t u v i₂ p₂ = {p₂} := by simp [R_set, hB]
    rw [hR, Finset.mem_singleton] at hx₂
    exact hp₂.2 (hx₂.1 ▸ hx₂.2)
  have hi₁s : i₁ ≠ s := by
    intro e; subst e; exact hp₁B (by simpa [T_set] using hp₁.1)
  have hi₂s : i₂ ≠ s := by
    intro e; subst e; exact hp₂B (by simpa [T_set] using hp₂.1)
  have hR₁ : R_set L t u v i₁ p₁ = {p₁, pick L t u v i₁} := by simp [R_set, hp₁B]
  have hR₂ : R_set L t u v i₂ p₂ = {p₂, pick L t u v i₂} := by simp [R_set, hp₂B]
  rw [hR₁, Finset.mem_insert, Finset.mem_singleton] at hx₁
  rw [hR₂, Finset.mem_insert, Finset.mem_singleton] at hx₂
  have hpk₁ : pick L t u v i₁ ∈ L i₂ ∩ ({t, u, v} : Finset (Fin 13)) := by
    rcases hx₁.1 with rfl | rfl
    · exact False.elim (hp₁.2 hx₁.2)
    · exact Finset.mem_inter.mpr ⟨hx₁.2, pick_mem_B L t u v i₁⟩
  have hpk₂ : pick L t u v i₂ ∈ L i₁ ∩ ({t, u, v} : Finset (Fin 13)) := by
    rcases hx₂.1 with rfl | rfl
    · exact False.elim (hp₂.2 hx₂.2)
    · exact Finset.mem_inter.mpr ⟨hx₂.2, pick_mem_B L t u v i₂⟩
  have c₁ := pick_cyc L s t u v i₂ htL huL hvL (hinter i₂ s hi₂s) _ hpk₁
  have c₂ := pick_cyc L s t u v i₁ htL huL hvL (hinter i₁ s hi₁s) _ hpk₂
  exact cycRel_anti t u v htu huv htv _ _ c₁ c₂

lemma outsideWitness {n : ℕ} {A B T : Finset (Fin n)}
    (thin : (A ∩ B).card ≤ 1) (sub : T ⊆ A) (many : 2 ≤ T.card) :
    ∃ p ∈ T, p ∉ B := by
  by_contra! inside
  have hsub : T ⊆ A ∩ B := fun p hp => Finset.mem_inter.mpr ⟨sub hp, inside p hp⟩
  have bound := Finset.card_le_card hsub
  omega

lemma disjointPayments {n m k : ℕ} (S T₀ : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)) (pay : Fin m → Finset (Fin k))
    (on : Fin k → Fin m → Fin n → Prop)
    (hTS : ∀ i, T₀ i ⊆ S i)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (separated : ∀ i j, i ≠ j → ¬ ((∃ p ∈ T₀ i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ p ∈ T₀ j \ S i, (R j p ∩ S i).Nonempty)))
    (wide : ∀ i t, t ∈ pay i → ∃ T : Finset (Fin n), T ⊆ T₀ i ∧ 2 ≤ T.card ∧
      ∀ p ∈ T, on t i p)
    (cross : ∀ i p j t, p ∈ T₀ i → on t i p → t ∈ pay j → (R i p ∩ S j).Nonempty) :
    ∀ i j, i ≠ j → Disjoint (pay i) (pay j) := by
  classical
  have witness {i j : Fin m} {t : Fin k} (diff : i ≠ j) (hi : t ∈ pay i) (hj : t ∈ pay j) :
      ∃ p ∈ T₀ i \ S j, (R i p ∩ S j).Nonempty := by
    obtain ⟨T, ts, two, high⟩ := wide i t hi
    obtain ⟨p, pt, pb⟩ := outsideWitness (thin i j diff) (ts.trans (hTS i)) two
    exact ⟨p, Finset.mem_sdiff.mpr ⟨ts pt, pb⟩, cross i p j t (ts pt) (high p pt) hj⟩
  intro i j diff
  rw [Finset.disjoint_left]
  intro t hi hj
  exact separated i j diff ⟨witness diff hi hj, witness diff.symm hj hi⟩

lemma sum_T_card (s t u v : Fin 13) (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v) :
    ∑ i : Fin 13, ((T_set L0 s t u v i).card - 1) = 38 := by
  have hB : ({t, u, v} : Finset (Fin 13)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair huv]
    simp [htu, htv]
  have hs := Finset.add_sum_erase (Finset.univ : Finset (Fin 13))
    (fun i => (T_set L0 s t u v i).card - 1) (Finset.mem_univ s)
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 13)).erase s, ((T_set L0 s t u v i).card - 1) =
      ∑ _i ∈ (Finset.univ : Finset (Fin 13)).erase s, 3 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have his : i ≠ s := (Finset.mem_erase.mp hi).1
    simp [T_set, his, L0_card]
  rw [hsum, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ s),
    Finset.card_univ, Fintype.card_fin] at hs
  have hsat : (T_set L0 s t u v s).card - 1 = 2 := by
    simp [T_set, hB]
  rw [hsat] at hs
  omega

lemma cone_lt_h (gates : List Gate) (h : Fin gates.length)
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, (gates.get g).op = GateOp.and ∧
      ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
        13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) :
    ∀ g ∈ I, g < h := by
  let T0 : Finset (Fin gates.length) := Finset.univ.filter (fun g' : Fin gates.length => g' < h)
  have hT0 : ∀ i g' : Fin gates.length, (i = h ∨ i ∈ T0) →
      13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T0 := by
    intro i g' hi _ hgi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hi with rfl | hi
    · exact hgi
    · exact lt_trans hgi (Finset.mem_filter.mp hi).2
  intro g hg
  exact (Finset.mem_filter.mp ((hI g hg).2 T0 hT0)).2

theorem main : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (s t u v : Fin 13), t ∈ L s → u ∈ L s → v ∈ L s → t ≠ u → u ≠ v → t ≠ v →
    Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = u))) = true →
    Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = v))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      38 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 1 I.card ≤ gates.length := by
  classical
  intro L hL gates o j h valid op unique hhj hin computes hcoline s t u v htL huL hvL htu huv htv ht_true hu_true hv_true I hI
  have hLeq : L = L0 := funext hL
  subst hLeq
  have hcold_of_h (x : Fin 13 → Bool)
      (hh : Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn x) = true) :
      Circuit.eval ⟨gates, 13 + (j : ℕ)⟩ (List.ofFn x) = false := by
    rw [not_eval_eq gates j h op hhj hin x, hh]
    rfl
  have low : ∀ i : Fin 13,
      Circuit.eval ⟨gates, 13 + (j : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y ∉ L0 i))) = false :=
    fun i => hcold_of_h _ (hcoline i)
  have hB_cold (x : Fin 13 → Bool)
      (hx : ∃ b ∈ ({t, u, v} : Finset (Fin 13)), x b = true) :
      Circuit.eval ⟨gates, 13 + (j : ℕ)⟩ (List.ofFn x) = false := by
    obtain ⟨b, hbB, hxb⟩ := hx
    have hbh : Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = b))) = true := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbB
      rcases hbB with rfl | rfl | rfl
      · exact ht_true
      · exact hu_true
      · exact hv_true
    have hle : ∀ y : Fin 13, decide (y = b) = true → x y = true := by
      intro y hy
      rw [of_decide_eq_true hy]
      exact hxb
    have hm := mono_lt (n := 13) ⟨gates, 0⟩ valid j unique
      (fun y : Fin 13 => decide (y = b)) x hle (13 + h.val)
      (by change 13 + h.val < 13 + j.val; change h.val < j.val at hhj; omega) hbh
    exact hcold_of_h x hm
  let yes (i : Fin 13) (p y : Fin 13) := decide (y ∈ R_set L0 t u v i p)
  let no (i : Fin 13) (y : Fin 13) := decide (y ∉ L0 i)
  have cold (i : Fin 13) (p : Fin 13) :
      Circuit.eval ⟨gates, 13 + (j : ℕ)⟩ (List.ofFn (yes i p)) = false := by
    apply hB_cold
    obtain ⟨b, hbB, hbR⟩ := R_has_B L0 t u v i p
    exact ⟨b, hbB, decide_eq_true hbR⟩
  have oneg (i : Fin 13) : Circuit.eval ⟨gates, o i⟩ (List.ofFn (no i)) = false := by
    rw [computes]
    apply decide_eq_false
    rintro ⟨y, hy, hyno⟩
    exact (of_decide_eq_true hyno) hy
  have opos (i : Fin 13) (p : Fin 13) (hp : p ∈ T_set L0 s t u v i) :
      Circuit.eval ⟨gates, o i⟩ (List.ofFn (yes i p)) = true := by
    have hsep := R_sep L0 s t u v htL huL hvL htu huv htv L0_inter i p hp
    have hmem : p ∈ R_set L0 t u v i p ∩ L0 i := by rw [hsep]; simp
    rw [computes]
    exact decide_eq_true ⟨p, (Finset.mem_inter.mp hmem).2, decide_eq_true (Finset.mem_inter.mp hmem).1⟩
  have found (i : Fin 13) := row_or gates j valid unique (L0 i) (T_set L0 s t u v i)
    (R_set L0 t u v i) (o i)
    (R_sep L0 s t u v htL huL hvL htu huv htv L0_inter i)
    (low i) (fun p _ => cold i p) (oneg i) (opos i)
  choose pay many props using found
  let on (q : Fin gates.length) (i : Fin 13) (p : Fin 13) : Prop :=
    Circuit.eval ⟨gates, 13 + q.val⟩ (List.ofFn (yes i p)) = true
  have wide (i : Fin 13) (q : Fin gates.length) (hq : q ∈ pay i) :
      ∃ T : Finset (Fin 13), T ⊆ T_set L0 s t u v i ∧ 2 ≤ T.card ∧ ∀ p ∈ T, on q i p :=
    ⟨(T_set L0 s t u v i).filter (on q i), Finset.filter_subset _ _, (props i q hq).2.2.2,
      fun _ hp => (Finset.mem_filter.mp hp).2⟩
  have cross (i : Fin 13) (p : Fin 13) (z : Fin 13) (q : Fin gates.length)
      (hp : p ∈ T_set L0 s t u v i) (hit : on q i p) (hq : q ∈ pay z) :
      (R_set L0 t u v i p ∩ L0 z).Nonempty := by
    by_contra hn
    have le (y : Fin 13) (hy : yes i p y = true) : no z y = true := by
      apply decide_eq_true
      intro hz
      exact hn ⟨y, Finset.mem_inter.mpr ⟨of_decide_eq_true hy, hz⟩⟩
    have hi := row_mono gates j valid unique (yes i p) (no z) (cold i p) (low z) le (13 + q.val) hit
    have lo : Circuit.eval ⟨gates, 13 + q.val⟩ (List.ofFn (no z)) = false := (props z q hq).2.2.1
    rw [lo] at hi
    contradiction
  let paid := Finset.univ.biUnion pay
  have hdisj := disjointPayments L0 (T_set L0 s t u v) (R_set L0 t u v) pay on
    (T_sub_L L0 s t u v htL huL hvL) L0_inter
    (R_separated L0 s t u v htL huL hvL htu huv htv L0_inter) wide cross
  have hpaid_card : 38 ≤ paid.card := by
    rw [Finset.card_biUnion (fun i _ i' _ hne => hdisj i i' hne)]
    calc 38 = ∑ i : Fin 13, ((T_set L0 s t u v i).card - 1) := (sum_T_card s t u v htu huv htv).symm
      _ ≤ ∑ i : Fin 13, (pay i).card := Finset.sum_le_sum fun i _ => many i
  let rs := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)
  have hI_lt : ∀ g ∈ I, g < j := fun g hg => lt_trans (cone_lt_h gates h I hI g hg) hhj
  have hpaid_prop : ∀ g ∈ paid, (gates.get g).op = GateOp.or ∧ ¬ (j < g ∧ 13 + j.val ∈ (gates.get g).inputs) := by
    intro g hg
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hg
    exact ⟨(props i g hgi).1, (props i g hgi).2.1⟩
  have hdis_pr : Disjoint paid rs := by
    rw [Finset.disjoint_left]
    intro g hgp hgr
    exact (hpaid_prop g hgp).2 (Finset.mem_filter.mp hgr).2
  have hdis_pI : Disjoint (paid ∪ rs) I := by
    rw [Finset.disjoint_left]
    intro g hg hgI
    rcases Finset.mem_union.mp hg with hgp | hgr
    · have h1 := (hpaid_prop g hgp).1
      have h2 := (hI g hgI).1
      rw [h1] at h2
      exact GateOp.noConfusion h2
    · have h1 : j < g := (Finset.mem_filter.mp hgr).2.1
      have h2 : g < j := hI_lt g hgI
      exact absurd (lt_trans h1 h2) (lt_irrefl j)
  have hj_not : j ∉ (paid ∪ rs) ∪ I := by
    intro hj
    rcases Finset.mem_union.mp hj with hjpr | hjI
    · rcases Finset.mem_union.mp hjpr with hjp | hjr
      · have h1 := (hpaid_prop j hjp).1
        rw [op] at h1
        exact GateOp.noConfusion h1
      · exact (lt_irrefl j) (Finset.mem_filter.mp hjr).2.1
    · exact (lt_irrefl j) (hI_lt j hjI)
  have hcap := Finset.card_le_univ (insert j ((paid ∪ rs) ∪ I))
  rw [Finset.card_insert_of_notMem hj_not, Finset.card_union_of_disjoint hdis_pI,
    Finset.card_union_of_disjoint hdis_pr, Fintype.card_fin] at hcap
  dsimp only [rs] at hcap
  omega

end PEqualNP.Outside.L_meta_1518

theorem PEqualNP.Outside.L_meta_1518 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (s t u v : Fin 13), t ∈ L s → u ∈ L s → v ∈ L s → t ≠ u → u ≠ v → t ≠ v →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = u))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = v))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      38 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 1 I.card ≤ gates.length :=
  PEqualNP.Outside.L_meta_1518.main
