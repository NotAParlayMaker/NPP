import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3382_677
    (cycleLower : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 0 && x 3) || (x 1 && x 4) ||
          (x 2 && x 4) || (x 3 && x 5) || (x 2 && x 5))) → 8 ≤ C.size)
    (drop_fixed :
      let pins (g : Gate) : List ℕ :=
        GateOp.casesOn g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
      let charged (g : Gate) := (pins g).contains 0 || (pins g).contains 3
      let lift (x : Fin 6 → Bool) : Fin 7 → Bool := ![x 0,x 1,false,x 2,x 3,x 4,x 5]
      ∀ C : Circuit, FanInTwo C →
      (∃ x : Fin 6 → Bool, C.eval (true :: List.ofFn (lift x)) = false) →
      ∃ E : Circuit, FanInTwo E ∧ E.size + C.gates.countP charged ≤ C.size ∧
        ∀ x : Fin 6 → Bool, E.eval (List.ofFn x) = C.eval (true :: List.ofFn (lift x)))
    (oneOutside :
      let f (x : Fin 7 → Bool) := ([1,12,4,15,26,35,46,36] : List ℕ).any
        (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))
      let pick (g : Gate) := g.op.eval [true,false] && g.inputs.contains 2
      let pins (g : Gate) : List ℕ :=
        GateOp.casesOn g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
      ∀ (C D : Circuit) (a b : ℕ), FanInTwo C → C.size = 11 → circuitFun 7 C = f →
      List.Forall₂ (fun g h : Gate => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs) C.gates D.gates →
      (∀ x, (D.wires (true :: List.ofFn x)).getD (C.output+1) false = (f x || x 2)) →
      (C.gates.filter pick).length = 2 →
      (((C.gates.zip D.gates).filter (fun p =>
        !pick p.1 && ((pins p.2).contains 0 || (pins p.2).contains 3))).map
        (fun p => (pins p.2).contains 0)) = [true] → False) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  intro f C D a b fanC sizeC funC edits funD
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  let Ok (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  let activeInputs (g : Gate) : List ℕ :=
    GateOp.casesOn g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
  let normGate (g : Gate) : Gate := ⟨g.op, activeInputs g⟩
  have normGate_eval (g : Gate) (F : ℕ → Bool) :
      (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
    obtain ⟨op, inputs⟩ := g
    cases op <;> simp only [normGate, activeInputs]
    cases inputs <;> rfl
  let fixedPins (g : Gate) : Bool :=
    (normGate g).inputs.contains 0 || (normGate g).inputs.contains 3
  let insertFalse (x : Fin 6 → Bool) : Fin 7 → Bool :=
    ![x 0, x 1, false, x 2, x 3, x 4, x 5]
  let paired (a b : ℕ) (g h : Gate) : Prop :=
    g.op = h.op ∧ List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs
  let orReader (g : Gate) : Bool :=
    g.op.eval [true,false] && g.inputs.contains 2
  let outsidePin (pair : Gate × Gate) : Bool := !orReader pair.1 && fixedPins pair.2
  let outsideEdit (pair : Gate × Gate) : Bool :=
    !orReader pair.1 && (normGate pair.2).inputs.contains 0
  have paired_norm {a b : ℕ} {g h : Gate} (hp : paired a b g h) :
      paired a b (normGate g) (normGate h) := by
    obtain ⟨op, is⟩ := g
    obtain ⟨op', js⟩ := h
    rcases hp with ⟨rfl, hp⟩
    cases op <;> first | exact ⟨rfl, hp⟩ | exact ⟨rfl, List.forall₂_take 1 hp⟩
  have paired_ok {a b : ℕ} {g h : Gate} (hp : paired a b g h) (hg : Ok g) : Ok h := by
    refine ⟨?_, ?_⟩
    · rw [← hp.1]; exact hg.1
    · rw [← hp.2.length_eq]; exact hg.2
  have mem_paired_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
      (hp : List.Forall₂ R xs ys) (x : α) (hx : x ∈ xs) :
      ∃ y ∈ ys, R x y := by
    induction hp with
    | nil => simp at hx
    | @cons x0 y0 xs ys hp0 hp ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self, hp0⟩
      · obtain ⟨y,hy,p⟩ := ih hx
        exact ⟨y,List.mem_cons_of_mem _ hy,p⟩
  have set_orReader {g : Gate} (hg : Ok g) (hr : orReader g = true) :
      g.op = GateOp.or ∧ 2 ∈ g.inputs := by
    simp only [orReader, Bool.and_eq_true, List.contains_iff_mem] at hr
    refine ⟨?_, hr.2⟩
    rcases hg.1 with h | h | h
    · have h' : g.op = GateOp.and := h
      have hf : GateOp.and.eval [true,false] = false := rfl
      rw [h', hf] at hr
      cases hr.1
    · exact h
    · have h' : g.op = GateOp.not := h
      have hf : GateOp.not.eval [true,false] = false := rfl
      rw [h', hf] at hr
      cases hr.1
  have fixed_when_orReader {a b : ℕ} {g h : Gate} (hp : paired a b g h)
      (hg : Ok g) (hr : orReader g = true) : fixedPins h = true := by
    obtain ⟨op,hin⟩ := set_orReader hg hr
    obtain ⟨j,hj,hmatch⟩ := mem_paired_right hp.2 2 hin
    have hop : h.op = GateOp.or := hp.1.symm.trans op
    rcases hmatch with rfl | ⟨rfl,_⟩ <;>
      simp_all [fixedPins, normGate, activeInputs, List.contains_iff_mem]
  have balance {a b : ℕ} {gs hs : List Gate} (hp : List.Forall₂ (paired a b) gs hs)
      (hg : ∀ g ∈ gs, Ok g) :
      hs.countP fixedPins = (gs.filter orReader).length + (gs.zip hs).countP outsidePin := by
    induction hp with
    | nil => rfl
    | @cons g h gs hs p ps ih =>
      have tail := ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg'))
      have front := hg g List.mem_cons_self
      rw [List.countP_cons, List.zip_cons_cons, List.countP_cons, List.filter_cons]
      cases hr : orReader g with
      | false =>
        cases hf : fixedPins h <;> simp [outsidePin, hr, hf, tail, Nat.add_assoc]
      | true =>
        simp [outsidePin, hr, fixed_when_orReader p front hr, tail, Nat.add_right_comm]
  have countP_le {α : Type} (p q : α → Bool) (l : List α)
      (h : ∀ a, p a = true → q a = true) : l.countP p ≤ l.countP q := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.countP_cons,List.countP_cons]
      cases hp : p a with
      | false => simp [hp]; omega
      | true => simp [hp, h a hp, ih]
  have count_edits_le (gs hs : List Gate) :
      (gs.zip hs).countP outsideEdit ≤ (gs.zip hs).countP outsidePin := by
    apply countP_le
    intro pair h
    simp only [outsideEdit, outsidePin, fixedPins,Bool.and_eq_true,Bool.or_eq_true] at h ⊢
    exact ⟨h.1, Or.inl h.2⟩
  have maps_shift {a b : ℕ} (w : List Bool) {is js : List ℕ}
      (hp : List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) is js)
      (hnot : 0 ∉ js) :
      js.map (fun j => (true :: w).getD j false) = is.map (fun i => w.getD i false) := by
    induction hp with
    | nil => rfl
    | @cons i j is js h rest ih =>
      have hn : j ≠ 0 := fun e => hnot (e ▸ List.mem_cons_self)
      have ht : 0 ∉ js := fun hm => hnot (List.mem_cons_of_mem _ hm)
      rcases h with rfl | ⟨rfl,_⟩
      · simp only [List.map_cons]
        exact congrArg (List.cons (w.getD i false)) (ih ht)
      · exact (hn rfl).elim
  have value_or (inputs : List ℕ) (w : List Bool) (j : ℕ) (hj : j ∈ inputs)
      (hv : w.getD j false = true) :
      GateOp.or.eval (inputs.map fun i => w.getD i false) = true := by
    change (inputs.map fun i => w.getD i false).any id = true
    simp only [List.any_eq_true, List.mem_map, id_eq]
    exact ⟨true, ⟨j,hj,hv⟩, rfl⟩
  have paired_value {a b : ℕ} {g h : Gate} (hp : paired a b g h)
      (hg : Ok g) (w : List Bool) (h2 : w.getD 2 false = true)
      (noEdit : outsideEdit (g,h) = false) :
      h.op.eval (h.inputs.map fun j => (true :: w).getD j false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    cases hr : orReader g with
    | false =>
      have noEdit' : 0 ∉ (normGate h).inputs := by
        simpa [outsideEdit, hr] using noEdit
      rw [← normGate_eval h, ← normGate_eval g]
      have hn := paired_norm hp
      rw [maps_shift w hn.2 noEdit', hn.1]
    | true =>
      obtain ⟨hop,hin⟩ := set_orReader hg hr
      obtain ⟨j,hj,hmatch⟩ := mem_paired_right hp.2 2 hin
      have vj : (true :: w).getD j false = true := by
        rcases hmatch with rfl | ⟨rfl,_⟩
        · exact h2
        · rfl
      rw [hop, ← hp.1, hop]
      exact (value_or _ _ j hj vj).trans (value_or _ _ 2 hin h2).symm
  have wires_no_outside_edit {a b : ℕ} {gs hs : List Gate}
      (hp : List.Forall₂ (paired a b) gs hs) (good : ∀ g ∈ gs, Ok g)
      (hcount : (gs.zip hs).countP outsideEdit = 0) :
      ∀ w : List Bool, 2 < w.length → w.getD 2 false = true →
        wiresFrom hs (true :: w) = true :: wiresFrom gs w := by
    induction hp with
    | nil => intro w _ _; rfl
    | @cons g h gs hs p ps ih =>
      intro w hlen ht
      have tail : (gs.zip hs).countP outsideEdit = 0 := by
        rw [List.zip_cons_cons,List.countP_cons] at hcount
        omega
      have head : outsideEdit (g,h) = false := by
        by_contra he
        have hyes : outsideEdit (g,h) = true := Bool.eq_true_of_not_eq_false he
        simp [List.countP_cons,hyes] at hcount
      have eq := paired_value p (good g List.mem_cons_self) w ht head
      let w' := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have hlen' : 2 < w'.length := by simp [w']; omega
      have ht' : w'.getD 2 false = true := by
        simpa only [w', List.getD_append _ _ _ _ hlen] using ht
      have htail := ih (fun g hg => good g (List.mem_cons_of_mem _ hg)) tail w' hlen' ht'
      change wiresFrom hs ((true :: w) ++ [h.op.eval (h.inputs.map fun j => (true :: w).getD j false)]) =
        true :: wiresFrom gs w'
      rw [eq]
      exact htail
  let E : Circuit := ⟨D.gates,C.output+1⟩
  let cycle (x : Fin 6 → Bool) := (x 0 && x 1) || (x 0 && x 3) || (x 1 && x 4) ||
    (x 2 && x 4) || (x 3 && x 5) || (x 2 && x 5)
  have identity : ∀ x : Fin 6 → Bool, (f (insertFalse x) || insertFalse x 2) = cycle x := by
    dsimp only [f, cycle, insertFalse]
    decide +kernel
  have evE (x : Fin 6 → Bool) : E.eval (true :: List.ofFn (insertFalse x)) = cycle x :=
    (funD (insertFalse x)).trans (identity x)
  have editRel : List.Forall₂ (paired a b) C.gates E.gates := edits
  have fanE : FanInTwo E := by
    intro h hh
    change h ∈ D.gates at hh
    have rv : ∀ {gs hs : List Gate}, List.Forall₂ (paired a b) gs hs →
        (∀ g ∈ gs, Ok g) → ∀ h ∈ hs, Ok h := by
      intro gs hs p
      induction p with
      | nil => simp
      | @cons g h gs hs p ps ih =>
        intro good d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact paired_ok p (good _ List.mem_cons_self)
        · exact ih (fun g hg => good g (List.mem_cons_of_mem _ hg)) d hd
    exact rv editRel fanC h hh
  have sameLength : E.size = C.size := editRel.length_eq.symm
  obtain ⟨H,fanH,nH,eqH⟩ := drop_fixed E fanE ⟨fun _ => false, (evE (fun _ => false)).trans rfl⟩
  have lb := cycleLower H fanH (fun x => (eqH x).trans (evE x))
  have hb := balance editRel fanC
  have hle : (C.gates.filter orReader).length + (C.gates.zip D.gates).countP outsidePin ≤ 3 := by
    change H.size + D.gates.countP fixedPins ≤ E.size at nH
    change D.gates.countP fixedPins = (C.gates.filter orReader).length +
      (C.gates.zip D.gates).countP outsidePin at hb
    omega
  have hpos : 0 < (C.gates.zip D.gates).countP outsideEdit := by
    by_contra! h
    have hz : (C.gates.zip D.gates).countP outsideEdit = 0 := by omega
    let t : Fin 7 → Bool := ![false,false,true,false,false,false,false]
    have h2 : (List.ofFn t).getD 2 false = true := rfl
    have equiv := wires_no_outside_edit edits fanC hz (List.ofFn t) (by simp) h2
    have same : (D.wires (true :: List.ofFn t)).getD (C.output+1) false =
        circuitFun 7 C t := by
      change (wiresFrom D.gates (true :: List.ofFn t)).getD (C.output+1) false =
        (wiresFrom C.gates (List.ofFn t)).getD C.output false
      rw [equiv]
      rfl
    rw [funD,funC] at same
    change true = false at same
    exact Bool.noConfusion same
  have hs := count_edits_le C.gates D.gates
  change (C.gates.filter orReader).length < 2
  by_contra! h
  have exactlyTwo : (C.gates.filter orReader).length = 2 := by omega
  have uniquePin : (C.gates.zip D.gates).countP outsidePin = 1 := by omega
  have pinLength : ((C.gates.zip D.gates).filter outsidePin).length = 1 := by
    rw [← List.countP_eq_length_filter]
    exact uniquePin
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp pinLength
  obtain ⟨q, hq, hqedit⟩ := List.countP_pos_iff.mp hpos
  have qp : outsidePin q = true := by
    simp only [outsideEdit, outsidePin, fixedPins, Bool.and_eq_true, Bool.or_eq_true] at hqedit ⊢
    exact ⟨hqedit.1, Or.inl hqedit.2⟩
  have member : q ∈ (C.gates.zip D.gates).filter outsidePin := List.mem_filter.mpr ⟨hq,qp⟩
  rw [hp] at member
  have eq : q = p := List.mem_singleton.mp member
  have actual : (normGate p.2).inputs.contains 0 = true := by
    subst p
    simp only [outsideEdit, Bool.and_eq_true] at hqedit
    exact hqedit.2
  apply oneOutside C D a b fanC sizeC funC edits funD exactlyTwo
  change List.map (fun p => (normGate p.2).inputs.contains 0)
    ((C.gates.zip D.gates).filter outsidePin) = [true]
  rw [hp]
  exact congrArg (fun b => [b]) actual
