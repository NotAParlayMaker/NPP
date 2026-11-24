import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2852_aux

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


lemma run_append (a b : List Gate) (w : List Bool) : run (a++b) w = run b (run a w) := by
  simp [run,List.foldl_append]

lemma rel_refl (xs : List Bool) : List.Forall₂ (fun a b => a=true → b=true) xs xs := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih => exact .cons (fun h => h) ih

lemma rel_getD {xs ys : List Bool} (h : List.Forall₂ (fun a b => a=true → b=true) xs ys)
    (i : ℕ) : xs.getD i false=true → ys.getD i false=true := by
  induction h generalizing i with
  | nil => exact id
  | cons hab h ih => cases i with | zero => exact hab | succ i => exact ih i

lemma map_rel (is : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i=true → g i=true) :
    List.Forall₂ (fun a b => a=true → b=true) (is.map f) (is.map g) := by
  induction is with
  | nil => exact .nil
  | cons i is ih => exact .cons (h i) ih

lemma eval_mono (op : GateOp) (hop : op=GateOp.and ∨ op=GateOp.or)
    (xs ys : List Bool) (h : List.Forall₂ (fun a b => a=true → b=true) xs ys) :
    op.eval xs=true → op.eval ys=true := by
  rcases hop with rfl | rfl
  · induction h with
    | nil => exact id
    | cons hab h ih =>
      simp only [GateOp.eval,List.all_cons,Bool.and_eq_true,id_eq] at *
      rintro ⟨ha,ht⟩
      exact ⟨hab ha,ih ht⟩
  · induction h with
    | nil => exact id
    | cons hab h ih =>
      simp only [GateOp.eval,List.any_cons,Bool.or_eq_true,id_eq] at *
      rintro (ha | ht)
      · exact Or.inl (hab ha)
      · exact Or.inr (ih ht)

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op=GateOp.and ∨ g.op=GateOp.or)
    (xs ys : List Bool) (h : List.Forall₂ (fun a b => a=true → b=true) xs ys) :
    List.Forall₂ (fun a b => a=true → b=true) (run gs xs) (run gs ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons,run_cons]
    apply ih (by intro g hg; exact hgs g (by simp [hg]))
    exact List.rel_append h (.cons (eval_mono g.op (hgs g (by simp)) _ _
      (map_rel g.inputs _ _ (rel_getD h))) .nil)

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem?_getD,hj]

lemma slot_rel (xs : List ℕ) (b w w' : ℕ) (f : ℕ → Bool)
    (hlen : xs.length=2) (hb : b<2) (hw : xs.getD b 0=w)
    (himp : f w=true → f w'=true) :
    List.Forall₂ (fun a b => a=true → b=true) (xs.map f) ((xs.set b w').map f) := by
  obtain ⟨a,c,rfl⟩ := List.length_eq_two.mp hlen
  have hcases : b=0 ∨ b=1 := by omega
  rcases hcases with rfl | rfl
  · have ha : a=w := by simpa using hw
    exact .cons (by simpa only [ha] using himp) (.cons (fun h => h) .nil)
  · have hc : c=w := by simpa using hw
    exact .cons (fun h => h) (.cons (by simpa only [hc] using himp) .nil)

lemma slot_eq (xs : List ℕ) (b w w' : ℕ) (f : ℕ → Bool)
    (hlen : xs.length=2) (hb : b<2) (hw : xs.getD b 0=w) (heq : f w=f w') :
    xs.map f = (xs.set b w').map f := by
  obtain ⟨a,c,rfl⟩ := List.length_eq_two.mp hlen
  have hcases : b=0 ∨ b=1 := by omega
  rcases hcases with rfl | rfl
  · have ha : a=w := by simpa using hw
    simp only [List.set_cons_zero,List.map_cons,List.map_nil,ha,heq]
  · have hc : c=w := by simpa using hw
    simp only [List.set_cons_succ,List.set_cons_zero,List.map_cons,List.map_nil,hc,heq]

lemma slot_down (xs : List ℕ) (b w w' : ℕ) (f : ℕ → Bool)
    (hlen : xs.length=2) (hb : b<2) (hw : xs.getD b 0=w)
    (himp : f w'=true → f w=true) :
    List.Forall₂ (fun a b => a=true → b=true) ((xs.set b w').map f) (xs.map f) := by
  obtain ⟨a,c,rfl⟩ := List.length_eq_two.mp hlen
  have hcases : b=0 ∨ b=1 := by omega
  rcases hcases with rfl | rfl
  · have ha : a=w := by simpa using hw
    exact .cons (by simpa only [ha] using himp) (.cons (fun h => h) .nil)
  · have hc : c=w := by simpa using hw
    exact .cons (fun h => h) (.cons (by simpa only [hc] using himp) .nil)

lemma inputs_rel {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ i, x i=true → y i=true) :
    List.Forall₂ (fun a b : Bool => a=true → b=true) (List.ofFn x) (List.ofFn y) := by
  induction n with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact .cons (hxy 0) (ih _ _ (fun i => hxy i.succ))

lemma circuit_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op=GateOp.and ∨ g.op=GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i=true → y i=true) :
    PEqualNP.MetaComplexity.circuitFun n C x=true →
    PEqualNP.MetaComplexity.circuitFun n C y=true := by
  have h := inputs_rel x y hxy
  exact rel_getD (run_mono C.gates hC _ _ h) C.output

lemma minimal_true {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (hx : f x=true) : ∃ y : Fin n → Bool, (∀ i, y i=true → x i=true) ∧
      f y=true ∧ ∀ z : Fin n → Bool, (∀ i, z i=true → y i=true) → z≠y → f z=false := by
  classical
  let supp := fun y : Fin n → Bool => Finset.univ.filter (fun i => y i=true)
  have hex : ∃ k : ℕ, ∃ y : Fin n → Bool,
      (∀ i, y i=true → x i=true) ∧ f y=true ∧ (supp y).card=k :=
    ⟨(supp x).card,x,fun _ h => h,hx,rfl⟩
  obtain ⟨y,hy,hfy,hcard⟩ := Nat.find_spec hex
  refine ⟨y,hy,hfy,?_⟩
  intro z hz hne
  cases hfz : f z with
  | false => rfl
  | true =>
    have hlt : (supp z).card < (supp y).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_,?_⟩
      · intro i hi
        have hi' : z i=true := by simpa [supp] using hi
        simpa [supp] using hz i hi'
      · intro heq
        apply hne
        funext i
        have ht : z i=true ↔ y i=true := by
          have hmem := congrArg (fun s : Finset (Fin n) => i ∈ s) heq
          simpa [supp] using hmem
        cases hzi : z i <;> cases hyi : y i <;> simp_all
    have hmin : Nat.find hex ≤ (supp z).card := Nat.find_min' hex
      ⟨z,fun i hi => hy i (hz i hi),hfz,rfl⟩
    omega

end PEqualNP.Outside.L_meta_2852_aux
open PEqualNP.Outside.L_meta_2852_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_2852 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) := by

  classical
  intro n C g b w w' hh
  obtain ⟨hC,hback,hg,hb,hslot,hw',himp⟩ := hh
  let G := gateAt C g
  let H : Gate := ⟨G.op,G.inputs.set b w'⟩
  let D : Circuit := ⟨C.gates.set g H,C.output⟩
  have hGmem : G ∈ C.gates := by rw [show G=C.gates[g] from gateAt_eq hg]; exact List.getElem_mem hg
  have hGlen : G.inputs.length=2 := hC.2.2 G hGmem
  have hGop := hC.1 G hGmem
  have hw : w<n+g := by
    apply hback g hg
    rw [← hslot]
    rw [List.getD_eq_getElem _ _ (by change b < G.inputs.length; omega)]
    exact List.getElem_mem _
  have hDgate (j : ℕ) (hj : j<C.gates.length) :
      gateAt D j = if g=j then H else gateAt C j := by
    rw [gateAt_eq (by simpa [D] using hj)]
    simp only [D,List.getElem_set]
    split_ifs <;> simp [gateAt_eq hj]
  have hDC : PEqualNP.TopForm.IsAO2 n D := by
    refine ⟨?_,?_,?_⟩
    · intro a ha
      rcases List.mem_or_eq_of_mem_set ha with ha | rfl
      · exact hC.1 a ha
      · exact hGop
    · intro j hj i hi
      have hj' : j<C.gates.length := by simpa [D] using hj
      rw [hDgate j hj'] at hi
      split_ifs at hi with heq
      · subst j
        rcases List.mem_or_eq_of_mem_set hi with hi | rfl
        · exact hback g hg i hi
        · exact hw'
      · exact hback j hj' i hi
    · intro a ha
      rcases List.mem_or_eq_of_mem_set ha with ha | rfl
      · exact hC.2.2 a ha
      · simpa [H] using hGlen
  have hdown (x : Fin n → Bool) : PEqualNP.MetaComplexity.circuitFun n D x=true →
      PEqualNP.MetaComplexity.circuitFun n C x=true := by
    let pre := run (C.gates.take g) (List.ofFn x)
    have plen : pre.length=n+g := by simp [pre,run_length,Nat.min_eq_left hg.le]
    have split : C.gates=C.gates.take g ++ G::C.gates.drop (g+1) := by
      calc C.gates = C.gates.take g ++ C.gates.drop g := (List.take_append_drop g C.gates).symm
           _ = _ := by rw [List.drop_eq_getElem_cons hg]; simp only [G,gateAt_eq hg]
    have preserve (a : ℕ) (ha : a<n+g) :
        (C.wires (List.ofFn x)).getD a false = pre.getD a false := by
      change (run C.gates (List.ofFn x)).getD a false = _
      rw [split,run_append]
      exact run_getD _ pre a (by omega)
    have himp' : pre.getD w' false=true → pre.getD w false=true := by
      intro hv
      have ht := himp x (by change (C.wires (List.ofFn x)).getD w' false=true; rw [preserve w' hw']; exact hv)
      change (C.wires (List.ofFn x)).getD w false=true at ht
      rwa [preserve w hw] at ht
    have oldrun : C.wires (List.ofFn x) =
        run (C.gates.drop (g+1)) (pre++[G.op.eval (G.inputs.map fun i => pre.getD i false)]) := by
      change run C.gates (List.ofFn x) = _
      rw (occs := [1]) [split]
      rw [run_append,run_cons]
    have newrun : D.wires (List.ofFn x) =
        run (C.gates.drop (g+1)) (pre++[H.op.eval (H.inputs.map fun i => pre.getD i false)]) := by
      change run (C.gates.set g H) (List.ofFn x) = _
      rw [List.set_eq_take_append_cons_drop,if_pos hg,run_append,run_cons]
    have hval := eval_mono G.op hGop _ _ (slot_down G.inputs b w w'
      (fun i => pre.getD i false) hGlen hb hslot himp')
    have hr := run_mono (C.gates.drop (g+1))
      (by intro a ha; exact hC.1 a (List.mem_of_mem_drop ha))
      _ _ (List.rel_append (rel_refl pre) (.cons hval .nil))
    have hout := rel_getD hr C.output
    change (D.wires (List.ofFn x)).getD C.output false=true →
      (C.wires (List.ofFn x)).getD C.output false=true
    rw [oldrun,newrun]
    exact hout
  change PEqualNP.TopForm.IsAO2 n D ∧ D.size=C.size ∧ _ ∧ _
  refine ⟨hDC,by simp [D,Circuit.size],hdown,?_⟩
  constructor
  · intro heq x hx
    rw [heq]
    exact hx.1
  · intro hmin
    funext x
    cases hc : PEqualNP.MetaComplexity.circuitFun n C x with
    | false =>
      cases hd : PEqualNP.MetaComplexity.circuitFun n D x with
      | false => rfl
      | true => have ht := hdown x hd; rw [hc] at ht; contradiction
    | true =>
      obtain ⟨y,hy,hfy,hsmall⟩ := minimal_true (PEqualNP.MetaComplexity.circuitFun n C) x hc
      have hdy := hmin y ⟨hfy,hsmall⟩
      exact circuit_mono D hDC.1 y x hy hdy
