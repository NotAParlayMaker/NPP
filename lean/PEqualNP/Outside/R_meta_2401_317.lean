import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2401_317
    (fixed :
      let offsets : Finset (Fin 13) := {0,1,3,9}
      let I := fun (p l : Fin 13) => ∃ d ∈ offsets, p = l+d
      let lift := fun (x : Fin 26 → Bool) (i : Fin 27) => (Fin.lastCases (x 0 || x 1) x i : Bool)
      let Q : List (List Nat) := [[3,9],[4,5],[4,5,7],[6,10],[6,10,11],[2,8],[2,8,12]]
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 27 D ∧ D.size = 18 ∧ D.output < 45 ∧
        (∀ u : Fin 27 → Bool, ∃ t : List Bool, t.length = 11 ∧
          D.wires (List.ofFn u) = List.ofFn u ++ Q.map (fun qs => qs.any (fun k => (List.ofFn u).getD k false)) ++ t) ∧
        ∀ x : Fin 26 → Bool, circuitFun 27 D (lift x) = true ↔
          ∃ l : Fin 13, I 0 l ∧ ∃ p : Fin 13, I p l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (affine :
      let offsets : Finset (Fin 13) := {0,1,3,9}
      let I := fun (p l : Fin 13) => ∃ d ∈ offsets, p = l+d
      let lift := fun (x : Fin 26 → Bool) (i : Fin 27) => (Fin.lastCases (x 0 || x 1) x i : Bool)
      let Q : List (List Nat) := [[3,9],[4,5],[4,5,7],[6,10],[6,10,11],[2,8],[2,8,12]]
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack 45 C ∧ C.size ≤ 43 ∧ C.output < 45+C.size ∧
        ∀ (x : Fin 26 → Bool) (t : List Bool), t.length = 11 →
          let A := fun p : Fin 13 => x (Fin.castAdd 13 p) = true
          let B := fun l : Fin 13 => x (Fin.natAdd 13 l) = true
          let hit := fun (s : Fin 13 → Prop) => ∃ l, s l ∧ B l ∧ ∃ p, A p ∧ I p l
          let v := C.eval (List.ofFn (lift x) ++ Q.map (fun qs => qs.any (fun k => (List.ofFn (lift x)).getD k false)) ++ t)
          (hit (fun l => ¬ I 0 l) → v = true) ∧
          (v = true → hit (fun _ => True) ∨
            (∃ l p, ∀ q, I q l → q ≠ p → A q) ∨
            (∃ p l, ∀ k, I p k → k ≠ l → B k))) :
    ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false := by
  have gateLookup (c : Circuit) (j : Nat) :
      gateAt c j = c.gates.getD j ⟨GateOp.or,[]⟩ := rfl
  have sizeEq (c : Circuit) : c.size = c.gates.length := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g rest ih =>
      change (rest.foldl step (step w g)).length = _
      rw [ih (step w g)]
      simp [step] <;> omega

  have old_index (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

  have append_order {a b : Circuit} {n : Nat}
      (ha : ReadsBack n a) (hb : ReadsBack (n + a.size) b) :
      ReadsBack n ⟨a.gates ++ b.gates,0⟩ := by
    intro j hj i hi
    by_cases h : j < a.gates.length
    · apply ha j h
      simpa [gateLookup,List.getD_eq_getElem?_getD,List.getElem?_append_left h] using hi
    · have hj' : j - a.gates.length < b.gates.length := by
        simp at hj
        omega
      have hx : i ∈ (gateAt b (j-a.gates.length)).inputs := by
        simpa [gateLookup,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : a.gates.length ≤ j)] using hi
      have := hb _ hj' _ hx
      rw [sizeEq] at this
      omega

  have glue (n : Nat) (a b : Circuit) (ha : Monotone2 a) (hb : Monotone2 b)
      (wa : ReadsBack n a) (wb : ReadsBack (n+a.size) b)
      (oa : a.output < n+a.size) (ob : b.output < n+a.size+b.size) :
      ∃ c : Circuit, Monotone2 c ∧ ReadsBack n c ∧ c.size = a.size+b.size+1 ∧
        ∀ x : Fin n → Bool,
          circuitFun n c x = (circuitFun n a x ||
            b.eval (a.wires (List.ofFn x))) := by
    let ab : Circuit := ⟨a.gates++b.gates,0⟩
    let last : Circuit := ⟨[⟨.or,[a.output,b.output]⟩],0⟩
    let c : Circuit := ⟨ab.gates++last.gates,n+a.size+b.size⟩
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ (a.gates ++ b.gates) ++ [⟨.or,[a.output,b.output]⟩] at hg
      simp only [List.mem_append,List.mem_singleton] at hg
      rcases hg with (h|h)|rfl
      · exact ha _ h
      · exact hb _ h
      · simp
    · have wab : ReadsBack n ab := append_order wa wb
      have wl : ReadsBack (n+ab.size) last := by
        intro j hj i hi
        change j < 1 at hj
        have : j=0 := by omega
        subst j
        simp [gateLookup,last] at hi
        simp [ab,sizeEq] at *
        omega
      exact append_order wab wl
    · simp [c,ab,last,sizeEq,Nat.add_assoc]
    · intro x
      let w := a.wires (List.ofFn x)
      let v := b.wires w
      have hw : w.length = n+a.size := by
        change (a.gates.foldl step (List.ofFn x)).length = _
        rw [fold_length]; simp [sizeEq]
      have hv : v.length = n+a.size+b.size := by
        change (b.gates.foldl step w).length = _
        rw [fold_length,hw]; rfl
      change (((a.gates++b.gates)++last.gates).foldl step (List.ofFn x)).getD _ false =
        (w.getD a.output false || v.getD b.output false)
      rw [List.foldl_append,List.foldl_append]
      change (v ++ [GateOp.or.eval ([a.output,b.output].map fun i => v.getD i false)]).getD (n+a.size+b.size) false = _
      rw [← hv]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,List.map_cons,List.map_nil,
        evalOr,List.any_cons,List.any_nil,id_eq,Bool.or_false]
      have hold : v.getD a.output false = w.getD a.output false :=
        old_index b.gates w a.output (by omega)
      simpa only [List.getD_eq_getElem?_getD] using congrArg (fun z => z || v.getD b.output false) hold


  let offsets : Finset (Fin 13) := {0,1,3,9}
  let I := fun (p l : Fin 13) => ∃ d ∈ offsets, p = l+d
  let lift := fun (x : Fin 26 → Bool) (i : Fin 27) => (Fin.lastCases (x 0 || x 1) x i : Bool)
  let Q : List (List Nat) := [[3,9],[4,5],[4,5,7],[6,10],[6,10,11],[2,8],[2,8,12]]
  obtain ⟨D,md,wd,sd,od,hw,hf⟩ := fixed
  obtain ⟨C,mc,wc,sc,oc,hc⟩ := affine
  have nl : 27 + D.size = 45 := by omega
  obtain ⟨G,mg,wg,sg,hg⟩ := glue 27 D C md mc wd (nl ▸ wc) (by omega) (by omega)
  refine ⟨1,G,mg,wg,by omega,?_⟩
  constructor
  · intro p l he
    let x : Fin 26 → Bool := fun i => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)
    change circuitFun 27 G (lift x) = true
    rw [hg]
    have xp : x (Fin.castAdd 13 p) = true := by simp [x]
    have xl : x (Fin.natAdd 13 l) = true := by simp [x]
    by_cases h0 : I 0 l
    · rw [Bool.or_eq_true]
      exact Or.inl ((hf x).mpr ⟨l,h0,p,he,xp,xl⟩)
    · obtain ⟨t,ht,h⟩ := hw (lift x)
      rw [h]
      rw [Bool.or_eq_true]
      exact Or.inr ((hc x t ht).1 ⟨l,h0,xl,p,xp,he⟩)
  · intro S blocked _ hgenc x hx
    let safe := fun l : Fin 13 => ∀ p ∈ S, ¬I p l
    have sep (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro e
      have v := congrArg Fin.val e
      change p.val = 13 + l.val at v
      omega
    have hp (p : Fin 13) : x (Fin.castAdd 13 p) = true ↔ p ∈ S := by
      rw [hx]
      constructor
      · rintro (⟨q,hq,e⟩ | ⟨k,e,_⟩)
        · have v := congrArg Fin.val e
          have eq : p = q := Fin.ext v
          exact eq ▸ hq
        · exact False.elim (sep p k e)
      · intro a
        exact Or.inl ⟨p,a,rfl⟩
    have hl (l : Fin 13) : x (Fin.natAdd 13 l) = true ↔ safe l := by
      rw [hx]
      constructor
      · rintro (⟨q,_,e⟩ | ⟨k,e,hk⟩)
        · exact False.elim (sep q l e.symm)
        · have v := congrArg Fin.val e
          change 13 + l.val = 13 + k.val at v
          have eq : l = k := Fin.ext (by omega)
          exact eq ▸ hk
      · intro a
        exact Or.inr ⟨l,rfl,a⟩
    have disjoint (p l : Fin 13) (a : x (Fin.castAdd 13 p) = true)
        (b : x (Fin.natAdd 13 l) = true) : ¬I p l := (hl l).mp b p ((hp p).mp a)
    have meet : ∀ l k : Fin 13, ∃ p, I p l ∧ I p k := by unfold I offsets; decide
    have join : ∀ p q : Fin 13, ∃ l, I p l ∧ I q l := by unfold I offsets; decide
    change circuitFun 27 G (lift x) = false
    rw [hg]
    obtain ⟨t,ht,hw'⟩ := hw (lift x)
    rw [hw']
    apply Bool.or_eq_false_iff.mpr
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨l,_,p,hpl,a,b⟩ := (hf x).mp h
      exact disjoint p l a b hpl
    · apply Bool.eq_false_iff.mpr
      intro h
      rcases (hc x t ht).2 h with ⟨l,_,b,p,a,hpl⟩ | ⟨l,p,htr⟩ | ⟨p,l,htr⟩
      · exact disjoint p l a b hpl
      · apply hgenc.2
        refine ⟨p, fun k hk => ?_⟩
        obtain ⟨q,hql,hqk⟩ := meet l k
        by_cases e : q = p
        · exact e ▸ hqk
        · exact False.elim (disjoint q k (htr q hql e) ((hl k).mpr hk) hqk)
      · apply hgenc.1
        refine ⟨l, fun q hq => ?_⟩
        obtain ⟨k,hpk,hqk⟩ := join p q
        by_cases e : k = l
        · exact e ▸ hqk
        · exact False.elim (disjoint q k ((hp q).mpr hq) (htr k hpk e) hqk)
