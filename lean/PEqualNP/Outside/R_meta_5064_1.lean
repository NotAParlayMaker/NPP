import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Delete an isolated matched edge by fixing its endpoints false and saving two gates.
-- Continue until there is no isolated matched edge, then distinguish whether a leaf remains.
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_5064_1
    (genuineLeaf : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n)) (C : Circuit),
      n < E.card →
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
      (∀ a, (a,p a) ∈ E) → IsAO2 (n+n) C →
      (∀ x, circuitFun (n+n) C x = decide (∃ a b : Fin n,
        (a,b) ∈ E ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) →
      (∀ i, ¬ ((∀ j, (i,j) ∈ E → j = p i) ∧ (∀ a, (a,p i) ∈ E → a = i))) →
      ((∃ i, ∀ j, (i,j) ∈ E → j = p i) ∨ ∃ j, ∀ i, (i,j) ∈ E → p i = j) →
      E.card + n ≤ C.size+1)
    (core : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n)) (C : Circuit),
      n < E.card →
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
      (∀ a, (a,p a) ∈ E) → IsAO2 (n+n) C →
      (∀ x, circuitFun (n+n) C x = decide (∃ a b : Fin n,
        (a,b) ∈ E ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) →
      (¬ ((∃ i, ∀ j, (i,j) ∈ E → j = p i) ∨ ∃ j, ∀ i, (i,j) ∈ E → p i = j)) →
      E.card + n ≤ C.size+1) :
∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) ∨ ∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x12, x11) ∈ x2 → x3 x12 = x11) → x2.card + x1 ≤ x4.size + (1 : ℕ)
 := by
  classical
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let val {k : ℕ} (gs : List Gate) (x : Fin k → Bool) (i : ℕ) : Bool :=
    (gs.foldl step (List.ofFn x)).getD i false
  have wireLen {k : ℕ} (gs : List Gate) (x : Fin k → Bool) :
      (gs.foldl step (List.ofFn x)).length = k + gs.length := by
    suffices h : ∀ W, (gs.foldl step W).length = W.length + gs.length by simpa using h (List.ofFn x)
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro W
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have oldVal {k : ℕ} (gs : List Gate) (g : Gate) (x : Fin k → Bool)
      (i : ℕ) (hi : i < k + gs.length) :
      val (gs ++ [g]) x i = val gs x i := by
    change ((gs ++ [g]).foldl step (List.ofFn x)).getD i false =
      (gs.foldl step (List.ofFn x)).getD i false
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, step]
    rw [List.getD_append _ _ _ _ (by rw [wireLen]; exact hi)]
  have atLast {k : ℕ} (gs : List Gate) (g : Gate) (x : Fin k → Bool) :
      val (gs ++ [g]) x (k+gs.length) = g.op.eval (g.inputs.map (val gs x)) := by
    change ((gs ++ [g]).foldl step (List.ofFn x)).getD (k+gs.length) false = _
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, step]
    rw [List.getD_append_right _ _ _ _ (by rw [wireLen]), wireLen, Nat.sub_self]
    rfl
  have valOutside {k : ℕ} (gs : List Gate) (x : Fin k → Bool) (i : ℕ)
      (hi : k + gs.length ≤ i) : val gs x i = false := by
    change (gs.foldl step (List.ofFn x)).getD i false = false
    rw [List.getD_eq_default _ _ (by rw [wireLen]; exact hi)]
  have rawVal {k : ℕ} (x : Fin k → Bool) (i : Fin k) : val [] x i.val = x i := by
    change (List.ofFn x).getD i.val false = x i
    simp [List.getD_eq_getElem?_getD, i.isLt]

  let layout (k : ℕ) (gs : List Gate) : Prop :=
    ∀ j g, gs[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧
        ∀ i ∈ g.inputs, i < k+j
  have within (k : ℕ) (gs : List Gate) (g : Gate) (base : layout k gs)
      (op : g.op = .and ∨ g.op = .or) (two : g.inputs.length = 2)
      (earlier : ∀ w ∈ g.inputs, w < k+gs.length) : layout k (gs ++ [g]) := by
    intro j h get
    by_cases b : j < gs.length
    · rw [List.getElem?_append_left b] at get
      exact base j h get
    · have last : j = gs.length := by
        have l := (List.getElem?_eq_some_iff.mp get).1
        simp only [List.length_append, List.length_cons, List.length_nil] at l
        omega
      subst j
      rw [List.getElem?_append_right (by rfl), Nat.sub_self] at get
      have hEq : g = h := Option.some.inj get
      subst h
      exact ⟨op,two,earlier⟩
  have parentLayout (k : ℕ) (gs : List Gate) (g : Gate) (whole : layout k (gs ++ [g])) :
      layout k gs := by
    intro j h get
    have b := (List.getElem?_eq_some_iff.mp get).1
    apply whole j h
    rwa [List.getElem?_append_left b]
  have ownGate (base : ℕ) (C : Circuit) (h : IsAO2 base C) : layout base C.gates := by
    intro j g get
    have hj := (List.getElem?_eq_some_iff.mp get).1
    have mem := List.mem_iff_getElem?.mpr ⟨j,get⟩
    have eq : gateAt C j = g := by
      change C.gates.getD j ⟨.or,[]⟩ = g
      rw [List.getD_eq_getElem?_getD, get]
      rfl
    refine ⟨h.1 g mem, h.2.2 g mem, ?_⟩
    intro i hi
    exact h.2.1 j hj i (eq.symm ▸ hi)
  have fromLayout (base : ℕ) (C : Circuit) (h : layout base C.gates) : IsAO2 base C := by
    constructor
    · intro g hg
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
      exact (h i g hi).1
    · constructor
      · intro j hj i hi
        have get : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
        apply (h j C.gates[j] get).2.2 i
        rwa [← List.getD_eq_getElem _ ⟨.or,[]⟩ hj]
      · intro g hg
        obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
        exact (h i g hi).2.1

  let isAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  let isOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalAnd (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by
    rw [isAnd]
    simp
  have evalOr (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
    rw [isOr]
    simp

  have sweep {old new : ℕ} (init : Fin old → Option ℕ)
      (bounds : ∀ w r, init w = some r → r < new) :
      ∀ gs : List Gate, layout old gs →
      ∃ ds : List Gate, ∃ refs : List (Option ℕ), ∃ kept : Finset ℕ,
        layout new ds ∧ refs.length = old + gs.length ∧
        (∀ w : Fin old, refs.getD w.val none = init w) ∧
        (∀ w r, refs.getD w none = some r → r < new + ds.length) ∧
        kept ⊆ Finset.range gs.length ∧ kept.card = ds.length ∧
        (∀ j g, gs[j]? = some g → (∃ i : Fin old, i.val ∈ g.inputs ∧ init i = none) →
          j ∉ kept) ∧
        (∀ j g, gs[j]? = some g → (∀ i ∈ g.inputs, ∃ w : Fin old, w.val = i ∧ init w = none) →
          refs.getD (old+j) none = none) ∧
        (∀ x : Fin old → Bool, ∀ y : Fin new → Bool,
          (∀ w : Fin old, x w = ((init w).map (val ds y)).getD false) →
          ∀ w, val gs x w = ((refs.getD w none).map (val ds y)).getD false) ∧
        (∀ x : Fin old → Bool, ∀ y : Fin new → Bool,
          (∀ (w : Fin old) (r : ℕ), init w = some r → x w = val ds y r) →
          (∀ j < gs.length, ∀ r, refs.getD (old+j) none = some r → j ∈ kept) →
          ∀ w r, refs.getD w none = some r → val gs x w = val ds y r) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
        intro _
        let refs := List.ofFn init
        have href (w : Fin old) : refs.getD w.val none = init w := by
          simp [refs, List.getD_eq_getElem?_getD, w.isLt]
        refine ⟨[],refs,∅,?_,by simp [refs],href,?_,by simp,by simp,?_,?_,?_,?_⟩
        · intro i g h
          simp at h
        · intro i r e
          by_cases hi : i < old
          · let a : Fin old := ⟨i,hi⟩
            exact Nat.lt_of_lt_of_le (bounds a r ((href a).symm.trans e)) (by simp)
          · have none : refs.getD i none = none := List.getD_eq_default _ _ (by simpa [refs] using Nat.le_of_not_gt hi)
            rw [none] at e
            contradiction
        · intro i g get
          simp at get
        · intro i g get
          simp at get
        · intro x y agree i
          by_cases hi : i < old
          · let a : Fin old := ⟨i,hi⟩
            rw [show refs.getD i none = init a from href a, show val [] x i = x a from rawVal x a]
            exact agree a
          · rw [valOutside [] x i (by simpa using Nat.le_of_not_gt hi),
              List.getD_eq_default _ _ (by simpa [refs] using Nat.le_of_not_gt hi)]
            rfl
        · intro x y agree _ i r e
          by_cases hi : i < old
          · let a : Fin old := ⟨i,hi⟩
            exact (rawVal x a).trans (agree a r ((href a).symm.trans e))
          · have none : refs.getD i none = none := List.getD_eq_default _ _ (by simpa [refs] using Nat.le_of_not_gt hi)
            rw [none] at e
            contradiction
    | append_singleton gs g ih =>
        intro ly
        obtain ⟨ds,refs,kept,ld,len,rawRef,refBounds,range,card,noKeep,zeros,exactly,on⟩ :=
          ih (parentLayout old gs g ly)
        have endGate : (gs ++ [g])[gs.length]? = some g := by
          rw [List.getElem?_append_right (by rfl), Nat.sub_self]
          rfl
        obtain ⟨op,two,back⟩ := ly gs.length g endGate
        obtain ⟨a,b,pins⟩ := List.length_eq_two.mp two
        have ha : a < old+gs.length := back a (by simp [pins])
        have hb : b < old+gs.length := back b (by simp [pins])
        let p := refs.getD a none
        let q := refs.getD b none
        let j := gs.length
        have jLength : (gs ++ [g]).length = j+1 := by simp [j]
        let read {k : ℕ} (D : List Gate) (y : Fin k → Bool) (r : Option ℕ) :=
          (r.map (val D y)).getD false
        have advance (D : List Gate) (kRef : Option ℕ) (keep : Bool)
            (dl : layout new D)
            (dlen : D.length = ds.length + (if keep then 1 else 0))
            (dSame : ∀ (y : Fin new → Bool) (r : ℕ), r < new + ds.length → val D y r = val ds y r)
            (pinRef : ∀ r, kRef = some r → r < new + D.length)
            (goodKeep : keep = true → p.isSome = true ∧ q.isSome = true)
            (badPin : p = none → q = none → kRef = none)
            (outEq : ∀ y : Fin new → Bool,
              g.op.eval [read ds y p, read ds y q] = read D y kRef)
            (okSome : keep = true → ∀ r, kRef = some r →
              ∃ r₁ r₂, p = some r₁ ∧ q = some r₂ ∧
                ∀ y : Fin new → Bool, g.op.eval [val ds y r₁,val ds y r₂] = val D y r) :
            ∃ ds' : List Gate, ∃ refs' : List (Option ℕ), ∃ kept' : Finset ℕ,
              layout new ds' ∧ refs'.length = old + (gs ++ [g]).length ∧
              (∀ w : Fin old, refs'.getD w.val none = init w) ∧
              (∀ w r, refs'.getD w none = some r → r < new + ds'.length) ∧
              kept' ⊆ Finset.range (gs ++ [g]).length ∧ kept'.card = ds'.length ∧
              (∀ l h, (gs ++ [g])[l]? = some h → (∃ i : Fin old, i.val ∈ h.inputs ∧ init i = none) →
                l ∉ kept') ∧
              (∀ l h, (gs ++ [g])[l]? = some h →
                (∀ i ∈ h.inputs, ∃ w : Fin old, w.val = i ∧ init w = none) →
                refs'.getD (old+l) none = none) ∧
              (∀ x : Fin old → Bool, ∀ y : Fin new → Bool,
                (∀ w : Fin old, x w = ((init w).map (val ds' y)).getD false) →
                ∀ w, val (gs++[g]) x w = ((refs'.getD w none).map (val ds' y)).getD false) ∧
              (∀ x : Fin old → Bool, ∀ y : Fin new → Bool,
                (∀ (w : Fin old) (r : ℕ), init w = some r → x w = val ds' y r) →
                (∀ l < (gs++[g]).length, ∀ r, refs'.getD (old+l) none = some r → l ∈ kept') →
                ∀ w r, refs'.getD w none = some r → val (gs++[g]) x w = val ds' y r) := by
          let rs := refs ++ [kRef]
          let K := if keep then insert j kept else kept
          have kLt (l : ℕ) (h : l ∈ kept) : l < j := Finset.mem_range.mp (range h)
          have same (w : ℕ) (hw : w < old+j) : rs.getD w none = refs.getD w none :=
            List.getD_append _ _ _ _ (by rw [len]; exact hw)
          have last : rs.getD (old+j) none = kRef := by
            change (refs ++ [kRef]).getD (old+j) none = kRef
            rw [List.getD_append_right _ _ _ _ (by rw [len]), len, Nat.sub_self]
            rfl
          have missing (w : ℕ) (hw : old+(j+1) ≤ w) : rs.getD w none = none :=
            List.getD_eq_default _ _ (by simp [rs,len]; omega)
          have oldK (l : ℕ) (hl : l < j) : l ∈ K ↔ l ∈ kept := by
            cases keep <;> simp [K, show l ≠ j by omega]
          have readEq (y : Fin new → Bool) (r : Option ℕ)
              (hr : ∀ z, r = some z → z < new+ds.length) : read D y r = read ds y r := by
            cases r with
            | none => rfl
            | some z => exact dSame y z (hr z rfl)
          have liftInit (y : Fin new → Bool) (w : Fin old) :
              read D y (init w) = read ds y (init w) :=
            readEq y _ (fun z h => Nat.lt_of_lt_of_le (bounds w z h) (by omega))
          have loc (l : ℕ) (h : Gate) (get : (gs ++ [g])[l]? = some h) :
              l < j ∨ (l = j ∧ h = g) := by
            have stat := (List.getElem?_eq_some_iff.mp get).1
            by_cases hlt : l < j
            · exact Or.inl hlt
            · rw [jLength] at stat
              have eq : l = j := by omega
              subst l
              rw [endGate] at get
              exact Or.inr ⟨rfl,(Option.some.inj get).symm⟩
          refine ⟨D,rs,K,dl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · simp only [rs,List.length_append,List.length_cons,List.length_nil,len,jLength]
            omega
          · intro w
            rw [same w.val (by have := w.isLt; omega), rawRef]
          · intro w r e
            by_cases lo : w < old+j
            · rw [same w lo] at e
              have b := refBounds w r e
              omega
            · by_cases eq : w = old+j
              · simpa only [eq,last] using pinRef r (by simpa only [eq,last] using e)
              · rw [missing w (by omega)] at e
                contradiction
          · intro l hl
            apply Finset.mem_range.mpr
            rw [jLength]
            cases keep
            · exact Nat.lt_succ_of_lt (kLt l hl)
            · simp only [K,ite_true,Finset.mem_insert] at hl
              rcases hl with eq | h
              · omega
              · exact Nat.lt_succ_of_lt (kLt l h)
          · cases keep
            · simpa [K,card] using dlen.symm
            · have nj : j ∉ kept := fun h => (Nat.lt_irrefl _ (kLt j h))
              simp [K,Finset.card_insert_of_notMem nj,card,dlen]
          · intro l h get missingPin
            rcases loc l h get with hl | ⟨rfl,rfl⟩
            · rw [oldK l hl]
              apply noKeep l h _ missingPin
              rwa [List.getElem?_append_left hl] at get
            · obtain ⟨u,hu,absent⟩ := missingPin
              have raw := rawRef u
              rw [pins] at hu
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
              cases keep
              · exact fun hj => Nat.lt_irrefl _ (kLt j hj)
              · have keepYes := goodKeep rfl
                rcases hu with h | h
                · have noneP : p = none := by dsimp only [p]; rw [← h,raw,absent]
                  simp [noneP] at keepYes
                · have noneQ : q = none := by dsimp only [q]; rw [← h,raw,absent]
                  simp [noneQ] at keepYes
          · intro l h get allMissing
            rcases loc l h get with hl | ⟨rfl,rfl⟩
            · rw [same _ (by omega)]
              exact zeros l h (by rwa [List.getElem?_append_left hl] at get) allMissing
            · rw [last]
              apply badPin
              · obtain ⟨w,e,absent⟩ := allMissing a (by simp [pins])
                dsimp only [p]
                rw [← e,rawRef,absent]
              · obtain ⟨w,e,absent⟩ := allMissing b (by simp [pins])
                dsimp only [q]
                rw [← e,rawRef,absent]
          · intro x y agree w
            have agreeOld : ∀ u : Fin old, x u = read ds y (init u) :=
              fun u => (agree u).trans (liftInit y u)
            by_cases lo : w < old+j
            · rw [oldVal gs g x w lo,exactly x y agreeOld w,same w lo]
              exact (readEq y _ (refBounds w)).symm
            · by_cases atJ : w = old+j
              · subst w
                rw [last,atLast gs g x,pins]
                simp only [List.map_cons,List.map_nil]
                rw [exactly x y agreeOld a,exactly x y agreeOld b]
                exact outEq y
              · have hi : old+(gs++[g]).length ≤ w := by rw [jLength]; omega
                rw [valOutside _ x w hi,missing w (by omega)]
                rfl
          · intro x y agree allSome w r e
            have agreeOld : ∀ (u : Fin old) (z : ℕ), init u = some z → x u = val ds y z := by
              intro u z eq
              exact (agree u z eq).trans (dSame y z (Nat.lt_of_lt_of_le (bounds u z eq) (by omega)))
            have someOld : ∀ l < gs.length, ∀ z, refs.getD (old+l) none = some z → l ∈ kept := by
              intro l hl z ze
              apply (oldK l hl).mp
              apply allSome l (by rw [jLength]; omega) z
              rwa [same _ (by omega)]
            by_cases lo : w < old+j
            · rw [same w lo] at e
              exact (oldVal gs g x w lo).trans ((on x y agreeOld someOld w r e).trans
                (dSame y r (refBounds w r e)).symm)
            · by_cases atJ : w = old+j
              · subst w
                rw [last] at e
                have jmem := allSome j (by rw [jLength]; omega) r (last.trans e)
                have yes : keep = true := by
                  cases keep
                  · exact (Nat.lt_irrefl _ (kLt j jmem)).elim
                  · rfl
                obtain ⟨r₁,r₂,ea,eb,eval⟩ := okSome yes r e
                rw [atLast gs g x,pins]
                simp only [List.map_cons,List.map_nil]
                rw [on x y agreeOld someOld a r₁ ea,on x y agreeOld someOld b r₂ eb]
                exact eval y
              · rw [missing w (by omega)] at e
                contradiction
        cases hp : p with
        | none =>
          cases hq : q with
          | none =>
            apply advance ds none false ld (by simp)
            · intro y r hr; rfl
            · simp
            · simp
            · simp
            · intro y
              cases op with
              | inl h => simp [h, hp,hq,read,evalAnd]
              | inr h => simp [h, hp,hq,read,evalOr]
            · simp
          | some r =>
            rcases op with ho | ho
            · apply advance ds none false ld (by simp)
              · intro y z hz; rfl
              · simp
              · simp
              · simp
              · intro y
                simp [ho,hp,hq,read,evalAnd]
              · simp
            · apply advance ds (some r) false ld (by simp)
              · intro y z hz; rfl
              · intro z e
                exact Option.some.inj e ▸ refBounds b r hq
              · simp
              · simp [hq]
              · intro y
                simp [ho,hp,hq,read,evalOr]
              · simp
        | some r =>
          cases hq : q with
          | none =>
            rcases op with ho | ho
            · apply advance ds none false ld (by simp)
              · intro y z hz; rfl
              · simp
              · simp
              · simp [hp]
              · intro y
                simp [ho,hp,hq,read,evalAnd]
              · simp
            · apply advance ds (some r) false ld (by simp)
              · intro y z hz; rfl
              · intro z e
                exact Option.some.inj e ▸ refBounds a r hp
              · simp
              · simp [hp]
              · intro y
                simp [ho,hp,hq,read,evalOr]
              · simp
          | some s =>
            let alt : Gate := ⟨g.op,[r,s]⟩
            have av : layout new (ds++[alt]) := within new ds alt ld op (by simp [alt])
              (by
                intro w hw
                simp [alt] at hw
                rcases hw with e | e
                · exact e ▸ refBounds a r hp
                · exact e ▸ refBounds b s hq)
            apply advance (ds++[alt]) (some (new+ds.length)) true av (by simp)
            · exact fun y w hw => oldVal ds alt y w hw
            · intro w e
              have eq := Option.some.inj e
              rw [← eq]
              simp
            · simp [hp,hq]
            · simp [hp,hq]
            · intro y
              rw [show read (ds++[alt]) y (some (new+ds.length)) =
                val (ds++[alt]) y (new+ds.length) from rfl, atLast]
              simp [read,hp,hq,alt]
            · intro _ w e
              have eq := Option.some.inj e
              refine ⟨r,s,hp,hq,?_⟩
              intro y
              rw [← eq,atLast]
              rfl

  have rawAny {k : ℕ} (gs : List Gate) (x : Fin k → Bool) (w : Fin k) :
      val gs x w.val = x w := by
    induction gs using List.reverseRecOn with
    | nil => exact rawVal x w
    | append_singleton gs g ih =>
      rw [oldVal gs g x _ (by have := w.isLt; omega)]
      exact ih

  have readerOf {k : ℕ} (C : Circuit) (u : Fin k) (out : C.output ≠ u.val)
      (x y : Fin k → Bool) (agree : ∀ v : Fin k, v ≠ u → x v = y v)
      (diff : circuitFun k C x ≠ circuitFun k C y) :
      ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ u.val ∈ g.inputs := by
    by_contra missing
    have no (g : Gate) (hg : g ∈ C.gates) : u.val ∉ g.inputs := by
      intro h
      obtain ⟨j,jh⟩ := List.mem_iff_getElem?.mp hg
      exact missing ⟨j,g,jh,h⟩
    have all : ∀ gs : List Gate, (∀ g ∈ gs, u.val ∉ g.inputs) →
        ∀ w, w ≠ u.val → val gs x w = val gs y w := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _ w hw
        by_cases i : w < k
        · let v : Fin k := ⟨w,i⟩
          change val [] x v.val = val [] y v.val
          rw [rawVal,rawVal]
          exact agree v (fun eq => hw (congrArg Fin.val eq))
        · rw [valOutside [] x w (by simpa using Nat.le_of_not_gt i),
            valOutside [] y w (by simpa using Nat.le_of_not_gt i)]
      | append_singleton gs g ih =>
        intro absent w hw
        have useOld : ∀ v, v ≠ u.val → val gs x v = val gs y v :=
          ih (fun h hh => absent h (List.mem_append_left _ hh))
        by_cases lo : w < k + gs.length
        · rw [oldVal gs g x _ lo,oldVal gs g y _ lo]
          exact useOld w hw
        · by_cases atG : w = k + gs.length
          · subst w
            rw [atLast gs g x,atLast gs g y]
            apply congrArg g.op.eval
            apply List.map_congr_left
            intro w h
            exact useOld w (fun eq => absent g (by simp) (eq ▸ h))
          · have hi : k+(gs++[g]).length ≤ w := by simp; omega
            rw [valOutside _ x w hi,valOutside _ y w hi]
    exact diff (all C.gates no C.output out)

  let extendFalse {old new : ℕ} (r : Fin old → Option (Fin new)) (y : Fin new → Bool)
      (w : Fin old) : Bool := ((r w).map y).getD false

  have paidRestriction {old new : ℕ} (C : Circuit) (AO : IsAO2 old C)
      (r : Fin old → Option (Fin new)) (u v : Fin old) (uv : u ≠ v)
      (deadU : r u = none) (deadV : r v = none)
      (readU : ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ u.val ∈ g.inputs)
      (readV : ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ v.val ∈ g.inputs)
      (nonzero : ∃ y, circuitFun old C (extendFalse r y) = true)
      (changes : ∃ (x : Fin old → Bool) (y : Fin new → Bool),
        (∀ w k, r w = some k → x w = y k) ∧
        circuitFun old C x ≠ circuitFun old C (extendFalse r y)) :
      ∃ D : Circuit, IsAO2 new D ∧ D.size + 2 ≤ C.size ∧
        ∀ y, circuitFun new D y = circuitFun old C (extendFalse r y) := by
    let init (w : Fin old) := (r w).map Fin.val
    have legal (w : Fin old) (z : ℕ) (hz : init w = some z) : z < new := by
      cases eq : r w with
      | none => simp [init, eq] at hz
      | some i =>
        have iz : i.val = z := by simpa [init, eq] using hz
        exact iz ▸ i.isLt
    obtain ⟨ds,refs,kept,ld,_,_,_,range,card,noKeep,zeros,exactly,on⟩ :=
      sweep init legal C.gates (ownGate old C AO)
    have lift (y : Fin new → Bool) (w : Fin old) :
        extendFalse r y w = ((init w).map (val ds y)).getD false := by
      cases eq : r w with
      | none => simp [extendFalse,init,eq]
      | some i => simpa [extendFalse, init, eq] using (rawAny ds y i).symm
    obtain ⟨yes, hy⟩ := nonzero
    have same := exactly (extendFalse r yes) yes (lift yes) C.output
    change val C.gates (extendFalse r yes) C.output = true at hy
    rw [hy] at same
    cases hRef : refs.getD C.output none with
    | none =>
      rw [hRef] at same
      contradiction
    | some w =>
      let D : Circuit := ⟨ds,w⟩
      have payTwo (a b : ℕ) (ne : a ≠ b) (ha : a < C.gates.length) (hb : b < C.gates.length)
          (offA : a ∉ kept) (offB : b ∉ kept) : ds.length+2 ≤ C.gates.length := by
        have sub : insert a (insert b kept) ⊆ Finset.range C.gates.length := by
          intro j hj
          simp only [Finset.mem_insert] at hj
          rcases hj with eq | eq | hk
          · exact Finset.mem_range.mpr (eq.symm ▸ ha)
          · exact Finset.mem_range.mpr (eq.symm ▸ hb)
          · exact range hk
        have aNot : a ∉ insert b kept := by simp [ne,offA]
        have tt := Finset.card_le_card sub
        rw [Finset.card_insert_of_notMem aNot, Finset.card_insert_of_notMem offB,
          Finset.card_range, card] at tt
        omega
      have safe : ∀ y, circuitFun new D y = circuitFun old C (extendFalse r y) := by
        intro y
        have agrees := exactly (extendFalse r y) y (lift y) C.output
        rw [hRef] at agrees
        exact agrees.symm
      refine ⟨D,fromLayout new D ld,?_,safe⟩
      change ds.length + 2 ≤ C.gates.length
      obtain ⟨a,g,ga,au⟩ := readU
      obtain ⟨b,h,hb,bv⟩ := readV
      have al := (List.getElem?_eq_some_iff.mp ga).1
      have bl := (List.getElem?_eq_some_iff.mp hb).1
      have aa : a ∉ kept := noKeep a g ga ⟨u,au,by simp [init,deadU]⟩
      have bb : b ∉ kept := noKeep b h hb ⟨v,bv,by simp [init,deadV]⟩
      by_cases ab : a ≠ b
      · exact payTwo a b ab al bl aa bb
      · have bEq : b = a := (of_not_not ab).symm
        subst b
        have gEq : h = g := Option.some.inj (hb.symm.trans ga)
        subst h
        have two := (ownGate old C AO a g ga).2.1
        obtain ⟨s,t,pins⟩ := List.length_eq_two.mp two
        have different : u.val ≠ v.val := fun e => uv (Fin.val_injective e)
        have allAbsent : ∀ i ∈ g.inputs, ∃ d : Fin old, d.val = i ∧ init d = none := by
          rw [pins] at au bv ⊢
          simp only [List.mem_cons,List.not_mem_nil,or_false] at au bv ⊢
          intro i zi
          rcases au with eu | eu <;> rcases bv with ev | ev
          · exact (different (eu.trans ev.symm)).elim
          · rcases zi with ei | ei
            · exact ⟨u,eu.trans ei.symm,by simp [init,deadU]⟩
            · exact ⟨v,ev.trans ei.symm,by simp [init,deadV]⟩
          · rcases zi with ei | ei
            · exact ⟨v,ev.trans ei.symm,by simp [init,deadV]⟩
            · exact ⟨u,eu.trans ei.symm,by simp [init,deadU]⟩
          · exact (different (eu.trans ev.symm)).elim
        have aZero := zeros a g ga allAbsent
        by_contra notPaid
        have allKept : ∀ j < C.gates.length, ∀ i, refs.getD (old+j) none = some i → j ∈ kept := by
          intro j jl i e
          have ne : a ≠ j := by
            rintro rfl
            rw [aZero] at e
            contradiction
          by_contra no
          exact notPaid (payTwo a j ne al jl aa no)
        obtain ⟨x,y,agrees,neq⟩ := changes
        have agree (u : Fin old) (i : ℕ) (h : init u = some i) : x u = val ds y i := by
          cases e : r u with
          | none => simp [init,e] at h
          | some k =>
            have ieq : k.val = i := by simpa [init,e] using h
            rw [← ieq,rawAny]
            exact agrees u k e
        have stable : circuitFun old C x = circuitFun new D y :=
          on x y agree allKept C.output w hRef
        exact neq (stable.trans (safe y))

  let inducedEdges {k : ℕ} (E : Finset (Fin (k + 1) × Fin (k + 1)))
      (i j : Fin (k + 1)) : Finset (Fin k × Fin k) :=
    Finset.univ.filter fun e => (i.succAbove e.1, j.succAbove e.2) ∈ E

  have mem_inducedEdges {k : ℕ} (E : Finset (Fin (k + 1) × Fin (k + 1)))
      (i j : Fin (k + 1)) (a b : Fin k) :
      (a, b) ∈ inducedEdges E i j ↔ (i.succAbove a, j.succAbove b) ∈ E := by
    simp [inducedEdges]

  have inducedPerm {k : ℕ} (p : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
      ∃ p' : Equiv.Perm (Fin k), ∀ a, (p i).succAbove (p' a) = p (i.succAbove a) := by
    have existsImage (a : Fin k) : ∃ b, (p i).succAbove b = p (i.succAbove a) :=
      Fin.exists_succAbove_eq_iff.mpr (fun h => Fin.succAbove_ne i a (p.injective h))
    choose f hf using existsImage
    have injective : Function.Injective f := by
      intro a b h
      apply (Fin.succAboveEmb i).injective
      change i.succAbove a = i.succAbove b
      apply p.injective
      rw [← hf a, ← hf b, h]
    exact ⟨Equiv.ofBijective f ⟨injective, Finite.surjective_of_injective injective⟩, hf⟩

  have induced_card {k : ℕ} (E : Finset (Fin (k + 1) × Fin (k + 1)))
      (i j : Fin (k + 1)) (present : (i, j) ∈ E)
      (row : ∀ b, (i, b) ∈ E → b = j) (col : ∀ a, (a, j) ∈ E → a = i) :
      E.card = (inducedEdges E i j).card + 1 := by
    let emb := (Fin.succAboveEmb i).prodMap (Fin.succAboveEmb j)
    have mapped : (inducedEdges E i j).map emb = E.erase (i, j) := by
      ext e
      rcases e with ⟨a, b⟩
      rw [Finset.mem_map, Finset.mem_erase]
      constructor
      · rintro ⟨⟨u, v⟩, h, eq⟩
        change (i.succAbove u, j.succAbove v) = (a, b) at eq
        rw [← eq]
        exact ⟨fun he => Fin.succAbove_ne i u (congrArg Prod.fst he),
          (mem_inducedEdges E i j u v).mp h⟩
      · rintro ⟨hne, he⟩
        have ha : a ≠ i := by
          intro h
          subst a
          exact hne (Prod.ext rfl (row b he))
        have hb : b ≠ j := by
          intro h
          subst b
          exact hne (Prod.ext (col a he) rfl)
        obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq_iff.mpr ha
        obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq_iff.mpr hb
        refine ⟨(u, v), (mem_inducedEdges E i j u v).mpr ?_, ?_⟩
        · simpa only [hu, hv] using he
        · exact Prod.ext hu hv
    rw [← Finset.card_erase_add_one present, ← mapped, Finset.card_map]

  have induced_noFour {k : ℕ} (E : Finset (Fin (k + 1) × Fin (k + 1)))
      (i j : Fin (k + 1))
      (noFour : ∀ a b c d, a ≠ b → c ≠ d →
        ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) :
      ∀ a b c d, a ≠ b → c ≠ d →
        ¬ ((a, c) ∈ inducedEdges E i j ∧ (a, d) ∈ inducedEdges E i j ∧
          (b, c) ∈ inducedEdges E i j ∧ (b, d) ∈ inducedEdges E i j) := by
    intro a b c d ab cd h
    apply noFour (i.succAbove a) (i.succAbove b) (j.succAbove c) (j.succAbove d)
      ((Fin.succAboveEmb i).injective.ne ab) ((Fin.succAboveEmb j).injective.ne cd)
    exact ⟨(mem_inducedEdges E i j a c).mp h.1, (mem_inducedEdges E i j a d).mp h.2.1,
      (mem_inducedEdges E i j b c).mp h.2.2.1, (mem_inducedEdges E i j b d).mp h.2.2.2⟩

  have induced_matching {k : ℕ} (E : Finset (Fin (k + 1) × Fin (k + 1)))
      (p : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) (matching : ∀ a, (a, p a) ∈ E) :
      ∃ p' : Equiv.Perm (Fin k), (∀ a, (p i).succAbove (p' a) = p (i.succAbove a)) ∧
        (∀ a, (a, p' a) ∈ inducedEdges E i (p i)) := by
    obtain ⟨p', hp'⟩ := inducedPerm p i
    refine ⟨p', hp', fun a => (mem_inducedEdges E i (p i) a (p' a)).mpr ?_⟩
    rw [hp' a]
    exact matching (i.succAbove a)

  let extendInput {k : ℕ} (i j : Fin (k + 1)) (z : Fin (k + k) → Bool) :
      Fin ((k + 1) + (k + 1)) → Bool :=
    Fin.addCases (i.insertNth false (fun a => z (Fin.castAdd k a)))
      (j.insertNth false (fun b => z (Fin.natAdd k b)))

  have extendInput_left_cut {k : ℕ} (i j : Fin (k + 1)) (z : Fin (k + k) → Bool) :
      extendInput i j z (Fin.castAdd (k + 1) i) = false := by
    dsimp only [extendInput]
    rw [Fin.addCases_left, Fin.insertNth_apply_same]

  have extendInput_right_cut {k : ℕ} (i j : Fin (k + 1)) (z : Fin (k + k) → Bool) :
      extendInput i j z (Fin.natAdd (k + 1) j) = false := by
    dsimp only [extendInput]
    rw [Fin.addCases_right, Fin.insertNth_apply_same]

  have extendInput_left_keep {k : ℕ} (i j : Fin (k + 1)) (z : Fin (k + k) → Bool)
      (a : Fin k) : extendInput i j z (Fin.castAdd (k + 1) (i.succAbove a)) =
      z (Fin.castAdd k a) := by
    dsimp only [extendInput]
    rw [Fin.addCases_left, Fin.insertNth_apply_succAbove]

  have extendInput_right_keep {k : ℕ} (i j : Fin (k + 1)) (z : Fin (k + k) → Bool)
      (b : Fin k) : extendInput i j z (Fin.natAdd (k + 1) (j.succAbove b)) =
      z (Fin.natAdd k b) := by
    dsimp only [extendInput]
    rw [Fin.addCases_right, Fin.insertNth_apply_succAbove]

  have induced_eval {k : ℕ} (E : Finset (Fin (k + 1) × Fin (k + 1)))
      (i j : Fin (k + 1)) (z : Fin (k + k) → Bool) :
      decide (∃ a b, (a, b) ∈ E ∧ extendInput i j z (Fin.castAdd (k + 1) a) = true ∧
        extendInput i j z (Fin.natAdd (k + 1) b) = true) =
      decide (∃ a b, (a, b) ∈ inducedEdges E i j ∧ z (Fin.castAdd k a) = true ∧
        z (Fin.natAdd k b) = true) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, he, ha, hb⟩
      have hane : a ≠ i := by
        rintro rfl
        rw [extendInput_left_cut] at ha
        simp at ha
      have hbne : b ≠ j := by
        rintro rfl
        rw [extendInput_right_cut] at hb
        simp at hb
      obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hane
      obtain ⟨v, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hbne
      exact ⟨u, v, (mem_inducedEdges E i j u v).mpr he,
        by rwa [extendInput_left_keep] at ha, by rwa [extendInput_right_keep] at hb⟩
    · rintro ⟨a, b, he, ha, hb⟩
      exact ⟨i.succAbove a, j.succAbove b, (mem_inducedEdges E i j a b).mp he,
        by rwa [extendInput_left_keep], by rwa [extendInput_right_keep]⟩




  let inputMap {k : ℕ} (i j : Fin (k + 1)) :
      Fin ((k + 1) + (k + 1)) → Option (Fin (k + k)) :=
    Fin.addCases (fun a => (finSuccEquiv' i a).map (Fin.castAdd k))
      (fun b => (finSuccEquiv' j b).map (Fin.natAdd k))

  have inputMap_left_cut {k : ℕ} (i j : Fin (k + 1)) :
      inputMap i j (Fin.castAdd (k + 1) i) = none := by
    dsimp only [inputMap]
    rw [Fin.addCases_left, finSuccEquiv'_at]
    rfl

  have inputMap_right_cut {k : ℕ} (i j : Fin (k + 1)) :
      inputMap i j (Fin.natAdd (k + 1) j) = none := by
    dsimp only [inputMap]
    rw [Fin.addCases_right, finSuccEquiv'_at]
    rfl

  have inputMap_left_keep {k : ℕ} (i j : Fin (k + 1)) (a : Fin k) :
      inputMap i j (Fin.castAdd (k + 1) (i.succAbove a)) = some (Fin.castAdd k a) := by
    dsimp only [inputMap]
    rw [Fin.addCases_left, finSuccEquiv'_succAbove]
    rfl

  have inputMap_right_keep {k : ℕ} (i j : Fin (k + 1)) (b : Fin k) :
      inputMap i j (Fin.natAdd (k + 1) (j.succAbove b)) = some (Fin.natAdd k b) := by
    dsimp only [inputMap]
    rw [Fin.addCases_right, finSuccEquiv'_succAbove]
    rfl

  have extendFalse_inputMap {k : ℕ} (i j : Fin (k + 1)) (y : Fin (k + k) → Bool) :
      extendFalse (inputMap i j) y = extendInput i j y := by
    funext w
    refine Fin.addCases (motive := fun w => extendFalse (inputMap i j) y w = extendInput i j y w)
      ?_ ?_ w
    · intro a
      refine Fin.succAboveCases i ?_ ?_ a
      · simp only [extendFalse, inputMap_left_cut, extendInput_left_cut]
        rfl
      · intro b
        simp only [extendFalse, inputMap_left_keep, extendInput_left_keep]
        rfl
    · intro b
      refine Fin.succAboveCases j ?_ ?_ b
      · simp only [extendFalse, inputMap_right_cut, extendInput_right_cut]
        rfl
      · intro a
        simp only [extendFalse, inputMap_right_keep, extendInput_right_keep]
        rfl

  let evalEdges {n : ℕ} (E : Finset (Fin n × Fin n)) (x : Fin (n + n) → Bool) : Bool :=
    decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)

  let markPair {n : ℕ} (u v : Fin n) (w : Fin n) : Bool := decide (w = u ∨ w = v)

  have left_ne_right {n : ℕ} (a b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n b := by
    intro h
    have e := congrArg Fin.val h
    change a.val = n + b.val at e
    omega

  have eval_mark_edge {n : ℕ} (E : Finset (Fin n × Fin n)) (a b : Fin n)
      (h : (a, b) ∈ E) : evalEdges E (markPair (Fin.castAdd n a) (Fin.natAdd n b)) = true := by
    exact decide_eq_true ⟨a, b, h, by simp [markPair], by simp [markPair]⟩

  have eval_mark_singleton {n : ℕ} (E : Finset (Fin n × Fin n)) (u : Fin (n + n)) :
      evalEdges E (markPair u u) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨a, b, _, ha, hb⟩ := of_decide_eq_true h
    have la : Fin.castAdd n a = u := by simpa [markPair] using ha
    have rb : Fin.natAdd n b = u := by simpa [markPair] using hb
    exact left_ne_right a b (la.trans rb.symm)

  have rawOutput {n : ℕ} (C : Circuit) (u : Fin n) (x : Fin n → Bool)
      (h : C.output = u.val) : circuitFun n C x = x u := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun wv => w.getD wv false)]
    have keep : ∀ (gs : List Gate) (w : List Bool), u.val < w.length →
        (gs.foldl step w).getD u.val false = w.getD u.val false := by
      intro gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        intro w hl
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hl
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = x u
    rw [h, keep _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, u.isLt]

  have isolatedStep
      (paidRestriction : ∀ {old new : ℕ} (C : Circuit), IsAO2 old C →
        ∀ (r : Fin old → Option (Fin new)) (u v : Fin old), u ≠ v → r u = none → r v = none →
        (∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ u.val ∈ g.inputs) →
        (∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ v.val ∈ g.inputs) →
        (∃ y, circuitFun old C (extendFalse r y) = true) →
        (∃ x y, (∀ w q, r w = some q → x w = y q) ∧
          circuitFun old C x ≠ circuitFun old C (extendFalse r y)) →
        ∃ D : Circuit, IsAO2 new D ∧ D.size + 2 ≤ C.size ∧
          ∀ y, circuitFun new D y = circuitFun old C (extendFalse r y))
      (readerOf : ∀ {old : ℕ} (C : Circuit) (u : Fin old), C.output ≠ u.val →
        ∀ x y : Fin old → Bool, (∀ w, w ≠ u → x w = y w) →
        circuitFun old C x ≠ circuitFun old C y →
        ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ u.val ∈ g.inputs)
      {k : ℕ} (E : Finset (Fin (k + 1) × Fin (k + 1))) (p : Equiv.Perm (Fin (k + 1)))
      (i : Fin (k + 1)) (C : Circuit) (more : k + 1 < E.card)
      (noFour : ∀ a b c d, a ≠ b → c ≠ d →
        ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
      (matching : ∀ a, (a, p a) ∈ E) (row : ∀ b, (i, b) ∈ E → b = p i)
      (col : ∀ a, (a, p i) ∈ E → a = i) (AO : IsAO2 ((k + 1) + (k + 1)) C)
      (sem : ∀ x, circuitFun ((k + 1) + (k + 1)) C x = evalEdges E x) :
      ∃ (E' : Finset (Fin k × Fin k)) (p' : Equiv.Perm (Fin k)) (D : Circuit),
        E.card = E'.card + 1 ∧ (∀ a b c d, a ≠ b → c ≠ d →
          ¬ ((a, c) ∈ E' ∧ (a, d) ∈ E' ∧ (b, c) ∈ E' ∧ (b, d) ∈ E')) ∧
        (∀ a, (a, p' a) ∈ E') ∧ IsAO2 (k + k) D ∧ D.size + 2 ≤ C.size ∧
        ∀ y, circuitFun (k + k) D y = evalEdges E' y := by
    let u := Fin.castAdd (k + 1) i
    let v := Fin.natAdd (k + 1) (p i)
    let r := inputMap i (p i)
    let E' := inducedEdges E i (p i)
    let edge := markPair u v
    let onlyU := markPair u u
    let onlyV := markPair v v
    have uv : u ≠ v := left_ne_right i (p i)
    have deadU : r u = none := inputMap_left_cut i (p i)
    have deadV : r v = none := inputMap_right_cut i (p i)
    have count : E.card = E'.card + 1 := induced_card E i (p i) (matching i) row col
    have hEdge : circuitFun ((k + 1) + (k + 1)) C edge = true :=
      (sem edge).trans (eval_mark_edge E i (p i) (matching i))
    have hOnlyU : circuitFun ((k + 1) + (k + 1)) C onlyU = false :=
      (sem onlyU).trans (eval_mark_singleton E u)
    have hOnlyV : circuitFun ((k + 1) + (k + 1)) C onlyV = false :=
      (sem onlyV).trans (eval_mark_singleton E v)
    have outU : C.output ≠ u.val := by
      intro h
      have eq := rawOutput C u onlyU h
      rw [hOnlyU] at eq
      simp [onlyU, markPair] at eq
    have outV : C.output ≠ v.val := by
      intro h
      have eq := rawOutput C v onlyV h
      rw [hOnlyV] at eq
      simp [onlyV, markPair] at eq
    have readU := readerOf C u outU edge onlyV
      (fun w hw => by simp [edge, onlyV, markPair, hw]) (by rw [hEdge, hOnlyV]; decide)
    have readV := readerOf C v outV edge onlyU
      (fun w hw => by simp [edge, onlyU, markPair, hw]) (by rw [hEdge, hOnlyU]; decide)
    have restrict (y : Fin (k + k) → Bool) :
        circuitFun ((k + 1) + (k + 1)) C (extendFalse r y) = evalEdges E' y := by
      rw [show r = inputMap i (p i) from rfl, extendFalse_inputMap, sem]
      exact induced_eval E i (p i) y
    have nonzero : ∃ y, circuitFun ((k + 1) + (k + 1)) C (extendFalse r y) = true := by
      have positive : 0 < E'.card := by omega
      obtain ⟨⟨a, b⟩, he⟩ := Finset.card_pos.mp positive
      refine ⟨markPair (Fin.castAdd k a) (Fin.natAdd k b), ?_⟩
      rw [restrict]
      exact eval_mark_edge E' a b he
    have changes : ∃ (x : Fin ((k + 1) + (k + 1)) → Bool) (y : Fin (k + k) → Bool),
        (∀ w q, r w = some q → x w = y q) ∧
        circuitFun ((k + 1) + (k + 1)) C x ≠
          circuitFun ((k + 1) + (k + 1)) C (extendFalse r y) := by
      refine ⟨edge, fun _ => false, ?_, ?_⟩
      · intro w q h
        have wu : w ≠ u := by
          rintro rfl
          rw [deadU] at h
          contradiction
        have wv : w ≠ v := by
          rintro rfl
          rw [deadV] at h
          contradiction
        simp [edge, markPair, wu, wv]
      · rw [hEdge, restrict]
        simp [evalEdges]
    obtain ⟨D, dAO, dSize, dEval⟩ :=
      paidRestriction C AO r u v uv deadU deadV readU readV nonzero changes
    obtain ⟨p', _, match'⟩ := induced_matching E p i matching
    exact ⟨E', p', D, count, induced_noFour E i (p i) noFour, match', dAO, dSize,
      fun y => (dEval y).trans (restrict y)⟩

  have bound : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n))
      (C : Circuit), n < E.card →
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
      (∀ a, (a,p a) ∈ E) → IsAO2 (n+n) C →
      (∀ x, circuitFun (n+n) C x = evalEdges E x) →
      E.card + n ≤ C.size+1 := by
    intro n
    induction n with
    | zero =>
      intro E _ _ more
      have empty : E = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        rintro ⟨a,b⟩
        exact Fin.elim0 a
      simp [empty] at more
    | succ k ih =>
      intro E p C more noFour matching AO sem
      by_cases cut : ∃ i : Fin (k+1),
          (∀ j, (i,j) ∈ E → j = p i) ∧ (∀ a, (a,p i) ∈ E → a = i)
      · obtain ⟨i,hrow,hcol⟩ := cut
        obtain ⟨E', p', D, eqSize, noFour', matching', AO', paid, sem'⟩ :=
          isolatedStep paidRestriction readerOf E p i C more noFour matching hrow hcol AO sem
        have more' : k < E'.card := by omega
        have lower := ih E' p' D more' noFour' matching' AO' sem'
        omega
      · by_cases leaf : (∃ i, ∀ j, (i,j) ∈ E → j = p i) ∨ ∃ j, ∀ i, (i,j) ∈ E → p i = j
        · apply genuineLeaf (k+1) E p C more noFour matching AO sem _ leaf
          intro i isol
          exact cut ⟨i, isol⟩
        · exact core (k+1) E p C more noFour matching AO sem leaf
  intro n E p C excess _ noFour matching AO sem _
  exact bound n E p C excess noFour matching AO sem
