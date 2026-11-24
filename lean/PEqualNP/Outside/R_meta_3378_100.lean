import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.GenericRejection

-- Count strict unions among rejecting OR gates that have a path to the output.
theorem PEqualNP.Outside.R_meta_3378_100
    (emptySharing : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      300 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → C.output < n+n+C.size → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      let offLines : Finset (Fin n) := ∅
      let A (l : Fin n) (w : ℕ) := Finset.univ.filter (fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w)
      (∃ w a b, n+n ≤ w ∧ w < n+n+C.size ∧
        Relation.ReflTransGen (fun u v : ℕ => n+n ≤ v ∧ v < n+n+C.size ∧ u < v ∧
          u ∈ (gateAt C (v-(n+n))).inputs) w C.output ∧
        (gateAt C (w-(n+n))).op = .or ∧ (gateAt C (w-(n+n))).inputs = [a,b] ∧
        ∃ K : Finset (Fin n), 100 < K.card ∧ (∀ p : Fin n, wireValue C (incidenceInput {p} offLines) w = false) ∧
          ∀ l ∈ K, wireValue C (incidenceInput (S l)ᶜ {l}) w = false ∧
            1 < (A l w).card ∧ A l w ⊆ S l ∧ ¬ A l a ⊆ A l b ∧ ¬ A l b ⊆ A l a) →
      n*q ≤ 100*C.size)
    (pencilSharing : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      300 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → C.output < n+n+C.size → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      let offLines : Finset (Fin n) := ∅
      let A (l : Fin n) (w : ℕ) := Finset.univ.filter (fun p : Fin n =>
        wireValue C (incidenceInput {p} {l}) w)
      (∃ w a b, n+n ≤ w ∧ w < n+n+C.size ∧
        Relation.ReflTransGen (fun u v : ℕ => n+n ≤ v ∧ v < n+n+C.size ∧ u < v ∧
          u ∈ (gateAt C (v-(n+n))).inputs) w C.output ∧
        (gateAt C (w-(n+n))).op = .or ∧ (gateAt C (w-(n+n))).inputs = [a,b] ∧
        ∃ K : Finset (Fin n), 100 < K.card ∧ (∃ p : Fin n,
          (∀ r : Fin n, wireValue C (incidenceInput {r} offLines) w = decide (r = p)) ∧
          ∀ l ∈ K, p ∈ S l) ∧
          ∀ l ∈ K, wireValue C (incidenceInput (S l)ᶜ {l}) w = false ∧
            1 < (A l w).card ∧ A l w ⊆ S l ∧ ¬ A l a ⊆ A l b ∧ ¬ A l b ⊆ A l a) →
      n*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨.or,[]⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have mergeBudget {α : Type} [DecidableEq α] (P : ℕ → Finset α)
      (alive good : ℕ → Prop) (n : ℕ)
      (step : ∀ j < n, alive j →
        (P j).card ≤ 1 ∨ (∃ a < j, alive a ∧ P j ⊆ P a) ∨
          (∃ a < j, ∃ b < j, alive a ∧ alive b ∧ P j = P a ∪ P b ∧ good j)) :
      ∀ R : Finset ℕ, R ⊆ Finset.range n → (∀ w ∈ R, alive w) →
      ∃ J : Finset ℕ, J ⊆ Finset.range n ∧ (∀ w ∈ J, good w) ∧
        (R.biUnion P).card ≤ R.card + J.card := by
    induction n with
    | zero =>
      intro R scope active
      have eq : R = ∅ := Finset.subset_empty.mp (by simpa using scope)
      subst R
      exact ⟨∅,by simp,by simp,by simp⟩
    | succ k ih =>
      have prior (w : ℕ) (hw : w < k) := step w (by omega)
      have old_to_next : Finset.range k ⊆ Finset.range (k+1) := Finset.range_mono (by omega)
      intro R scope active
      by_cases peak : k ∈ R
      · let rest := R.erase k
        have inside : rest ⊆ Finset.range k := by
          intro w hw
          obtain ⟨ne,member⟩ := Finset.mem_erase.mp hw
          have lt := Finset.mem_range.mp (scope member)
          exact Finset.mem_range.mpr (by omega)
        have restLive (w : ℕ) (hw : w ∈ rest) : alive w :=
          active w (Finset.mem_erase.mp hw).2
        have rightSize : rest.card + 1 = R.card := Finset.card_erase_add_one peak
        have split : R.biUnion P = P k ∪ rest.biUnion P := by
          rw [← Finset.insert_erase peak,Finset.biUnion_insert]
        have replace (B : Finset ℕ) (hB : B ⊆ Finset.range k)
            (aliveB : ∀ w ∈ B, alive w) (covers : P k ⊆ B.biUnion P) :
            ∃ J : Finset ℕ, J ⊆ Finset.range k ∧ (∀ w ∈ J, good w) ∧
              (R.biUnion P).card ≤ rest.card+B.card+J.card := by
          obtain ⟨J,space,ok,bound⟩ := ih prior (rest∪B) (Finset.union_subset inside hB)
            (fun w hw => (Finset.mem_union.mp hw).elim (restLive w) (aliveB w))
          have subset : R.biUnion P ⊆ (rest∪B).biUnion P := by
            rw [split,Finset.union_biUnion]
            exact Finset.union_subset (covers.trans (Finset.subset_union_right)) Finset.subset_union_left
          have h₁ := Finset.card_le_card subset
          have h₂ := Finset.card_union_le rest B
          exact ⟨J,space,ok,by omega⟩
        rcases step k (by omega) (active k peak) with tiny | ⟨a,ha,la,cover⟩ | ⟨a,ha,b,hb,la,lb,merge,tag⟩
        · obtain ⟨J,space,ok,bound⟩ := ih prior rest inside restLive
          have h : (R.biUnion P).card ≤ (P k).card + (rest.biUnion P).card := by
            rw [split]
            exact Finset.card_union_le _ _
          exact ⟨J,space.trans old_to_next,ok,by omega⟩
        · obtain ⟨J,space,ok,bound⟩ := replace {a} (by simpa using ha)
            (by simpa using la) (by simpa using cover)
          simp only [Finset.card_singleton] at bound
          exact ⟨J,space.trans old_to_next,ok,by omega⟩
        · have sub : ({a,b} : Finset ℕ) ⊆ Finset.range k := by
            intro w hw
            simp only [Finset.mem_insert,Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_range.mpr ha
            · exact Finset.mem_range.mpr hb
          have both : ∀ w ∈ ({a,b} : Finset ℕ), alive w := by
            intro w hw
            simp only [Finset.mem_insert,Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          have cover : P k ⊆ ({a,b} : Finset ℕ).biUnion P := by
            rw [Finset.biUnion_insert,Finset.singleton_biUnion,merge]
          obtain ⟨J,space,ok,bound⟩ := replace {a,b} sub both cover
          have ne : k ∉ J := fun h => (Nat.lt_irrefl k) (Finset.mem_range.mp (space h))
          have csize : (insert k J).card = J.card+1 := Finset.card_insert_of_notMem ne
          have cap : ({a,b} : Finset ℕ).card ≤ 2 :=
            (Finset.card_insert_le ..).trans (by simp)
          refine ⟨insert k J,?_,?_,by omega⟩
          · intro w hw
            rcases Finset.mem_insert.mp hw with rfl | h
            · exact Finset.mem_range.mpr (by omega)
            · exact old_to_next (space h)
          · intro w hw
            rcases Finset.mem_insert.mp hw with rfl | h
            · exact tag
            · exact ok w h
      · have small : R ⊆ Finset.range k := by
          intro w hw
          have lt := Finset.mem_range.mp (scope hw)
          have ne : w ≠ k := fun eq => peak (eq ▸ hw)
          exact Finset.mem_range.mpr (by omega)
        obtain ⟨J,space,ok,bound⟩ := ih prior R small active
        exact ⟨J,space.trans old_to_next,ok,bound⟩

  let wval {n : ℕ} (C : Circuit) (X Y : Finset (Fin n)) (w : ℕ) : Bool :=
    wireValue C (incidenceInput X Y) w

  have len {n : ℕ} (X Y : Finset (Fin n)) : (incidenceInput X Y).length = n+n := by
    delta incidenceInput
    simp

  have raw_point {n : ℕ} (C : Circuit) (X Y : Finset (Fin n)) (x : Fin n) :
      wval C X Y x.val = decide (x ∈ X) := by
    change val C (incidenceInput X Y) x.val = _
    rw [val_input (len X Y) (by have := x.isLt; omega)]
    delta incidenceInput
    have h : x.val < (List.ofFn (fun p : Fin n => decide (p ∈ X))).length := by simp
    rw [List.getD_append _ _ _ _ h,List.getD_eq_getElem _ _ h,List.getElem_ofFn]

  have raw_line {n : ℕ} (C : Circuit) (X Y : Finset (Fin n)) (l : Fin n) :
      wval C X Y (n+l.val) = decide (l ∈ Y) := by
    change val C (incidenceInput X Y) (n+l.val) = _
    rw [val_input (len X Y) (by have := l.isLt; omega)]
    delta incidenceInput
    rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.add_sub_cancel_left]
    have h : l.val < (List.ofFn (fun p : Fin n => decide (p ∈ Y))).length := by simp
    rw [List.getD_eq_getElem _ _ h,List.getElem_ofFn]

  have wires_two {n : ℕ} (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 (n+n) C)
      {j : ℕ} (hj : j < C.size) :
      ∃ a b, a < n+n+j ∧ b < n+n+j ∧ (gateAt C j).inputs = [a,b] ∧
        (((gateAt C j).op = .and ∧ ∀ X Y : Finset (Fin n),
          wval C X Y (n+n+j) = (wval C X Y a && wval C X Y b)) ∨
        ((gateAt C j).op = .or ∧ ∀ X Y : Finset (Fin n),
          wval C X Y (n+n+j) = (wval C X Y a || wval C X Y b))) := by
    have gate : gateAt C j ∈ C.gates := gateAt_mem hj
    obtain ⟨a,b,h⟩ := List.length_eq_two.mp (ao.2.2 _ gate)
    have ha := ao.2.1 j hj a (by simp [h])
    have hb := ao.2.1 j hj b (by simp [h])
    refine ⟨a,b,ha,hb,h,?_⟩
    have value (X Y : Finset (Fin n)) :
        wval C X Y (n+n+j) = (gateAt C j).op.eval [wval C X Y a,wval C X Y b] := by
      change val C (incidenceInput X Y) (n+n+j) = _
      rw [val_gate (len X Y) hj,h]
      simp only [List.map_cons,List.map_nil,ite_eq_left ha,ite_eq_left hb]
      rfl
    rcases ao.1 _ gate with op | op
    · refine Or.inl ⟨op,?_⟩
      intro X Y
      rw [value,op]
      cases wval C X Y a <;> cases wval C X Y b <;> rfl
    · refine Or.inr ⟨op,?_⟩
      intro X Y
      rw [value,op]
      cases wval C X Y a <;> cases wval C X Y b <;> rfl

  have mono {n : ℕ} (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 (n+n) C)
      {X Y X' Y' : Finset (Fin n)} (hx : X ⊆ X') (hy : Y ⊆ Y') :
      ∀ w < n+n+C.size, wval C X Y w = true → wval C X' Y' w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro inrange yes
      by_cases point : w < n
      · let x : Fin n := ⟨w,point⟩
        change wval C X Y x.val = true at yes
        change wval C X' Y' x.val = true
        rw [raw_point] at yes ⊢
        exact decide_eq_true (hx (of_decide_eq_true yes))
      by_cases line : w < n+n
      · let l : Fin n := ⟨w-n,by omega⟩
        have eq : w = n+l.val := by change w = n+(w-n); omega
        rw [eq,raw_line] at yes ⊢
        exact decide_eq_true (hy (of_decide_eq_true yes))
      · let j := w-(n+n)
        have eq : n+n+j = w := by dsimp [j]; omega
        have hj : j < C.size := by dsimp [j]; omega
        obtain ⟨a,b,ha,hb,_,kind⟩ := wires_two C ao hj
        rw [eq] at ha hb kind
        rcases kind with ⟨_,vf⟩ | ⟨_,vf⟩
        · rw [vf] at yes ⊢
          exact Bool.and_eq_true_iff.mpr ⟨ih a ha (by omega) (Bool.and_eq_true_iff.mp yes).1,
            ih b hb (by omega) (Bool.and_eq_true_iff.mp yes).2⟩
        · rw [vf] at yes ⊢
          exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp yes).imp
            (ih a ha (by omega)) (ih b hb (by omega)))

  let support {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
    Finset.univ.filter fun p => wval C {p} Y w = true

  let live (C : Circuit) (n w : ℕ) : Prop :=
    Relation.ReflTransGen (fun a b : ℕ => n+n ≤ b ∧ b < n+n+C.size ∧
      a < b ∧ a ∈ (gateAt C (b-(n+n))).inputs) w C.output

  let strict {n : ℕ} (C : Circuit) (s Y : Finset (Fin n)) (w : ℕ) : Prop :=
    n+n ≤ w ∧ w < n+n+C.size ∧ live C n w ∧ (gateAt C (w-(n+n))).op = .or ∧
      wval C sᶜ Y w = false ∧ 1 < (support C Y w).card ∧ support C Y w ⊆ s ∧
      ∃ a b, (gateAt C (w-(n+n))).inputs = [a,b] ∧
        ¬ support C Y a ⊆ support C Y b ∧ ¬ support C Y b ⊆ support C Y a

  have column {n : ℕ} (C : Circuit) (s Y : Finset (Fin n))
      (ao : PEqualNP.TopForm.IsAO2 (n+n) C) (output : C.output < n+n+C.size)
      (pos : ∀ p ∈ s, C.eval (incidenceInput {p} Y) = true)
      (neg : C.eval (incidenceInput sᶜ Y) = false) :
      ∃ J : Finset ℕ, s.card ≤ J.card+1 ∧ ∀ w ∈ J, strict C s Y w := by
    classical
    let P (w : ℕ) := if wval C sᶜ Y w = false then support C Y w else ∅
    have equals (w : ℕ) (off : wval C sᶜ Y w = false) : P w = support C Y w := by simp [P,off]
    have mems (w : ℕ) (off : wval C sᶜ Y w = false) (p : Fin n) :
        p ∈ P w ↔ wval C {p} Y w = true := by
      rw [equals w off]
      simp [support]
    have contained (w : ℕ) (bound : w < n+n+C.size) (off : wval C sᶜ Y w = false) :
        support C Y w ⊆ s := by
      intro p hp
      by_contra out
      have inc : ({p} : Finset (Fin n)) ⊆ sᶜ := by simp [out]
      have sends := mono C ao inc (show Y ⊆ Y by rfl) w bound (Finset.mem_filter.mp hp).2
      rw [off] at sends
      contradiction
    have step : ∀ w < n+n+C.size, live C n w →
        (P w).card ≤ 1 ∨ (∃ a < w, live C n a ∧ P w ⊆ P a) ∨
          (∃ a < w, ∃ b < w, live C n a ∧ live C n b ∧ P w = P a ∪ P b ∧ strict C s Y w) := by
      intro w limit active
      by_cases small : (P w).card ≤ 1
      · exact Or.inl small
      have off : wval C sᶜ Y w = false := by
        by_contra h
        apply small
        simp [P,h]
      have gate : n+n ≤ w := by
        by_contra! raw
        apply small
        apply Finset.card_le_one.mpr
        intro p hp r hr
        have pp := (mems w off p).mp hp
        have rr := (mems w off r).mp hr
        by_cases h : w < n
        · let i : Fin n := ⟨w,h⟩
          change wval C {p} Y i.val = true at pp
          change wval C {r} Y i.val = true at rr
          rw [raw_point] at pp rr
          exact (Finset.mem_singleton.mp (of_decide_eq_true pp)).symm.trans
            (Finset.mem_singleton.mp (of_decide_eq_true rr))
        · let l : Fin n := ⟨w-n,by omega⟩
          have e : w = n+l.val := by change w = n+(w-n); omega
          rw [e,raw_line] at pp off
          rw [off] at pp
          contradiction
      let j := w-(n+n)
      have e : n+n+j = w := by dsimp [j]; omega
      have hj : j < C.size := by dsimp [j]; omega
      obtain ⟨a,b,ha,hb,pins,kind⟩ := wires_two C ao hj
      rw [e] at ha hb kind
      have la : live C n a :=
        Relation.ReflTransGen.head ⟨gate,limit,ha,by change a ∈ (gateAt C j).inputs; simp [pins]⟩ active
      have lb : live C n b :=
        Relation.ReflTransGen.head ⟨gate,limit,hb,by change b ∈ (gateAt C j).inputs; simp [pins]⟩ active
      rcases kind with ⟨_,value⟩ | ⟨orOp,value⟩
      · have off' := off
        rw [value sᶜ Y] at off'
        rcases Bool.and_eq_false_iff.mp off' with oa | ob
        · refine Or.inr (Or.inl ⟨a,ha,la,?_⟩)
          intro p hp
          have yes := (mems w off p).mp hp
          rw [value {p} Y] at yes
          exact (mems a oa p).mpr (Bool.and_eq_true_iff.mp yes).1
        · refine Or.inr (Or.inl ⟨b,hb,lb,?_⟩)
          intro p hp
          have yes := (mems w off p).mp hp
          rw [value {p} Y] at yes
          exact (mems b ob p).mpr (Bool.and_eq_true_iff.mp yes).2
      · have off' := off
        rw [value sᶜ Y] at off'
        obtain ⟨oa,ob⟩ := Bool.or_eq_false_iff.mp off'
        have join : P w = P a ∪ P b := by
          ext p
          rw [Finset.mem_union,mems w off,mems a oa,mems b ob,value {p} Y,Bool.or_eq_true]
        by_cases coveredA : P a ⊆ P b
        · exact Or.inr (Or.inl ⟨b,hb,lb,by rw [join]; exact Finset.union_subset coveredA (by rfl)⟩)
        by_cases coveredB : P b ⊆ P a
        · exact Or.inr (Or.inl ⟨a,ha,la,by rw [join]; exact Finset.union_subset (by rfl) coveredB⟩)
        have rich : 1 < (support C Y w).card := by rw [← equals w off]; omega
        rw [equals a oa,equals b ob] at coveredA coveredB
        exact Or.inr (Or.inr ⟨a,ha,b,hb,la,lb,join,gate,limit,active,orOp,off,rich,
          contained w limit off,a,b,pins,coveredA,coveredB⟩)
    have off : wval C sᶜ Y C.output = false := neg
    have eq : P C.output = s := by
      apply Finset.Subset.antisymm
      · rw [equals C.output off]
        exact contained C.output output off
      · intro p hp
        exact (mems C.output off p).mpr (pos p hp)
    have range : ({C.output} : Finset ℕ) ⊆ Finset.range (n+n+C.size) := by simpa using output
    have root (w : ℕ) (member : w ∈ ({C.output} : Finset ℕ)) : live C n w := by
      have eqw : w = C.output := Finset.mem_singleton.mp member
      subst w
      exact Relation.ReflTransGen.refl
    obtain ⟨J,_,good,count⟩ := mergeBudget P (live C n) (strict C s Y) (n+n+C.size)
      step {C.output} range root
    simp only [Finset.singleton_biUnion,Finset.card_singleton,eq] at count
    exact ⟨J,by omega,good⟩

  intro q n S C hq shape degree unique ao output accept reject
  have each (l : Fin n) := column C (S l) {l} ao output (accept l)
    (reject _ _ (by simp; omega) (by
      intro k hk
      simp only [Finset.mem_singleton] at hk
      subst k
      exact disjoint_compl_right))
  choose J cards certified using each
  let K (w : ℕ) := Finset.univ.filter (fun l : Fin n => w ∈ J l)
  let G := Finset.Ico (n+n) (n+n+C.size)
  have in_G (l : Fin n) (w : ℕ) (hw : w ∈ J l) : w ∈ G := by
    obtain ⟨lo,hi,_⟩ := certified l w hw
    exact Finset.mem_Ico.mpr ⟨lo,hi⟩
  by_cases heavy : ∃ w ∈ G, 100 < (K w).card
  · obtain ⟨w,win,many⟩ := heavy
    have facts (l : Fin n) (hl : l ∈ K w) : strict C (S l) {l} w :=
      certified l w (Finset.mem_filter.mp hl).2
    obtain ⟨l,hl,k,hk,lk⟩ := Finset.one_lt_card.mp (show 1 < (K w).card by omega)
    obtain ⟨low,high,reaches,opcode,_,_,_,a,b,pins,_,_⟩ := facts l hl
    have sides (t : Fin n) (ht : t ∈ K w) :
        wval C (S t)ᶜ {t} w = false ∧ 1 < (support C {t} w).card ∧ support C {t} w ⊆ S t ∧
        ¬ support C {t} a ⊆ support C {t} b ∧ ¬ support C {t} b ⊆ support C {t} a := by
      obtain ⟨_,_,_,_,off,rich,contained,a',b',pins',ab,ba⟩ := facts t ht
      have e : a' = a ∧ b' = b := by simpa using pins'.symm.trans pins
      rcases e with ⟨rfl,rfl⟩
      exact ⟨off,rich,contained,ab,ba⟩
    have common (p : Fin n) (yes : wval C {p} ∅ w = true) (t : Fin n) (ht : t ∈ K w) : p ∈ S t := by
      have someLine := mono C ao (show ({p} : Finset (Fin n)) ⊆ {p} by rfl)
        (Finset.empty_subset ({t} : Finset (Fin n))) w high yes
      exact (sides t ht).2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,someLine⟩)
    by_cases nonempty : ∃ p : Fin n, wval C {p} ∅ w = true
    · obtain ⟨p,yes⟩ := nonempty
      have uniquePoint (r : Fin n) (also : wval C {r} ∅ w = true) : r = p := by
        by_contra different
        exact lk ((unique r p different).unique
          ⟨common r also l hl,common p yes l hl⟩ ⟨common r also k hk,common p yes k hk⟩)
      have one (r : Fin n) : wval C {r} ∅ w = decide (r = p) := by
        by_cases same : r = p
        · subst r
          simpa using yes
        · have h := Bool.eq_false_of_ne_true (fun v => same (uniquePoint r v))
          simpa only [decide_eq_false_iff_not.mpr same] using h
      exact pencilSharing q n S C hq shape degree unique ao output accept reject
        ⟨w,a,b,low,high,reaches,opcode,pins,K w,many,⟨p,one,common p yes⟩,sides⟩
    · have none (p : Fin n) : wval C {p} ∅ w = false :=
        Bool.eq_false_of_ne_true (fun e => nonempty ⟨p,e⟩)
      exact emptySharing q n S C hq shape degree unique ao output accept reject
        ⟨w,a,b,low,high,reaches,opcode,pins,K w,many,none,sides⟩
  · have small (w : ℕ) (hw : w ∈ G) : (K w).card ≤ 100 :=
      Nat.le_of_not_gt (fun h => heavy ⟨w,hw,h⟩)
    have gsize : G.card = C.size := by simp [G]
    have asSum (l : Fin n) : (J l).card = ∑ w ∈ G, (if w ∈ J l then 1 else 0) := by
      rw [← Finset.sum_filter]
      have eq : G.filter (fun w => w ∈ J l) = J l := by
        ext w
        simp only [Finset.mem_filter]
        exact ⟨And.right,fun h => ⟨in_G l w h,h⟩⟩
      simp [eq]
    calc n*q = ∑ _ : Fin n, q := by simp
         _ ≤ ∑ l : Fin n, (J l).card := Finset.sum_le_sum (fun l _ => by
           have bound := cards l
           rw [degree l] at bound
           omega)
         _ = ∑ w ∈ G, (K w).card := by
           simp_rw [asSum]
           rw [Finset.sum_comm]
           apply Finset.sum_congr rfl
           intro w _
           rw [← Finset.sum_filter]
           simp [K]
         _ ≤ ∑ w ∈ G, 100 := Finset.sum_le_sum small
         _ = 100*C.size := by simp [gsize,Nat.mul_comm]
