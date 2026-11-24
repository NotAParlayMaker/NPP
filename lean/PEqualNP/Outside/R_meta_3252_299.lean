import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Compile the set trace for the bounded-order branch and use exact sparse-line certificates
-- for the remaining orders. The saturation argument follows R_meta_2794_601.
theorem PEqualNP.Outside.R_meta_3252_299
    (small : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      100 < q → q ≤ 299 → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N+N) C x = false) → N*q ≤ 100*C.size)
    (coverBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 300 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) →
      ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < N+N+s → (∀ v < N+N, F v = {{v}}) →
      (∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g,
        F (N+N+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (N+N+g) = F a ∨
        F (N+N+g) = {∅} ∨ F (N+N+g) = F a ∪ F b) →
      (∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N+l.val ∈ A) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
        (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T)) → N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x19 x21 (x12 + x20) ∧ x23 ∈ x19 x21 (x12 + x20) ∧ ¬∃ x24 < x12 + x20, ∃ x25 < x12 + x20, x19 x21 (x12 + x20) = x19 x21 x24 ∪ x19 x21 x25) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
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

  have compile {Z : Type} (m s o : ℕ) (W : ℕ → Set Z) (V : Z → List Bool)
      (inputLength : ∀ z, (V z).length = m)
      (inputEval : ∀ w < m, ∀ z, (V z).getD w false = true ↔ z ∈ W w)
      (laws : ∀ g < s, ∃ a b, max a b < m+g ∧
        W (m+g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) :
      ∃ C : Circuit, Monotone2 C ∧ C.size = s ∧ C.output = o ∧
        ∀ z w, w < m+s → ((C.wires (V z)).getD w false = true ↔ z ∈ W w) := by
    classical
    let spec (g : Fin s) (G : Gate) : Prop :=
      (G.op = .and ∨ G.op = .or) ∧ G.inputs.length ≤ 2 ∧
      (∀ j ∈ G.inputs, j < m+g.val) ∧
      ∀ (z : Z) (R : ℕ → Bool), (∀ j ∈ G.inputs, R j = true ↔ z ∈ W j) →
        (G.op.eval (G.inputs.map R) = true ↔ z ∈ W (m+g.val))
    have existence (g : Fin s) : ∃ G, spec g G := by
      obtain ⟨a,b,hlt,h⟩ := laws g.val g.isLt
      have ha : a < m+g.val := lt_of_le_of_lt (le_max_left _ _) hlt
      have hb : b < m+g.val := lt_of_le_of_lt (le_max_right _ _) hlt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h
      · refine ⟨⟨.or,[a,b]⟩,Or.inr rfl,by simp,?_,?_⟩
        · simpa only [List.mem_cons, List.not_mem_nil, or_false] using
            (fun j (e : j = a ∨ j = b) => e.elim (· ▸ ha) (· ▸ hb))
        · intro z R hr
          change (R a || (R b || false)) = true ↔ z ∈ W (m+g.val)
          rw [h]
          simp only [Bool.or_false, Bool.or_eq_true, Set.mem_union,
            hr a (by simp), hr b (by simp)]
      · refine ⟨⟨.or,[a]⟩,Or.inr rfl,by simp,by simpa using ha,?_⟩
        intro z R hr
        change (R a || false) = true ↔ z ∈ W (m+g.val)
        simpa only [Bool.or_false,h] using (hr a (by simp))
      · refine ⟨⟨.or,[]⟩,Or.inr rfl,by simp,by simp,?_⟩
        intro z R hr
        change false = true ↔ z ∈ W (m+g.val)
        simp [h]
      · refine ⟨⟨.and,[a,b]⟩,Or.inl rfl,by simp,?_,?_⟩
        · simpa only [List.mem_cons, List.not_mem_nil, or_false] using
            (fun j (e : j = a ∨ j = b) => e.elim (· ▸ ha) (· ▸ hb))
        · intro z R hr
          change (R a && (R b && true)) = true ↔ z ∈ W (m+g.val)
          rw [h]
          simp only [Bool.and_true, Bool.and_eq_true, Set.mem_inter_iff,
            hr a (by simp), hr b (by simp)]
    let select (g : Fin s) : Gate := Classical.choose (existence g)
    have selected (g : Fin s) : spec g (select g) := Classical.choose_spec (existence g)
    let C : Circuit := ⟨List.ofFn select,o⟩
    have length : C.gates.length = s := List.length_ofFn
    have gate_eq (g : Fin s) : gateAt C g.val = select g := by
      rw [gateAt_eq (show g.val < C.gates.length by rw [length]; exact g.isLt)]
      change (List.ofFn select)[g.val] = select g
      rw [List.getElem_ofFn]
    refine ⟨C,?_,length,rfl,?_⟩
    · intro G hG
      change G ∈ List.ofFn select at hG
      obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hG
      exact ⟨by simpa using (selected g).1,(selected g).2.1⟩
    · intro z w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro valid
        change val C (V z) w = true ↔ z ∈ W w
        by_cases raw : w < m
        · rw [val_input (inputLength z) raw]
          exact inputEval w raw z
        · let g : Fin s := ⟨w-m,by omega⟩
          have hw : w = m+g.val := by change w = m+(w-m); omega
          have hg : g.val < C.gates.length := by rw [length]; exact g.isLt
          rw [hw,val_gate (inputLength z) hg,gate_eq g]
          apply (selected g).2.2.2
          intro j hj
          have earlier := (selected g).2.2.1 j hj
          rw [ite_eq_left earlier]
          exact ih j (by omega) (by omega)

  have row_mono {N s : ℕ} (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool)))
      (raw : ∀ i : Fin N, W i.val = {z | z.1 i = true} ∧ W (N+i.val) = {z | z.2 i = true})
      (laws : ∀ g < s, ∃ a b, max a b < N+N+g ∧
        W (N+N+g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b])
      (x y : (Fin N → Bool) × (Fin N → Bool))
      (h₁ : ∀ i, x.1 i = true → y.1 i = true) (h₂ : ∀ i, x.2 i = true → y.2 i = true) :
      ∀ w < N+N+s, x ∈ W w → y ∈ W w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro valid h
      by_cases hraw : w < N+N
      · by_cases hp : w < N
        · let p : Fin N := ⟨w,hp⟩
          rw [(raw p).1] at h ⊢
          exact h₁ p h
        · let l : Fin N := ⟨w-N,by omega⟩
          have hw : w = N+l.val := by change w = N+(w-N); omega
          rw [hw,(raw l).2] at h ⊢
          exact h₂ l h
      · let g := w-(N+N)
        have hw : N+N+g = w := by dsimp [g]; omega
        obtain ⟨a,b,earlier,op⟩ := laws g (by dsimp [g]; omega)
        rw [hw] at earlier op
        have ia := ih a (lt_of_le_of_lt (le_max_left _ _) earlier) (by omega)
        have ib := ih b (lt_of_le_of_lt (le_max_right _ _) earlier) (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at op
        rcases op with e | e | e | e
        · rw [e] at h ⊢
          exact h.elim (fun h => Or.inl (ia h)) (fun h => Or.inr (ib h))
        · rw [e] at h ⊢
          exact ia h
        · rw [e] at h
          exact h.elim
        · rw [e] at h ⊢
          exact ⟨ia h.1,ib h.2⟩

  have incidence_circuit (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (ho : o < N+N+s)
      (raw : ∀ i : Fin N, W i.val = {z | z.1 i = true} ∧ W (N+i.val) = {z | z.2 i = true})
      (laws : ∀ g < s, ∃ a b, max a b < N+N+g ∧
        W (N+N+g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b])
      (pos : ∀ p l : Fin N, I p l → (fun i => decide (i = p),fun i => decide (i = l)) ∈ W o)
      (neg : ∀ y : Fin N → Bool, Fintype.card {l : Fin N // y l = true} ≤ q →
        (fun p => decide (¬ ∃ l, I p l ∧ y l = true),y) ∉ W o) :
      ∃ C : Circuit, Monotone2 C ∧ C.size = s ∧
        (∀ p l : Fin N, I p l → circuitFun (N+N) C
          (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) ∧
        (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
          (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          circuitFun (N+N) C x = false) := by
    let V (z : (Fin N → Bool) × (Fin N → Bool)) := List.ofFn (Fin.append z.1 z.2)
    have hraw : ∀ w < N+N, ∀ z, (V z).getD w false = true ↔ z ∈ W w := by
      suffices ∀ i : Fin (N+N), ∀ z, (V z).getD i.val false = true ↔ z ∈ W i.val by
        exact fun w h z => this ⟨w,h⟩ z
      intro i z
      have get : (V z).getD i.val false = Fin.append z.1 z.2 i := by
        have hi : i.val < (V z).length := by simp [V]
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_ofFn _
      rw [get]
      induction i using Fin.addCases with
      | left p =>
        change Fin.append z.1 z.2 (Fin.castAdd N p) = true ↔ z ∈ W p.val
        rw [Fin.append_left,(raw p).1]
        rfl
      | right l =>
        change Fin.append z.1 z.2 (Fin.natAdd N l) = true ↔ z ∈ W (N+l.val)
        rw [Fin.append_right,(raw l).2]
        rfl
    obtain ⟨C,mono,size,out,simulates⟩ := compile (N+N) s o W V (fun _ => by simp [V]) hraw laws
    let split (x : Fin (N+N) → Bool) :=
      (fun p : Fin N => x (Fin.castAdd N p),fun l : Fin N => x (Fin.natAdd N l))
    have root_eval (x : Fin (N+N) → Bool) : circuitFun (N+N) C x = true ↔ split x ∈ W o := by
      have join : Fin.append (split x).1 (split x).2 = x := by
        funext i
        induction i using Fin.addCases with
        | left p => simp only [split, Fin.append_left]
        | right l => simp only [split, Fin.append_right]
      have sim := simulates (split x) o ho
      change (C.wires (List.ofFn (Fin.append (split x).1 (split x).2))).getD o false = true ↔ _ at sim
      rw [join] at sim
      change (C.wires (List.ofFn x)).getD C.output false = true ↔ _
      rw [out]
      exact sim
    have sep (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro eq
      have same := congrArg Fin.val eq
      change p.val = N+l.val at same
      have := p.isLt
      omega
    refine ⟨C,mono,size,?_,?_⟩
    · intro p l h
      apply (root_eval _).mpr
      have sides : split (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) =
          (fun i => decide (i = p), fun i => decide (i = l)) := by
        apply Prod.ext <;> funext i
        · have ep : Fin.castAdd N i = Fin.castAdd N p ↔ i = p :=
            ⟨fun e => Fin.ext (congrArg (fun a : Fin (N+N) => a.val) e),congrArg (Fin.castAdd N)⟩
          change decide (Fin.castAdd N i = Fin.castAdd N p ∨ Fin.castAdd N i = Fin.natAdd N l) =
            decide (i = p)
          simp only [ep,sep i l,or_false]
        · have el : Fin.natAdd N i = Fin.natAdd N l ↔ i = l :=
            ⟨fun e => Fin.ext (Nat.add_left_cancel (congrArg Fin.val e)),congrArg (Fin.natAdd N)⟩
          change decide (Fin.natAdd N i = Fin.castAdd N p ∨ Fin.natAdd N i = Fin.natAdd N l) =
            decide (i = l)
          simp only [el,Ne.symm (sep p i),false_or]
      rw [sides]
      exact pos p l h
    · intro x hx hno
      cases got : circuitFun (N+N) C x with
      | false => rfl
      | true =>
        exfalso
        let y := (split x).2
        let z (p : Fin N) := decide (¬ ∃ l, I p l ∧ y l = true)
        have dom (p : Fin N) (hp : (split x).1 p = true) : z p = true := by
          apply decide_eq_true
          rintro ⟨l,hl,hy⟩
          exact hno ⟨p,l,hl,hp,hy⟩
        exact neg y hx (row_mono W raw laws (split x) (z,y) dom (fun _ h => h)
          o ho ((root_eval x).mp got))

  have certificates (Z : Type) (m s : ℕ) (X : ℕ → Set Z)
      (ops : ∀ g < s, ∃ a < m+g, ∃ b < m+g,
          X (m+g) = X a ∪ X b ∨ X (m+g) = X a ∨ X (m+g) = ∅ ∨ X (m+g) = X a ∩ X b) :
      ∃ F : ℕ → Set (Finset ℕ), (∀ v < m, F v = {{v}}) ∧
        (∀ g < s, ∃ a < m+g, ∃ b < m+g,
          F (m+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m+g) = F a ∨
          F (m+g) = {∅} ∨ F (m+g) = F a ∪ F b) ∧
        ∀ w < m+s, (∀ A ∈ F w, ∀ v ∈ A, v < m) ∧
          ∀ z, z ∉ X w ↔ ∃ A ∈ F w, ∀ v ∈ A, z ∉ X v := by
    classical
    let valid (Y : Set Z) (K : Set (Finset ℕ)) : Prop :=
      (∀ A ∈ K, ∀ v ∈ A, v < m) ∧ ∀ z, z ∉ Y ↔ ∃ A ∈ K, ∀ v ∈ A, z ∉ X v
    let allowable (K U V : Set (Finset ℕ)) : Prop :=
      K = Set.image2 (· ∪ ·) U V ∨ K = U ∨ K = {∅} ∨ K = U ∪ V
    have build (k : ℕ) (limit : k ≤ s) :
        ∃ F : ℕ → Set (Finset ℕ), (∀ v < m, F v = {{v}}) ∧
          (∀ g < k, ∃ a < m+g, ∃ b < m+g, allowable (F (m+g)) (F a) (F b)) ∧
          ∀ w < m+k, valid (X w) (F w) := by
      induction k with
      | zero =>
        refine ⟨fun w => {{w}},fun _ _ => rfl,by simp,?_⟩
        intro w hw
        have h : w < m := by omega
        refine ⟨?_,?_⟩
        · intro A hA v hv
          have e : A = {w} := hA
          subst A
          exact (Finset.mem_singleton.mp hv).symm ▸ h
        · intro z
          constructor
          · intro no
            exact ⟨{w},rfl,fun v hv => (Finset.mem_singleton.mp hv).symm ▸ no⟩
          · rintro ⟨A,hA,no⟩
            have e : A = {w} := hA
            exact no w (by simp [e])
      | succ k ih =>
        obtain ⟨F,leaves,gates,old⟩ := ih (by omega)
        obtain ⟨a,ha,b,hb,op⟩ := ops k (by omega)
        have va := old a ha
        have vb := old b hb
        have next : ∃ K, allowable K (F a) (F b) ∧ valid (X (m+k)) K := by
          rcases op with e | e | e | e <;> rw [e]
          · refine ⟨Set.image2 (· ∪ ·) (F a) (F b),Or.inl rfl,?_,?_⟩
            · rintro A ⟨B,hB,C,hC,rfl⟩ v hv
              exact (Finset.mem_union.mp hv).elim (va.1 B hB v) (vb.1 C hC v)
            · intro z
              constructor
              · intro no
                obtain ⟨B,hB,nb⟩ := (va.2 z).mp (fun h => no (Or.inl h))
                obtain ⟨C,hC,nc⟩ := (vb.2 z).mp (fun h => no (Or.inr h))
                exact ⟨B ∪ C,⟨B,hB,C,hC,rfl⟩,fun v hv =>
                  (Finset.mem_union.mp hv).elim (nb v) (nc v)⟩
              · rintro ⟨A,⟨B,hB,C,hC,rfl⟩,no⟩ part
                exact part.elim
                  ((va.2 z).mpr ⟨B,hB,fun v hv => no v (Finset.mem_union.mpr (Or.inl hv))⟩)
                  ((vb.2 z).mpr ⟨C,hC,fun v hv => no v (Finset.mem_union.mpr (Or.inr hv))⟩)
          · exact ⟨F a,Or.inr (Or.inl rfl),va⟩
          · refine ⟨{∅},Or.inr (Or.inr (Or.inl rfl)),?_,?_⟩
            · intro A hA v hv
              have e : A = ∅ := hA
              simpa [e] using hv
            · intro z
              exact ⟨fun _ => ⟨∅,rfl,by simp⟩,fun _ h => h.elim⟩
          · refine ⟨F a ∪ F b,Or.inr (Or.inr (Or.inr rfl)),?_,?_⟩
            · intro A hA
              exact hA.elim (va.1 A) (vb.1 A)
            · intro z
              constructor
              · intro no
                by_cases ma : z ∈ X a
                · obtain ⟨A,hA,hz⟩ := (vb.2 z).mp (fun h => no ⟨ma,h⟩)
                  exact ⟨A,Or.inr hA,hz⟩
                · obtain ⟨A,hA,hz⟩ := (va.2 z).mp ma
                  exact ⟨A,Or.inl hA,hz⟩
              · rintro ⟨A,hA,hz⟩ hz'
                exact hA.elim
                  (fun h => (va.2 z).mpr ⟨A,h,hz⟩ hz'.1)
                  (fun h => (vb.2 z).mpr ⟨A,h,hz⟩ hz'.2)
        obtain ⟨K,how,correct⟩ := next
        let G (w : ℕ) := if w = m+k then K else F w
        have same (w : ℕ) (hw : w < m+k) : G w = F w := by
          simp [G, Nat.ne_of_lt hw]
        have added : G (m+k) = K := by simp [G]
        refine ⟨G,?_,?_,?_⟩
        · intro v hv
          rw [same v (by omega)]
          exact leaves v hv
        · intro g hg
          by_cases prev : g < k
          · obtain ⟨a',ha',b',hb',law⟩ := gates g prev
            refine ⟨a',ha',b',hb',?_⟩
            rw [same (m+g) (by omega),same a' (by omega),same b' (by omega)]
            exact law
          · have eq : g = k := by omega
            subst g
            refine ⟨a,ha,b,hb,?_⟩
            rw [added,same a ha,same b hb]
            exact how
        · intro w hw
          by_cases prev : w < m+k
          · rw [same w prev]
            exact old w prev
          · have eq : w = m+k := by omega
            subst w
            rw [added]
            exact correct
    exact build s le_rfl

  have freshPoint (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (degrees : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (unique : ∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l)
      (T : Finset (Fin N)) (size : T.card ≤ q) (l : Fin N) (outside : l ∉ T) :
      ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k := by
    classical
    by_contra impossible
    have hit (p : {p : Fin N // I p l}) : ∃ k ∈ T, I p.val k := by
      by_contra! misses
      exact impossible ⟨p.val,p.property,misses⟩
    let f (p : {p : Fin N // I p l}) : {k : Fin N // k ∈ T} :=
      ⟨(hit p).choose,(hit p).choose_spec.1⟩
    have incident (p : {p : Fin N // I p l}) : I p.val (f p).val :=
      (hit p).choose_spec.2
    have inj : Function.Injective f := by
      intro a b same
      apply Subtype.ext
      by_contra different
      obtain ⟨k,_,common⟩ := unique a.val b.val different
      have ea : l = k := common l ⟨a.property,b.property⟩
      have ib : I b.val (f a).val := by rw [same]; exact incident b
      have eb : (f a).val = k := common _ ⟨incident a,ib⟩
      apply outside
      rw [ea.trans eb.symm]
      exact (f a).property
    have count := Fintype.card_le_of_injective f inj
    rw [degrees l, Fintype.card_coe] at count
    omega

  intro q N I inst hq hN degrees unique s o W
  dsimp only
  intro ho inputs steps pos neg _
  by_cases bounded : q ≤ 299
  · obtain ⟨C,mono,size,posC,negC⟩ := incidence_circuit q N I s o W ho inputs steps pos neg
    simpa only [size] using small q N I C hq bounded hN degrees unique mono posC negC
  have wide : 300 ≤ q := by omega
  obtain ⟨F, leaves, gates, spec⟩ := certificates _ (N+N) s W (by
    intro g hg
    obtain ⟨a,b,earlier,op⟩ := steps g hg
    refine ⟨a,lt_of_le_of_lt (le_max_left _ _) earlier,
      b,lt_of_le_of_lt (le_max_right _ _) earlier,?_⟩
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using op)
  have cover (A : Finset ℕ) (hA : A ∈ F o) (p l : Fin N) (h : I p l) : p.val ∈ A ∨ N+l.val ∈ A := by
    by_contra! miss
    apply ((spec o ho).2 _).mpr ⟨A,hA,?_⟩ (pos p l h)
    intro v hv
    have hvb := (spec o ho).1 A hA v hv
    by_cases small : v < N
    · let k : Fin N := ⟨v,small⟩
      rw [(inputs k).1]
      change ¬ decide (k = p) = true
      exact fun e => miss.1 ((congrArg Fin.val (of_decide_eq_true e)) ▸ hv)
    · let k : Fin N := ⟨v-N,by omega⟩
      have e : v = N + k.val := by dsimp [k]; omega
      rw [e,(inputs k).2]
      change ¬ decide (k = l) = true
      intro eq
      have : v = N+l.val := e.trans (congrArg (fun a : Fin N => N+a.val) (of_decide_eq_true eq))
      exact miss.2 (this ▸ hv)
  have saturated : ∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
      (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T) := by
    intro T ht
    let y := fun l : Fin N => decide (l ∈ T)
    let x := fun p : Fin N => decide (¬ ∃ l, I p l ∧ y l = true)
    have cy : Fintype.card {l : Fin N // y l = true} ≤ q := by
      simpa [Fintype.card_subtype, y] using ht
    obtain ⟨A,hA,zero⟩ := ((spec o ho).2 (x,y)).mp (neg y cy)
    have pl (p : Fin N) (h : p.val ∈ A) : ∃ l ∈ T, I p l := by
      have hh := zero p.val h
      rw [(inputs p).1] at hh
      change ¬ x p = true at hh
      simpa [x,y,and_comm] using hh
    have ln (l : Fin N) (h : N+l.val ∈ A) : l ∉ T := by
      have hh := zero _ h
      rw [(inputs l).2] at hh
      exact fun m => hh (show y l = true from decide_eq_true m)
    refine ⟨A,hA,fun p => ⟨⟨pl p,?_⟩,⟨ln p,?_⟩⟩⟩
    · rintro ⟨l,hl,inc⟩
      exact (cover A hA p l inc).resolve_right (fun bad => ln l bad hl)
    · intro hp
      obtain ⟨a, ha, avoid⟩ := freshPoint q N I degrees unique T ht p hp
      apply (cover A hA a p ha).resolve_left
      intro bad
      obtain ⟨l,hl,inc⟩ := pl a bad
      exact avoid l hl inc
  exact coverBound q N I wide hN degrees unique s o F ho leaves gates cover saturated
