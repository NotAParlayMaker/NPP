import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18049_aux

open PEqualNP.CircuitLowerBounds

def isAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | _ => false

def gv {α : Type} (z : α) (A O : α → α → α) (g : Gate) (w : List α) : α :=
  if isAnd g = true then A (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)
  else O (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)

def grun {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) : List α :=
  gs.foldl (fun w g => w ++ [gv z A O g w]) x

theorem grun_snoc {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (g : Gate) (x : List α) :
    grun z A O (gs ++ [g]) x = grun z A O gs x ++ [gv z A O g (grun z A O gs x)] := by
  simp [grun, List.foldl_append]

theorem grun_length {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) :
    (grun z A O gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [grun]
  | append_singleton gs g ih => rw [grun_snoc]; simp [ih]; omega

theorem getD_lt {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
    ∃ a b, gs[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j

theorem good_init {n : ℕ} {gs : List Gate} {g : Gate} (h : Good n (gs ++ [g])) :
    Good n gs ∧ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + gs.length ∧ b < n + gs.length) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · simpa using h gs.length (by simp)

theorem grun_input {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) (i : ℕ)
    (hi : i < x.length) : (grun z A O gs x).getD i z = x.getD i z := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => rw [grun_snoc, getD_lt _ _ _ _ (by rw [grun_length]; omega), ih]

theorem grun_gate {α : Type} (z : α) (A O : α → α → α) (n : ℕ) (gs : List Gate) (hgs : Good n gs)
    (x : List α) (hx : x.length = n) : ∀ (j : ℕ) (hj : j < gs.length),
      (grun z A O gs x).getD (n + j) z = gv z A O gs[j] (grun z A O gs x) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    obtain ⟨hg0, hop, a, b, hab, ha, hb⟩ := good_init hgs
    have hlen : (grun z A O gs x).length = n + gs.length := by rw [grun_length, hx]
    intro j hj
    have hin : ∀ (g' : Gate) (a b : ℕ), g'.inputs = [a, b] → a < n + gs.length →
        b < n + gs.length → gv z A O g' (grun z A O (gs ++ [g]) x) =
          gv z A O g' (grun z A O gs x) := by
      intro g' a b h ha hb
      unfold gv
      simp only [h, List.getD_cons_zero, List.getD_cons_succ]
      rw [grun_snoc, getD_lt _ _ _ _ (by rw [hlen]; exact ha),
        getD_lt _ _ _ _ (by rw [hlen]; exact hb)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h]
      obtain ⟨-, a', b', h1, h2, h3⟩ := hg0 j h
      rw [hin _ a' b' h1 (by omega) (by omega), grun_snoc, getD_lt _ _ _ _ (by rw [hlen]; omega)]
      exact ih hg0 j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, hin g a b hab ha hb, grun_snoc, ← hlen, getD_at]

theorem fold_congr {α : Type} (f g : List α → Gate → List α) (gs : List Gate)
    (h : ∀ q ∈ gs, ∀ w, f w q = g w q) : ∀ x, gs.foldl f x = gs.foldl g x := by
  induction gs with
  | nil => intro x; rfl
  | cons q gs ih =>
    intro x
    simp only [List.foldl_cons]
    rw [h q (by simp), ih (fun q' hq' => h q' (by simp [hq']))]

theorem wires_eq {n : ℕ} (C : Circuit) (h : Good n C.gates) (x : List Bool) :
    C.wires x = grun false (· && ·) (· || ·) C.gates x := by
  unfold Circuit.wires grun
  refine fold_congr _ _ _ (fun q hq w => ?_) x
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
  obtain ⟨hop, a, b, hab, -, -⟩ := h j hj
  rcases hop with ho | ho <;> simp [gv, isAnd, ho, hab, GateOp.eval]


def bA (p q : Bool × Bool) : Bool × Bool := (p.1 && q.1, (p.1 && q.2) || (p.2 && q.1))
def bO (p q : Bool × Bool) : Bool × Bool := (p.1 || q.1, p.2 || q.2)

theorem mem_good {n : ℕ} {gs : List Gate} (h : Good n gs) {q : Gate} (hq : q ∈ gs) :
    (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ ∃ a b, q.inputs = [a, b] := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
  obtain ⟨h1, a, b, h2, -, -⟩ := h j hj
  exact ⟨h1, a, b, h2⟩

theorem lin_eq {n : ℕ} (C : Circuit) (h : Good n C.gates) (L : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C L x = grun (false, false) bA bO C.gates
      ((x.zipIdx).map fun (b, i) => if L i then (false, b) else (b, false)) := by
  unfold PEqualNP.ReadK.linearParts grun
  refine fold_congr _ _ _ (fun q hq w => ?_) _
  obtain ⟨hop, a, b, hab⟩ := mem_good h hq
  rcases hop with ho | ho <;> simp [gv, isAnd, ho, hab, bA, bO]


theorem pathway (n : ℕ) (C : Circuit) (p q : ℕ) (ao : TopForm.IsAO2 n C)
    (hs : ReadK.lineSingle C n (fun i => decide (i = q)) p q = true) :
    Relation.ReflTransGen (fun u v => ∃ (j b : ℕ) (g : Gate), v = n + j ∧ C.gates[j]? = some g ∧
      (g.inputs = [u,b] ∨ g.inputs = [b,u]) ∧ (g.op = GateOp.or ∨
        (C.wires (List.ofFn fun i : Fin n => decide (i.val = p))).getD b false = true)) q C.output := by
  obtain ⟨a1,a2,a3⟩ := ao
  have good : Good n C.gates := by
    intro j hj
    have hm := List.getElem_mem hj
    obtain ⟨a,b,hab⟩ := List.length_eq_two.1 (a3 _ hm)
    have hr := a2 j hj
    unfold MetaComplexity.NestedCover.gateAt at hr
    rw [List.getD_eq_getElem _ _ hj, hab] at hr
    exact ⟨a1 _ hm, a,b,hab,hr a (by simp),hr b (by simp)⟩
  let x := List.ofFn fun i : Fin n => decide (i.val = p)
  let X : List (Bool × Bool) := (((List.range n).map fun i => i == p || i == q).zipIdx).map
    (fun (b,i) => if decide (i = q) then (false,b) else (b,false))
  have lx : x.length = n := by simp [x]
  have lX : X.length = n := by simp [X]
  let V := grun (false,false) bA bO C.gates X
  let W := grun false (· && ·) (· || ·) C.gates x
  have hw : C.wires x = W := wires_eq C good x
  let R := fun u v => ∃ (j b : ℕ) (g : Gate), v = n+j ∧ C.gates[j]? = some g ∧
    (g.inputs = [u,b] ∨ g.inputs = [b,u]) ∧ (g.op = GateOp.or ∨ W.getD b false = true)
  change Relation.ReflTransGen (fun u v => ∃ (j b : ℕ) (g : Gate), v = n+j ∧ C.gates[j]? = some g ∧
    (g.inputs = [u,b] ∨ g.inputs = [b,u]) ∧ (g.op = GateOp.or ∨ (C.wires x).getD b false = true)) q C.output
  rw [hw]
  change Relation.ReflTransGen R q C.output
  have inv (i : ℕ) : ((V.getD i (false,false)).1 = true → W.getD i false = true) ∧
      ((V.getD i (false,false)).2 = true → Relation.ReflTransGen R q i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases hi : i < n
      · have ev₁ : V.getD i (false,false) = X.getD i (false,false) :=
          grun_input _ _ _ _ _ _ (by omega)
        have ev₂ : W.getD i false = x.getD i false := grun_input _ _ _ _ _ _ (by omega)
        rw [ev₁,ev₂,List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]
        simp only [X,x,List.getElem_map,List.getElem_zipIdx,List.getElem_range,List.getElem_ofFn]
        by_cases hq : i = q
        · subst i
          simp [Relation.ReflTransGen.refl]
        · simp [hq]
      · let j := i - n
        have ei : i = n+j := by dsimp [j]; omega
        by_cases hj : j < C.gates.length
        · obtain ⟨hop,a,b,hab,ha,hb⟩ := good j hj
          have va := ih a (by omega)
          have vb := ih b (by omega)
          have eg : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
          have ev₁ : V.getD i (false,false) = gv (false,false) bA bO C.gates[j] V := by
            rw [ei]; exact grun_gate _ _ _ _ _ good _ lX _ hj
          have ev₂ : W.getD i false = gv false (· && ·) (· || ·) C.gates[j] W := by
            rw [ei]; exact grun_gate _ _ _ _ _ good _ lx _ hj
          have left (f : C.gates[j].op = GateOp.or ∨ W.getD b false = true) :
              R a i := ⟨j,b,C.gates[j],ei,eg,Or.inl hab,f⟩
          have right (f : C.gates[j].op = GateOp.or ∨ W.getD a false = true) :
              R b i := ⟨j,a,C.gates[j],ei,eg,Or.inr hab,f⟩
          rw [ev₁,ev₂]
          rcases hop with op | op
          · simp only [gv,isAnd,op,ite_true,hab,List.getD_cons_zero,List.getD_cons_succ,bA,
                Bool.and_eq_true,Bool.or_eq_true]
            constructor
            · rintro ⟨aa,bb⟩
              exact ⟨va.1 aa,vb.1 bb⟩
            · rintro (⟨aa,bb⟩|⟨aa,bb⟩)
              · exact (vb.2 bb).tail (right (Or.inr (va.1 aa)))
              · exact (va.2 aa).tail (left (Or.inr (vb.1 bb)))
          · simp only [gv,isAnd,op,Bool.false_eq_true,ite_false,hab,List.getD_cons_zero,
                List.getD_cons_succ,bO,Bool.or_eq_true]
            constructor
            · rintro (aa|bb)
              · exact Or.inl (va.1 aa)
              · exact Or.inr (vb.1 bb)
            · rintro (aa|bb)
              · exact (va.2 aa).tail (left (Or.inl op))
              · exact (vb.2 bb).tail (right (Or.inl op))
        · have lv : V.length = n+C.gates.length := by rw [grun_length, lX]
          rw [List.getD_eq_default V _ (by omega)]
          simp
  apply (inv C.output).2
  unfold ReadK.lineSingle at hs
  rw [lin_eq C good] at hs
  exact hs
end PEqualNP.Outside.L_meta_18049_aux

theorem PEqualNP.Outside.L_meta_18049 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x2 < (26 : ℕ) → x3 < (26 : ℕ) → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = x3)) x2 x3 = Bool.true → Relation.ReflTransGen (fun (x8 x9 : ℕ) => ∃ (x10 : ℕ) (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x9 = (26 : ℕ) + x10 ∧ x1.gates[x10]? = Option.some x12 ∧ (x12.inputs = [x8, x11] ∨ x12.inputs = [x11, x8]) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (x1.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = x2))).getD x11 Bool.false = Bool.true)) x3 x1.output := by
  intro C p q ao _ _ hs
  exact PEqualNP.Outside.L_meta_18049_aux.pathway 26 C p q ao hs
