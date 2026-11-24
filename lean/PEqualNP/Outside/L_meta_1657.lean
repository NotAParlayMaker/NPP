import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1657

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

end S90

def V {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  Circuit.eval ⟨gs,w⟩ (List.ofFn x)

def A (gs : List Gate) (k : ℕ) : Gate := gateAt ⟨gs,0⟩ k

def Z (gs : List Gate) (j : ℕ) : List Gate := gs.set j ⟨GateOp.or,[]⟩

lemma A_get (gs : List Gate) (k : Fin gs.length) : A gs k = gs.get k := by
  exact S90.gateAt_eq k.isLt

lemma V_input {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    V gs w x = x ⟨w,hw⟩ := by
  change S90.val ⟨gs,0⟩ (List.ofFn x) w = _
  rw [S90.val_input (n := n) (by simp) hw]
  simp [List.getD_eq_getElem?_getD,hw]

lemma V_far {n : ℕ} (gs : List Gate) (w : ℕ) (hw : n+gs.length ≤ w) (x : Fin n → Bool) :
    V gs w x = false := S90.val_ge (C := ⟨gs,w⟩) (by simp) hw

lemma V_gate {n : ℕ} (gs : List Gate)
    (hRB : ∀ k, k < gs.length → ∀ w ∈ (A gs k).inputs, w < n+k)
    (k : ℕ) (hk : k < gs.length) (x : Fin n → Bool) :
    V gs (n+k) x = (A gs k).op.eval ((A gs k).inputs.map fun w => V gs w x) := by
  change S90.val ⟨gs,0⟩ (List.ofFn x) (n+k) = _
  rw [S90.val_gate (n := n) (by simp) hk]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact if_pos (hRB k hk w hw)

lemma Z_length (gs : List Gate) (j : ℕ) : (Z gs j).length = gs.length := by simp [Z]

lemma A_Z_same (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    A (Z gs j) j = ⟨GateOp.or,[]⟩ := by
  rw [A, S90.gateAt_eq (by simpa [Z] using hj)]
  simp [Z]

lemma A_Z_other (gs : List Gate) (j k : ℕ) (hk : k < gs.length) (hkj : k ≠ j) :
    A (Z gs j) k = A gs k := by
  rw [A, S90.gateAt_eq (by simpa [Z] using hk), A, S90.gateAt_eq hk]
  simp [Z,hkj,Ne.symm hkj]

lemma Z_back {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hRB : ∀ k, k < gs.length → ∀ w ∈ (A gs k).inputs, w < n+k) :
    ∀ k, k < (Z gs j).length → ∀ w ∈ (A (Z gs j) k).inputs, w < n+k := by
  intro k hk w hw
  rw [Z_length] at hk
  by_cases hkj : k = j
  · subst k
    rw [A_Z_same gs j hj] at hw
    simp at hw
  · rw [A_Z_other gs j k hk hkj] at hw
    exact hRB k hk w hw

lemma Z_zero {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hRB : ∀ k, k < gs.length → ∀ w ∈ (A gs k).inputs, w < n+k) (x : Fin n → Bool) :
    V (Z gs j) (n+j) x = false := by
  rw [V_gate (Z gs j) (Z_back gs j hj hRB) j (by simpa [Z] using hj), A_Z_same gs j hj]
  rfl

lemma Z_compare {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hRB : ∀ k, k < gs.length → ∀ w ∈ (A gs k).inputs, w < n+k)
    (hAO : ∀ k, k < gs.length → k ≠ j → (A gs k).op = GateOp.and ∨ (A gs k).op = GateOp.or)
    (x : Fin n → Bool) : ∀ w,
      (V (Z gs j) w x = true → V gs w x = true) ∧
      (V gs (n+j) x = false → V (Z gs j) w x = V gs w x) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · rw [V_input _ w hw, V_input _ w hw]
      exact ⟨id,fun _ => rfl⟩
    by_cases hf : n+gs.length ≤ w
    · rw [V_far gs w hf, V_far (Z gs j) w (by simpa [Z] using hf)]
      exact ⟨id,fun _ => rfl⟩
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < gs.length := by omega
    by_cases hkj : k = j
    · subst k
      rw [Z_zero gs j hj hRB]
      exact ⟨by simp,fun h => h.symm⟩
    rw [V_gate gs hRB k hk, V_gate (Z gs j) (Z_back gs j hj hRB) k
      (by simpa [Z] using hk), A_Z_other gs j k hk hkj]
    constructor
    · apply S90.opMono_imp _ (hAO k hk hkj)
      intro u hu
      exact (ih u (hRB k hk u hu)).1
    · intro hzero
      apply S90.opMono_eq _ (hAO k hk hkj)
      intro u hu
      exact (ih u (hRB k hk u hu)).2 hzero

lemma mono_before {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hRB : ∀ k, k < gs.length → ∀ w ∈ (A gs k).inputs, w < n+k)
    (hAO : ∀ k, k < gs.length → k ≠ j → (A gs k).op = GateOp.and ∨ (A gs k).op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, w < n+j → V gs w x = true → V gs w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [V_input gs w hwn, V_input gs w hwn]
      exact hxy _
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < gs.length := by omega
    rw [V_gate gs hRB k hk, V_gate gs hRB k hk]
    apply S90.opMono_imp _ (hAO k hk (by omega))
    intro u hu
    have hul := hRB k hk u hu
    exact ih u hul (by omega)

/-- If every reader of the changed wire was already false, only that wire can differ. -/
lemma Z_no_live_reader {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hRB : ∀ k, k < gs.length → ∀ w ∈ (A gs k).inputs, w < n+k)
    (hAO : ∀ k, k < gs.length → k ≠ j → (A gs k).op = GateOp.and ∨ (A gs k).op = GateOp.or)
    (x : Fin n → Bool)
    (hr : ∀ k, k < gs.length → n+j ∈ (A gs k).inputs → V gs (n+k) x = false) :
    ∀ w, w ≠ n+j → V (Z gs j) w x = V gs w x := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne
    by_cases hw : w < n
    · rw [V_input _ w hw, V_input _ w hw]
    by_cases hf : n+gs.length ≤ w
    · rw [V_far gs w hf, V_far (Z gs j) w (by simpa [Z] using hf)]
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < gs.length := by omega
    have hkj : k ≠ j := by omega
    by_cases hread : n+j ∈ (A gs k).inputs
    · have hfalse := hr k hk hread
      have hlo := (Z_compare gs j hj hRB hAO x (n+k)).1
      rw [hfalse]
      cases he : V (Z gs j) (n+k) x
      · rfl
      · have := hlo he
        rw [hfalse] at this
        contradiction
    · rw [V_gate gs hRB k hk, V_gate (Z gs j) (Z_back gs j hj hRB) k
        (by simpa [Z] using hk), A_Z_other gs j k hk hkj]
      apply S90.opMono_eq _ (hAO k hk hkj)
      intro u hu
      apply ih u (hRB k hk u hu)
      intro he
      exact hread (he ▸ hu)

theorem main1657 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := by
  classical
  intro q N L va vb vc sa sb sc hq _hN hcard _hmeet _hjoin _hnoncol
    _hvbsa _hvcsa _hvcsb _hvasb _hvasc _hvbsc gs o j h hOps hback hnot huniq
    hhj hin houtputs hreaders ev ev' hev hev' hhsingle _hreadGeom
  have he : ev = fun w x => V gs w x := by
    funext w x
    exact hev w x
  have he' : ev' = fun w x => V (Z gs j) w x := by
    funext w x
    exact hev' w x
  simp only [he,he'] at hhsingle ⊢
  have hRB : ∀ k, k < gs.length → ∀ w ∈ (A gs k).inputs, w < N+k := by
    intro k hk w hw
    have hg := A_get gs ⟨k,hk⟩
    change A gs k = _ at hg
    rw [hg] at hw
    exact hback ⟨k,hk⟩ w hw
  have hAO : ∀ k, k < gs.length → k ≠ j →
      (A gs k).op = GateOp.and ∨ (A gs k).op = GateOp.or := by
    intro k hk hkj
    have hg := A_get gs ⟨k,hk⟩
    change A gs k = _ at hg
    have hgmem : A gs k ∈ gs := S90.gateAt_mem (C := ⟨gs,0⟩) hk
    rcases (hOps _ hgmem).1 with ho | ho | ho
    · exact Or.inl ho
    · exact Or.inr ho
    · rw [hg] at ho
      have heq := congrArg Fin.val (huniq ⟨k,hk⟩ ho)
      exact (hkj heq).elim
  obtain ⟨r,hin⟩ := hin
  have hjval : ∀ x : Fin N → Bool, V gs (N+j) x = !(V gs (N+h) x) := by
    intro x
    rw [V_gate gs hRB j j.isLt, A_get gs j, hnot, hin]
    rfl
  have hzero : ∀ x : Fin N → Bool, V gs (N+h) x = true → V gs (N+j) x = false := by
    intro x hx
    rw [hjval x,hx]
    rfl
  have hcompare := Z_compare gs j j.isLt hRB hAO
  have hnoout : ∀ t, o t ≠ N+j := by
    intro t heq
    have hhva : V gs (N+h) (fun v => decide (v=va)) = true :=
      (hhsingle va).2 (Or.inl rfl)
    have hhAll : V gs (N+h) (fun _ : Fin N => true) = true := by
      apply mono_before gs j j.isLt hRB hAO (fun v => decide (v=va)) (fun _ : Fin N => true)
        (by simp) (N+h) (by exact Nat.add_lt_add_left hhj N) hhva
    have ho := houtputs t (fun _ : Fin N => true)
    change V gs (o t) (fun _ : Fin N => true) = _ at ho
    rw [heq,hzero _ hhAll] at ho
    have hn : (L t).Nonempty := Finset.card_pos.mp (by rw [hcard t]; omega)
    have ht : decide (∃ v ∈ L t, (fun _ : Fin N => true) v = true) = true := by
      rw [decide_eq_true_eq]
      obtain ⟨v,hv⟩ := hn
      exact ⟨v,hv,rfl⟩
    rw [ht] at ho
    contradiction
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro w x
    exact (hcompare x w).1
  · intro w x hx
    exact (hcompare x w).2 (hzero x hx)
  · intro i x hiread
    have hji : (j : ℕ) < i := by
      have hh := hback i (N+j) hiread
      omega
    have hip : (A gs i).op = GateOp.and := by
      rw [A_get gs i]
      exact hreaders i hiread
    have hiread' : N+j ∈ (A gs i).inputs := by rw [A_get gs i]; exact hiread
    rw [V_gate (Z gs j) (Z_back gs j j.isLt hRB) i (by simpa [Z] using i.isLt),
      A_Z_other gs j i i.isLt (by omega),hip]
    simp only [GateOp.eval,List.all_map,List.all_eq_false,Function.comp_apply,id_eq]
    exact ⟨N+j,hiread',by rw [Z_zero gs j j.isLt hRB x]; simp⟩
  · intro t P hPt hfalse
    by_contra hn
    have hr : ∀ k, k < gs.length → N+j ∈ (A gs k).inputs →
        V gs (N+k) (fun v => decide (v=P)) = false := by
      intro k hk hread
      have hg := A_get gs ⟨k,hk⟩
      change A gs k = _ at hg
      have hread' : N+j ∈ (gs.get ⟨k,hk⟩).inputs := by rw [← hg]; exact hread
      cases heval : V gs (N+k) (fun v => decide (v=P))
      · rfl
      · exact (hn ⟨⟨k,hk⟩,hread',heval⟩).elim
    have heq := Z_no_live_reader gs j j.isLt hRB hAO (fun v => decide (v=P)) hr (o t) (hnoout t)
    have htrue : V gs (o t) (fun v => decide (v=P)) = true := by
      have ho := houtputs t (fun v => decide (v=P))
      change V gs (o t) _ = _ at ho
      rw [ho]
      simp only [decide_eq_true_eq]
      exact ⟨P,hPt,by simp⟩
    rw [hfalse,htrue] at heq
    contradiction
  · intro t v hv hvt
    have hv' : v=va ∨ v=vb ∨ v=vc := by simpa using hv
    have hhtrue := (hhsingle v).2 hv'
    rw [(hcompare (fun u => decide (u=v)) (o t)).2 (hzero _ hhtrue)]
    have ho := houtputs t (fun u => decide (u=v))
    change V gs (o t) _ = _ at ho
    rw [ho]
    simp only [decide_eq_true_eq]
    exact ⟨v,hvt,by simp⟩

end PEqualNP.Outside.L_meta_1657

theorem PEqualNP.Outside.L_meta_1657 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := PEqualNP.Outside.L_meta_1657.main1657
