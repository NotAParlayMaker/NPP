import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4273

/-- A gate is *special* when it reads wire `0` or wire `9`. -/
def special (g : Gate) : Prop := 0 ∈ g.inputs ∨ 9 ∈ g.inputs

theorem special_iff (g : Gate) :
    ([0, 9].any g.inputs.contains) = true ↔ special g := by
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    List.contains_iff_mem, special]

theorem not_special_iff (g : Gate) :
    ([0, 9].any g.inputs.contains) = false ↔ ¬ special g := by
  constructor
  · intro hf hs
    have ht : ([0, 9].any g.inputs.contains) = true := (special_iff g).mpr hs
    rw [hf] at ht
    exact Bool.noConfusion ht
  · intro hns
    cases h : ([0, 9].any g.inputs.contains)
    · rfl
    · exact (hns ((special_iff g).mp h)).elim

/-- The cone set `S`, as an inductive closure: it contains the output wire and
every non-special gate wire, and it is closed under taking inputs (other than
the two special wires `0` and `9`) of gates already in the set. -/
inductive InS (C : Circuit) : ℕ → Prop where
  | out : InS C C.output
  | nonspec {k : ℕ} {g : Gate} (hk : C.gates[k]? = some g)
      (hg : ([0, 9].any g.inputs.contains) = false) : InS C (10 + k)
  | step {k : ℕ} {g : Gate} {w : ℕ} (hk : C.gates[k]? = some g)
      (hg : InS C (10 + k)) (hw : w ∈ g.inputs) (h0 : w ≠ 0) (h9 : w ≠ 9) :
      InS C w

/-- The value of wire `i` of `C` on the restricted input `x` (length `10`)
is the `i`-th entry of the input whenever `i < 10`: the fold only appends. -/
theorem wires_getD_of_lt (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  induction C.gates generalizing x with
  | nil => rfl
  | cons g gs ih =>
      have hlen : i < (x ++ [g.op.eval
          (List.map (fun i => x.getD i false) g.inputs)]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      simp only [List.foldl_cons]
      rw [ih _ hlen, List.getD_append _ _ _ _ hi]

/-- From a decomposition `C.gates = p ++ g :: t`, the gate at position
`p.length` is `g`. -/
theorem getElem?_of_append {C : Circuit} {p : List Gate} {g : Gate} {t : List Gate}
    (h : C.gates = p ++ g :: t) : C.gates[p.length]? = some g := by
  rw [h]
  rw [List.getElem?_append_right (by simp)]
  simp

/-! ## The restriction construction

Substituting wire `0 ↦ false` and wire `9 ↦ true` into `C` and simplifying
gives a circuit on `8` inputs for the restricted function.  Each old wire gets
a *status*: a constant, or the new wire that carries its value.  A gate whose
status is a fresh wire contributes one gate to the new circuit; constant and
pass-through gates contribute none. -/

/-- The status of an old wire after restriction: a constant value, or the
index of the new wire carrying the same value. -/
inductive Status where
  | const (b : Bool) : Status
  | wire (k : ℕ) : Status
deriving DecidableEq, Inhabited

/-- The value a status stands for, read off a list of new wire values. -/
def sval : Status → List Bool → Bool
  | .const b, _ => b
  | .wire k, ws => ws.getD k false

/-- The status of wire `i` given the statuses `gs` of the gates processed so
far (gate `j` has status `gs[j]`, and sits at wire `10 + j`). -/
def wstat (gs : List Status) (i : ℕ) : Status :=
  if i = 0 then .const false
  else if i = 9 then .const true
  else if i < 10 then .wire (i - 1)
  else (gs[i - 10]?).getD (.const false)

/-- The wire index carried by a status, if any. -/
def wireOf : Status → Option ℕ
  | .wire k => some k
  | .const _ => none

/-- One gate after restriction: its status, and the new gate it contributes
(if any).  `ng` is the number of new gates so far, so a fresh gate sits at
new wire `8 + ng`. -/
def combine (op : GateOp) (ng : ℕ) (ss : List Status) : Status × Option Gate :=
  match op with
  | .and =>
      if ss.any (· = .const false) then (.const false, none)
      else match ss.filterMap wireOf with
        | [] => (.const true, none)
        | [k] => (.wire k, none)
        | ks => (.wire (8 + ng), some ⟨.and, ks⟩)
  | .or =>
      if ss.any (· = .const true) then (.const true, none)
      else match ss.filterMap wireOf with
        | [] => (.const false, none)
        | [k] => (.wire k, none)
        | ks => (.wire (8 + ng), some ⟨.or, ks⟩)
  | .not =>
      match ss with
      | [] => (.const true, none)
      | .const b :: _ => (.const (!b), none)
      | .wire k :: _ => (.wire (8 + ng), some ⟨.not, [k]⟩)
  | _ => (.const false, none)

/-- The restriction step for one gate of `C`. -/
def gstep (gs : List Status) (ng : ℕ) (g : Gate) : Status × Option Gate :=
  combine g.op ng (g.inputs.map (wstat gs))

/-- The restriction of a gate list: the statuses of its gates and the new
gates produced, in order.  `added`/`ngn` are the new gates so far and their
count. -/
def buildFrom (gs : List Status) (added : List Gate) (ngn : ℕ) :
    List Gate → List Status × List Gate
  | [] => (gs, added)
  | g :: rest =>
      let (s, og) := gstep gs ngn g
      buildFrom (gs ++ [s]) (added ++ og.toList) (ngn + og.toList.length) rest

/-- The full restriction of `C`: gate statuses and the new gate list. -/
def build (C : Circuit) : List Status × List Gate := buildFrom [] [] 0 C.gates

/-- The status of wire `i` of `C` after restriction. -/
def statusOf (C : Circuit) (i : ℕ) : Status := wstat (build C).1 i

theorem buildFrom_nil (gs : List Status) (added : List Gate) (ngn : ℕ) :
    buildFrom gs added ngn [] = (gs, added) := rfl

theorem buildFrom_cons (gs : List Status) (added : List Gate) (ngn : ℕ)
    (g : Gate) (rest : List Gate) :
    buildFrom gs added ngn (g :: rest) =
      buildFrom (gs ++ [(gstep gs ngn g).1])
        (added ++ (gstep gs ngn g).2.toList)
        (ngn + (gstep gs ngn g).2.toList.length) rest := rfl

/-- `buildFrom` only appends to the status list and the gate list, and it
appends exactly one status per gate. -/
theorem buildFrom_extends (gs : List Status) (added : List Gate) (ngn : ℕ)
    (L : List Gate) :
    ∃ (Δs : List Status) (Δg : List Gate),
      buildFrom gs added ngn L = (gs ++ Δs, added ++ Δg) ∧ Δs.length = L.length := by
  induction L generalizing gs added ngn with
  | nil => exact ⟨[], [], by simp [buildFrom]⟩
  | cons g rest ih =>
      obtain ⟨Δs, Δg, h, hlen⟩ := ih (gs := gs ++ [(gstep gs ngn g).1])
        (added := added ++ (gstep gs ngn g).2.toList)
        (ngn := ngn + (gstep gs ngn g).2.toList.length)
      refine ⟨(gstep gs ngn g).1 :: Δs, (gstep gs ngn g).2.toList ++ Δg, ?_, by simp [hlen]⟩
      rw [buildFrom_cons, h]
      simp [List.append_assoc]

theorem buildFrom_fst_length (gs : List Status) (added : List Gate) (ngn : ℕ)
    (L : List Gate) : (buildFrom gs added ngn L).1.length = gs.length + L.length := by
  obtain ⟨Δs, Δg, h, hlen⟩ := buildFrom_extends gs added ngn L
  rw [h]
  simp [hlen]

/-- `buildFrom` over an append splits at the append. -/
theorem buildFrom_append (gs : List Status) (added : List Gate) (ngn : ℕ)
    (L₁ L₂ : List Gate) : buildFrom gs added ngn (L₁ ++ L₂) =
      buildFrom (buildFrom gs added ngn L₁).1 (buildFrom gs added ngn L₁).2
        ((buildFrom gs added ngn L₁).2.length - added.length + ngn) L₂ := by
  induction L₁ generalizing gs added ngn with
  | nil => simp [buildFrom]
  | cons g rest ih =>
      obtain ⟨Δs, Δg, hΔ, -⟩ := buildFrom_extends (gs ++ [(gstep gs ngn g).1])
        (added ++ (gstep gs ngn g).2.toList) (ngn + (gstep gs ngn g).2.toList.length) rest
      have h1 : (buildFrom (gs ++ [(gstep gs ngn g).1])
          (added ++ (gstep gs ngn g).2.toList)
          (ngn + (gstep gs ngn g).2.toList.length) rest).1
          = (gs ++ [(gstep gs ngn g).1]) ++ Δs := congrArg Prod.fst hΔ
      have h2 : (buildFrom (gs ++ [(gstep gs ngn g).1])
          (added ++ (gstep gs ngn g).2.toList)
          (ngn + (gstep gs ngn g).2.toList.length) rest).2
          = (added ++ (gstep gs ngn g).2.toList) ++ Δg := congrArg Prod.snd hΔ
      rw [List.cons_append, buildFrom_cons, buildFrom_cons, ih, h1, h2]
      congr 1
      simp only [List.length_append]
      omega

/-- Reading the wire appended at the end of the list. -/
theorem getD_append_length (ws : List Bool) (v : Bool) :
    (ws ++ [v]).getD ws.length false = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

/-- A status pointing at an existing wire reads the same value after
appending one more wire. -/
theorem sval_append_of_lt (s : Status) (ws : List Bool) (v : Bool)
    (h : ∀ k, s = .wire k → k < ws.length) :
    sval s (ws ++ [v]) = sval s ws := by
  cases s with
  | const b => rfl
  | wire k =>
      show (ws ++ [v]).getD k false = ws.getD k false
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (h k rfl),
        List.getD_eq_getElem?_getD]

/-- With no `const false` among the statuses, `all` over the values is `all`
over the values of the wire statuses alone. -/
theorem all_sval_filterMap (ws : List Bool) : ∀ (ss : List Status),
    (∀ s ∈ ss, s ≠ .const false) →
    (ss.map (fun s => sval s ws)).all id
      = ((ss.filterMap wireOf).map (fun k => ws.getD k false)).all id := by
  intro ss
  induction ss with
  | nil => intro _; rfl
  | cons s ss ih =>
      intro h
      have hs : s ≠ .const false := h s (by simp)
      have hss : ∀ s ∈ ss, s ≠ .const false := fun s hs' => h s (by simp [hs'])
      simp only [List.map_cons, List.filterMap_cons]
      cases s with
      | const b =>
          have hb : b = true := by
            cases b with
            | false => exact absurd rfl hs
            | true => rfl
          show (b && (ss.map (fun s => sval s ws)).all id)
            = ((ss.filterMap wireOf).map (fun k => ws.getD k false)).all id
          rw [hb, Bool.true_and]
          exact ih hss
      | wire k =>
          show (ws.getD k false && (ss.map (fun s => sval s ws)).all id)
            = (ws.getD k false
              && ((ss.filterMap wireOf).map (fun k => ws.getD k false)).all id)
          rw [ih hss]

/-- With no `const true` among the statuses, `any` over the values is `any`
over the values of the wire statuses alone. -/
theorem any_sval_filterMap (ws : List Bool) : ∀ (ss : List Status),
    (∀ s ∈ ss, s ≠ .const true) →
    (ss.map (fun s => sval s ws)).any id
      = ((ss.filterMap wireOf).map (fun k => ws.getD k false)).any id := by
  intro ss
  induction ss with
  | nil => intro _; rfl
  | cons s ss ih =>
      intro h
      have hs : s ≠ .const true := h s (by simp)
      have hss : ∀ s ∈ ss, s ≠ .const true := fun s hs' => h s (by simp [hs'])
      simp only [List.map_cons, List.filterMap_cons]
      cases s with
      | const b =>
          have hb : b = false := by
            cases b with
            | true => exact absurd rfl hs
            | false => rfl
          show (b || (ss.map (fun s => sval s ws)).any id)
            = ((ss.filterMap wireOf).map (fun k => ws.getD k false)).any id
          rw [hb, Bool.false_or]
          exact ih hss
      | wire k =>
          show (ws.getD k false || (ss.map (fun s => sval s ws)).any id)
            = (ws.getD k false
              || ((ss.filterMap wireOf).map (fun k => ws.getD k false)).any id)
          rw [ih hss]

/-- The wire-list step of `Circuit.wires`, named for convenience. -/
def wstep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]

theorem bool_eq_false_of_not_eq_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact (h rfl).elim

/-- The restriction step for one gate computes the same value as the gate
itself, where the new wire values extend `ws` by the contributed gate. -/
theorem gstep_eval (gs : List Status) (ng : ℕ) (g : Gate) (w ws : List Bool)
    (hws : ws.length = 8 + ng)
    (hinv : ∀ i, w.getD i false = sval (wstat gs i) ws)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    g.op.eval (g.inputs.map (fun i => w.getD i false))
      = sval (gstep gs ng g).1 ((gstep gs ng g).2.toList.foldl wstep ws) := by
  rcases g with ⟨op, inputs⟩
  dsimp only at hop ⊢
  have hmap : inputs.map (fun i => w.getD i false)
      = (inputs.map (wstat gs)).map (fun s => sval s ws) := by
    rw [List.map_map]
    congr 1
    funext i
    show w.getD i false = sval (wstat gs i) ws
    exact hinv i
  rw [hmap]
  set ss := inputs.map (wstat gs) with hssdef
  rcases hop with rfl | rfl | rfl
  · -- op = and
    show (ss.map (fun s => sval s ws)).all id
        = sval (combine .and ng ss).1 ((combine .and ng ss).2.toList.foldl wstep ws)
    by_cases hfalse : ss.any (· = .const false) = true
    · have hcomb : combine .and ng ss = (.const false, none) := by
        simp [combine, hfalse]
      obtain ⟨s, hs, hseq⟩ : ∃ s ∈ ss, s = .const false := by
        have h1 := (List.any_eq_true).mp hfalse
        obtain ⟨s, hs, hs'⟩ := h1
        exact ⟨s, hs, by simpa using hs'⟩
      have hmem : false ∈ ss.map (fun s => sval s ws) := by
        rw [List.mem_map]
        exact ⟨s, hs, by rw [hseq]; rfl⟩
      rw [hcomb]
      show (ss.map (fun s => sval s ws)).all id = false
      cases hA : (ss.map (fun s => sval s ws)).all id with
      | false => rfl
      | true =>
          exfalso
          rw [List.all_eq_true] at hA
          have h2 := hA false hmem
          simp at h2
    · have hfalse' : ss.any (· = .const false) = false :=
        bool_eq_false_of_not_eq_true hfalse
      have hne : ∀ s ∈ ss, s ≠ .const false := by
        intro s hs
        have h1 := (List.any_eq_false).mp hfalse' s hs
        simpa using h1
      have hall := all_sval_filterMap ws ss hne
      cases hks : ss.filterMap wireOf with
      | nil =>
          have hcomb : combine .and ng ss = (.const true, none) := by
            simp [combine, hfalse', hks]
          rw [hcomb, hall, hks]
          rfl
      | cons k ks =>
          cases ks with
          | nil =>
              have hcomb : combine .and ng ss = (.wire k, none) := by
                simp [combine, hfalse', hks]
              rw [hcomb, hall, hks]
              show ([ws.getD k false].all id) = ws.getD k false
              simp
          | cons k₂ ks' =>
              have hcomb : combine .and ng ss
                  = (.wire (8 + ng), some ⟨.and, k :: k₂ :: ks'⟩) := by
                simp [combine, hfalse', hks]
              rw [hcomb, hall, hks]
              show ((k :: k₂ :: ks').map (fun k => ws.getD k false)).all id
                = (ws ++ [GateOp.eval .and
                    ((k :: k₂ :: ks').map (fun k => ws.getD k false))]).getD
                    (8 + ng) false
              rw [← hws, getD_append_length]
              rfl
  · -- op = or
    show (ss.map (fun s => sval s ws)).any id
        = sval (combine .or ng ss).1 ((combine .or ng ss).2.toList.foldl wstep ws)
    by_cases htrue : ss.any (· = .const true) = true
    · have hcomb : combine .or ng ss = (.const true, none) := by
        simp [combine, htrue]
      obtain ⟨s, hs, hseq⟩ : ∃ s ∈ ss, s = .const true := by
        have h1 := (List.any_eq_true).mp htrue
        obtain ⟨s, hs, hs'⟩ := h1
        exact ⟨s, hs, by simpa using hs'⟩
      have hmem : true ∈ ss.map (fun s => sval s ws) := by
        rw [List.mem_map]
        exact ⟨s, hs, by rw [hseq]; rfl⟩
      rw [hcomb]
      show (ss.map (fun s => sval s ws)).any id = true
      rw [List.any_eq_true]
      exact ⟨true, hmem, rfl⟩
    · have htrue' : ss.any (· = .const true) = false :=
        bool_eq_false_of_not_eq_true htrue
      have hne : ∀ s ∈ ss, s ≠ .const true := by
        intro s hs
        have h1 := (List.any_eq_false).mp htrue' s hs
        simpa using h1
      have hany := any_sval_filterMap ws ss hne
      cases hks : ss.filterMap wireOf with
      | nil =>
          have hcomb : combine .or ng ss = (.const false, none) := by
            simp [combine, htrue', hks]
          rw [hcomb, hany, hks]
          rfl
      | cons k ks =>
          cases ks with
          | nil =>
              have hcomb : combine .or ng ss = (.wire k, none) := by
                simp [combine, htrue', hks]
              rw [hcomb, hany, hks]
              show ([ws.getD k false].any id) = ws.getD k false
              simp
          | cons k₂ ks' =>
              have hcomb : combine .or ng ss
                  = (.wire (8 + ng), some ⟨.or, k :: k₂ :: ks'⟩) := by
                simp [combine, htrue', hks]
              rw [hcomb, hany, hks]
              show ((k :: k₂ :: ks').map (fun k => ws.getD k false)).any id
                = (ws ++ [GateOp.eval .or
                    ((k :: k₂ :: ks').map (fun k => ws.getD k false))]).getD
                    (8 + ng) false
              rw [← hws, getD_append_length]
              rfl
  · -- op = not
    show GateOp.eval .not (ss.map (fun s => sval s ws))
        = sval (combine .not ng ss).1 ((combine .not ng ss).2.toList.foldl wstep ws)
    cases hinputs : inputs with
    | nil =>
        rw [hinputs] at hssdef
        simp [hssdef] at *
        show (!false) = sval (combine .not ng []).1 _
        rw [show combine .not ng [] = (.const true, none) from rfl]
        rfl
    | cons a rest =>
        rw [hinputs] at hssdef
        have hss : ss = wstat gs a :: (rest.map (wstat gs)) := by
          rw [hssdef, List.map_cons]
        cases hsta : wstat gs a with
        | const b =>
            have hcomb : combine .not ng ss = (.const (!b), none) := by
              rw [hss, hsta]; rfl
            rw [hcomb, hss]
            show (!((wstat gs a :: rest.map (wstat gs)).map
                (fun s => sval s ws)).headD false) = sval (.const (!b)) _
            rw [hsta]
            simp [sval, List.headD]
        | wire k =>
            have hcomb : combine .not ng ss
                = (.wire (8 + ng), some ⟨.not, [k]⟩) := by
              rw [hss, hsta]; rfl
            rw [hcomb, hss]
            show (!((wstat gs a :: rest.map (wstat gs)).map
                (fun s => sval s ws)).headD false)
              = sval (.wire (8 + ng)) (wstep ws ⟨.not, [k]⟩)
            rw [hsta]
            have e1 : ((Status.wire k :: rest.map (wstat gs)).map
                (fun s => sval s ws)).headD false = ws.getD k false := rfl
            have e2 : wstep ws ⟨.not, [k]⟩ = ws ++ [!(ws.getD k false)] := rfl
            rw [e1, e2]
            show (!(ws.getD k false))
              = (ws ++ [!(ws.getD k false)]).getD (8 + ng) false
            rw [← hws, getD_append_length]

/-- A wire status read off `wstat` points at an input wire or at a status
already present. -/
theorem wstat_wire_lt (gs : List Status) (n : ℕ)
    (hB : ∀ s ∈ gs, ∀ k, s = .wire k → k < 8 + n) (i k : ℕ)
    (h : wstat gs i = .wire k) : k < 8 + n := by
  unfold wstat at h
  by_cases h0 : i = 0
  · rw [if_pos h0] at h; cases h
  · by_cases h9 : i = 9
    · rw [if_neg h0, if_pos h9] at h; cases h
    · by_cases h10 : i < 10
      · rw [if_neg h0, if_neg h9, if_pos h10] at h
        rw [Status.wire.injEq] at h
        omega
      · rw [if_neg h0, if_neg h9, if_neg h10] at h
        have hmem : Status.wire k ∈ gs := by
          cases hgi : gs[i - 10]? with
          | none => rw [hgi] at h; cases h
          | some s =>
              rw [hgi] at h
              have hs : s = .wire k := h
              rw [← hs]
              exact List.mem_of_getElem? hgi
        exact hB _ hmem k rfl

/-- A fresh wire produced by `combine` either comes from an input status or
is the fresh index `8 + ng` with a gate attached. -/
theorem combine_fresh (op : GateOp) (ng : ℕ) (ss : List Status) (k : ℕ)
    (h : (combine op ng ss).1 = .wire k) :
    (.wire k ∈ ss) ∨ (k = 8 + ng ∧ (combine op ng ss).2 ≠ none) := by
  cases op with
  | and =>
      by_cases hf : ss.any (· = .const false) = true
      · have hcomb : combine .and ng ss = (.const false, none) := by
          simp [combine, hf]
        rw [hcomb] at h; cases h
      · have hf' : ss.any (· = .const false) = false :=
          bool_eq_false_of_not_eq_true hf
        cases hks : ss.filterMap wireOf with
        | nil =>
            have hcomb : combine .and ng ss = (.const true, none) := by
              simp [combine, hf', hks]
            rw [hcomb] at h; cases h
        | cons k' ks =>
            cases ks with
            | nil =>
                have hcomb : combine .and ng ss = (.wire k', none) := by
                  simp [combine, hf', hks]
                rw [hcomb] at h
                rw [Status.wire.injEq] at h
                refine Or.inl ?_
                have hmem : k' ∈ ss.filterMap wireOf := by rw [hks]; simp
                rw [List.mem_filterMap] at hmem
                obtain ⟨s, hs, hso⟩ := hmem
                cases s with
                | const b => simp [wireOf] at hso
                | wire k'' =>
                    have hkk : k'' = k' := by simpa [wireOf] using hso
                    rw [hkk] at hs
                    rwa [h] at hs
            | cons k₂ ks' =>
                have hcomb : combine .and ng ss
                    = (.wire (8 + ng), some ⟨.and, k' :: k₂ :: ks'⟩) := by
                  simp [combine, hf', hks]
                rw [hcomb] at h ⊢
                rw [Status.wire.injEq] at h
                exact Or.inr ⟨h.symm, by simp⟩
  | or =>
      by_cases ht : ss.any (· = .const true) = true
      · have hcomb : combine .or ng ss = (.const true, none) := by
          simp [combine, ht]
        rw [hcomb] at h; cases h
      · have ht' : ss.any (· = .const true) = false :=
          bool_eq_false_of_not_eq_true ht
        cases hks : ss.filterMap wireOf with
        | nil =>
            have hcomb : combine .or ng ss = (.const false, none) := by
              simp [combine, ht', hks]
            rw [hcomb] at h; cases h
        | cons k' ks =>
            cases ks with
            | nil =>
                have hcomb : combine .or ng ss = (.wire k', none) := by
                  simp [combine, ht', hks]
                rw [hcomb] at h
                rw [Status.wire.injEq] at h
                refine Or.inl ?_
                have hmem : k' ∈ ss.filterMap wireOf := by rw [hks]; simp
                rw [List.mem_filterMap] at hmem
                obtain ⟨s, hs, hso⟩ := hmem
                cases s with
                | const b => simp [wireOf] at hso
                | wire k'' =>
                    have hkk : k'' = k' := by simpa [wireOf] using hso
                    rw [hkk] at hs
                    rwa [h] at hs
            | cons k₂ ks' =>
                have hcomb : combine .or ng ss
                    = (.wire (8 + ng), some ⟨.or, k' :: k₂ :: ks'⟩) := by
                  simp [combine, ht', hks]
                rw [hcomb] at h ⊢
                rw [Status.wire.injEq] at h
                exact Or.inr ⟨h.symm, by simp⟩
  | not =>
      rcases ss with _ | ⟨s, rest⟩
      · have hcomb : combine .not ng [] = (.const true, none) := by
          simp [combine]
        rw [hcomb] at h; cases h
      · cases s with
        | const b =>
            have hcomb : combine .not ng (Status.const b :: rest)
                = (.const (!b), none) := by
              simp [combine]
            rw [hcomb] at h; cases h
        | wire k' =>
            have hcomb : combine .not ng (Status.wire k' :: rest)
                = (.wire (8 + ng), some ⟨.not, [k']⟩) := by
              simp [combine]
            rw [hcomb] at h ⊢
            rw [Status.wire.injEq] at h
            exact Or.inr ⟨h.symm, by simp⟩
  | mod m => simp [combine] at h
  | maj => simp [combine] at h

theorem foldl_wstep_length (L : List Gate) (ws : List Bool) :
    (L.foldl wstep ws).length = ws.length + L.length := by
  induction L generalizing ws with
  | nil => simp
  | cons g rest ih =>
      rw [List.foldl_cons, ih]
      have e : (wstep ws g).length = ws.length + 1 := by simp [wstep]
      have e2 : (g :: rest).length = rest.length + 1 := rfl
      omega

theorem getD_append_of_ne (l : List Bool) (v : Bool) (i : ℕ)
    (h : i ≠ l.length) : (l ++ [v]).getD i false = l.getD i false := by
  by_cases hi : i < l.length
  · exact List.getD_append l [v] false i hi
  · have hi2 : l.length < i := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_lt hi2),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (le_of_lt hi2),
      List.getElem?_eq_none_iff.mpr (show [v].length ≤ i - l.length by
        simp; omega)]

/-- One step of the simulation: appending gate `g`'s value to the old wires
corresponds, under `wstat`, to running the contributed gates on the new
wires. -/
theorem sim_step (gs : List Status) (ngn : ℕ) (g : Gate) (w ws : List Bool)
    (hw : w.length = 10 + gs.length)
    (hws : ws.length = 8 + ngn)
    (hinv : ∀ i, w.getD i false = sval (wstat gs i) ws)
    (hbound : ∀ s ∈ gs, ∀ k, s = .wire k → k < 8 + ngn)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ i, (wstep w g).getD i false
      = sval (wstat (gs ++ [(gstep gs ngn g).1]) i)
          ((gstep gs ngn g).2.toList.foldl wstep ws) := by
  obtain ⟨s, og, hsg⟩ : ∃ s og, gstep gs ngn g = (s, og) := ⟨_, _, rfl⟩
  have hstep := gstep_eval gs ngn g w ws hws hinv hop
  rw [hsg] at hstep
  dsimp only at hstep
  rw [hsg]
  dsimp only
  intro i
  by_cases hi : i = 10 + gs.length
  · subst hi
    have h1 : (wstep w g).getD (10 + gs.length) false
        = g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
      show (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]).getD
          (10 + gs.length) false = _
      rw [← hw, getD_append_length]
    rw [h1, hstep]
    congr 1
    unfold wstat
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hsub : 10 + gs.length - 10 = gs.length := by omega
    rw [hsub, List.getElem?_append_right (Nat.le_refl gs.length)]
    simp
  · have h2 : (wstep w g).getD i false = w.getD i false :=
      getD_append_of_ne w _ i (by omega)
    rw [h2, hinv i]
    have h3 : wstat (gs ++ [s]) i = wstat gs i := by
      by_cases h10 : i < 10
      · have e : ∀ (gs' : List Status), wstat gs' i
            = (if i = 0 then .const false
              else if i = 9 then .const true else .wire (i - 1)) := by
          intro gs'
          unfold wstat
          by_cases h0 : i = 0
          · rw [if_pos h0, if_pos h0]
          · by_cases h9 : i = 9
            · rw [if_neg h0, if_pos h9, if_neg h0, if_pos h9]
            · rw [if_neg h0, if_neg h9, if_pos h10, if_neg h0, if_neg h9]
        rw [e, e]
      · have key : ∀ (gs₁ gs₂ : List Status),
            gs₁[i - 10]? = gs₂[i - 10]? → wstat gs₁ i = wstat gs₂ i := by
          intro gs₁ gs₂ hgs
          unfold wstat
          rw [hgs]
        apply key
        by_cases hj : i - 10 < gs.length
        · exact List.getElem?_append_left hj
        · have hgt : gs.length < i - 10 := by
            have hne : i - 10 ≠ gs.length := by
              intro hcon
              apply hi
              omega
            omega
          rw [List.getElem?_append_right (le_of_lt hgt),
            List.getElem?_eq_none_iff.mpr (le_of_lt hgt)]
          exact List.getElem?_eq_none_iff.mpr (by simp; omega)
    rw [h3]
    cases og with
    | none => rfl
    | some g' =>
        have hws'eq : (Option.toList (some g')).foldl wstep ws
            = ws ++ [g'.op.eval (g'.inputs.map (fun i => ws.getD i false))] :=
          rfl
        rw [hws'eq]
        exact (sval_append_of_lt (wstat gs i) ws _ (fun k hk => by
          have h4 := wstat_wire_lt gs ngn hbound i k hk
          omega)).symm

/-- The simulation: running the old circuit's gates corresponds, under
`wstat`, to running the built circuit's gates. -/
theorem sim_gen (L : List Gate) (gs : List Status) (added : List Gate)
    (ngn : ℕ) (w ws : List Bool)
    (hngn : ngn = added.length)
    (hw : w.length = 10 + gs.length)
    (hws : ws.length = 8 + added.length)
    (hinv : ∀ i, w.getD i false = sval (wstat gs i) ws)
    (hbound : ∀ s ∈ gs, ∀ k, s = .wire k → k < 8 + added.length)
    (hfan : ∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∃ (Δs : List Status) (Δg : List Gate),
      buildFrom gs added ngn L = (gs ++ Δs, added ++ Δg) ∧
      ∀ i, (L.foldl wstep w).getD i false
        = sval (wstat (gs ++ Δs) i) (Δg.foldl wstep ws) := by
  induction L generalizing gs added ngn w ws with
  | nil =>
      refine ⟨[], [], by simp [buildFrom], fun i => ?_⟩
      simpa using hinv i
  | cons g rest ih =>
      have hfan_g : g.op = .and ∨ g.op = .or ∨ g.op = .not :=
        hfan g (by simp)
      have hfan_rest : ∀ g' ∈ rest,
          g'.op = .and ∨ g'.op = .or ∨ g'.op = .not :=
        fun g' hg' => hfan g' (by simp [hg'])
      have hstep : ∀ i, (wstep w g).getD i false
          = sval (wstat (gs ++ [(gstep gs ngn g).1]) i)
              ((gstep gs ngn g).2.toList.foldl wstep ws) :=
        sim_step gs ngn g w ws hw (by omega) hinv
          (by rwa [← hngn] at hbound) hfan_g
      have hbound' : ∀ s' ∈ gs ++ [(gstep gs ngn g).1], ∀ k, s' = .wire k
          → k < 8 + (added ++ (gstep gs ngn g).2.toList).length := by
        intro s' hs' k hk
        simp only [List.length_append]
        rcases List.mem_append.mp hs' with hmem | hmem
        · have h1 := hbound s' hmem k hk; omega
        · have hs'eq : s' = (gstep gs ngn g).1 := by simpa using hmem
          subst hs'eq
          rcases combine_fresh g.op ngn (g.inputs.map (wstat gs)) k hk with
            hmem2 | ⟨hkeq, hne⟩
          · rw [List.mem_map] at hmem2
            obtain ⟨i, -, hi2⟩ := hmem2
            have h2 := wstat_wire_lt gs added.length hbound i k hi2
            omega
          · have hlen : (gstep gs ngn g).2.toList.length = 1 := by
              obtain ⟨g', hg'⟩ : ∃ g', (gstep gs ngn g).2 = some g' := by
                cases h2 : (gstep gs ngn g).2 with
                | none => exact absurd h2 hne
                | some g' => exact ⟨g', rfl⟩
              rw [hg']; rfl
            omega
      have hw'len : (wstep w g).length
          = 10 + (gs ++ [(gstep gs ngn g).1]).length := by
        have e : (wstep w g).length = w.length + 1 := by simp [wstep]
        rw [e, hw]
        simp only [List.length_append, List.length_singleton]
        omega
      have hws'len : ((gstep gs ngn g).2.toList.foldl wstep ws).length
          = 8 + (added ++ (gstep gs ngn g).2.toList).length := by
        rw [foldl_wstep_length, hws]; simp only [List.length_append]; omega
      obtain ⟨Δs, Δg, hbuild, hsim⟩ := ih (gs := gs ++ [(gstep gs ngn g).1])
        (added := added ++ (gstep gs ngn g).2.toList)
        (ngn := ngn + (gstep gs ngn g).2.toList.length)
        (w := wstep w g) (ws := (gstep gs ngn g).2.toList.foldl wstep ws)
        (by simp [hngn]) hw'len hws'len hstep hbound' hfan_rest
      refine ⟨(gstep gs ngn g).1 :: Δs, (gstep gs ngn g).2.toList ++ Δg, ?_, ?_⟩
      · rw [buildFrom_cons, hbuild]
        simp [List.append_assoc]
      · intro i
        have e1 : ((g :: rest).foldl wstep w)
            = rest.foldl wstep (wstep w g) := rfl
        have e2 : (((gstep gs ngn g).2.toList ++ Δg).foldl wstep ws)
            = Δg.foldl wstep ((gstep gs ngn g).2.toList.foldl wstep ws) := by
          rw [List.foldl_append]
        have e3 : gs ++ ((gstep gs ngn g).1 :: Δs)
            = (gs ++ [(gstep gs ngn g).1]) ++ Δs := by
          simp [List.append_assoc]
        rw [e1, e2, e3]
        exact hsim i

/-- If `f x = none` for some `x ∈ l`, the filterMap is strictly shorter. -/
theorem filterMap_length_le_of_none {α β : Type*} (f : α → Option β)
    (l : List α) (x : α) (hx : x ∈ l) (hfx : f x = none) :
    (l.filterMap f).length ≤ l.length - 1 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      cases hfa : f a with
      | none =>
          have h1 : (a :: l).filterMap f = l.filterMap f := by
            rw [List.filterMap_cons, hfa]
          rw [h1]
          have h2 : (l.filterMap f).length ≤ l.length :=
            List.length_filterMap_le f l
          have h3 : (a :: l).length = l.length + 1 := rfl
          omega
      | some b =>
          have h1 : (a :: l).filterMap f = b :: l.filterMap f := by
            rw [List.filterMap_cons, hfa]
          rw [h1]
          have hx' : x ∈ l := by
            rcases List.mem_cons.mp hx with h | h
            · exfalso
              rw [h] at hfx
              rw [hfx] at hfa
              cases hfa
            · exact h
          have h2 := ih hx'
          have hlen : 0 < l.length := by
            cases l with
            | nil => simp at hx'
            | cons c l' => simp
          have h3 : (a :: l).length = l.length + 1 := rfl
          have h4 : (b :: l.filterMap f).length
              = (l.filterMap f).length + 1 := rfl
          omega

theorem filterMap_length_le_one_cases (l : List ℕ) (h : l.length ≤ 1) :
    l = [] ∨ ∃ k, l = [k] := by
  cases l with
  | nil => exact Or.inl rfl
  | cons k ks =>
      cases ks with
      | nil => exact Or.inr ⟨k, rfl⟩
      | cons k₂ ks' => simp at h

/-- An AND step contributes no gate when a constant false is among the
inputs, or when at most one input is a genuine wire. -/
theorem combine_and_snd_none (ngn : ℕ) (ss : List Status)
    (h : (∃ s ∈ ss, s = .const false) ∨ (ss.filterMap wireOf).length ≤ 1) :
    (combine .and ngn ss).2 = none := by
  rcases h with ⟨s, hs, rfl⟩ | hlen
  · have h1 : ss.any (· = .const false) = true :=
      List.any_eq_true.mpr ⟨.const false, hs, rfl⟩
    have hcomb : combine .and ngn ss = (.const false, none) := by
      simp [combine, h1]
    rw [hcomb]
  · by_cases hf : ss.any (· = .const false) = true
    · have hcomb : combine .and ngn ss = (.const false, none) := by
        simp [combine, hf]
      rw [hcomb]
    · have hf' : ss.any (· = .const false) = false :=
        bool_eq_false_of_not_eq_true hf
      rcases filterMap_length_le_one_cases _ hlen with hks | ⟨k, hks⟩ <;>
        simp [combine, hf', hks]

/-- An OR step contributes no gate when a constant true is among the
inputs, or when at most one input is a genuine wire. -/
theorem combine_or_snd_none (ngn : ℕ) (ss : List Status)
    (h : (∃ s ∈ ss, s = .const true) ∨ (ss.filterMap wireOf).length ≤ 1) :
    (combine .or ngn ss).2 = none := by
  rcases h with ⟨s, hs, rfl⟩ | hlen
  · have h1 : ss.any (· = .const true) = true :=
      List.any_eq_true.mpr ⟨.const true, hs, rfl⟩
    have hcomb : combine .or ngn ss = (.const true, none) := by
      simp [combine, h1]
    rw [hcomb]
  · by_cases ht : ss.any (· = .const true) = true
    · have hcomb : combine .or ngn ss = (.const true, none) := by
        simp [combine, ht]
      rw [hcomb]
    · have ht' : ss.any (· = .const true) = false :=
        bool_eq_false_of_not_eq_true ht
      rcases filterMap_length_le_one_cases _ hlen with hks | ⟨k, hks⟩ <;>
        simp [combine, ht', hks]

/-- A NOT step contributes no gate when its first input is constant
(including the empty input list). -/
theorem combine_not_snd_none (ngn : ℕ) (ss : List Status)
    (h : ss = [] ∨ ∃ b ss', ss = .const b :: ss') :
    (combine .not ngn ss).2 = none := by
  rcases h with rfl | ⟨b, ss', rfl⟩ <;> simp [combine]

/-- A constant status always comes with no contributed gate. -/
theorem combine_snd_none_of_const (op : GateOp) (ngn : ℕ) (ss : List Status)
    (b : Bool) (h : (combine op ngn ss).1 = .const b) :
    (combine op ngn ss).2 = none := by
  cases op with
  | and =>
      by_cases hf : ss.any (· = .const false) = true
      · have hcomb : combine .and ngn ss = (.const false, none) := by
          simp [combine, hf]
        rw [hcomb]
      · have hf' : ss.any (· = .const false) = false :=
          bool_eq_false_of_not_eq_true hf
        cases hks : ss.filterMap wireOf with
        | nil =>
            have hcomb : combine .and ngn ss = (.const true, none) := by
              simp [combine, hf', hks]
            rw [hcomb]
        | cons k ks =>
            cases ks with
            | nil =>
                have hcomb : combine .and ngn ss = (.wire k, none) := by
                  simp [combine, hf', hks]
                rw [hcomb] at h; cases h
            | cons k₂ ks' =>
                have hcomb : combine .and ngn ss
                    = (.wire (8 + ngn), some ⟨.and, k :: k₂ :: ks'⟩) := by
                  simp [combine, hf', hks]
                rw [hcomb] at h; cases h
  | or =>
      by_cases ht : ss.any (· = .const true) = true
      · have hcomb : combine .or ngn ss = (.const true, none) := by
          simp [combine, ht]
        rw [hcomb]
      · have ht' : ss.any (· = .const true) = false :=
          bool_eq_false_of_not_eq_true ht
        cases hks : ss.filterMap wireOf with
        | nil =>
            have hcomb : combine .or ngn ss = (.const false, none) := by
              simp [combine, ht', hks]
            rw [hcomb]
        | cons k ks =>
            cases ks with
            | nil =>
                have hcomb : combine .or ngn ss = (.wire k, none) := by
                  simp [combine, ht', hks]
                rw [hcomb] at h; cases h
            | cons k₂ ks' =>
                have hcomb : combine .or ngn ss
                    = (.wire (8 + ngn), some ⟨.or, k :: k₂ :: ks'⟩) := by
                  simp [combine, ht', hks]
                rw [hcomb] at h; cases h
  | not =>
      rcases ss with _ | ⟨s, rest⟩
      · simp [combine]
      · cases s with
        | const b' => simp [combine]
        | wire k =>
            have hcomb : combine .not ngn (Status.wire k :: rest)
                = (.wire (8 + ngn), some ⟨.not, [k]⟩) := by
              simp [combine]
            rw [hcomb] at h; cases h
  | mod m => simp [combine]
  | maj => simp [combine]

/-- A list of length at most one containing `a` is exactly `[a]`. -/
theorem eq_singleton_of_mem_of_length_le_one {a : ℕ} {l : List ℕ}
    (h : a ∈ l) (hlen : l.length ≤ 1) : l = [a] := by
  cases l with
  | nil => simp at h
  | cons b rest =>
      cases rest with
      | nil =>
          have hb : b = a := (List.mem_singleton.mp h).symm
          rw [hb]
      | cons c rest' =>
          simp only [List.length_cons] at hlen
          omega

/-- A special gate never contributes a gate to the restriction. -/
theorem special_gstep_snd (gs : List Status) (ngn : ℕ) (g : Gate)
    (hsp : special g) (hlen : g.inputs.length ≤ 2)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hnot1 : g.op = .not → g.inputs.length ≤ 1) :
    (gstep gs ngn g).2 = none := by
  have hw0 : wstat gs 0 = .const false := rfl
  have hw9 : wstat gs 9 = .const true := rfl
  rcases g with ⟨op, inputs⟩
  dsimp only at hop
  have hsp' : 0 ∈ inputs ∨ 9 ∈ inputs := hsp
  have hlen' : inputs.length ≤ 2 := hlen
  have hnot1' : op = .not → inputs.length ≤ 1 := hnot1
  have hmem0 : 0 ∈ inputs → Status.const false ∈ inputs.map (wstat gs) :=
    fun h0 => List.mem_map.mpr ⟨0, h0, hw0⟩
  have hmem9 : 9 ∈ inputs → Status.const true ∈ inputs.map (wstat gs) :=
    fun h9 => List.mem_map.mpr ⟨9, h9, hw9⟩
  have hlenmap : (inputs.map (wstat gs)).length = inputs.length :=
    List.length_map ..
  show (combine op ngn (inputs.map (wstat gs))).2 = none
  rcases hop with rfl | rfl | rfl
  · apply combine_and_snd_none
    rcases hsp' with h0 | h9
    · exact Or.inl ⟨.const false, hmem0 h0, rfl⟩
    · refine Or.inr ?_
      have h1 := filterMap_length_le_of_none wireOf (inputs.map (wstat gs))
        (.const true) (hmem9 h9) rfl
      omega
  · apply combine_or_snd_none
    rcases hsp' with h0 | h9
    · refine Or.inr ?_
      have h1 := filterMap_length_le_of_none wireOf (inputs.map (wstat gs))
        (.const false) (hmem0 h0) rfl
      omega
    · exact Or.inl ⟨.const true, hmem9 h9, rfl⟩
  · have hlen1 : inputs.length ≤ 1 := hnot1' rfl
    apply combine_not_snd_none
    rcases hsp' with h0 | h9
    · have hinputs : inputs = [0] :=
        eq_singleton_of_mem_of_length_le_one h0 hlen1
      exact Or.inr ⟨false, [], by simp [hinputs, hw0]⟩
    · have hinputs : inputs = [9] :=
        eq_singleton_of_mem_of_length_le_one h9 hlen1
      exact Or.inr ⟨true, [], by simp [hinputs, hw9]⟩

/-- A gate with a constant-status input contributes no gate either, when
its step is evaluated at a state where that input has constant status. -/
theorem nonspec_const_gstep_snd (gs : List Status) (ngn : ℕ) (g : Gate)
    (hlen : g.inputs.length ≤ 2)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hnot1 : g.op = .not → g.inputs.length ≤ 1)
    (hconst : ∃ j ∈ g.inputs, ∃ b, wstat gs j = .const b) :
    (gstep gs ngn g).2 = none := by
  obtain ⟨j, hjin, b, hjstat⟩ := hconst
  rcases g with ⟨op, inputs⟩
  dsimp only at hop
  have hjin' : j ∈ inputs := hjin
  have hlen' : inputs.length ≤ 2 := hlen
  have hnot1' : op = .not → inputs.length ≤ 1 := hnot1
  have hmem : Status.const b ∈ inputs.map (wstat gs) :=
    List.mem_map.mpr ⟨j, hjin', hjstat⟩
  have hlenmap : (inputs.map (wstat gs)).length = inputs.length :=
    List.length_map ..
  show (combine op ngn (inputs.map (wstat gs))).2 = none
  rcases hop with rfl | rfl | rfl
  · apply combine_and_snd_none
    cases b with
    | false => exact Or.inl ⟨.const false, hmem, rfl⟩
    | true =>
        refine Or.inr ?_
        have h1 := filterMap_length_le_of_none wireOf (inputs.map (wstat gs))
          (.const true) hmem rfl
        omega
  · apply combine_or_snd_none
    cases b with
    | true => exact Or.inl ⟨.const true, hmem, rfl⟩
    | false =>
        refine Or.inr ?_
        have h1 := filterMap_length_le_of_none wireOf (inputs.map (wstat gs))
          (.const false) hmem rfl
        omega
  · have hlen1 : inputs.length ≤ 1 := hnot1' rfl
    have hinputs : inputs = [j] :=
      eq_singleton_of_mem_of_length_le_one hjin' hlen1
    apply combine_not_snd_none
    exact Or.inr ⟨b, [], by simp [hinputs, hjstat]⟩

/-- The restriction of a gate list adds at most one new gate per
non-special gate. -/
theorem buildFrom_length_le (L : List Gate) :
    (∀ (gs : List Status) (ngn : ℕ) (g : Gate), g ∈ L → special g →
      (gstep gs ngn g).2 = none) →
    ∀ (gs : List Status) (added : List Gate) (ngn : ℕ),
    (buildFrom gs added ngn L).2.length
      ≤ added.length
        + (L.filter (fun g => !([0, 9].any g.inputs.contains))).length := by
  induction L with
  | nil => intro _ gs added ngn; simp [buildFrom]
  | cons g rest ih =>
      intro hskip gs added ngn
      have hskip' : ∀ (gs : List Status) (ngn : ℕ) (g₀ : Gate), g₀ ∈ rest →
          special g₀ → (gstep gs ngn g₀).2 = none :=
        fun gs ngn g₀ hg₀ hsp₀ =>
          hskip gs ngn g₀ (List.mem_cons_of_mem g hg₀) hsp₀
      rw [buildFrom_cons]
      by_cases hsp : special g
      · have h2 := hskip gs ngn g List.mem_cons_self hsp
        have ih' := ih hskip' (gs ++ [(gstep gs ngn g).1])
          (added ++ (gstep gs ngn g).2.toList)
          (ngn + (gstep gs ngn g).2.toList.length)
        simp only [h2, Option.toList_none, List.append_nil, List.length_nil,
          Nat.add_zero] at ih'
        simp only [h2, Option.toList_none, List.append_nil, List.length_nil,
          Nat.add_zero]
        have hfilter : ((g :: rest).filter
              (fun g => !([0, 9].any g.inputs.contains))).length
            = (rest.filter (fun g => !([0, 9].any g.inputs.contains))).length := by
          have h1 : ([0, 9].any g.inputs.contains) = true :=
            (special_iff g).mpr hsp
          simp only [List.filter_cons, h1, Bool.not_true, Bool.false_eq_true,
            ite_false]
        rw [hfilter]
        exact ih'
      · have ih' := ih hskip' (gs ++ [(gstep gs ngn g).1])
          (added ++ (gstep gs ngn g).2.toList)
          (ngn + (gstep gs ngn g).2.toList.length)
        have hfilter : ((g :: rest).filter
              (fun g => !([0, 9].any g.inputs.contains))).length
            = (rest.filter (fun g => !([0, 9].any g.inputs.contains))).length
              + 1 := by
          have h1 : ([0, 9].any g.inputs.contains) = false :=
            (not_special_iff g).mpr hsp
          simp only [List.filter_cons, h1, Bool.not_false, if_true,
            List.length_cons]
        have hle : (gstep gs ngn g).2.toList.length ≤ 1 := by
          cases (gstep gs ngn g).2 <;> simp
        simp only [List.length_append] at ih'
        rw [hfilter]
        omega

/-- Every gate produced by `buildFrom` either was already in `added` or is
the contributed gate of a gate of the input list, at some state. -/
theorem buildFrom_mem_snd (L : List Gate) (gs : List Status)
    (added : List Gate) (ngn : ℕ) :
    ∀ g' ∈ (buildFrom gs added ngn L).2,
      g' ∈ added ∨ ∃ g ∈ L, ∃ (gs' : List Status) (ngn' : ℕ),
        (gstep gs' ngn' g).2 = some g' := by
  induction L generalizing gs added ngn with
  | nil => intro g' hg'; exact Or.inl hg'
  | cons g rest ih =>
      intro g' hg'
      rw [buildFrom_cons] at hg'
      rcases ih (gs ++ [(gstep gs ngn g).1])
        (added ++ (gstep gs ngn g).2.toList)
        (ngn + (gstep gs ngn g).2.toList.length) g' hg' with
        h | ⟨g₀, hg₀, gs', ngn', hstep⟩
      · rcases List.mem_append.mp h with h1 | h1
        · exact Or.inl h1
        · refine Or.inr ⟨g, by simp, gs, ngn, ?_⟩
          cases hog : (gstep gs ngn g).2 with
          | none => simp [hog] at h1
          | some g'' =>
              have h2 : g' = g'' := by
                have h3 : (gstep gs ngn g).2.toList = [g''] := by
                  rw [hog]; rfl
                rw [h3] at h1
                exact List.mem_singleton.mp h1
              rw [h2]
      · exact Or.inr ⟨g₀, by simp [hg₀], gs', ngn', hstep⟩

/-- A contributed gate has the same operation as its source gate and no
more inputs. -/
theorem gstep_some_fanin (gs : List Status) (ngn : ℕ) (g g' : Gate)
    (h : (gstep gs ngn g).2 = some g') :
    g'.op = g.op ∧ g'.inputs.length ≤ g.inputs.length := by
  cases hop : g.op with
  | and =>
      by_cases hf : (g.inputs.map (wstat gs)).any (· = .const false) = true
      · have hcomb : gstep gs ngn g = (.const false, none) := by
          simp [gstep, combine, hop, hf]
        rw [hcomb] at h; cases h
      · have hf' : (g.inputs.map (wstat gs)).any (· = .const false) = false :=
          bool_eq_false_of_not_eq_true hf
        cases hks : (g.inputs.map (wstat gs)).filterMap wireOf with
        | nil =>
            have hcomb : gstep gs ngn g = (.const true, none) := by
              simp [gstep, combine, hop, hf', hks]
            rw [hcomb] at h; cases h
        | cons k ks =>
            cases ks with
            | nil =>
                have hcomb : gstep gs ngn g = (.wire k, none) := by
                  simp [gstep, combine, hop, hf', hks]
                rw [hcomb] at h; cases h
            | cons k₂ ks' =>
                have hcomb : gstep gs ngn g
                    = (.wire (8 + ngn), some ⟨.and, k :: k₂ :: ks'⟩) := by
                  simp [gstep, combine, hop, hf', hks]
                rw [hcomb] at h
                have h2 : some ⟨GateOp.and, k :: k₂ :: ks'⟩ = some g' := h
                have hg' : g' = ⟨GateOp.and, k :: k₂ :: ks'⟩ :=
                  (Option.some.inj h2).symm
                subst hg'
                refine ⟨rfl, ?_⟩
                have e0 : (⟨GateOp.and, k :: k₂ :: ks'⟩ : Gate).inputs.length
                    = (k :: k₂ :: ks').length := rfl
                have e1 : (k :: k₂ :: ks').length
                    = ((g.inputs.map (wstat gs)).filterMap wireOf).length := by
                  rw [hks]
                have e2 := List.length_filterMap_le wireOf
                  (g.inputs.map (wstat gs))
                have e3 : (g.inputs.map (wstat gs)).length
                    = g.inputs.length := List.length_map ..
                omega
  | or =>
      by_cases ht : (g.inputs.map (wstat gs)).any (· = .const true) = true
      · have hcomb : gstep gs ngn g = (.const true, none) := by
          simp [gstep, combine, hop, ht]
        rw [hcomb] at h; cases h
      · have ht' : (g.inputs.map (wstat gs)).any (· = .const true) = false :=
          bool_eq_false_of_not_eq_true ht
        cases hks : (g.inputs.map (wstat gs)).filterMap wireOf with
        | nil =>
            have hcomb : gstep gs ngn g = (.const false, none) := by
              simp [gstep, combine, hop, ht', hks]
            rw [hcomb] at h; cases h
        | cons k ks =>
            cases ks with
            | nil =>
                have hcomb : gstep gs ngn g = (.wire k, none) := by
                  simp [gstep, combine, hop, ht', hks]
                rw [hcomb] at h; cases h
            | cons k₂ ks' =>
                have hcomb : gstep gs ngn g
                    = (.wire (8 + ngn), some ⟨.or, k :: k₂ :: ks'⟩) := by
                  simp [gstep, combine, hop, ht', hks]
                rw [hcomb] at h
                have h2 : some ⟨GateOp.or, k :: k₂ :: ks'⟩ = some g' := h
                have hg' : g' = ⟨GateOp.or, k :: k₂ :: ks'⟩ :=
                  (Option.some.inj h2).symm
                subst hg'
                refine ⟨rfl, ?_⟩
                have e0 : (⟨GateOp.or, k :: k₂ :: ks'⟩ : Gate).inputs.length
                    = (k :: k₂ :: ks').length := rfl
                have e1 : (k :: k₂ :: ks').length
                    = ((g.inputs.map (wstat gs)).filterMap wireOf).length := by
                  rw [hks]
                have e2 := List.length_filterMap_le wireOf
                  (g.inputs.map (wstat gs))
                have e3 : (g.inputs.map (wstat gs)).length
                    = g.inputs.length := List.length_map ..
                omega
  | not =>
      cases hss : g.inputs.map (wstat gs) with
      | nil =>
          have hcomb : gstep gs ngn g = (.const true, none) := by
            simp [gstep, combine, hop, hss]
          rw [hcomb] at h; cases h
      | cons s rest =>
          cases s with
          | const b =>
              have hcomb : gstep gs ngn g = (.const (!b), none) := by
                simp [gstep, combine, hop, hss]
              rw [hcomb] at h; cases h
          | wire k =>
              have hcomb : gstep gs ngn g
                  = (.wire (8 + ngn), some ⟨.not, [k]⟩) := by
                simp [gstep, combine, hop, hss]
              rw [hcomb] at h
              have h2 : some ⟨GateOp.not, [k]⟩ = some g' := h
              have hg' : g' = ⟨GateOp.not, [k]⟩ := (Option.some.inj h2).symm
              subst hg'
              refine ⟨rfl, ?_⟩
              have hne : g.inputs ≠ [] := by
                intro hnil
                rw [hnil] at hss
                simp at hss
              cases h3 : g.inputs with
              | nil => exact absurd h3 hne
              | cons a r => simp
  | mod m =>
      have hcomb : gstep gs ngn g = (.const false, none) := by
        simp [gstep, combine, hop]
      rw [hcomb] at h; cases h
  | maj =>
      have hcomb : gstep gs ngn g = (.const false, none) := by
        simp [gstep, combine, hop]
      rw [hcomb] at h; cases h

/-- If the gate at a decomposition step is skipped, the whole restriction
has at most one gate fewer than the number of non-special gates. -/
theorem build_length_le_of_skip (L₁ : List Gate) (h : Gate) (L₂ : List Gate)
    (hskip : ∀ (gs : List Status) (ngn : ℕ) (g : Gate), g ∈ L₁ ++ h :: L₂ →
      special g → (gstep gs ngn g).2 = none)
    (hskip_h : (gstep (buildFrom [] [] 0 L₁).1
      ((buildFrom [] [] 0 L₁).2.length) h).2 = none)
    (hns : ¬ special h) :
    (buildFrom [] [] 0 (L₁ ++ h :: L₂)).2.length + 1
      ≤ ((L₁ ++ h :: L₂).filter
          (fun g => !([0, 9].any g.inputs.contains))).length := by
  have hA := buildFrom_length_le L₁
    (fun gs ngn g hg hsp => hskip gs ngn g (List.mem_append_left _ hg) hsp)
    [] [] 0
  have hB : buildFrom [] [] 0 (L₁ ++ h :: L₂)
      = buildFrom ((buildFrom [] [] 0 L₁).1
          ++ [(gstep (buildFrom [] [] 0 L₁).1
            ((buildFrom [] [] 0 L₁).2.length) h).1])
        ((buildFrom [] [] 0 L₁).2
          ++ (gstep (buildFrom [] [] 0 L₁).1
            ((buildFrom [] [] 0 L₁).2.length) h).2.toList)
        ((buildFrom [] [] 0 L₁).2.length
          + (gstep (buildFrom [] [] 0 L₁).1
            ((buildFrom [] [] 0 L₁).2.length) h).2.toList.length) L₂ := by
    have e := buildFrom_append [] [] 0 L₁ (h :: L₂)
    simp only [List.length_nil, Nat.sub_zero, Nat.add_zero] at e
    rw [e, buildFrom_cons]
  have hC := buildFrom_length_le L₂
    (fun gs ngn g hg hsp =>
      hskip gs ngn g (List.mem_append_right _ (List.mem_cons_of_mem h hg)) hsp)
    ((buildFrom [] [] 0 L₁).1
      ++ [(gstep (buildFrom [] [] 0 L₁).1
        ((buildFrom [] [] 0 L₁).2.length) h).1])
    ((buildFrom [] [] 0 L₁).2
      ++ (gstep (buildFrom [] [] 0 L₁).1
        ((buildFrom [] [] 0 L₁).2.length) h).2.toList)
    ((buildFrom [] [] 0 L₁).2.length
      + (gstep (buildFrom [] [] 0 L₁).1
        ((buildFrom [] [] 0 L₁).2.length) h).2.toList.length)
  have hfilter : ((L₁ ++ h :: L₂).filter
        (fun g => !([0, 9].any g.inputs.contains))).length
      = (L₁.filter (fun g => !([0, 9].any g.inputs.contains))).length
        + ((L₂.filter (fun g => !([0, 9].any g.inputs.contains))).length + 1) := by
    have h1 : ([0, 9].any h.inputs.contains) = false :=
      (not_special_iff h).mpr hns
    simp only [List.filter_append, List.length_append, List.filter_cons, h1,
      Bool.not_false, if_true, List.length_cons]
  rw [hB]
  simp only [hskip_h, Option.toList_none, List.append_nil, List.length_nil,
    Nat.add_zero] at hC
  simp only [hskip_h, Option.toList_none, List.append_nil, List.length_nil,
    Nat.add_zero]
  simp only [List.length_nil, Nat.zero_add] at hA
  omega

/-- A gate occurring at position `k` splits the gate list. -/
theorem gates_take_append (C : Circuit) (hk : C.gates[k]? = some g) :
    C.gates = C.gates.take k ++ g :: C.gates.drop (k + 1) := by
  have hklen : k < C.gates.length := by
    by_contra hc
    have hle : C.gates.length ≤ k := le_of_not_gt hc
    have hnone : C.gates[k]? = none := List.getElem?_eq_none_iff.mpr hle
    rw [hk] at hnone
    cases hnone
  have hget : C.gates[k] = g := by
    have h := hk
    rw [List.getElem?_eq_getElem hklen] at h
    exact Option.some.inj h
  have e1 : C.gates.take k ++ C.gates.drop k = C.gates :=
    List.take_append_drop ..
  have e2 : C.gates.drop k = g :: C.gates.drop (k + 1) := by
    have e := List.drop_eq_getElem_cons hklen
    rw [hget] at e
    exact e
  conv_lhs => rw [← e1]
  rw [e2]

/-- The status list of a full build, read at the position just past a
prefix, is the status the next gate receives at its own step. -/
theorem buildFrom_fst_getElem (gs : List Status) (added : List Gate)
    (ngn : ℕ) (L₁ : List Gate) (g : Gate) (L₂ : List Gate) :
    ((buildFrom gs added ngn (L₁ ++ g :: L₂)).1)[gs.length + L₁.length]?
      = some (gstep (buildFrom gs added ngn L₁).1
          ((buildFrom gs added ngn L₁).2.length - added.length + ngn) g).1 := by
  rw [buildFrom_append, buildFrom_cons]
  obtain ⟨Δs, Δg, hΔ, -⟩ := buildFrom_extends
    ((buildFrom gs added ngn L₁).1 ++ [(gstep (buildFrom gs added ngn L₁).1
      ((buildFrom gs added ngn L₁).2.length - added.length + ngn) g).1])
    ((buildFrom gs added ngn L₁).2 ++ (gstep (buildFrom gs added ngn L₁).1
      ((buildFrom gs added ngn L₁).2.length - added.length + ngn) g).2.toList)
    (((buildFrom gs added ngn L₁).2.length - added.length + ngn)
      + (gstep (buildFrom gs added ngn L₁).1
        ((buildFrom gs added ngn L₁).2.length - added.length + ngn)
        g).2.toList.length)
    L₂
  have h1 := congrArg Prod.fst hΔ
  rw [h1, List.getElem?_append_left (by
      have e := buildFrom_fst_length gs added ngn L₁
      simp only [List.length_append, List.length_singleton]; omega),
    List.getElem?_append_right (by
      have e := buildFrom_fst_length gs added ngn L₁; omega)]
  have e := buildFrom_fst_length gs added ngn L₁
  have e2 : gs.length + L₁.length - (buildFrom gs added ngn L₁).1.length = 0 := by
    omega
  rw [e2]
  rfl

/-- The final status of the wire of the gate at position `k`. -/
theorem statusOf_gate (C : Circuit) (hk : C.gates[k]? = some g) :
    statusOf C (10 + k) = (gstep (buildFrom [] [] 0 (C.gates.take k)).1
      ((buildFrom [] [] 0 (C.gates.take k)).2.length) g).1 := by
  have hklen : k < C.gates.length := by
    by_contra hc
    have hle : C.gates.length ≤ k := le_of_not_gt hc
    have hnone : C.gates[k]? = none := List.getElem?_eq_none_iff.mpr hle
    rw [hk] at hnone
    cases hnone
  have hdec := gates_take_append C hk
  have hget := buildFrom_fst_getElem [] [] 0 (C.gates.take k) g
    (C.gates.drop (k + 1))
  simp only [Nat.zero_add, List.length_nil, List.length_take,
    min_eq_left (le_of_lt hklen), Nat.sub_zero, Nat.add_zero] at hget
  have hbuild : (buildFrom [] [] 0 C.gates).1
      = (buildFrom [] [] 0 (C.gates.take k ++ g :: C.gates.drop (k + 1))).1 := by
    conv_lhs => rw [hdec]
  show wstat (buildFrom [] [] 0 C.gates).1 (10 + k) = _
  rw [hbuild]
  unfold wstat
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hsub : 10 + k - 10 = k := by omega
  rw [hsub, hget]
  rfl

/-- Extending the status list can only turn a wire status into `const
false` (a not-yet-computed wire) or leave it unchanged. -/
theorem wstat_append (gs Δ : List Status) (j : ℕ) :
    wstat (gs ++ Δ) j = wstat gs j ∨ wstat gs j = .const false := by
  unfold wstat
  by_cases h0 : j = 0
  · rw [if_pos h0, if_pos h0]; exact Or.inl rfl
  · by_cases h9 : j = 9
    · rw [if_neg h0, if_pos h9, if_neg h0, if_pos h9]; exact Or.inl rfl
    · by_cases h10 : j < 10
      · rw [if_neg h0, if_neg h9, if_pos h10, if_neg h0, if_neg h9, if_pos h10]
        exact Or.inl rfl
      · rw [if_neg h0, if_neg h9, if_neg h10, if_neg h0, if_neg h9, if_neg h10]
        by_cases hj : j - 10 < gs.length
        · rw [List.getElem?_append_left hj]; exact Or.inl rfl
        · have hnone : gs[j - 10]? = none :=
            List.getElem?_eq_none_iff.mpr (by omega)
          rw [hnone]; exact Or.inr rfl

/-- If the final status of a wire `j` is constant, then already at the
step of the gate at position `k` its status was that constant, or
`const false`. -/
theorem statusOf_step_const (C : Circuit) (hk : C.gates[k]? = some g) (j : ℕ)
    (b : Bool) (hst : statusOf C j = .const b) :
    wstat (buildFrom [] [] 0 (C.gates.take k)).1 j = .const b
      ∨ wstat (buildFrom [] [] 0 (C.gates.take k)).1 j = .const false := by
  obtain ⟨Δs, Δg, hΔ, -⟩ := buildFrom_extends
    (buildFrom [] [] 0 (C.gates.take k)).1
    (buildFrom [] [] 0 (C.gates.take k)).2
    ((buildFrom [] [] 0 (C.gates.take k)).2.length) (g :: C.gates.drop (k + 1))
  have hfst : (build C).1 = (buildFrom [] [] 0 (C.gates.take k)).1 ++ Δs := by
    have hbuild : build C = buildFrom (buildFrom [] [] 0 (C.gates.take k)).1
        (buildFrom [] [] 0 (C.gates.take k)).2
        ((buildFrom [] [] 0 (C.gates.take k)).2.length)
        (g :: C.gates.drop (k + 1)) := by
      show buildFrom [] [] 0 C.gates = _
      conv_lhs => rw [gates_take_append C hk]
      rw [buildFrom_append]
      simp only [List.length_nil, Nat.sub_zero, Nat.add_zero]
    have h2 : build C = ((buildFrom [] [] 0 (C.gates.take k)).1 ++ Δs,
        (buildFrom [] [] 0 (C.gates.take k)).2 ++ Δg) := by rw [hbuild, hΔ]
    exact congrArg Prod.fst h2
  have hst' : wstat ((buildFrom [] [] 0 (C.gates.take k)).1 ++ Δs) j
      = .const b := by
    have e : statusOf C j
        = wstat ((buildFrom [] [] 0 (C.gates.take k)).1 ++ Δs) j := by
      show wstat (build C).1 j = _
      rw [hfst]
    rw [e] at hst; exact hst
  rcases wstat_append (buildFrom [] [] 0 (C.gates.take k)).1 Δs j with hkj | hkj
  · exact Or.inl (hkj ▸ hst')
  · exact Or.inr hkj

/-- A special gate one of whose inputs has constant status at its step,
where all inputs are that wire or the fixed wires, receives constant
status itself. -/
theorem special_step_status_const (gs : List Status) (ngn : ℕ) (g : Gate)
    (v : ℕ) (b : Bool) (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hlen : g.inputs.length ≤ 2) (hnot1 : g.op = .not → g.inputs.length ≤ 1)
    (hsp : special g) (hvin : v ∈ g.inputs) (hv0 : v ≠ 0) (hv9 : v ≠ 9)
    (hvstat : wstat gs v = .const b) :
    ∃ b', (gstep gs ngn g).1 = .const b' := by
  have hw0 : wstat gs 0 = .const false := rfl
  have hw9 : wstat gs 9 = .const true := rfl
  have key : ∀ u ∈ g.inputs, u = v ∨ u = 0 ∨ u = 9 := by
    intro u hu
    cases hgi : g.inputs with
    | nil => simp [hgi] at hu
    | cons a rest =>
        cases rest with
        | nil =>
            have hua : u = a := by simpa [hgi] using hu
            have hva : v = a := by simpa [hgi] using hvin
            exact Or.inl (by rw [hua, hva])
        | cons c rest' =>
            have hrest : rest' = [] := by
              cases rest' with
              | nil => rfl
              | cons d rest'' =>
                  simp only [hgi, List.length_cons] at hlen
                  omega
            subst hrest
            have hu2 : u = a ∨ u = c := by simpa [hgi] using hu
            have hv2 : v = a ∨ v = c := by simpa [hgi] using hvin
            have hsp2 : a = 0 ∨ a = 9 ∨ c = 0 ∨ c = 9 := by
              rcases hsp with h0 | h9
              · have hm : 0 = a ∨ 0 = c := by simpa [hgi] using h0
                rcases hm with h | h
                · exact Or.inl h.symm
                · exact Or.inr (Or.inr (Or.inl h.symm))
              · have hm : 9 = a ∨ 9 = c := by simpa [hgi] using h9
                rcases hm with h | h
                · exact Or.inr (Or.inl h.symm)
                · exact Or.inr (Or.inr (Or.inr h.symm))
            rcases hu2 with rfl | rfl <;> rcases hv2 with hv | hv
            · exact Or.inl hv.symm
            · rcases hsp2 with h | h | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
              · exact absurd (hv.trans h) hv0
              · exact absurd (hv.trans h) hv9
            · rcases hsp2 with h | h | h | h
              · exact absurd (hv.trans h) hv0
              · exact absurd (hv.trans h) hv9
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
            · exact Or.inl hv.symm
  have hallconst : ∀ s ∈ g.inputs.map (wstat gs), ∃ b', s = .const b' := by
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨u, huin, rfl⟩ := hs
    rcases key u huin with h | h | h
    · exact ⟨b, by rw [h]; exact hvstat⟩
    · exact ⟨false, by rw [h]; exact hw0⟩
    · exact ⟨true, by rw [h]; exact hw9⟩
  have hfilter : (g.inputs.map (wstat gs)).filterMap wireOf = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro s hs
    obtain ⟨b', hb'⟩ := hallconst s hs
    simp [wireOf, hb']
  rcases hop with hop | hop | hop
  · by_cases hf : (g.inputs.map (wstat gs)).any (· = .const false) = true
    · exact ⟨false, by simp [gstep, combine, hop, hf]⟩
    · have hf' : (g.inputs.map (wstat gs)).any (· = .const false) = false :=
        bool_eq_false_of_not_eq_true hf
      exact ⟨true, by simp [gstep, combine, hop, hf', hfilter]⟩
  · by_cases ht : (g.inputs.map (wstat gs)).any (· = .const true) = true
    · exact ⟨true, by simp [gstep, combine, hop, ht]⟩
    · have ht' : (g.inputs.map (wstat gs)).any (· = .const true) = false :=
        bool_eq_false_of_not_eq_true ht
      exact ⟨false, by simp [gstep, combine, hop, ht', hfilter]⟩
  · have hsing : g.inputs = [v] := by
      apply eq_singleton_of_mem_of_length_le_one hvin
      exact hnot1 hop
    have hcomb : gstep gs ngn g = (.const (!b), none) := by
      have hss : g.inputs.map (wstat gs) = [.const b] := by
        rw [hsing]; simp [hvstat]
      simp [gstep, combine, hop, hss]
    exact ⟨!b, congrArg Prod.fst hcomb⟩

/-- A special gate that is not in clean form (with the other input outside
the fixed wires) receives constant status at its step. -/
theorem dirty_status_const (gs : List Status) (ngn : ℕ) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hlen : g.inputs.length ≤ 2) (hnot1 : g.op = .not → g.inputs.length ≤ 1)
    (hsp : special g)
    (hclean : ¬ ((g.op = .or ∧ ∃ w, (g.inputs = [0, w] ∨ g.inputs = [w, 0])
        ∧ w ≠ 0 ∧ w ≠ 9)
      ∨ (g.op = .and ∧ ∃ w, (g.inputs = [9, w] ∨ g.inputs = [w, 9])
        ∧ w ≠ 0 ∧ w ≠ 9))) :
    ∃ b', (gstep gs ngn g).1 = .const b' := by
  have hw0 : wstat gs 0 = .const false := rfl
  have hw9 : wstat gs 9 = .const true := rfl
  have hfilter_of : (∀ u ∈ g.inputs, u = 0 ∨ u = 9) →
      (g.inputs.map (wstat gs)).filterMap wireOf = [] := by
    intro hall
    apply List.filterMap_eq_nil_iff.mpr
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨u, huin, rfl⟩ := hs
    rcases hall u huin with h | h
    · simp [wireOf, h, hw0]
    · simp [wireOf, h, hw9]
  have hall_of : (∀ u ∈ g.inputs, u = 0 ∨ u = 9) →
      ∀ s ∈ g.inputs.map (wstat gs), ∃ b', s = .const b' := by
    intro hall s hs
    rw [List.mem_map] at hs
    obtain ⟨u, huin, rfl⟩ := hs
    rcases hall u huin with h | h
    · exact ⟨false, by rw [h]; exact hw0⟩
    · exact ⟨true, by rw [h]; exact hw9⟩
  rcases hop with hop | hop | hop
  · -- AND
    by_cases h0in : 0 ∈ g.inputs
    · have hmem : .const false ∈ g.inputs.map (wstat gs) := by
        rw [List.mem_map]
        exact ⟨0, h0in, hw0.symm⟩
      have hf : (g.inputs.map (wstat gs)).any (· = .const false) = true := by
        rw [List.any_eq_true]
        exact ⟨.const false, hmem, rfl⟩
      exact ⟨false, by simp [gstep, combine, hop, hf]⟩
    · have h9in : 9 ∈ g.inputs := by
        rcases hsp with h | h
        · exact absurd h h0in
        · exact h
      have hall : ∀ u ∈ g.inputs, u = 9 := by
        intro u hu
        by_contra hu9
        have hu0 : u ≠ 0 := by
          intro hbad
          rw [hbad] at hu
          exact h0in hu
        apply hclean
        refine Or.inr ⟨hop, u, ?_, hu0, hu9⟩
        have hlen' := hlen
        cases hgi : g.inputs with
        | nil => simp [hgi] at hu
        | cons a rest =>
            cases rest with
            | nil =>
                have hua : u = a := by simpa [hgi] using hu
                have h9a : 9 = a := by simpa [hgi] using h9in
                exact absurd (h9a.trans hua.symm).symm hu9
            | cons c rest' =>
                have hrest : rest' = [] := by
                  cases rest' with
                  | nil => rfl
                  | cons d rest'' =>
                      simp only [hgi, List.length_cons] at hlen'
                      omega
                subst hrest
                have hu2 : u = a ∨ u = c := by simpa [hgi] using hu
                have h92 : 9 = a ∨ 9 = c := by simpa [hgi] using h9in
                rcases hu2 with rfl | rfl
                · rcases h92 with h | h
                  · exact absurd h.symm hu9
                  · exact Or.inr (by rw [← h])
                · rcases h92 with h | h
                  · exact Or.inl (by rw [← h])
                  · exact absurd h.symm hu9
      have hall09 : ∀ u ∈ g.inputs, u = 0 ∨ u = 9 :=
        fun u hu => Or.inr (hall u hu)
      have hf : (g.inputs.map (wstat gs)).any (· = .const false) = false := by
        rw [List.any_eq_false]
        intro s hs
        obtain ⟨b', hb'⟩ := hall_of hall09 s hs
        have hb9 : b' = true := by
          rw [List.mem_map] at hs
          obtain ⟨u, huin, hu2⟩ := hs
          have h9 : wstat gs 9 = .const b' := by
            rw [hall u huin] at hu2
            exact hu2.trans hb'
          rw [hw9] at h9
          exact (Status.const.inj h9).symm
        simp [hb', hb9]
      exact ⟨true, by simp [gstep, combine, hop, hf, hfilter_of hall09]⟩
  · -- OR
    by_cases h9in : 9 ∈ g.inputs
    · have hmem : .const true ∈ g.inputs.map (wstat gs) := by
        rw [List.mem_map]
        exact ⟨9, h9in, hw9.symm⟩
      have ht : (g.inputs.map (wstat gs)).any (· = .const true) = true := by
        rw [List.any_eq_true]
        exact ⟨.const true, hmem, rfl⟩
      exact ⟨true, by simp [gstep, combine, hop, ht]⟩
    · have h0in : 0 ∈ g.inputs := by
        rcases hsp with h | h
        · exact h
        · exact absurd h h9in
      have hall : ∀ u ∈ g.inputs, u = 0 := by
        intro u hu
        by_contra hu0
        have hu9 : u ≠ 9 := by
          intro hbad
          rw [hbad] at hu
          exact h9in hu
        apply hclean
        refine Or.inl ⟨hop, u, ?_, hu0, hu9⟩
        have hlen' := hlen
        cases hgi : g.inputs with
        | nil => simp [hgi] at hu
        | cons a rest =>
            cases rest with
            | nil =>
                have hua : u = a := by simpa [hgi] using hu
                have h0a : 0 = a := by simpa [hgi] using h0in
                exact absurd (h0a.trans hua.symm).symm hu0
            | cons c rest' =>
                have hrest : rest' = [] := by
                  cases rest' with
                  | nil => rfl
                  | cons d rest'' =>
                      simp only [hgi, List.length_cons] at hlen'
                      omega
                subst hrest
                have hu2 : u = a ∨ u = c := by simpa [hgi] using hu
                have h02 : 0 = a ∨ 0 = c := by simpa [hgi] using h0in
                rcases hu2 with rfl | rfl
                · rcases h02 with h | h
                  · exact absurd h.symm hu0
                  · exact Or.inr (by rw [← h])
                · rcases h02 with h | h
                  · exact Or.inl (by rw [← h])
                  · exact absurd h.symm hu0
      have hall09 : ∀ u ∈ g.inputs, u = 0 ∨ u = 9 :=
        fun u hu => Or.inl (hall u hu)
      have ht : (g.inputs.map (wstat gs)).any (· = .const true) = false := by
        rw [List.any_eq_false]
        intro s hs
        obtain ⟨b', hb'⟩ := hall_of hall09 s hs
        have hb0 : b' = false := by
          rw [List.mem_map] at hs
          obtain ⟨u, huin, hu2⟩ := hs
          have h0 : wstat gs 0 = .const b' := by
            rw [hall u huin] at hu2
            exact hu2.trans hb'
          rw [hw0] at h0
          exact (Status.const.inj h0).symm
        simp [hb', hb0]
      exact ⟨false, by simp [gstep, combine, hop, ht, hfilter_of hall09]⟩
  · -- NOT
    rcases hsp with h0 | h9
    · have hsing : g.inputs = [0] :=
        eq_singleton_of_mem_of_length_le_one h0 (hnot1 hop)
      have hss : g.inputs.map (wstat gs) = [.const false] := by
        rw [hsing]; simp [hw0]
      have hcomb : gstep gs ngn g = (.const true, none) := by
        simp [gstep, combine, hop, hss]
      exact ⟨true, congrArg Prod.fst hcomb⟩
    · have hsing : g.inputs = [9] :=
        eq_singleton_of_mem_of_length_le_one h9 (hnot1 hop)
      have hss : g.inputs.map (wstat gs) = [.const true] := by
        rw [hsing]; simp [hw9]
      have hcomb : gstep gs ngn g = (.const false, none) := by
        simp [gstep, combine, hop, hss]
      exact ⟨false, congrArg Prod.fst hcomb⟩

/-- The restriction input's wires agree with the initial statuses. -/
theorem restriction_hinv (y : Fin 8 → Bool) (i : ℕ) :
    (false :: List.ofFn y ++ [true]).getD i false
      = sval (wstat [] i) (List.ofFn y) := by
  by_cases h0 : i = 0
  · subst h0; rfl
  by_cases h9 : i = 9
  · subst h9
    have h9' : (false :: List.ofFn y ++ [true])[9]? = some true := by
      have e1 : (false :: List.ofFn y ++ [true])[9]?
          = (List.ofFn y ++ [true])[8]? := List.getElem?_cons_succ
      rw [e1, List.getElem?_append_right (by simp [List.length_ofFn])]
      simp
    show ((false :: List.ofFn y ++ [true])[9]?).getD false = true
    rw [h9']
    rfl
  by_cases h10 : i < 10
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi' : i' < 8 := by omega
    have hw : wstat [] (i' + 1) = .wire i' := by
      unfold wstat
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      have hsub : i' + 1 - 1 = i' := by omega
      rw [hsub]
    rw [hw]
    have e : (false :: List.ofFn y ++ [true])[i' + 1]?
        = (List.ofFn y)[i']? := by
      have e1 : (false :: List.ofFn y ++ [true])[i' + 1]?
          = (List.ofFn y ++ [true])[i']? := List.getElem?_cons_succ
      rw [e1, List.getElem?_append_left (by simp [List.length_ofFn]; exact hi')]
    show ((false :: List.ofFn y ++ [true])[i' + 1]?).getD false
      = (List.ofFn y).getD i' false
    rw [e]
    rfl
  · have hge : 10 ≤ i := by omega
    have hw : wstat [] i = .const false := by
      unfold wstat
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl
    rw [hw]
    have hnone : (false :: List.ofFn y ++ [true])[i]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      have hlen : (false :: List.ofFn y ++ [true]).length = 10 := by
        simp [List.length_ofFn]
      omega
    show ((false :: List.ofFn y ++ [true])[i]?).getD false = false
    rw [hnone]
    rfl

/-- The packaged simulation: the restriction of `C` computes `f`. -/
theorem sim_output (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (y : Fin 8 → Bool) :
    C.eval (false :: List.ofFn y ++ [true])
      = sval (statusOf C C.output) ((build C).2.foldl wstep (List.ofFn y)) := by
  obtain ⟨Δs, Δg, hΔ, hsim⟩ := sim_gen C.gates [] [] 0
    (false :: List.ofFn y ++ [true]) (List.ofFn y) rfl
    (by simp [List.length_ofFn]) (by simp [List.length_ofFn])
    (fun i => restriction_hinv y i) (by simp) hfan
  have hfst : (build C).1 = Δs := by
    have h2 : (build C).1 = [] ++ Δs := congrArg Prod.fst hΔ
    rwa [List.nil_append] at h2
  have hsnd : (build C).2 = Δg := by
    have h2 : (build C).2 = [] ++ Δg := congrArg Prod.snd hΔ
    rwa [List.nil_append] at h2
  have hst : statusOf C C.output = wstat Δs C.output := by
    show wstat (build C).1 C.output = wstat Δs C.output
    rw [hfst]
  rw [hsnd, hst]
  have hsim'' : (C.gates.foldl wstep (false :: List.ofFn y ++ [true])).getD
        C.output false
      = sval (wstat Δs C.output) (Δg.foldl wstep (List.ofFn y)) := by
    have h := hsim C.output
    rwa [List.nil_append] at h
  show (C.gates.foldl wstep (false :: List.ofFn y ++ [true])).getD C.output
      false
    = sval (wstat Δs C.output) (Δg.foldl wstep (List.ofFn y))
  exact hsim''

/-- The chain: a member of `S` with constant final status forces either a
skipped non-special gate (the surgery witness) or a constant output. -/
theorem chain (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hnot1 : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) :
    ∀ v, InS C v → ∀ b, statusOf C v = .const b →
      (∃ (k : ℕ) (h : Gate), C.gates[k]? = some h ∧ ¬ special h ∧
        (gstep (buildFrom [] [] 0 (C.gates.take k)).1
          ((buildFrom [] [] 0 (C.gates.take k)).2.length) h).2 = none)
      ∨ (∃ b', statusOf C C.output = .const b') := by
  intro v hv
  induction hv with
  | out =>
      intro b hst
      exact Or.inr ⟨b, hst⟩
  | nonspec hk hg =>
      rename_i k g
      intro b hst
      refine Or.inl ⟨k, g, hk, (not_special_iff g).mp hg, ?_⟩
      have h1 : statusOf C (10 + k)
          = (gstep (buildFrom [] [] 0 (C.gates.take k)).1
            ((buildFrom [] [] 0 (C.gates.take k)).2.length) g).1 :=
        statusOf_gate C hk
      rw [h1] at hst
      exact combine_snd_none_of_const g.op _ _ b hst
  | step hk hg hw h0 h9 ih =>
      rename_i k g w
      intro b hst
      have hgmem : g ∈ C.gates := List.mem_of_getElem? hk
      obtain ⟨b₀, hb₀⟩ : ∃ b₀, wstat (buildFrom [] [] 0 (C.gates.take k)).1 w
          = .const b₀ := by
        rcases statusOf_step_const C hk w b hst with h | h
        · exact ⟨b, h⟩
        · exact ⟨false, h⟩
      by_cases hsp : special g
      · obtain ⟨b', hb'⟩ := special_step_status_const
          (buildFrom [] [] 0 (C.gates.take k)).1
          ((buildFrom [] [] 0 (C.gates.take k)).2.length) g w b₀
          (hfan g hgmem) (hlen g hgmem) (hnot1 g hgmem) hsp hw h0 h9 hb₀
        have hgate : statusOf C (10 + k) = .const b' := by
          rw [statusOf_gate C hk]
          exact hb'
        exact ih b' hgate
      · refine Or.inl ⟨k, g, hk, hsp, ?_⟩
        exact nonspec_const_gstep_snd _ _ g (hlen g hgmem) (hfan g hgmem)
          (hnot1 g hgmem) ⟨w, hw, b₀, hb₀⟩

/-- Members of the closure are never the fixed wires, provided the output
is not one either. -/
theorem InS_ne (C : Circuit) (hC0 : C.output ≠ 0) (hC9 : C.output ≠ 9) :
    ∀ v, InS C v → v ≠ 0 ∧ v ≠ 9 := by
  intro v hv
  induction hv with
  | out => exact ⟨hC0, hC9⟩
  | nonspec hk hg => exact ⟨by omega, by omega⟩
  | step hk hg hw h0 h9 ih => exact ⟨h0, h9⟩

end PEqualNP.Outside.L_meta_4273

open PEqualNP.Outside.L_meta_4273 in
theorem PEqualNP.Outside.L_meta_4273 :
    ∀ (C : Circuit), FanInTwo C →
    (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
    12 + (C.gates.filter (fun g => [0,9].any g.inputs.contains)).length = C.size →
    let f := fun y : Fin 8 → Bool => C.eval (false :: List.ofFn y ++ [true])
    (∃ x y, f x ≠ f y) → ¬ HasCircuitSize 8 f 11 →
    ∃ S : Set ℕ, C.output ∈ S ∧ 0 ∉ S ∧ 9 ∉ S ∧
      ∀ (p : List Gate) (g : Gate) (t : List Gate), C.gates = p ++ g :: t →
        if [0,9].any g.inputs.contains then
          10+p.length ∈ S → ∃ k ∈ S,
            (g.op = .or ∧ (g.inputs = [0,k] ∨ g.inputs = [k,0])) ∨
            (g.op = .and ∧ (g.inputs = [9,k] ∨ g.inputs = [k,9]))
        else 10+p.length ∈ S ∧ ∀ k ∈ g.inputs, k ∈ S := by
  intro C hfan hnot1 hsize
  show (∃ x y, (fun y : Fin 8 → Bool =>
      C.eval (false :: List.ofFn y ++ [true])) x
      ≠ (fun y : Fin 8 → Bool => C.eval (false :: List.ofFn y ++ [true])) y)
    → ¬ HasCircuitSize 8
      (fun y : Fin 8 → Bool => C.eval (false :: List.ofFn y ++ [true])) 11
    → ∃ S : Set ℕ, C.output ∈ S ∧ 0 ∉ S ∧ 9 ∉ S ∧
      ∀ (p : List Gate) (g : Gate) (t : List Gate), C.gates = p ++ g :: t →
        if [0,9].any g.inputs.contains then
          10+p.length ∈ S → ∃ k ∈ S,
            (g.op = .or ∧ (g.inputs = [0,k] ∨ g.inputs = [k,0])) ∨
            (g.op = .and ∧ (g.inputs = [9,k] ∨ g.inputs = [k,9]))
        else 10+p.length ∈ S ∧ ∀ k ∈ g.inputs, k ∈ S
  intro hnc hhard
  obtain ⟨y₁, y₂, hne⟩ := hnc
  change C.eval (false :: List.ofFn y₁ ++ [true])
    ≠ C.eval (false :: List.ofFn y₂ ++ [true]) at hne
  have hfan' : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not :=
    fun g hg => by simpa using (hfan g hg).1
  have hlen_all : ∀ g ∈ C.gates, g.inputs.length ≤ 2 :=
    fun g hg => (hfan g hg).2
  have hskip_all : ∀ (gs : List Status) (ngn : ℕ) (g : Gate), g ∈ C.gates →
      special g → (gstep gs ngn g).2 = none :=
    fun gs ngn g hg hsp => special_gstep_snd gs ngn g hsp (hlen_all g hg)
      (hfan' g hg) (hnot1 g hg)
  have hC0 : C.output ≠ 0 := by
    intro hbad
    apply hne
    have e : ∀ y : Fin 8 → Bool, C.eval (false :: List.ofFn y ++ [true]) = false := by
      intro y
      show (C.wires (false :: List.ofFn y ++ [true])).getD C.output false
        = false
      rw [hbad]
      have hlt : (0 : ℕ) < (false :: List.ofFn y ++ [true]).length := by simp
      rw [wires_getD_of_lt C _ 0 hlt]
      rfl
    rw [e y₁, e y₂]
  have hC9 : C.output ≠ 9 := by
    intro hbad
    apply hne
    have e : ∀ y : Fin 8 → Bool, C.eval (false :: List.ofFn y ++ [true]) = true := by
      intro y
      show (C.wires (false :: List.ofFn y ++ [true])).getD C.output false
        = true
      rw [hbad]
      have hlt : (9 : ℕ) < (false :: List.ofFn y ++ [true]).length := by
        simp [List.length_ofFn]
      rw [wires_getD_of_lt C _ 9 hlt]
      exact restriction_hinv y 9
    rw [e y₁, e y₂]
  refine ⟨{v | InS C v}, InS.out, ?_, ?_, ?_⟩
  · intro h
    exact (InS_ne C hC0 hC9 0 h).1 rfl
  · intro h
    exact (InS_ne C hC0 hC9 9 h).2 rfl
  · intro p g t hdecomp
    have hk : C.gates[p.length]? = some g := getElem?_of_append hdecomp
    have hgmem : g ∈ C.gates := List.mem_of_getElem? hk
    by_cases hsp : ([0, 9].any g.inputs.contains) = true
    · rw [if_pos hsp]
      intro hmem
      have hsp' : special g := (special_iff g).mp hsp
      by_cases hcleanA :
          (g.op = .or ∧ ∃ w, (g.inputs = [0, w] ∨ g.inputs = [w, 0])
            ∧ w ≠ 0 ∧ w ≠ 9)
          ∨ (g.op = .and ∧ ∃ w, (g.inputs = [9, w] ∨ g.inputs = [w, 9])
            ∧ w ≠ 0 ∧ w ≠ 9)
      · rcases hcleanA with ⟨hopor, w, hform, hw0, hw9⟩
          | ⟨hopand, w, hform, hw0, hw9⟩
        · have hwin : w ∈ g.inputs := by
            rcases hform with h | h <;> simp [h]
          exact ⟨w, InS.step hk hmem hwin hw0 hw9, Or.inl ⟨hopor, hform⟩⟩
        · have hwin : w ∈ g.inputs := by
            rcases hform with h | h <;> simp [h]
          exact ⟨w, InS.step hk hmem hwin hw0 hw9, Or.inr ⟨hopand, hform⟩⟩
      · exfalso
        obtain ⟨b', hb'⟩ := dirty_status_const
          (buildFrom [] [] 0 (C.gates.take p.length)).1
          ((buildFrom [] [] 0 (C.gates.take p.length)).2.length) g
          (hfan' g hgmem) (hlen_all g hgmem) (hnot1 g hgmem) hsp' hcleanA
        have hgate : statusOf C (10 + p.length) = .const b' := by
          rw [statusOf_gate C hk]
          exact hb'
        rcases chain C hfan' hlen_all hnot1 (10 + p.length) hmem b' hgate with
          ⟨k', h', hk', hns', hskip'⟩ | ⟨b'', hb''⟩
        · have hdec' := gates_take_append C hk'
          have hskip_pieces : ∀ (gs : List Status) (ngn : ℕ) (g₀ : Gate),
              g₀ ∈ C.gates.take k' ++ h' :: C.gates.drop (k' + 1) →
              special g₀ → (gstep gs ngn g₀).2 = none :=
            fun gs ngn g₀ hg hsp₀ => hskip_all gs ngn g₀ (hdec'.symm ▸ hg) hsp₀
          have hcount := build_length_le_of_skip (C.gates.take k') h'
            (C.gates.drop (k' + 1)) hskip_pieces hskip' hns'
          rw [← hdec'] at hcount
          have hlen12 : (C.gates.filter
              (fun g => !([0, 9].any g.inputs.contains))).length = 12 := by
            have e := List.length_eq_length_filter_add
              (fun g => [0, 9].any g.inputs.contains) (l := C.gates)
            have e2 : (C.gates.filter
                (fun a => !(fun g => [0, 9].any g.inputs.contains) a)).length
              = (C.gates.filter
                (fun g => !([0, 9].any g.inputs.contains))).length := rfl
            have hsize' : C.size = C.gates.length := rfl
            omega
          have hle11 : (buildFrom [] [] 0 C.gates).2.length ≤ 11 := by omega
          by_cases hout : ∃ b, statusOf C C.output = .const b
          · obtain ⟨b, hb⟩ := hout
            have e : ∀ y : Fin 8 → Bool, C.eval (false :: List.ofFn y ++ [true]) = b := by
              intro y
              have h := sim_output C hfan' y
              rw [hb] at h
              exact h
            exact hne (by rw [e y₁, e y₂])
          · obtain ⟨k₀, hk₀⟩ : ∃ k₀, statusOf C C.output = .wire k₀ := by
              cases hst : statusOf C C.output with
              | const b => exact absurd ⟨b, hst⟩ hout
              | wire k₀ => exact ⟨k₀, rfl⟩
            refine hhard ⟨⟨(build C).2, k₀⟩, ?_, ?_, ?_⟩
            · intro g' hg'
              have hg'' : g' ∈ (buildFrom [] [] 0 C.gates).2 := hg'
              rcases buildFrom_mem_snd C.gates [] [] 0 g' hg'' with
                h | ⟨g₀, hg₀, gs', ngn', hstep⟩
              · simp at h
              · obtain ⟨h1, h2⟩ := gstep_some_fanin gs' ngn' g₀ g' hstep
                refine ⟨?_, le_trans h2 (hlen_all g₀ hg₀)⟩
                rw [h1]
                exact (hfan g₀ hg₀).1
            · exact hle11
            · intro x
              show (⟨(build C).2, k₀⟩ : Circuit).eval (List.ofFn x)
                = C.eval (false :: List.ofFn x ++ [true])
              have h := sim_output C hfan' x
              rw [hk₀] at h
              rw [h]
              show ((build C).2.foldl wstep (List.ofFn x)).getD k₀ false
                = sval (Status.wire k₀) ((build C).2.foldl wstep (List.ofFn x))
              rfl
        · have e : ∀ y : Fin 8 → Bool, C.eval (false :: List.ofFn y ++ [true]) = b'' := by
            intro y
            have h := sim_output C hfan' y
            rw [hb''] at h
            exact h
          exact hne (by rw [e y₁, e y₂])
    · have hfalse : ([0, 9].any g.inputs.contains) = false :=
        bool_eq_false_of_not_eq_true hsp
      rw [if_neg hsp]
      have hns : ¬ special g := (not_special_iff g).mp hfalse
      refine ⟨InS.nonspec hk hfalse, fun j hj => ?_⟩
      have hj0 : j ≠ 0 := by
        intro hbad
        apply hns
        rw [hbad] at hj
        exact Or.inl hj
      have hj9 : j ≠ 9 := by
        intro hbad
        apply hns
        rw [hbad] at hj
        exact Or.inr hj
      exact InS.step hk (InS.nonspec hk hfalse) hj hj0 hj9
