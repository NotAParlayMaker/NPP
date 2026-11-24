import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3684

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresOf C.gates x := rfl

lemma wiresOf_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresOf (g :: gs) x =
      wiresOf gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    rw [wiresOf_cons]
    rw [ih]
    simp
    omega

lemma wiresOf_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresOf_cons]
    rw [ih _ (by simp; omega)]
    exact List.getD_append x _ false i hi

lemma wiresOf_append (gs gs' : List Gate) (x : List Bool) :
    wiresOf (gs ++ gs') x = wiresOf gs' (wiresOf gs x) := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    rw [List.cons_append, wiresOf_cons, ih, wiresOf_cons]

lemma wiresOf_singleton (g : Gate) (x : List Bool) :
    wiresOf [g] x = x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)] := by
  simp [wiresOf]

lemma gate_at (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresOf gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresOf (gs.take j) x).getD i false) := by
  have htake : (gs.take j).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlen : (wiresOf (gs.take j) x).length = x.length + j := by
    rw [wiresOf_length, htake]
  have happ : gs = (gs.take j ++ [gs[j]]) ++ gs.drop (j + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  conv_lhs => rw [happ]
  rw [wiresOf_append]
  have hi : x.length + j < (wiresOf (gs.take j ++ [gs[j]]) x).length := by
    rw [wiresOf_length, List.length_append, List.length_singleton, htake]
    omega
  rw [wiresOf_input _ _ _ hi, wiresOf_append, wiresOf_singleton]
  simp [hlen]

lemma replicate_getD_false (n i : ℕ) :
    (List.replicate n false).getD i false = false := by
  cases Nat.lt_or_ge i n with
  | inl hi =>
    rw [List.getD_eq_getElem (List.replicate n false) false (by simpa [List.length_replicate] using hi)]
    simp
  | inr hi =>
    exact List.getD_eq_default _ _ (by simp [List.length_replicate]; omega)

lemma ofFn_getD {m : ℕ} (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
  cases Nat.lt_or_ge i m with
  | inl h =>
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    simp [h]
  | inr h =>
    rw [List.getD_eq_default _ _ (by simp; omega)]
    have : ¬ i < m := by omega
    simp [this]

lemma op_and_or (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg

lemma and_map_mono (idxs : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false = true → wb.getD i false = true) :
    ((idxs.map fun i => wa.getD i false).all id = true) →
      (idxs.map fun i => wb.getD i false).all id = true := by
  intro h
  rw [List.all_eq_true] at h ⊢
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hwa : wa.getD i false = true := by
    simpa using h (wa.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  simpa using hle i hwa

lemma or_map_mono (idxs : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false = true → wb.getD i false = true) :
    ((idxs.map fun i => wa.getD i false).any id = true) →
      (idxs.map fun i => wb.getD i false).any id = true := by
  intro h
  rw [List.any_eq_true] at h ⊢
  obtain ⟨b, hb, hbtrue⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  refine ⟨wb.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
  simpa using hle i (by simpa using hbtrue)

lemma step_getD (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (wa wb : List Bool) (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false = true → wb.getD i false = true) (i : ℕ)
    (hi : (wa ++ [g.op.eval (g.inputs.map fun k => wa.getD k false)]).getD i false = true) :
    (wb ++ [g.op.eval (g.inputs.map fun k => wb.getD k false)]).getD i false = true := by
  by_cases hlt : i < wa.length
  · rw [List.getD_append wa _ false i hlt] at hi
    rw [List.getD_append wb _ false i (by omega)]
    exact hle i hi
  · have hge : wa.length ≤ i := by omega
    have heq : i = wa.length := by
      by_contra hne
      have hgt : wa.length + 1 ≤ i := by omega
      rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      cases hi
    subst heq
    have hlast (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by simp
    rw [hlast] at hi
    rw [hlen, hlast]
    rcases hop with hop | hop
    · rw [hop] at hi ⊢
      exact and_map_mono g.inputs wa wb hle hi
    · rw [hop] at hi ⊢
      exact or_map_mono g.inputs wa wb hle hi

lemma wires_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresOf gs x).getD i false = true → (wiresOf gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil =>
    intro i hi
    simp only [wiresOf, List.foldl_nil] at hi
    exact hle i hi
  | cons g gs ih =>
    intro i hi
    rw [wiresOf_cons] at hi
    have hstep := step_getD g (hgs g List.mem_cons_self) x y hlen hle
    have := ih (fun g' hg => hgs g' (List.mem_cons_of_mem _ hg))
      (x ++ [g.op.eval (g.inputs.map fun k => x.getD k false)])
      (y ++ [g.op.eval (g.inputs.map fun k => y.getD k false)])
      (by simp [hlen]) hstep i hi
    simpa [wiresOf_cons] using this

lemma eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  rw [Circuit.eval, wires_eq, wiresOf_input _ _ _ h]

lemma prefix_off (gs : List Gate) (x y : List Bool) (flip : ℕ)
    (hlen : x.length = y.length) (hoff : ∀ i, i ≠ flip → x.getD i false = y.getD i false)
    (hgate : ∀ k, k < gs.length →
      (wiresOf gs x).getD (x.length + k) false = (wiresOf gs y).getD (y.length + k) false) :
    ∀ i, i ≠ flip → (wiresOf gs x).getD i false = (wiresOf gs y).getD i false := by
  intro i hine
  by_cases hi : i < x.length
  · rw [wiresOf_input _ _ _ hi, wiresOf_input _ _ _ (by omega)]
    exact hoff i hine
  · by_cases hk : i < x.length + gs.length
    · have hk' : i - x.length < gs.length := by omega
      have hie : i = x.length + (i - x.length) := by omega
      rw [hie]
      simpa [hlen] using hgate (i - x.length) hk'
    · rw [List.getD_eq_default _ _ (by rw [wiresOf_length]; omega),
        List.getD_eq_default _ _ (by rw [wiresOf_length, ← hlen]; omega)]

lemma card_hit (n : ℕ) (idxs : List ℕ) :
    (Finset.univ.filter fun l : Fin n => n + l.val ∈ idxs).card ≤ idxs.length := by
  induction idxs with
  | nil => simp
  | cons a idxs ih =>
    have hsplit : Finset.univ.filter (fun l : Fin n => n + l.val = a ∨ n + l.val ∈ idxs) ⊆
        (Finset.univ.filter fun l : Fin n => n + l.val = a) ∪
          (Finset.univ.filter fun l : Fin n => n + l.val ∈ idxs) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hl ⊢
      exact hl
    have hone : (Finset.univ.filter fun l : Fin n => n + l.val = a).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact Fin.ext (by omega)
    have hlen : (a :: idxs).length = idxs.length + 1 := by simp
    calc (Finset.univ.filter fun l : Fin n => n + l.val ∈ a :: idxs).card
        = (Finset.univ.filter fun l : Fin n => n + l.val = a ∨ n + l.val ∈ idxs).card := by
          simp [List.mem_cons]
      _ ≤ ((Finset.univ.filter fun l : Fin n => n + l.val = a) ∪
            (Finset.univ.filter fun l : Fin n => n + l.val ∈ idxs)).card :=
          Finset.card_le_card hsplit
      _ ≤ (Finset.univ.filter fun l : Fin n => n + l.val = a).card +
            (Finset.univ.filter fun l : Fin n => n + l.val ∈ idxs).card :=
          Finset.card_union_le _ _
      _ ≤ idxs.length + 1 := by omega
      _ = (a :: idxs).length := by simp

lemma bound (n : ℕ) (C D : Circuit) (houtput : C.output = D.output) (hmono : Monotone2 C)
    (hleft : C.eval (List.ofFn fun i : Fin (n + n) =>
      Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) i) = false)
    (S : Fin n → Finset (Fin n))
    (hpairs : ∀ (l p : Fin n), p ∈ S l →
      C.eval (List.ofFn (pairInput (Fin.castAdd n p) (Fin.natAdd n l))) = true ∧
      D.eval (List.ofFn (pairInput (Fin.castAdd n p) (Fin.natAdd n l))) = false) :
    Fintype.card {l : Fin n // (S l).Nonempty} ≤
      2 * Fintype.card {j : Fin C.size //
        (C.wires (List.replicate (n + n) false)).getD (n + n + ↑j) false = false ∧
          ∃ l : Fin n, ∃ p ∈ S l, gateVal (n + n) C ↑j
            (pairInput (Fin.castAdd n p) (Fin.natAdd n l)) = true} := by
  classical
  let m := n + n
  let allL : Fin m → Bool := fun i => Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) i
  let oneL (p : Fin n) : Fin m → Bool := fun w => decide (w = Fin.castAdd n p)
  let pairL (p l : Fin n) : Fin m → Bool := pairInput (Fin.castAdd n p) (Fin.natAdd n l)
  have hCmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => op_and_or g (hmono g hg).1
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hmono g hg).2
  rw [Fintype.card_subtype, Fintype.card_subtype]
  let Active : Finset (Fin n) := Finset.univ.filter fun l => (S l).Nonempty
  let Gates : Finset (Fin C.size) := Finset.univ.filter fun j =>
    (C.wires (List.replicate m false)).getD (m + ↑j) false = false ∧
      ∃ l : Fin n, ∃ p ∈ S l, gateVal m C ↑j (pairL p l) = true
  change Active.card ≤ 2 * Gates.card
  have hone_all : ∀ p i, (List.ofFn (oneL p)).getD i false = true →
      (List.ofFn allL).getD i false = true := by
    intro p i hi
    rw [ofFn_getD] at hi ⊢
    by_cases h : i < m
    · simp only [h, dite_true] at hi ⊢
      simp only [oneL, decide_eq_true_eq] at hi
      have hval : i < n := by
        have heq : i = p.val := by simpa using congrArg Fin.val hi
        omega
      simp [allL, Fin.addCases, hval]
    · simp [h] at hi
  have hone_pair : ∀ p l i, (List.ofFn (oneL p)).getD i false = true →
      (List.ofFn (pairL p l)).getD i false = true := by
    intro p l i hi
    rw [ofFn_getD] at hi ⊢
    by_cases h : i < m
    · simp only [h, dite_true] at hi ⊢
      simp only [oneL, decide_eq_true_eq] at hi
      simp [pairL, pairInput, hi]
    · simp [h] at hi
  have hfalse_one : ∀ p, C.eval (List.ofFn (oneL p)) = false := by
    intro p
    have hup := wires_mono C.gates hCmono (List.ofFn (oneL p)) (List.ofFn allL) (by simp [m]) (hone_all p)
    rw [← wires_eq, ← wires_eq] at hup
    by_contra ht
    have ht' : (C.wires (List.ofFn (oneL p))).getD C.output false = true := by
      simpa [Circuit.eval] using ht
    have := hup C.output ht'
    have hf : (C.wires (List.ofFn allL)).getD C.output false = false := by
      simpa [Circuit.eval] using hleft
    rw [this] at hf
    cases hf
  have pick : ∀ l : Fin n, (S l).Nonempty → ∃ j : Fin C.size,
      j ∈ Gates ∧ n + l.val ∈ (C.gates[j.1]).inputs := by
    intro l hl
    let p : Fin n := hl.choose
    have hp : p ∈ S l := hl.choose_spec
    have hx : C.eval (List.ofFn (pairL p l)) = true := (hpairs l p hp).1
    have hd : D.eval (List.ofFn (pairL p l)) = false := (hpairs l p hp).2
    have hy : C.eval (List.ofFn (oneL p)) = false := hfalse_one p
    let x := List.ofFn (pairL p l)
    let y := List.ofFn (oneL p)
    have hxm : x.length = m := by simp [x, m]
    have hym : y.length = m := by simp [y, m]
    have hout_ge : m ≤ C.output := by
      by_contra hlt
      have hlt' : C.output < m := by omega
      have eC := eval_input C x (by simpa [x, m] using hlt')
      have eD := eval_input D x (by
        have hDo : D.output < m := by rw [← houtput]; exact hlt'
        simpa [x, m] using hDo)
      have : C.eval x = D.eval x := by rw [eC, eD, houtput]
      rw [hx, hd] at this
      cases this
    have hout_lt : C.output < m + C.gates.length := by
      by_contra hge
      have hfalse : C.eval x = false := by
        rw [Circuit.eval, wires_eq]
        exact List.getD_eq_default _ _ (by rw [wiresOf_length, hxm]; omega)
      rw [hx] at hfalse
      cases hfalse
    let j0 := C.output - m
    have hj0 : j0 < C.gates.length := by omega
    have hj0x : (C.wires x).getD (m + j0) false = true := by
      have : C.output = m + j0 := by omega
      simpa [Circuit.eval, this] using hx
    have hj0y : (C.wires y).getD (m + j0) false = false := by
      have : C.output = m + j0 := by omega
      simpa [Circuit.eval, this] using hy
    let P : ℕ → Prop := fun j => j < C.gates.length ∧
      (C.wires y).getD (m + j) false = false ∧ (C.wires x).getD (m + j) false = true
    have hex : ∃ j, P j := ⟨j0, hj0, hj0y, hj0x⟩
    have : DecidablePred P := fun _ => inferInstance
    let j := Nat.find hex
    have hjP : P j := Nat.find_spec hex
    have hmin : ∀ k < j, ¬ P k := fun k hk => Nat.find_min hex hk
    have hjlt : j < C.gates.length := hjP.1
    have hyx : ∀ i, y.getD i false = true → x.getD i false = true := hone_pair p l
    have hpre : ∀ k < j, (C.wires y).getD (m + k) false = (C.wires x).getD (m + k) false := by
      intro k hk
      have hklt : k < C.gates.length := by omega
      have hnot := hmin k hk
      simp only [P, hklt, true_and, not_and] at hnot
      have hup := wires_mono C.gates hCmono y x (by simp [hym, hxm]) hyx
      rw [← wires_eq, ← wires_eq] at hup
      cases hyv : (C.wires y).getD (m + k) false
      · have hxf : (C.wires x).getD (m + k) false = false := by
          by_contra hxtrue
          have hxt : (C.wires x).getD (m + k) false = true := by
            cases h : (C.wires x).getD (m + k) false <;> simp_all
          exact hnot (by rw [hyv]) hxt
        exact hxf.symm
      · exact (hup (m + k) hyv).symm
    have hstab (z : List Bool) (hz : z.length = m) (k : ℕ) (hk : k < j) :
        (wiresOf (C.gates.take j) z).getD (m + k) false = (C.wires z).getD (m + k) false := by
      have hs : wiresOf C.gates z = wiresOf (C.gates.take j ++ C.gates.drop j) z := by
        simp [List.take_append_drop]
      rw [wires_eq, hs, wiresOf_append]
      symm
      apply wiresOf_input
      rw [wiresOf_length, List.length_take, Nat.min_eq_left (by omega), hz]
      omega
    have hflip_ne : ∀ i, i ≠ n + l.val →
        (wiresOf (C.gates.take j) y).getD i false = (wiresOf (C.gates.take j) x).getD i false := by
      refine prefix_off (C.gates.take j) y x (n + l.val) (by simp [hym, hxm]) ?_ ?_
      · intro i hine
        rw [ofFn_getD, ofFn_getD]
        by_cases h : i < m
        · simp only [h, dite_true]
          have hneR' : (⟨i, by simpa [m] using h⟩ : Fin m) ≠ l.addNat n := by
            intro heq
            apply hine
            have hv := congrArg Fin.val heq
            rw [Fin.val_addNat] at hv
            rw [Nat.add_comm] at hv
            exact hv
          by_cases hL : (⟨i, by simpa [m] using h⟩ : Fin m) = Fin.castAdd n p
          · simp [oneL, pairL, pairInput, hL, hneR']
          · simp [oneL, pairL, pairInput, hL, hneR']
        · simp [h]
      · intro k hk
        have hk' : k < j := by
          rw [List.length_take, Nat.min_eq_left (by omega)] at hk
          exact hk
        have hyk := hstab y hym k hk'
        have hxk := hstab x hxm k hk'
        rw [hym, hxm, hyk, hxk]
        exact hpre k hk'
    have hreads : n + l.val ∈ (C.gates[j]).inputs := by
      by_contra hnot
      have hin : ((C.gates[j]).inputs.map fun i => (wiresOf (C.gates.take j) y).getD i false) =
          (C.gates[j]).inputs.map fun i => (wiresOf (C.gates.take j) x).getD i false := by
        apply List.map_congr_left
        intro i hi
        exact hflip_ne i (fun heq => hnot (by simpa [heq] using hi))
      have hyg := gate_at C.gates y j hjlt
      have hxg := gate_at C.gates x j hjlt
      rw [← wires_eq] at hyg hxg
      rw [hym] at hyg
      rw [hxm] at hxg
      have : (C.wires y).getD (m + j) false = (C.wires x).getD (m + j) false := by
        rw [hyg, hxg, hin]
      rw [hjP.2.1, hjP.2.2] at this
      cases this
    have hfalse0 : (C.wires (List.replicate m false)).getD (m + j) false = false := by
      have hup := wires_mono C.gates hCmono (List.replicate m false) y
        (by simp [hym, m]) (fun i hi => by rw [replicate_getD_false] at hi; cases hi)
      rw [← wires_eq, ← wires_eq] at hup
      cases h0 : (C.wires (List.replicate m false)).getD (m + j) false
      · rfl
      · have := hup (m + j) h0
        rw [hjP.2.1] at this
        cases this
    refine ⟨⟨j, hjlt⟩, ?_, hreads⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hfalse0, l, p, hp, ?_⟩
    simpa [gateVal, x, pairL] using hjP.2.2
  by_cases hAct : Active = ∅
  · simp [hAct]
  · have hne : ∃ l, l ∈ Active := by
      simpa [Finset.eq_empty_iff_forall_notMem] using hAct
    let φ : Fin n → Fin C.size := fun l =>
      if h : (S l).Nonempty then (pick l h).choose else
        (pick hne.choose (by
          have := hne.choose_spec
          simpa [Active] using this)).choose
    have hφ : ∀ l ∈ Active, φ l ∈ Gates ∧ n + l.val ∈ (C.gates[φ l]).inputs := by
      intro l hl
      have hS : (S l).Nonempty := by simpa [Active] using hl
      have := (pick l hS).choose_spec
      simpa [φ, hS] using this
    have hmaps : (Active : Set (Fin n)).MapsTo φ Gates := fun l hl => (hφ l hl).1
    have hsplit := Finset.card_eq_sum_card_fiberwise (f := φ) (s := Active) (t := Gates) hmaps
    have hfiber : ∀ j ∈ Gates, (Active.filter fun l => φ l = j).card ≤ 2 := by
      intro j hj
      have hsub : (Active.filter fun l => φ l = j) ⊆
          Finset.univ.filter fun l : Fin n => n + l.val ∈ (C.gates[j]).inputs := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
        have hmem := (hφ l hl.1).2
        simpa [hl.2] using hmem
      have hlen := hfan (C.gates[j]) (List.getElem_mem (by exact j.isLt))
      calc (Active.filter fun l => φ l = j).card
          ≤ (Finset.univ.filter fun l : Fin n => n + l.val ∈ (C.gates[j]).inputs).card :=
            Finset.card_le_card hsub
        _ ≤ (C.gates[j]).inputs.length := card_hit n _
        _ ≤ 2 := hlen
    calc Active.card = ∑ j ∈ Gates, (Active.filter fun l => φ l = j).card := hsplit
      _ ≤ ∑ j ∈ Gates, 2 := Finset.sum_le_sum hfiber
      _ = Gates.card * 2 := by simp [Finset.sum_const]
      _ = 2 * Gates.card := Nat.mul_comm _ _

end PEqualNP.Outside.L_meta_3684

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3684

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_3684 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x2.output = x3.output →     PEqualNP.MetaComplexity.Monotone2 x2 →       x2.eval (List.ofFn fun (x6 : Fin (x1 + x1)) => Fin.addCases (fun (x7 : Fin x1) => Bool.true) (fun (x7 : Fin x1) => Bool.false) x6) = Bool.false →         have x7 : Fin x1 → Fin x1 → Fin (x1 + x1) → Bool := fun (x7 x8 : Fin x1) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x1 x7) (Fin.natAdd x1 x8);         ∀ (x8 : Fin x1 → Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x10 ∈ x8 x9 → x2.eval (List.ofFn (x7 x10 x9)) = Bool.true ∧ x3.eval (List.ofFn (x7 x10 x9)) = Bool.false) → Fintype.card { x10 : Fin x1 // (x8 x10).Nonempty } ≤ (2 : ℕ) * Fintype.card { x10 : Fin x2.size // (x2.wires (List.replicate (x1 + x1) Bool.false)).getD (x1 + x1 + ↑x10) Bool.false = Bool.false ∧ ∃ (x11 : Fin x1), ∃ x12 ∈ x8 x11, PEqualNP.EdgeOwnership.gateVal (x1 + x1) x2 (↑x10) (x7 x12 x11) = Bool.true } := by
  dsimp only
  intro n C D houtput hmono hleft S hpairs
  simpa using bound n C D houtput hmono hleft S hpairs

