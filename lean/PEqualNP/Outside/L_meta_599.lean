import Mathlib
import PEqualNP.Defs

namespace LMeta599

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

lemma eval_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true)
    (hx : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true :=
  wires_mono C hmono x y hxy C.output hx

lemma find_or_gate_avoid (n : ℕ) (C : Circuit) (a : Fin n) (bad : Option ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x : Fin n → Bool)
    (hflip : C.eval (List.ofFn x) = false ∧ C.eval (List.ofFn (Function.update x a true)) = true)
    (hbad : ∀ j0, bad = some j0 →
      (C.wires (List.ofFn x)).getD (n + j0) false =
      (C.wires (List.ofFn (Function.update x a true))).getD (n + j0) false)
    (y : Fin n → Bool) (hya : y a = false) (hyt : C.eval (List.ofFn y) = true) :
    ∃ (j : ℕ) (g : Gate) (i : ℕ),
      C.gates[j]? = some g ∧ g.op = GateOp.or ∧ (some j ≠ bad) ∧
      i ∈ g.inputs ∧ i < n + j ∧
      ∀ z : Fin n → Bool, z a = false → (C.wires (List.ofFn z)).getD i false = false := by
  by_contra hno
  have hmain : ∀ w : ℕ,
      ((C.wires (List.ofFn x)).getD w false ≠
        (C.wires (List.ofFn (Function.update x a true))).getD w false) →
      ∀ z : Fin n → Bool, z a = false → (C.wires (List.ofFn z)).getD w false = false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hne z hza
      by_cases hw1 : w < n
      · rw [wires_input C x w hw1, wires_input C (Function.update x a true) w hw1] at hne
        rw [wires_input C z w hw1]
        by_cases hwa : (⟨w, hw1⟩ : Fin n) = a
        · rw [hwa, hza]
        · rw [Function.update_of_ne hwa] at hne
          exact absurd rfl hne
      · by_cases hw2 : n + C.gates.length ≤ w
        · rw [wires_oob C x w hw2, wires_oob C (Function.update x a true) w hw2] at hne
          exact absurd rfl hne
        · have hjlt : w - n < C.gates.length := by omega
          set j := w - n
          have hwj : w = n + j := by omega
          by_cases hjb : some j = bad
          · rw [hwj] at hne
            exact absurd (hbad j hjb.symm) hne
          · set g := C.gates[j]'hjlt
            have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
            have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
              simpa using (hmono g (List.mem_of_getElem? hg)).1
            have hgx : (C.wires (List.ofFn x)).getD w false =
                g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
              rw [hwj]; exact wires_gate_ofFn C x j g hg
            have hgx' : (C.wires (List.ofFn (Function.update x a true))).getD w false =
                g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn (Function.update x a true))).getD i false else false) := by
              rw [hwj]; exact wires_gate_ofFn C (Function.update x a true) j g hg
            have hgz : (C.wires (List.ofFn z)).getD w false =
                g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn z)).getD i false else false) := by
              rw [hwj]; exact wires_gate_ofFn C z j g hg
            rw [hgx, hgx'] at hne
            have hex : ∃ i ∈ g.inputs,
                (if i < n + j then (C.wires (List.ofFn x)).getD i false else false) ≠
                (if i < n + j then (C.wires (List.ofFn (Function.update x a true))).getD i false else false) := by
              by_contra hall
              apply hne
              congr 1
              apply List.map_congr_left
              intro i hi
              by_contra hnei
              exact hall ⟨i, hi, hnei⟩
            obtain ⟨i, hi_mem, hi_ne⟩ := hex
            have hi_lt : i < n + j := by
              by_contra hge
              simp only [hge, ↓reduceIte] at hi_ne
              exact hi_ne rfl
            simp only [hi_lt, ↓reduceIte] at hi_ne
            have hZi := ih i (by omega) hi_ne
            rcases hgop with hand | hor
            · rw [hgz, hand]
              change (g.inputs.map fun k => if k < n + j then (C.wires (List.ofFn z)).getD k false else false).all id = false
              cases hval : (g.inputs.map fun k => if k < n + j then (C.wires (List.ofFn z)).getD k false else false).all id with
              | false => rfl
              | true =>
                have htrue := List.all_eq_true.mp hval
                have hres := htrue _ (List.mem_map_of_mem hi_mem)
                simp only [id_eq, hi_lt, ↓reduceIte, hZi z hza] at hres
                exact absurd hres (by decide)
            · exact absurd ⟨j, g, i, hg, hor, hjb, hi_mem, hi_lt, hZi⟩ hno
  have hzero := hmain C.output (by
    change C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x a true))
    rw [hflip.1, hflip.2]
    decide) y hya
  change C.eval (List.ofFn y) = false at hzero
  rw [hyt] at hzero
  exact absurd hzero (by decide)

lemma set_gate_mono_struct (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (j0 : ℕ) (g' : Gate) (hgop : g'.op = GateOp.and) (hglen : g'.inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.Monotone2 ⟨C.gates.set j0 g', C.output⟩ := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  by_cases hkj : k = j0
  · subst hkj
    rw [List.getElem_set_self]
    exact ⟨by simp [hgop], hglen⟩
  · rw [List.getElem_set_ne (Ne.symm hkj)]
    exact hmono _ (List.getElem_mem (by simpa using hk))

lemma set_gate_or_subset (C : Circuit) (A : Finset ℕ)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A)
    (j0 : ℕ) (g' : Gate) (hgop : g'.op = GateOp.and) :
    ∀ (j : ℕ) (g : Gate), (C.gates.set j0 g')[j]? = some g → g.op = GateOp.or → j ∈ A.erase j0 := by
  intro j g hj hor
  by_cases hjj : j = j0
  · subst hjj
    by_cases hlt : j < C.gates.length
    · rw [List.getElem?_set_self hlt, Option.some.injEq] at hj
      subst hj
      rw [hgop] at hor
      cases hor
    · rw [List.getElem?_eq_none (by simp; omega)] at hj
      cases hj
  · rw [List.getElem?_set_ne (Ne.symm hjj)] at hj
    exact Finset.mem_erase.mpr ⟨hjj, hA j g hj hor⟩

lemma set_gate_le {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (j0 : ℕ) (hj0 : j0 < C.gates.length) (g' : Gate)
    (hgop : g'.op = GateOp.and)
    (x : Fin n → Bool)
    (hle0 : g'.op.eval (g'.inputs.map fun i => if i < n + j0 then (C.wires (List.ofFn x)).getD i false else false) = true →
      (C.wires (List.ofFn x)).getD (n + j0) false = true) :
    ∀ w : ℕ, ((Circuit.mk (C.gates.set j0 g') C.output).wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn x)).getD w false = true := by
  set C' : Circuit := ⟨C.gates.set j0 g', C.output⟩
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C' x w hw1, wires_input C x w hw1]
      exact id
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C' x w (by simp [C', hw2])]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        by_cases hjj : j = j0
        · subst hjj
          have hg' : C'.gates[j]? = some g' := List.getElem?_set_self hj0
          rw [hwj, wires_gate_ofFn C' x j g' hg']
          intro ht
          apply hle0
          exact gateOp_mono g'.op (Or.inl hgop) g'.inputs
            (fun i => if i < n + j then (C'.wires (List.ofFn x)).getD i false else false)
            (fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false)
            (fun i _ hi => by
              by_cases hilt : i < n + j
              · simp only [hilt, ↓reduceIte] at hi ⊢
                exact ih i (by omega) hi
              · simp only [hilt, ↓reduceIte] at hi
                exact absurd hi (by decide))
            ht
        · have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
          have hg' : C'.gates[j]? = some (C.gates[j]'hjlt) := by
            show (C.gates.set j0 g')[j]? = some (C.gates[j]'hjlt)
            rw [List.getElem?_set_ne (Ne.symm hjj)]
            exact hg
          have hgopj : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
            simpa using (hmono _ (List.mem_of_getElem? hg)).1
          rw [hwj, wires_gate_ofFn C' x j _ hg', wires_gate_ofFn C x j _ hg]
          apply gateOp_mono _ hgopj
          intro i _ hi
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte] at hi ⊢
            exact ih i (by omega) hi
          · simp only [hilt, ↓reduceIte] at hi
            exact absurd hi (by decide)

lemma set_gate_eq {n : ℕ} (C : Circuit) (j0 : ℕ) (hj0 : j0 < C.gates.length) (g' : Gate)
    (x : Fin n → Bool)
    (heq0 : g'.op.eval (g'.inputs.map fun i => if i < n + j0 then (C.wires (List.ofFn x)).getD i false else false) =
      (C.wires (List.ofFn x)).getD (n + j0) false) :
    ∀ w : ℕ, ((Circuit.mk (C.gates.set j0 g') C.output).wires (List.ofFn x)).getD w false =
      (C.wires (List.ofFn x)).getD w false := by
  set C' : Circuit := ⟨C.gates.set j0 g', C.output⟩
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C' x w hw1, wires_input C x w hw1]
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C' x w (by simp [C', hw2]), wires_oob C x w hw2]
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        by_cases hjj : j = j0
        · subst hjj
          have hg' : C'.gates[j]? = some g' := List.getElem?_set_self hj0
          rw [hwj, wires_gate_ofFn C' x j g' hg', ← heq0]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte]
            exact ih i (by omega)
          · simp only [hilt, ↓reduceIte]
        · have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
          have hg' : C'.gates[j]? = some (C.gates[j]'hjlt) := by
            show (C.gates.set j0 g')[j]? = some (C.gates[j]'hjlt)
            rw [List.getElem?_set_ne (Ne.symm hjj)]
            exact hg
          rw [hwj, wires_gate_ofFn C' x j _ hg', wires_gate_ofFn C x j _ hg]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hilt : i < n + j
          · simp only [hilt, ↓reduceIte]
            exact ih i (by omega)
          · simp only [hilt, ↓reduceIte]

def rfGate {n : ℕ} (C : Circuit) (a : Fin n) (K : Finset ℕ) (ki : ℕ → ℕ)
    (j : Fin C.gates.length) : Gate :=
  let g := C.gates[j.val]
  let rep : ℕ → ℕ := fun k => if k = a.val then n + j.val else k
  if j.val ∈ K then
    match g.inputs.filter (fun k => k != ki j.val) with
    | [] => ⟨GateOp.and, [n + j.val]⟩
    | k :: _ => ⟨GateOp.and, [rep k]⟩
  else
    ⟨g.op, g.inputs.map rep⟩

def rfCircuit {n : ℕ} (C : Circuit) (a : Fin n) (K : Finset ℕ) (ki : ℕ → ℕ) : Circuit :=
  ⟨List.ofFn (rfGate C a K ki), if C.output = a.val then n + C.gates.length else C.output⟩

lemma rfCircuit_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (a : Fin n) (K : Finset ℕ) (ki : ℕ → ℕ) :
    PEqualNP.MetaComplexity.Monotone2 (rfCircuit C a K ki) := by
  intro g' hg'
  simp only [rfCircuit, List.mem_ofFn] at hg'
  obtain ⟨j, rfl⟩ := hg'
  unfold rfGate
  by_cases hjK : j.val ∈ K
  · simp only [hjK, ↓reduceIte]
    cases (C.gates[j.val]).inputs.filter (fun k => k != ki j.val) with
    | nil => exact ⟨by simp, by simp⟩
    | cons k ks => exact ⟨by simp, by simp⟩
  · simp only [hjK, ↓reduceIte]
    have hg := hmono (C.gates[j.val]) (List.getElem_mem j.isLt)
    exact ⟨hg.1, by simp only [List.length_map]; exact hg.2⟩

lemma rfCircuit_or_subset {n : ℕ} (C : Circuit) (A : Finset ℕ)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A)
    (a : Fin n) (K : Finset ℕ) (ki : ℕ → ℕ) :
    ∀ (j : ℕ) (g : Gate), (rfCircuit C a K ki).gates[j]? = some g → g.op = GateOp.or → j ∈ A \ K := by
  intro j g hj hor
  simp only [rfCircuit, List.getElem?_ofFn] at hj
  by_cases hlt : j < C.gates.length
  · simp only [hlt, ↓reduceDIte, Option.some.injEq] at hj
    subst hj
    unfold rfGate at hor
    by_cases hjK : j ∈ K
    · simp only [hjK, ↓reduceIte] at hor
      cases h : (C.gates[j]'hlt).inputs.filter (fun k => k != ki j) with
      | nil => rw [h] at hor; cases hor
      | cons k ks => rw [h] at hor; cases hor
    · simp only [hjK, ↓reduceIte] at hor
      exact Finset.mem_sdiff.mpr ⟨hA j _ (List.getElem?_eq_getElem hlt) hor, hjK⟩
  · simp only [hlt, ↓reduceDIte] at hj
    cases hj

lemma rfCircuit_wires {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (a : Fin n) (K : Finset ℕ) (ki : ℕ → ℕ)
    (hK : ∀ j ∈ K, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.or ∧
      ki j ∈ g.inputs ∧ ki j < n + j ∧
      ∀ z : Fin n → Bool, z a = false → (C.wires (List.ofFn z)).getD (ki j) false = false)
    (x : Fin n → Bool) :
    ∀ w : ℕ, w ≠ a.val →
      ((rfCircuit C a K ki).wires (List.ofFn x)).getD w false =
      (C.wires (List.ofFn (Function.update x a false))).getD w false := by
  set C' := rfCircuit C a K ki
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwa
    by_cases hw1 : w < n
    · rw [wires_input C' x w hw1, wires_input C (Function.update x a false) w hw1]
      have hne : (⟨w, hw1⟩ : Fin n) ≠ a := fun h => hwa (congrArg Fin.val h)
      rw [Function.update_of_ne hne]
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C' x w (by simp [C', rfCircuit, hw2]), wires_oob C _ w hw2]
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hg' : C'.gates[j]? = some (rfGate C a K ki ⟨j, hjlt⟩) := by
          simp [C', rfCircuit, hjlt]
        rw [hwj, wires_gate_ofFn C' x j _ hg', wires_gate_ofFn C _ j _ hg]
        have hrep : ∀ k : ℕ,
            (if (if k = a.val then n + j else k) < n + j then
              (C'.wires (List.ofFn x)).getD (if k = a.val then n + j else k) false else false) =
            (if k < n + j then (C.wires (List.ofFn (Function.update x a false))).getD k false else false) := by
          intro k
          by_cases hka : k = a.val
          · subst hka
            have ha_lt : a.val < n + j := by omega
            simp only [↓reduceIte, lt_irrefl, ha_lt]
            rw [wires_input C (Function.update x a false) a.val a.isLt]
            have : (⟨a.val, a.isLt⟩ : Fin n) = a := Fin.ext rfl
            rw [this, Function.update_self]
          · simp only [hka, ↓reduceIte]
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              exact ih k (by omega) hka
            · simp only [hklt, ↓reduceIte]
        unfold rfGate
        by_cases hjK : j ∈ K
        · simp only [hjK, ↓reduceIte]
          obtain ⟨g0, hg0, hor0, hmem0, hlt0, hzero0⟩ := hK j hjK
          rw [hg, Option.some.injEq] at hg0
          subst hg0
          have hlen2 : (C.gates[j]'hjlt).inputs.length ≤ 2 := (hmono _ (List.getElem_mem hjlt)).2
          have hki0 : (C.wires (List.ofFn (Function.update x a false))).getD (ki j) false = false :=
            hzero0 (Function.update x a false) (Function.update_self a false x)
          rw [hor0]
          rcases hlist : (C.gates[j]'hjlt).inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
          · rw [hlist] at hmem0; simp at hmem0
          · rw [hlist] at hmem0
            simp only [List.mem_singleton] at hmem0
            subst hmem0
            simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil]
            simp only [GateOp.eval, List.map_cons, List.map_nil, lt_irrefl, ↓reduceIte, hlt0, hki0, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          · rw [hlist] at hmem0
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem0
            rcases hmem0 with hkp | hkq
            · subst hkp
              by_cases hqp : q = ki j
              · subst hqp
                simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil]
                simp only [GateOp.eval, List.map_cons, List.map_nil, lt_irrefl, ↓reduceIte, hlt0, hki0, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
              · have hne_b : (q != ki j) = true := bne_iff_ne.mpr hqp
                simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hne_b, List.filter_nil]
                simp only [GateOp.eval, List.map_cons, List.map_nil, hlt0, ↓reduceIte, hki0, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.false_or, Bool.or_false]
                exact hrep q
            · subst hkq
              by_cases hpq : p = ki j
              · subst hpq
                simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil]
                simp only [GateOp.eval, List.map_cons, List.map_nil, lt_irrefl, ↓reduceIte, hlt0, hki0, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
              · have hne_b : (p != ki j) = true := bne_iff_ne.mpr hpq
                simp only [List.filter_cons, hne_b, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true, List.filter_nil]
                simp only [GateOp.eval, List.map_cons, List.map_nil, hlt0, ↓reduceIte, hki0, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
                exact hrep p
          · rw [hlist] at hlen2; simp at hlen2
        · simp only [hjK, ↓reduceIte, List.map_map]
          congr 1
          apply List.map_congr_left
          intro k _
          exact hrep k

lemma rfCircuit_eval {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (a : Fin n) (K : Finset ℕ) (ki : ℕ → ℕ)
    (hK : ∀ j ∈ K, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.or ∧
      ki j ∈ g.inputs ∧ ki j < n + j ∧
      ∀ z : Fin n → Bool, z a = false → (C.wires (List.ofFn z)).getD (ki j) false = false)
    (x : Fin n → Bool) :
    (rfCircuit C a K ki).eval (List.ofFn x) = C.eval (List.ofFn (Function.update x a false)) := by
  unfold Circuit.eval
  by_cases ho : C.output = a.val
  · have hout : (rfCircuit C a K ki).output = n + C.gates.length := by simp [rfCircuit, ho]
    rw [hout, ho]
    rw [wires_oob (rfCircuit C a K ki) x (n + C.gates.length) (by simp [rfCircuit])]
    rw [wires_input C (Function.update x a false) a.val a.isLt]
    have : (⟨a.val, a.isLt⟩ : Fin n) = a := Fin.ext rfl
    rw [this, Function.update_self]
  · have hout : (rfCircuit C a K ki).output = C.output := by simp [rfCircuit, ho]
    rw [hout]
    exact rfCircuit_wires C hmono a K ki hK x C.output ho

def rtGate {n : ℕ} (C : Circuit) (a : Fin n) (j1 : ℕ) (j : Fin C.gates.length) : Gate :=
  let g := C.gates[j.val]
  match g.op with
  | GateOp.and => ⟨GateOp.and, g.inputs.filter (fun k => k != a.val)⟩
  | _ =>
    if j.val = j1 ∨ a.val ∈ g.inputs then
      ⟨GateOp.and, []⟩
    else
      g

def rtCircuit {n : ℕ} (C : Circuit) (a : Fin n) (j1 : ℕ) : Circuit :=
  ⟨List.ofFn (rtGate C a j1), C.output⟩

lemma rtCircuit_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (a : Fin n) (j1 : ℕ) :
    PEqualNP.MetaComplexity.Monotone2 (rtCircuit C a j1) := by
  intro g' hg'
  simp only [rtCircuit, List.mem_ofFn] at hg'
  obtain ⟨j, rfl⟩ := hg'
  have hg := hmono C.gates[j] (List.getElem_mem j.isLt)
  unfold rtGate
  dsimp only
  cases h : (C.gates[j.val]).op with
  | and => exact ⟨by simp, le_trans (List.length_filter_le _ _) hg.2⟩
  | or =>
    by_cases hkill : j.val = j1 ∨ a.val ∈ (C.gates[j.val]).inputs
    · simp only [hkill, ↓reduceIte]; exact ⟨by simp, by simp⟩
    · simp only [hkill, ↓reduceIte]; exact hg
  | not =>
    by_cases hkill : j.val = j1 ∨ a.val ∈ (C.gates[j.val]).inputs
    · simp only [hkill, ↓reduceIte]; exact ⟨by simp, by simp⟩
    · simp only [hkill, ↓reduceIte]; exact hg
  | mod m =>
    by_cases hkill : j.val = j1 ∨ a.val ∈ (C.gates[j.val]).inputs
    · simp only [hkill, ↓reduceIte]; exact ⟨by simp, by simp⟩
    · simp only [hkill, ↓reduceIte]; exact hg
  | maj =>
    by_cases hkill : j.val = j1 ∨ a.val ∈ (C.gates[j.val]).inputs
    · simp only [hkill, ↓reduceIte]; exact ⟨by simp, by simp⟩
    · simp only [hkill, ↓reduceIte]; exact hg

lemma rtCircuit_or_subset {n : ℕ} (C : Circuit) (A : Finset ℕ)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A)
    (a : Fin n) (j1 : ℕ) :
    ∀ (j : ℕ) (g : Gate), (rtCircuit C a j1).gates[j]? = some g → g.op = GateOp.or → j ∈ A.erase j1 := by
  intro j g hj hor
  simp only [rtCircuit, List.getElem?_ofFn] at hj
  by_cases hlt : j < C.gates.length
  · simp only [hlt, ↓reduceDIte, Option.some.injEq] at hj
    subst hj
    unfold rtGate at hor
    dsimp only at hor
    cases hop : (C.gates[j]'hlt).op with
    | and => simp only [hop] at hor; cases hor
    | or =>
      simp only [hop] at hor
      by_cases hkill : j = j1 ∨ a.val ∈ (C.gates[j]'hlt).inputs
      · simp only [hkill, ↓reduceIte] at hor; cases hor
      · have hne : j ≠ j1 := fun h => hkill (Or.inl h)
        exact Finset.mem_erase.mpr ⟨hne, hA j _ (List.getElem?_eq_getElem hlt) hop⟩
    | not =>
      simp only [hop] at hor
      by_cases hkill : j = j1 ∨ a.val ∈ (C.gates[j]'hlt).inputs
      · simp only [hkill, ↓reduceIte] at hor; cases hor
      · simp only [hkill, ↓reduceIte, hop] at hor; cases hor
    | mod m =>
      simp only [hop] at hor
      by_cases hkill : j = j1 ∨ a.val ∈ (C.gates[j]'hlt).inputs
      · simp only [hkill, ↓reduceIte] at hor; cases hor
      · simp only [hkill, ↓reduceIte, hop] at hor; cases hor
    | maj =>
      simp only [hop] at hor
      by_cases hkill : j = j1 ∨ a.val ∈ (C.gates[j]'hlt).inputs
      · simp only [hkill, ↓reduceIte] at hor; cases hor
      · simp only [hkill, ↓reduceIte, hop] at hor; cases hor
  · simp only [hlt, ↓reduceDIte] at hj
    cases hj

lemma rtCircuit_wires {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (a : Fin n) (j1 i1 : ℕ) (g1 : Gate)
    (hj1 : C.gates[j1]? = some g1) (hor1 : g1.op = GateOp.or)
    (hi1_mem : i1 ∈ g1.inputs) (hi1_lt : i1 < n + j1)
    (hi1_one : ∀ z : Fin n → Bool, z a = true → (C.wires (List.ofFn z)).getD i1 false = true)
    (x : Fin n → Bool) :
    ∀ w : ℕ, w ≠ a.val →
      ((rtCircuit C a j1).wires (List.ofFn x)).getD w false =
      (C.wires (List.ofFn (Function.update x a true))).getD w false := by
  set C' := rtCircuit C a j1
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwa
    by_cases hw1 : w < n
    · rw [wires_input C' x w hw1, wires_input C (Function.update x a true) w hw1]
      have hne : (⟨w, hw1⟩ : Fin n) ≠ a := fun h => hwa (congrArg Fin.val h)
      rw [Function.update_of_ne hne]
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C' x w (by simp [C', rtCircuit, hw2]), wires_oob C _ w hw2]
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hg' : C'.gates[j]? = some (rtGate C a j1 ⟨j, hjlt⟩) := by
          simp [C', rtCircuit, hjlt]
        rw [hwj, wires_gate_ofFn C' x j _ hg', wires_gate_ofFn C _ j _ hg]
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.getElem_mem hjlt)).1
        unfold rtGate
        dsimp only
        rcases hgop with hand | hor
        · simp only [hand]
          change (((C.gates[j]'hjlt).inputs.filter (fun k => k != a.val)).map
              (fun i => if i < n + j then (C'.wires (List.ofFn x)).getD i false else false)).all id =
            ((C.gates[j]'hjlt).inputs.map
              (fun i => if i < n + j then (C.wires (List.ofFn (Function.update x a true))).getD i false else false)).all id
          apply Bool.eq_iff_iff.mpr
          simp only [List.all_eq_true, List.mem_map, List.mem_filter, bne_iff_ne, id_eq]
          constructor
          · rintro h _ ⟨k, hk, rfl⟩
            by_cases hka : k = a.val
            · subst hka
              have ha_lt : a.val < n + j := by omega
              simp only [ha_lt, ↓reduceIte]
              rw [wires_input C _ a.val a.isLt]
              have : (⟨a.val, a.isLt⟩ : Fin n) = a := Fin.ext rfl
              rw [this, Function.update_self]
            · have hk' := h _ ⟨k, ⟨hk, hka⟩, rfl⟩
              by_cases hklt : k < n + j
              · simp only [hklt, ↓reduceIte] at hk' ⊢
                rw [← ih k (by omega) hka]
                exact hk'
              · simp only [hklt, ↓reduceIte] at hk'
                exact absurd hk' (by decide)
          · rintro h _ ⟨k, ⟨hk, hka⟩, rfl⟩
            have hk' := h _ ⟨k, hk, rfl⟩
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte] at hk' ⊢
              rw [ih k (by omega) hka]
              exact hk'
            · simp only [hklt, ↓reduceIte] at hk'
              exact absurd hk' (by decide)
        · simp only [hor]
          by_cases hkill : j = j1 ∨ a.val ∈ (C.gates[j]'hjlt).inputs
          · simp only [hkill, ↓reduceIte]
            change true = ((C.gates[j]'hjlt).inputs.map (fun i => if i < n + j then (C.wires (List.ofFn (Function.update x a true))).getD i false else false)).any id
            symm
            rw [List.any_eq_true]
            rcases hkill with rfl | hamem
            · rw [hg, Option.some.injEq] at hj1
              subst hj1
              refine ⟨_, List.mem_map_of_mem hi1_mem, ?_⟩
              simp only [id_eq, hi1_lt, ↓reduceIte]
              exact hi1_one (Function.update x a true) (Function.update_self a true x)
            · refine ⟨_, List.mem_map_of_mem hamem, ?_⟩
              have ha_lt : a.val < n + j := by omega
              simp only [id_eq, ha_lt, ↓reduceIte]
              rw [wires_input C _ a.val a.isLt]
              have : (⟨a.val, a.isLt⟩ : Fin n) = a := Fin.ext rfl
              rw [this, Function.update_self]
          · simp only [hkill, ↓reduceIte]
            congr 1
            apply List.map_congr_left
            intro k hk
            have hka : k ≠ a.val := fun h => hkill (Or.inr (h ▸ hk))
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              exact ih k (by omega) hka
            · simp only [hklt, ↓reduceIte]

def andFoldStep {n : ℕ} (f : ℕ → Option (Finset (Fin n))) (acc : Option (Finset (Fin n))) (i : ℕ) :
    Option (Finset (Fin n)) :=
  match acc with
  | none => none
  | some S =>
    match f i with
    | none => none
    | some T => some (S ∪ T)

def andStatusAux {n : ℕ} (C : Circuit) (w : ℕ) : Option (Finset (Fin n)) :=
  if hw : w < n then
    some {⟨w, hw⟩}
  else
    match C.gates[w - n]? with
    | none => none
    | some g =>
      g.inputs.foldl (andFoldStep fun i => if _hi : i < w then andStatusAux C i else none) (some ∅)
termination_by w

lemma foldl_andStatus_sound {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool)
    (f : ℕ → Option (Finset (Fin n)))
    (hf : ∀ i, match f i with
      | none => (if i < w then (C.wires (List.ofFn x)).getD i false else false) = false
      | some T => (if i < w then (C.wires (List.ofFn x)).getD i false else false) = decide (∀ u ∈ T, x u = true))
    (l : List ℕ) (acc : Option (Finset (Fin n))) :
    match l.foldl (andFoldStep f) acc with
    | none => ((match acc with | none => false | some S => decide (∀ u ∈ S, x u = true)) && (l.map fun i => if i < w then (C.wires (List.ofFn x)).getD i false else false).all id) = false
    | some U => ((match acc with | none => false | some S => decide (∀ u ∈ S, x u = true)) && (l.map fun i => if i < w then (C.wires (List.ofFn x)).getD i false else false).all id) = decide (∀ u ∈ U, x u = true) := by
  induction l generalizing acc with
  | nil =>
    cases acc with
    | none => simp
    | some S => simp
  | cons i l ih =>
    simp only [List.foldl_cons, List.map_cons, List.all_cons, id_eq]
    cases acc with
    | none =>
      have h := ih none
      simpa [andFoldStep] using h
    | some S =>
      have hfi := hf i
      cases hfi_eq : f i with
      | none =>
        rw [hfi_eq] at hfi
        have h := ih none
        simp only [andFoldStep, hfi_eq, hfi, Bool.false_and, Bool.and_false] at h ⊢
        exact h
      | some T =>
        rw [hfi_eq] at hfi
        have h := ih (some (S ∪ T))
        have hcomb : (decide (∀ u ∈ S, x u = true) && decide (∀ u ∈ T, x u = true)) = decide (∀ u ∈ S ∪ T, x u = true) := by
          apply Bool.eq_iff_iff.mpr
          simp [Finset.mem_union, or_imp, forall_and]
        simp only [andFoldStep, hfi_eq]
        rw [← Bool.and_assoc, hfi, hcomb]
        exact h

lemma andStatusAux_sound {n : ℕ} (C : Circuit) (limit : ℕ)
    (hand : ∀ j < limit, ∀ g, C.gates[j]? = some g → g.op = GateOp.and)
    (w : ℕ) (hwlim : w < n + limit) :
    match andStatusAux C w with
    | none => ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = false
    | some S => ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = decide (∀ u ∈ S, x u = true) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [andStatusAux]
    split_ifs with hw
    · intro x
      rw [wires_input C x w hw]
      simp
    · cases hget : C.gates[w - n]? with
      | none =>
        intro x
        have hge : C.gates.length ≤ w - n := List.getElem?_eq_none_iff.mp hget
        exact wires_oob C x w (by omega)
      | some g =>
        have hwj : w = n + (w - n) := by omega
        have hjlim : w - n < limit := by omega
        have hgop : g.op = GateOp.and := hand (w - n) hjlim g hget
        set f : ℕ → Option (Finset (Fin n)) := fun i => if _hi : i < w then andStatusAux C i else none
        have hfold := fun x => foldl_andStatus_sound C w x f
          (fun i => by
            by_cases hi : i < w
            · simp only [f, hi, ↓reduceDIte, ↓reduceIte]
              have hprev := ih i hi (by omega)
              cases heq : andStatusAux C i with
              | none => rw [heq] at hprev; exact hprev x
              | some T => rw [heq] at hprev; exact hprev x
            · simp only [f, hi, ↓reduceDIte, ↓reduceIte])
          g.inputs (some ∅)
        change match g.inputs.foldl (andFoldStep f) (some ∅) with
          | none => ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = false
          | some S => ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = decide (∀ u ∈ S, x u = true)
        cases hres : g.inputs.foldl (andFoldStep f) (some ∅) with
        | none =>
          intro x
          have hx := hfold x
          rw [hres] at hx
          simp only [Finset.notMem_empty, IsEmpty.forall_iff, imp_true_iff, decide_true, Bool.true_and] at hx
          rw [hwj, wires_gate_ofFn C x (w - n) g hget, hgop, ← hwj]
          exact hx
        | some U =>
          intro x
          have hx := hfold x
          rw [hres] at hx
          simp only [Finset.notMem_empty, IsEmpty.forall_iff, imp_true_iff, decide_true, Bool.true_and] at hx
          rw [hwj, wires_gate_ofFn C x (w - n) g hget, hgop, ← hwj]
          exact hx

def delVert {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ a ∧ v ≠ a
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

lemma delVert_le {n : ℕ} (G : SimpleGraph (Fin n)) (a : Fin n) : delVert G a ≤ G :=
  fun _ _ h => h.1

lemma subgraph_hpf {n : ℕ} (G G' : SimpleGraph (Fin n)) (hle : G' ≤ G)
    (hpf : ∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) :
    ∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G'.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card := by
  intro S
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hpf S)
  intro e ⟨he, hS⟩
  exact ⟨SimpleGraph.edgeSet_mono hle he, hS⟩

lemma subgraph_hno4 {n : ℕ} (G G' : SimpleGraph (Fin n)) (hle : G' ≤ G)
    (hno4 : ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) :
    ∀ (v : Fin n) (c : G'.Walk v v), c.IsCycle → c.length ≠ 4 := by
  intro v c hc
  have hc' : (c.mapLe hle).IsCycle := SimpleGraph.Walk.IsCycle.map (f := SimpleGraph.Hom.ofLE hle) (fun _ _ h => h) hc
  have hlen : (c.mapLe hle).length = c.length := SimpleGraph.Walk.length_map _ _
  rw [← hlen]
  exact hno4 v (c.mapLe hle) hc'

lemma delVert_edge_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n) :
    (delVert G a).edgeSet.ncard + G.degree a = G.edgeSet.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  have h1 : (delVert G a).edgeSet.toFinset = (G.edgeFinset).filter (fun e => a ∉ e) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Set.mem_toFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.mem_iff, not_or]
      change (G.Adj u v ∧ u ≠ a ∧ v ≠ a) ↔ (G.Adj u v ∧ a ≠ u ∧ a ≠ v)
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.symm, h3.symm⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.symm, h3.symm⟩
  have h2 : G.edgeSet.toFinset = G.edgeFinset := by
    ext e; simp
  rw [h1, h2]
  have hpart := Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (p := fun e => a ∉ e)
  have hinc : (G.edgeFinset.filter (fun e => ¬ a ∉ e)).card = G.degree a := by
    rw [SimpleGraph.degree]
    refine Finset.card_bij (fun e he => (Sym2.mem_iff_exists.mp (by simpa using (Finset.mem_filter.mp he).2)).choose) ?_ ?_ ?_
    · intro e he
      have hmem := (Finset.mem_filter.mp he).1
      have hae : a ∈ e := by simpa using (Finset.mem_filter.mp he).2
      have hspec := (Sym2.mem_iff_exists.mp hae).choose_spec
      rw [SimpleGraph.mem_neighborFinset]
      rw [SimpleGraph.mem_edgeFinset, hspec] at hmem
      exact hmem
    · intro e1 he1 e2 he2 heq
      have hae1 : a ∈ e1 := by simpa using (Finset.mem_filter.mp he1).2
      have hae2 : a ∈ e2 := by simpa using (Finset.mem_filter.mp he2).2
      rw [(Sym2.mem_iff_exists.mp hae1).choose_spec, (Sym2.mem_iff_exists.mp hae2).choose_spec, heq]
    · intro u hu
      rw [SimpleGraph.mem_neighborFinset] at hu
      refine ⟨s(a, u), Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hu, by simp⟩, ?_⟩
      have hae : a ∈ s(a, u) := Sym2.mem_mk_left a u
      have hspec := (Sym2.mem_iff_exists.mp hae).choose_spec
      rcases Sym2.eq_iff.mp hspec with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2.symm
      · exfalso; exact G.ne_of_adj hu h2.symm
  omega

lemma no_four_cycle_common {n : ℕ} (G : SimpleGraph (Fin n))
    (hno4 : ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4)
    (a b w1 w2 : Fin n) (hab : a ≠ b) (hw : w1 ≠ w2)
    (ha1 : G.Adj a w1) (ha2 : G.Adj a w2) (hb1 : G.Adj b w1) (hb2 : G.Adj b w2) : False := by
  have hw1a : w1 ≠ a := G.ne_of_adj ha1.symm
  have hw2a : w2 ≠ a := G.ne_of_adj ha2.symm
  have hw1b : w1 ≠ b := G.ne_of_adj hb1.symm
  have hw2b : w2 ≠ b := G.ne_of_adj hb2.symm
  let c : G.Walk a a :=
    SimpleGraph.Walk.cons ha1
      (SimpleGraph.Walk.cons hb1.symm
        (SimpleGraph.Walk.cons hb2
          (SimpleGraph.Walk.cons ha2.symm SimpleGraph.Walk.nil)))
  have hc : c.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · simp only [c, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true, and_true, not_or]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
    · intro h; simp [c] at h
    · simp only [c, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true, and_true, not_or]
      exact ⟨⟨hw1b, hw, hw1a⟩, ⟨hw2b.symm, hab.symm⟩, hw2a⟩
  exact hno4 a c hc rfl

lemma all_deg_two_of_no_deg_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpf : ∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card)
    (hno1 : ∀ v : Fin n, G.degree v ≠ 1) :
    ∀ v : Fin n, (∃ w, G.Adj v w) → G.degree v = 2 := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun v => ∃ w, G.Adj v w)
  have hge2 : ∀ v ∈ S, 2 ≤ G.degree v := by
    intro v hv
    obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hv).2
    have hpos : 0 < G.degree v := Finset.card_pos.mpr ⟨w, (SimpleGraph.mem_neighborFinset G v w).mpr hw⟩
    have hne1 := hno1 v
    omega
  have hsum_all : ∑ v : Fin n, G.degree v = ∑ v ∈ S, G.degree v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro v _ hv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hv
    rw [SimpleGraph.degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    exact hv w ((SimpleGraph.mem_neighborFinset G v w).mp hw)
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hedgeS : {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Set.mem_toFinset, Set.mem_ofPred_eq, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeFinset, S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro huv
        refine ⟨huv, fun t ht => ?_⟩
        rcases Sym2.mem_iff.mp ht with rfl | rfl
        · exact ⟨v, huv⟩
        · exact ⟨u, huv.symm⟩
  have hleS : G.edgeFinset.card ≤ S.card := by
    rw [← hedgeS]; exact hpf S
  have hsum_eq : ∑ v ∈ S, G.degree v = ∑ _v ∈ S, 2 := by
    have h1 : ∑ _v ∈ S, 2 ≤ ∑ v ∈ S, G.degree v := Finset.sum_le_sum hge2
    have h2 : ∑ _v ∈ S, 2 = 2 * S.card := by simp [mul_comm]
    omega
  have hall2 : ∀ v ∈ S, G.degree v = 2 := by
    intro v hv
    by_contra hne
    have hlt : 2 < G.degree v := lt_of_le_of_ne (hge2 v hv) (Ne.symm hne)
    have hstrict := Finset.sum_lt_sum hge2 ⟨v, hv, hlt⟩
    omega
  intro v hv
  exact hall2 v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)

lemma deg_two_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (hdeg : G.degree v = 2) :
    ∃ w1 w2 : Fin n, w1 ≠ w2 ∧ G.Adj v w1 ∧ G.Adj v w2 ∧ ∀ w : Fin n, G.Adj v w ↔ w = w1 ∨ w = w2 := by
  rw [SimpleGraph.degree, Finset.card_eq_two] at hdeg
  obtain ⟨w1, w2, hne, hset⟩ := hdeg
  refine ⟨w1, w2, hne, ?_, ?_, ?_⟩
  · exact (SimpleGraph.mem_neighborFinset G v w1).mp (hset ▸ Finset.mem_insert_self w1 {w2})
  · exact (SimpleGraph.mem_neighborFinset G v w2).mp (hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w2))
  · intro w
    rw [← SimpleGraph.mem_neighborFinset, hset, Finset.mem_insert, Finset.mem_singleton]

lemma card_edges_ge_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h2 : 2 ≤ G.edgeSet.ncard)
    (hdeg2 : ∀ v : Fin n, (∃ w, G.Adj v w) → G.degree v = 2) :
    3 ≤ G.edgeSet.ncard := by
  classical
  have hpos : 0 < G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card'] at h2
    have : G.edgeSet.toFinset = G.edgeFinset := by ext e; simp
    rw [← this]; omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    obtain ⟨w1, w2, hne, hu1, hu2, hallu⟩ := deg_two_neighbors G u (hdeg2 u ⟨v, huv⟩)
    obtain ⟨z1, z2, hnez, hv1, hv2, hallv⟩ := deg_two_neighbors G v (hdeg2 v ⟨u, huv.symm⟩)
    have hvu : v = w1 ∨ v = w2 := (hallu v).mp huv
    have huv' : u = z1 ∨ u = z2 := (hallv u).mp huv.symm
    obtain ⟨w, hwu, hwv⟩ : ∃ w, G.Adj u w ∧ w ≠ v := by
      rcases hvu with rfl | rfl
      · exact ⟨w2, hu2, hne.symm⟩
      · exact ⟨w1, hu1, hne⟩
    obtain ⟨z, hzv, hzu⟩ : ∃ z, G.Adj v z ∧ z ≠ u := by
      rcases huv' with rfl | rfl
      · exact ⟨z2, hv2, hnez.symm⟩
      · exact ⟨z1, hv1, hnez⟩
    have hsub : ({s(u, v), s(u, w), s(v, z)} : Finset (Sym2 (Fin n))) ⊆ G.edgeFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact SimpleGraph.mem_edgeFinset.mpr huv
      · exact SimpleGraph.mem_edgeFinset.mpr hwu
      · exact SimpleGraph.mem_edgeFinset.mpr hzv
    have hcard3 : ({s(u, v), s(u, w), s(v, z)} : Finset (Sym2 (Fin n))).card = 3 := by
      have huv_ne : u ≠ v := G.ne_of_adj huv
      have huw_ne : u ≠ w := G.ne_of_adj hwu
      have hvz_ne : v ≠ z := G.ne_of_adj hzv
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact huv_ne h1
        · exact hwv h2
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_⟩
        · intro h
          rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact hwv h2.symm
          · exact huw_ne h1
        · intro h
          rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact huv_ne h1
          · exact hzu h1.symm
    have hle := Finset.card_le_card hsub
    rw [hcard3] at hle
    rw [Set.ncard_eq_toFinset_card']
    have : G.edgeSet.toFinset = G.edgeFinset := by ext x; simp
    rw [this]; exact hle

lemma two_distinct_edges {n : ℕ} (G : SimpleGraph (Fin n))
    (h2 : 2 ≤ G.edgeSet.ncard) :
    ∃ u1 v1 u2 v2 : Fin n, G.Adj u1 v1 ∧ G.Adj u2 v2 ∧ s(u1, v1) ≠ s(u2, v2) := by
  classical
  rw [Set.ncard_eq_toFinset_card'] at h2
  have h1 : 1 < G.edgeSet.toFinset.card := by omega
  obtain ⟨e1, he1, e2, he2, hne⟩ := Finset.one_lt_card.mp h1
  induction e1 using Sym2.ind with
  | _ u1 v1 =>
    induction e2 using Sym2.ind with
    | _ u2 v2 =>
      exact ⟨u1, v1, u2, v2, by simpa using he1, by simpa using he2, hne⟩

lemma main_thm (n : ℕ) :
    ∀ N : ℕ, ∀ (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ),
      G.edgeSet.ncard + A.card = N →
      (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) →
      G.edgeSet.ncard ≤ A.card + 1 := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro G C A hN hpf hno4 hmono hfun hA
    by_cases hE1 : G.edgeSet.ncard ≤ 1
    · omega
    have hE2 : 2 ≤ G.edgeSet.ncard := by omega
    by_cases hleaf : ∃ a : Fin n, G.degree a = 1
    · obtain ⟨a, hdega⟩ := hleaf
      rw [SimpleGraph.degree, Finset.card_eq_one] at hdega
      obtain ⟨u, hu⟩ := hdega
      have hau : G.Adj a u := (SimpleGraph.mem_neighborFinset G a u).mp (hu ▸ Finset.mem_singleton_self u)
      have hau_ne : a ≠ u := G.ne_of_adj hau
      set G' := delVert G a
      have hG'card : G'.edgeSet.ncard + 1 = G.edgeSet.ncard := by
        have := delVert_edge_card G a
        rw [SimpleGraph.degree, hu, Finset.card_singleton] at this
        exact this
      have hG'ne : G'.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨e0, he0⟩ := hG'ne
      induction e0 using Sym2.ind with
      | _ u0 v0 =>
        have huv0 : G'.Adj u0 v0 := he0
        have hf0 : C.eval (List.ofFn (fun t : Fin n => decide (t = u))) = false := by
          cases h : C.eval (List.ofFn (fun t : Fin n => decide (t = u))) with
          | false => rfl
          | true =>
            obtain ⟨p, q, hpq, hp, hq⟩ := (hfun _).mp h
            simp only [decide_eq_true_eq] at hp hq
            subst hp; subst hq
            exact absurd hpq (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn (Function.update (fun t : Fin n => decide (t = u)) a true)) = true := by
          rw [hfun]
          exact ⟨a, u, hau, by simp, by rw [Function.update_of_ne hau_ne.symm]; simp⟩
        have hy0 : (fun t : Fin n => decide (t = u0 ∨ t = v0)) a = false := by
          have h1 : a ≠ u0 := huv0.2.1.symm
          have h2 : a ≠ v0 := huv0.2.2.symm
          simp [h1, h2]
        have hyt : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true := by
          rw [hfun]
          exact ⟨u0, v0, huv0.1, by simp, by simp⟩
        obtain ⟨j1, g1, i1, hj1, hor1, _, hi1m, hi1lt, hi1z⟩ :=
          find_or_gate_avoid n C a none hmono _ ⟨hf0, hf1⟩ (by intro _ h; cases h) _ hy0 hyt
        set C' := rfCircuit C a {j1} (fun _ => i1)
        have hK : ∀ j ∈ ({j1} : Finset ℕ), ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.or ∧
            i1 ∈ g.inputs ∧ i1 < n + j ∧ ∀ z : Fin n → Bool, z a = false → (C.wires (List.ofFn z)).getD i1 false = false := by
          intro j hj
          rw [Finset.mem_singleton] at hj; subst hj
          exact ⟨g1, hj1, hor1, hi1m, hi1lt, hi1z⟩
        have hC'fun : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G'.Adj u v ∧ x u = true ∧ x v = true := by
          intro x
          rw [rfCircuit_eval C hmono a {j1} (fun _ => i1) hK x, hfun]
          constructor
          · rintro ⟨p, q, hpq, hp, hq⟩
            have hpa : p ≠ a := by intro h; subst h; rw [Function.update_self] at hp; exact absurd hp (by decide)
            have hqa : q ≠ a := by intro h; subst h; rw [Function.update_self] at hq; exact absurd hq (by decide)
            rw [Function.update_of_ne hpa] at hp
            rw [Function.update_of_ne hqa] at hq
            exact ⟨p, q, ⟨hpq, hpa, hqa⟩, hp, hq⟩
          · rintro ⟨p, q, ⟨hpq, hpa, hqa⟩, hp, hq⟩
            exact ⟨p, q, hpq, by rw [Function.update_of_ne hpa]; exact hp, by rw [Function.update_of_ne hqa]; exact hq⟩
        have hj1A : j1 ∈ A := hA j1 g1 hj1 hor1
        have hA'card : (A \ {j1}).card + 1 = A.card := by
          rw [Finset.sdiff_singleton_eq_erase]
          exact Finset.card_erase_add_one hj1A
        have hrec := ih (G'.edgeSet.ncard + (A \ {j1}).card) (by omega) G' C' (A \ {j1}) rfl
          (subgraph_hpf G G' (delVert_le G a) hpf)
          (subgraph_hno4 G G' (delVert_le G a) hno4)
          (rfCircuit_mono C hmono a {j1} (fun _ => i1))
          hC'fun
          (rfCircuit_or_subset C A hA a {j1} (fun _ => i1))
        omega
    · have hno1 : ∀ v : Fin n, G.degree v ≠ 1 := fun v h => hleaf ⟨v, h⟩
      have hdeg2 : ∀ v : Fin n, (∃ w, G.Adj v w) → G.degree v = 2 := all_deg_two_of_no_deg_one G hpf hno1
      have hE3 : 3 ≤ G.edgeSet.ncard := card_edges_ge_three G hE2 hdeg2
      have hhas_or : ∃ j : ℕ, ∃ h : j < C.gates.length, (C.gates[j]'h).op = GateOp.or := by
        by_contra hno_or
        have hall_and : ∀ j < C.gates.length, ∀ g, C.gates[j]? = some g → g.op = GateOp.and := by
          intro j hj g hget
          have hmem := List.mem_of_getElem? hget
          rcases (by simpa using (hmono g hmem).1 : g.op = GateOp.and ∨ g.op = GateOp.or) with h | h
          · exact h
          · rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hget
            exact absurd ⟨j, hj, hget ▸ h⟩ hno_or
        by_cases hoob : n + C.gates.length ≤ C.output
        · obtain ⟨u1, v1, _, _, huv1, _, _⟩ := two_distinct_edges G hE2
          have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u1 ∨ t = v1))) = true :=
            (hfun _).mpr ⟨u1, v1, huv1, by simp, by simp⟩
          unfold Circuit.eval at ht
          rw [wires_oob C _ C.output hoob] at ht
          exact absurd ht (by decide)
        · have hsnd := @andStatusAux_sound n C C.gates.length hall_and C.output (by omega)
          cases hst : andStatusAux C C.output with
          | none =>
            rw [hst] at hsnd
            obtain ⟨u1, v1, _, _, huv1, _, _⟩ := two_distinct_edges G hE2
            have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u1 ∨ t = v1))) = true :=
              (hfun _).mpr ⟨u1, v1, huv1, by simp, by simp⟩
            unfold Circuit.eval at ht
            rw [hsnd] at ht
            exact absurd ht (by decide)
          | some S =>
            rw [hst] at hsnd
            obtain ⟨u1, v1, u2, v2, huv1, huv2, hne_e⟩ := two_distinct_edges G hE2
            have hS1 : S ⊆ {u1, v1} := by
              have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u1 ∨ t = v1))) = true :=
                (hfun _).mpr ⟨u1, v1, huv1, by simp, by simp⟩
              unfold Circuit.eval at ht
              rw [hsnd, decide_eq_true_eq] at ht
              intro t htS
              have := ht t htS
              simpa using this
            have hS2 : S ⊆ {u2, v2} := by
              have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u2 ∨ t = v2))) = true :=
                (hfun _).mpr ⟨u2, v2, huv2, by simp, by simp⟩
              unfold Circuit.eval at ht
              rw [hsnd, decide_eq_true_eq] at ht
              intro t htS
              have := ht t htS
              simpa using this
            have hScard : 2 ≤ S.card := by
              by_contra hlt2
              have hle1 : S.card ≤ 1 := by omega
              rcases (@Finset.card_le_one_iff_subset_singleton _ S ⟨u1⟩).mp hle1 with ⟨a0, ha0⟩
              have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = a0))) = true := by
                unfold Circuit.eval
                rw [hsnd, decide_eq_true_eq]
                intro t htS
                simp [Finset.mem_singleton.mp (ha0 htS)]
              obtain ⟨p, q, hpq, hp, hq⟩ := (hfun _).mp ht
              simp only [decide_eq_true_eq] at hp hq
              subst hp; subst hq
              exact G.loopless.irrefl _ hpq
            have hcard1 : ({u1, v1} : Finset (Fin n)).card = 2 := Finset.card_pair (G.ne_of_adj huv1)
            have hcard2 : ({u2, v2} : Finset (Fin n)).card = 2 := Finset.card_pair (G.ne_of_adj huv2)
            have heq1 : S = {u1, v1} := Finset.eq_of_subset_of_card_le hS1 (by omega)
            have heq2 : S = {u2, v2} := Finset.eq_of_subset_of_card_le hS2 (by omega)
            have heq12 : ({u1, v1} : Finset (Fin n)) = {u2, v2} := heq1.symm.trans heq2
            have hu1mem : u1 ∈ ({u2, v2} : Finset (Fin n)) := heq12 ▸ Finset.mem_insert_self u1 {v1}
            have hv1mem : v1 ∈ ({u2, v2} : Finset (Fin n)) := heq12 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v1)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu1mem hv1mem
            rcases hu1mem with rfl | rfl <;> rcases hv1mem with rfl | rfl
            · exact G.loopless.irrefl _ huv1
            · exact hne_e rfl
            · exact hne_e Sym2.eq_swap
            · exact G.loopless.irrefl _ huv1
      set j1 := Nat.find hhas_or
      have hj1_spec := Nat.find_spec hhas_or
      obtain ⟨hj1_lt, hor1⟩ := hj1_spec
      set g1 := C.gates[j1]'hj1_lt
      have hg1 : C.gates[j1]? = some g1 := List.getElem?_eq_getElem hj1_lt
      have hj1A : j1 ∈ A := hA j1 g1 hg1 hor1
      have hbefore_and : ∀ j < j1, ∀ g, C.gates[j]? = some g → g.op = GateOp.and := by
        intro j hjj1 g hget
        have hjlt : j < C.gates.length := by omega
        rcases (by simpa using (hmono g (List.mem_of_getElem? hget)).1 : g.op = GateOp.and ∨ g.op = GateOp.or) with h | h
        · exact h
        · rw [List.getElem?_eq_getElem hjlt, Option.some.injEq] at hget
          exact absurd ⟨hjlt, hget ▸ h⟩ (Nat.find_min hhas_or hjj1)
      have elim_j1 : ∀ (g' : Gate), g'.op = GateOp.and → g'.inputs.length ≤ 2 →
          (∀ x : Fin n → Bool, g'.op.eval (g'.inputs.map fun i => if i < n + j1 then (C.wires (List.ofFn x)).getD i false else false) =
            (C.wires (List.ofFn x)).getD (n + j1) false) → G.edgeSet.ncard ≤ A.card + 1 := by
        intro g' hgop' hglen' heq'
        set C' : Circuit := ⟨C.gates.set j1 g', C.output⟩
        have hA'card : (A.erase j1).card + 1 = A.card := Finset.card_erase_add_one hj1A
        have hC'fun : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
          intro x
          have := set_gate_eq C j1 hj1_lt g' x (heq' x) C.output
          change C'.eval (List.ofFn x) = C.eval (List.ofFn x) at this
          rw [this, hfun]
        have hrec := ih (G.edgeSet.ncard + (A.erase j1).card) (by omega) G C' (A.erase j1) rfl
          hpf hno4 (set_gate_mono_struct C hmono j1 g' hgop' hglen') hC'fun
          (set_gate_or_subset C A hA j1 g' hgop')
        omega
      have kill_two_and_rec : ∀ (a : Fin n) (i_j1 : ℕ),
          G.degree a = 2 →
          i_j1 ∈ g1.inputs → i_j1 < n + j1 →
          (∀ z : Fin n → Bool, z a = false → (C.wires (List.ofFn z)).getD i_j1 false = false) →
          (∃ x : Fin n → Bool,
            C.eval (List.ofFn x) = false ∧
            C.eval (List.ofFn (Function.update x a true)) = true ∧
            (C.wires (List.ofFn x)).getD (n + j1) false =
            (C.wires (List.ofFn (Function.update x a true))).getD (n + j1) false) →
          G.edgeSet.ncard ≤ A.card + 1 := by
        intro a i_j1 hdega hij1_m hij1_lt hij1_z ⟨x, hf0, hf1, hconst⟩
        set G' := delVert G a
        have hG'card : G'.edgeSet.ncard + 2 = G.edgeSet.ncard := by
          have := delVert_edge_card G a
          rw [hdega] at this; exact this
        have hG'ne : G'.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨e0, he0⟩ := hG'ne
        induction e0 using Sym2.ind with
        | _ u0 v0 =>
          have huv0 : G'.Adj u0 v0 := he0
          have hy0 : (fun t : Fin n => decide (t = u0 ∨ t = v0)) a = false := by
            have h1 : a ≠ u0 := huv0.2.1.symm
            have h2 : a ≠ v0 := huv0.2.2.symm
            simp [h1, h2]
          have hyt : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true := by
            rw [hfun]
            exact ⟨u0, v0, huv0.1, by simp, by simp⟩
          obtain ⟨j2, g2, i2, hj2, hor2, hj2ne, hi2m, hi2lt, hi2z⟩ :=
            find_or_gate_avoid n C a (some j1) hmono x ⟨hf0, hf1⟩
              (by intro j0 h0; cases h0; exact hconst) _ hy0 hyt
          have hj12 : j1 ≠ j2 := fun h => hj2ne (congrArg some h.symm)
          set K : Finset ℕ := {j1, j2}
          set ki : ℕ → ℕ := fun j => if j = j1 then i_j1 else i2
          have hK : ∀ j ∈ K, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.or ∧
              ki j ∈ g.inputs ∧ ki j < n + j ∧ ∀ z : Fin n → Bool, z a = false → (C.wires (List.ofFn z)).getD (ki j) false = false := by
            intro j hj
            simp only [K, Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl
            · simp only [ki, ↓reduceIte]
              exact ⟨g1, hg1, hor1, hij1_m, hij1_lt, hij1_z⟩
            · simp only [ki, hj12.symm, ↓reduceIte]
              exact ⟨g2, hj2, hor2, hi2m, hi2lt, hi2z⟩
          set C' := rfCircuit C a K ki
          have hC'fun : ∀ z : Fin n → Bool, C'.eval (List.ofFn z) = true ↔ ∃ u v : Fin n, G'.Adj u v ∧ z u = true ∧ z v = true := by
            intro z
            rw [rfCircuit_eval C hmono a K ki hK z, hfun]
            constructor
            · rintro ⟨p, q, hpq, hp, hq⟩
              have hpa : p ≠ a := by intro h; subst h; rw [Function.update_self] at hp; exact absurd hp (by decide)
              have hqa : q ≠ a := by intro h; subst h; rw [Function.update_self] at hq; exact absurd hq (by decide)
              rw [Function.update_of_ne hpa] at hp
              rw [Function.update_of_ne hqa] at hq
              exact ⟨p, q, ⟨hpq, hpa, hqa⟩, hp, hq⟩
            · rintro ⟨p, q, ⟨hpq, hpa, hqa⟩, hp, hq⟩
              exact ⟨p, q, hpq, by rw [Function.update_of_ne hpa]; exact hp, by rw [Function.update_of_ne hqa]; exact hq⟩
          have hj2A : j2 ∈ A := hA j2 g2 hj2 hor2
          have hKsub : K ⊆ A := by
            intro j hj
            simp only [K, Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl
            · exact hj1A
            · exact hj2A
          have hKcard : K.card = 2 := Finset.card_pair hj12
          have hA'card : (A \ K).card + 2 = A.card := by
            have := Finset.card_sdiff_add_card_eq_card hKsub
            omega
          have hrec := ih (G'.edgeSet.ncard + (A \ K).card) (by omega) G' C' (A \ K) rfl
            (subgraph_hpf G G' (delVert_le G a) hpf)
            (subgraph_hno4 G G' (delVert_le G a) hno4)
            (rfCircuit_mono C hmono a K ki)
            hC'fun
            (rfCircuit_or_subset C A hA a K ki)
          omega
      have hlen1 : g1.inputs.length ≤ 2 := (hmono g1 (List.getElem_mem hj1_lt)).2
      rcases hinp : g1.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · apply elim_j1 ⟨GateOp.and, [n + j1]⟩ rfl (by simp)
        intro x
        rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
        simp [GateOp.eval]
      · apply elim_j1 ⟨GateOp.and, [p]⟩ rfl (by simp)
        intro x
        rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
        simp [GateOp.eval]
      · by_cases hplt : p < n + j1
        · by_cases hqlt : q < n + j1
          · have hpsnd := andStatusAux_sound C j1 hbefore_and p hplt
            have hqsnd := andStatusAux_sound C j1 hbefore_and q hqlt
            cases hpst : andStatusAux C p with
            | none =>
              rw [hpst] at hpsnd
              apply elim_j1 ⟨GateOp.and, [q]⟩ rfl (by simp)
              intro x
              rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, hplt, hqlt, ↓reduceIte, hpsnd x, Bool.false_or]
            | some S1 =>
              rw [hpst] at hpsnd
              cases hqst : andStatusAux C q with
              | none =>
                rw [hqst] at hqsnd
                apply elim_j1 ⟨GateOp.and, [p]⟩ rfl (by simp)
                intro x
                rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, hplt, hqlt, ↓reduceIte, hqsnd x]
              | some S2 =>
                rw [hqst] at hqsnd
                by_cases hS1sub : S1 ⊆ S2
                · apply elim_j1 ⟨GateOp.and, [p]⟩ rfl (by simp)
                  intro x
                  rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, hplt, hqlt, ↓reduceIte, hpsnd x, hqsnd x]
                  cases h2 : decide (∀ u ∈ S2, x u = true) with
                  | false => simp
                  | true =>
                    have h1 : decide (∀ u ∈ S1, x u = true) = true := by
                      rw [decide_eq_true_eq] at h2 ⊢
                      exact fun u hu => h2 u (hS1sub hu)
                    simp [h1]
                · by_cases hS2sub : S2 ⊆ S1
                  · apply elim_j1 ⟨GateOp.and, [q]⟩ rfl (by simp)
                    intro x
                    rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, hplt, hqlt, ↓reduceIte, hpsnd x, hqsnd x]
                    cases h1 : decide (∀ u ∈ S1, x u = true) with
                    | false => simp
                    | true =>
                      have h2 : decide (∀ u ∈ S2, x u = true) = true := by
                        rw [decide_eq_true_eq] at h1 ⊢
                        exact fun u hu => h1 u (hS2sub hu)
                      simp [h2]
                  · have hS1ne : S1.Nonempty := by
                      by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; exact hS1sub (h ▸ Finset.empty_subset S2)
                    have hS2ne : S2.Nonempty := by
                      by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; exact hS2sub (h ▸ Finset.empty_subset S1)
                    have elim_iso : ∀ (z : Fin n), (∀ w, ¬ G.Adj z w) → (z ∈ S1 ∨ z ∈ S2) → G.edgeSet.ncard ≤ A.card + 1 := by
                      intro z hiso hzmem
                      obtain ⟨i0, hi0m, hi0lt, hi0z⟩ : ∃ i0 ∈ g1.inputs, i0 < n + j1 ∧
                          ∀ x : Fin n → Bool, x z = false → (C.wires (List.ofFn x)).getD i0 false = false := by
                        rcases hzmem with hz1 | hz2
                        · refine ⟨p, by rw [hinp]; simp, hplt, fun x hxz => ?_⟩
                          rw [hpsnd x, decide_eq_false_iff_not]
                          intro h; have := h z hz1; rw [hxz] at this; exact absurd this (by decide)
                        · refine ⟨q, by rw [hinp]; simp, hqlt, fun x hxz => ?_⟩
                          rw [hqsnd x, decide_eq_false_iff_not]
                          intro h; have := h z hz2; rw [hxz] at this; exact absurd this (by decide)
                      set C' := rfCircuit C z {j1} (fun _ => i0)
                      have hK : ∀ j ∈ ({j1} : Finset ℕ), ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.or ∧
                          i0 ∈ g.inputs ∧ i0 < n + j ∧ ∀ x : Fin n → Bool, x z = false → (C.wires (List.ofFn x)).getD i0 false = false := by
                        intro j hj; rw [Finset.mem_singleton] at hj; subst hj; exact ⟨g1, hg1, hor1, hi0m, hi0lt, hi0z⟩
                      have hC'fun : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
                        intro x
                        rw [rfCircuit_eval C hmono z {j1} (fun _ => i0) hK x, hfun]
                        constructor
                        · rintro ⟨u, v, huv, hu, hv⟩
                          have huz : u ≠ z := fun h => hiso v (h ▸ huv)
                          have hvz : v ≠ z := fun h => hiso u (h ▸ huv.symm)
                          rw [Function.update_of_ne huz] at hu
                          rw [Function.update_of_ne hvz] at hv
                          exact ⟨u, v, huv, hu, hv⟩
                        · rintro ⟨u, v, huv, hu, hv⟩
                          have huz : u ≠ z := fun h => hiso v (h ▸ huv)
                          have hvz : v ≠ z := fun h => hiso u (h ▸ huv.symm)
                          exact ⟨u, v, huv, by rw [Function.update_of_ne huz]; exact hu, by rw [Function.update_of_ne hvz]; exact hv⟩
                      have hA'card : (A \ {j1}).card + 1 = A.card := by
                        rw [Finset.sdiff_singleton_eq_erase]; exact Finset.card_erase_add_one hj1A
                      have hrec := ih (G.edgeSet.ncard + (A \ {j1}).card) (by omega) G C' (A \ {j1}) rfl
                        hpf hno4 (rfCircuit_mono C hmono z {j1} (fun _ => i0)) hC'fun
                        (rfCircuit_or_subset C A hA z {j1} (fun _ => i0))
                      omega
                    by_cases hiso1 : ∃ z ∈ S1, ∀ w, ¬ G.Adj z w
                    · obtain ⟨z, hz1, hiso⟩ := hiso1
                      exact elim_iso z hiso (Or.inl hz1)
                    by_cases hiso2 : ∃ z ∈ S2, ∀ w, ¬ G.Adj z w
                    · obtain ⟨z, hz2, hiso⟩ := hiso2
                      exact elim_iso z hiso (Or.inr hz2)
                    have hdegS1 : ∀ z ∈ S1, G.degree z = 2 := by
                      intro z hz
                      apply hdeg2 z
                      by_contra hno
                      exact hiso1 ⟨z, hz, fun w hw => hno ⟨w, hw⟩⟩
                    have hdegS2 : ∀ z ∈ S2, G.degree z = 2 := by
                      intro z hz
                      apply hdeg2 z
                      by_contra hno
                      exact hiso2 ⟨z, hz, fun w hw => hno ⟨w, hw⟩⟩
                    have drop_monomial : ∀ (Sbad Skeep : Finset (Fin n)) (pbad pkeep : ℕ),
                        g1.inputs = [pbad, pkeep] ∨ g1.inputs = [pkeep, pbad] →
                        pbad < n + j1 → pkeep < n + j1 →
                        (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD pbad false = decide (∀ u ∈ Sbad, x u = true)) →
                        (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD pkeep false = decide (∀ u ∈ Skeep, x u = true)) →
                        (∀ u v : Fin n, G.Adj u v → ¬ Sbad ⊆ {u, v}) →
                        G.edgeSet.ncard ≤ A.card + 1 := by
                      intro Sbad Skeep pbad pkeep hord hpb_lt hpk_lt hpb_s hpk_s hnoedge
                      set g' : Gate := ⟨GateOp.and, [pkeep]⟩
                      set C' : Circuit := ⟨C.gates.set j1 g', C.output⟩
                      have hC'mono := set_gate_mono_struct C hmono j1 g' rfl (by simp [g'])
                      have hA'card : (A.erase j1).card + 1 = A.card := Finset.card_erase_add_one hj1A
                      have hC'fun : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
                        intro x
                        constructor
                        · intro ht
                          rw [← hfun]
                          apply set_gate_le C hmono j1 hj1_lt g' rfl x
                          · intro hk
                            rw [wires_gate_ofFn C x j1 g1 hg1, hor1]
                            change (g'.inputs.map fun i => if i < n + j1 then (C.wires (List.ofFn x)).getD i false else false).all id = true at hk
                            simp only [g', List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hpk_lt, ↓reduceIte] at hk
                            rcases hord with h1 | h1 <;> rw [h1]
                            · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hpk_lt, ↓reduceIte, hk, Bool.or_true, Bool.true_or]
                            · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hpk_lt, ↓reduceIte, hk, Bool.true_or]
                          · exact ht
                        · rintro ⟨u, v, huv, hu, hv⟩
                          set xuv : Fin n → Bool := fun t => decide (t = u ∨ t = v)
                          have hbad0 : (C.wires (List.ofFn xuv)).getD pbad false = false := by
                            rw [hpb_s xuv, decide_eq_false_iff_not]
                            intro hsub
                            apply hnoedge u v huv
                            intro t ht
                            have := hsub t ht
                            simpa [xuv] using this
                          have heq0 : g'.op.eval (g'.inputs.map fun i => if i < n + j1 then (C.wires (List.ofFn xuv)).getD i false else false) =
                              (C.wires (List.ofFn xuv)).getD (n + j1) false := by
                            rw [wires_gate_ofFn C xuv j1 g1 hg1, hor1]
                            rcases hord with h1 | h1 <;> rw [h1]
                            · simp only [g', GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, hpb_lt, hpk_lt, ↓reduceIte, hbad0, Bool.and_true, Bool.false_or, Bool.or_false]
                            · simp only [g', GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, hpb_lt, hpk_lt, ↓reduceIte, hbad0, Bool.and_true, Bool.or_false]
                          have htuv : C'.eval (List.ofFn xuv) = true := by
                            change (C'.wires (List.ofFn xuv)).getD C.output false = true
                            rw [set_gate_eq C j1 hj1_lt g' xuv heq0 C.output]
                            exact (hfun xuv).mpr ⟨u, v, huv, by simp [xuv], by simp [xuv]⟩
                          apply eval_mono C' hC'mono xuv x _ htuv
                          intro t ht
                          simp only [xuv, decide_eq_true_eq] at ht
                          rcases ht with rfl | rfl <;> assumption
                      have hrec := ih (G.edgeSet.ncard + (A.erase j1).card) (by omega) G C' (A.erase j1) rfl
                        hpf hno4 hC'mono hC'fun (set_gate_or_subset C A hA j1 g' rfl)
                      omega
                    by_cases hS1drop : ∀ u v : Fin n, G.Adj u v → ¬ S1 ⊆ {u, v}
                    · exact drop_monomial S1 S2 p q (Or.inl hinp) hplt hqlt hpsnd hqsnd hS1drop
                    by_cases hS2drop : ∀ u v : Fin n, G.Adj u v → ¬ S2 ⊆ {u, v}
                    · exact drop_monomial S2 S1 q p (Or.inr hinp) hqlt hplt hqsnd hpsnd hS2drop
                    have hS1class : (∃ a : Fin n, S1 = {a}) ∨ (∃ a c : Fin n, G.Adj a c ∧ S1 = {a, c}) := by
                      have hcard2 : S1.card ≤ 2 := by
                        by_contra hgt
                        apply hS1drop
                        intro u v _ hsub
                        have := Finset.card_le_card hsub
                        have h2 : ({u, v} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
                        omega
                      have hpos1 : 1 ≤ S1.card := Finset.Nonempty.card_pos hS1ne
                      by_cases hc1 : S1.card = 1
                      · exact Or.inl (Finset.card_eq_one.mp hc1)
                      · have hc2 : S1.card = 2 := by omega
                        by_contra hnot
                        apply hS1drop
                        intro u v huv hsub
                        have hpair : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair (G.ne_of_adj huv)
                        have heq : S1 = {u, v} := Finset.eq_of_subset_of_card_le hsub (by omega)
                        exact hnot (Or.inr ⟨u, v, huv, heq⟩)
                    have hS2class : (∃ b : Fin n, S2 = {b}) ∨ (∃ b d : Fin n, G.Adj b d ∧ S2 = {b, d}) := by
                      have hcard2 : S2.card ≤ 2 := by
                        by_contra hgt
                        apply hS2drop
                        intro u v _ hsub
                        have := Finset.card_le_card hsub
                        have h2 : ({u, v} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
                        omega
                      have hpos2 : 1 ≤ S2.card := Finset.Nonempty.card_pos hS2ne
                      by_cases hc1 : S2.card = 1
                      · exact Or.inl (Finset.card_eq_one.mp hc1)
                      · have hc2 : S2.card = 2 := by omega
                        by_contra hnot
                        apply hS2drop
                        intro u v huv hsub
                        have hpair : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair (G.ne_of_adj huv)
                        have heq : S2 = {u, v} := Finset.eq_of_subset_of_card_le hsub (by omega)
                        exact hnot (Or.inr ⟨u, v, huv, heq⟩)
                    have edge_branch : ∀ (Sedge Sother : Finset (Fin n)) (pedge pother : ℕ),
                        g1.inputs = [pedge, pother] ∨ g1.inputs = [pother, pedge] →
                        pedge < n + j1 → pother < n + j1 →
                        (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD pedge false = decide (∀ u ∈ Sedge, x u = true)) →
                        (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD pother false = decide (∀ u ∈ Sother, x u = true)) →
                        (∀ z ∈ Sedge, G.degree z = 2) →
                        ¬ Sedge ⊆ Sother →
                        (∃ a c : Fin n, G.Adj a c ∧ Sedge = {a, c}) →
                        G.edgeSet.ncard ≤ A.card + 1 := by
                      intro Sedge Sother pedge pother hord hpe_lt hpo_lt hpe_s hpo_s hdegE hnot_sub ⟨a0, c0, hac0, hSe⟩
                      obtain ⟨a, haE, haNot⟩ := Finset.not_subset.mp hnot_sub
                      have ha_or : a = a0 ∨ a = c0 := by
                        rw [hSe, Finset.mem_insert, Finset.mem_singleton] at haE; exact haE
                      obtain ⟨c, hac, hSe'⟩ : ∃ c : Fin n, G.Adj a c ∧ Sedge = {a, c} := by
                        rcases ha_or with rfl | rfl
                        · exact ⟨c0, hac0, hSe⟩
                        · exact ⟨a0, hac0.symm, by rw [hSe, Finset.pair_comm]⟩
                      obtain ⟨w1, w2, hw12, haw1, haw2, halla⟩ := deg_two_neighbors G a (hdegE a haE)
                      have hca : c = w1 ∨ c = w2 := (halla c).mp hac
                      obtain ⟨w, haw, hwc⟩ : ∃ w : Fin n, G.Adj a w ∧ w ≠ c := by
                        rcases hca with rfl | rfl
                        · exact ⟨w2, haw2, hw12.symm⟩
                        · exact ⟨w1, haw1, hw12⟩
                      have haw_ne : a ≠ w := G.ne_of_adj haw
                      have hac_ne : a ≠ c := G.ne_of_adj hac
                      apply kill_two_and_rec a pedge (hdegE a haE)
                      · rcases hord with h1 | h1 <;> rw [h1] <;> simp
                      · exact hpe_lt
                      · intro z hza
                        rw [hpe_s z, decide_eq_false_iff_not]
                        intro h; have := h a haE; rw [hza] at this; exact absurd this (by decide)
                      · set xw : Fin n → Bool := fun t => decide (t = w)
                        refine ⟨xw, ?_, ?_, ?_⟩
                        · cases h : C.eval (List.ofFn xw) with
                          | false => rfl
                          | true =>
                            obtain ⟨u, v, huv, hu, hv⟩ := (hfun xw).mp h
                            simp only [xw, decide_eq_true_eq] at hu hv
                            subst hu; subst hv
                            exact absurd huv (G.loopless.irrefl _)
                        · rw [hfun]
                          exact ⟨a, w, haw, Function.update_self a true xw, by rw [Function.update_of_ne haw_ne.symm]; simp [xw]⟩
                        · have hpe0 : (C.wires (List.ofFn xw)).getD pedge false = false := by
                            rw [hpe_s xw, decide_eq_false_iff_not]
                            intro h
                            have hc := h c (by rw [hSe']; simp)
                            simp only [xw, decide_eq_true_eq] at hc
                            exact hwc hc.symm
                          have hpe1 : (C.wires (List.ofFn (Function.update xw a true))).getD pedge false = false := by
                            rw [hpe_s _, decide_eq_false_iff_not]
                            intro h
                            have hc := h c (by rw [hSe']; simp)
                            rw [Function.update_of_ne hac_ne.symm] at hc
                            simp only [xw, decide_eq_true_eq] at hc
                            exact hwc hc.symm
                          have hpoeq : (C.wires (List.ofFn xw)).getD pother false =
                              (C.wires (List.ofFn (Function.update xw a true))).getD pother false := by
                            rw [hpo_s xw, hpo_s _]
                            congr 1
                            apply propext
                            constructor
                            · intro h u hu
                              have hua : u ≠ a := fun heq => haNot (heq ▸ hu)
                              rw [Function.update_of_ne hua]; exact h u hu
                            · intro h u hu
                              have hua : u ≠ a := fun heq => haNot (heq ▸ hu)
                              have := h u hu
                              rwa [Function.update_of_ne hua] at this
                          rw [wires_gate_ofFn C xw j1 g1 hg1, wires_gate_ofFn C _ j1 g1 hg1, hor1]
                          rcases hord with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hpe_lt, hpo_lt, ↓reduceIte, hpe0, hpe1, hpoeq]
                    rcases hS1class with ⟨a, rfl⟩ | hS1edge
                    · rcases hS2class with ⟨b, rfl⟩ | hS2edge
                      · have hab : a ≠ b := fun h => hS1sub (by simp [h])
                        have hdega : G.degree a = 2 := hdegS1 a (Finset.mem_singleton_self a)
                        have hdegb : G.degree b = 2 := hdegS2 b (Finset.mem_singleton_self b)
                        obtain ⟨w1, w2, hw12, haw1, haw2, halla⟩ := deg_two_neighbors G a hdega
                        by_cases hgood : ∃ w : Fin n, G.Adj a w ∧ w ≠ b ∧ ¬ G.Adj b w
                        · obtain ⟨w, haw, hwb, hnbw⟩ := hgood
                          have haw_ne : a ≠ w := G.ne_of_adj haw
                          apply kill_two_and_rec a p hdega (by rw [hinp]; simp) hplt
                          · intro z hza
                            rw [hpsnd z, decide_eq_false_iff_not]
                            intro h; have := h a (Finset.mem_singleton_self a); rw [hza] at this; exact absurd this (by decide)
                          · set xbw : Fin n → Bool := fun t => decide (t = b ∨ t = w)
                            refine ⟨xbw, ?_, ?_, ?_⟩
                            · cases h : C.eval (List.ofFn xbw) with
                              | false => rfl
                              | true =>
                                obtain ⟨u, v, huv, hu, hv⟩ := (hfun xbw).mp h
                                simp only [xbw, decide_eq_true_eq] at hu hv
                                rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
                                · exact absurd huv (G.loopless.irrefl _)
                                · exact absurd huv hnbw
                                · exact absurd huv.symm hnbw
                                · exact absurd huv (G.loopless.irrefl _)
                            · rw [hfun]
                              exact ⟨a, w, haw, Function.update_self a true xbw, by rw [Function.update_of_ne haw_ne.symm]; simp [xbw]⟩
                            · have hq1 : (C.wires (List.ofFn xbw)).getD q false = true := by
                                rw [hqsnd xbw, decide_eq_true_eq]
                                intro u hu; rw [Finset.mem_singleton.mp hu]; simp [xbw]
                              have hq2 : (C.wires (List.ofFn (Function.update xbw a true))).getD q false = true := by
                                rw [hqsnd _, decide_eq_true_eq]
                                intro u hu; rw [Finset.mem_singleton.mp hu, Function.update_of_ne hab.symm]; simp [xbw]
                              rw [wires_gate_ofFn C xbw j1 g1 hg1, wires_gate_ofFn C _ j1 g1 hg1, hor1, hinp]
                              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hplt, hqlt, ↓reduceIte, hq1, hq2, Bool.or_true, Bool.true_or]
                        · have hbw1 : w1 = b ∨ G.Adj b w1 := by
                            by_contra h; push Not at h; exact hgood ⟨w1, haw1, h.1, h.2⟩
                          have hbw2 : w2 = b ∨ G.Adj b w2 := by
                            by_contra h; push Not at h; exact hgood ⟨w2, haw2, h.1, h.2⟩
                          obtain ⟨c, hab_adj, hac_adj, hbc_adj⟩ : ∃ c : Fin n, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
                            rcases hbw1 with rfl | hb1
                            · rcases hbw2 with h2 | hb2
                              · exact absurd h2.symm hw12
                              · exact ⟨w2, haw1, haw2, hb2⟩
                            · rcases hbw2 with rfl | hb2
                              · exact ⟨w1, haw2, haw1, hb1⟩
                              · exact absurd (no_four_cycle_common G hno4 a b w1 w2 hab hw12 haw1 haw2 hb1 hb2) id
                          have hac_ne : a ≠ c := G.ne_of_adj hac_adj
                          have hbc_ne : b ≠ c := G.ne_of_adj hbc_adj
                          have hdegc : G.degree c = 2 := hdeg2 c ⟨a, hac_adj.symm⟩
                          have hNa : ∀ w, G.Adj a w ↔ w = b ∨ w = c := by
                            obtain ⟨x1, x2, hxne, hax1, hax2, hallx⟩ := deg_two_neighbors G a hdega
                            have hb_in := (hallx b).mp hab_adj
                            have hc_in := (hallx c).mp hac_adj
                            intro w
                            rw [hallx w]
                            rcases hb_in with rfl | rfl <;> rcases hc_in with rfl | rfl
                            · exact absurd rfl hbc_ne
                            · rfl
                            · exact or_comm
                            · exact absurd rfl hbc_ne
                          have hNb : ∀ w, G.Adj b w ↔ w = a ∨ w = c := by
                            obtain ⟨x1, x2, hxne, hbx1, hbx2, hallx⟩ := deg_two_neighbors G b hdegb
                            have ha_in := (hallx a).mp hab_adj.symm
                            have hc_in := (hallx c).mp hbc_adj
                            intro w
                            rw [hallx w]
                            rcases ha_in with rfl | rfl <;> rcases hc_in with rfl | rfl
                            · exact absurd rfl hac_ne
                            · rfl
                            · exact or_comm
                            · exact absurd rfl hac_ne
                          have hNc : ∀ w, G.Adj c w ↔ w = a ∨ w = b := by
                            obtain ⟨x1, x2, hxne, hcx1, hcx2, hallx⟩ := deg_two_neighbors G c hdegc
                            have ha_in := (hallx a).mp hac_adj.symm
                            have hb_in := (hallx b).mp hbc_adj.symm
                            intro w
                            rw [hallx w]
                            rcases ha_in with rfl | rfl <;> rcases hb_in with rfl | rfl
                            · exact absurd rfl hab
                            · rfl
                            · exact or_comm
                            · exact absurd rfl hab
                          set G1 := delVert G a
                          set G2 := delVert G1 b
                          have hG1degb : G1.degree b = 1 := by
                            rw [SimpleGraph.degree, Finset.card_eq_one]
                            refine ⟨c, ?_⟩
                            ext w
                            rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
                            simp only [G1, delVert, hNb]
                            constructor
                            · rintro ⟨rfl | rfl, _, hwa⟩
                              · exact absurd rfl hwa
                              · rfl
                            · rintro rfl
                              exact ⟨Or.inr rfl, hab.symm, hac_ne.symm⟩
                          have hG2card : G2.edgeSet.ncard + 3 = G.edgeSet.ncard := by
                            have h1 : G1.edgeSet.ncard + G.degree a = G.edgeSet.ncard := delVert_edge_card G a
                            have h2 : G2.edgeSet.ncard + G1.degree b = G1.edgeSet.ncard := delVert_edge_card G1 b
                            rw [hdega] at h1
                            rw [hG1degb] at h2
                            omega
                          have hG2le : G2 ≤ G := le_trans (delVert_le G1 b) (delVert_le G a)
                          have hG2no_c : ∀ u v : Fin n, G2.Adj u v → u ≠ c ∧ v ≠ c := by
                            intro u v huv
                            have hGuv : G.Adj u v := hG2le huv
                            have hua : u ≠ a := huv.1.2.1
                            have hva : v ≠ a := huv.1.2.2
                            have hub : u ≠ b := huv.2.1
                            have hvb : v ≠ b := huv.2.2
                            refine ⟨?_, ?_⟩
                            · intro huc; subst huc
                              rcases (hNc v).mp hGuv with rfl | rfl
                              · exact hva rfl
                              · exact hvb rfl
                            · intro hvc; subst hvc
                              rcases (hNc u).mp hGuv.symm with rfl | rfl
                              · exact hua rfl
                              · exact hub rfl
                          have hout_ne_a : C.output ≠ a.val := by
                            intro hoa
                            have hfa : C.eval (List.ofFn (fun t : Fin n => decide (t = a))) = false := by
                              cases h : C.eval (List.ofFn (fun t : Fin n => decide (t = a))) with
                              | false => rfl
                              | true =>
                                obtain ⟨u, v, huv, hu, hv⟩ := (hfun _).mp h
                                simp only [decide_eq_true_eq] at hu hv
                                subst hu; subst hv
                                exact absurd huv (G.loopless.irrefl _)
                            unfold Circuit.eval at hfa
                            rw [hoa, wires_input C _ a.val a.isLt] at hfa
                            simp at hfa
                          set C1 := rtCircuit C a j1
                          have hC1mono := rtCircuit_mono C hmono a j1
                          have hC1or := rtCircuit_or_subset C A hA a j1
                          have hC1eval : ∀ x : Fin n → Bool, C1.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x a true)) := by
                            intro x
                            unfold Circuit.eval
                            change ((rtCircuit C a j1).wires (List.ofFn x)).getD C.output false = _
                            exact rtCircuit_wires C hmono a j1 p g1 hg1 hor1 (by rw [hinp]; simp) hplt
                              (fun z hza => by rw [hpsnd z, decide_eq_true_eq]; intro u hu; rw [Finset.mem_singleton.mp hu]; exact hza)
                              x C.output hout_ne_a
                          have hC1fun : ∀ x : Fin n → Bool, C1.eval (List.ofFn x) = true ↔
                              x b = true ∨ x c = true ∨ ∃ u v : Fin n, G2.Adj u v ∧ x u = true ∧ x v = true := by
                            intro x
                            rw [hC1eval x, hfun]
                            constructor
                            · rintro ⟨u, v, huv, hu, hv⟩
                              by_cases hua : u = a
                              · subst hua
                                rcases (hNa v).mp huv with rfl | rfl
                                · rw [Function.update_of_ne hab.symm] at hv; exact Or.inl hv
                                · rw [Function.update_of_ne hac_ne.symm] at hv; exact Or.inr (Or.inl hv)
                              · by_cases hva : v = a
                                · subst hva
                                  rcases (hNa u).mp huv.symm with rfl | rfl
                                  · rw [Function.update_of_ne hab.symm] at hu; exact Or.inl hu
                                  · rw [Function.update_of_ne hac_ne.symm] at hu; exact Or.inr (Or.inl hu)
                                · rw [Function.update_of_ne hua] at hu
                                  rw [Function.update_of_ne hva] at hv
                                  by_cases hub : u = b
                                  · subst hub; exact Or.inl hu
                                  · by_cases hvb : v = b
                                    · subst hvb; exact Or.inl hv
                                    · exact Or.inr (Or.inr ⟨u, v, ⟨⟨huv, hua, hva⟩, hub, hvb⟩, hu, hv⟩)
                            · rintro (hb | hc | ⟨u, v, huv2, hu, hv⟩)
                              · exact ⟨a, b, hab_adj, Function.update_self a true x, by rw [Function.update_of_ne hab.symm]; exact hb⟩
                              · exact ⟨a, c, hac_adj, Function.update_self a true x, by rw [Function.update_of_ne hac_ne.symm]; exact hc⟩
                              · exact ⟨u, v, hG2le huv2, by rw [Function.update_of_ne huv2.1.2.1]; exact hu, by rw [Function.update_of_ne huv2.1.2.2]; exact hv⟩
                          have hC1_0 : C1.eval (List.ofFn (fun _ : Fin n => false)) = false := by
                            cases h : C1.eval (List.ofFn (fun _ : Fin n => false)) with
                            | false => rfl
                            | true =>
                              rcases (hC1fun _).mp h with hb | hc | ⟨_, _, _, hu, _⟩ <;> exact absurd (by assumption) (by decide)
                          have hC1_b : C1.eval (List.ofFn (Function.update (fun _ : Fin n => false) b true)) = true := by
                            rw [hC1fun]; exact Or.inl (by simp)
                          have hC1_c : C1.eval (List.ofFn (fun t : Fin n => decide (t = c))) = true := by
                            rw [hC1fun]; exact Or.inr (Or.inl (by simp))
                          obtain ⟨jb, gb, ib, hjb, horb, _, hibm, hiblt, hibz⟩ :=
                            find_or_gate_avoid n C1 b none hC1mono (fun _ => false) ⟨hC1_0, hC1_b⟩
                              (by intro _ h; cases h) (fun t => decide (t = c)) (by simp [hbc_ne]) hC1_c
                          have hjbA1 : jb ∈ A.erase j1 := hC1or jb gb hjb horb
                          have hA1card : (A.erase j1).card + 1 = A.card := Finset.card_erase_add_one hj1A
                          by_cases hG2zero : G2.edgeSet.ncard = 0
                          · have hA1pos : 1 ≤ (A.erase j1).card := Finset.card_pos.mpr ⟨jb, hjbA1⟩
                            omega
                          · have hG2ne : G2.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero hG2zero
                            obtain ⟨e2, he2⟩ := hG2ne
                            induction e2 using Sym2.ind with
                            | _ u0 v0 =>
                              have huv0 : G2.Adj u0 v0 := he2
                              have huc0 := (hG2no_c u0 v0 huv0).1
                              have hvc0 := (hG2no_c u0 v0 huv0).2
                              set C2 := rfCircuit C1 b {jb} (fun _ => ib)
                              have hKb : ∀ j ∈ ({jb} : Finset ℕ), ∃ g : Gate, C1.gates[j]? = some g ∧ g.op = GateOp.or ∧
                                  ib ∈ g.inputs ∧ ib < n + j ∧ ∀ z : Fin n → Bool, z b = false → (C1.wires (List.ofFn z)).getD ib false = false := by
                                intro j hj; rw [Finset.mem_singleton] at hj; subst hj; exact ⟨gb, hjb, horb, hibm, hiblt, hibz⟩
                              have hC2mono := rfCircuit_mono C1 hC1mono b {jb} (fun _ => ib)
                              have hC2or := rfCircuit_or_subset C1 (A.erase j1) hC1or b {jb} (fun _ => ib)
                              have hC2fun : ∀ x : Fin n → Bool, C2.eval (List.ofFn x) = true ↔
                                  x c = true ∨ ∃ u v : Fin n, G2.Adj u v ∧ x u = true ∧ x v = true := by
                                intro x
                                rw [rfCircuit_eval C1 hC1mono b {jb} (fun _ => ib) hKb x, hC1fun]
                                constructor
                                · rintro (hb | hc | ⟨u, v, huv2, hu, hv⟩)
                                  · rw [Function.update_self] at hb; exact absurd hb (by decide)
                                  · rw [Function.update_of_ne hbc_ne.symm] at hc; exact Or.inl hc
                                  · rw [Function.update_of_ne huv2.2.1] at hu
                                    rw [Function.update_of_ne huv2.2.2] at hv
                                    exact Or.inr ⟨u, v, huv2, hu, hv⟩
                                · rintro (hc | ⟨u, v, huv2, hu, hv⟩)
                                  · exact Or.inr (Or.inl (by rw [Function.update_of_ne hbc_ne.symm]; exact hc))
                                  · exact Or.inr (Or.inr ⟨u, v, huv2, by rw [Function.update_of_ne huv2.2.1]; exact hu, by rw [Function.update_of_ne huv2.2.2]; exact hv⟩)
                              have hC2_0 : C2.eval (List.ofFn (fun _ : Fin n => false)) = false := by
                                cases h : C2.eval (List.ofFn (fun _ : Fin n => false)) with
                                | false => rfl
                                | true =>
                                  rcases (hC2fun _).mp h with hc | ⟨_, _, _, hu, _⟩ <;> exact absurd (by assumption) (by decide)
                              have hC2_c : C2.eval (List.ofFn (Function.update (fun _ : Fin n => false) c true)) = true := by
                                rw [hC2fun]; exact Or.inl (by simp)
                              have hC2_e : C2.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true := by
                                rw [hC2fun]; exact Or.inr ⟨u0, v0, huv0, by simp, by simp⟩
                              have hyc : (fun t : Fin n => decide (t = u0 ∨ t = v0)) c = false := by
                                simp [huc0.symm, hvc0.symm]
                              obtain ⟨jc, gc, ic, hjc, horc, _, hicm, hiclt, hicz⟩ :=
                                find_or_gate_avoid n C2 c none hC2mono (fun _ => false) ⟨hC2_0, hC2_c⟩
                                  (by intro _ h; cases h) (fun t => decide (t = u0 ∨ t = v0)) hyc hC2_e
                              set C3 := rfCircuit C2 c {jc} (fun _ => ic)
                              have hKc : ∀ j ∈ ({jc} : Finset ℕ), ∃ g : Gate, C2.gates[j]? = some g ∧ g.op = GateOp.or ∧
                                  ic ∈ g.inputs ∧ ic < n + j ∧ ∀ z : Fin n → Bool, z c = false → (C2.wires (List.ofFn z)).getD ic false = false := by
                                intro j hj; rw [Finset.mem_singleton] at hj; subst hj; exact ⟨gc, hjc, horc, hicm, hiclt, hicz⟩
                              have hC3fun : ∀ x : Fin n → Bool, C3.eval (List.ofFn x) = true ↔
                                  ∃ u v : Fin n, G2.Adj u v ∧ x u = true ∧ x v = true := by
                                intro x
                                rw [rfCircuit_eval C2 hC2mono c {jc} (fun _ => ic) hKc x, hC2fun]
                                constructor
                                · rintro (hc | ⟨u, v, huv2, hu, hv⟩)
                                  · rw [Function.update_self] at hc; exact absurd hc (by decide)
                                  · rw [Function.update_of_ne (hG2no_c u v huv2).1] at hu
                                    rw [Function.update_of_ne (hG2no_c u v huv2).2] at hv
                                    exact ⟨u, v, huv2, hu, hv⟩
                                · rintro ⟨u, v, huv2, hu, hv⟩
                                  exact Or.inr ⟨u, v, huv2, by rw [Function.update_of_ne (hG2no_c u v huv2).1]; exact hu, by rw [Function.update_of_ne (hG2no_c u v huv2).2]; exact hv⟩
                              set A2 := (A.erase j1) \ {jb}
                              set A3 := A2 \ {jc}
                              have hA2card : A2.card + 1 = (A.erase j1).card := by
                                rw [show A2 = (A.erase j1).erase jb from Finset.sdiff_singleton_eq_erase jb _]
                                exact Finset.card_erase_add_one hjbA1
                              have hjcA2 : jc ∈ A2 := hC2or jc gc hjc horc
                              have hA3card : A3.card + 1 = A2.card := by
                                rw [show A3 = A2.erase jc from Finset.sdiff_singleton_eq_erase jc A2]
                                exact Finset.card_erase_add_one hjcA2
                              have hrec := ih (G2.edgeSet.ncard + A3.card) (by omega) G2 C3 A3 rfl
                                (subgraph_hpf G G2 hG2le hpf)
                                (subgraph_hno4 G G2 hG2le hno4)
                                (rfCircuit_mono C2 hC2mono c {jc} (fun _ => ic))
                                hC3fun
                                (rfCircuit_or_subset C2 A2 hC2or c {jc} (fun _ => ic))
                              omega
                      · exact edge_branch S2 {a} q p (Or.inr hinp) hqlt hplt hqsnd hpsnd hdegS2 hS2sub hS2edge
                    · exact edge_branch S1 S2 p q (Or.inl hinp) hplt hqlt hpsnd hqsnd hdegS1 hS1sub hS1edge
          · apply elim_j1 ⟨GateOp.and, [p]⟩ rfl (by simp)
            intro x
            rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
            simp [GateOp.eval, hqlt]
        · apply elim_j1 ⟨GateOp.and, [q]⟩ rfl (by simp)
          intro x
          rw [wires_gate_ofFn C x j1 g1 hg1, hor1, hinp]
          simp [GateOp.eval, hplt]
      · rw [hinp] at hlen1; simp at hlen1

end LMeta599

theorem PEqualNP.Outside.L_meta_599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 := by
  intro n G C A hpf hno4 hmono hfun hA
  exact LMeta599.main_thm n (G.edgeSet.ncard + A.card) G C A rfl hpf hno4 hmono hfun hA
