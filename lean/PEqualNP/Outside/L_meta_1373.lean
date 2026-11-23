import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1373

open PEqualNP.CircuitLowerBounds

private def foldWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem foldWires_eq_wires (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (foldWires gs x).getD o false := rfl

private theorem foldWires_length (gs : List Gate) (x : List Bool) :
    (foldWires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [foldWires]
  | append_singleton gs g ih =>
    simp only [foldWires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    change (foldWires gs x).length + 1 = x.length + (gs.length + 1)
    rw [ih]; omega

private theorem foldWires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    foldWires (gs ++ [g]) x =
      foldWires gs x ++ [g.op.eval (g.inputs.map fun i => (foldWires gs x).getD i false)] := by
  simp [foldWires]

private theorem getD_append_singleton {α : Type*} (l : List α) (a d : α) (w : ℕ) :
    (l ++ [a]).getD w d = if w < l.length then l.getD w d else if w = l.length then a else d := by
  by_cases h1 : w < l.length
  · simp only [h1, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h1,
      ← List.getD_eq_getElem _ _ h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : w = l.length
    · subst h2
      simp only [↓reduceIte]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp
    · simp only [h2, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by simp; omega)]

private theorem foldWires_prefix_getD (gs hs : List Gate) (x : List Bool) {w : ℕ}
    (hw : w < x.length + gs.length) :
    (foldWires (gs ++ hs) x).getD w false = (foldWires gs x).getD w false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs h ih =>
    rw [← List.append_assoc, foldWires_snoc, getD_append_singleton]
    have hlen : w < (foldWires (gs ++ hs) x).length := by
      rw [foldWires_length, List.length_append]; omega
    simp only [hlen, ↓reduceIte]
    exact ih

private theorem foldWires_input (gs : List Gate) (x : List Bool) {w : ℕ}
    (hw : w < x.length) :
    (foldWires gs x).getD w false = x.getD w false := by
  simpa [foldWires] using foldWires_prefix_getD [] gs x (by simpa using hw)

private theorem foldWires_getD_gate (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length) :
    (foldWires gs x).getD (x.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i => (foldWires (gs.take k) x).getD i false) := by
  have hsplit : gs = (gs.take k ++ [gs[k]]) ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  have htk : (gs.take k).length = k := by simp [Nat.min_eq_left (Nat.le_of_lt hk)]
  conv_lhs => rw [hsplit]
  rw [foldWires_prefix_getD (gs.take k ++ [gs[k]]) (gs.drop (k + 1)) x (by simp; omega)]
  rw [foldWires_snoc, getD_append_singleton]
  have hlen : (foldWires (gs.take k) x).length = x.length + k := by
    rw [foldWires_length, htk]
  rw [hlen]
  simp

private theorem foldWires_mono {n : ℕ} (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ w : ℕ, (foldWires gs (List.ofFn x)).getD w false = true →
      (foldWires gs (List.ofFn y)).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [foldWires, List.foldl_nil] at hw ⊢
    by_cases hwn : w < n
    · have h1 : w < (List.ofFn x).length := by simp; omega
      have h2 : w < (List.ofFn y).length := by simp; omega
      rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn] at hw
      rw [List.getD_eq_getElem _ _ h2, List.getElem_ofFn]
      exact hxy ⟨w, hwn⟩ hw
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hw
      exact Bool.noConfusion hw
  | append_singleton gs g ih =>
    have hmono' : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hmono h (List.mem_append_left _ hh)
    have ih' := ih hmono'
    intro w hw
    rw [foldWires_snoc, getD_append_singleton] at hw ⊢
    have hlenx : (foldWires gs (List.ofFn x)).length = n + gs.length := by
      rw [foldWires_length]; simp
    have hleny : (foldWires gs (List.ofFn y)).length = n + gs.length := by
      rw [foldWires_length]; simp
    rw [hlenx] at hw
    rw [hleny]
    by_cases h1 : w < n + gs.length
    · simp only [h1, ↓reduceIte] at hw ⊢
      exact ih' w hw
    · simp only [h1, ↓reduceIte] at hw ⊢
      by_cases h2 : w = n + gs.length
      · simp only [h2, ↓reduceIte] at hw ⊢
        rcases hmono g (List.mem_append_right _ (List.mem_singleton_self g)) with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hw ⊢
          intro u hu
          exact ih' u (hw u hu)
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hw ⊢
          obtain ⟨u, hu, hvu⟩ := hw
          exact ⟨u, hu, ih' u hvu⟩
      · simp only [h2, ↓reduceIte] at hw ⊢
        exact hw

private theorem not_gate_antimono {n : ℕ} (gates : List Gate) (j0 : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j0)
    (hnot : (gates.get j0).op = GateOp.not)
    (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    Circuit.eval ⟨gates, n + j0.val⟩ (List.ofFn y) = true →
      Circuit.eval ⟨gates, n + j0.val⟩ (List.ofFn x) = true := by
  have hpre_mono : ∀ g ∈ gates.take j0.val, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hgm
    obtain ⟨k, hk, hgk⟩ := List.mem_iff_getElem.mp hgm
    have hkj : k < j0.val := by simp only [List.length_take] at hk; omega
    have hkl : k < gates.length := by omega
    have hge : gates.get ⟨k, hkl⟩ = g := by rw [← hgk, List.getElem_take]; rfl
    rcases (hg g (hge ▸ List.get_mem gates ⟨k, hkl⟩)).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have heq := huniq ⟨k, hkl⟩ (by rw [hge]; exact h)
      have : k = j0.val := congrArg Fin.val heq
      omega
  have hx : Circuit.eval ⟨gates, n + j0.val⟩ (List.ofFn x) =
      !(((gates[j0.val]'j0.isLt).inputs.map fun i =>
        (foldWires (gates.take j0.val) (List.ofFn x)).getD i false).headD false) := by
    rw [foldWires_eq_wires]
    have h := foldWires_getD_gate gates (List.ofFn x) j0.val j0.isLt
    simp only [List.length_ofFn] at h
    rw [h]
    have hop : (gates[j0.val]'j0.isLt).op = GateOp.not := hnot
    rw [hop]; rfl
  have hy : Circuit.eval ⟨gates, n + j0.val⟩ (List.ofFn y) =
      !(((gates[j0.val]'j0.isLt).inputs.map fun i =>
        (foldWires (gates.take j0.val) (List.ofFn y)).getD i false).headD false) := by
    rw [foldWires_eq_wires]
    have h := foldWires_getD_gate gates (List.ofFn y) j0.val j0.isLt
    simp only [List.length_ofFn] at h
    rw [h]
    have hop : (gates[j0.val]'j0.isLt).op = GateOp.not := hnot
    rw [hop]; rfl
  rw [hx, hy]
  cases hgi : (gates[j0.val]'j0.isLt).inputs with
  | nil => simp
  | cons a rest =>
    simp only [List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hyf
    by_cases hxv : (foldWires (gates.take j0.val) (List.ofFn x)).getD a false = true
    · have := foldWires_mono (gates.take j0.val) hpre_mono x y hxy a hxv
      rw [hyf] at this; exact Bool.noConfusion this
    · exact Bool.eq_false_iff.mpr hxv

private def remapOut (n len j0 o : ℕ) : ℕ :=
  if o < n + j0 then o else if o < n + len then o - 1 else n + len

private def dropFalseGate (n len j0 : ℕ) (gates : List Gate) (i : Fin (gates.length - 1)) : Gate :=
  if hlt : i.val < j0 then
    let g := gates[i.val]'(by omega)
    ⟨g.op, g.inputs.map (fun u => if u < n + i.val then u else n + len)⟩
  else
    let g := gates[i.val + 1]'(by omega)
    ⟨g.op, g.inputs.map (fun u =>
      if u < n + j0 then u
      else if u = n + j0 then n + len
      else if u < n + (i.val + 1) then u - 1
      else n + len)⟩

private theorem drop_gate_false {n : ℕ} (gates : List Gate) (j0 : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j0) :
    ∃ gs' : List Gate,
      gs'.length = gates.length - 1 ∧
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ (x : Fin n → Bool),
        Circuit.eval ⟨gates, n + j0.val⟩ (List.ofFn x) = false →
        ∀ (o : ℕ), o ≠ n + j0.val →
          Circuit.eval ⟨gs', remapOut n gates.length j0.val o⟩ (List.ofFn x) =
            Circuit.eval ⟨gates, o⟩ (List.ofFn x) := by
  let gs' : List Gate := List.ofFn (dropFalseGate n gates.length j0.val gates)
  refine ⟨gs', by simp [gs'], ?_, ?_⟩
  · intro g hgm
    simp only [gs', List.mem_ofFn] at hgm
    obtain ⟨i, rfl⟩ := hgm
    dsimp only [dropFalseGate]
    split_ifs with hlt
    · have hi : i.val < gates.length := by omega
      have hne : (⟨i.val, hi⟩ : Fin gates.length) ≠ j0 := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      obtain ⟨hop, hlen⟩ := hg (gates[i.val]'hi) (List.getElem_mem hi)
      refine ⟨?_, by simpa using hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (huniq ⟨i.val, hi⟩ h) hne
    · have hi : i.val + 1 < gates.length := by omega
      have hne : (⟨i.val + 1, hi⟩ : Fin gates.length) ≠ j0 := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      obtain ⟨hop, hlen⟩ := hg (gates[i.val + 1]'hi) (List.getElem_mem hi)
      refine ⟨?_, by simpa using hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (huniq ⟨i.val + 1, hi⟩ h) hne
  · intro x hxf
    have hwire : ∀ k : ℕ, k < gs'.length →
        (foldWires gs' (List.ofFn x)).getD (n + k) false =
          (foldWires gates (List.ofFn x)).getD (if k < j0.val then n + k else n + (k + 1)) false := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk
        have hklen : k < gates.length - 1 := by simpa [gs'] using hk
        have h1 := foldWires_getD_gate gs' (List.ofFn x) k hk
        simp only [List.length_ofFn] at h1
        rw [h1]
        have hgs_k : gs'[k]'hk = dropFalseGate n gates.length j0.val gates ⟨k, hklen⟩ := by
          simp [gs']
        rw [hgs_k]
        dsimp only [dropFalseGate]
        split_ifs with hlt
        · have hkl : k < gates.length := by omega
          have h2 := foldWires_getD_gate gates (List.ofFn x) k hkl
          simp only [List.length_ofFn] at h2
          rw [h2]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro u _
          dsimp only [Function.comp_apply]
          by_cases hu : u < n + k
          · simp only [hu, ↓reduceIte]
            rw [← foldWires_prefix_getD (gs'.take k) (gs'.drop k) (List.ofFn x)
                (by simp [Nat.min_eq_left (Nat.le_of_lt hk), hu]),
              List.take_append_drop,
              ← foldWires_prefix_getD (gates.take k) (gates.drop k) (List.ofFn x)
                (by simp [Nat.min_eq_left (Nat.le_of_lt hkl), hu]),
              List.take_append_drop]
            by_cases hun : u < n
            · rw [foldWires_input gs' (List.ofFn x) (by simp; omega),
                foldWires_input gates (List.ofFn x) (by simp; omega)]
            · have hr : u - n < k := by omega
              have hreq : n + (u - n) = u := by omega
              rw [← hreq, ih (u - n) hr (by omega)]
              simp [show u - n < j0.val by omega]
          · simp only [hu, ↓reduceIte]
            rw [List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
              List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega)]
        · have hkl : k + 1 < gates.length := by omega
          have h2 := foldWires_getD_gate gates (List.ofFn x) (k + 1) hkl
          simp only [List.length_ofFn] at h2
          rw [h2]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro u _
          dsimp only [Function.comp_apply]
          by_cases hu1 : u < n + j0.val
          · simp only [hu1, ↓reduceIte]
            rw [← foldWires_prefix_getD (gs'.take k) (gs'.drop k) (List.ofFn x)
                (by simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
              List.take_append_drop,
              ← foldWires_prefix_getD (gates.take (k + 1)) (gates.drop (k + 1)) (List.ofFn x)
                (by simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega),
              List.take_append_drop]
            by_cases hun : u < n
            · rw [foldWires_input gs' (List.ofFn x) (by simp; omega),
                foldWires_input gates (List.ofFn x) (by simp; omega)]
            · have hr : u - n < k := by omega
              have hreq : n + (u - n) = u := by omega
              rw [← hreq, ih (u - n) hr (by omega)]
              simp [show u - n < j0.val by omega]
          · simp only [hu1, ↓reduceIte]
            by_cases hu2 : u = n + j0.val
            · subst hu2
              simp only [↓reduceIte]
              rw [List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
                ← foldWires_prefix_getD (gates.take (k + 1)) (gates.drop (k + 1)) (List.ofFn x)
                  (by simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega),
                List.take_append_drop]
              exact hxf.symm
            · simp only [hu2, ↓reduceIte]
              by_cases hu3 : u < n + (k + 1)
              · simp only [hu3, ↓reduceIte]
                have hr : u - 1 - n < k := by omega
                have hreq1 : n + (u - 1 - n) = u - 1 := by omega
                have hreq2 : n + (u - 1 - n + 1) = u := by omega
                rw [← foldWires_prefix_getD (gs'.take k) (gs'.drop k) (List.ofFn x)
                    (by simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
                  List.take_append_drop,
                  ← foldWires_prefix_getD (gates.take (k + 1)) (gates.drop (k + 1)) (List.ofFn x)
                    (by simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega),
                  List.take_append_drop]
                rw [← hreq1, ih (u - 1 - n) hr (by omega)]
                have hge : ¬ (u - 1 - n < j0.val) := by omega
                simp only [hge, ↓reduceIte, hreq2]
              · simp only [hu3, ↓reduceIte]
                rw [List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
                  List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega)]
    intro o ho
    rw [foldWires_eq_wires, foldWires_eq_wires]
    dsimp only [remapOut]
    by_cases h1 : o < n + j0.val
    · simp only [h1, ↓reduceIte]
      by_cases hon : o < n
      · rw [foldWires_input gs' (List.ofFn x) (by simp; omega),
          foldWires_input gates (List.ofFn x) (by simp; omega)]
      · have hreq : n + (o - n) = o := by omega
        rw [← hreq, hwire (o - n) (by simp [gs']; omega)]
        simp [show o - n < j0.val by omega]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : o < n + gates.length
      · simp only [h2, ↓reduceIte]
        have hreq1 : n + (o - 1 - n) = o - 1 := by omega
        have hreq2 : n + (o - 1 - n + 1) = o := by omega
        rw [← hreq1, hwire (o - 1 - n) (by simp [gs']; omega)]
        have hge : ¬ (o - 1 - n < j0.val) := by omega
        simp only [hge, ↓reduceIte, hreq2]
      · simp only [h2, ↓reduceIte]
        rw [List.getD_eq_default _ _ (by rw [foldWires_length]; simp [gs']),
          List.getD_eq_default _ _ (by rw [foldWires_length]; simp; omega)]

private def dropTrueGate (n len j0 : ℕ) (gates : List Gate) (i : Fin (gates.length - 1)) : Gate :=
  if hlt : i.val < j0 then
    let g := gates[i.val]'(by omega)
    ⟨g.op, g.inputs.map (fun u => if u < n + i.val then u else n + len)⟩
  else
    let g := gates[i.val + 1]'(by omega)
    let rmHi := fun u =>
      if u < n + j0 then u
      else if u < n + (i.val + 1) then u - 1
      else n + len
    match g.op with
    | GateOp.and => ⟨GateOp.and, (g.inputs.filter (fun u => decide (u ≠ n + j0))).map rmHi⟩
    | GateOp.or =>
        if n + j0 ∈ g.inputs then ⟨GateOp.and, []⟩
        else ⟨GateOp.or, g.inputs.map rmHi⟩
    | op => ⟨op, g.inputs.map rmHi⟩

private theorem drop_gate_true {n : ℕ} (gates : List Gate) (j0 : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j0) :
    ∃ gs' : List Gate,
      gs'.length = gates.length - 1 ∧
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ (x : Fin n → Bool),
        Circuit.eval ⟨gates, n + j0.val⟩ (List.ofFn x) = true →
        ∀ (o : ℕ), o ≠ n + j0.val →
          Circuit.eval ⟨gs', remapOut n gates.length j0.val o⟩ (List.ofFn x) =
            Circuit.eval ⟨gates, o⟩ (List.ofFn x) := by
  let gs' : List Gate := List.ofFn (dropTrueGate n gates.length j0.val gates)
  refine ⟨gs', by simp [gs'], ?_, ?_⟩
  · intro g hgm
    simp only [gs', List.mem_ofFn] at hgm
    obtain ⟨i, rfl⟩ := hgm
    dsimp only [dropTrueGate]
    by_cases hlt : i.val < j0.val
    · simp only [hlt, ↓reduceDIte]
      have hi : i.val < gates.length := by omega
      have hne : (⟨i.val, hi⟩ : Fin gates.length) ≠ j0 := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      obtain ⟨hop, hlen⟩ := hg (gates[i.val]'hi) (List.getElem_mem hi)
      refine ⟨?_, by simpa using hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (huniq ⟨i.val, hi⟩ h) hne
    · simp only [hlt, ↓reduceDIte]
      have hi : i.val + 1 < gates.length := by omega
      have hne : (⟨i.val + 1, hi⟩ : Fin gates.length) ≠ j0 := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      obtain ⟨hop, hlen⟩ := hg (gates[i.val + 1]'hi) (List.getElem_mem hi)
      rcases hop with h | h | h
      · simp only [h]
        refine ⟨Or.inl trivial, ?_⟩
        simp only [List.length_map]
        exact le_trans (List.length_filter_le _ _) hlen
      · simp only [h]
        by_cases hmem : n + j0.val ∈ (gates[i.val + 1]'hi).inputs
        · simp only [hmem, ↓reduceIte]; exact ⟨Or.inl trivial, by simp⟩
        · simp only [hmem, ↓reduceIte]; exact ⟨Or.inr trivial, by simpa using hlen⟩
      · exact absurd (huniq ⟨i.val + 1, hi⟩ h) hne
  · intro x hxt
    have hwire : ∀ k : ℕ, k < gs'.length →
        (foldWires gs' (List.ofFn x)).getD (n + k) false =
          (foldWires gates (List.ofFn x)).getD (if k < j0.val then n + k else n + (k + 1)) false := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk
        have hklen : k < gates.length - 1 := by simpa [gs'] using hk
        have h1 := foldWires_getD_gate gs' (List.ofFn x) k hk
        simp only [List.length_ofFn] at h1
        rw [h1]
        have hgs_k : gs'[k]'hk = dropTrueGate n gates.length j0.val gates ⟨k, hklen⟩ := by
          simp [gs']
        rw [hgs_k]
        dsimp only [dropTrueGate]
        by_cases hlt : k < j0.val
        · simp only [hlt, ↓reduceDIte, ↓reduceIte]
          have hkl : k < gates.length := by omega
          have h2 := foldWires_getD_gate gates (List.ofFn x) k hkl
          simp only [List.length_ofFn] at h2
          rw [h2]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro u _
          dsimp only [Function.comp_apply]
          by_cases hu : u < n + k
          · simp only [hu, ↓reduceIte]
            rw [← foldWires_prefix_getD (gs'.take k) (gs'.drop k) (List.ofFn x)
                (by simp [Nat.min_eq_left (Nat.le_of_lt hk), hu]),
              List.take_append_drop,
              ← foldWires_prefix_getD (gates.take k) (gates.drop k) (List.ofFn x)
                (by simp [Nat.min_eq_left (Nat.le_of_lt hkl), hu]),
              List.take_append_drop]
            by_cases hun : u < n
            · rw [foldWires_input gs' (List.ofFn x) (by simp; omega),
                foldWires_input gates (List.ofFn x) (by simp; omega)]
            · have hr : u - n < k := by omega
              have hreq : n + (u - n) = u := by omega
              rw [← hreq, ih (u - n) hr (by omega)]
              simp [show u - n < j0.val by omega]
          · simp only [hu, ↓reduceIte]
            rw [List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
              List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega)]
        · simp only [hlt, ↓reduceDIte, ↓reduceIte]
          have hkl : k + 1 < gates.length := by omega
          have hne : (⟨k + 1, hkl⟩ : Fin gates.length) ≠ j0 := by
            intro h; have := congrArg Fin.val h; dsimp only at this; omega
          have h2 := foldWires_getD_gate gates (List.ofFn x) (k + 1) hkl
          simp only [List.length_ofFn] at h2
          rw [h2]
          let rmHi : ℕ → ℕ := fun u =>
            if u < n + j0.val then u
            else if u < n + (k + 1) then u - 1
            else n + gates.length
          have hrm_eq : ∀ u : ℕ, u ≠ n + j0.val →
              (foldWires (gs'.take k) (List.ofFn x)).getD (rmHi u) false =
                (foldWires (gates.take (k + 1)) (List.ofFn x)).getD u false := by
            intro u hu
            dsimp only [rmHi]
            by_cases hu1 : u < n + j0.val
            · simp only [hu1, ↓reduceIte]
              rw [← foldWires_prefix_getD (gs'.take k) (gs'.drop k) (List.ofFn x)
                  (by simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
                List.take_append_drop,
                ← foldWires_prefix_getD (gates.take (k + 1)) (gates.drop (k + 1)) (List.ofFn x)
                  (by simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega),
                List.take_append_drop]
              by_cases hun : u < n
              · rw [foldWires_input gs' (List.ofFn x) (by simp; omega),
                  foldWires_input gates (List.ofFn x) (by simp; omega)]
              · have hr : u - n < k := by omega
                have hreq : n + (u - n) = u := by omega
                rw [← hreq, ih (u - n) hr (by omega)]
                simp [show u - n < j0.val by omega]
            · simp only [hu1, ↓reduceIte]
              by_cases hu3 : u < n + (k + 1)
              · simp only [hu3, ↓reduceIte]
                have hr : u - 1 - n < k := by omega
                have hreq1 : n + (u - 1 - n) = u - 1 := by omega
                have hreq2 : n + (u - 1 - n + 1) = u := by omega
                rw [← foldWires_prefix_getD (gs'.take k) (gs'.drop k) (List.ofFn x)
                    (by simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
                  List.take_append_drop,
                  ← foldWires_prefix_getD (gates.take (k + 1)) (gates.drop (k + 1)) (List.ofFn x)
                    (by simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega),
                  List.take_append_drop]
                rw [← hreq1, ih (u - 1 - n) hr (by omega)]
                have hge : ¬ (u - 1 - n < j0.val) := by omega
                simp only [hge, ↓reduceIte, hreq2]
              · simp only [hu3, ↓reduceIte]
                rw [List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hk)]; omega),
                  List.getD_eq_default _ _ (by rw [foldWires_length]; simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega)]
          have hj0_val : (foldWires (gates.take (k + 1)) (List.ofFn x)).getD (n + j0.val) false = true := by
            rw [← foldWires_prefix_getD (gates.take (k + 1)) (gates.drop (k + 1)) (List.ofFn x)
                (by simp [Nat.min_eq_left (Nat.le_of_lt hkl)]; omega),
              List.take_append_drop]
            exact hxt
          obtain ⟨hop, _⟩ := hg (gates[k + 1]'hkl) (List.getElem_mem hkl)
          rcases hop with hop | hop | hop
          · simp only [hop]
            rw [Bool.eq_iff_iff]
            simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq,
              List.mem_filter, decide_eq_true_eq]
            constructor
            · intro h u hu
              by_cases huj : u = n + j0.val
              · subst huj; exact hj0_val
              · rw [← hrm_eq u huj]; exact h u ⟨hu, huj⟩
            · intro h u ⟨hu, huj⟩
              rw [hrm_eq u huj]; exact h u hu
          · simp only [hop]
            by_cases hmem : n + j0.val ∈ (gates[k + 1]'hkl).inputs
            · simp only [hmem, ↓reduceIte, GateOp.eval, List.map_nil, List.all_nil]
              symm
              simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
              exact ⟨n + j0.val, hmem, hj0_val⟩
            · simp only [hmem, ↓reduceIte]
              congr 1
              rw [List.map_map]
              apply List.map_congr_left
              intro u hu
              exact hrm_eq u (fun heq => hmem (heq ▸ hu))
          · exact absurd (huniq ⟨k + 1, hkl⟩ hop) hne
    intro o ho
    rw [foldWires_eq_wires, foldWires_eq_wires]
    dsimp only [remapOut]
    by_cases h1 : o < n + j0.val
    · simp only [h1, ↓reduceIte]
      by_cases hon : o < n
      · rw [foldWires_input gs' (List.ofFn x) (by simp; omega),
          foldWires_input gates (List.ofFn x) (by simp; omega)]
      · have hreq : n + (o - n) = o := by omega
        rw [← hreq, hwire (o - n) (by simp [gs']; omega)]
        simp [show o - n < j0.val by omega]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : o < n + gates.length
      · simp only [h2, ↓reduceIte]
        have hreq1 : n + (o - 1 - n) = o - 1 := by omega
        have hreq2 : n + (o - 1 - n + 1) = o := by omega
        rw [← hreq1, hwire (o - 1 - n) (by simp [gs']; omega)]
        have hge : ¬ (o - 1 - n < j0.val) := by omega
        simp only [hge, ↓reduceIte, hreq2]
      · simp only [h2, ↓reduceIte]
        rw [List.getD_eq_default _ _ (by rw [foldWires_length]; simp [gs']),
          List.getD_eq_default _ _ (by rw [foldWires_length]; simp; omega)]

private theorem plane_pair_line {q : ℕ} (S : Fin (q^2 + q + 1) → Finset (Fin (q^2 + q + 1)))
    (hcard : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (p0 p : Fin (q^2 + q + 1)) (hne : p ≠ p0) :
    ∃ i : Fin (q^2 + q + 1), p0 ∈ S i ∧ p ∈ S i := by
  let L0 := Finset.univ.filter (fun i => p0 ∈ S i)
  let U := L0.biUnion (fun i => (S i).erase p0)
  have hdisj : Set.PairwiseDisjoint (L0 : Set (Fin (q^2 + q + 1))) (fun i => (S i).erase p0) := by
    intro i hi j hj hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hi0 : p0 ∈ S i := (Finset.mem_filter.mp hi).2
    have hj0 : p0 ∈ S j := (Finset.mem_filter.mp hj).2
    have hxi' : x ∈ S i := Finset.mem_of_mem_erase hxi
    have hxj' : x ∈ S j := Finset.mem_of_mem_erase hxj
    have hxne : x ≠ p0 := Finset.ne_of_mem_erase hxi
    have hsub : ({x, p0} : Finset _) ⊆ S i ∩ S j := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hxi', hxj'⟩
      · exact Finset.mem_inter.mpr ⟨hi0, hj0⟩
    have h2 : 2 ≤ (S i ∩ S j).card := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hxne] at this
    have h1 := hinter i j hij
    omega
  have hUcard : U.card = q^2 + q := by
    rw [Finset.card_biUnion hdisj]
    have hterm : ∀ i ∈ L0, ((S i).erase p0).card = q := by
      intro i hi
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hi).2, hcard i]
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hdeg p0, smul_eq_mul]
    ring
  have hUsub : U ⊆ Finset.univ.erase p0 := by
    intro x hx
    simp only [U, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hxi, Finset.mem_univ x⟩
  have hEcard : (Finset.univ.erase p0).card = q^2 + q := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p0), Finset.card_univ, Fintype.card_fin]
    omega
  have hUeq : U = Finset.univ.erase p0 := Finset.eq_of_subset_of_card_le hUsub (by omega)
  have hpU : p ∈ U := by rw [hUeq]; exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ p⟩
  simp only [U, Finset.mem_biUnion] at hpU
  obtain ⟨i, hiL, hpi⟩ := hpU
  exact ⟨i, (Finset.mem_filter.mp hiL).2, Finset.mem_of_mem_erase hpi⟩

private theorem plane_meeting_bound {q : ℕ} (S : Fin (q^2 + q + 1) → Finset (Fin (q^2 + q + 1)))
    (hcard : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (A : Finset (Fin (q^2 + q + 1))) (hAne : A.Nonempty) :
    (Finset.univ.filter (fun i => ¬ Disjoint (S i) A)).card ≤ A.card * q + 1 := by
  obtain ⟨p0, hp0⟩ := hAne
  let L0 := Finset.univ.filter (fun i => p0 ∈ S i)
  let Rest := (A.erase p0).biUnion (fun p => (Finset.univ.filter (fun i => p ∈ S i)) \ L0)
  have hsub : Finset.univ.filter (fun i => ¬ Disjoint (S i) A) ⊆ L0 ∪ Rest := by
    intro i hi
    have hnd : ¬ Disjoint (S i) A := (Finset.mem_filter.mp hi).2
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨p, hpSi, hpA⟩ := hnd
    by_cases hp : p = p0
    · subst hp
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpSi⟩)
    · by_cases hiL : i ∈ L0
      · exact Finset.mem_union_left _ hiL
      · apply Finset.mem_union_right
        simp only [Rest, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_sdiff,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨p, ⟨hp, hpA⟩, hpSi, hiL⟩
  have hRest : Rest.card ≤ (A.card - 1) * q := by
    have h1 := Finset.card_biUnion_le (s := A.erase p0)
      (t := fun p => (Finset.univ.filter (fun i => p ∈ S i)) \ L0)
    have h2 : ∀ p ∈ A.erase p0, ((Finset.univ.filter (fun i => p ∈ S i)) \ L0).card ≤ q := by
      intro p hp
      have hpne : p ≠ p0 := Finset.ne_of_mem_erase hp
      obtain ⟨i0, hi0p0, hi0p⟩ := plane_pair_line S hcard hinter hdeg p0 p hpne
      have hi0_mem : i0 ∈ Finset.univ.filter (fun i => p ∈ S i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0p⟩
      have hi0_L0 : i0 ∈ L0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0p0⟩
      have hsub_e : (Finset.univ.filter (fun i => p ∈ S i)) \ L0 ⊆
          (Finset.univ.filter (fun i => p ∈ S i)).erase i0 := by
        intro i hi
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_erase.mpr ⟨fun heq => hi.2 (heq ▸ hi0_L0), hi.1⟩
      have hc := Finset.card_le_card hsub_e
      rw [Finset.card_erase_of_mem hi0_mem, hdeg p] at hc
      omega
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, Finset.card_erase_of_mem hp0, smul_eq_mul] at h3
    exact le_trans h1 h3
  have hcard1 := Finset.card_le_card hsub
  have hcard2 := Finset.card_union_le L0 Rest
  have hL0 : L0.card = q + 1 := hdeg p0
  have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨p0, hp0⟩
  have hmul : (A.card - 1) * q + (q + 1) = A.card * q + 1 := by
    have : A.card = (A.card - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  omega

theorem main_1373
    (H1 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (S i).card) →
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
      (∀ i : Fin m, c i ≤ k) →
      (∀ i : Fin m, c i + 1 ≤ (S i).card) →
      ∑ i : Fin m, c i ≤ C.size)
    (H2 : ∀ (n : ℕ) (gates : List Gate) (T Z : Finset (Fin n)),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∃ (gates' : List Gate) (r : ℕ → ℕ),
        (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        gates'.length ≤ gates.length ∧
        ∀ o : ℕ,
          (∃ x y : Fin n → Bool,
            Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠
            Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) →
          ∀ x : Fin n → Bool,
            Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
            Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)))
    (q : ℕ) (S : Fin (q^2 + q + 1) → Finset (Fin (q^2 + q + 1)))
    (gates : List Gate) (out : Fin (q^2 + q + 1) → ℕ)
    (hq : 2 ≤ q)
    (hcard : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (hgs : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot_uniq : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j)
    (hev : ∀ (w : Fin (q^2 + q + 1)) (x : Fin (q^2 + q + 1) → Bool),
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2 + q + 1) * min (w - 1) q) (q * ((q^2 + q + 1) - (w * q + 1))) ≤ gates.length := by
  let N := q^2 + q + 1
  have mono_full_bound : ∀ (gs : List Gate) (os : Fin N → ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ (i : Fin N) (x : Fin N → Bool), Circuit.eval ⟨gs, os i⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true)) →
      N * q ≤ gs.length := by
    intro gs os hgm hge
    obtain ⟨gs', r, hgs'2, hgs'len, hgs'ev⟩ := H2 N gs ∅ ∅ hgm
    have hok : ∀ (i : Fin N) (x : Fin N → Bool),
        Circuit.eval ⟨gs', r (os i)⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true) := by
      intro i x
      have hnc : ∃ x0 y0 : Fin N → Bool,
          Circuit.eval ⟨gs, os i⟩ (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else x0 j)) ≠
          Circuit.eval ⟨gs, os i⟩ (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else y0 j)) := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        simp only [Finset.notMem_empty, ↓reduceIte]
        rw [hge i, hge i]
        have hne : (S i).Nonempty := Finset.card_pos.mp (by rw [hcard i]; omega)
        obtain ⟨p, hp⟩ := hne
        simp; exact ⟨p, hp⟩
      have h1 := hgs'ev (os i) hnc x
      simp only [Finset.notMem_empty, ↓reduceIte] at h1
      rw [h1, hge i x]
    have hH1 := H1 N N q S ⟨gs', 0⟩ (fun i => r (os i)) (fun _ => q) hinter
      (fun i => by rw [hcard i]; omega) hgs'2
      (fun i p => by
        change Circuit.eval ⟨gs', r (os i)⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = true ↔ p ∈ S i
        rw [hok i]
        simp)
      (fun i x _ hno => by
        change Circuit.eval ⟨gs', r (os i)⟩ (List.ofFn x) = false
        rw [hok i]
        apply decide_eq_false
        rintro ⟨v, hv, hxv⟩
        rw [hno v hv] at hxv; exact Bool.noConfusion hxv)
      (fun _ => le_refl q)
      (fun i => by rw [hcard i])
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at hH1
    exact le_trans hH1 hgs'len
  by_cases hex : ∃ j0 : Fin gates.length, (gates.get j0).op = GateOp.not
  · obtain ⟨j0, hj0⟩ := hex
    have huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j0 :=
      fun i hi => hnot_uniq i j0 hi hj0
    have hanti := not_gate_antimono (n := N) gates j0 hgs huniq hj0
    have hout_ne : ∀ i : Fin N, out i ≠ N + j0.val := by
      intro i heq
      have h0 : Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn (fun _ : Fin N => false)) = false := by
        rw [← heq, hev i]; simp
      have h1 : Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn (fun _ : Fin N => true)) = true := by
        rw [← heq, hev i]
        obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hcard i]; omega)
        exact decide_eq_true ⟨p, hp, rfl⟩
      have h2 := hanti (fun _ => false) (fun _ => true) (fun _ h => Bool.noConfusion h) h1
      rw [h0] at h2; exact Bool.noConfusion h2
    obtain ⟨gsT, hgsT_len, hgsT_mono, hgsT_ev⟩ := drop_gate_true gates j0 hgs huniq
    obtain ⟨gsF, hgsF_len, hgsF_mono, hgsF_ev⟩ := drop_gate_false gates j0 hgs huniq
    have hlen_pos : 1 ≤ gates.length := by have := j0.isLt; omega
    let Bad : Finset (Finset (Fin N)) := Finset.univ.filter
      (fun A : Finset (Fin N) => Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn (fun v => decide (v ∈ A))) = false)
    by_cases hBad : Bad.Nonempty
    · obtain ⟨A, hABad, hAmin⟩ := Finset.exists_min_image Bad Finset.card hBad
      have hAf : Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn (fun v => decide (v ∈ A))) = false :=
        (Finset.mem_filter.mp hABad).2
      by_cases hA0 : A.card = 0
      · have hAempty : A = ∅ := Finset.card_eq_zero.mp hA0
        subst hAempty
        have hallF : ∀ x : Fin N → Bool, Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn x) = false := by
          intro x
          by_contra hne
          have hxt : Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn x) = true :=
            Bool.eq_true_of_not_eq_false hne
          have h0t := hanti (fun v => decide (v ∈ (∅ : Finset (Fin N)))) x
            (fun v hv => by simp at hv) hxt
          rw [hAf] at h0t; exact Bool.noConfusion h0t
        have hbd := mono_full_bound gsF (fun i => remapOut N gates.length j0.val (out i)) hgsF_mono
          (fun i x => by rw [hgsF_ev x (hallF x) (out i) (hout_ne i), hev i x])
        refine ⟨q + 1, by omega, ?_⟩
        have hsub0 : q ^ 2 + q + 1 - ((q + 1) * q + 1) = 0 := by
          apply Nat.sub_eq_zero_of_le; nlinarith
        have hminq : min (q + 1 - 1) q = q := by simp
        rw [hsub0, hminq]
        simp only [mul_zero, Nat.max_zero]
        dsimp only [N] at hbd
        omega
      · have hApos : 1 ≤ A.card := by omega
        have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
        let w := A.card
        -- Bound A: light inputs of weight <= w - 1
        have hBoundA : N * min (w - 1) q ≤ gates.length - 1 := by
          by_cases hw1 : w = 1
          · simp [hw1]
          have hw2 : 2 ≤ w := by omega
          have hlightT : ∀ x : Fin N → Bool,
              (Finset.univ.filter (fun v : Fin N => x v = true)).card ≤ w - 1 →
              Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn x) = true := by
            intro x hwx
            by_contra hne
            have hxf : Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn x) = false :=
              Bool.eq_false_iff.mpr hne
            let B : Finset (Fin N) := Finset.univ.filter (fun v => x v = true)
            have hBx : (fun v => decide (v ∈ B)) = x := by
              funext v; simp [B]
            have hBBad : B ∈ Bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hBx]; exact hxf⟩
            have hle := hAmin B hBBad
            dsimp only [B, w] at hle ⊢
            omega
          obtain ⟨gsT', rT, hgsT'2, hgsT'len, hgsT'ev⟩ := H2 N gsT ∅ ∅ hgsT_mono
          have hT_ok : ∀ (i : Fin N) (x : Fin N → Bool),
              (Finset.univ.filter (fun v : Fin N => x v = true)).card ≤ w - 1 →
              Circuit.eval ⟨gsT', rT (remapOut N gates.length j0.val (out i))⟩ (List.ofFn x) =
                decide (∃ v ∈ S i, x v = true) := by
            intro i x hwx
            have hnc : ∃ x0 y0 : Fin N → Bool,
                Circuit.eval ⟨gsT, remapOut N gates.length j0.val (out i)⟩
                  (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else x0 j)) ≠
                Circuit.eval ⟨gsT, remapOut N gates.length j0.val (out i)⟩
                  (List.ofFn (fun j => if j ∈ (∅ : Finset (Fin N)) then true else if j ∈ (∅ : Finset (Fin N)) then false else y0 j)) := by
              obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hcard i]; omega)
              refine ⟨fun _ => false, fun v => decide (v = p), ?_⟩
              simp only [Finset.notMem_empty, ↓reduceIte]
              have hw0 : (Finset.univ.filter (fun _ : Fin N => false = true)).card ≤ w - 1 := by simp
              have hwp : (Finset.univ.filter (fun v : Fin N => decide (v = p) = true)).card ≤ w - 1 := by
                have : (Finset.univ.filter (fun v : Fin N => decide (v = p) = true)) = {p} := by
                  ext v; simp
                rw [this, Finset.card_singleton]; omega
              rw [hgsT_ev _ (hlightT _ hw0) (out i) (hout_ne i), hev i,
                hgsT_ev _ (hlightT _ hwp) (out i) (hout_ne i), hev i]
              simp [hp]
            have h1 := hgsT'ev (remapOut N gates.length j0.val (out i)) hnc x
            simp only [Finset.notMem_empty, ↓reduceIte] at h1
            rw [h1, hgsT_ev x (hlightT x hwx) (out i) (hout_ne i), hev i x]
          have hH1A := H1 N N (w - 1) S ⟨gsT', 0⟩
            (fun i => rT (remapOut N gates.length j0.val (out i)))
            (fun _ => min (w - 1) q) hinter (fun i => by rw [hcard i]; omega) hgsT'2
            (fun i p => by
              change Circuit.eval ⟨gsT', rT (remapOut N gates.length j0.val (out i))⟩
                (List.ofFn (fun v : Fin N => decide (v = p))) = true ↔ p ∈ S i
              have hwp : (Finset.univ.filter (fun v : Fin N => decide (v = p) = true)).card ≤ w - 1 := by
                have : (Finset.univ.filter (fun v : Fin N => decide (v = p) = true)) = {p} := by
                  ext v; simp
                rw [this, Finset.card_singleton]; omega
              rw [hT_ok i _ hwp]; simp)
            (fun i x hwx hno => by
              change Circuit.eval ⟨gsT', rT (remapOut N gates.length j0.val (out i))⟩ (List.ofFn x) = false
              rw [hT_ok i x hwx]
              apply decide_eq_false
              rintro ⟨v, hv, hxv⟩
              rw [hno v hv] at hxv; exact Bool.noConfusion hxv)
            (fun _ => Nat.min_le_left _ _)
            (fun i => by rw [hcard i]; have := Nat.min_le_right (w - 1) q; omega)
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at hH1A
          omega
        -- Bound B: heavy inputs containing A, lines disjoint from A
        have hBoundB : q * (N - (w * q + 1)) ≤ gates.length - 1 := by
          let U : Finset (Fin N) := Finset.univ.filter (fun i => Disjoint (S i) A)
          have hUcard : N - (w * q + 1) ≤ U.card := by
            have hmeet := plane_meeting_bound S hcard hinter hdeg A hAne
            have hcompl : U.card + (Finset.univ.filter (fun i => ¬ Disjoint (S i) A)).card = N := by
              have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
                (fun i => Disjoint (S i) A)
              simpa [U] using h
            dsimp only [N, w] at hcompl ⊢
            omega
          obtain ⟨gsF', rF, hgsF'2, hgsF'len, hgsF'ev⟩ := H2 N gsF A ∅ hgsF_mono
          have hheavyF : ∀ x : Fin N → Bool,
              Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn (fun v => if v ∈ A then true else x v)) = false := by
            intro x
            by_contra hne
            have hxt : Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn (fun v => if v ∈ A then true else x v)) = true :=
              Bool.eq_true_of_not_eq_false hne
            have hAt := hanti (fun v => decide (v ∈ A)) (fun v => if v ∈ A then true else x v)
              (fun v hv => by simp [of_decide_eq_true hv]) hxt
            rw [hAf] at hAt; exact Bool.noConfusion hAt
          have hF_ok : ∀ i ∈ U, ∀ x : Fin N → Bool,
              Circuit.eval ⟨gsF', rF (remapOut N gates.length j0.val (out i))⟩ (List.ofFn x) =
                decide (∃ v ∈ S i, x v = true) := by
            intro i hiU x
            have hdisj : Disjoint (S i) A := (Finset.mem_filter.mp hiU).2
            have heval_i : ∀ y : Fin N → Bool,
                Circuit.eval ⟨gsF, remapOut N gates.length j0.val (out i)⟩
                  (List.ofFn (fun v => if v ∈ A then true else if v ∈ (∅ : Finset (Fin N)) then false else y v)) =
                  decide (∃ v ∈ S i, y v = true) := by
              intro y
              simp only [Finset.notMem_empty, ↓reduceIte]
              rw [hgsF_ev _ (hheavyF y) (out i) (hout_ne i), hev i]
              congr 1; apply propext
              constructor
              · rintro ⟨v, hv, hvy⟩
                have hvA : v ∉ A := Finset.disjoint_left.mp hdisj hv
                simp only [hvA, ↓reduceIte] at hvy
                exact ⟨v, hv, hvy⟩
              · rintro ⟨v, hv, hvy⟩
                have hvA : v ∉ A := Finset.disjoint_left.mp hdisj hv
                exact ⟨v, hv, by simp [hvA, hvy]⟩
            have hnc : ∃ x0 y0 : Fin N → Bool,
                Circuit.eval ⟨gsF, remapOut N gates.length j0.val (out i)⟩
                  (List.ofFn (fun v => if v ∈ A then true else if v ∈ (∅ : Finset (Fin N)) then false else x0 v)) ≠
                Circuit.eval ⟨gsF, remapOut N gates.length j0.val (out i)⟩
                  (List.ofFn (fun v => if v ∈ A then true else if v ∈ (∅ : Finset (Fin N)) then false else y0 v)) := by
              obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hcard i]; omega)
              refine ⟨fun _ => false, fun _ => true, ?_⟩
              rw [heval_i, heval_i]
              simp; exact ⟨p, hp⟩
            rw [hgsF'ev (remapOut N gates.length j0.val (out i)) hnc x, heval_i x]
          let e := U.equivFin.symm
          have hH1B := H1 N U.card q (fun k => S (e k).1) ⟨gsF', 0⟩
            (fun k => rF (remapOut N gates.length j0.val (out (e k).1)))
            (fun _ => q)
            (fun k1 k2 hne => hinter _ _ (fun heq => hne (e.injective (Subtype.ext heq))))
            (fun k => by rw [hcard]; omega) hgsF'2
            (fun k p => by
              change Circuit.eval ⟨gsF', rF (remapOut N gates.length j0.val (out (e k).1))⟩
                (List.ofFn (fun v : Fin N => decide (v = p))) = true ↔ p ∈ S (e k).1
              rw [hF_ok (e k).1 (e k).2]; simp)
            (fun k x _ hno => by
              change Circuit.eval ⟨gsF', rF (remapOut N gates.length j0.val (out (e k).1))⟩ (List.ofFn x) = false
              rw [hF_ok (e k).1 (e k).2]
              apply decide_eq_false
              rintro ⟨v, hv, hxv⟩
              rw [hno v hv] at hxv; exact Bool.noConfusion hxv)
            (fun _ => le_refl q)
            (fun k => by rw [hcard])
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at hH1B
          have hmul_le : q * (N - (w * q + 1)) ≤ U.card * q := by
            rw [mul_comm]; exact Nat.mul_le_mul_right q hUcard
          omega
        refine ⟨w, hApos, ?_⟩
        have hmax : max ((q^2 + q + 1) * min (w - 1) q) (q * ((q^2 + q + 1) - (w * q + 1))) ≤ gates.length - 1 :=
          max_le hBoundA hBoundB
        omega
    · -- Bad is empty: f_NOT is always true
      have hallT : ∀ x : Fin N → Bool, Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn x) = true := by
        intro x
        by_contra hne
        have hxf : Circuit.eval ⟨gates, N + j0.val⟩ (List.ofFn x) = false := Bool.eq_false_iff.mpr hne
        let B : Finset (Fin N) := Finset.univ.filter (fun v => x v = true)
        have hBx : (fun v => decide (v ∈ B)) = x := by funext v; simp [B]
        exact hBad ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hBx]; exact hxf⟩⟩
      have hbd := mono_full_bound gsT (fun i => remapOut N gates.length j0.val (out i)) hgsT_mono
        (fun i x => by rw [hgsT_ev x (hallT x) (out i) (hout_ne i), hev i x])
      refine ⟨q + 1, by omega, ?_⟩
      have hsub0 : q ^ 2 + q + 1 - ((q + 1) * q + 1) = 0 := by
        apply Nat.sub_eq_zero_of_le; nlinarith
      have hminq : min (q + 1 - 1) q = q := by simp
      rw [hsub0, hminq]
      simp only [mul_zero, Nat.max_zero]
      dsimp only [N] at hbd
      omega
  · -- No NOT gate in gates
    have hgm : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨hop, hlen⟩ := hgs (gates[k]'hk) hg
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd ⟨⟨k, hk⟩, h⟩ hex
    have hbd := mono_full_bound gates out hgm hev
    refine ⟨1, le_refl 1, ?_⟩
    simp only [Nat.sub_self, Nat.zero_min, mul_zero, one_mul, Nat.zero_max]
    have hdiff : N - (q + 1) = q^2 := by dsimp only [N]; omega
    rw [hdiff]
    have hlt : 1 + q * q^2 ≤ N * q := by dsimp only [N]; nlinarith
    omega

end PEqualNP.Outside.L_meta_1373

theorem PEqualNP.Outside.L_meta_1373 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1))) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q^2+q+1) → ℕ), 2 ≤ q → (∀ i, (S i).card = q + 1) → (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ (w : Fin (q^2+q+1)) (x : Fin (q^2+q+1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2+q+1) * min (w - 1) q) (q * ((q^2+q+1) - (w * q + 1))) ≤ gates.length :=
  PEqualNP.Outside.L_meta_1373.main_1373
