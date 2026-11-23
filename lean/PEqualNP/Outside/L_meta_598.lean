import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_598

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

private lemma runWires_nil (x : List Bool) : runWires [] x = x := rfl

private lemma runWires_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    runWires (gs ++ [g]) x = stepWire (runWires gs x) g := by
  simp [runWires]

private lemma runWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    runWires (gs1 ++ gs2) x = runWires gs2 (runWires gs1 x) := by
  simp [runWires, List.foldl_append]

private lemma runWires_length (gs : List Gate) (x : List Bool) :
    (runWires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runWires]
  | append_singleton gs g ih =>
    rw [runWires_append_singleton, stepWire, List.length_append, List.length_singleton, ih]
    simp [Nat.add_assoc]

private lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h h1)), List.getElem?_append_left h1]
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (h1 h))]
    by_cases h2 : i = w.length
    · subst h2
      rw [ite_eq_left_iff.mpr (fun h => False.elim (h rfl)), List.getElem?_append_right (le_refl _)]
      simp
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (h2 h)), List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private def wireVal (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (runWires gs (List.ofFn x)).getD i false

private lemma wireVal_append_left (n : ℕ) (gs1 gs2 : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs1.length) :
    wireVal n (gs1 ++ gs2) x i = wireVal n gs1 x i := by
  induction gs2 using List.reverseRecOn with
  | nil => simp [wireVal]
  | append_singleton gs2 g ih =>
    have hlt : i < (runWires (gs1 ++ gs2) (List.ofFn x)).length := by
      rw [runWires_length, List.length_ofFn, List.length_append]
      omega
    rw [← List.append_assoc, wireVal, runWires_append_singleton, stepWire, getD_append_singleton,
      ite_eq_left_iff.mpr (fun h => False.elim (h hlt))]
    exact ih

private lemma wireVal_input (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n gs x i = x ⟨i, hi⟩ := by
  have h1 := wireVal_append_left n [] gs x i (by simpa using hi)
  simp only [List.nil_append] at h1
  rw [h1, wireVal, runWires_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

private lemma wireVal_of_ge (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) :
    wireVal n gs x i = false := by
  apply getD_of_ge
  rw [runWires_length, List.length_ofFn]
  exact hi

private lemma wireVal_gate (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) :
    wireVal n gs x (n + j) =
      g.op.eval (g.inputs.map fun k => if k < n + j then wireVal n gs x k else false) := by
  have hlt : j < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (not_lt.mp h)] at hj
    simp at hj
  have hsplit : gs = (gs.take j ++ [g]) ++ gs.drop (j + 1) := by
    have hget : gs[j] = g := by
      rw [List.getElem?_eq_getElem hlt] at hj
      exact Option.some.inj hj
    have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hlt
    rw [h2, hget] at h1
    simpa [List.append_assoc] using h1.symm
  have htake_len : (gs.take j).length = j := List.length_take_of_le (le_of_lt hlt)
  have h1 : wireVal n gs x (n + j) = wireVal n (gs.take j ++ [g]) x (n + j) := by
    conv_lhs => rw [hsplit]
    apply wireVal_append_left
    rw [List.length_append, List.length_singleton, htake_len]
    omega
  rw [h1, wireVal, runWires_append_singleton, stepWire, getD_append_singleton,
    runWires_length, List.length_ofFn, htake_len]
  simp only [lt_irrefl, ite_false, ite_true]
  congr 1
  apply List.map_congr_left
  intro k _
  by_cases hk : k < n + j
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hk))]
    have htake_eq : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
    have h2 : wireVal n gs x k = wireVal n (gs.take j) x k := by
      conv_lhs => rw [htake_eq]
      exact wireVal_append_left n (gs.take j) (gs.drop j) x k (by rw [htake_len]; exact hk)
    exact h2.symm
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hk h))]
    apply getD_of_ge
    rw [runWires_length, List.length_ofFn, htake_len]
    omega

private def IsDead (n : ℕ) (gs : List Gate) (v : Fin n) (i : ℕ) : Prop :=
  ∀ x : Fin n → Bool, x v = false → wireVal n gs x i = false

private def IsIndep (n : ℕ) (gs : List Gate) (v : Fin n) (i : ℕ) : Prop :=
  ∀ x : Fin n → Bool,
    wireVal n gs (Function.update x v true) i = wireVal n gs (Function.update x v false) i

private lemma exists_or_reading_dead (n : ℕ) (C : Circuit) (v : Fin n)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hdep : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true)
    (hnotbelow : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true) :
    ∃ (j : ℕ) (g : Gate) (i : ℕ),
      C.gates[j]? = some g ∧ g.op = GateOp.or ∧ i ∈ g.inputs ∧ i < n + j ∧
        IsDead n C.gates v i := by
  by_contra hno
  have hclass : ∀ w : ℕ, IsDead n C.gates v w ∨ IsIndep n C.gates v w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hwn : w < n
      · by_cases hwv : w = v.val
        · left
          intro x hx
          rw [wireVal_input n C.gates x w hwn]
          have hfin : (⟨w, hwn⟩ : Fin n) = v := Fin.ext hwv
          rw [hfin]
          exact hx
        · right
          intro x
          rw [wireVal_input n C.gates _ w hwn, wireVal_input n C.gates _ w hwn]
          have hne : (⟨w, hwn⟩ : Fin n) ≠ v := fun h => hwv (congrArg Fin.val h)
          simp [Function.update, hne]
      · by_cases hwlen : w < n + C.gates.length
        · let j := w - n
          have hj_lt : j < C.gates.length := by omega
          have hw_eq : w = n + j := by omega
          let g := C.gates[j]
          have hj_get : C.gates[j]? = some g := List.getElem?_eq_getElem hj_lt
          have hg_mem : g ∈ C.gates := List.getElem_mem hj_lt
          rcases (hmono g hg_mem).1 with hop | hop
          · by_cases hex : ∃ k ∈ g.inputs, ¬ (k < n + j) ∨ IsDead n C.gates v k
            · left
              rcases hex with ⟨k, hk, hkd⟩
              intro x hx
              rw [hw_eq, wireVal_gate n C.gates x j g hj_get, hop, GateOp.eval]
              have hf : (if k < n + j then wireVal n C.gates x k else false) = false := by
                rcases hkd with hge | hd
                · simp [hge]
                · by_cases hlt : k < n + j
                  · simp [hlt, hd x hx]
                  · simp [hlt]
              cases hval : (g.inputs.map fun k => if k < n + j then wireVal n C.gates x k else false).all id
              · rfl
              · exfalso
                rw [List.all_eq_true] at hval
                have := hval _ (List.mem_map_of_mem hk)
                simp [hf] at this
            · right
              intro x
              rw [hw_eq, wireVal_gate n C.gates _ j g hj_get, wireVal_gate n C.gates _ j g hj_get]
              congr 1
              apply List.map_congr_left
              intro k hk
              have hkd : k < n + j ∧ ¬ IsDead n C.gates v k := by
                by_contra h
                exact hex ⟨k, hk, by tauto⟩
              rw [ite_eq_left_iff.mpr (fun h => False.elim (h hkd.1)),
                ite_eq_left_iff.mpr (fun h => False.elim (h hkd.1))]
              have hind : IsIndep n C.gates v k := (ih k (by omega)).resolve_left hkd.2
              exact hind x
          · right
            intro x
            rw [hw_eq, wireVal_gate n C.gates _ j g hj_get, wireVal_gate n C.gates _ j g hj_get]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hlt : k < n + j
            · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hlt)),
                ite_eq_left_iff.mpr (fun h => False.elim (h hlt))]
              have hnd : ¬ IsDead n C.gates v k := fun hd =>
                hno ⟨j, g, k, hj_get, hop, hk, hlt, hd⟩
              exact (ih k (by omega)).resolve_left hnd x
            · simp [hlt]
        · right
          intro x
          rw [wireVal_of_ge n C.gates _ w (by omega), wireVal_of_ge n C.gates _ w (by omega)]
  rcases hclass C.output with hdead | hindep
  · rcases hnotbelow with ⟨x, hxv, hx1⟩
    have := hdead x hxv
    change C.eval (List.ofFn x) = false at this
    rw [hx1] at this
    cases this
  · rcases hdep with ⟨x, hxv, hx0, hx1⟩
    have hupd : Function.update x v false = x := by
      funext u
      by_cases hu : u = v
      · subst hu; simp [hxv]
      · simp [Function.update, hu]
    have h1 := hindep x
    rw [hupd] at h1
    change C.eval (List.ofFn (Function.update x v true)) = C.eval (List.ofFn x) at h1
    rw [hx1, hx0] at h1
    cases h1

private lemma restrict_false_eliminates_or (n : ℕ) (C : Circuit) (v : Fin n) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A)
    (hdep : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true)
    (hnotbelow : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true) :
    ∃ (C' : Circuit) (j : ℕ),
      j ∈ A ∧
      PEqualNP.MetaComplexity.Monotone2 C' ∧
      (∀ (k : ℕ) (g : Gate), C'.gates[k]? = some g → g.op = GateOp.or → k ∈ A.erase j) ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) := by
  classical
  obtain ⟨j0, g0, i0, hj0, hg0_op, hi0_mem, hi0_lt, hi0_dead⟩ :=
    exists_or_reading_dead n C v hmono hdep hnotbelow
  have hj0A : j0 ∈ A := hA j0 g0 hj0 hg0_op
  let dead : ℕ → Prop := IsDead n C.gates v
  let simpGate : ℕ → Gate → Gate := fun k g =>
    if dead (n + k) then ⟨GateOp.and, []⟩
    else if g.op = GateOp.and then g
    else
      match g.inputs with
      | [] => ⟨GateOp.and, []⟩
      | [a] => ⟨GateOp.and, [a]⟩
      | [a, b] =>
        if a ≥ n + k ∨ dead a then ⟨GateOp.and, [b]⟩
        else if b ≥ n + k ∨ dead b then ⟨GateOp.and, [a]⟩
        else g
      | _ => g
  let C' : Circuit := ⟨C.gates.mapIdx simpGate, C.output⟩
  have hlen' : C'.gates.length = C.gates.length := List.length_mapIdx
  have hget' (k : ℕ) : C'.gates[k]? = (C.gates[k]?).map (simpGate k) := List.getElem?_mapIdx
  have hmono' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g' hg'
    obtain ⟨k, hk_lt, rfl⟩ := List.mem_iff_getElem.mp hg'
    have hke : C'.gates[k]? = some C'.gates[k] := List.getElem?_eq_getElem hk_lt
    rw [hget'] at hke
    have hk_lt_C : k < C.gates.length := by omega
    rw [List.getElem?_eq_getElem hk_lt_C, Option.map_some] at hke
    have hge := Option.some.inj hke
    rw [← hge]
    have hg_mono := hmono C.gates[k] (List.getElem_mem hk_lt_C)
    dsimp only [simpGate]
    split_ifs
    · simp
    · exact hg_mono
    · cases hgin : C.gates[k].inputs with
      | nil => simp
      | cons a tl =>
        cases tl with
        | nil => simp
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            dsimp only
            split_ifs
            · simp
            · simp
            · exact hg_mono
          | cons c tl3 =>
            exact hg_mono
  have hA' : ∀ (k : ℕ) (g' : Gate), C'.gates[k]? = some g' → g'.op = GateOp.or → k ∈ A.erase j0 := by
    intro k g' hk' hop'
    rw [hget'] at hk'
    cases hkC : C.gates[k]? with
    | none => rw [hkC] at hk'; simp at hk'
    | some g =>
      rw [hkC, Option.map_some] at hk'
      have hge := Option.some.inj hk'
      rw [← hge] at hop'
      have hk_lt : k < C.gates.length := by
        by_contra h
        rw [List.getElem?_eq_none (not_lt.mp h)] at hkC
        simp at hkC
      have hg_mono := hmono g (by
        rw [List.getElem?_eq_getElem hk_lt] at hkC
        rw [← Option.some.inj hkC]
        exact List.getElem_mem hk_lt)
      have hnd_nk : ¬ dead (n + k) := by
        intro hd
        dsimp only [simpGate] at hop'
        rw [if_pos hd] at hop'
        cases hop'
      have hnot_and : g.op ≠ GateOp.and := by
        intro hand
        dsimp only [simpGate] at hop'
        rw [if_neg hnd_nk, if_pos hand] at hop'
        rw [hand] at hop'
        cases hop'
      have hg_or : g.op = GateOp.or := by
        rcases hg_mono.1 with h | h
        · exact False.elim (hnot_and h)
        · exact h
      have hkA : k ∈ A := hA k g hkC hg_or
      apply Finset.mem_erase.mpr
      refine ⟨?_, hkA⟩
      intro hkj
      subst hkj
      rw [hj0] at hkC
      have hg_eq : g = g0 := Option.some.inj hkC.symm
      subst hg_eq
      dsimp only [simpGate] at hop'
      rw [if_neg hnd_nk, if_neg hnot_and] at hop'
      have hglen := hg_mono.2
      cases hgin : g.inputs with
      | nil => rw [hgin] at hop'; cases hop'
      | cons a tl =>
        cases tl with
        | nil => rw [hgin] at hop'; cases hop'
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hi0_mem hop'
            dsimp only at hop'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0_mem
            rcases hi0_mem with rfl | rfl
            · have ha : i0 ≥ n + k ∨ dead i0 := Or.inr hi0_dead
              rw [if_pos ha] at hop'
              cases hop'
            · by_cases ha : a ≥ n + k ∨ dead a
              · rw [if_pos ha] at hop'
                cases hop'
              · have hb : i0 ≥ n + k ∨ dead i0 := Or.inr hi0_dead
                rw [if_neg ha, if_pos hb] at hop'
                cases hop'
          | cons c tl3 =>
            rw [hgin] at hglen
            simp at hglen
  have hwire : ∀ w : ℕ, ¬ dead w → ∀ x : Fin n → Bool,
      wireVal n C'.gates x w = wireVal n C.gates (Function.update x v false) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hnd x
      have hv_upd : Function.update x v false v = false := by simp
      by_cases hwn : w < n
      · rw [wireVal_input n C'.gates x w hwn, wireVal_input n C.gates _ w hwn]
        have hne : (⟨w, hwn⟩ : Fin n) ≠ v := by
          intro heq
          apply hnd
          intro y hy
          rw [wireVal_input n C.gates y w hwn, heq]
          exact hy
        simp [Function.update, hne]
      · by_cases hwlen : w < n + C.gates.length
        · let k := w - n
          have hk_lt : k < C.gates.length := by omega
          have hw_eq : w = n + k := by omega
          let g := C.gates[k]
          have hkC : C.gates[k]? = some g := List.getElem?_eq_getElem hk_lt
          have hk' : C'.gates[k]? = some (simpGate k g) := by
            rw [hget', hkC, Option.map_some]
          have hg_mono := hmono g (List.getElem_mem hk_lt)
          have hnd_k : ¬ dead (n + k) := hw_eq ▸ hnd
          rw [hw_eq, wireVal_gate n C'.gates x k (simpGate k g) hk',
            wireVal_gate n C.gates (Function.update x v false) k g hkC]
          rcases hg_mono.1 with hop | hop
          · have hsg : simpGate k g = g := by
              dsimp only [simpGate]
              rw [if_neg hnd_k, if_pos hop]
            rw [hsg]
            congr 1
            apply List.map_congr_left
            intro a ha
            have ha_ok : a < n + k ∧ ¬ dead a := by
              by_contra hbad
              apply hnd_k
              intro y hy
              rw [wireVal_gate n C.gates y k g hkC, hop, GateOp.eval]
              have haf : (if a < n + k then wireVal n C.gates y a else false) = false := by
                by_cases hlt : a < n + k
                · have had : dead a := by
                    by_contra hna
                    exact hbad ⟨hlt, hna⟩
                  simp [hlt, had y hy]
                · simp [hlt]
              cases hval : (g.inputs.map fun a => if a < n + k then wireVal n C.gates y a else false).all id
              · rfl
              · exfalso
                rw [List.all_eq_true] at hval
                have := hval _ (List.mem_map_of_mem ha)
                simp [haf] at this
            rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1)),
              ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
            exact ih a (by omega) ha_ok.2 x
          · have hnot_and : g.op ≠ GateOp.and := by
              rw [hop]; intro h; cases h
            have hglen := hg_mono.2
            cases hgin : g.inputs with
            | nil =>
              exfalso
              apply hnd_k
              intro y _
              rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
              rfl
            | cons a tl =>
              cases tl with
              | nil =>
                have hsg : simpGate k g = ⟨GateOp.and, [a]⟩ := by
                  dsimp only [simpGate]
                  rw [if_neg hnd_k, if_neg hnot_and, hgin]
                have ha_ok : a < n + k ∧ ¬ dead a := by
                  by_contra hbad
                  apply hnd_k
                  intro y hy
                  rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
                  by_cases hlt : a < n + k
                  · have had : dead a := by
                      by_contra hna
                      exact hbad ⟨hlt, hna⟩
                    simp [hlt, had y hy]
                  · simp [hlt]
                rw [hsg, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
                  ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
                exact ih a (by omega) ha_ok.2 x
              | cons b tl2 =>
                cases tl2 with
                | nil =>
                  by_cases ha_bad : a ≥ n + k ∨ dead a
                  · have ha_f (y : Fin n → Bool) (hy : y v = false) :
                        (if a < n + k then wireVal n C.gates y a else false) = false := by
                      rcases ha_bad with hge | had
                      · simp [not_lt.mpr hge]
                      · by_cases hlt : a < n + k
                        · simp [hlt, had y hy]
                        · simp [hlt]
                    have hb_ok : b < n + k ∧ ¬ dead b := by
                      by_contra hbad
                      apply hnd_k
                      intro y hy
                      rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                        Bool.or_false, ha_f y hy, Bool.false_or]
                      by_cases hlt : b < n + k
                      · have hbd : dead b := by
                          by_contra hnb
                          exact hbad ⟨hlt, hnb⟩
                        simp [hlt, hbd y hy]
                      · simp [hlt]
                    have hsg : simpGate k g = ⟨GateOp.and, [b]⟩ := by
                      dsimp only [simpGate]
                      rw [if_neg hnd_k, if_neg hnot_and, hgin]
                      dsimp only
                      rw [if_pos ha_bad]
                    rw [hsg, hop]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                      List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
                      ha_f (Function.update x v false) hv_upd, Bool.false_or,
                      ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                    exact ih b (by omega) hb_ok.2 x
                  · have ha_ok : a < n + k ∧ ¬ dead a := by
                      exact ⟨by omega, fun h => ha_bad (Or.inr h)⟩
                    by_cases hb_bad : b ≥ n + k ∨ dead b
                    · have hb_f (y : Fin n → Bool) (hy : y v = false) :
                          (if b < n + k then wireVal n C.gates y b else false) = false := by
                        rcases hb_bad with hge | hbd
                        · simp [not_lt.mpr hge]
                        · by_cases hlt : b < n + k
                          · simp [hlt, hbd y hy]
                          · simp [hlt]
                      have hsg : simpGate k g = ⟨GateOp.and, [a]⟩ := by
                        dsimp only [simpGate]
                        rw [if_neg hnd_k, if_neg hnot_and, hgin]
                        dsimp only
                        rw [if_neg ha_bad, if_pos hb_bad]
                      rw [hsg, hop]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
                        hb_f (Function.update x v false) hv_upd, Bool.or_false,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
                      exact ih a (by omega) ha_ok.2 x
                    · have hb_ok : b < n + k ∧ ¬ dead b := by
                        exact ⟨by omega, fun h => hb_bad (Or.inr h)⟩
                      have hsg : simpGate k g = g := by
                        dsimp only [simpGate]
                        rw [if_neg hnd_k, if_neg hnot_and, hgin]
                        dsimp only
                        rw [if_neg ha_bad, if_neg hb_bad]
                      rw [hsg, hop, hgin]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        id, Bool.or_false,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1)),
                        ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                      rw [ih a (by omega) ha_ok.2 x, ih b (by omega) hb_ok.2 x]
                | cons c tl3 =>
                  rw [hgin] at hglen
                  simp at hglen
        · exfalso
          apply hnd
          intro y _
          exact wireVal_of_ge n C.gates y w (by omega)
  have hout_nd : ¬ dead C.output := by
    intro hd
    rcases hnotbelow with ⟨x, hxv, hx1⟩
    have := hd x hxv
    change C.eval (List.ofFn x) = false at this
    rw [hx1] at this
    cases this
  refine ⟨C', j0, hj0A, hmono', hA', fun x => ?_⟩
  exact hwire C.output hout_nd x

private def deleteVertex {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ b ≠ v
  symm := ⟨fun _ _ ⟨h, ha, hb⟩ => ⟨h.symm, hb, ha⟩⟩
  loopless := ⟨fun _ ⟨h, _, _⟩ => G.loopless.irrefl _ h⟩

private lemma walk_split {n : ℕ} {G : SimpleGraph (Fin n)} {a b v : Fin n}
    (p : G.Walk a b) (hv : v ∈ p.support) :
    ∃ (p1 : G.Walk a v) (p2 : G.Walk v b), p1.length + p2.length = p.length := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact ⟨.nil, .nil, rfl⟩
  | @cons x y z hxy q ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hvq
    · exact ⟨.nil, .cons hxy q, by simp⟩
    · obtain ⟨p1, p2, hlen⟩ := ih hvq
      exact ⟨.cons hxy p1, p2, by simp; omega⟩

private lemma walk_lift_delete {n : ℕ} {G : SimpleGraph (Fin n)} {v a b : Fin n}
    (p : G.Walk a b) (hv : v ∉ p.support) :
    (deleteVertex G v).Reachable a b := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy q ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hv
    have hne_y : y ≠ v := fun h => hv.2 (h ▸ SimpleGraph.Walk.start_mem_support q)
    have hadj : (deleteVertex G v).Adj x y := ⟨hxy, Ne.symm hv.1, hne_y⟩
    exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hadj) (ih hv.2)

private lemma walk_to_orig {n : ℕ} {G : SimpleGraph (Fin n)} {v a b : Fin n}
    (h : (deleteVertex G v).Reachable a b) : G.Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy q ih =>
    exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hxy.1) ih

private lemma exists_adj_of_reachable_ne {n : ℕ} {G : SimpleGraph (Fin n)} {a b : Fin n}
    (h : G.Reachable a b) (hne : a ≠ b) : ∃ w : Fin n, G.Adj a w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons hadj _ => exact ⟨_, hadj⟩

private noncomputable def activeVerts {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (fun v => ∃ w : Fin n, G.Adj v w)

private noncomputable def activeComps {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset G.ConnectedComponent :=
  by classical exact Finset.univ.filter (fun K => ∃ v w : Fin n, G.connectedComponentMk v = K ∧ G.Adj v w)

private noncomputable def compVerts {n : ℕ} (G : SimpleGraph (Fin n))
    (K : G.ConnectedComponent) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (fun v => G.connectedComponentMk v = K)

private lemma activeVerts_card_eq_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    {v : Fin n | ∃ w : Fin n, G.Adj v w}.ncard = (activeVerts G).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext v
  simp [activeVerts]

private lemma activeComps_card_eq_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    {K : G.ConnectedComponent | ∃ v w : Fin n, G.connectedComponentMk v = K ∧ G.Adj v w}.ncard =
      (activeComps G).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext K
  simp [activeComps]

private lemma activeVerts_eq_biUnion {n : ℕ} (G : SimpleGraph (Fin n)) :
    activeVerts G = (activeComps G).biUnion (compVerts G) := by
  classical
  ext v
  simp only [activeVerts, activeComps, compVerts, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hvw⟩
    exact ⟨G.connectedComponentMk v, ⟨v, w, rfl, hvw⟩, rfl⟩
  · rintro ⟨K, ⟨a, b, ha, hab⟩, hv⟩
    have hreach : G.Reachable v a := SimpleGraph.ConnectedComponent.exact (hv.trans ha.symm)
    by_cases hva : v = a
    · subst hva; exact ⟨b, hab⟩
    · exact exists_adj_of_reachable_ne hreach hva

private lemma activeVerts_card_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) :
    (activeVerts G).card = ∑ K ∈ activeComps G, (compVerts G K).card := by
  classical
  rw [activeVerts_eq_biUnion, Finset.card_biUnion]
  intro K1 _ K2 _ hne
  change Disjoint (compVerts G K1) (compVerts G K2)
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
  exact hne (hv1.symm.trans hv2)

private lemma compVerts_ge_two {n : ℕ} (G : SimpleGraph (Fin n)) (K : G.ConnectedComponent)
    (hK : K ∈ activeComps G) : 2 ≤ (compVerts G K).card := by
  classical
  simp only [activeComps, Finset.mem_filter, Finset.mem_univ, true_and] at hK
  rcases hK with ⟨a, b, ha, hab⟩
  have hne : a ≠ b := G.ne_of_adj hab
  have ha_mem : a ∈ compVerts G K := by simp [compVerts, ha]
  have hb_mem : b ∈ compVerts G K := by
    simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hab.symm)).trans ha
  have hsub : ({a, b} : Finset (Fin n)) ⊆ compVerts G K := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha_mem
    · exact hb_mem
  calc
    2 = ({a, b} : Finset (Fin n)).card := (Finset.card_pair hne).symm
    _ ≤ (compVerts G K).card := Finset.card_le_card hsub

private lemma exists_noncut_step {n : ℕ} (G : SimpleGraph (Fin n))
    (hbig : (activeComps G).card + 1 < (activeVerts G).card) :
    ∃ v : Fin n,
      (∃ w : Fin n, G.Adj v w) ∧
      (∃ a b : Fin n, G.Adj a b ∧ a ≠ v ∧ b ≠ v) ∧
      (activeVerts G).card + (activeComps (deleteVertex G v)).card ≤
        (activeVerts (deleteVertex G v)).card + (activeComps G).card + 1 := by
  classical
  by_cases hge3 : ∃ K ∈ activeComps G, 3 ≤ (compVerts G K).card
  · rcases hge3 with ⟨K, hK, hK3⟩
    have hKne : (compVerts G K).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨r, hr⟩ := hKne
    have hr_mk : G.connectedComponentMk r = K := by
      simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact hr
    have hreach_K (u : Fin n) (hu : u ∈ compVerts G K) : G.Reachable r u := by
      simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact SimpleGraph.ConnectedComponent.exact (hr_mk.trans hu.symm)
    let minD : Fin n → ℕ := fun u =>
      if h : G.Reachable r u then
        Nat.find (show ∃ d : ℕ, ∃ p : G.Walk r u, p.length = d from
          let ⟨p⟩ := h; ⟨p.length, p, rfl⟩)
      else 0
    have hminD_spec (u : Fin n) (h : G.Reachable r u) :
        ∃ p : G.Walk r u, p.length = minD u := by
      dsimp only [minD]
      rw [dif_pos h]
      exact Nat.find_spec (show ∃ d : ℕ, ∃ p : G.Walk r u, p.length = d from
        let ⟨p⟩ := h; ⟨p.length, p, rfl⟩)
    have hminD_le (u : Fin n) (h : G.Reachable r u) (p : G.Walk r u) : minD u ≤ p.length := by
      dsimp only [minD]
      rw [dif_pos h]
      exact Nat.find_min' _ ⟨p, rfl⟩
    obtain ⟨v, hvK, hv_max⟩ := Finset.exists_max_image (compVerts G K) minD ⟨r, hr⟩
    have hv_mk : G.connectedComponentMk v = K := by
      simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hvK
      exact hvK
    have hv_ne_r : v ≠ r := by
      have hex_other : ∃ u ∈ compVerts G K, u ≠ r := by
        by_contra h
        have hsub : compVerts G K ⊆ {r} := by
          intro u hu
          by_contra hur
          exact h ⟨u, hu, Finset.mem_singleton.not.mp hur⟩
        have hc := Finset.card_le_card hsub
        simp at hc
        omega
      rcases hex_other with ⟨u, huK, hur⟩
      have hu_pos : 1 ≤ minD u := by
        obtain ⟨p, hp⟩ := hminD_spec u (hreach_K u huK)
        cases p with
        | nil => exact False.elim (hur rfl)
        | cons _ _ => simp at hp; omega
      have hv_pos : 1 ≤ minD v := le_trans hu_pos (hv_max u huK)
      intro hvr
      subst hvr
      have h0 : minD v ≤ 0 := hminD_le v (SimpleGraph.Reachable.refl v) .nil
      omega
    let G' := deleteVertex G v
    have hreach_G' (u : Fin n) (huK : u ∈ compVerts G K) (huv : u ≠ v) : G'.Reachable r u := by
      obtain ⟨p, hp⟩ := hminD_spec u (hreach_K u huK)
      apply walk_lift_delete p
      intro hv_sup
      obtain ⟨p1, p2, hlen⟩ := walk_split p hv_sup
      have hp1 : minD v ≤ p1.length := hminD_le v (hreach_K v hvK) p1
      have hp2 : 1 ≤ p2.length := by
        cases p2 with
        | nil => exact False.elim (huv rfl)
        | cons _ _ => simp
      have hmax := hv_max u huK
      omega
    have hex_z : ∃ z ∈ compVerts G K, z ≠ r ∧ z ≠ v := by
      by_contra h
      have hsub : compVerts G K ⊆ {r, v} := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hrv
        push Not at hrv
        exact h ⟨z, hz, hrv.1, hrv.2⟩
      have hc := Finset.card_le_card hsub
      have h2 : ({r, v} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      omega
    rcases hex_z with ⟨z, hzK, hzr, hzv⟩
    have hr_adj_G' : ∃ w : Fin n, G'.Adj r w :=
      exists_adj_of_reachable_ne (hreach_G' z hzK hzv) hzr.symm
    have hv_adj_G : ∃ w : Fin n, G.Adj v w :=
      exists_adj_of_reachable_ne (hreach_K v hvK).symm hv_ne_r
    have hV'_eq : activeVerts G' = (activeVerts G).erase v := by
      ext u
      simp only [activeVerts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨w, huw⟩
        exact ⟨huw.2.1, w, huw.1⟩
      · rintro ⟨huv, w, huw⟩
        by_cases huK : u ∈ compVerts G K
        · by_cases hur : u = r
          · subst hur; exact hr_adj_G'
          · exact exists_adj_of_reachable_ne (hreach_G' u huK huv).symm hur
        · have hwv : w ≠ v := by
            intro h
            subst h
            apply huK
            simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and]
            exact (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable huw)).trans hv_mk
          exact ⟨w, huw, huv, hwv⟩
    have hV'_card : (activeVerts G').card + 1 = (activeVerts G).card := by
      rw [hV'_eq]
      have hv_mem : v ∈ activeVerts G := by simp [activeVerts, hv_adj_G]
      have := Finset.card_erase_add_one hv_mem
      exact this
    let φ : G'.ConnectedComponent → G.ConnectedComponent :=
      Quot.lift (fun u => G.connectedComponentMk u)
        (fun _ _ h => SimpleGraph.ConnectedComponent.eq.mpr (walk_to_orig h))
    have hφ_mk (u : Fin n) : φ (G'.connectedComponentMk u) = G.connectedComponentMk u := rfl
    have hφ_maps : ∀ K' ∈ activeComps G', φ K' ∈ activeComps G := by
      intro K' hK'
      simp only [activeComps, Finset.mem_filter, Finset.mem_univ, true_and] at hK' ⊢
      rcases hK' with ⟨a, b, ha, hab⟩
      refine ⟨a, b, ?_, hab.1⟩
      rw [← ha, hφ_mk]
    have hφ_inj : Set.InjOn φ (activeComps G') := by
      intro K1' hK1' K2' hK2' heq
      simp only [Finset.mem_coe, activeComps, Finset.mem_filter, Finset.mem_univ, true_and] at hK1' hK2'
      rcases hK1' with ⟨a1, b1, ha1, hab1⟩
      rcases hK2' with ⟨a2, b2, ha2, hab2⟩
      have hmk_eq : G.connectedComponentMk a1 = G.connectedComponentMk a2 := by
        rw [← hφ_mk a1, ha1, heq, ← ha2, hφ_mk a2]
      rw [← ha1, ← ha2, SimpleGraph.ConnectedComponent.eq]
      by_cases hL : G.connectedComponentMk a1 = K
      · have ha1K : a1 ∈ compVerts G K := by simp [compVerts, hL]
        have ha2K : a2 ∈ compVerts G K := by simp [compVerts, hmk_eq.symm.trans hL]
        exact (hreach_G' a1 ha1K hab1.2.1).symm.trans (hreach_G' a2 ha2K hab2.2.1)
      · obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hmk_eq
        apply walk_lift_delete p
        intro hv_sup
        obtain ⟨p1, _, _⟩ := walk_split p hv_sup
        have h1 : G.connectedComponentMk a1 = G.connectedComponentMk v :=
          SimpleGraph.ConnectedComponent.eq.mpr ⟨p1⟩
        exact hL (h1.trans hv_mk)
    have hC'_card : (activeComps G').card ≤ (activeComps G).card :=
      Finset.card_le_card_of_injOn φ hφ_maps hφ_inj
    rcases hr_adj_G' with ⟨w, hrw⟩
    refine ⟨v, hv_adj_G, ⟨r, w, hrw.1, hrw.2.1, hrw.2.2⟩, ?_⟩
    change (activeVerts G).card + (activeComps G').card ≤
      (activeVerts G').card + (activeComps G).card + 1
    omega
  · push Not at hge3
    have hsum : (activeVerts G).card ≤ 2 * (activeComps G).card := by
      rw [activeVerts_card_eq_sum]
      calc
        ∑ K ∈ activeComps G, (compVerts G K).card
            ≤ ∑ _K ∈ activeComps G, 2 := Finset.sum_le_sum (fun K hK => by have := hge3 K hK; omega)
        _ = 2 * (activeComps G).card := by simp [Nat.mul_comm]
    have hc_ge2 : 2 ≤ (activeComps G).card := by omega
    have hc_pos : 0 < (activeComps G).card := by omega
    obtain ⟨K, hK⟩ := Finset.card_pos.mp hc_pos
    have hK_card : (compVerts G K).card = 2 := by
      have h1 := compVerts_ge_two G K hK
      have h2 := hge3 K hK
      omega
    have hK_mem := hK
    simp only [activeComps, Finset.mem_filter, Finset.mem_univ, true_and] at hK_mem
    rcases hK_mem with ⟨v, w, hv_mk, hvw⟩
    have hvw_ne : v ≠ w := G.ne_of_adj hvw
    have hw_mk : G.connectedComponentMk w = K :=
      (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hvw.symm)).trans hv_mk
    have hK_eq_pair : compVerts G K = {v, w} := by
      have hsub : ({v, w} : Finset (Fin n)) ⊆ compVerts G K := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · simp [compVerts, hv_mk]
        · simp [compVerts, hw_mk]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hK_card, Finset.card_pair hvw_ne])).symm
    have hother : ∃ L ∈ activeComps G, L ≠ K := by
      by_contra h
      have hsub : activeComps G ⊆ {K} := by
        intro L hL
        by_contra hLK
        exact h ⟨L, hL, Finset.mem_singleton.not.mp hLK⟩
      have := Finset.card_le_card hsub
      simp at this
      omega
    rcases hother with ⟨L, hL, hLK⟩
    have hL_mem := hL
    simp only [activeComps, Finset.mem_filter, Finset.mem_univ, true_and] at hL_mem
    rcases hL_mem with ⟨a, b, ha_mk, hab⟩
    have ha_ne_v : a ≠ v := fun h => hLK (ha_mk.symm.trans (h ▸ hv_mk))
    have hb_ne_v : b ≠ v := by
      intro h
      have hbm : G.connectedComponentMk b = L :=
        (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hab.symm)).trans ha_mk
      exact hLK (hbm.symm.trans (h ▸ hv_mk))
    let G' := deleteVertex G v
    have hV'_eq : activeVerts G' = ((activeVerts G).erase v).erase w := by
      ext u
      simp only [activeVerts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨z, huz⟩
        refine ⟨?_, huz.2.1, z, huz.1⟩
        intro huw
        subst huw
        have hzK : z ∈ compVerts G K := by
          simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable huz.1.symm)).trans hw_mk
        rw [hK_eq_pair, Finset.mem_insert, Finset.mem_singleton] at hzK
        rcases hzK with rfl | rfl
        · exact huz.2.2 rfl
        · exact G.loopless.irrefl _ huz.1
      · rintro ⟨huw, huv, z, huz⟩
        have hzv : z ≠ v := by
          intro h
          subst h
          have huK : u ∈ compVerts G K := by
            simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and]
            exact (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable huz)).trans hv_mk
          rw [hK_eq_pair, Finset.mem_insert, Finset.mem_singleton] at huK
          rcases huK with rfl | rfl
          · exact huv rfl
          · exact huw rfl
        exact ⟨z, huz, huv, hzv⟩
    have hV'_card : (activeVerts G').card + 2 = (activeVerts G).card := by
      have hv_mem : v ∈ activeVerts G := by simp [activeVerts]; exact ⟨w, hvw⟩
      have hw_mem : w ∈ (activeVerts G).erase v := by
        rw [Finset.mem_erase]
        exact ⟨hvw_ne.symm, by simp [activeVerts]; exact ⟨v, hvw.symm⟩⟩
      rw [hV'_eq]
      have h1 := Finset.card_erase_add_one hw_mem
      have h2 := Finset.card_erase_add_one hv_mem
      omega
    let φ : G'.ConnectedComponent → G.ConnectedComponent :=
      Quot.lift (fun u => G.connectedComponentMk u)
        (fun _ _ h => SimpleGraph.ConnectedComponent.eq.mpr (walk_to_orig h))
    have hφ_mk (u : Fin n) : φ (G'.connectedComponentMk u) = G.connectedComponentMk u := rfl
    have hφ_maps : ∀ K' ∈ activeComps G', φ K' ∈ (activeComps G).erase K := by
      intro K' hK'
      simp only [activeComps, Finset.mem_filter, Finset.mem_univ, true_and] at hK'
      rcases hK' with ⟨x1, y1, hx1, hxy1⟩
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hEq
        have hx1K : x1 ∈ compVerts G K := by
          simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hφ_mk x1, hx1, hEq]
        rw [hK_eq_pair, Finset.mem_insert, Finset.mem_singleton] at hx1K
        rcases hx1K with rfl | rfl
        · exact hxy1.2.1 rfl
        · have hy1K : y1 ∈ compVerts G K := by
            simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and]
            exact (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hxy1.1.symm)).trans hw_mk
          rw [hK_eq_pair, Finset.mem_insert, Finset.mem_singleton] at hy1K
          rcases hy1K with rfl | rfl
          · exact hxy1.2.2 rfl
          · exact G.loopless.irrefl _ hxy1.1
      · simp only [activeComps, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x1, y1, by rw [← hx1, hφ_mk], hxy1.1⟩
    have hφ_inj : Set.InjOn φ (activeComps G') := by
      intro K1' hK1' K2' hK2' heq
      have hK1_ne : φ K1' ≠ K := (Finset.mem_erase.mp (hφ_maps K1' hK1')).1
      simp only [Finset.mem_coe, activeComps, Finset.mem_filter, Finset.mem_univ, true_and] at hK1' hK2'
      rcases hK1' with ⟨a1, b1, ha1, hab1⟩
      rcases hK2' with ⟨a2, b2, ha2, hab2⟩
      have hmk_eq : G.connectedComponentMk a1 = G.connectedComponentMk a2 := by
        rw [← hφ_mk a1, ha1, heq, ← ha2, hφ_mk a2]
      rw [← ha1, ← ha2, SimpleGraph.ConnectedComponent.eq]
      obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hmk_eq
      apply walk_lift_delete p
      intro hv_sup
      obtain ⟨p1, _, _⟩ := walk_split p hv_sup
      have h1 : G.connectedComponentMk a1 = G.connectedComponentMk v :=
        SimpleGraph.ConnectedComponent.eq.mpr ⟨p1⟩
      apply hK1_ne
      rw [← ha1, hφ_mk, h1, hv_mk]
    have hC'_card : (activeComps G').card + 1 ≤ (activeComps G).card := by
      have hle := Finset.card_le_card_of_injOn φ hφ_maps hφ_inj
      have h1 := Finset.card_erase_add_one hK
      omega
    refine ⟨v, ⟨w, hvw⟩, ⟨a, b, hab, ha_ne_v, hb_ne_v⟩, ?_⟩
    change (activeVerts G).card + (activeComps G').card ≤
      (activeVerts G').card + (activeComps G).card + 1
    omega

private lemma main_ind (n : ℕ) :
    ∀ (k : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ),
      A.card = k →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) →
      (activeVerts G).card ≤ A.card + (activeComps G).card + 1 := by
  intro k
  induction k with
  | zero =>
    intro G C A hAk hmono hspec hA
    by_contra hlt
    push Not at hlt
    have hbig : (activeComps G).card + 1 < (activeVerts G).card := by omega
    obtain ⟨v, ⟨w, hvw⟩, ⟨a, b, hab, hav, hbv⟩, _⟩ := exists_noncut_step G hbig
    have hdep : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
        C.eval (List.ofFn (Function.update x v true)) = true := by
      refine ⟨fun u => decide (u = w), ?_, ?_, ?_⟩
      · simp [G.ne_of_adj hvw]
      · cases hval : C.eval (List.ofFn (fun u => decide (u = w)))
        · rfl
        · exfalso
          rcases (hspec _).mp hval with ⟨u1, u2, hu12, h1, h2⟩
          simp only [decide_eq_true_eq] at h1 h2
          subst h1; subst h2
          exact G.loopless.irrefl _ hu12
      · apply (hspec _).mpr
        refine ⟨v, w, hvw, by simp, ?_⟩
        simp [Function.update, (G.ne_of_adj hvw).symm]
    have hnotbelow : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
      refine ⟨fun u => decide (u = a ∨ u = b), ?_, ?_⟩
      · simp [hav.symm, hbv.symm]
      · apply (hspec _).mpr
        exact ⟨a, b, hab, by simp, by simp⟩
    obtain ⟨j, g, _, hj, hop, _, _, _⟩ := exists_or_reading_dead n C v hmono hdep hnotbelow
    have hjA : j ∈ A := hA j g hj hop
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨j, hjA⟩
    omega
  | succ k ih =>
    intro G C A hAk hmono hspec hA
    by_cases hsmall : (activeVerts G).card ≤ (activeComps G).card + 1
    · omega
    · have hbig : (activeComps G).card + 1 < (activeVerts G).card := by omega
      obtain ⟨v, ⟨w, hvw⟩, ⟨a, b, hab, hav, hbv⟩, hstep⟩ := exists_noncut_step G hbig
      have hdep : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
          C.eval (List.ofFn (Function.update x v true)) = true := by
        refine ⟨fun u => decide (u = w), ?_, ?_, ?_⟩
        · simp [G.ne_of_adj hvw]
        · cases hval : C.eval (List.ofFn (fun u => decide (u = w)))
          · rfl
          · exfalso
            rcases (hspec _).mp hval with ⟨u1, u2, hu12, h1, h2⟩
            simp only [decide_eq_true_eq] at h1 h2
            subst h1; subst h2
            exact G.loopless.irrefl _ hu12
        · apply (hspec _).mpr
          refine ⟨v, w, hvw, by simp, ?_⟩
          simp [Function.update, (G.ne_of_adj hvw).symm]
      have hnotbelow : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
        refine ⟨fun u => decide (u = a ∨ u = b), ?_, ?_⟩
        · simp [hav.symm, hbv.symm]
        · apply (hspec _).mpr
          exact ⟨a, b, hab, by simp, by simp⟩
      obtain ⟨C', j, hjA, hmono', hA', heval'⟩ :=
        restrict_false_eliminates_or n C v A hmono hA hdep hnotbelow
      have hspec' : ∀ x : Fin n → Bool,
          C'.eval (List.ofFn x) = true ↔
            ∃ u1 u2 : Fin n, (deleteVertex G v).Adj u1 u2 ∧ x u1 = true ∧ x u2 = true := by
        intro x
        rw [heval' x, hspec (Function.update x v false)]
        constructor
        · rintro ⟨u1, u2, hu12, h1, h2⟩
          have hu1v : u1 ≠ v := fun h => by subst h; simp at h1
          have hu2v : u2 ≠ v := fun h => by subst h; simp at h2
          simp [Function.update, hu1v] at h1
          simp [Function.update, hu2v] at h2
          exact ⟨u1, u2, ⟨hu12, hu1v, hu2v⟩, h1, h2⟩
        · rintro ⟨u1, u2, ⟨hu12, hu1v, hu2v⟩, h1, h2⟩
          exact ⟨u1, u2, hu12, by simp [Function.update, hu1v, h1], by simp [Function.update, hu2v, h2]⟩
      have hA'_card : (A.erase j).card = k := by
        have := Finset.card_erase_add_one hjA
        omega
      have hih := ih (deleteVertex G v) C' (A.erase j) hA'_card hmono' hspec' hA'
      omega

end PEqualNP.Outside.L_meta_598

theorem PEqualNP.Outside.L_meta_598 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → {v : Fin n | ∃ w : Fin n, G.Adj v w}.ncard ≤ A.card + {K : G.ConnectedComponent | ∃ v w : Fin n, G.connectedComponentMk v = K ∧ G.Adj v w}.ncard + 1 := by
  intro n G C A hmono hspec hA
  rw [PEqualNP.Outside.L_meta_598.activeVerts_card_eq_ncard,
    PEqualNP.Outside.L_meta_598.activeComps_card_eq_ncard]
  exact PEqualNP.Outside.L_meta_598.main_ind n A.card G C A rfl hmono hspec hA
