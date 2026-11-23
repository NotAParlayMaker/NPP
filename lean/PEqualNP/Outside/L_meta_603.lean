import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_603

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

private lemma runWires_nil (x : List Bool) : runWires [] x = x := rfl

private lemma runWires_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    runWires (gs ++ [g]) x = stepWire (runWires gs x) g := by
  simp [runWires]

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

private def IsLive (n : ℕ) (gs : List Gate) (v : Fin n) (i : ℕ) : Prop :=
  ∀ x : Fin n → Bool, x v = true → wireVal n gs x i = true

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
              exact (ih k (by omega)).resolve_left hkd.2 x
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

private lemma exists_and_reading_live (n : ℕ) (C : Circuit) (v : Fin n)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hdep : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true)
    (hnotabove : ∃ x : Fin n → Bool, x v = true ∧ C.eval (List.ofFn x) = false) :
    ∃ (j : ℕ) (g : Gate) (i : ℕ),
      C.gates[j]? = some g ∧ g.op = GateOp.and ∧ i ∈ g.inputs ∧ i < n + j ∧
        IsLive n C.gates v i := by
  by_contra hno
  have hclass : ∀ w : ℕ, IsLive n C.gates v w ∨ IsIndep n C.gates v w := by
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
          · right
            intro x
            rw [hw_eq, wireVal_gate n C.gates _ j g hj_get, wireVal_gate n C.gates _ j g hj_get]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hlt : k < n + j
            · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hlt)),
                ite_eq_left_iff.mpr (fun h => False.elim (h hlt))]
              have hnl : ¬ IsLive n C.gates v k := fun hl =>
                hno ⟨j, g, k, hj_get, hop, hk, hlt, hl⟩
              exact (ih k (by omega)).resolve_left hnl x
            · simp [hlt]
          · by_cases hex : ∃ k ∈ g.inputs, k < n + j ∧ IsLive n C.gates v k
            · left
              rcases hex with ⟨k, hk, hlt, hl⟩
              intro x hx
              rw [hw_eq, wireVal_gate n C.gates x j g hj_get, hop, GateOp.eval, List.any_eq_true]
              refine ⟨true, List.mem_map.mpr ⟨k, hk, ?_⟩, rfl⟩
              simp [hlt, hl x hx]
            · right
              intro x
              rw [hw_eq, wireVal_gate n C.gates _ j g hj_get, wireVal_gate n C.gates _ j g hj_get]
              congr 1
              apply List.map_congr_left
              intro k hk
              by_cases hlt : k < n + j
              · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hlt)),
                  ite_eq_left_iff.mpr (fun h => False.elim (h hlt))]
                have hnl : ¬ IsLive n C.gates v k := fun hl => hex ⟨k, hk, hlt, hl⟩
                exact (ih k (by omega)).resolve_left hnl x
              · simp [hlt]
        · right
          intro x
          rw [wireVal_of_ge n C.gates _ w (by omega), wireVal_of_ge n C.gates _ w (by omega)]
  rcases hclass C.output with hlive | hindep
  · rcases hnotabove with ⟨x, hxv, hx0⟩
    have := hlive x hxv
    change C.eval (List.ofFn x) = true at this
    rw [hx0] at this
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

private lemma restrict_false_or_elim (n : ℕ) (C : Circuit) (v : Fin n) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A)
    (hnotbelow : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true) :
    ∃ (C' : Circuit),
      PEqualNP.MetaComplexity.Monotone2 C' ∧
      (∀ (k : ℕ) (g' : Gate), C'.gates[k]? = some g' → g'.op = GateOp.or →
        k ∈ A ∧ ∀ (g : Gate), C.gates[k]? = some g →
          ∀ i ∈ g.inputs, i < n + k → ¬ IsDead n C.gates v i) ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) := by
  classical
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
    rw [← Option.some.inj hke]
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
          | cons _ _ => exact hg_mono
  have hA' : ∀ (k : ℕ) (g' : Gate), C'.gates[k]? = some g' → g'.op = GateOp.or →
      k ∈ A ∧ ∀ (g : Gate), C.gates[k]? = some g →
        ∀ i ∈ g.inputs, i < n + k → ¬ dead i := by
    intro k g' hk' hop'
    rw [hget'] at hk'
    cases hkC : C.gates[k]? with
    | none => rw [hkC] at hk'; simp at hk'
    | some g =>
      rw [hkC, Option.map_some] at hk'
      rw [← Option.some.inj hk'] at hop'
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
        rw [ite_eq_left_iff.mpr (fun h => False.elim (h hd))] at hop'
        cases hop'
      have hnot_and : g.op ≠ GateOp.and := by
        intro hand
        dsimp only [simpGate] at hop'
        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_nk h)),
          ite_eq_left_iff.mpr (fun h => False.elim (h hand)), hand] at hop'
        cases hop'
      have hg_or : g.op = GateOp.or := hg_mono.1.resolve_left hnot_and
      refine ⟨hA k g hkC hg_or, ?_⟩
      intro g1 hg1 i hi hilt hdi
      have hgeq : g1 = g := Option.some.inj hg1.symm
      subst hgeq
      dsimp only [simpGate] at hop'
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_nk h)),
        ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h))] at hop'
      have hglen := hg_mono.2
      cases hgin : g1.inputs with
      | nil => rw [hgin] at hop'; cases hop'
      | cons a tl =>
        cases tl with
        | nil => rw [hgin] at hop'; cases hop'
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hi hop'
            dsimp only at hop'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · have ha : i ≥ n + k ∨ dead i := Or.inr hdi
              rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha))] at hop'
              cases hop'
            · by_cases ha : a ≥ n + k ∨ dead a
              · rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha))] at hop'
                cases hop'
              · have hb : i ≥ n + k ∨ dead i := Or.inr hdi
                rw [ite_eq_right_iff.mpr (fun h => False.elim (ha h)),
                  ite_eq_left_iff.mpr (fun h => False.elim (h hb))] at hop'
                cases hop'
          | cons _ _ =>
            rw [hgin] at hglen; simp at hglen
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
          have hk' : C'.gates[k]? = some (simpGate k g) := by rw [hget', hkC, Option.map_some]
          have hg_mono := hmono g (List.getElem_mem hk_lt)
          have hnd_k : ¬ dead (n + k) := hw_eq ▸ hnd
          rw [hw_eq, wireVal_gate n C'.gates x k (simpGate k g) hk',
            wireVal_gate n C.gates (Function.update x v false) k g hkC]
          rcases hg_mono.1 with hop | hop
          · have hsg : simpGate k g = g := by
              dsimp only [simpGate]
              rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                ite_eq_left_iff.mpr (fun h => False.elim (h hop))]
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
                · have had : dead a := by by_contra hna; exact hbad ⟨hlt, hna⟩
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
          · have hnot_and : g.op ≠ GateOp.and := by rw [hop]; intro h; cases h
            have hglen := hg_mono.2
            cases hgin : g.inputs with
            | nil =>
              exfalso; apply hnd_k; intro y _
              rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]; rfl
            | cons a tl =>
              cases tl with
              | nil =>
                have hsg : simpGate k g = ⟨GateOp.and, [a]⟩ := by
                  dsimp only [simpGate]
                  rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                    ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                have ha_ok : a < n + k ∧ ¬ dead a := by
                  by_contra hbad
                  apply hnd_k; intro y hy
                  rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
                  by_cases hlt : a < n + k
                  · have had : dead a := by by_contra hna; exact hbad ⟨hlt, hna⟩
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
                      apply hnd_k; intro y hy
                      rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                        Bool.or_false, ha_f y hy, Bool.false_or]
                      by_cases hlt : b < n + k
                      · have hbd : dead b := by by_contra hnb; exact hbad ⟨hlt, hnb⟩
                        simp [hlt, hbd y hy]
                      · simp [hlt]
                    have hsg : simpGate k g = ⟨GateOp.and, [b]⟩ := by
                      dsimp only [simpGate]
                      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                        ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                      dsimp only
                      rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_bad))]
                    rw [hsg, hop]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                      List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
                      ha_f (Function.update x v false) hv_upd, Bool.false_or,
                      ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                    exact ih b (by omega) hb_ok.2 x
                  · have ha_ok : a < n + k ∧ ¬ dead a := ⟨by omega, fun h => ha_bad (Or.inr h)⟩
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
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                        dsimp only
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (ha_bad h)),
                          ite_eq_left_iff.mpr (fun h => False.elim (h hb_bad))]
                      rw [hsg, hop]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
                        hb_f (Function.update x v false) hv_upd, Bool.or_false,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
                      exact ih a (by omega) ha_ok.2 x
                    · have hb_ok : b < n + k ∧ ¬ dead b := ⟨by omega, fun h => hb_bad (Or.inr h)⟩
                      have hsg : simpGate k g = g := by
                        dsimp only [simpGate]
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                        dsimp only
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (ha_bad h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hb_bad h))]
                      rw [hsg, hop, hgin]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        id, Bool.or_false,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1)),
                        ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                      rw [ih a (by omega) ha_ok.2 x, ih b (by omega) hb_ok.2 x]
                | cons _ _ => rw [hgin] at hglen; simp at hglen
        · exfalso; apply hnd; intro y _; exact wireVal_of_ge n C.gates y w (by omega)
  have hout_nd : ¬ dead C.output := by
    intro hd
    rcases hnotbelow with ⟨x, hxv, hx1⟩
    have := hd x hxv
    change C.eval (List.ofFn x) = false at this
    rw [hx1] at this
    cases this
  exact ⟨C', hmono', hA', fun x => hwire C.output hout_nd x⟩

private lemma restrict_true_and_elim (n : ℕ) (C : Circuit) (v : Fin n) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (hdep : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true)
    (hnotabove : ∃ x : Fin n → Bool, x v = true ∧ C.eval (List.ofFn x) = false) :
    ∃ (C' : Circuit) (j : ℕ),
      j ∈ A ∧
      PEqualNP.MetaComplexity.Monotone2 C' ∧
      (∀ (k : ℕ) (g : Gate), C'.gates[k]? = some g → g.op = GateOp.and → k ∈ A.erase j) ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v true))) := by
  classical
  obtain ⟨j0, g0, i0, hj0, hg0_op, hi0_mem, hi0_lt, hi0_live⟩ :=
    exists_and_reading_live n C v hmono hdep hnotabove
  have hj0A : j0 ∈ A := hA j0 g0 hj0 hg0_op
  let live : ℕ → Prop := IsLive n C.gates v
  let simpGate : ℕ → Gate → Gate := fun k g =>
    if live (n + k) then ⟨GateOp.or, []⟩
    else if g.op = GateOp.or then g
    else
      match g.inputs with
      | [] => ⟨GateOp.or, []⟩
      | [a] => if a ≥ n + k then ⟨GateOp.or, []⟩ else ⟨GateOp.or, [a]⟩
      | [a, b] =>
        if a ≥ n + k ∨ b ≥ n + k then ⟨GateOp.or, []⟩
        else if live a then ⟨GateOp.or, [b]⟩
        else if live b then ⟨GateOp.or, [a]⟩
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
    rw [← Option.some.inj hke]
    have hg_mono := hmono C.gates[k] (List.getElem_mem hk_lt_C)
    dsimp only [simpGate]
    split_ifs
    · simp
    · exact hg_mono
    · cases hgin : C.gates[k].inputs with
      | nil => simp
      | cons a tl =>
        cases tl with
        | nil => dsimp only; split_ifs <;> simp
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            dsimp only
            split_ifs
            · simp
            · simp
            · simp
            · exact hg_mono
          | cons _ _ => exact hg_mono
  have hA' : ∀ (k : ℕ) (g' : Gate), C'.gates[k]? = some g' → g'.op = GateOp.and → k ∈ A.erase j0 := by
    intro k g' hk' hop'
    rw [hget'] at hk'
    cases hkC : C.gates[k]? with
    | none => rw [hkC] at hk'; simp at hk'
    | some g =>
      rw [hkC, Option.map_some] at hk'
      rw [← Option.some.inj hk'] at hop'
      have hk_lt : k < C.gates.length := by
        by_contra h
        rw [List.getElem?_eq_none (not_lt.mp h)] at hkC
        simp at hkC
      have hg_mono := hmono g (by
        rw [List.getElem?_eq_getElem hk_lt] at hkC
        rw [← Option.some.inj hkC]
        exact List.getElem_mem hk_lt)
      have hnl_nk : ¬ live (n + k) := by
        intro hl
        dsimp only [simpGate] at hop'
        rw [ite_eq_left_iff.mpr (fun h => False.elim (h hl))] at hop'
        cases hop'
      have hnot_or : g.op ≠ GateOp.or := by
        intro hor
        dsimp only [simpGate] at hop'
        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_nk h)),
          ite_eq_left_iff.mpr (fun h => False.elim (h hor)), hor] at hop'
        cases hop'
      have hg_and : g.op = GateOp.and := hg_mono.1.resolve_right hnot_or
      apply Finset.mem_erase.mpr
      refine ⟨?_, hA k g hkC hg_and⟩
      intro hkj
      subst hkj
      rw [hj0] at hkC
      have hgeq : g = g0 := Option.some.inj hkC.symm
      subst hgeq
      dsimp only [simpGate] at hop'
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_nk h)),
        ite_eq_right_iff.mpr (fun h => False.elim (hnot_or h))] at hop'
      have hglen := hg_mono.2
      cases hgin : g.inputs with
      | nil => rw [hgin] at hop'; cases hop'
      | cons a tl =>
        cases tl with
        | nil =>
          rw [hgin] at hop'; dsimp only at hop'
          by_cases ha : a ≥ n + k
          · rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha))] at hop'; cases hop'
          · rw [ite_eq_right_iff.mpr (fun h => False.elim (ha h))] at hop'; cases hop'
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hi0_mem hop'
            dsimp only at hop'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0_mem
            by_cases hoob : a ≥ n + k ∨ b ≥ n + k
            · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hoob))] at hop'
              cases hop'
            · rw [ite_eq_right_iff.mpr (fun h => False.elim (hoob h))] at hop'
              rcases hi0_mem with rfl | rfl
              · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hi0_live))] at hop'
                cases hop'
              · by_cases hla : live a
                · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hla))] at hop'
                  cases hop'
                · rw [ite_eq_right_iff.mpr (fun h => False.elim (hla h)),
                    ite_eq_left_iff.mpr (fun h => False.elim (h hi0_live))] at hop'
                  cases hop'
          | cons _ _ => rw [hgin] at hglen; simp at hglen
  have hwire : ∀ w : ℕ, ¬ live w → ∀ x : Fin n → Bool,
      wireVal n C'.gates x w = wireVal n C.gates (Function.update x v true) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hnl x
      have hv_upd : Function.update x v true v = true := by simp
      by_cases hwn : w < n
      · rw [wireVal_input n C'.gates x w hwn, wireVal_input n C.gates _ w hwn]
        have hne : (⟨w, hwn⟩ : Fin n) ≠ v := by
          intro heq
          apply hnl
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
          have hk' : C'.gates[k]? = some (simpGate k g) := by rw [hget', hkC, Option.map_some]
          have hg_mono := hmono g (List.getElem_mem hk_lt)
          have hnl_k : ¬ live (n + k) := hw_eq ▸ hnl
          rw [hw_eq, wireVal_gate n C'.gates x k (simpGate k g) hk',
            wireVal_gate n C.gates (Function.update x v true) k g hkC]
          rcases hg_mono.1 with hop | hop
          · have hnot_or : g.op ≠ GateOp.or := by rw [hop]; intro h; cases h
            have hglen := hg_mono.2
            cases hgin : g.inputs with
            | nil =>
              exfalso; apply hnl_k; intro y _
              rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]; rfl
            | cons a tl =>
              cases tl with
              | nil =>
                by_cases haoob : a ≥ n + k
                · have hsg : simpGate k g = ⟨GateOp.or, []⟩ := by
                    dsimp only [simpGate]
                    rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_k h)),
                      ite_eq_right_iff.mpr (fun h => False.elim (hnot_or h)), hgin]
                    dsimp only
                    rw [ite_eq_left_iff.mpr (fun h => False.elim (h haoob))]
                  rw [hsg, hop]
                  simp [GateOp.eval, not_lt.mpr haoob]
                · have ha_lt : a < n + k := by omega
                  have ha_nl : ¬ live a := by
                    intro hla
                    apply hnl_k; intro y hy
                    rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                    simp [ha_lt, hla y hy]
                  have hsg : simpGate k g = ⟨GateOp.or, [a]⟩ := by
                    dsimp only [simpGate]
                    rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_k h)),
                      ite_eq_right_iff.mpr (fun h => False.elim (hnot_or h)), hgin]
                    dsimp only
                    rw [ite_eq_right_iff.mpr (fun h => False.elim (haoob h))]
                  rw [hsg, hop]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                    List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true,
                    ite_eq_left_iff.mpr (fun h => False.elim (h ha_lt))]
                  exact ih a (by omega) ha_nl x
              | cons b tl2 =>
                cases tl2 with
                | nil =>
                  by_cases hoob : a ≥ n + k ∨ b ≥ n + k
                  · have hsg : simpGate k g = ⟨GateOp.or, []⟩ := by
                      dsimp only [simpGate]
                      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_k h)),
                        ite_eq_right_iff.mpr (fun h => False.elim (hnot_or h)), hgin]
                      dsimp only
                      rw [ite_eq_left_iff.mpr (fun h => False.elim (h hoob))]
                    rw [hsg, hop]
                    rcases hoob with ha | hb
                    · simp [GateOp.eval, not_lt.mpr ha]
                    · simp [GateOp.eval, not_lt.mpr hb]
                  · have ha_lt : a < n + k := by omega
                    have hb_lt : b < n + k := by omega
                    by_cases hla : live a
                    · have hlb : ¬ live b := by
                        intro hb
                        apply hnl_k; intro y hy
                        rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                        simp [ha_lt, hb_lt, hla y hy, hb y hy]
                      have hsg : simpGate k g = ⟨GateOp.or, [b]⟩ := by
                        dsimp only [simpGate]
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_k h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hnot_or h)), hgin]
                        dsimp only
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hoob h)),
                          ite_eq_left_iff.mpr (fun h => False.elim (h hla))]
                      rw [hsg, hop]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_lt)),
                        ite_eq_left_iff.mpr (fun h => False.elim (h hb_lt)),
                        hla (Function.update x v true) hv_upd, Bool.true_and]
                      exact ih b (by omega) hlb x
                    · by_cases hlb : live b
                      · have hsg : simpGate k g = ⟨GateOp.or, [a]⟩ := by
                          dsimp only [simpGate]
                          rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_k h)),
                            ite_eq_right_iff.mpr (fun h => False.elim (hnot_or h)), hgin]
                          dsimp only
                          rw [ite_eq_right_iff.mpr (fun h => False.elim (hoob h)),
                            ite_eq_right_iff.mpr (fun h => False.elim (hla h)),
                            ite_eq_left_iff.mpr (fun h => False.elim (h hlb))]
                        rw [hsg, hop]
                        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                          List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true,
                          ite_eq_left_iff.mpr (fun h => False.elim (h ha_lt)),
                          ite_eq_left_iff.mpr (fun h => False.elim (h hb_lt)),
                          hlb (Function.update x v true) hv_upd, Bool.and_true]
                        exact ih a (by omega) hla x
                      · have hsg : simpGate k g = g := by
                          dsimp only [simpGate]
                          rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_k h)),
                            ite_eq_right_iff.mpr (fun h => False.elim (hnot_or h)), hgin]
                          dsimp only
                          rw [ite_eq_right_iff.mpr (fun h => False.elim (hoob h)),
                            ite_eq_right_iff.mpr (fun h => False.elim (hla h)),
                            ite_eq_right_iff.mpr (fun h => False.elim (hlb h))]
                        rw [hsg, hop, hgin]
                        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                          id, Bool.and_true,
                          ite_eq_left_iff.mpr (fun h => False.elim (h ha_lt)),
                          ite_eq_left_iff.mpr (fun h => False.elim (h hb_lt))]
                        rw [ih a (by omega) hla x, ih b (by omega) hlb x]
                | cons _ _ => rw [hgin] at hglen; simp at hglen
          · rw [Set.mem_singleton_iff] at hop
            have hsg : simpGate k g = g := by
              dsimp only [simpGate]
              rw [ite_eq_right_iff.mpr (fun h => False.elim (hnl_k h)),
                ite_eq_left_iff.mpr (fun h => False.elim (h hop))]
            rw [hsg]
            congr 1
            apply List.map_congr_left
            intro a ha
            by_cases ha_lt : a < n + k
            · have ha_nl : ¬ live a := by
                intro hla
                apply hnl_k; intro y hy
                rw [wireVal_gate n C.gates y k g hkC, hop, GateOp.eval, List.any_eq_true]
                exact ⟨true, List.mem_map.mpr ⟨a, ha, by simp [ha_lt, hla y hy]⟩, rfl⟩
              rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_lt)),
                ite_eq_left_iff.mpr (fun h => False.elim (h ha_lt))]
              exact ih a (by omega) ha_nl x
            · simp [ha_lt]
        · rw [wireVal_of_ge n C'.gates x w (by omega), wireVal_of_ge n C.gates _ w (by omega)]
  have hout_nl : ¬ live C.output := by
    intro hl
    rcases hnotabove with ⟨x, hxv, hx0⟩
    have := hl x hxv
    change C.eval (List.ofFn x) = true at this
    rw [hx0] at this
    cases this
  exact ⟨C', j0, hj0A, hmono', hA', fun x => hwire C.output hout_nl x⟩

private lemma restrict_false_no_new_and (n : ℕ) (C : Circuit) (v : Fin n) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ (C' : Circuit),
      PEqualNP.MetaComplexity.Monotone2 C' ∧
      (∀ (k : ℕ) (g : Gate), C'.gates[k]? = some g → g.op = GateOp.and → k ∈ A) ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) := by
  classical
  let dead : ℕ → Prop := IsDead n C.gates v
  let simpGate : ℕ → Gate → Gate := fun k g =>
    if dead (n + k) then ⟨GateOp.or, []⟩
    else if g.op = GateOp.and then g
    else
      match g.inputs with
      | [] => ⟨GateOp.or, []⟩
      | [a] => ⟨GateOp.or, [a]⟩
      | [a, b] =>
        if a ≥ n + k ∨ dead a then ⟨GateOp.or, [b]⟩
        else if b ≥ n + k ∨ dead b then ⟨GateOp.or, [a]⟩
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
    rw [← Option.some.inj hke]
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
            dsimp only; split_ifs
            · simp
            · simp
            · exact hg_mono
          | cons _ _ => exact hg_mono
  have hA' : ∀ (k : ℕ) (g' : Gate), C'.gates[k]? = some g' → g'.op = GateOp.and → k ∈ A := by
    intro k g' hk' hop'
    rw [hget'] at hk'
    cases hkC : C.gates[k]? with
    | none => rw [hkC] at hk'; simp at hk'
    | some g =>
      rw [hkC, Option.map_some] at hk'
      rw [← Option.some.inj hk'] at hop'
      have hnd_nk : ¬ dead (n + k) := by
        intro hd; dsimp only [simpGate] at hop'
        rw [ite_eq_left_iff.mpr (fun h => False.elim (h hd))] at hop'; cases hop'
      by_cases hand : g.op = GateOp.and
      · exact hA k g hkC hand
      · exfalso
        dsimp only [simpGate] at hop'
        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_nk h)),
          ite_eq_right_iff.mpr (fun h => False.elim (hand h))] at hop'
        have hk_lt : k < C.gates.length := by
          by_contra h; rw [List.getElem?_eq_none (not_lt.mp h)] at hkC; simp at hkC
        have hg_mono := hmono g (by
          rw [List.getElem?_eq_getElem hk_lt] at hkC
          rw [← Option.some.inj hkC]; exact List.getElem_mem hk_lt)
        have hglen := hg_mono.2
        have hor : g.op = GateOp.or := hg_mono.1.resolve_left hand
        cases hgin : g.inputs with
        | nil => rw [hgin] at hop'; cases hop'
        | cons a tl =>
          cases tl with
          | nil => rw [hgin] at hop'; cases hop'
          | cons b tl2 =>
            cases tl2 with
            | nil =>
              rw [hgin] at hop'; dsimp only at hop'
              by_cases ha_bad : a ≥ n + k ∨ dead a
              · rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_bad))] at hop'; cases hop'
              · rw [ite_eq_right_iff.mpr (fun h => False.elim (ha_bad h))] at hop'
                by_cases hb_bad : b ≥ n + k ∨ dead b
                · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hb_bad))] at hop'; cases hop'
                · rw [ite_eq_right_iff.mpr (fun h => False.elim (hb_bad h)), hor] at hop'; cases hop'
            | cons _ _ => rw [hgin] at hglen; simp at hglen
  have hwire : ∀ w : ℕ, ∀ x : Fin n → Bool,
      (dead w → (w < n → w = v.val) → True) ∧
      (¬ dead w → wireVal n C'.gates x w = wireVal n C.gates (Function.update x v false) w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x
      refine ⟨fun _ _ => trivial, fun hnd => ?_⟩
      have hv_upd : Function.update x v false v = false := by simp
      by_cases hwn : w < n
      · rw [wireVal_input n C'.gates x w hwn, wireVal_input n C.gates _ w hwn]
        have hne : (⟨w, hwn⟩ : Fin n) ≠ v := by
          intro heq; apply hnd; intro y hy; rw [wireVal_input n C.gates y w hwn, heq]; exact hy
        simp [Function.update, hne]
      · by_cases hwlen : w < n + C.gates.length
        · let k := w - n
          have hk_lt : k < C.gates.length := by omega
          have hw_eq : w = n + k := by omega
          let g := C.gates[k]
          have hkC : C.gates[k]? = some g := List.getElem?_eq_getElem hk_lt
          have hk' : C'.gates[k]? = some (simpGate k g) := by rw [hget', hkC, Option.map_some]
          have hg_mono := hmono g (List.getElem_mem hk_lt)
          have hnd_k : ¬ dead (n + k) := hw_eq ▸ hnd
          rw [hw_eq, wireVal_gate n C'.gates x k (simpGate k g) hk',
            wireVal_gate n C.gates (Function.update x v false) k g hkC]
          rcases hg_mono.1 with hop | hop
          · have hsg : simpGate k g = g := by
              dsimp only [simpGate]
              rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                ite_eq_left_iff.mpr (fun h => False.elim (h hop))]
            rw [hsg]; congr 1; apply List.map_congr_left; intro a ha
            have ha_ok : a < n + k ∧ ¬ dead a := by
              by_contra hbad; apply hnd_k; intro y hy
              rw [wireVal_gate n C.gates y k g hkC, hop, GateOp.eval]
              have haf : (if a < n + k then wireVal n C.gates y a else false) = false := by
                by_cases hlt : a < n + k
                · have had : dead a := by by_contra hna; exact hbad ⟨hlt, hna⟩
                  simp [hlt, had y hy]
                · simp [hlt]
              cases hval : (g.inputs.map fun a => if a < n + k then wireVal n C.gates y a else false).all id
              · rfl
              · exfalso; rw [List.all_eq_true] at hval
                have := hval _ (List.mem_map_of_mem ha); simp [haf] at this
            rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1)),
              ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
            exact (ih a (by omega) x).2 ha_ok.2
          · have hnot_and : g.op ≠ GateOp.and := by rw [hop]; intro h; cases h
            have hglen := hg_mono.2
            cases hgin : g.inputs with
            | nil =>
              exfalso; apply hnd_k; intro y _
              rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]; rfl
            | cons a tl =>
              cases tl with
              | nil =>
                have hsg : simpGate k g = ⟨GateOp.or, [a]⟩ := by
                  dsimp only [simpGate]
                  rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                    ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                have ha_ok : a < n + k ∧ ¬ dead a := by
                  by_contra hbad; apply hnd_k; intro y hy
                  rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
                  by_cases hlt : a < n + k
                  · have had : dead a := by by_contra hna; exact hbad ⟨hlt, hna⟩
                    simp [hlt, had y hy]
                  · simp [hlt]
                rw [hsg, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id, Bool.or_false, ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
                exact (ih a (by omega) x).2 ha_ok.2
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
                      by_contra hbad; apply hnd_k; intro y hy
                      rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                        Bool.or_false, ha_f y hy, Bool.false_or]
                      by_cases hlt : b < n + k
                      · have hbd : dead b := by by_contra hnb; exact hbad ⟨hlt, hnb⟩
                        simp [hlt, hbd y hy]
                      · simp [hlt]
                    have hsg : simpGate k g = ⟨GateOp.or, [b]⟩ := by
                      dsimp only [simpGate]
                      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                        ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                      dsimp only
                      rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_bad))]
                    rw [hsg, hop]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id, Bool.or_false, ha_f (Function.update x v false) hv_upd, Bool.false_or,
                      ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                    exact (ih b (by omega) x).2 hb_ok.2
                  · have ha_ok : a < n + k ∧ ¬ dead a := ⟨by omega, fun h => ha_bad (Or.inr h)⟩
                    by_cases hb_bad : b ≥ n + k ∨ dead b
                    · have hb_f (y : Fin n → Bool) (hy : y v = false) :
                          (if b < n + k then wireVal n C.gates y b else false) = false := by
                        rcases hb_bad with hge | hbd
                        · simp [not_lt.mpr hge]
                        · by_cases hlt : b < n + k
                          · simp [hlt, hbd y hy]
                          · simp [hlt]
                      have hsg : simpGate k g = ⟨GateOp.or, [a]⟩ := by
                        dsimp only [simpGate]
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                        dsimp only
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (ha_bad h)),
                          ite_eq_left_iff.mpr (fun h => False.elim (h hb_bad))]
                      rw [hsg, hop]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        id, Bool.or_false, hb_f (Function.update x v false) hv_upd,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
                      exact (ih a (by omega) x).2 ha_ok.2
                    · have hb_ok : b < n + k ∧ ¬ dead b := ⟨by omega, fun h => hb_bad (Or.inr h)⟩
                      have hsg : simpGate k g = g := by
                        dsimp only [simpGate]
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                        dsimp only
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (ha_bad h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hb_bad h))]
                      rw [hsg, hop, hgin]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        id, Bool.or_false,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1)),
                        ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                      rw [(ih a (by omega) x).2 ha_ok.2, (ih b (by omega) x).2 hb_ok.2]
                | cons _ _ => rw [hgin] at hglen; simp at hglen
        · exfalso; apply hnd; intro y _; exact wireVal_of_ge n C.gates y w (by omega)
  by_cases hout : dead C.output
  · refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], by intro _ _ h; simp at h, ?_⟩
    intro x
    have h1 := hout (Function.update x v false) (by simp)
    change C.eval (List.ofFn (Function.update x v false)) = false at h1
    rw [h1]
    apply getD_of_ge
    simp [Circuit.wires]
  · exact ⟨C', hmono', hA', fun x => (hwire C.output x).2 hout⟩

private lemma replace_gate_same_val (n : ℕ) (C : Circuit) (p : ℕ) (g' : Gate)
    (hp : p < C.gates.length)
    (hg'_mono : g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hval : ∀ x : Fin n → Bool,
      g'.op.eval (g'.inputs.map fun k => if k < n + p then wireVal n C.gates x k else false) =
        wireVal n C.gates x (n + p)) :
    let C' : Circuit := ⟨C.gates.set p g', C.output⟩
    PEqualNP.MetaComplexity.Monotone2 C' ∧
    (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
    (∀ (k : ℕ) (g : Gate), C'.gates[k]? = some g → g.op = GateOp.or →
      (k = p ∧ g'.op = GateOp.or) ∨ (k ≠ p ∧ C.gates[k]? = some g)) := by
  intro C'
  have hlen' : C'.gates.length = C.gates.length := List.length_set
  have hget' (k : ℕ) : C'.gates[k]? = if k = p then some g' else C.gates[k]? := by
    by_cases hkp : k = p
    · subst hkp
      rw [ite_eq_left_iff.mpr (fun h => False.elim (h rfl))]
      have hlt : k < C'.gates.length := by omega
      rw [List.getElem?_eq_getElem hlt]
      simp [C']
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (hkp h))]
      exact List.getElem?_set_ne (Ne.symm hkp)
  have hmono' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    obtain ⟨k, hk_lt, rfl⟩ := List.mem_iff_getElem.mp hg
    have hke : C'.gates[k]? = some C'.gates[k] := List.getElem?_eq_getElem hk_lt
    rw [hget'] at hke
    by_cases hkp : k = p
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hkp))] at hke
      rw [← Option.some.inj hke]
      exact hg'_mono
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (hkp h))] at hke
      have hk_lt_C : k < C.gates.length := by omega
      rw [List.getElem?_eq_getElem hk_lt_C] at hke
      rw [← Option.some.inj hke]
      exact hmono C.gates[k] (List.getElem_mem hk_lt_C)
  have hwire : ∀ w : ℕ, ∀ x : Fin n → Bool, wireVal n C'.gates x w = wireVal n C.gates x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x
      by_cases hwn : w < n
      · rw [wireVal_input n C'.gates x w hwn, wireVal_input n C.gates x w hwn]
      · by_cases hwlen : w < n + C.gates.length
        · let k := w - n
          have hk_lt : k < C.gates.length := by omega
          have hw_eq : w = n + k := by omega
          by_cases hkp : k = p
          · subst hkp
            have hk' : C'.gates[k]? = some g' := by rw [hget']; simp
            rw [hw_eq, wireVal_gate n C'.gates x k g' hk', ← hval x]
            congr 1
            apply List.map_congr_left
            intro a _
            by_cases ha : a < n + k
            · simp [ha, ih a (by omega) x]
            · simp [ha]
          · have hkC : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk_lt
            have hk' : C'.gates[k]? = some C.gates[k] := by
              rw [hget', ite_eq_right_iff.mpr (fun h => False.elim (hkp h)), hkC]
            rw [hw_eq, wireVal_gate n C'.gates x k C.gates[k] hk',
              wireVal_gate n C.gates x k C.gates[k] hkC]
            congr 1
            apply List.map_congr_left
            intro a _
            by_cases ha : a < n + k
            · simp [ha, ih a (by omega) x]
            · simp [ha]
        · rw [wireVal_of_ge n C'.gates x w (by omega), wireVal_of_ge n C.gates x w (by omega)]
  refine ⟨hmono', fun x => hwire C.output x, ?_⟩
  intro k g hk hop
  rw [hget'] at hk
  by_cases hkp : k = p
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hkp))] at hk
    have hgeq := Option.some.inj hk
    left
    exact ⟨hkp, hgeq ▸ hop⟩
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hkp h))] at hk
    right
    exact ⟨hkp, hk⟩

private lemma elim_const_false_or (n : ℕ) (C : Circuit) (p : ℕ) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A)
    (hp_false : ∀ x : Fin n → Bool, wireVal n C.gates x (n + p) = false)
    (hout_true : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    ∃ (C' : Circuit),
      PEqualNP.MetaComplexity.Monotone2 C' ∧
      (∀ (k : ℕ) (g : Gate), C'.gates[k]? = some g → g.op = GateOp.or → k ∈ A.erase p) ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) := by
  classical
  let dead : ℕ → Prop := fun w => ∀ x : Fin n → Bool, wireVal n C.gates x w = false
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
    rw [← Option.some.inj hke]
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
            dsimp only; split_ifs
            · simp
            · simp
            · exact hg_mono
          | cons _ _ => exact hg_mono
  have hA' : ∀ (k : ℕ) (g' : Gate), C'.gates[k]? = some g' → g'.op = GateOp.or → k ∈ A.erase p := by
    intro k g' hk' hop'
    rw [hget'] at hk'
    cases hkC : C.gates[k]? with
    | none => rw [hkC] at hk'; simp at hk'
    | some g =>
      rw [hkC, Option.map_some] at hk'
      rw [← Option.some.inj hk'] at hop'
      have hnd_nk : ¬ dead (n + k) := by
        intro hd; dsimp only [simpGate] at hop'
        rw [ite_eq_left_iff.mpr (fun h => False.elim (h hd))] at hop'; cases hop'
      have hnot_and : g.op ≠ GateOp.and := by
        intro hand; dsimp only [simpGate] at hop'
        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_nk h)),
          ite_eq_left_iff.mpr (fun h => False.elim (h hand)), hand] at hop'; cases hop'
      have hk_lt : k < C.gates.length := by
        by_contra h; rw [List.getElem?_eq_none (not_lt.mp h)] at hkC; simp at hkC
      have hg_mono := hmono g (by
        rw [List.getElem?_eq_getElem hk_lt] at hkC
        rw [← Option.some.inj hkC]; exact List.getElem_mem hk_lt)
      have hg_or : g.op = GateOp.or := hg_mono.1.resolve_left hnot_and
      apply Finset.mem_erase.mpr
      refine ⟨fun hkp => hnd_nk (hkp ▸ hp_false), hA k g hkC hg_or⟩
  have hwire : ∀ w : ℕ, ¬ dead w → ∀ x : Fin n → Bool,
      wireVal n C'.gates x w = wireVal n C.gates x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hnd x
      by_cases hwn : w < n
      · rw [wireVal_input n C'.gates x w hwn, wireVal_input n C.gates x w hwn]
      · by_cases hwlen : w < n + C.gates.length
        · let k := w - n
          have hk_lt : k < C.gates.length := by omega
          have hw_eq : w = n + k := by omega
          let g := C.gates[k]
          have hkC : C.gates[k]? = some g := List.getElem?_eq_getElem hk_lt
          have hk' : C'.gates[k]? = some (simpGate k g) := by rw [hget', hkC, Option.map_some]
          have hg_mono := hmono g (List.getElem_mem hk_lt)
          have hnd_k : ¬ dead (n + k) := hw_eq ▸ hnd
          rw [hw_eq, wireVal_gate n C'.gates x k (simpGate k g) hk',
            wireVal_gate n C.gates x k g hkC]
          rcases hg_mono.1 with hop | hop
          · have hsg : simpGate k g = g := by
              dsimp only [simpGate]
              rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                ite_eq_left_iff.mpr (fun h => False.elim (h hop))]
            rw [hsg]; congr 1; apply List.map_congr_left; intro a ha
            have ha_ok : a < n + k ∧ ¬ dead a := by
              by_contra hbad; apply hnd_k; intro y
              rw [wireVal_gate n C.gates y k g hkC, hop, GateOp.eval]
              have haf : (if a < n + k then wireVal n C.gates y a else false) = false := by
                by_cases hlt : a < n + k
                · have had : dead a := by by_contra hna; exact hbad ⟨hlt, hna⟩
                  simp [hlt, had y]
                · simp [hlt]
              cases hval : (g.inputs.map fun a => if a < n + k then wireVal n C.gates y a else false).all id
              · rfl
              · exfalso; rw [List.all_eq_true] at hval
                have := hval _ (List.mem_map_of_mem ha); simp [haf] at this
            rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1)),
              ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
            exact ih a (by omega) ha_ok.2 x
          · have hnot_and : g.op ≠ GateOp.and := by rw [hop]; intro h; cases h
            have hglen := hg_mono.2
            cases hgin : g.inputs with
            | nil =>
              exfalso; apply hnd_k; intro y
              rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]; rfl
            | cons a tl =>
              cases tl with
              | nil =>
                have hsg : simpGate k g = ⟨GateOp.and, [a]⟩ := by
                  dsimp only [simpGate]
                  rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                    ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                have ha_ok : a < n + k ∧ ¬ dead a := by
                  by_contra hbad; apply hnd_k; intro y
                  rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
                  by_cases hlt : a < n + k
                  · have had : dead a := by by_contra hna; exact hbad ⟨hlt, hna⟩
                    simp [hlt, had y]
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
                  · have ha_f (y : Fin n → Bool) :
                        (if a < n + k then wireVal n C.gates y a else false) = false := by
                      rcases ha_bad with hge | had
                      · simp [not_lt.mpr hge]
                      · by_cases hlt : a < n + k
                        · simp [hlt, had y]
                        · simp [hlt]
                    have hb_ok : b < n + k ∧ ¬ dead b := by
                      by_contra hbad; apply hnd_k; intro y
                      rw [wireVal_gate n C.gates y k g hkC, hop, hgin, GateOp.eval]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                        Bool.or_false, ha_f y, Bool.false_or]
                      by_cases hlt : b < n + k
                      · have hbd : dead b := by by_contra hnb; exact hbad ⟨hlt, hnb⟩
                        simp [hlt, hbd y]
                      · simp [hlt]
                    have hsg : simpGate k g = ⟨GateOp.and, [b]⟩ := by
                      dsimp only [simpGate]
                      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                        ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                      dsimp only
                      rw [ite_eq_left_iff.mpr (fun h => False.elim (h ha_bad))]
                    rw [hsg, hop]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                      List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
                      ha_f x, Bool.false_or, ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                    exact ih b (by omega) hb_ok.2 x
                  · have ha_ok : a < n + k ∧ ¬ dead a := ⟨by omega, fun h => ha_bad (Or.inr h)⟩
                    by_cases hb_bad : b ≥ n + k ∨ dead b
                    · have hb_f (y : Fin n → Bool) :
                          (if b < n + k then wireVal n C.gates y b else false) = false := by
                        rcases hb_bad with hge | hbd
                        · simp [not_lt.mpr hge]
                        · by_cases hlt : b < n + k
                          · simp [hlt, hbd y]
                          · simp [hlt]
                      have hsg : simpGate k g = ⟨GateOp.and, [a]⟩ := by
                        dsimp only [simpGate]
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                        dsimp only
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (ha_bad h)),
                          ite_eq_left_iff.mpr (fun h => False.elim (h hb_bad))]
                      rw [hsg, hop]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
                        hb_f x, ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1))]
                      exact ih a (by omega) ha_ok.2 x
                    · have hb_ok : b < n + k ∧ ¬ dead b := ⟨by omega, fun h => hb_bad (Or.inr h)⟩
                      have hsg : simpGate k g = g := by
                        dsimp only [simpGate]
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (hnd_k h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hnot_and h)), hgin]
                        dsimp only
                        rw [ite_eq_right_iff.mpr (fun h => False.elim (ha_bad h)),
                          ite_eq_right_iff.mpr (fun h => False.elim (hb_bad h))]
                      rw [hsg, hop, hgin]
                      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        id, Bool.or_false,
                        ite_eq_left_iff.mpr (fun h => False.elim (h ha_ok.1)),
                        ite_eq_left_iff.mpr (fun h => False.elim (h hb_ok.1))]
                      rw [ih a (by omega) ha_ok.2 x, ih b (by omega) hb_ok.2 x]
                | cons _ _ => rw [hgin] at hglen; simp at hglen
        · exfalso; apply hnd; intro y; exact wireVal_of_ge n C.gates y w (by omega)
  have hout_nd : ¬ dead C.output := by
    intro hd
    rcases hout_true with ⟨x, hx⟩
    have := hd x
    change C.eval (List.ofFn x) = false at this
    rw [hx] at this; cases this
  exact ⟨C', hmono', hA', fun x => hwire C.output hout_nd x⟩

private lemma and_prefix_monomial (n : ℕ) (C : Circuit) (p : ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hand : ∀ k < p, ∀ g : Gate, C.gates[k]? = some g → g.op = GateOp.and) :
    ∀ w < n + p,
      (∀ x : Fin n → Bool, wireVal n C.gates x w = false) ∨
      ∃ M : Finset (Fin n), ∀ x : Fin n → Bool,
        wireVal n C.gates x w = true ↔ ∀ u ∈ M, x u = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · right
      refine ⟨{⟨w, hwn⟩}, fun x => ?_⟩
      rw [wireVal_input n C.gates x w hwn]
      simp
    · let k := w - n
      have hkp : k < p := by omega
      have hw_eq : w = n + k := by omega
      by_cases hklen : k < C.gates.length
      · let g := C.gates[k]
        have hkC : C.gates[k]? = some g := List.getElem?_eq_getElem hklen
        have hop : g.op = GateOp.and := hand k hkp g hkC
        have hlen := (hmono g (List.getElem_mem hklen)).2
        cases hgin : g.inputs with
        | nil =>
          right
          refine ⟨∅, fun x => ?_⟩
          rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
          simp
        | cons a tl =>
          cases tl with
          | nil =>
            by_cases ha : a < n + k
            · rcases ih a (by omega) (by omega) with haf | ⟨M, hM⟩
              · left; intro x
                rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
                simp [ha, haf x]
              · right; refine ⟨M, fun x => ?_⟩
                rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
                simp [ha, hM x]
            · left; intro x
              rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
              simp [ha]
          | cons b tl2 =>
            cases tl2 with
            | nil =>
              by_cases hab : a < n + k ∧ b < n + k
              · rcases ih a (by omega) (by omega) with haf | ⟨Ma, hMa⟩
                · left; intro x
                  rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
                  simp [hab.1, hab.2, haf x]
                · rcases ih b (by omega) (by omega) with hbf | ⟨Mb, hMb⟩
                  · left; intro x
                    rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
                    simp [hab.1, hab.2, hbf x]
                  · right; refine ⟨Ma ∪ Mb, fun x => ?_⟩
                    rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
                      Bool.and_true, ite_eq_left_iff.mpr (fun h => False.elim (h hab.1)),
                      ite_eq_left_iff.mpr (fun h => False.elim (h hab.2)),
                      Bool.and_eq_true, hMa x, hMb x, Finset.mem_union]
                    constructor
                    · rintro ⟨h1, h2⟩ u (hu | hu)
                      · exact h1 u hu
                      · exact h2 u hu
                    · intro h
                      exact ⟨fun u hu => h u (Or.inl hu), fun u hu => h u (Or.inr hu)⟩
              · left; intro x
                rw [hw_eq, wireVal_gate n C.gates x k g hkC, hop, hgin, GateOp.eval]
                by_cases ha : a < n + k
                · have hb : ¬ b < n + k := fun hb => hab ⟨ha, hb⟩
                  simp [ha, hb]
                · simp [ha]
            | cons _ _ => rw [hgin] at hlen; simp at hlen
      · left; intro x
        exact wireVal_of_ge n C.gates x w (by omega)

private def targetEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (3, 5), (4, 6), (0, 7)]

private def hasEdge (E : List (ℕ × ℕ)) (x : Fin 8 → Bool) : Prop :=
  ∃ u v : Fin 8, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true

private lemma hasEdge_no_wt1 (E : List (ℕ × ℕ)) (h : ∀ p ∈ E, p.1 ≠ p.2) (z : Fin 8) :
    ¬ hasEdge E (fun w => decide (w = z)) := by
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact h _ hab rfl

private lemma hasEdge_update_false_iff (E E' : List (ℕ × ℕ)) (v : Fin 8)
    (h1 : ∀ p ∈ E, p.1 ≠ v.val → p.2 ≠ v.val → p ∈ E')
    (h2 : ∀ p ∈ E', p ∈ E ∧ p.1 ≠ v.val ∧ p.2 ≠ v.val) (x : Fin 8 → Bool) :
    hasEdge E (Function.update x v false) ↔ hasEdge E' x := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hav : a ≠ v := fun h => by subst h; simp at ha
    have hbv : b ≠ v := fun h => by subst h; simp at hb
    simp [Function.update, hav] at ha
    simp [Function.update, hbv] at hb
    exact ⟨a, b, h1 _ hab (Fin.val_ne_of_ne hav) (Fin.val_ne_of_ne hbv), ha, hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hmem, hav, hbv⟩ := h2 _ hab
    have hav' : a ≠ v := fun h => hav (congrArg Fin.val h)
    have hbv' : b ≠ v := fun h => hbv (congrArg Fin.val h)
    exact ⟨a, b, hmem, by simp [Function.update, hav', ha], by simp [Function.update, hbv', hb]⟩

private lemma hasEdge_update_true_false_iff (E E' : List (ℕ × ℕ)) (v u : Fin 8)
    (hvu : v ≠ u)
    (h1 : ∀ p ∈ E, p.1 ≠ u.val → p.2 ≠ u.val → p.1 ≠ v.val ∧ p.2 ≠ v.val ∧ p ∈ E')
    (h2 : ∀ p ∈ E', p ∈ E ∧ p.1 ≠ u.val ∧ p.2 ≠ u.val ∧ p.1 ≠ v.val ∧ p.2 ≠ v.val)
    (x : Fin 8 → Bool) :
    hasEdge E (Function.update (Function.update x u false) v true) ↔ hasEdge E' x := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hau : a ≠ u := by
      intro h; subst h; simp [Function.update, hvu.symm] at ha
    have hbu : b ≠ u := by
      intro h; subst h; simp [Function.update, hvu.symm] at hb
    obtain ⟨hav, hbv, hmem⟩ := h1 _ hab (Fin.val_ne_of_ne hau) (Fin.val_ne_of_ne hbu)
    have hav' : a ≠ v := fun h => hav (congrArg Fin.val h)
    have hbv' : b ≠ v := fun h => hbv (congrArg Fin.val h)
    simp [Function.update, hav', hau] at ha
    simp [Function.update, hbv', hbu] at hb
    exact ⟨a, b, hmem, ha, hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hmem, hau, hbu, hav, hbv⟩ := h2 _ hab
    have hau' : a ≠ u := fun h => hau (congrArg Fin.val h)
    have hbu' : b ≠ u := fun h => hbu (congrArg Fin.val h)
    have hav' : a ≠ v := fun h => hav (congrArg Fin.val h)
    have hbv' : b ≠ v := fun h => hbv (congrArg Fin.val h)
    exact ⟨a, b, hmem, by simp [Function.update, hav', hau', ha],
      by simp [Function.update, hbv', hbu', hb]⟩

private lemma and_bound_4 (C : Circuit) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hspec : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔ hasEdge targetEdges x)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    4 ≤ A.card := by
  have step_true_false : ∀ (E E' : List (ℕ × ℕ)) (v u : Fin 8) (C0 : Circuit) (A0 : Finset ℕ),
      PEqualNP.MetaComplexity.Monotone2 C0 →
      (∀ x : Fin 8 → Bool, C0.eval (List.ofFn x) = true ↔ hasEdge E x) →
      (∀ (j : ℕ) (g : Gate), C0.gates[j]? = some g → g.op = GateOp.and → j ∈ A0) →
      (∃ x : Fin 8 → Bool, x v = false ∧ ¬ hasEdge E x ∧ hasEdge E (Function.update x v true)) →
      (∃ x : Fin 8 → Bool, x v = true ∧ ¬ hasEdge E x) →
      (∀ x : Fin 8 → Bool, hasEdge E (Function.update (Function.update x u false) v true) ↔ hasEdge E' x) →
      ∃ (C1 : Circuit) (j : ℕ), j ∈ A0 ∧
        PEqualNP.MetaComplexity.Monotone2 C1 ∧
        (∀ (k : ℕ) (g : Gate), C1.gates[k]? = some g → g.op = GateOp.and → k ∈ A0.erase j) ∧
        (∀ x : Fin 8 → Bool, C1.eval (List.ofFn x) = true ↔ hasEdge E' x) := by
    intro E E' v u C0 A0 hm0 hs0 hA0 hdep0 hna0 heq
    have hdep : ∃ x : Fin 8 → Bool, x v = false ∧ C0.eval (List.ofFn x) = false ∧
        C0.eval (List.ofFn (Function.update x v true)) = true := by
      rcases hdep0 with ⟨x, hxv, h0, h1⟩
      refine ⟨x, hxv, ?_, (hs0 _).mpr h1⟩
      cases hv : C0.eval (List.ofFn x)
      · rfl
      · exact False.elim (h0 ((hs0 _).mp hv))
    have hna : ∃ x : Fin 8 → Bool, x v = true ∧ C0.eval (List.ofFn x) = false := by
      rcases hna0 with ⟨x, hxv, h0⟩
      refine ⟨x, hxv, ?_⟩
      cases hv : C0.eval (List.ofFn x)
      · rfl
      · exact False.elim (h0 ((hs0 _).mp hv))
    obtain ⟨Ct, j, hjA, hmt, hAt, hevt⟩ := restrict_true_and_elim 8 C0 v A0 hm0 hA0 hdep hna
    obtain ⟨C1, hm1, hA1, hev1⟩ := restrict_false_no_new_and 8 Ct u (A0.erase j) hmt hAt
    refine ⟨C1, j, hjA, hm1, hA1, fun x => ?_⟩
    rw [hev1 x, hevt (Function.update x u false), hs0, heq x]
  let E1 : List (ℕ × ℕ) := [(1, 2), (2, 3), (3, 4), (3, 5), (4, 6)]
  let E2 : List (ℕ × ℕ) := [(1, 2), (4, 6)]
  let E3 : List (ℕ × ℕ) := [(1, 2)]
  obtain ⟨C1, j1, hj1, hm1, hA1, hs1⟩ := step_true_false targetEdges E1 7 0 C A hmono hspec hA
    ⟨fun w => decide (w = 0), by decide, hasEdge_no_wt1 targetEdges (by decide) 0,
      ⟨0, 7, by simp [targetEdges], by decide, by decide⟩⟩
    ⟨fun w => decide (w = 7), by decide, hasEdge_no_wt1 targetEdges (by decide) 7⟩
    (hasEdge_update_true_false_iff targetEdges E1 7 0 (by decide) (by decide) (by decide))
  obtain ⟨C2, j2, hj2, hm2, hA2, hs2⟩ := step_true_false E1 E2 5 3 C1 (A.erase j1) hm1 hs1 hA1
    ⟨fun w => decide (w = 3), by decide, hasEdge_no_wt1 E1 (by decide) 3,
      ⟨3, 5, by simp [E1], by decide, by decide⟩⟩
    ⟨fun w => decide (w = 5), by decide, hasEdge_no_wt1 E1 (by decide) 5⟩
    (hasEdge_update_true_false_iff E1 E2 5 3 (by decide) (by decide) (by decide))
  obtain ⟨C3, j3, hj3, hm3, hA3, hs3⟩ := step_true_false E2 E3 6 4 C2 ((A.erase j1).erase j2) hm2 hs2 hA2
    ⟨fun w => decide (w = 4), by decide, hasEdge_no_wt1 E2 (by decide) 4,
      ⟨4, 6, by simp [E2], by decide, by decide⟩⟩
    ⟨fun w => decide (w = 6), by decide, hasEdge_no_wt1 E2 (by decide) 6⟩
    (hasEdge_update_true_false_iff E2 E3 6 4 (by decide) (by decide) (by decide))
  have hdep3 : ∃ x : Fin 8 → Bool, x 1 = false ∧ C3.eval (List.ofFn x) = false ∧
      C3.eval (List.ofFn (Function.update x 1 true)) = true := by
    refine ⟨fun w => decide (w = 2), by decide, ?_, (hs3 _).mpr ⟨1, 2, by simp [E3], by decide, by decide⟩⟩
    cases hv : C3.eval (List.ofFn (fun w : Fin 8 => decide (w = 2)))
    · rfl
    · exact False.elim (hasEdge_no_wt1 E3 (by decide) 2 ((hs3 _).mp hv))
  have hna3 : ∃ x : Fin 8 → Bool, x 1 = true ∧ C3.eval (List.ofFn x) = false := by
    refine ⟨fun w => decide (w = 1), by decide, ?_⟩
    cases hv : C3.eval (List.ofFn (fun w : Fin 8 => decide (w = 1)))
    · rfl
    · exact False.elim (hasEdge_no_wt1 E3 (by decide) 1 ((hs3 _).mp hv))
  obtain ⟨j4, g4, _, hj4g, hg4op, _, _, _⟩ := exists_and_reading_live 8 C3 1 hm3 hdep3 hna3
  have hj4 : j4 ∈ (((A.erase j1).erase j2).erase j3) := hA3 j4 g4 hj4g hg4op
  have hc4 : 1 ≤ (((A.erase j1).erase j2).erase j3).card := Finset.card_pos.mpr ⟨j4, hj4⟩
  have hc3 := Finset.card_erase_add_one hj3
  have hc2 := Finset.card_erase_add_one hj2
  have hc1 := Finset.card_erase_add_one hj1
  omega

private def c5Edges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]

private lemma p4_or_bound (v : Fin 8) (hv : v.val < 5) (C : Circuit) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hspec : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔
      hasEdge c5Edges (Function.update x v false))
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) :
    2 ≤ A.card := by
  have hpath : ∃ a b c d : Fin 8,
      a ≠ v ∧ b ≠ v ∧ c ≠ v ∧ d ≠ v ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ((a.val, b.val) ∈ c5Edges ∨ (b.val, a.val) ∈ c5Edges) ∧
      ((b.val, c.val) ∈ c5Edges ∨ (c.val, b.val) ∈ c5Edges) ∧
      ((c.val, d.val) ∈ c5Edges ∨ (d.val, c.val) ∈ c5Edges) := by
    fin_cases v
    · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 4, 0, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨3, 4, 0, 1, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨4, 0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · simp at hv
    · simp at hv
    · simp at hv
  rcases hpath with ⟨a, b, c, d, hav, hbv, hcv, hdv, hab, hac, had, hbc, hbd, hcd, eab, ebc, ecd⟩
  have hasEdge_symm : ∀ (x : Fin 8 → Bool) (p q : Fin 8),
      ((p.val, q.val) ∈ c5Edges ∨ (q.val, p.val) ∈ c5Edges) →
      x p = true → x q = true → hasEdge c5Edges x := by
    intro x p q hpq hp hq
    rcases hpq with h | h
    · exact ⟨p, q, h, hp, hq⟩
    · exact ⟨q, p, h, hq, hp⟩
  have hno_wt1 : ∀ (z : Fin 8), ¬ hasEdge c5Edges (fun w => decide (w = z)) :=
    hasEdge_no_wt1 c5Edges (by decide)
  have hdep_a : ∃ x : Fin 8 → Bool, x a = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x a true)) = true := by
    refine ⟨fun w => decide (w = b), by simp [hab], ?_, ?_⟩
    · cases hval : C.eval (List.ofFn (fun w => decide (w = b)))
      · rfl
      · exfalso
        rcases (hspec _).mp hval with ⟨p, q, hpq, hp, hq⟩
        have h1 : p = b := by
          by_cases hpv : p = v
          · subst hpv; simp at hp
          · simp [Function.update, hpv] at hp; exact hp
        have h2 : q = b := by
          by_cases hqv : q = v
          · subst hqv; simp at hq
          · simp [Function.update, hqv] at hq; exact hq
        exact hno_wt1 b ⟨p, q, hpq, by simp [h1], by simp [h2]⟩
    · apply (hspec _).mpr
      apply hasEdge_symm _ a b eab
      · simp [Function.update, hav]
      · simp [Function.update, hbv, hab.symm]
  have hnb_a : ∃ x : Fin 8 → Bool, x a = false ∧ C.eval (List.ofFn x) = true := by
    refine ⟨fun w => decide (w = c ∨ w = d), by simp [hac, had], (hspec _).mpr ?_⟩
    apply hasEdge_symm _ c d ecd
    · simp [Function.update, hcv]
    · simp [Function.update, hdv]
  obtain ⟨j1, g1, i1, hj1g, hg1op, hi1m, hi1lt, hi1d⟩ :=
    exists_or_reading_dead 8 C a hmono hdep_a hnb_a
  have hj1A : j1 ∈ A := hA j1 g1 hj1g hg1op
  obtain ⟨C1, hm1, hA1_raw, hev1⟩ := restrict_false_or_elim 8 C a A hmono hA hnb_a
  have hA1 : ∀ (k : ℕ) (g : Gate), C1.gates[k]? = some g → g.op = GateOp.or → k ∈ A.erase j1 := by
    intro k g hk hop
    obtain ⟨hkA, hnod⟩ := hA1_raw k g hk hop
    apply Finset.mem_erase.mpr
    refine ⟨?_, hkA⟩
    intro hkj; subst hkj
    exact hnod g1 hj1g i1 hi1m hi1lt hi1d
  have hdep_b : ∃ x : Fin 8 → Bool, x b = false ∧ C1.eval (List.ofFn x) = false ∧
      C1.eval (List.ofFn (Function.update x b true)) = true := by
    refine ⟨fun w => decide (w = c), by simp [hbc], ?_, ?_⟩
    · rw [hev1]
      cases hval : C.eval (List.ofFn (Function.update (fun w => decide (w = c)) a false))
      · rfl
      · exfalso
        rcases (hspec _).mp hval with ⟨p, q, hpq, hp, hq⟩
        have h1 : p = c := by
          by_cases hpv : p = v
          · subst hpv; simp at hp
          · simp [Function.update, hpv] at hp
            by_cases hpa : p = a
            · subst hpa; simp at hp
            · simp [hpa] at hp; exact hp
        have h2 : q = c := by
          by_cases hqv : q = v
          · subst hqv; simp at hq
          · simp [Function.update, hqv] at hq
            by_cases hqa : q = a
            · subst hqa; simp at hq
            · simp [hqa] at hq; exact hq
        exact hno_wt1 c ⟨p, q, hpq, by simp [h1], by simp [h2]⟩
    · rw [hev1, hspec]
      apply hasEdge_symm _ b c ebc
      · simp [Function.update, hbv, hab.symm]
      · simp [Function.update, hcv, hac.symm, hbc.symm]
  have hnb_b : ∃ x : Fin 8 → Bool, x b = false ∧ C1.eval (List.ofFn x) = true := by
    refine ⟨fun w => decide (w = c ∨ w = d), by simp [hbc, hbd], ?_⟩
    rw [hev1, hspec]
    apply hasEdge_symm _ c d ecd
    · simp [Function.update, hcv, hac.symm]
    · simp [Function.update, hdv, had.symm]
  obtain ⟨j2, g2, _, hj2g, hg2op, _, _, _⟩ := exists_or_reading_dead 8 C1 b hm1 hdep_b hnb_b
  have hj2 : j2 ∈ A.erase j1 := hA1 j2 g2 hj2g hg2op
  have hc2 : 1 ≤ (A.erase j1).card := Finset.card_pos.mpr ⟨j2, hj2⟩
  have hc1 := Finset.card_erase_add_one hj1A
  omega

private lemma factor_at_p (C : Circuit) (p : ℕ) (X Y : Finset (Fin 8))
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hp_val : ∀ x : Fin 8 → Bool,
      wireVal 8 C.gates x (8 + p) = true ↔
        (∀ u ∈ X, x u = true) ∨ (∀ u ∈ Y, x u = true))
    (honly : ∀ v ∈ X ∪ Y, ∀ (j : ℕ) (g : Gate) (i : ℕ),
      C.gates[j]? = some g → g.op = GateOp.or → i ∈ g.inputs → i < 8 + j →
      IsDead 8 C.gates v i → j = p)
    (hfree : ∀ v ∈ X ∪ Y, ∃ z : Fin 8 → Bool, z v = false ∧ C.eval (List.ofFn z) = true) :
    ∀ x y : Fin 8 → Bool,
      (∀ u : Fin 8, u ∉ X ∪ Y → x u = y u) →
      (((∀ u ∈ X, x u = true) ∨ (∀ u ∈ Y, x u = true)) ↔
        ((∀ u ∈ X, y u = true) ∨ (∀ u ∈ Y, y u = true))) →
      C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  intro x y hagree hbit
  have hinv : ∀ w : ℕ, (∃ v ∈ X ∪ Y, IsDead 8 C.gates v w) ∨
      wireVal 8 C.gates x w = wireVal 8 C.gates y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hwn : w < 8
      · by_cases hmem : (⟨w, hwn⟩ : Fin 8) ∈ X ∪ Y
        · left
          refine ⟨⟨w, hwn⟩, hmem, fun z hz => ?_⟩
          rw [wireVal_input 8 C.gates z w hwn]
          exact hz
        · right
          rw [wireVal_input 8 C.gates x w hwn, wireVal_input 8 C.gates y w hwn]
          exact hagree ⟨w, hwn⟩ hmem
      · by_cases hwlen : w < 8 + C.gates.length
        · let k := w - 8
          have hk_lt : k < C.gates.length := by omega
          have hw_eq : w = 8 + k := by omega
          by_cases hkp : k = p
          · subst hkp
            right
            rw [hw_eq]
            cases hx : wireVal 8 C.gates x (8 + k) <;> cases hy : wireVal 8 C.gates y (8 + k)
            · rfl
            · exfalso
              have h1 := (hp_val y).mp hy
              have h2 := (hp_val x).mpr (hbit.mpr h1)
              rw [hx] at h2; cases h2
            · exfalso
              have h1 := (hp_val x).mp hx
              have h2 := (hp_val y).mpr (hbit.mp h1)
              rw [hy] at h2; cases h2
            · rfl
          · let g := C.gates[k]
            have hkC : C.gates[k]? = some g := List.getElem?_eq_getElem hk_lt
            rcases (hmono g (List.getElem_mem hk_lt)).1 with hop | hop
            · by_cases hex : ∃ i ∈ g.inputs, i < 8 + k ∧ ∃ v ∈ X ∪ Y, IsDead 8 C.gates v i
              · left
                rcases hex with ⟨i, hi, hilt, v, hv, hdv⟩
                refine ⟨v, hv, fun z hz => ?_⟩
                rw [hw_eq, wireVal_gate 8 C.gates z k g hkC, hop, GateOp.eval]
                have hf : (if i < 8 + k then wireVal 8 C.gates z i else false) = false := by
                  simp [hilt, hdv z hz]
                cases hval : (g.inputs.map fun i => if i < 8 + k then wireVal 8 C.gates z i else false).all id
                · rfl
                · exfalso; rw [List.all_eq_true] at hval
                  have := hval _ (List.mem_map_of_mem hi); simp [hf] at this
              · right
                rw [hw_eq, wireVal_gate 8 C.gates x k g hkC, wireVal_gate 8 C.gates y k g hkC]
                congr 1; apply List.map_congr_left; intro i hi
                by_cases hilt : i < 8 + k
                · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hilt)),
                    ite_eq_left_iff.mpr (fun h => False.elim (h hilt))]
                  exact (ih i (by omega)).resolve_left (fun h => hex ⟨i, hi, hilt, h⟩)
                · simp [hilt]
            · right
              rw [hw_eq, wireVal_gate 8 C.gates x k g hkC, wireVal_gate 8 C.gates y k g hkC]
              congr 1; apply List.map_congr_left; intro i hi
              by_cases hilt : i < 8 + k
              · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hilt)),
                  ite_eq_left_iff.mpr (fun h => False.elim (h hilt))]
                have hnd : ¬ ∃ v ∈ X ∪ Y, IsDead 8 C.gates v i := by
                  rintro ⟨v, hv, hdv⟩
                  exact hkp (honly v hv k g i hkC hop hi hilt hdv)
                exact (ih i (by omega)).resolve_left hnd
              · simp [hilt]
        · right
          rw [wireVal_of_ge 8 C.gates x w (by omega), wireVal_of_ge 8 C.gates y w (by omega)]
  rcases hinv C.output with ⟨v, hv, hdv⟩ | heq
  · exfalso
    rcases hfree v hv with ⟨z, hzv, hz1⟩
    have := hdv z hzv
    change C.eval (List.ofFn z) = false at this
    rw [hz1] at this; cases this
  · exact heq

private lemma c5_no_factor (X Y : Finset (Fin 8))
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXY : ¬ X ⊆ Y) (hYX : ¬ Y ⊆ X)
    (hS5 : ∀ u ∈ X ∪ Y, u.val < 5)
    (hfac : ∀ x y : Fin 8 → Bool,
      (∀ u : Fin 8, u ∉ X ∪ Y → x u = y u) →
      (((∀ u ∈ X, x u = true) ∨ (∀ u ∈ Y, x u = true)) ↔
        ((∀ u ∈ X, y u = true) ∨ (∀ u ∈ Y, y u = true))) →
      (hasEdge c5Edges x ↔ hasEdge c5Edges y)) :
    False := by
  have hhas_symm : ∀ (x : Fin 8 → Bool) (p q : Fin 8),
      ((p.val, q.val) ∈ c5Edges ∨ (q.val, p.val) ∈ c5Edges) →
      x p = true → x q = true → hasEdge c5Edges x := by
    intro x p q hpq hp hq
    rcases hpq with h | h
    · exact ⟨p, q, h, hp, hq⟩
    · exact ⟨q, p, h, hq, hp⟩
  have hno_wt1 : ∀ (z : Fin 8), ¬ hasEdge c5Edges (fun w => decide (w = z)) :=
    hasEdge_no_wt1 c5Edges (by decide)
  have hnb2 : ∀ u : Fin 8, u.val < 5 →
      ∃ a b : Fin 8, a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
        ((u.val, a.val) ∈ c5Edges ∨ (a.val, u.val) ∈ c5Edges) ∧
        ((u.val, b.val) ∈ c5Edges ∨ (b.val, u.val) ∈ c5Edges) := by
    intro u hu
    fin_cases u
    · exact ⟨1, 4, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨1, 3, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 4, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨3, 0, by decide, by decide, by decide, by decide, by decide⟩
    · simp at hu
    · simp at hu
    · simp at hu
  obtain ⟨u, huX, huY⟩ := Finset.not_subset.mp hXY
  obtain ⟨v, hvY, hvX⟩ := Finset.not_subset.mp hYX
  have huv : u ≠ v := fun h => hvX (h ▸ huX)
  have hu5 : u.val < 5 := hS5 u (Finset.mem_union_left _ huX)
  have hv5 : v.val < 5 := hS5 v (Finset.mem_union_right _ hvY)
  have kill_ge2 : ∀ (X1 Y1 : Finset (Fin 8)) (u1 : Fin 8),
      u1 ∈ X1 → u1 ∉ Y1 → Y1.Nonempty → 2 ≤ X1.card → u1.val < 5 →
      (∀ x y : Fin 8 → Bool,
        (∀ z : Fin 8, z ∉ X1 ∪ Y1 → x z = y z) →
        (((∀ z ∈ X1, x z = true) ∨ (∀ z ∈ Y1, x z = true)) ↔
          ((∀ z ∈ X1, y z = true) ∨ (∀ z ∈ Y1, y z = true))) →
        (hasEdge c5Edges x ↔ hasEdge c5Edges y)) → False := by
    intro X1 Y1 u1 hu1X hu1Y hY1ne hX1card hu15 hf1
    obtain ⟨a, b, hab, hau, hbu, eua, eub⟩ := hnb2 u1 hu15
    by_cases hYa : Y1 = {a}
    · let x : Fin 8 → Bool := fun w => decide (w = a)
      let y : Fin 8 → Bool := fun w => decide (w = a ∨ w = u1)
      have heq := hf1 x y
        (fun z hz => by
          have hzu : z ≠ u1 := fun h => hz (h ▸ Finset.mem_union_left _ hu1X)
          simp [x, y, hzu])
        (by
          have h1 : ∀ z ∈ Y1, x z = true := by intro z hz; rw [hYa, Finset.mem_singleton] at hz; simp [x, hz]
          have h2 : ∀ z ∈ Y1, y z = true := by intro z hz; rw [hYa, Finset.mem_singleton] at hz; simp [y, hz]
          exact ⟨fun _ => Or.inr h2, fun _ => Or.inr h1⟩)
      exact hno_wt1 a (heq.mpr (hhas_symm y u1 a eua (by simp [y]) (by simp [y])))
    · by_cases hYb : Y1 = {b}
      · let x : Fin 8 → Bool := fun w => decide (w = b)
        let y : Fin 8 → Bool := fun w => decide (w = b ∨ w = u1)
        have heq := hf1 x y
          (fun z hz => by
            have hzu : z ≠ u1 := fun h => hz (h ▸ Finset.mem_union_left _ hu1X)
            simp [x, y, hzu])
          (by
            have h1 : ∀ z ∈ Y1, x z = true := by intro z hz; rw [hYb, Finset.mem_singleton] at hz; simp [x, hz]
            have h2 : ∀ z ∈ Y1, y z = true := by intro z hz; rw [hYb, Finset.mem_singleton] at hz; simp [y, hz]
            exact ⟨fun _ => Or.inr h2, fun _ => Or.inr h1⟩)
        exact hno_wt1 b (heq.mpr (hhas_symm y u1 b eub (by simp [y]) (by simp [y])))
      · have hex_c : ∃ c : Fin 8, c ≠ u1 ∧ Y1 ≠ {c} ∧ X1 ≠ {u1, c} ∧
            ((u1.val, c.val) ∈ c5Edges ∨ (c.val, u1.val) ∈ c5Edges) := by
          by_cases hXa : X1 = {u1, a}
          · refine ⟨b, hbu, hYb, ?_, eub⟩
            intro hXb
            have ha_mem : a ∈ ({u1, b} : Finset (Fin 8)) := by rw [← hXb, hXa]; simp
            simp [hau, hab] at ha_mem
          · exact ⟨a, hau, hYa, hXa, eua⟩
        rcases hex_c with ⟨c, hcu, hYc, hXc, euc⟩
        let x : Fin 8 → Bool := fun w => decide (w = c)
        let y : Fin 8 → Bool := fun w => decide (w = c ∨ w = u1)
        have hX1x : ¬ ∀ z ∈ X1, x z = true := by
          intro h
          have hsub : X1 ⊆ {c} := fun z hz => Finset.mem_singleton.mpr (by simpa [x] using h z hz)
          have := Finset.card_le_card hsub; simp at this; omega
        have hX1y : ¬ ∀ z ∈ X1, y z = true := by
          intro h
          have hsub : X1 ⊆ {u1, c} := fun z hz => by
            have hz' := h z hz; simp [y] at hz'
            rcases hz' with rfl | rfl <;> simp
          have hcard2 : ({u1, c} : Finset (Fin 8)).card = 2 := Finset.card_pair hcu.symm
          exact hXc (Finset.eq_of_subset_of_card_le hsub (by omega))
        have hY1x : ¬ ∀ z ∈ Y1, x z = true := by
          intro h
          have hsub : Y1 ⊆ {c} := fun z hz => Finset.mem_singleton.mpr (by simpa [x] using h z hz)
          obtain ⟨w, hw⟩ := hY1ne
          have hwc : w = c := Finset.mem_singleton.mp (hsub hw)
          exact hYc (Finset.Subset.antisymm hsub (by intro z hz; rw [Finset.mem_singleton.mp hz, ← hwc]; exact hw))
        have hY1y : ¬ ∀ z ∈ Y1, y z = true := by
          intro h
          apply hY1x; intro z hz
          have hz' := h z hz; simp [y] at hz'
          rcases hz' with rfl | rfl
          · simp [x]
          · exact False.elim (hu1Y hz)
        have heq := hf1 x y
          (fun z hz => by
            have hzu : z ≠ u1 := fun h => hz (h ▸ Finset.mem_union_left _ hu1X)
            simp [x, y, hzu])
          (by simp [hX1x, hX1y, hY1x, hY1y])
        exact hno_wt1 c (heq.mpr (hhas_symm y u1 c euc (by simp [y]) (by simp [y])))
  by_cases hX2 : 2 ≤ X.card
  · exact kill_ge2 X Y u huX huY hYne hX2 hu5 hfac
  · by_cases hY2 : 2 ≤ Y.card
    · exact kill_ge2 Y X v hvY hvX hXne hY2 hv5 (fun x y ha hb =>
        hfac x y (by simpa [Finset.union_comm] using ha) (by simpa [or_comm] using hb))
    · have hXeq : X = {u} := by
        have hsub : {u} ⊆ X := Finset.singleton_subset_iff.mpr huX
        exact (Finset.eq_of_subset_of_card_le hsub (by simp; omega)).symm
      have hYeq : Y = {v} := by
        have hsub : {v} ⊆ Y := Finset.singleton_subset_iff.mpr hvY
        exact (Finset.eq_of_subset_of_card_le hsub (by simp; omega)).symm
      by_cases hadj : (u.val, v.val) ∈ c5Edges ∨ (v.val, u.val) ∈ c5Edges
      · let x : Fin 8 → Bool := fun w => decide (w = u)
        let y : Fin 8 → Bool := fun w => decide (w = u ∨ w = v)
        have heq := hfac x y
          (fun z hz => by
            have hzv : z ≠ v := fun h => hz (h ▸ Finset.mem_union_right _ hvY)
            simp [x, y, hzv])
          (by simp [hXeq, hYeq, x, y])
        exact hno_wt1 u (heq.mpr (hhas_symm y u v hadj (by simp [y]) (by simp [y])))
      · have hdiff : ∀ u0 v0 : Fin 8, u0.val < 5 → v0.val < 5 → u0 ≠ v0 →
            ¬ ((u0.val, v0.val) ∈ c5Edges ∨ (v0.val, u0.val) ∈ c5Edges) →
            ∃ a : Fin 8, a ≠ u0 ∧ a ≠ v0 ∧
              ((u0.val, a.val) ∈ c5Edges ∨ (a.val, u0.val) ∈ c5Edges) ∧
              ¬ ((v0.val, a.val) ∈ c5Edges ∨ (a.val, v0.val) ∈ c5Edges) := by
          intro u0 v0 hu0 hv0 huv0 hna0
          let a : Fin 8 :=
            if (u0.val + 2) % 5 = v0.val then ⟨(u0.val + 4) % 5, by omega⟩
            else ⟨(u0.val + 1) % 5, by omega⟩
          refine ⟨a, ?_⟩
          revert hu0 hv0 huv0 hna0
          fin_cases u0 <;> fin_cases v0 <;> simp [a, c5Edges]
        obtain ⟨a, hau, hav, eua, neva⟩ := hdiff u v hu5 hv5 huv hadj
        let x : Fin 8 → Bool := fun w => decide (w = a ∨ w = u)
        let y : Fin 8 → Bool := fun w => decide (w = a ∨ w = v)
        have heq := hfac x y
          (fun z hz => by
            have hzu : z ≠ u := fun h => hz (h ▸ Finset.mem_union_left _ huX)
            have hzv : z ≠ v := fun h => hz (h ▸ Finset.mem_union_right _ hvY)
            simp [x, y, hzu, hzv])
          (by simp [hXeq, hYeq, x, y])
        have hx1 : hasEdge c5Edges x := hhas_symm x u a eua (by simp [x]) (by simp [x])
        have hy1 : hasEdge c5Edges y := heq.mp hx1
        rcases hy1 with ⟨p, q, hpq, hp, hq⟩
        simp only [y, decide_eq_true_eq] at hp hq
        rcases hp with hpa | hpv <;> rcases hq with hqa | hqv
        · rw [hpa, hqa] at hpq
          exact hno_wt1 a ⟨a, a, hpq, by simp, by simp⟩
        · rw [hpa, hqv] at hpq
          exact neva (Or.inr hpq)
        · rw [hpv, hqa] at hpq
          exact neva (Or.inl hpq)
        · rw [hpv, hqv] at hpq
          exact hno_wt1 v ⟨v, v, hpq, by simp, by simp⟩

private lemma c5_or_bound_ind :
    ∀ k : ℕ, k ≤ 3 →
      ¬ ∃ (C : Circuit) (A : Finset ℕ),
        A.card = k ∧
        PEqualNP.MetaComplexity.Monotone2 C ∧
        (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔ hasEdge c5Edges x) ∧
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk3
    rintro ⟨C, A, hAk, hmono, hspec, hA⟩
    have hfree_v : ∀ v : Fin 8, ∃ z : Fin 8 → Bool, z v = false ∧ C.eval (List.ofFn z) = true := by
      intro v
      have hex : ∃ a b : Fin 8, a ≠ v ∧ b ≠ v ∧ (a.val, b.val) ∈ c5Edges := by
        fin_cases v
        · exact ⟨1, 2, by decide, by decide, by decide⟩
        · exact ⟨2, 3, by decide, by decide, by decide⟩
        · exact ⟨3, 4, by decide, by decide, by decide⟩
        · exact ⟨0, 4, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
      rcases hex with ⟨a, b, hav, hbv, hab⟩
      refine ⟨fun w => decide (w = a ∨ w = b), by simp [hav.symm, hbv.symm], (hspec _).mpr ?_⟩
      exact ⟨a, b, hab, by simp, by simp⟩
    have hdep0 : ∃ x : Fin 8 → Bool, x 0 = false ∧ C.eval (List.ofFn x) = false ∧
        C.eval (List.ofFn (Function.update x 0 true)) = true := by
      refine ⟨fun w => decide (w = 1), by decide, ?_, (hspec _).mpr ⟨0, 1, by simp [c5Edges], by decide, by decide⟩⟩
      cases hval : C.eval (List.ofFn (fun w : Fin 8 => decide (w = 1)))
      · rfl
      · exact False.elim (hasEdge_no_wt1 c5Edges (by decide) 1 ((hspec _).mp hval))
    obtain ⟨j_ex, g_ex, _, hj_ex, hop_ex, _, _, _⟩ :=
      exists_or_reading_dead 8 C 0 hmono hdep0 (hfree_v 0)
    have hex_or : ∃ p : ℕ, ∃ g : Gate, C.gates[p]? = some g ∧ g.op = GateOp.or :=
      ⟨j_ex, g_ex, hj_ex, hop_ex⟩
    classical
    let p := Nat.find hex_or
    obtain ⟨g, hgp, hgop⟩ := Nat.find_spec hex_or
    have hp_lt : p < C.gates.length := by
      by_contra h; rw [List.getElem?_eq_none (not_lt.mp h)] at hgp; simp at hgp
    have hpA : p ∈ A := hA p g hgp hgop
    have hhand : ∀ j < p, ∀ g' : Gate, C.gates[j]? = some g' → g'.op = GateOp.and := by
      intro j hjp g' hjg'
      have hjlt : j < C.gates.length := by
        by_contra h; rw [List.getElem?_eq_none (not_lt.mp h)] at hjg'; simp at hjg'
      have hgm := hmono g' (by
        rw [List.getElem?_eq_getElem hjlt] at hjg'
        rw [← Option.some.inj hjg']; exact List.getElem_mem hjlt)
      rcases hgm.1 with h | h
      · exact h
      · exact False.elim (Nat.find_min hex_or hjp ⟨g', hjg', h⟩)
    have hless : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' →
        (∀ x : Fin 8 → Bool, C'.eval (List.ofFn x) = true ↔ hasEdge c5Edges x) →
        (∀ (j : ℕ) (g' : Gate), C'.gates[j]? = some g' → g'.op = GateOp.or → j ∈ A.erase p) →
        False := by
      intro C' hm' hs' hA'
      have hcard : (A.erase p).card < k := by
        have := Finset.card_erase_add_one hpA; omega
      exact ih (A.erase p).card hcard (by omega) ⟨C', A.erase p, rfl, hm', hs', hA'⟩
    have hnot_copy : ∀ (a : ℕ), a < 8 + p →
        (∀ x : Fin 8 → Bool, wireVal 8 C.gates x (8 + p) = wireVal 8 C.gates x a) → False := by
      intro a ha heq
      have hrep := replace_gate_same_val 8 C p ⟨GateOp.and, [a]⟩ hp_lt (by simp) hmono (fun x => by
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true, ite_eq_left_iff.mpr (fun h => False.elim (h ha))]
        exact (heq x).symm)
      apply hless ⟨C.gates.set p ⟨GateOp.and, [a]⟩, C.output⟩ hrep.1
      · intro x; rw [hrep.2.1 x, hspec x]
      · intro j g' hjg' hop'
        rcases hrep.2.2 j g' hjg' hop' with ⟨_, hbad⟩ | ⟨hne, hC⟩
        · cases hbad
        · exact Finset.mem_erase.mpr ⟨hne, hA j g' hC hop'⟩
    have hnot_true : (∀ x : Fin 8 → Bool, wireVal 8 C.gates x (8 + p) = true) → False := by
      intro heq
      have hrep := replace_gate_same_val 8 C p ⟨GateOp.and, []⟩ hp_lt (by simp) hmono (fun x => by
        simp [GateOp.eval, heq x])
      apply hless ⟨C.gates.set p ⟨GateOp.and, []⟩, C.output⟩ hrep.1
      · intro x; rw [hrep.2.1 x, hspec x]
      · intro j g' hjg' hop'
        rcases hrep.2.2 j g' hjg' hop' with ⟨_, hbad⟩ | ⟨hne, hC⟩
        · cases hbad
        · exact Finset.mem_erase.mpr ⟨hne, hA j g' hC hop'⟩
    have hnot_false : (∀ x : Fin 8 → Bool, wireVal 8 C.gates x (8 + p) = false) → False := by
      intro heq
      obtain ⟨z, _, hz1⟩ := hfree_v 0
      obtain ⟨C', hm', hA', hev'⟩ := elim_const_false_or 8 C p A hmono hA heq ⟨z, hz1⟩
      exact hless C' hm' (fun x => by rw [hev' x, hspec x]) hA'
    have hglen := (hmono g (by
      rw [List.getElem?_eq_getElem hp_lt] at hgp
      rw [← Option.some.inj hgp]; exact List.getElem_mem hp_lt)).2
    cases hgin : g.inputs with
    | nil =>
      apply hnot_false; intro x
      rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]; rfl
    | cons a tl =>
      cases tl with
      | nil =>
        by_cases ha : a < 8 + p
        · apply hnot_copy a ha; intro x
          rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
          simp [ha]
        · apply hnot_false; intro x
          rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
          simp [ha]
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          by_cases ha : a < 8 + p
          · by_cases hb : b < 8 + p
            · rcases and_prefix_monomial 8 C p hmono hhand a ha with haf | ⟨X, hX⟩
              · apply hnot_copy b hb; intro x
                rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
                simp [ha, hb, haf x]
              · rcases and_prefix_monomial 8 C p hmono hhand b hb with hbf | ⟨Y, hY⟩
                · apply hnot_copy a ha; intro x
                  rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
                  simp [ha, hb, hbf x]
                · have hp_val : ∀ x : Fin 8 → Bool,
                      wireVal 8 C.gates x (8 + p) = true ↔
                        (∀ u ∈ X, x u = true) ∨ (∀ u ∈ Y, x u = true) := by
                    intro x
                    rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                      Bool.or_false, ite_eq_left_iff.mpr (fun h => False.elim (h ha)),
                      ite_eq_left_iff.mpr (fun h => False.elim (h hb)), Bool.or_eq_true, hX x, hY x]
                  have hXne : X.Nonempty := by
                    by_contra hne
                    rw [Finset.not_nonempty_iff_eq_empty] at hne
                    apply hnot_true; intro x
                    exact (hp_val x).mpr (Or.inl (by simp [hne]))
                  have hYne : Y.Nonempty := by
                    by_contra hne
                    rw [Finset.not_nonempty_iff_eq_empty] at hne
                    apply hnot_true; intro x
                    exact (hp_val x).mpr (Or.inr (by simp [hne]))
                  have hXY : ¬ X ⊆ Y := by
                    intro hsub
                    apply hnot_copy a ha; intro x
                    cases h1 : wireVal 8 C.gates x (8 + p) <;> cases h2 : wireVal 8 C.gates x a
                    · rfl
                    · exfalso
                      have := (hp_val x).mpr (Or.inl ((hX x).mp h2))
                      rw [h1] at this; cases this
                    · exfalso
                      rcases (hp_val x).mp h1 with hxX | hxY
                      · have := (hX x).mpr hxX; rw [h2] at this; cases this
                      · have := (hX x).mpr (fun u hu => hxY u (hsub hu)); rw [h2] at this; cases this
                    · rfl
                  have hYX : ¬ Y ⊆ X := by
                    intro hsub
                    apply hnot_copy b hb; intro x
                    cases h1 : wireVal 8 C.gates x (8 + p) <;> cases h2 : wireVal 8 C.gates x b
                    · rfl
                    · exfalso
                      have := (hp_val x).mpr (Or.inr ((hY x).mp h2))
                      rw [h1] at this; cases this
                    · exfalso
                      rcases (hp_val x).mp h1 with hxX | hxY
                      · have := (hY x).mpr (fun u hu => hxX u (hsub hu)); rw [h2] at this; cases this
                      · have := (hY x).mpr hxY; rw [h2] at this; cases this
                    · rfl
                  have hp_dead : ∀ v ∈ X ∪ Y, ∃ i ∈ g.inputs, i < 8 + p ∧ IsDead 8 C.gates v i := by
                    intro v hv
                    rcases Finset.mem_union.mp hv with hvX | hvY
                    · refine ⟨a, by simp [hgin], ha, fun x hx => ?_⟩
                      cases hval : wireVal 8 C.gates x a
                      · rfl
                      · exfalso; have := (hX x).mp hval v hvX; rw [hx] at this; cases this
                    · refine ⟨b, by simp [hgin], hb, fun x hx => ?_⟩
                      cases hval : wireVal 8 C.gates x b
                      · rfl
                      · exfalso; have := (hY x).mp hval v hvY; rw [hx] at this; cases this
                  have hS5 : ∀ v ∈ X ∪ Y, v.val < 5 := by
                    intro v hv
                    by_contra hge5
                    obtain ⟨C', hm', hA'_raw, hev'⟩ :=
                      restrict_false_or_elim 8 C v A hmono hA (hfree_v v)
                    apply hless C' hm'
                    · intro x
                      rw [hev' x, hspec (Function.update x v false)]
                      have hc5_lt5 : ∀ p ∈ c5Edges, p.1 < 5 ∧ p.2 < 5 := by decide
                      exact hasEdge_update_false_iff c5Edges c5Edges v
                        (fun p hp _ _ => hp)
                        (fun p hp => ⟨hp, by have := hc5_lt5 p hp; omega, by have := hc5_lt5 p hp; omega⟩) x
                    · intro j g' hjg' hop'
                      obtain ⟨hjA, hnod⟩ := hA'_raw j g' hjg' hop'
                      apply Finset.mem_erase.mpr
                      refine ⟨?_, hjA⟩
                      intro hjp; subst hjp
                      rcases hp_dead v hv with ⟨i, hi, hilt, hdi⟩
                      exact hnod g hgp i hi hilt hdi
                  have honly : ∀ v ∈ X ∪ Y, ∀ (j : ℕ) (gj : Gate) (i : ℕ),
                      C.gates[j]? = some gj → gj.op = GateOp.or → i ∈ gj.inputs → i < 8 + j →
                      IsDead 8 C.gates v i → j = p := by
                    intro v hv j gj i hjg hjop him hilt hdi
                    by_contra hjp
                    have hjA : j ∈ A := hA j gj hjg hjop
                    obtain ⟨C', hm', hA'_raw, hev'⟩ :=
                      restrict_false_or_elim 8 C v A hmono hA (hfree_v v)
                    have hA' : ∀ (k' : ℕ) (gk : Gate), C'.gates[k']? = some gk →
                        gk.op = GateOp.or → k' ∈ (A.erase p).erase j := by
                      intro k' gk hkg hopk
                      obtain ⟨hkA, hnod⟩ := hA'_raw k' gk hkg hopk
                      apply Finset.mem_erase.mpr
                      refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hkA⟩⟩
                      · intro hkj; subst hkj; exact hnod gj hjg i him hilt hdi
                      · intro hkp; subst hkp
                        rcases hp_dead v hv with ⟨ip, hip, hiplt, hdip⟩
                        exact hnod g hgp ip hip hiplt hdip
                    have h2 := p4_or_bound v (hS5 v hv) C' ((A.erase p).erase j) hm'
                      (fun x => by rw [hev' x, hspec]) hA'
                    have hj_in : j ∈ A.erase p := Finset.mem_erase.mpr ⟨hjp, hjA⟩
                    have hc1 := Finset.card_erase_add_one hpA
                    have hc2 := Finset.card_erase_add_one hj_in
                    omega
                  have hfac := factor_at_p C p X Y hmono hp_val honly (fun v _ => hfree_v v)
                  exact c5_no_factor X Y hXne hYne hXY hYX hS5 (fun x y ha hb => by
                    rw [← hspec x, ← hspec y, hfac x y ha hb])
            · apply hnot_copy a ha; intro x
              rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
              simp [ha, hb]
          · by_cases hb : b < 8 + p
            · apply hnot_copy b hb; intro x
              rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
              simp [ha, hb]
            · apply hnot_false; intro x
              rw [wireVal_gate 8 C.gates x p g hgp, hgop, hgin, GateOp.eval]
              simp [ha, hb]
        | cons _ _ => rw [hgin] at hglen; simp at hglen

private lemma or_bound_7 (C : Circuit) (A : Finset ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hspec : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔ hasEdge targetEdges x)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) :
    7 ≤ A.card := by
  have peel : ∀ (E E' : List (ℕ × ℕ)) (v : Fin 8) (C0 : Circuit) (A0 : Finset ℕ),
      PEqualNP.MetaComplexity.Monotone2 C0 →
      (∀ x : Fin 8 → Bool, C0.eval (List.ofFn x) = true ↔ hasEdge E x) →
      (∀ (j : ℕ) (g : Gate), C0.gates[j]? = some g → g.op = GateOp.or → j ∈ A0) →
      (∃ x : Fin 8 → Bool, x v = false ∧ ¬ hasEdge E x ∧ hasEdge E (Function.update x v true)) →
      (∃ x : Fin 8 → Bool, x v = false ∧ hasEdge E x) →
      (∀ x : Fin 8 → Bool, hasEdge E (Function.update x v false) ↔ hasEdge E' x) →
      ∃ (C1 : Circuit) (j : ℕ), j ∈ A0 ∧
        PEqualNP.MetaComplexity.Monotone2 C1 ∧
        (∀ (k : ℕ) (g : Gate), C1.gates[k]? = some g → g.op = GateOp.or → k ∈ A0.erase j) ∧
        (∀ x : Fin 8 → Bool, C1.eval (List.ofFn x) = true ↔ hasEdge E' x) := by
    intro E E' v C0 A0 hm0 hs0 hA0 hdep0 hnb0 heq
    have hdep : ∃ x : Fin 8 → Bool, x v = false ∧ C0.eval (List.ofFn x) = false ∧
        C0.eval (List.ofFn (Function.update x v true)) = true := by
      rcases hdep0 with ⟨x, hxv, h0, h1⟩
      refine ⟨x, hxv, ?_, (hs0 _).mpr h1⟩
      cases hv : C0.eval (List.ofFn x)
      · rfl
      · exact False.elim (h0 ((hs0 _).mp hv))
    have hnb : ∃ x : Fin 8 → Bool, x v = false ∧ C0.eval (List.ofFn x) = true := by
      rcases hnb0 with ⟨x, hxv, h1⟩
      exact ⟨x, hxv, (hs0 _).mpr h1⟩
    obtain ⟨j0, g0, i0, hj0, hg0op, hi0m, hi0lt, hi0d⟩ :=
      exists_or_reading_dead 8 C0 v hm0 hdep hnb
    have hj0A : j0 ∈ A0 := hA0 j0 g0 hj0 hg0op
    obtain ⟨C1, hm1, hA1_raw, hev1⟩ := restrict_false_or_elim 8 C0 v A0 hm0 hA0 hnb
    refine ⟨C1, j0, hj0A, hm1, ?_, fun x => by rw [hev1 x, hs0, heq x]⟩
    intro k g hk hop
    obtain ⟨hkA, hnod⟩ := hA1_raw k g hk hop
    apply Finset.mem_erase.mpr
    refine ⟨?_, hkA⟩
    intro hkj; subst hkj
    exact hnod g0 hj0 i0 hi0m hi0lt hi0d
  let E1 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (3, 5), (4, 6)]
  let E2 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (4, 6)]
  obtain ⟨C1, j1, hj1, hm1, hA1, hs1⟩ := peel targetEdges E1 7 C A hmono hspec hA
    ⟨fun w => decide (w = 0), by decide, hasEdge_no_wt1 targetEdges (by decide) 0,
      ⟨0, 7, by simp [targetEdges], by decide, by decide⟩⟩
    ⟨fun w => decide (w = 1 ∨ w = 2), by decide, ⟨1, 2, by simp [targetEdges], by decide, by decide⟩⟩
    (hasEdge_update_false_iff targetEdges E1 7 (by decide) (by decide))
  obtain ⟨C2, j2, hj2, hm2, hA2, hs2⟩ := peel E1 E2 5 C1 (A.erase j1) hm1 hs1 hA1
    ⟨fun w => decide (w = 3), by decide, hasEdge_no_wt1 E1 (by decide) 3,
      ⟨3, 5, by simp [E1], by decide, by decide⟩⟩
    ⟨fun w => decide (w = 1 ∨ w = 2), by decide, ⟨1, 2, by simp [E1], by decide, by decide⟩⟩
    (hasEdge_update_false_iff E1 E2 5 (by decide) (by decide))
  obtain ⟨C3, j3, hj3, hm3, hA3, hs3⟩ := peel E2 c5Edges 6 C2 ((A.erase j1).erase j2) hm2 hs2 hA2
    ⟨fun w => decide (w = 4), by decide, hasEdge_no_wt1 E2 (by decide) 4,
      ⟨4, 6, by simp [E2], by decide, by decide⟩⟩
    ⟨fun w => decide (w = 1 ∨ w = 2), by decide, ⟨1, 2, by simp [E2], by decide, by decide⟩⟩
    (hasEdge_update_false_iff E2 c5Edges 6 (by decide) (by decide))
  have h4 : 4 ≤ (((A.erase j1).erase j2).erase j3).card := by
    by_contra hlt
    exact c5_or_bound_ind _ (by omega) ⟨C3, ((A.erase j1).erase j2).erase j3, rfl, hm3, hs3, hA3⟩
  have hc3 := Finset.card_erase_add_one hj3
  have hc2 := Finset.card_erase_add_one hj2
  have hc1 := Finset.card_erase_add_one hj1
  omega

end PEqualNP.Outside.L_meta_603

theorem PEqualNP.Outside.L_meta_603 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 11 → (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (3, 5), (4, 6), (0, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) → ∃ A : Finset ℕ, A.card = 4 ∧ ∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
  classical
  intro C hmono hsz hspec
  let A : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
    ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and)
  let B : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
    ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
  have hAmem : ∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
      C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    intro j
    simp only [A, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    rintro ⟨g, hj, _⟩
    by_contra h
    rw [List.getElem?_eq_none (not_lt.mp h)] at hj
    simp at hj
  have hBmem : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ B := by
    intro j g hj hop
    have hlt : j < C.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (not_lt.mp h)] at hj
      simp at hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, g, hj, hop⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    rcases (Finset.mem_filter.mp hjA).2 with ⟨g1, h1, op1⟩
    rcases (Finset.mem_filter.mp hjB).2 with ⟨g2, h2, op2⟩
    rw [h1] at h2
    have hgeq := Option.some.inj h2
    rw [← hgeq, op1] at op2
    cases op2
  have hunion : A ∪ B ⊆ Finset.range C.gates.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have hsum : A.card + B.card ≤ C.gates.length := by
    rw [← Finset.card_union_of_disjoint hdisj]
    calc
      (A ∪ B).card ≤ (Finset.range C.gates.length).card := Finset.card_le_card hunion
      _ = C.gates.length := Finset.card_range _
  have hA4 : 4 ≤ A.card :=
    PEqualNP.Outside.L_meta_603.and_bound_4 C A hmono hspec (fun j g hj hop => (hAmem j).mpr ⟨g, hj, hop⟩)
  have hB7 : 7 ≤ B.card :=
    PEqualNP.Outside.L_meta_603.or_bound_7 C B hmono hspec hBmem
  have hlen : C.gates.length ≤ 11 := hsz
  refine ⟨A, by omega, hAmem⟩
