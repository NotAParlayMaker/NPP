import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_clb_034

private lemma all_replicate_true (n : ℕ) : (List.replicate n true).all id = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private lemma all_replicate_false {n : ℕ} (hn : 1 ≤ n) : (List.replicate n false).all id = false := by
  cases n with
  | zero => omega
  | succ n => simp [List.replicate_succ]

private lemma getD_eq_default_of_le {α : Type*} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD]
  have : l[i]? = none := List.getElem?_eq_none_iff.mpr h
  rw [this]
  rfl

private lemma getD_replicate_true (n i : ℕ) (hi : i < n) :
    (List.replicate n true).getD i false = true := by
  rw [List.getD_eq_getElem?_getD]
  have : (List.replicate n true)[i]? = some true := by
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨by simpa using hi, ?_⟩
    simp
  rw [this]
  rfl

private lemma getD_set_ne (n k i : ℕ) (hki : k ≠ i) (hi : i < n) :
    ((List.replicate n true).set k false).getD i false = true := by
  rw [List.getD_eq_getElem?_getD]
  have hi' : i < (List.replicate n true).length := by simpa using hi
  rw [List.getElem?_set_of_lt false (List.replicate n true) hi']
  have : ¬(k = i) := hki
  simp [this]
  rw [← List.getD_eq_getElem?_getD]
  exact getD_replicate_true n i hi

private lemma all_set_false (n k : ℕ) (hk : k < n) :
    ((List.replicate n true).set k false).all id = false := by
  have hk' : k < (List.replicate n true).length := by simpa using hk
  rw [List.set_eq_take_cons_drop false hk']
  simp [List.all_append]

private lemma wires_nil (C : Circuit) (h : C.gates = []) (x : List Bool) : C.wires x = x := by
  unfold Circuit.wires
  rw [h]
  rfl

private lemma eval_nil (C : Circuit) (h : C.gates = []) (x : List Bool) : C.eval x = x.getD C.output false := by
  unfold Circuit.eval
  rw [wires_nil C h x]

private lemma wires_singleton (C : Circuit) (g : Gate) (h : C.gates = [g]) (x : List Bool) :
    C.wires x = x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)] := by
  unfold Circuit.wires
  rw [h]
  rfl

private lemma eval_singleton (C : Circuit) (g : Gate) (h : C.gates = [g]) (x : List Bool) :
    C.eval x = (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD C.output false := by
  unfold Circuit.eval
  rw [wires_singleton C g h x]

private lemma getD_append_singleton (x : List Bool) (v : Bool) (o : ℕ) :
    (x ++ [v]).getD o false =
      if o < x.length then x.getD o false
      else if o = x.length then v
      else false := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  · have hge : x.length + 1 ≤ o := by omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    cases ho : o - x.length with
    | zero => omega
    | succ m => simp [List.getD]

end PEqualNP.Outside.L_clb_034

open PEqualNP.Outside.L_clb_034

theorem PEqualNP.Outside.L_clb_034 :
  ∀ (n d : ℕ), 2 ≤ n →
    ({x : List Bool | x.all id = true} : Language Bool) ∉
      PEqualNP.CircuitLowerBounds.SizeDepth
        {PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not}
        (fun m : ℕ => if m = n then 1 else m + 2) d := by
  intro n d hn hSD
  have h_ex := hSD n
  dsimp only at h_ex
  rw [ite_eq_left] at h_ex
  · obtain ⟨C, h_gates, h_sz, h_dp, h_dec⟩ := h_ex
    unfold Circuit.size at h_sz
    let x_all := List.replicate n true
    have hx_all_len : x_all.length = n := by simp [x_all]
    have hx_all_all : x_all.all id = true := all_replicate_true n
    have h_all : C.eval x_all = true := by
      rw [h_dec x_all hx_all_len]
      exact hx_all_all
    rcases hgates : C.gates with _ | ⟨g, rest⟩
    · -- Case 1: C.gates = []
      have heval : ∀ x, C.eval x = x.getD C.output false := fun x => eval_nil C hgates x
      rw [heval x_all] at h_all
      by_cases ho : C.output < n
      · let k := if C.output = 0 then 1 else 0
        have hk : k < n := by dsimp [k]; split_ifs <;> omega
        have hki : k ≠ C.output := by dsimp [k]; split_ifs <;> omega
        let x_bad := (List.replicate n true).set k false
        have hx_bad_len : x_bad.length = n := by simp [x_bad]
        have h_bad_eval : C.eval x_bad = true := by
          rw [heval x_bad]
          exact getD_set_ne n k C.output hki ho
        have h_bad_mem : x_bad.all id = true := (h_dec x_bad hx_bad_len).mp h_bad_eval
        have h_bad_false : x_bad.all id = false := all_set_false n k hk
        rw [h_bad_false] at h_bad_mem
        contradiction
      · have hge : n ≤ C.output := by omega
        have hdef : x_all.getD C.output false = false :=
          getD_eq_default_of_le x_all false C.output (by rw [hx_all_len]; exact hge)
        rw [hdef] at h_all
        contradiction
    · -- Case 2: C.gates = g :: rest
      rw [hgates] at h_sz
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons r rest2 =>
          simp only [List.length_cons] at h_sz
          omega
      subst hrest
      have hg_len : g.inputs.length ≤ 1 := by
        have := h_gates g (by simp [hgates])
        exact this.2
      have heval : ∀ x, C.eval x = (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD C.output false :=
        fun x => eval_singleton C g hgates x
      by_cases ho_lt : C.output < n
      · let k := if C.output = 0 then 1 else 0
        have hk : k < n := by dsimp [k]; split_ifs <;> omega
        have hki : k ≠ C.output := by dsimp [k]; split_ifs <;> omega
        let x_bad := (List.replicate n true).set k false
        have hx_bad_len : x_bad.length = n := by simp [x_bad]
        have heval_bad : C.eval x_bad = x_bad.getD C.output false := by
          rw [heval x_bad, getD_append_singleton]
          have : C.output < x_bad.length := by rw [hx_bad_len]; exact ho_lt
          simp [this]
        have h_bad_eval : C.eval x_bad = true := by
          rw [heval_bad]
          exact getD_set_ne n k C.output hki ho_lt
        have h_bad_mem : x_bad.all id = true := (h_dec x_bad hx_bad_len).mp h_bad_eval
        have h_bad_false : x_bad.all id = false := all_set_false n k hk
        rw [h_bad_false] at h_bad_mem
        contradiction
      · by_cases ho_gt : C.output > n
        · have heval_all : C.eval x_all = false := by
            rw [heval x_all, getD_append_singleton]
            have h1 : ¬(C.output < x_all.length) := by simp [hx_all_len]; omega
            have h2 : ¬(C.output = x_all.length) := by simp [hx_all_len]; omega
            simp [h1, h2]
          rw [heval_all] at h_all
          contradiction
        · have ho_eq : C.output = n := by omega
          have heval_gate : ∀ x, x.length = n → C.eval x = g.op.eval (g.inputs.map fun i => x.getD i false) := by
            intro x hx
            rw [heval x, getD_append_singleton]
            have h2 : C.output = x.length := by simp [hx, ho_eq]
            simp [h2]
          rcases hgin : g.inputs with _ | ⟨inp, inprest⟩
          · -- g.inputs = []
            let x0 := List.replicate n false
            have hx0_len : x0.length = n := by simp [x0]
            have heval0 : C.eval x0 = g.op.eval [] := by
              simpa [hgin] using heval_gate x0 hx0_len
            have heval_all' : C.eval x_all = g.op.eval [] := by
              simpa [hgin] using heval_gate x_all hx_all_len
            have h0_true : C.eval x0 = true := by rw [heval0, ← heval_all', h_all]
            have h0_mem : x0.all id = true := (h_dec x0 hx0_len).mp h0_true
            have h0_false : x0.all id = false := all_replicate_false (by omega)
            rw [h0_false] at h0_mem
            contradiction
          · have hinprest : inprest = [] := by
              cases inprest with
              | nil => rfl
              | cons _ _ => simp [hgin] at hg_len
            subst hinprest
            by_cases hinp_ge : inp ≥ n
            · let x0 := List.replicate n false
              have hx0_len : x0.length = n := by simp [x0]
              have hx0_get : x0.getD inp false = false :=
                getD_eq_default_of_le x0 false inp (by rw [hx0_len]; exact hinp_ge)
              have heval0 : C.eval x0 = g.op.eval [false] := by
                have := heval_gate x0 hx0_len
                simp only [hgin, List.map_cons, List.map_nil, hx0_get] at this
                exact this
              have heval_all' : C.eval x_all = g.op.eval [false] := by
                have := heval_gate x_all hx_all_len
                have hx_all_get : x_all.getD inp false = false :=
                  getD_eq_default_of_le x_all false inp (by rw [hx_all_len]; exact hinp_ge)
                simp only [hgin, List.map_cons, List.map_nil, hx_all_get] at this
                exact this
              have h0_true : C.eval x0 = true := by rw [heval0, ← heval_all', h_all]
              have h0_mem : x0.all id = true := (h_dec x0 hx0_len).mp h0_true
              have h0_false : x0.all id = false := all_replicate_false (by omega)
              rw [h0_false] at h0_mem
              contradiction
            · have hinp_lt : inp < n := by omega
              let k := if inp = 0 then 1 else 0
              have hk : k < n := by dsimp [k]; split_ifs <;> omega
              have hki : k ≠ inp := by dsimp [k]; split_ifs <;> omega
              let x_bad := (List.replicate n true).set k false
              have hx_bad_len : x_bad.length = n := by simp [x_bad]
              have h_bad_inp : x_bad.getD inp false = true := getD_set_ne n k inp hki hinp_lt
              have h_all_inp : x_all.getD inp false = true := getD_replicate_true n inp hinp_lt
              have heval_bad : C.eval x_bad = g.op.eval [true] := by
                have := heval_gate x_bad hx_bad_len
                simp only [hgin, List.map_cons, List.map_nil, h_bad_inp] at this
                exact this
              have heval_all' : C.eval x_all = g.op.eval [true] := by
                have := heval_gate x_all hx_all_len
                simp only [hgin, List.map_cons, List.map_nil, h_all_inp] at this
                exact this
              have h_bad_eval : C.eval x_bad = true := by rw [heval_bad, ← heval_all', h_all]
              have h_bad_mem : x_bad.all id = true := (h_dec x_bad hx_bad_len).mp h_bad_eval
              have h_bad_false : x_bad.all id = false := all_set_false n k hk
              rw [h_bad_false] at h_bad_mem
              contradiction
  · rfl
