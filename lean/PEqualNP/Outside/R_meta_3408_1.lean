import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3408_1

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def targetFun (x11 : Fin 9 → Bool) : Bool :=
  x11 0 && x11 1 || x11 1 && x11 2 || x11 2 && x11 3 || x11 3 && x11 4 || x11 4 && x11 0 ||
    x11 0 && x11 5 || x11 1 && x11 6 || x11 2 && x11 7 || x11 3 && x11 8 ||
    x11 5 && x11 7 || x11 6 && x11 8 || x11 8 && x11 5

private lemma wires_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun i => acc[i]?.getD false))]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma bool_le_all_false_true (a b : List Bool) (hle : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (a.getD i false = true → b.getD i false = true) := h

private lemma list_mono_step (gs : List Gate)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a b : List Bool) (hlen : a.length = b.length)
    (hle : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun j => acc[j]?.getD false))]) a).getD i false = true →
      (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun j => acc[j]?.getD false))]) b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hmon g (by simp)
    apply ih (fun g' hg' => hmon g' (by simp [hg']))
    · simp [hlen]
    · intro i hi
      simp only [List.getD_eq_getElem?_getD] at hi ⊢
      by_cases hilt : i < a.length
      · rw [List.getElem?_append_left hilt] at hi
        rw [List.getElem?_append_left (by omega : i < b.length)]
        simpa [List.getD_eq_getElem?_getD] using hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
      · by_cases hieq : i = a.length
        · subst hieq
          rw [List.getElem?_append_right (le_refl _)] at hi
          rw [List.getElem?_append_right (by omega : b.length ≤ a.length)]
          simp only [Nat.sub_self, hlen, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
          rcases hg.1 with hand | hor
          · rw [hand] at hi ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
            rintro _ ⟨k, hk, rfl⟩
            simpa [List.getD_eq_getElem?_getD] using hle k (by simpa [List.getD_eq_getElem?_getD] using hi _ ⟨k, hk, rfl⟩)
          · rw [hor] at hi ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
            rcases hi with ⟨_, ⟨k, hk, rfl⟩, hk_true⟩
            exact ⟨_, ⟨k, hk, rfl⟩, by simpa [List.getD_eq_getElem?_getD] using hle k (by simpa [List.getD_eq_getElem?_getD] using hk_true)⟩
        · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi

theorem main
    (h_lo : ∀ (x1 : List (Fin 11)) (x2 x3 : Circuit),
      x1.length ≤ 2 → Monotone2 x2 → FanInTwo x3 → x2.size + x3.size ≤ 12 →
      x2.output ≤ 24 → x3.output ≤ 24 →
      (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ 24) →
      x3.output < 11 + x2.gates.length →
      ∃ (x11 : Fin 9 → Bool),
        have x12 : List Bool := List.ofFn x11 ++ [x11 0 || x11 4]
        have x13 : List Bool := x2.wires (x12 ++ [GateOp.and.eval (List.map (fun (x13 : Fin 11) => x12.getD (↑x13) false) x1)])
        x3.eval (x13 ++ [!x13.getD x2.output false]) ≠ targetFun x11)
    (h_ge : ∀ (x1 : List (Fin 11)) (x2 x3 : Circuit),
      x1.length ≤ 2 → Monotone2 x2 → FanInTwo x3 → x2.size + x3.size ≤ 12 →
      x2.output ≤ 24 → x3.output ≤ 24 →
      (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ 24) →
      11 + x2.gates.length ≤ x3.output →
      x3.output < 12 + x2.gates.length + x3.gates.length →
      1 ≤ x3.size →
      ∃ (x11 : Fin 9 → Bool),
        have x12 : List Bool := List.ofFn x11 ++ [x11 0 || x11 4]
        have x13 : List Bool := x2.wires (x12 ++ [GateOp.and.eval (List.map (fun (x13 : Fin 11) => x12.getD (↑x13) false) x1)])
        x3.eval (x13 ++ [!x13.getD x2.output false]) ≠ targetFun x11) :
    ∀ (x1 : List (Fin (11 : ℕ))) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), x1.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.FanInTwo x3 → x2.size + x3.size ≤ (12 : ℕ) → x2.output ≤ (24 : ℕ) → x3.output ≤ (24 : ℕ) → (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ (24 : ℕ)) → ∃ (x11 : Fin (9 : ℕ) → Bool), have x12 : List Bool := List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]; have x13 : List Bool := x2.wires (x12 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x13 : Fin (11 : ℕ)) => x12.getD (↑x13) Bool.false) x1)]); x3.eval (x13 ++ [!x13.getD x2.output Bool.false]) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 x3 hlen hm2 hf2 hsz ho2 ho3 hinp
  by_cases hout_lo : x3.output < 11 + x2.gates.length
  · exact h_lo x1 x2 x3 hlen hm2 hf2 hsz ho2 ho3 hinp hout_lo
  · by_cases hout_hi : 12 + x2.gates.length + x3.gates.length ≤ x3.output
    · refine ⟨fun _ => true, ?_⟩
      dsimp only
      change _ ≠ targetFun (fun _ => true)
      let init_t := List.ofFn (fun _ : Fin 9 => true) ++ [true || true] ++
          [GateOp.and.eval (List.map (fun (x13 : Fin 11) => (List.ofFn (fun _ : Fin 9 => true) ++ [true || true]).getD ↑x13 false) x1)]
      have heval_false : x3.eval (x2.wires init_t ++ [!(x2.wires init_t).getD x2.output false]) = false := by
        simp only [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none]
        · rfl
        · rw [wires_length]
          simp only [List.length_append, List.length_singleton, wires_length, List.length_ofFn]
          omega
      rw [heval_false]
      decide
    · have hout_ge : 11 + x2.gates.length ≤ x3.output := by omega
      have hout_lt : x3.output < 12 + x2.gates.length + x3.gates.length := by omega
      by_cases hsz3 : 1 ≤ x3.size
      · exact h_ge x1 x2 x3 hlen hm2 hf2 hsz ho2 ho3 hinp hout_ge hout_lt hsz3
      · have hgs3 : x3.gates = [] := List.eq_nil_of_length_eq_zero (by simpa [Circuit.size] using hsz3)
        have hout_eq : x3.output = 11 + x2.gates.length := by simp [hgs3] at hout_lt; omega
        let y0 : Fin 9 → Bool := fun _ => false
        let y1 : Fin 9 → Bool := fun _ => true
        let x12_0 := List.ofFn y0 ++ [y0 0 || y0 4]
        let x12_1 := List.ofFn y1 ++ [y1 0 || y1 4]
        let init0 := x12_0 ++ [GateOp.and.eval (List.map (fun (x13 : Fin 11) => x12_0.getD ↑x13 false) x1)]
        let init1 := x12_1 ++ [GateOp.and.eval (List.map (fun (x13 : Fin 11) => x12_1.getD ↑x13 false) x1)]
        have hinit_len : init0.length = init1.length := by simp [init0, init1, x12_0, x12_1]
        have hinit_le : ∀ i, init0.getD i false = true → init1.getD i false = true := by
          intro i hi
          have h12_false : ∀ j, x12_0.getD j false = false := by
            intro j
            rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
            all_goals simp [x12_0, y0, List.getD_eq_getElem?_getD]
          have h12_le : ∀ j, x12_0.getD j false = true → x12_1.getD j false = true := by
            intro j hj; rw [h12_false j] at hj; cases hj
          by_cases hilt : i < 10
          · have hi0 : init0.getD i false = x12_0.getD i false := by
              simp only [init0, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left (by simp [x12_0, hilt])]
            rw [hi0, h12_false i] at hi
            cases hi
          · by_cases hieq : i = 10
            · subst hieq
              simp only [init0, init1, List.getD_eq_getElem?_getD] at hi ⊢
              rw [List.getElem?_append_right (by simp [x12_0])] at hi
              rw [List.getElem?_append_right (by simp [x12_1])]
              simp only [List.length_append, List.length_ofFn, List.length_singleton, Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some, GateOp.eval] at hi ⊢
              simp only [List.all_eq_true, List.mem_map, id_eq] at hi ⊢
              rintro _ ⟨k, hk, rfl⟩
              simpa [List.getD_eq_getElem?_getD] using h12_le ↑k (by simpa [List.getD_eq_getElem?_getD] using hi _ ⟨k, hk, rfl⟩)
            · simp only [init0, List.getD_eq_getElem?_getD] at hi
              rw [List.getElem?_eq_none (by simp [x12_0]; omega)] at hi
              simp at hi
        have hwire_le := list_mono_step x2.gates hm2 init0 init1 hinit_len hinit_le x2.output
        have heval0 : x3.eval (x2.wires init0 ++ [!(x2.wires init0).getD x2.output false]) =
            !(x2.wires init0).getD x2.output false := by
          simp only [Circuit.eval, Circuit.wires, hgs3, List.foldl_nil, hout_eq, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by rw [wires_length]; simp [init0, x12_0])]
          rw [wires_length]
          simp [init0, x12_0]
        have heval1 : x3.eval (x2.wires init1 ++ [!(x2.wires init1).getD x2.output false]) =
            !(x2.wires init1).getD x2.output false := by
          simp only [Circuit.eval, Circuit.wires, hgs3, List.foldl_nil, hout_eq, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by rw [wires_length]; simp [init1, x12_1])]
          rw [wires_length]
          simp [init1, x12_1]
        by_cases h0 : (x2.wires init0).getD x2.output false = true
        · have h1 : (x2.wires init1).getD x2.output false = true := by
            dsimp only [Circuit.wires] at h0 ⊢
            exact hwire_le h0
          refine ⟨y1, ?_⟩
          dsimp only
          change _ ≠ targetFun y1
          have htf1 : targetFun y1 = true := by simp [targetFun, y1]
          rw [htf1]
          change x3.eval (x2.wires init1 ++ [!(x2.wires init1).getD x2.output false]) ≠ true
          rw [heval1, h1]
          decide
        · have h0f : (x2.wires init0).getD x2.output false = false := Bool.eq_false_iff.mpr h0
          refine ⟨y0, ?_⟩
          dsimp only
          change _ ≠ targetFun y0
          have htf0 : targetFun y0 = false := by simp [targetFun, y0]
          rw [htf0]
          change x3.eval (x2.wires init0 ++ [!(x2.wires init0).getD x2.output false]) ≠ false
          rw [heval0, h0f]
          decide

end PEqualNP.Outside.R_meta_3408_1
