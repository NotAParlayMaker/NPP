import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_11721

namespace PEqualNP.Outside.L_meta_14840

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem getD_app (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_append_left h, if_pos h]
  · rw [if_neg h, List.getElem?_append_right (by omega)]
    by_cases h2 : i = w.length
    · simp [h2]
    · rw [if_neg h2, List.getElem?_eq_none (by simp; omega)]; rfl

theorem wf_spec (gs : List Gate) (x : List Bool) :
    (wf gs x).length = x.length + gs.length ∧ (∀ i, i < x.length → (wf gs x).getD i false = x.getD i false) ∧
    ∀ j (hj : j < gs.length), (wf gs x).getD (x.length + j) false
      = (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then (wf gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun _ _ => rfl, fun j hj => absurd hj (by simp)⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e : wf (gs ++ [g]) x = wf gs x ++ [g.op.eval (g.inputs.map fun i => (wf gs x).getD i false)] := by
      rw [wf_append]; rfl
    have low : ∀ i, i < x.length + gs.length → (wf (gs ++ [g]) x).getD i false = (wf gs x).getD i false := by
      intro i hi
      rw [e, getD_app, if_pos (by omega)]
    refine ⟨by rw [e]; simp [h1]; omega, fun i hi => by rw [low i (by omega), h2 i hi], fun j hj => ?_⟩
    by_cases hjl : j < gs.length
    · rw [low _ (by omega), h3 j hjl, List.getElem_append_left hjl]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      by_cases hi : i < x.length + j
      · rw [if_pos hi, if_pos hi, low i (by omega)]
      · rw [if_neg hi, if_neg hi]
    · obtain rfl : j = gs.length := by simp at hj; omega
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      rw [e, getD_app, if_neg (by omega), if_pos h1.symm]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      by_cases hi : i < x.length + gs.length
      · rw [if_pos hi, getD_app, if_pos (by omega)]
      · rw [if_neg hi]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]; rfl

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) : (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Value of wire `i` at input `x` (`false` if there is no such wire). -/
def V (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool := (wf gs (List.ofFn x)).getD i false

theorem V_in (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) : V gs x i = x ⟨i, h⟩ := by
  unfold V
  rw [(wf_spec gs (List.ofFn x)).2.1 i (by simpa using h), getD_ofFn]

theorem V_gate (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    V gs x (n + j) = (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < n + j then V gs x i else false) := by
  have := (wf_spec gs (List.ofFn x)).2.2 j hj
  simpa [V] using this

theorem V_out (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : n + gs.length ≤ i) : V gs x i = false := by
  unfold V
  have := (wf_spec gs (List.ofFn x)).1
  simp only [List.length_ofFn] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem eval_eq (gs : List Gate) (o : ℕ) {n : ℕ} (x : Fin n → Bool) : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = V gs x o := rfl

/-- Delete a gate whose value is an earlier wire or `false` on the inputs `X y`. -/
theorem delete (gs : List Gate) (o : ℕ) (k : ℕ) (hk : k < gs.length) (a : Fin 8) (idx : ℕ → ℕ)
    (X : (Fin 7 → Bool) → Fin 8 → Bool) (hX0 : ∀ y, X y a = false)
    (hX : ∀ v : Fin 8, v ≠ a → ∃ i : Fin 7, idx v.val = i.val ∧ ∀ y, X y v = y i)
    (r : ℕ) (hr : ∀ y, V gs (X y) (8 + k) = if r < 8 + k then V gs (X y) r else false)
    (hone : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j)
    (hop : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
      (∀ i j : Fin gs'.length, (gs'.get i).op = GateOp.not → (gs'.get j).op = GateOp.not → i = j) ∧
      gs'.length + 1 = gs.length ∧ ∀ y : Fin 7 → Bool, V gs' y o' = V gs (X y) o := by
  classical
  set M := 7 + gs.length with hM
  let f1 : ℕ → ℕ := fun w => if w < 8 then (if w = a.val then M else idx w) else if w < 8 + k then w - 1 else w - 2
  let f : ℕ → ℕ := fun w => if w = 8 + k then (if r < 8 + k then f1 r else M) else f1 w
  let e : ℕ → ℕ := fun p => if p < k then p else p + 1
  have he : ∀ p, p < gs.length - 1 → e p < gs.length := by intro p hp; simp only [e]; split <;> omega
  let gt : (p : ℕ) → p < gs.length - 1 → Gate := fun p hp =>
    ⟨(gs[e p]'(he p hp)).op, (gs[e p]'(he p hp)).inputs.map fun w => if w < 8 + e p then f w else M⟩
  let gs' : List Gate := List.ofFn fun p : Fin (gs.length - 1) => gt p.1 p.2
  have hl : gs'.length = gs.length - 1 := by simp [gs']
  have hg : ∀ p (hp : p < gs'.length), gs'[p] = gt p (by omega) := by intro p hp; simp [gs']
  -- inputs
  have hin : ∀ y w, w < 8 → ∀ B, 7 ≤ B → B ≤ M → (if f1 w < B then V gs' y (f1 w) else false) = V gs (X y) w := by
    intro y w hw B hB hBM
    rw [V_in gs (X y) w hw]
    by_cases hwa : w = a.val
    · have : f1 w = M := by simp only [f1]; rw [if_pos hw, if_pos hwa]
      rw [this, if_neg (by omega)]
      have : (⟨w, hw⟩ : Fin 8) = a := Fin.ext hwa
      rw [this, hX0]
    · obtain ⟨i, h1, h2⟩ := hX ⟨w, hw⟩ (fun h => hwa (congrArg Fin.val h))
      have : f1 w = i.val := by simp only [f1]; rw [if_pos hw, if_neg hwa]; exact h1
      rw [this, if_pos (by omega), h2 y, V_in gs' y i.val i.2]
  -- gates
  have main : ∀ y : Fin 7 → Bool, ∀ n p, p < n → p < gs.length - 1 → V gs' y (7 + p) = V gs (X y) (8 + e p) := by
    intro y n
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      intro p hpn hp
      have gateval : ∀ q, q < p → V gs' y (7 + q) = V gs (X y) (8 + e q) := fun q hq => ih q (by omega) (by omega)
      have wire : ∀ w, w < 8 + e p → (if f w < 7 + p then V gs' y (f w) else false) = V gs (X y) w := by
        intro w hw
        have old : ∀ u, u < 8 + e p → u ≠ 8 + k → (if f1 u < 7 + p then V gs' y (f1 u) else false) = V gs (X y) u := by
          intro u hu huk
          by_cases h8 : u < 8
          · exact hin y u h8 (7 + p) (by omega) (by omega)
          · by_cases hk' : u < 8 + k
            · have e1 : f1 u = 7 + (u - 8) := by simp only [f1]; rw [if_neg h8, if_pos hk']; omega
              have hq : u - 8 < p := by
                simp only [e] at hu; split at hu <;> omega
              rw [e1, if_pos (by omega), gateval (u - 8) hq]
              have : e (u - 8) = u - 8 := by simp only [e]; rw [if_pos (by omega)]
              rw [this]; congr 1; omega
            · have e1 : f1 u = 7 + (u - 9) := by simp only [f1]; rw [if_neg h8, if_neg hk']; omega
              have hq : u - 9 < p := by
                simp only [e] at hu; split at hu <;> omega
              rw [e1, if_pos (by omega), gateval (u - 9) hq]
              have : e (u - 9) = u - 8 := by simp only [e]; rw [if_neg (by omega)]; omega
              rw [this]; congr 1; omega
        by_cases hwk : w = 8 + k
        · subst hwk
          have e1 : f (8 + k) = if r < 8 + k then f1 r else M := if_pos rfl
          rw [e1, hr y]
          by_cases hrk : r < 8 + k
          · rw [if_pos hrk, if_pos hrk]; exact old r (by omega) (by omega)
          · rw [if_neg hrk, if_neg hrk, if_neg (by omega)]
        · have e1 : f w = f1 w := by simp only [f]; rw [if_neg hwk]
          rw [e1]; exact old w hw hwk
      rw [V_gate gs' y p (by omega), hg p (by omega), V_gate gs (X y) (e p) (he p hp)]
      simp only [gt, List.map_map]
      congr 1
      refine List.map_congr_left fun w _ => ?_
      simp only [Function.comp]
      by_cases hw : w < 8 + e p
      · rw [if_pos hw, if_pos hw]; exact wire w hw
      · rw [if_neg hw, if_neg hw, if_neg (by omega)]
  refine ⟨gs', if o < 8 + gs.length then f o else M, ?_, ?_, by omega, ?_⟩
  · intro g hgm
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hgm
    rw [hg p hp]
    simp only [gt, List.length_map]
    exact hop _ (List.getElem_mem _)
  · intro i j hi hj
    have hi' : (gs.get ⟨e i.1, he _ (by omega)⟩).op = GateOp.not := by
      have := hi; rw [List.get_eq_getElem, hg i.1 i.2] at this; exact this
    have hj' : (gs.get ⟨e j.1, he _ (by omega)⟩).op = GateOp.not := by
      have := hj; rw [List.get_eq_getElem, hg j.1 j.2] at this; exact this
    have := congrArg Fin.val (hone _ _ hi' hj')
    simp only [e] at this
    apply Fin.ext
    split at this <;> split at this <;> omega
  · intro y
    have all : ∀ p, p < gs.length - 1 → V gs' y (7 + p) = V gs (X y) (8 + e p) := fun p hp => main y (p + 1) p (by omega) hp
    have hMf : V gs' y M = false := V_out gs' y M (by omega)
    have inn : ∀ w, w < 8 → V gs' y (f1 w) = V gs (X y) w := by
      intro w hw
      have := hin y w hw M (by omega) (le_refl _)
      by_cases hlt : f1 w < M
      · rwa [if_pos hlt] at this
      · rw [if_neg hlt] at this
        rw [← this]; exact V_out gs' y _ (by omega)
    have old : ∀ u, u < 8 + gs.length → u ≠ 8 + k → V gs' y (f1 u) = V gs (X y) u := by
      intro u hu huk
      by_cases h8 : u < 8
      · exact inn u h8
      · by_cases hk' : u < 8 + k
        · have e1 : f1 u = 7 + (u - 8) := by simp only [f1]; rw [if_neg h8, if_pos hk']; omega
          rw [e1, all (u - 8) (by omega)]
          have : e (u - 8) = u - 8 := by simp only [e]; rw [if_pos (by omega)]
          rw [this]; congr 1; omega
        · have e1 : f1 u = 7 + (u - 9) := by simp only [f1]; rw [if_neg h8, if_neg hk']; omega
          rw [e1, all (u - 9) (by omega)]
          have : e (u - 9) = u - 8 := by simp only [e]; rw [if_neg (by omega)]; omega
          rw [this]; congr 1; omega
    by_cases ho : o < 8 + gs.length
    · rw [if_pos ho]
      by_cases hok : o = 8 + k
      · subst hok
        have e1 : f (8 + k) = if r < 8 + k then f1 r else M := if_pos rfl
        rw [e1, hr y]
        by_cases hrk : r < 8 + k
        · rw [if_pos hrk, if_pos hrk]; exact old r (by omega) (by omega)
        · rw [if_neg hrk, if_neg hrk, hMf]
      · have e1 : f o = f1 o := by simp only [f]; rw [if_neg hok]
        rw [e1]; exact old o ho hok
    · rw [if_neg ho, hMf, V_out gs (X y) o (by omega)]

theorem op_and (l : List ℕ) (F : ℕ → Bool) : GateOp.eval GateOp.and (l.map F) = l.all F := by
  simp [GateOp.eval, List.all_map]

theorem op_or (l : List ℕ) (F : ℕ → Bool) : GateOp.eval GateOp.or (l.map F) = l.any F := by
  simp [GateOp.eval, List.any_map]

theorem op_not (l : List ℕ) (F : ℕ → Bool) : GateOp.eval GateOp.not (l.map F) = !((l.map F).headD false) := rfl

/-- An AND or OR gate of fan-in at most two one of whose wires is constant on `X y` is redundant there. -/
theorem redundant (gs : List Gate) (k : ℕ) (hk : k < gs.length) (X : (Fin 7 → Bool) → Fin 8 → Bool)
    (hop : (gs[k]).op = GateOp.and ∨ (gs[k]).op = GateOp.or) (hlen : (gs[k]).inputs.length ≤ 2)
    (z : ℕ) (hz : z ∈ (gs[k]).inputs) (hzk : z < 8 + k) (b : Bool) (hb : ∀ y, V gs (X y) z = b) :
    ∃ r, ∀ y, V gs (X y) (8 + k) = if r < 8 + k then V gs (X y) r else false := by
  set I := (gs[k]).inputs with hI
  -- the value as a function of the other wire
  obtain ⟨q, hq⟩ : ∃ q, ∀ F : ℕ → Bool, I.all F = (F z && F q) ∧ I.any F = (F z || F q) := by
    match I, hlen, hz with
    | [c], _, hz =>
      obtain rfl : z = c := by simpa using hz
      exact ⟨z, fun F => by simp⟩
    | [c, d], _, hz =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨d, fun F => by simp⟩
      · exact ⟨c, fun F => by simp [Bool.and_comm, Bool.or_comm]⟩
  rcases hop with h | h
  · have hv : ∀ y, V gs (X y) (8 + k) = (b && if q < 8 + k then V gs (X y) q else false) := by
      intro y
      rw [V_gate gs (X y) k hk, h, op_and, (hq _).1, if_pos hzk, hb y]
    cases b
    · exact ⟨8 + k, fun y => by rw [hv y, if_neg (Nat.lt_irrefl _)]; rfl⟩
    · exact ⟨q, fun y => by rw [hv y]; simp⟩
  · have hv : ∀ y, V gs (X y) (8 + k) = (b || if q < 8 + k then V gs (X y) q else false) := by
      intro y
      rw [V_gate gs (X y) k hk, h, op_or, (hq _).2, if_pos hzk, hb y]
    cases b
    · exact ⟨q, fun y => by rw [hv y]; simp⟩
    · exact ⟨z, fun y => by rw [hv y, if_pos hzk, hb y]; rfl⟩

/-- If the function depends on input `a` and is monotone there, some gate is redundant when `a` is off. -/
theorem exists_redundant (gs : List Gate) (o : ℕ) (a : Fin 8) (X : (Fin 7 → Bool) → Fin 8 → Bool) (hX0 : ∀ y, X y a = false)
    (hone : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j)
    (hop : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (u0 u1 w0 : Fin 8 → Bool) (hu : ∀ v, v ≠ a → u0 v = u1 v) (ha0 : u0 a = false) (ha1 : u1 a = true)
    (h0 : V gs u0 o = false) (h1 : V gs u1 o = true) (hw : w0 a = true) (hw0 : V gs w0 o = false) :
    ∃ k, k < gs.length ∧ ∃ r, ∀ y, V gs (X y) (8 + k) = if r < 8 + k then V gs (X y) r else false := by
  by_contra hno
  have nored : ∀ k (hk : k < gs.length), ((gs[k]).op = GateOp.and ∨ (gs[k]).op = GateOp.or) → ∀ z ∈ (gs[k]).inputs, z < 8 + k → ∀ b, ¬ ∀ y, V gs (X y) z = b := by
    intro k hk hk' z hz hzk b hb
    exact hno ⟨k, hk, redundant gs k hk X hk' (hop _ (List.getElem_mem _)).2 z hz hzk b hb⟩
  have va : ∀ x : Fin 8 → Bool, V gs x a.val = x a := fun x => V_in gs x a.val a.2
  -- every gate is blind to `a`, or is the negation of `a`
  have key : ∀ n j, j < n → ∀ hj : j < gs.length, V gs u0 (8 + j) = V gs u1 (8 + j) ∨
      ((gs[j]).op = GateOp.not ∧ ∀ x : Fin 8 → Bool, V gs x (8 + j) = !(x a)) := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hjn hj
      -- a wire read by gate `j`
      have wire : ∀ z, z < 8 + j → V gs u0 z = V gs u1 z ∨ z = a.val ∨ ∃ i, ∃ hi : i < j, z = 8 + i ∧ (gs[i]).op = GateOp.not ∧ ∀ x : Fin 8 → Bool, V gs x (8 + i) = !(x a) := by
        intro z hz
        by_cases h8 : z < 8
        · by_cases hza : z = a.val
          · exact Or.inr (Or.inl hza)
          · left
            rw [V_in gs u0 z h8, V_in gs u1 z h8]
            exact hu _ fun h => hza (congrArg Fin.val h)
        · rcases ih (z - 8) (by omega) (by omega) with h | ⟨h, h'⟩
          · left; rwa [show 8 + (z - 8) = z by omega] at h
          · exact Or.inr (Or.inr ⟨z - 8, by omega, by omega, h, h'⟩)
      have hg := hop _ (List.getElem_mem hj)
      have ao : ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) → V gs u0 (8 + j) = V gs u1 (8 + j) := by
        intro hao
        rw [V_gate gs u0 j hj, V_gate gs u1 j hj]
        congr 1
        refine List.map_congr_left fun z hz => ?_
        by_cases hzj : z < 8 + j
        · rw [if_pos hzj, if_pos hzj]
          rcases wire z hzj with h | h | ⟨i, hi, rfl, hn, hv⟩
          · exact h
          · exact absurd (fun y => by rw [h, va, hX0]) (nored j hj hao z hz hzj false)
          · exact absurd (fun y => by rw [hv, hX0]; rfl) (nored j hj hao (8 + i) hz hzj true)
        · rw [if_neg hzj, if_neg hzj]
      rcases hg.1 with h | h | h
      · exact Or.inl (ao (Or.inl h))
      · exact Or.inl (ao (Or.inr h))
      · -- a NOT gate
        have hval : ∀ x : Fin 8 → Bool, V gs x (8 + j) = !((gs[j]).inputs.map fun i => if i < 8 + j then V gs x i else false).headD false := by
          intro x; rw [V_gate gs x j hj, h, op_not]
        rcases hc : (gs[j]).inputs with _ | ⟨z, t⟩
        · left; rw [hval, hval, hc]; rfl
        · rw [hc] at hval
          simp only [List.map_cons, List.headD_cons] at hval
          by_cases hzj : z < 8 + j
          · simp only [if_pos hzj] at hval
            rcases wire z hzj with h' | h' | ⟨i, hi, rfl, hn, hv⟩
            · left; rw [hval, hval, h']
            · right; exact ⟨h, fun x => by rw [hval, h', va]⟩
            · have := congrArg Fin.val (hone ⟨i, by omega⟩ ⟨j, hj⟩ hn h)
              simp at this; omega
          · left; rw [hval, hval, if_neg hzj, if_neg hzj]
  by_cases ho8 : o < 8
  · by_cases hoa : o = a.val
    · rw [hoa, va, hw] at hw0; simp at hw0
    · rw [V_in gs u0 o ho8, hu _ fun h => hoa (congrArg Fin.val h), ← V_in gs u1 o ho8, h1] at h0
      simp at h0
  · by_cases hol : o < 8 + gs.length
    · rcases key (o - 8 + 1) (o - 8) (by omega) (by omega) with h | ⟨_, h⟩
      · rw [show 8 + (o - 8) = o by omega, h0, h1] at h; simp at h
      · have := h u1
        rw [show 8 + (o - 8) = o by omega, h1, ha1] at this; simp at this
    · rw [V_out gs u1 o (by omega)] at h1; simp at h1

/-- From seven inputs to eight: one new OR gate for the twin. -/
theorem lift (gs : List Gate) (o : ℕ) (a b : Fin 8) (s : Fin 7 → Fin 8) (t : Fin 7)
    (hop : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length = gs.length + 1 ∧ ∀ x : Fin 8 → Bool, V gs' x o' = V gs (fun i => if i = t then (x a || x b) else x (s i)) o := by
  set M := 9 + gs.length with hM
  let f : ℕ → ℕ := fun w => if h : w < 7 then (if (⟨w, h⟩ : Fin 7) = t then 8 else (s ⟨w, h⟩).val) else w + 2
  let gt : (p : ℕ) → p < gs.length → Gate := fun p hp => ⟨(gs[p]).op, (gs[p]).inputs.map fun w => if w < 7 + p then f w else M⟩
  let tl : List Gate := List.ofFn fun p : Fin gs.length => gt p.1 p.2
  let gs' : List Gate := ⟨.or, [a.val, b.val]⟩ :: tl
  have hl : gs'.length = gs.length + 1 := by simp [gs', tl]
  have hg0 : gs'[0]'(by omega) = ⟨.or, [a.val, b.val]⟩ := rfl
  have hg : ∀ p (hp : p < gs.length), gs'[p + 1]'(by omega) = gt p hp := by intro p hp; simp [gs', tl]
  have key : ∀ x : Fin 8 → Bool, ∀ n, (∀ p, p < n → p < gs.length → V gs' x (9 + p) = V gs (fun i => if i = t then (x a || x b) else x (s i)) (7 + p)) := by
    intro x n
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      intro p hpn hp
      have h8 : V gs' x 8 = (x a || x b) := by
        have := V_gate gs' x 0 (by omega)
        rw [hg0, op_or] at this
        simp only [List.any_cons, List.any_nil, Bool.or_false] at this
        rw [if_pos (by omega), if_pos (by omega), V_in gs' x a.val a.2, V_in gs' x b.val b.2] at this
        exact this
      have e9 : 9 + p = 8 + (p + 1) := by omega
      rw [e9, V_gate gs' x (p + 1) (by omega), hg p hp, V_gate gs _ p hp]
      simp only [gt, List.map_map]
      congr 1
      refine List.map_congr_left fun w _ => ?_
      simp only [Function.comp]
      by_cases hw : w < 7 + p
      · rw [if_pos hw, if_pos hw]
        by_cases h7 : w < 7
        · rw [V_in gs _ w h7]
          by_cases ht : (⟨w, h7⟩ : Fin 7) = t
          · have : f w = 8 := by simp only [f]; rw [dif_pos h7, if_pos ht]
            rw [this, if_pos (by omega), h8, if_pos ht]
          · have : f w = (s ⟨w, h7⟩).val := by simp only [f]; rw [dif_pos h7, if_neg ht]
            rw [this, if_pos (by have := (s ⟨w, h7⟩).2; omega), V_in gs' x _ (s ⟨w, h7⟩).2, if_neg ht]
        · have : f w = 9 + (w - 7) := by simp only [f]; rw [dif_neg h7]; omega
          rw [this, if_pos (by omega), ih (w - 7) (by omega) (by omega), show 7 + (w - 7) = w by omega]
      · rw [if_neg hw, if_neg hw, if_neg (by omega)]
  refine ⟨gs', if o < 7 + gs.length then f o else M, ?_, hl, ?_⟩
  · intro g hgm
    rcases List.mem_cons.1 hgm with rfl | h
    · exact ⟨Or.inr rfl, by simp⟩
    · obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem h
      have hp' : p < gs.length := by simpa [tl] using hp
      have : tl[p] = gt p hp' := by simp [tl]
      rw [this]
      simp only [gt, List.length_map]
      exact hop _ (List.getElem_mem _)
  · intro x
    by_cases ho : o < 7 + gs.length
    · rw [if_pos ho]
      by_cases h7 : o < 7
      · rw [V_in gs _ o h7]
        by_cases ht : (⟨o, h7⟩ : Fin 7) = t
        · have : f o = 8 := by simp only [f]; rw [dif_pos h7, if_pos ht]
          rw [this, if_pos ht]
          have := V_gate gs' x 0 (by omega)
          rw [hg0, op_or] at this
          simp only [List.any_cons, List.any_nil, Bool.or_false] at this
          rw [if_pos (by omega), if_pos (by omega), V_in gs' x a.val a.2, V_in gs' x b.val b.2] at this
          exact this
        · have : f o = (s ⟨o, h7⟩).val := by simp only [f]; rw [dif_pos h7, if_neg ht]
          rw [this, V_in gs' x _ (s ⟨o, h7⟩).2, if_neg ht]
      · have : f o = 9 + (o - 7) := by simp only [f]; rw [dif_neg h7]; omega
        rw [this, key x (o - 7 + 1) (o - 7) (by omega) (by omega), show 7 + (o - 7) = o by omega]
    · rw [if_neg ho, V_out gs' x M (by omega), V_out gs _ o (by omega)]

/-- Graph function of a flat edge list. -/
def gf (L : List ℕ) {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide (∃ i < L.length / 2, (List.ofFn x).getD (L.getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (L.getD (2 * i + 1) 0) false = true)

theorem twin (L : List ℕ) (K : List ℕ) (a b : Fin 8) (s : Fin 7 → Fin 8) (t : Fin 7) (idx : ℕ → ℕ)
    (row : ∀ (gates : List Gate) (o : ℕ), (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j) →
      (∀ x : Fin 7 → Bool, V gates x o = gf K x) →
      ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, V gates' x o' = gf K x)
    (X : (Fin 7 → Bool) → Fin 8 → Bool) (hX0 : ∀ y, X y a = false)
    (hX : ∀ v : Fin 8, v ≠ a → ∃ i : Fin 7, idx v.val = i.val ∧ ∀ y, X y v = y i)
    (hXf : ∀ y, gf L (X y) = gf K y)
    (hup : ∀ x : Fin 8 → Bool, gf K (fun i => if i = t then (x a || x b) else x (s i)) = gf L x)
    (u0 u1 w0 : Fin 8 → Bool) (hu : ∀ v, v ≠ a → u0 v = u1 v) (ha0 : u0 a = false) (ha1 : u1 a = true)
    (h0 : gf L u0 = false) (h1 : gf L u1 = true) (hw : w0 a = true) (hw0 : gf L w0 = false)
    (gates : List Gate) (o : ℕ) (hop : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j)
    (hf : ∀ x : Fin 8 → Bool, V gates x o = gf L x) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, V gates' x o' = gf L x := by
  obtain ⟨k, hk, r, hr⟩ := exists_redundant gates o a X hX0 hone hop u0 u1 w0 hu ha0 ha1 (by rw [hf, h0]) (by rw [hf, h1]) hw (by rw [hf, hw0])
  obtain ⟨g1, o1, c1, c2, c3, c4⟩ := delete gates o k hk a idx X hX0 hX r hr hone hop
  obtain ⟨g2, o2, d1, d2, d3⟩ := row g1 o1 c1 c2 fun y => by rw [c4, hf, hXf]
  obtain ⟨g3, o3, e1, e2, e3⟩ := lift g2 o2 a b s t d1
  exact ⟨g3, o3, e1, by omega, fun x => by rw [e3, d3, hup]⟩

end PEqualNP.Outside.L_meta_14840

open PEqualNP.Outside.L_meta_14840 in
theorem PEqualNP.Outside.L_meta_14840 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hop hone hf
  exact twin [0, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] [0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] 2 3 (fun i => ![0, 1, 3, 4, 5, 6, 7] i) 2 (fun n => [0, 1, 7, 2, 3, 4, 5, 6].getD n 0) PEqualNP.Outside.L_meta_11721
    (fun y v => ![y 0, y 1, false, y 2, y 3, y 4, y 5, y 6] v) (by decide +kernel) (by
      intro v hv
      fin_cases v
      all_goals first
        | exact absurd rfl hv
        | exact ⟨0, rfl, fun y => rfl⟩
        | exact ⟨1, rfl, fun y => rfl⟩
        | exact ⟨2, rfl, fun y => rfl⟩
        | exact ⟨3, rfl, fun y => rfl⟩
        | exact ⟨4, rfl, fun y => rfl⟩
        | exact ⟨5, rfl, fun y => rfl⟩
        | exact ⟨6, rfl, fun y => rfl⟩)
    (by decide +kernel) (by decide +kernel)
    (fun v => decide (v = 6)) (fun v => decide (v = 6 ∨ v = 2)) (fun v => decide (v = 2))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) gates o hop hone hf
