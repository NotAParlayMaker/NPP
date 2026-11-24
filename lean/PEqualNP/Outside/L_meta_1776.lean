import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1776

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem W_inp (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega)]; exact ih

theorem W_oob (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  apply List.getD_eq_default; rw [W_len]; exact hi

theorem W_spec (gs : List Gate) (x : List Bool) : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
    (W gs x).getD (x.length + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + k then (W gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g h; simp at h
  | append_singleton gs a ih =>
    intro k g h
    rw [W_snoc]
    rcases Nat.lt_or_ge k gs.length with hk | hk
    · rw [List.getElem?_append_left hk] at h
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih k g h]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + k
      · simp only [hi, if_true]
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
      · simp only [hi, if_false]
    · rcases Nat.lt_or_ge k (gs.length + 1) with hk1 | hk1
      · have hk2 : k = gs.length := by omega
        subst hk2
        have hag : a = g := by simpa using h
        subst hag
        rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
        simp only [Nat.sub_self, List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + gs.length
        · simp only [hi, if_true]
          rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
        · simp only [hi, if_false]
          exact W_oob gs x i (by omega)
      · rw [List.getElem?_eq_none (by simp; omega)] at h
        cases h

def sh (p : ℕ) (i : ℕ) : ℕ := if p < i then i - 1 else i

def up (p : ℕ) (m : ℕ) : ℕ := if m < p then m else m + 1

def del (G : List Gate) (j : ℕ) (T : Gate → Gate) : List Gate :=
  G.take j ++ (G.drop (j + 1)).map T

theorem del_len (G : List Gate) (j : ℕ) (T : Gate → Gate) (hj : j < G.length) :
    (del G j T).length + 1 = G.length := by
  simp [del]; omega

theorem del_lt (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : k < j) (h : (del G j T)[k]? = some g) : G[k]? = some g := by
  unfold del at h
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take] at h
  simpa [hk] using h

theorem del_ge (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
    (hk : j ≤ k) (h : (del G j T)[k]? = some g) : ∃ g0, G[k + 1]? = some g0 ∧ g = T g0 := by
  unfold del at h
  rw [List.getElem?_append_right (by simp; omega)] at h
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop] at h
  have e : j + 1 + (k - min j G.length) = k + 1 := by
    rw [Nat.min_eq_left (by omega)]; omega
  rw [e] at h
  cases hg : G[k + 1]? with
  | none => rw [hg] at h; simp at h
  | some g0 => rw [hg] at h; exact ⟨g0, rfl, by simpa using h.symm⟩

theorem sim (G : List Gate) (j : ℕ) (T : Gate → Gate) (x : List Bool) (n : ℕ) (hx : x.length = n)
    (hj : j < G.length)
    (hT : ∀ (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g → ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G x).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G x).getD i false) →
      (∀ i, i < n → ρ' i = x.getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ)) :
    ∀ m, (W (del G j T) x).getD m false = (W G x).getD (up (n + j) m) false := by
  subst hx
  have hlen := del_len G j T hj
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m x.length with hm | hm
  · rw [W_inp _ _ _ hm, show up (x.length + j) m = m by simp only [up]; split_ifs <;> omega,
      W_inp _ _ _ hm]
  · obtain ⟨k, rfl⟩ : ∃ k, m = x.length + k := ⟨m - x.length, by omega⟩
    rcases Nat.lt_or_ge k (del G j T).length with hk | hk
    · have hg : (del G j T)[k]? = some (del G j T)[k] := List.getElem?_eq_getElem hk
      rw [W_spec _ _ k _ hg]
      rcases Nat.lt_or_ge k j with hkj | hkj
      · have hg0 := del_lt G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + k by
          simp only [up]; split_ifs <;> omega, W_spec _ _ k _ hg0]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, if_true]
          rw [ih i hi, show up (x.length + j) i = i by simp only [up]; split_ifs <;> omega]
        · simp only [hi, if_false]
      · obtain ⟨g0, hg0, hgT⟩ := del_ge G j T k _ hj hkj hg
        rw [show up (x.length + j) (x.length + k) = x.length + (k + 1) by
          simp only [up]; split_ifs <;> omega, W_spec _ _ (k + 1) _ hg0, hgT]
        apply hT k g0 hkj hg0
        · intro i hi
          by_cases h1 : x.length + j < i
          · have e1 : sh (x.length + j) i = i - 1 := by simp only [sh]; split_ifs; rfl
            rw [e1]
            by_cases h2 : i < x.length + (k + 1)
            · have h3 : i - 1 < x.length + k := by omega
              simp only [h2, h3, if_true]
              rw [ih (i - 1) h3]
              congr 1
              simp only [up]; split_ifs <;> omega
            · have h3 : ¬ i - 1 < x.length + k := by omega
              simp only [h2, h3, if_false]
          · have e1 : sh (x.length + j) i = i := by simp only [sh]; split_ifs; rfl
            rw [e1]
            have h2 : i < x.length + (k + 1) := by omega
            have h3 : i < x.length + k := by omega
            simp only [h2, h3, if_true]
            rw [ih i h3]
            congr 1
            simp only [up]; split_ifs <;> omega
        · have h2 : x.length + j < x.length + (k + 1) := by omega
          simp only [h2, if_true]
        · intro i hi
          have h2 : i < x.length + (k + 1) := by omega
          simp only [h2, if_true]
        · intro i hi
          have h3 : i < x.length + k := by omega
          simp only [h3, if_true]
          exact W_inp _ _ _ hi
        · intro i hi
          have h3 : ¬ i < x.length + k := by omega
          simp only [h3, if_false]
    · rw [W_oob _ _ _ (by omega), W_oob _ _ _ (by simp only [up]; split_ifs <;> omega)]

def Ts (p t : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i = p then t else sh p i⟩

theorem Ts_eval (p t : ℕ) (g : Gate) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ' t = ρ p) :
    (Ts p t g).op.eval ((Ts p t g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  simp only [Ts, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i = p
  · subst hi; simp only [Function.comp, if_true]; exact hp
  · simp only [Function.comp, hi, if_false]; exact h1 i hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def Rn (v B : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i = v then B else i⟩

theorem subst (G : List Gate) (n v : ℕ) (hv : v < n) (x y : List Bool) (hx : x.length = n)
    (hy : y.length = n)
    (hxy : ∀ i, i < n → i ≠ v → x.getD i false = y.getD i false)
    (hyv : y.getD v false = false) :
    ∀ m, m ≠ v →
      (W (G.map (Rn v (n + G.length))) x).getD m false = (W G y).getD m false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hmv
  rcases Nat.lt_or_ge m n with hm | hm
  · rw [W_inp (G.map (Rn v (n + G.length))) x m (by omega), W_inp G y m (by omega)]
    exact hxy m hm hmv
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    rcases Nat.lt_or_ge k G.length with hk | hk
    · have hg : G[k]? = some G[k] := List.getElem?_eq_getElem hk
      have hg1 : (G.map (Rn v (n + G.length)))[k]? = some (Rn v (n + G.length) G[k]) := by
        rw [List.getElem?_map, hg]; rfl
      have e1 := W_spec (G.map (Rn v (n + G.length))) x k _ hg1
      have e2 := W_spec G y k _ hg
      rw [hx] at e1
      rw [hy] at e2
      rw [e1, e2]
      simp only [Rn, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i = v
      · have h1 : ¬ (n + G.length < n + k) := by omega
        have h2 : i < n + k := by omega
        rw [if_pos hi, if_neg h1, if_pos h2, hi, W_inp G y v (by omega)]
        exact hyv.symm
      · rw [if_neg hi]
        by_cases h2 : i < n + k
        · rw [if_pos h2, if_pos h2]; exact ih i h2 hi
        · rw [if_neg h2, if_neg h2]
    · rw [W_oob (G.map (Rn v (n + G.length))) x (n + k) (by rw [List.length_map]; omega),
        W_oob G y (n + k) (by omega)]

theorem gate_alias (H : List Gate) (n j B : ℕ) (op : GateOp) (inputs : List ℕ)
    (hg : H[j]? = some ⟨op, inputs⟩)
    (hB : n + H.length ≤ B) (hmem : B ∈ inputs)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : inputs.length ≤ 2) :
    ∃ t, (t < n + j ∨ t = B) ∧ ∀ x : List Bool, x.length = n →
      (W H x).getD (n + j) false = (W H x).getD t false := by
  have hjl : j < H.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hBj : ¬ (B < n + j) := by omega
  have key : ∀ x : List Bool, x.length = n → (W H x).getD (n + j) false =
      op.eval (inputs.map fun i => if i < n + j then (W H x).getD i false else false) := by
    intro x hx
    have e := W_spec H x j _ hg
    rw [hx] at e
    exact e
  have hBf : ∀ x : List Bool, x.length = n → (W H x).getD B false = false := by
    intro x hx
    exact W_oob H x B (by omega)
  have hfalse : (∀ x : List Bool, x.length = n → (W H x).getD (n + j) false = false) →
      ∃ t, (t < n + j ∨ t = B) ∧ ∀ x : List Bool, x.length = n →
        (W H x).getD (n + j) false = (W H x).getD t false := by
    intro h
    exact ⟨B, Or.inr rfl, fun x hx => by rw [h x hx, hBf x hx]⟩
  have hwire : ∀ w, (∀ x : List Bool, x.length = n → (W H x).getD (n + j) false =
      (if w < n + j then (W H x).getD w false else false)) →
      ∃ t, (t < n + j ∨ t = B) ∧ ∀ x : List Bool, x.length = n →
        (W H x).getD (n + j) false = (W H x).getD t false := by
    intro w h
    by_cases hw : w < n + j
    · exact ⟨w, Or.inl hw, fun x hx => by rw [h x hx, if_pos hw]⟩
    · exact hfalse (fun x hx => by rw [h x hx, if_neg hw])
  rcases hop with rfl | rfl
  · apply hfalse
    intro x hx
    rw [key x hx]
    simp only [GateOp.eval]
    rw [List.all_eq_false]
    exact ⟨false, List.mem_map.mpr ⟨B, hmem, if_neg hBj⟩, by simp⟩
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hmem
    · apply hwire a
      intro x hx
      rw [key x hx]
      simp [GateOp.eval]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · apply hwire b
        intro x hx
        rw [key x hx, ← h]
        simp [GateOp.eval, hBj]
      · apply hwire a
        intro x hx
        rw [key x hx, ← h]
        simp [GateOp.eval, hBj]
    · simp at hlen

theorem main (n : ℕ) (v : Fin n) (C : Circuit) (hM : Monotone2 C) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hdep1 : ∃ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) ∧ y v = false ∧ f x ≠ f y)
    (hdep2 : ∃ x : Fin n → Bool, f x ≠ x v) :
    ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f (Function.update x v false) := by
  obtain ⟨B, hB⟩ : ∃ B, B = n + C.gates.length := ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = C.gates.map (Rn v.val B) := ⟨_, rfl⟩
  obtain ⟨o1, ho1⟩ : ∃ o1, o1 = if C.output = v.val then B else C.output := ⟨_, rfl⟩
  have hlen1 : G1.length = C.gates.length := by rw [hG1, List.length_map]
  have hf' : ∀ x : Fin n → Bool, (W C.gates (List.ofFn x)).getD C.output false = f x := hf
  have hS : ∀ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) → y v = false → ∀ m, m ≠ v.val →
      (W G1 (List.ofFn x)).getD m false = (W C.gates (List.ofFn y)).getD m false := by
    intro x y hxy hyv
    rw [hG1, hB]
    apply subst C.gates n v.val v.isLt (List.ofFn x) (List.ofFn y) (by simp) (by simp)
    · intro i hi hiv
      rw [ofFn_getD x i hi, ofFn_getD y i hi]
      exact hxy ⟨i, hi⟩ (fun h => hiv (congrArg Fin.val h))
    · rw [ofFn_getD y v.val v.isLt]
      exact hyv
  have hC1 : ∀ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) → y v = false →
      (W G1 (List.ofFn x)).getD o1 false = f y := by
    intro x y hxy hyv
    rw [← hf' y]
    by_cases ho : C.output = v.val
    · rw [ho1, if_pos ho, ho, W_oob G1 (List.ofFn x) B (by rw [List.length_ofFn]; omega),
        W_inp C.gates (List.ofFn y) v.val (by rw [List.length_ofFn]; exact v.isLt),
        ofFn_getD y v.val v.isLt]
      exact hyv.symm
    · rw [ho1, if_neg ho]
      exact hS x y hxy hyv C.output ho
  have hM1 : ∀ g ∈ G1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rw [hG1] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := hM g0 hg0
    exact ⟨h0.1, by simp only [Rn, List.length_map]; exact h0.2⟩
  by_cases hr : ∃ g ∈ C.gates, v.val ∈ g.inputs
  · obtain ⟨g, hgm, hvg⟩ := hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgm
    have hj1 : j < G1.length := by omega
    have hg1 : G1[j]? = some ⟨C.gates[j].op,
        C.gates[j].inputs.map fun i => if i = v.val then B else i⟩ := by
      rw [hG1, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hBm : B ∈ C.gates[j].inputs.map fun i => if i = v.val then B else i :=
      List.mem_map.mpr ⟨v.val, hvg, if_pos rfl⟩
    have hMj := hM _ hgm
    have hopj : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
      have h0 := hMj.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
      exact h0
    obtain ⟨t, ht, hal⟩ := gate_alias G1 n j B _ _ hg1 (by omega) hBm hopj
      (by rw [List.length_map]; exact hMj.2)
    have key : ∀ (x : Fin n → Bool) (m : ℕ),
        (W (del G1 j (Ts (n + j) t)) (List.ofFn x)).getD m false
          = (W G1 (List.ofFn x)).getD (up (n + j) m) false := by
      intro x
      apply sim G1 j (Ts (n + j) t) (List.ofFn x) n (by simp) hj1
      intro k g _ _ ρ ρ' h1 h2 h5 h3 h4
      apply Ts_eval _ _ g ρ ρ' h1
      rcases ht with ht | ht
      · have e : sh (n + j) t = t := by
          simp only [sh]; split_ifs <;> omega
        have a1 := h1 t (by omega)
        rw [e] at a1
        rw [a1, h5 t ht, h2]
        exact (hal (List.ofFn x) (by simp)).symm
      · rw [h4 t (by omega), h2, hal (List.ofFn x) (by simp), ht]
        exact (W_oob G1 (List.ofFn x) B (by rw [List.length_ofFn]; omega)).symm
    refine ⟨⟨del G1 j (Ts (n + j) t), if o1 = n + j then t else sh (n + j) o1⟩, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ del G1 j (Ts (n + j) t) at hg
      unfold del at hg
      rcases List.mem_append.mp hg with h | h
      · exact hM1 g (List.mem_of_mem_take h)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
        have h0 := hM1 g0 (List.mem_of_mem_drop hg0)
        exact ⟨h0.1, by simp only [Ts, List.length_map]; exact h0.2⟩
    · have hd := del_len G1 j (Ts (n + j) t) hj1
      change (del G1 j (Ts (n + j) t)).length < C.gates.length
      omega
    · intro x
      change (W (del G1 j (Ts (n + j) t)) (List.ofFn x)).getD
        (if o1 = n + j then t else sh (n + j) o1) false = _
      rw [key x, ← hC1 x (Function.update x v false)
        (fun i hi => by rw [Function.update_apply, if_neg hi])
        (by rw [Function.update_apply, if_pos rfl])]
      by_cases ho : o1 = n + j
      · rw [if_pos ho, ho, hal (List.ofFn x) (by simp)]
        rcases ht with ht | ht
        · rw [show up (n + j) t = t by simp only [up]; split_ifs <;> omega]
        · rw [W_oob G1 (List.ofFn x) t (by rw [List.length_ofFn]; omega)]
          exact W_oob G1 (List.ofFn x) _
            (by rw [List.length_ofFn]; simp only [up]; split_ifs <;> omega)
      · rw [if_neg ho]
        congr 1
        simp only [up, sh]
        split_ifs <;> omega
  · exfalso
    have hr' : ∀ g ∈ C.gates, v.val ∉ g.inputs := fun g hg hv => hr ⟨g, hg, hv⟩
    have hRn : ∀ g ∈ C.gates, Rn v.val B g = g := by
      intro g hg
      have e : (g.inputs.map fun i => if i = v.val then B else i) = g.inputs := by
        have e2 : (g.inputs.map fun i => if i = v.val then B else i) = g.inputs.map id := by
          apply List.map_congr_left
          intro i hi
          have hne : i ≠ v.val := fun h => hr' g hg (h ▸ hi)
          rw [if_neg hne]; rfl
        rw [e2, List.map_id]
      unfold Rn
      rw [e]
    have hG : G1 = C.gates := by
      have e2 : C.gates.map (Rn v.val B) = C.gates.map id :=
        List.map_congr_left (fun g hg => hRn g hg)
      rw [hG1, e2, List.map_id]
    by_cases ho : C.output = v.val
    · obtain ⟨x, hx⟩ := hdep2
      apply hx
      rw [← hf' x, ho,
        W_inp C.gates (List.ofFn x) v.val (by rw [List.length_ofFn]; exact v.isLt),
        ofFn_getD x v.val v.isLt]
    · obtain ⟨x, y, hxy, hyv, hne⟩ := hdep1
      apply hne
      have h := hC1 x y hxy hyv
      rw [ho1, if_neg ho, hG] at h
      rw [← h]
      exact (hf' x).symm

def F {α : Type} (step : Gate → List α → α) (gs : List Gate) (d : List α) : List α :=
  gs.foldl (fun d g => d ++ [step g d]) d

theorem F_append {α : Type} (step : Gate → List α → α) (a b : List Gate) (d : List α) :
    F step (a ++ b) d = F step b (F step a d) := by
  simp [F, List.foldl_append]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, w, i :: is => ⟨GateOp.or, [acc, i]⟩ :: chain w (w + 1) is

def cfin : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | _, w, _ :: is => cfin w (w + 1) is

theorem chain_len : ∀ (ins : List ℕ) (acc w : ℕ), (chain acc w ins).length = ins.length
  | [], _, _ => rfl
  | _ :: is, _, w => by simp [chain, chain_len is]

theorem chain_or : ∀ (ins : List ℕ) (acc w : ℕ), ∀ g ∈ chain acc w ins,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chain]
  | i :: is, acc, w => by
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact chain_or is w (w + 1) g hg

theorem chain_spec {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
    (hstep : ∀ (a b : ℕ) (d : List α),
      step ⟨GateOp.or, [a, b]⟩ d = op (d.getD a dflt) (d.getD b dflt))
    (ins : List ℕ) : ∀ (acc w : ℕ) (d : List α), d.length = w → acc < w → (∀ i ∈ ins, i < w) →
      (F step (chain acc w ins) d).length = w + ins.length ∧
      (∀ i < w, (F step (chain acc w ins) d).getD i dflt = d.getD i dflt) ∧
      (F step (chain acc w ins) d).getD (cfin acc w ins) dflt =
        ins.foldl (fun v i => op v (d.getD i dflt)) (d.getD acc dflt) ∧
      cfin acc w ins < w + ins.length := by
  induction ins with
  | nil =>
    intro acc w d hw hacc _
    refine ⟨by simp [chain, F, hw], fun i _ => by simp [chain, F], by simp [chain, F, cfin],
      by simpa [cfin] using hacc⟩
  | cons i is ih =>
    intro acc w d hw hacc hins
    have hi : i < w := hins i (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih w (w + 1) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d])
      (by simp [hw]) (by omega) (fun k hk => by have := hins k (by simp [hk]); omega)
    have hF : F step (chain acc w (i :: is)) d =
        F step (chain w (w + 1) is) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]) := by
      simp [F, chain]
    have hpre : ∀ k < w, (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD k dflt = d.getD k dflt :=
      fun k hk => List.getD_append _ _ _ _ (by omega)
    have hd : (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD w dflt =
        op (d.getD acc dflt) (d.getD i dflt) := by
      rw [List.getD_append_right _ _ _ _ (by omega), hstep]
      simp [hw]
    have hc : cfin acc w (i :: is) = cfin w (w + 1) is := by simp [cfin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF, h1]; simp only [List.length_cons]; omega
    · intro k hk; rw [hF, h2 k (by omega), hpre k hk]
    · rw [hF, hc, h3, hd, List.foldl_cons]
      exact List.foldl_ext _ _ _ (fun v k hk => by rw [hpre k (hins k (by simp [hk]))])
    · rw [hc]; simp only [List.length_cons]; omega

def PC (n m : ℕ) : List Gate := chain 0 (n + m) (List.range' 1 (n - 1))

def PW (n m : ℕ) : ℕ := cfin 0 (n + m) (List.range' 1 (n - 1))

def LC (n m : ℕ) : List Gate := chain n (n + m + (n - 1)) (List.range' (n + 1) (m - 1))

def LW (n m : ℕ) : ℕ := cfin n (n + m + (n - 1)) (List.range' (n + 1) (m - 1))

def Ckt (n m : ℕ) : Circuit :=
  ⟨PC n m ++ LC n m ++ [⟨GateOp.and, [PW n m, LW n m]⟩], n + m + (n - 1) + (m - 1)⟩

theorem asm {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
    (hstep : ∀ (a b : ℕ) (d : List α),
      step ⟨GateOp.or, [a, b]⟩ d = op (d.getD a dflt) (d.getD b dflt))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (d0 : List α) (h0 : d0.length = n + m) :
    (F step (PC n m ++ LC n m) d0).length = n + m + (n - 1) + (m - 1) ∧
    PW n m < n + m + (n - 1) + (m - 1) ∧ LW n m < n + m + (n - 1) + (m - 1) ∧
    (F step (PC n m ++ LC n m) d0).getD (PW n m) dflt =
      (List.range' 1 (n - 1)).foldl (fun v i => op v (d0.getD i dflt)) (d0.getD 0 dflt) ∧
    (F step (PC n m ++ LC n m) d0).getD (LW n m) dflt =
      (List.range' (n + 1) (m - 1)).foldl (fun v i => op v (d0.getD i dflt)) (d0.getD n dflt) := by
  unfold PC LC PW LW
  obtain ⟨a1, a2, a3, a4⟩ := chain_spec step dflt op hstep (List.range' 1 (n - 1)) 0 (n + m) d0 h0
    (by omega) (fun i hi => by rw [List.mem_range'_1] at hi; omega)
  rw [List.length_range'] at a1 a4
  obtain ⟨b1, b2, b3, b4⟩ := chain_spec step dflt op hstep (List.range' (n + 1) (m - 1)) n
    (n + m + (n - 1)) (F step (chain 0 (n + m) (List.range' 1 (n - 1))) d0) a1 (by omega)
    (fun i hi => by rw [List.mem_range'_1] at hi; omega)
  rw [List.length_range'] at b1 b4
  rw [F_append]
  refine ⟨b1, by omega, b4, ?_, ?_⟩
  · rw [b2 _ a4]; exact a3
  · rw [b3, a2 n (by omega)]
    exact List.foldl_ext _ _ _
      (fun v k hk => by rw [List.mem_range'_1] at hk; rw [a2 k (by omega)])

def wstep (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wstep_or (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.or, [a, b]⟩ d = (d.getD a false || d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem foldl_or (f : ℕ → Bool) : ∀ (l : List ℕ) (a : Bool),
    l.foldl (fun v i => v || f i) a = (a || l.any f)
  | [], a => by simp
  | i :: is, a => by simp [foldl_or f is, Bool.or_assoc]

theorem any_chain (f : ℕ → Bool) (s k : ℕ) :
    (f s || (List.range' (s + 1) k).any f) = true ↔ ∃ i, s ≤ i ∧ i < s + k + 1 ∧ f i = true := by
  rw [Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact ⟨s, le_refl _, by omega, h⟩
    · rw [List.mem_range'_1] at hi; exact ⟨i, by omega, by omega, h⟩
  · rintro ⟨i, h1, h2, h⟩
    by_cases e : i = s
    · subst e; exact Or.inl h
    · exact Or.inr ⟨i, by rw [List.mem_range'_1]; omega, h⟩

theorem ckt_eval (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (x : List Bool) (hx : x.length = n + m) :
    (Ckt n m).eval x = true ↔ (∃ i, i < n ∧ x.getD i false = true) ∧
      (∃ k, n ≤ k ∧ k < n + m ∧ x.getD k false = true) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := asm wstep false (fun u v => u || v) wstep_or n m hn hm x hx
  have hE : (Ckt n m).eval x =
      wstep ⟨GateOp.and, [PW n m, LW n m]⟩ (F wstep (PC n m ++ LC n m) x) := by
    show (F wstep (PC n m ++ LC n m ++ [⟨GateOp.and, [PW n m, LW n m]⟩]) x).getD
      (n + m + (n - 1) + (m - 1)) false = _
    rw [F_append]
    show (F wstep (PC n m ++ LC n m) x ++
      [wstep ⟨GateOp.and, [PW n m, LW n m]⟩ (F wstep (PC n m ++ LC n m) x)]).getD
      (n + m + (n - 1) + (m - 1)) false = _
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [c1]
  have hA : wstep ⟨GateOp.and, [PW n m, LW n m]⟩ (F wstep (PC n m ++ LC n m) x) =
      ((F wstep (PC n m ++ LC n m) x).getD (PW n m) false &&
        (F wstep (PC n m ++ LC n m) x).getD (LW n m) false) := by
    simp [wstep, GateOp.eval]
  rw [hE, hA, c4, c5, foldl_or (fun i => x.getD i false), foldl_or (fun i => x.getD i false),
    Bool.and_eq_true]
  have h1 := any_chain (fun i => x.getD i false) 0 (n - 1)
  have h2 := any_chain (fun i => x.getD i false) n (m - 1)
  constructor
  · rintro ⟨u, v⟩
    obtain ⟨i, _, hi, hf⟩ := h1.mp u
    obtain ⟨k, hk1, hk2, hg⟩ := h2.mp v
    clear h1 h2
    exact ⟨⟨i, by omega, hf⟩, ⟨k, hk1, by omega, hg⟩⟩
  · rintro ⟨⟨i, hi, hf⟩, ⟨k, hk1, hk2, hg⟩⟩
    have e1 : i < 0 + (n - 1) + 1 := by clear h1 h2; omega
    have e2 : k < n + (m - 1) + 1 := by clear h1 h2; omega
    exact ⟨h1.mpr ⟨i, Nat.zero_le _, e1, hf⟩, h2.mpr ⟨k, hk1, e2, hg⟩⟩

def dstep (g : Gate) (d : List ℕ) : ℕ := g.lineDegree d

theorem dstep_or (a b : ℕ) (d : List ℕ) :
    dstep ⟨GateOp.or, [a, b]⟩ d = max (d.getD a 0) (d.getD b 0) := by
  simp [dstep, Gate.lineDegree]

theorem foldl_max_zero (g : ℕ → ℕ) : ∀ (l : List ℕ) (a : ℕ), a = 0 → (∀ i ∈ l, g i = 0) →
    l.foldl (fun v i => max v (g i)) a = 0
  | [], a, ha, _ => by simpa using ha
  | i :: is, a, ha, h => by
    rw [List.foldl_cons]
    exact foldl_max_zero g is _ (by rw [ha, h i (by simp)]; rfl)
      (fun k hk => h k (by simp [hk]))

theorem init_getD (N : ℕ) (marked : Finset ℕ) (i : ℕ) (hi : i < N) (hm : i ∉ marked) :
    ((List.range N).map fun i => if i ∈ marked then 1 else 0).getD i 0 = 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [hm]

theorem ckt_deg (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (marked : Finset ℕ) :
    ((∀ i < n, i ∉ marked) →
      ((Ckt n m).lineDegrees (n + m) marked).getD (PW n m) 0 = 0) ∧
    ((∀ i, n ≤ i → i < n + m → i ∉ marked) →
      ((Ckt n m).lineDegrees (n + m) marked).getD (LW n m) 0 = 0) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := asm dstep 0 max dstep_or n m hn hm
    ((List.range (n + m)).map fun i => if i ∈ marked then 1 else 0) (by simp)
  have hD : (Ckt n m).lineDegrees (n + m) marked =
      F dstep (PC n m ++ LC n m) ((List.range (n + m)).map fun i => if i ∈ marked then 1 else 0) ++
      [dstep ⟨GateOp.and, [PW n m, LW n m]⟩ (F dstep (PC n m ++ LC n m)
        ((List.range (n + m)).map fun i => if i ∈ marked then 1 else 0))] := by
    show F dstep (PC n m ++ LC n m ++ [⟨GateOp.and, [PW n m, LW n m]⟩]) _ = _
    rw [F_append]
    rfl
  rw [hD]
  constructor
  · intro h
    rw [List.getD_append _ _ _ _ (by omega), c4]
    exact foldl_max_zero _ _ _ (init_getD _ _ _ (by omega) (h 0 hn))
      (fun i hi => by
        rw [List.mem_range'_1] at hi
        exact init_getD _ _ _ (by omega) (h i (by omega)))
  · intro h
    rw [List.getD_append _ _ _ _ (by omega), c5]
    exact foldl_max_zero _ _ _ (init_getD _ _ _ (by omega) (h n (le_refl _) (by omega)))
      (fun i hi => by
        rw [List.mem_range'_1] at hi
        exact init_getD _ _ _ (by omega) (h i (by omega) (by omega)))

theorem gate_and (n m j : ℕ) (hj : j < (Ckt n m).gates.length)
    (h : (NestedCover.gateAt (Ckt n m) j).op = GateOp.and) :
    NestedCover.gateAt (Ckt n m) j = ⟨GateOp.and, [PW n m, LW n m]⟩ := by
  have hg : NestedCover.gateAt (Ckt n m) j =
      (PC n m ++ LC n m ++ [Gate.mk GateOp.and [PW n m, LW n m]]).getD j ⟨GateOp.or, []⟩ := rfl
  rw [hg] at h ⊢
  by_cases hlt : j < (PC n m ++ LC n m).length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt] at h
    have hmem := List.getElem_mem hlt
    rw [List.mem_append] at hmem
    have hor : ((PC n m ++ LC n m)[j]).op = GateOp.or := by
      rcases hmem with hmem | hmem
      · exact (chain_or _ _ _ _ hmem).1
      · exact (chain_or _ _ _ _ hmem).1
    rw [hor] at h
    cases h
  · have hl : (Ckt n m).gates.length = (PC n m ++ LC n m).length + 1 := by
      simp [Ckt]
      omega
    have hje : j = (PC n m ++ LC n m).length := by omega
    rw [hje, List.getD_append_right _ _ _ _ (le_refl _)]
    simp

theorem ckt_mono (n m : ℕ) : Monotone2 (Ckt n m) := by
  intro g hg
  have hg' : g ∈ PC n m ++ LC n m ++ [Gate.mk GateOp.and [PW n m, LW n m]] := hg
  rw [List.mem_append, List.mem_append, List.mem_singleton] at hg'
  rcases hg' with (hg' | hg') | rfl
  · obtain ⟨h1, h2⟩ := chain_or _ _ _ g hg'
    rw [h1, h2]; simp
  · obtain ⟨h1, h2⟩ := chain_or _ _ _ g hg'
    rw [h1, h2]; simp
  · simp

theorem ckt_size (n m : ℕ) : (Ckt n m).size = (n - 1) + (m - 1) + 1 := by
  simp [Ckt, Circuit.size, PC, LC, chain_len]
  omega

def gAB {N : ℕ} (A B : Finset (Fin N)) (x : Fin N → Bool) : Bool :=
  decide (∃ a ∈ A, ∃ b ∈ B, x a = true ∧ x b = true)

theorem gAB_true {N : ℕ} (A B : Finset (Fin N)) (x : Fin N → Bool) :
    gAB A B x = true ↔ ∃ a ∈ A, ∃ b ∈ B, x a = true ∧ x b = true := by
  unfold gAB
  exact decide_eq_true_iff

theorem gAB_comm {N : ℕ} (A B : Finset (Fin N)) (x : Fin N → Bool) : gAB A B x = gAB B A x := by
  rw [Bool.eq_iff_iff, gAB_true, gAB_true]
  constructor
  · rintro ⟨a, ha, b, hb, h1, h2⟩
    exact ⟨b, hb, a, ha, h2, h1⟩
  · rintro ⟨a, ha, b, hb, h1, h2⟩
    exact ⟨b, hb, a, ha, h2, h1⟩

theorem step {N : ℕ} (A B : Finset (Fin N)) (hd : Disjoint A B) (a : Fin N) (ha : a ∈ A)
    (b : Fin N) (hb : b ∈ B) (C : Circuit) (hM : Monotone2 C)
    (hf : ∀ x : Fin N → Bool, C.eval (List.ofFn x) = gAB A B x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
      ∀ x : Fin N → Bool, D.eval (List.ofFn x) = gAB (A.erase a) B x := by
  have hab : ∀ c, c ∈ A → c ∈ B → False := fun c h1 h2 => Finset.disjoint_left.mp hd h1 h2
  have hdep1 : ∃ x y : Fin N → Bool, (∀ i, i ≠ a → x i = y i) ∧ y a = false ∧
      gAB A B x ≠ gAB A B y := by
    refine ⟨fun i => decide (i = a ∨ i = b),
      Function.update (fun i => decide (i = a ∨ i = b)) a false, ?_, by simp, ?_⟩
    · intro i hi; rw [Function.update_of_ne hi]
    · have h1 : gAB A B (fun i => decide (i = a ∨ i = b)) = true := by
        rw [gAB_true]; exact ⟨a, ha, b, hb, by simp, by simp⟩
      have h2 : gAB A B (Function.update (fun i => decide (i = a ∨ i = b)) a false) = false := by
        rw [Bool.eq_false_iff]; intro h; rw [gAB_true] at h
        obtain ⟨a', ha', b', hb', h3, h4⟩ := h
        have ne1 : a' ≠ a := by
          intro e; rw [e, Function.update_self] at h3; cases h3
        rw [Function.update_of_ne ne1] at h3
        have h5 := of_decide_eq_true h3
        rcases h5 with h5 | h5
        · exact ne1 h5
        · rw [h5] at ha'; exact hab b ha' hb
      rw [h1, h2]; simp
  have hdep2 : ∃ x : Fin N → Bool, gAB A B x ≠ x a := by
    refine ⟨fun i => decide (i = a), ?_⟩
    have h2 : gAB A B (fun i => decide (i = a)) = false := by
      rw [Bool.eq_false_iff]; intro h; rw [gAB_true] at h
      obtain ⟨a', ha', b', hb', h3, h4⟩ := h
      have h3' := of_decide_eq_true h3
      have h4' := of_decide_eq_true h4
      rw [h3'] at ha'; rw [h4'] at hb'
      exact hab a ha' hb'
    rw [h2]; simp
  obtain ⟨D, hD1, hD2, hD3⟩ := main N a C hM (gAB A B) hf hdep1 hdep2
  refine ⟨D, hD1, hD2, fun x => ?_⟩
  rw [hD3 x, Bool.eq_iff_iff, gAB_true, gAB_true]
  constructor
  · rintro ⟨a', ha', b', hb', h1, h2⟩
    have ne1 : a' ≠ a := by
      intro e; rw [e, Function.update_self] at h1; cases h1
    have ne2 : b' ≠ a := by
      intro e; rw [e, Function.update_self] at h2; cases h2
    rw [Function.update_of_ne ne1] at h1
    rw [Function.update_of_ne ne2] at h2
    exact ⟨a', Finset.mem_erase.mpr ⟨ne1, ha'⟩, b', hb', h1, h2⟩
  · rintro ⟨a', ha', b', hb', h1, h2⟩
    obtain ⟨ne1, ha''⟩ := Finset.mem_erase.mp ha'
    have ne2 : b' ≠ a := by
      intro e; rw [e] at hb'; exact hab a ha hb'
    exact ⟨a', ha'', b', hb', by rw [Function.update_of_ne ne1]; exact h1,
      by rw [Function.update_of_ne ne2]; exact h2⟩

theorem base {N : ℕ} (A B : Finset (Fin N)) (hd : Disjoint A B) (a : Fin N) (ha : a ∈ A)
    (b : Fin N) (hb : b ∈ B) (C : Circuit)
    (hf : ∀ x : Fin N → Bool, C.eval (List.ofFn x) = gAB A B x) : 1 ≤ C.size := by
  by_contra hlt
  have hg : C.gates = [] :=
    List.eq_nil_of_length_eq_zero (by unfold Circuit.size at hlt; omega)
  have hE : ∀ x : List Bool, C.eval x = x.getD C.output false := by
    intro x; unfold Circuit.eval Circuit.wires; rw [hg]; rfl
  have h1 := hf (fun _ => true)
  have ht : gAB A B (fun _ => true) = true := by
    rw [gAB_true]; exact ⟨a, ha, b, hb, rfl, rfl⟩
  rw [hE, ht] at h1
  have ho : C.output < N := by
    by_contra hno
    rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at h1
    cases h1
  have h2 := hf (fun i => decide (i = ⟨C.output, ho⟩))
  have hF : gAB A B (fun i => decide (i = ⟨C.output, ho⟩)) = false := by
    rw [Bool.eq_false_iff]; intro h; rw [gAB_true] at h
    obtain ⟨a', ha', b', hb', h3, h4⟩ := h
    have h3' := of_decide_eq_true h3
    have h4' := of_decide_eq_true h4
    rw [h3'] at ha'; rw [h4'] at hb'
    exact Finset.disjoint_left.mp hd ha' hb'
  rw [hE, ofFn_getD _ _ ho, hF] at h2
  simp at h2

theorem lb {N : ℕ} : ∀ (k : ℕ) (A B : Finset (Fin N)), A.card + B.card = k → Disjoint A B →
    A.Nonempty → B.Nonempty → ∀ C : Circuit, Monotone2 C →
    (∀ x : Fin N → Bool, C.eval (List.ofFn x) = gAB A B x) → A.card + B.card ≤ C.size + 1 := by
  intro k
  induction k with
  | zero =>
    intro A B hk _ hA _
    have := Finset.card_pos.mpr hA
    omega
  | succ k ih =>
    intro A B hk hd hA hB C hM hf
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    by_cases h2 : 2 ≤ A.card
    · obtain ⟨D, hD1, hD2, hD3⟩ := step A B hd a ha b hb C hM hf
      have hc : (A.erase a).card = A.card - 1 := Finset.card_erase_of_mem ha
      have := ih (A.erase a) B (by omega) (hd.mono_left (Finset.erase_subset _ _))
        (Finset.card_pos.mp (by omega)) ⟨b, hb⟩ D hD1 hD3
      omega
    · by_cases h3 : 2 ≤ B.card
      · have hf' : ∀ x : Fin N → Bool, C.eval (List.ofFn x) = gAB B A x :=
          fun x => by rw [hf x, gAB_comm]
        obtain ⟨D, hD1, hD2, hD3⟩ := step B A hd.symm b hb a ha C hM hf'
        have hc : (B.erase b).card = B.card - 1 := Finset.card_erase_of_mem hb
        have := ih (B.erase b) A (by omega) (hd.symm.mono_left (Finset.erase_subset _ _))
          (Finset.card_pos.mp (by omega)) ⟨a, ha⟩ D hD1 hD3
        omega
      · have h4 := base A B hd a ha b hb C hf
        have h5 : 0 < A.card := Finset.card_pos.mpr ⟨a, ha⟩
        have h6 : 0 < B.card := Finset.card_pos.mpr ⟨b, hb⟩
        omega

theorem stmt_iff (n m : ℕ) (z : Fin (n + m) → Bool) :
    (∃ p : Fin n, ∃ j : Fin m, z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n j) = true) ↔
    (∃ i, i < n ∧ (List.ofFn z).getD i false = true) ∧
      (∃ k, n ≤ k ∧ k < n + m ∧ (List.ofFn z).getD k false = true) := by
  constructor
  · rintro ⟨p, j, h1, h2⟩
    have hp := p.isLt
    have hj := j.isLt
    refine ⟨⟨p.val, hp, ?_⟩, ⟨n + j.val, by omega, by omega, ?_⟩⟩
    · rw [ofFn_getD z p.val (by omega)]; exact h1
    · rw [ofFn_getD z (n + j.val) (by omega)]; exact h2
  · rintro ⟨⟨i, hi, h1⟩, ⟨k, hk1, hk2, h2⟩⟩
    rw [ofFn_getD z i (by omega)] at h1
    rw [ofFn_getD z k hk2] at h2
    refine ⟨⟨i, hi⟩, ⟨k - n, by omega⟩, h1, ?_⟩
    have e : Fin.natAdd n (⟨k - n, by omega⟩ : Fin m) = ⟨k, hk2⟩ :=
      Fin.ext (by show n + (k - n) = k; omega)
    rw [e]; exact h2

def PA (n m : ℕ) : Finset (Fin (n + m)) := Finset.univ.filter (fun i => i.val < n)

def LB (n m : ℕ) : Finset (Fin (n + m)) := Finset.univ.filter (fun i => ¬ i.val < n)

theorem gAB_iff (n m : ℕ) (z : Fin (n + m) → Bool) :
    gAB (PA n m) (LB n m) z = true ↔
    (∃ i, i < n ∧ (List.ofFn z).getD i false = true) ∧
      (∃ k, n ≤ k ∧ k < n + m ∧ (List.ofFn z).getD k false = true) := by
  rw [gAB_true]
  constructor
  · rintro ⟨a, ha, b, hb, h1, h2⟩
    have ha' : a.val < n := (Finset.mem_filter.mp ha).2
    have hb' : ¬ b.val < n := (Finset.mem_filter.mp hb).2
    refine ⟨⟨a.val, ha', ?_⟩, ⟨b.val, by omega, b.isLt, ?_⟩⟩
    · rw [ofFn_getD z a.val a.isLt]; exact h1
    · rw [ofFn_getD z b.val b.isLt]; exact h2
  · rintro ⟨⟨i, hi, h1⟩, ⟨k, hk1, hk2, h2⟩⟩
    rw [ofFn_getD z i (by omega)] at h1
    rw [ofFn_getD z k hk2] at h2
    exact ⟨⟨i, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ⟨k, hk2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.not_lt.mpr hk1⟩, h1, h2⟩

theorem fin_thm (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ C : Circuit, IsMinimalMonoCircuit (n + m) C ∧
      (∀ z : Fin (n + m) → Bool, circuitFun (n + m) C z =
        decide (∃ p : Fin n, ∃ j : Fin m, z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n j) = true)) ∧
      (∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
        (∃ i ∈ (NestedCover.gateAt C j).inputs,
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧
        (∃ i ∈ (NestedCover.gateAt C j).inputs,
          (C.lineDegrees (n + m) (Finset.range n)).getD i 0 = 0)) := by
  have hfun : ∀ z : Fin (n + m) → Bool, circuitFun (n + m) (Ckt n m) z =
      decide (∃ p : Fin n, ∃ j : Fin m,
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n j) = true) := by
    intro z
    rw [Bool.eq_iff_iff, decide_eq_true_iff, stmt_iff]
    exact ckt_eval n m hn hm (List.ofFn z) (by simp)
  refine ⟨Ckt n m, ⟨ckt_mono n m, ?_⟩, hfun, ?_⟩
  · intro D hD hDf
    have hf : ∀ x : Fin (n + m) → Bool, D.eval (List.ofFn x) = gAB (PA n m) (LB n m) x := by
      intro x
      have h2 : D.eval (List.ofFn x) = circuitFun (n + m) (Ckt n m) x := congrFun hDf x
      rw [h2, hfun x, Bool.eq_iff_iff, decide_eq_true_iff, stmt_iff, gAB_iff]
    have hdis : Disjoint (PA n m) (LB n m) := by
      rw [Finset.disjoint_left]
      intro a h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hA : (PA n m).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩⟩
    have hB : (LB n m).Nonempty :=
      ⟨⟨n, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_irrefl n⟩⟩
    have hlb := lb _ (PA n m) (LB n m) rfl hdis hA hB D hD hf
    have hcard : (PA n m).card + (LB n m).card = n + m := by
      have hU : PA n m ∪ LB n m = Finset.univ := by
        ext a
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_cases h : a.val < n
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have h := Finset.card_union_add_card_inter (PA n m) (LB n m)
      rw [hU, Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.card_univ, Fintype.card_fin,
        Finset.card_empty] at h
      omega
    have hs := ckt_size n m
    omega
  · intro j hj hand
    rw [gate_and n m j hj hand]
    obtain ⟨d1, _⟩ := ckt_deg n m hn hm (Finset.Ico n (n + m))
    obtain ⟨_, d2⟩ := ckt_deg n m hn hm (Finset.range n)
    refine ⟨⟨PW n m, by simp, d1 (fun i hi => by rw [Finset.mem_Ico]; omega)⟩,
      ⟨LW n m, by simp, d2 (fun i h1 h2 => by rw [Finset.mem_range]; omega)⟩⟩

end PEqualNP.Outside.L_meta_1776

theorem PEqualNP.Outside.L_meta_1776 : ∀ n m : ℕ, 0 < n → 0 < m → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalMonoCircuit (n + m) C ∧ (∀ z : Fin (n + m) → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) C z = decide (∃ p : Fin n, ∃ j : Fin m, z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n j) = true)) ∧ (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ (∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.range n)).getD i 0 = 0)) := by
  intro n m hn hm
  exact PEqualNP.Outside.L_meta_1776.fin_thm n m hn hm
