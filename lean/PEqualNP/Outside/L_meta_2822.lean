import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2822

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

def Tt (p : ℕ) : Gate → Gate
  | ⟨GateOp.and, l⟩ => ⟨GateOp.and, (l.filter fun i => decide (i ≠ p)).map (sh p)⟩
  | ⟨GateOp.or, l⟩ => if p ∈ l then ⟨GateOp.and, []⟩ else ⟨GateOp.or, l.map (sh p)⟩
  | ⟨GateOp.not, l⟩ => if l.head? = some p then ⟨GateOp.or, []⟩ else ⟨GateOp.not, l.map (sh p)⟩
  | g => g

theorem all_filter (p : ℕ) (ρ ρ' : ℕ → Bool) (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i)
    (hp : ρ p = true) (l : List ℕ) :
    ((((l.filter fun i => decide (i ≠ p)).map (sh p)).map ρ').all id) = ((l.map ρ).all id) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = p
    · have e : ((a :: l).filter fun i => decide (i ≠ p)) = (l.filter fun i => decide (i ≠ p)) := by
        simp [List.filter_cons, ha]
      rw [e, ih]
      simp [ha, hp]
    · have e : ((a :: l).filter fun i => decide (i ≠ p))
          = a :: (l.filter fun i => decide (i ≠ p)) := by
        simp [List.filter_cons, ha]
      rw [e]
      simp only [List.map_cons, List.all_cons]
      rw [ih, h1 a ha]

theorem Tt_eval (p : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ p = true) :
    (Tt p g).op.eval ((Tt p g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    simp only [Tt, GateOp.eval]
    exact all_filter p ρ ρ' h1 hp inputs
  | or =>
    by_cases hm : p ∈ inputs
    · simp only [Tt, hm, if_true, GateOp.eval]
      simp only [List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨p, hm, hp⟩, rfl⟩
    · simp only [Tt, hm, if_false, GateOp.eval, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h1 i (fun h => hm (h ▸ hi))
  | not =>
    cases inputs with
    | nil => simp [Tt, GateOp.eval]
    | cons a l =>
      by_cases ha : a = p
      · subst ha; simp [Tt, GateOp.eval, hp]
      · simp [Tt, GateOp.eval, ha, h1 a ha]
  | mod m => simp at hop
  | maj => simp at hop

theorem Tt_fan (p : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (Tt p g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (Tt p g).inputs.length ≤ 2 := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hl⟩ := h
  cases op with
  | and =>
    refine ⟨by simp [Tt], ?_⟩
    simp only [Tt, List.length_map]
    exact le_trans (List.length_filter_le _ _) hl
  | or =>
    by_cases hm : p ∈ inputs
    · simp [Tt, hm]
    · refine ⟨by simp [Tt, hm], ?_⟩
      simp only [Tt, hm, if_false, List.length_map]
      exact hl
  | not =>
    by_cases hm : inputs.head? = some p
    · simp [Tt, hm]
    · refine ⟨by simp [Tt, hm], ?_⟩
      simp only [Tt, hm, if_false, List.length_map]
      exact hl
  | mod m => simp at hop
  | maj => simp at hop

theorem Ts_fan (p t : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (Ts p t g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (Ts p t g).inputs.length ≤ 2 := by
  refine ⟨h.1, ?_⟩
  simp only [Ts, List.length_map]
  exact h.2

def FT (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def eff (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

def Red (n : ℕ) (G : List Gate) (j : ℕ) : Prop :=
  (∃ b : Bool, ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + j) false = b) ∨
  (∃ o, o < n + j ∧ ∀ x : Fin n → Bool,
    (W G (List.ofFn x)).getD (n + j) false = (W G (List.ofFn x)).getD o false)

theorem fin2 (n : ℕ) (h : (Fin n → Bool) → Bool) (G : List Gate) (out : ℕ) (hF : FT G)
    (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
    (j : ℕ) (hj : j < G.length) (T : Gate → Gate)
    (hTF : ∀ g ∈ G, (T g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (T g).inputs.length ≤ 2)
    (hT : ∀ (x : Fin n → Bool) (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g →
      ∀ ρ ρ' : ℕ → Bool,
      (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
      ρ (n + j) = (W G (List.ofFn x)).getD (n + j) false →
      (∀ i, i < n + j → ρ i = (W G (List.ofFn x)).getD i false) →
      (∀ i, i < n → ρ' i = (List.ofFn x).getD i false) →
      (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
      (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ))
    (ho : out = n + j → ∃ o, o < n + j ∧
      ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x) :
    ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
      (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
      ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
  have key : ∀ (x : Fin n → Bool) (m : ℕ),
      (W (del G j T) (List.ofFn x)).getD m false
        = (W G (List.ofFn x)).getD (up (n + j) m) false := by
    intro x
    exact sim G j T (List.ofFn x) n (by simp) hj (fun k g hk hg => hT x k g hk hg)
  have hlen := del_len G j T hj
  have hFT : FT (del G j T) := by
    intro g hg
    unfold del at hg
    rcases List.mem_append.mp hg with h1 | h1
    · exact hF g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
      exact hTF g0 (List.mem_of_mem_drop hg0)
  have hlow : ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
      (W (del G j T) (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
    intro x m hm
    rw [key x m, show up (n + j) m = m by simp only [up]; split_ifs <;> omega]
  by_cases hout : out = n + j
  · obtain ⟨o, hon, hox⟩ := ho hout
    exact ⟨del G j T, o, hFT, hlen, fun x => by rw [hlow x o hon]; exact hox x, hlow⟩
  · refine ⟨del G j T, sh (n + j) out, hFT, hlen, ?_, hlow⟩
    intro x
    rw [key x, ← hf x]
    congr 1
    simp only [up, sh]
    split_ifs <;> omega

theorem sdl (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y)
    (G : List Gate) (out : ℕ) (hF : FT G)
    (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
    (j : ℕ) (hj : j < G.length) (hR : Red n G j) :
    ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
      (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
      ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
  rcases hR with ⟨b, hb⟩ | ⟨o, hoj, hoe⟩
  · have ho : out = n + j → ∃ o, o < n + j ∧
        ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x := by
      intro hout
      exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      rw [← hf x, ← hf y, hout, hb x, hb y]
    cases b with
    | false =>
      refine fin2 n h G out hF hf j hj (Ts (n + j) (n + G.length))
        (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ho
      intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
      apply Ts_eval _ _ g ρ ρ' h1
      rw [h2, hb x]
      exact h4 _ (by omega)
    | true =>
      refine fin2 n h G out hF hf j hj (Tt (n + j))
        (fun g hg => Tt_fan _ g (hF g hg)) ?_ ho
      intro x k g _ hg ρ ρ' h1 h2 h5 h3 h4
      exact Tt_eval _ g (hF g (List.mem_of_getElem? hg)).1 ρ ρ' h1 (h2.trans (hb x))
  · refine fin2 n h G out hF hf j hj (Ts (n + j) o)
      (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ?_
    · intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
      apply Ts_eval _ _ g ρ ρ' h1
      have e : sh (n + j) o = o := by
        simp only [sh]; split_ifs <;> omega
      have a1 := h1 o (by omega)
      rw [e] at a1
      rw [a1, h5 o hoj, h2]
      exact (hoe x).symm
    · intro hout
      exact ⟨o, hoj, fun x => by rw [← hoe x, ← hout]; exact hf x⟩

theorem iter (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y) :
    ∀ (k : ℕ) (S : Finset ℕ), S.card = k → ∀ (G : List Gate) (out : ℕ), FT G →
      (∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x) →
      (∀ j ∈ S, j < G.length ∧ Red n G j) →
      ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + k = G.length ∧
        ∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x := by
  intro k
  induction k with
  | zero =>
    intro S _ G out hF hf _
    exact ⟨G, out, hF, rfl, hf⟩
  | succ k ih =>
    intro S hS G out hF hf hR
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hj, hRj⟩ := hR (S.max' hne) (S.max'_mem hne)
    obtain ⟨G1, out1, hF1, hl1, hf1, hlow⟩ := sdl n h hnc G out hF hf (S.max' hne) hj hRj
    have hR1 : ∀ i ∈ S.erase (S.max' hne), i < G1.length ∧ Red n G1 i := by
      intro i hi
      have hlt : i < S.max' hne := Finset.lt_max'_of_mem_erase_max' S hne hi
      obtain ⟨_, hRi⟩ := hR i (Finset.mem_of_mem_erase hi)
      refine ⟨by omega, ?_⟩
      rcases hRi with ⟨b, hb⟩ | ⟨o, ho, hoe⟩
      · exact Or.inl ⟨b, fun x => by rw [hlow x _ (by omega)]; exact hb x⟩
      · exact Or.inr ⟨o, ho, fun x => by
          rw [hlow x _ (by omega), hlow x _ (by omega)]; exact hoe x⟩
    obtain ⟨G2, out2, hF2, hl2, hf2⟩ := ih (S.erase (S.max' hne))
      (by rw [Finset.card_erase_of_mem (S.max'_mem hne)]; omega) G1 out1 hF1 hf1 hR1
    exact ⟨G2, out2, hF2, by omega, hf2⟩

theorem gl0 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g) :
    (∃ b : Bool, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = b) ∨
    (∃ w : ℕ, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = ρ w) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp [eff, GateOp.eval] at hq
      cases c with
      | false =>
        exact Or.inl ⟨false, fun ρ hρ => by
          rcases hq with rfl | rfl <;> simp [GateOp.eval, hρ]⟩
      | true =>
        rcases hq with rfl | rfl
        · exact Or.inr ⟨b, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
        · exact Or.inr ⟨a, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp at hlen
  | or =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp [eff, GateOp.eval] at hq
      cases c with
      | true =>
        exact Or.inl ⟨true, fun ρ hρ => by
          rcases hq with rfl | rfl <;> simp [GateOp.eval, hρ]⟩
      | false =>
        rcases hq with rfl | rfl
        · exact Or.inr ⟨b, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
        · exact Or.inr ⟨a, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
    · simp at hlen
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inl ⟨!c, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
  | mod m => simp at hop
  | maj => simp at hop

theorem gl (n : ℕ) (G : List Gate) (k : ℕ) (g : Gate) (hg : G[k]? = some g)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g)
    (hc : ∀ x : Fin n → Bool,
      (if q < n + k then (W G (List.ofFn x)).getD q false else false) = c) :
    Red n G k := by
  have key : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < n + k then (W G (List.ofFn x)).getD i false else false) := by
    intro x
    have e := W_spec G (List.ofFn x) k g hg
    rw [List.length_ofFn] at e
    exact e
  rcases gl0 g hop hlen q c hq with ⟨b, hb⟩ | ⟨w, hw⟩
  · exact Or.inl ⟨b, fun x => by
      rw [key x]
      exact hb (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)⟩
  · by_cases hwk : w < n + k
    · exact Or.inr ⟨w, hwk, fun x => by
        rw [key x,
          hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
        exact if_pos hwk⟩
    · exact Or.inl ⟨false, fun x => by
        rw [key x,
          hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
        exact if_neg hwk⟩

theorem gv0 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hnor : g.op ≠ GateOp.or) (q : ℕ) (hq : q ∈ eff g) :
    (g.op = GateOp.and ∧ ∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = true → ρ q = true) ∨
    (g.op = GateOp.not ∧ ∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = !ρ q) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    refine Or.inl ⟨rfl, ?_⟩
    intro ρ he
    have hq' : q ∈ inputs := List.mem_of_mem_take hq
    simp only [GateOp.eval] at he
    exact List.all_eq_true.mp he (ρ q) (List.mem_map.mpr ⟨q, hq', rfl⟩)
  | or => exact absurd rfl hnor
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [eff, GateOp.eval] at hq
    · simp [eff, GateOp.eval] at hq
      subst hq
      exact Or.inr ⟨rfl, fun ρ => by simp [GateOp.eval]⟩
  | mod m => simp at hop
  | maj => simp at hop

theorem gl2 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (v p : ℕ) (hvp : v ≠ p) (hv : v ∈ eff g) (hp : p ∈ eff g) :
    (∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = (ρ v && ρ p)) ∨
    (∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = (ρ v || ρ p)) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hv
    · simp [eff, GateOp.eval] at hv hp
      omega
    · simp [eff, GateOp.eval] at hv hp
      left
      intro ρ
      rcases hv with rfl | rfl <;> rcases hp with rfl | rfl
      · exact absurd rfl hvp
      · simp [GateOp.eval]
      · simp [GateOp.eval, Bool.and_comm]
      · exact absurd rfl hvp
    · simp at hlen
  | or =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [eff, GateOp.eval] at hv
    · simp [eff, GateOp.eval] at hv hp
      omega
    · simp [eff, GateOp.eval] at hv hp
      right
      intro ρ
      rcases hv with rfl | rfl <;> rcases hp with rfl | rfl
      · exact absurd rfl hvp
      · simp [GateOp.eval]
      · simp [GateOp.eval, Bool.or_comm]
      · exact absurd rfl hvp
    · simp at hlen
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [eff, GateOp.eval] at hv
    · simp [eff, GateOp.eval] at hv hp
      omega
  | mod m => simp at hop
  | maj => simp at hop

theorem Ts_dead (p t : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (hne : p ∉ eff g) (ρ ρ' : ℕ → Bool)
    (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) :
    (Ts p t g).op.eval ((Ts p t g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    have e : eff ⟨GateOp.and, inputs⟩ = inputs := List.take_of_length_le hlen
    rw [e] at hne
    simp only [Ts, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hip : i ≠ p := fun h => hne (h ▸ hi)
    simp only [Function.comp, hip, if_false]
    exact h1 i hip
  | or =>
    have e : eff ⟨GateOp.or, inputs⟩ = inputs := List.take_of_length_le hlen
    rw [e] at hne
    simp only [Ts, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hip : i ≠ p := fun h => hne (h ▸ hi)
    simp only [Function.comp, hip, if_false]
    exact h1 i hip
  | not =>
    rcases inputs with _ | ⟨a, l⟩
    · simp [Ts, GateOp.eval]
    · have ha : a ≠ p := by
        intro h
        apply hne
        simp [eff, GateOp.eval, h]
      simp [Ts, GateOp.eval, ha, h1 a ha]
  | mod m => simp at hop
  | maj => simp at hop

theorem pos_set (l : List Gate) (p : Gate → Bool) :
    ∃ S : Finset ℕ, S.card = (l.filter p).length ∧
      ∀ i ∈ S, ∃ g, l[i]? = some g ∧ p g = true := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨∅, by simp, by simp⟩
  | append_singleton l a ih =>
    obtain ⟨S, hS, hSp⟩ := ih
    have hlt : ∀ i ∈ S, i < l.length := by
      intro i hi
      obtain ⟨g, hg, _⟩ := hSp i hi
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hg
      cases hg
    by_cases hpa : p a = true
    · refine ⟨insert l.length S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun hm => by have := hlt _ hm; omega), hS]
        simp [List.filter_append, hpa]
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact ⟨a, by simp, hpa⟩
        · obtain ⟨g, hg, hpg⟩ := hSp i hi
          exact ⟨g, by rw [List.getElem?_append_left (hlt i hi)]; exact hg, hpg⟩
    · refine ⟨S, ?_, ?_⟩
      · rw [hS]; simp [List.filter_append, hpa]
      · intro i hi
        obtain ⟨g, hg, hpg⟩ := hSp i hi
        exact ⟨g, by rw [List.getElem?_append_left (hlt i hi)]; exact hg, hpg⟩

theorem eff_Rn (v B : ℕ) (g : Gate) :
    eff (Rn v B g) = (eff g).map fun i => if i = v then B else i := by
  simp [eff, Rn, List.map_take]


def rmI (v B i : ℕ) : ℕ := if i < v then i else if i = v then B else i - 1

def Rm (v B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rmI v B)⟩

theorem ins_getD (y : Fin 8 → Bool) (v : ℕ) (hv : v < 9) (m : ℕ) :
    ((List.ofFn y).insertIdx v false).getD m false =
      if m < v then (List.ofFn y).getD m false else if m = v then false
      else (List.ofFn y).getD (m - 1) false := by
  have hl : v ≤ (List.ofFn y).length := by simp; omega
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_insertIdx_of_lt h1]
  · subst h2; rw [List.getElem?_insertIdx_self, if_pos hl]; rfl
  · rw [List.getElem?_insertIdx_of_gt (by omega)]

theorem remove (G : List Gate) (v : ℕ) (hv : v < 9) (y : Fin 8 → Bool) :
    ∀ m, m ≠ v →
      (W (G.map (Rm v (8 + G.length))) (List.ofFn y)).getD (rmI v (8 + G.length) m) false =
        (W G ((List.ofFn y).insertIdx v false)).getD m false := by
  have hlen : ((List.ofFn y).insertIdx v false).length = 9 := by
    rw [List.length_insertIdx_of_le_length (by simp; omega)]; simp
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hmv
  rcases Nat.lt_or_ge m 9 with hm | hm
  · rw [W_inp _ _ m (by omega), ins_getD y v hv m]
    rw [W_inp _ _ _ (by simp only [rmI, List.length_ofFn]; split_ifs <;> omega)]
    simp only [rmI]
    split_ifs <;> first | rfl | omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = 9 + k := ⟨m - 9, by omega⟩
    rcases Nat.lt_or_ge k G.length with hk | hk
    · have hg : G[k]? = some G[k] := List.getElem?_eq_getElem hk
      have hg1 : (G.map (Rm v (8 + G.length)))[k]? = some (Rm v (8 + G.length) G[k]) := by
        rw [List.getElem?_map, hg]; rfl
      have e1 := W_spec (G.map (Rm v (8 + G.length))) (List.ofFn y) k _ hg1
      have e2 := W_spec G ((List.ofFn y).insertIdx v false) k _ hg
      rw [List.length_ofFn] at e1
      rw [hlen] at e2
      have hr : rmI v (8 + G.length) (9 + k) = 8 + k := by simp only [rmI]; split_ifs <;> omega
      rw [hr, e1, e2]
      simp only [Rm, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i = v
      · have h1 : ¬ (rmI v (8 + G.length) i < 8 + k) := by simp only [rmI]; split_ifs <;> omega
        rw [if_neg h1, if_pos (by omega), hi, W_inp _ _ v (by omega), ins_getD y v hv v]
        simp
      · by_cases h2 : i < 9 + k
        · rw [if_pos h2, if_pos (by simp only [rmI]; split_ifs <;> omega)]
          exact ih i h2 hi
        · rw [if_neg h2, if_neg (by simp only [rmI]; split_ifs <;> omega)]
    · have hr : rmI v (8 + G.length) (9 + k) = 8 + k := by simp only [rmI]; split_ifs <;> omega
      rw [hr, W_oob _ _ (8 + k) (by simp; omega), W_oob _ _ (9 + k) (by rw [hlen]; omega)]

theorem remove_eval (C : Circuit) (v : ℕ) (hv : v < 9) (y : Fin 8 → Bool) :
    (Circuit.mk (C.gates.map (Rm v (8 + C.gates.length)))
        (rmI v (8 + C.gates.length) C.output)).eval (List.ofFn y) =
      C.eval ((List.ofFn y).insertIdx v false) := by
  change (W _ _).getD _ false = (W _ _).getD _ false
  by_cases ho : C.output = v
  · have hr : rmI v (8 + C.gates.length) C.output = 8 + C.gates.length := by
      simp only [rmI]; split_ifs <;> omega
    rw [hr, W_oob _ _ _ (by simp), ho, W_inp _ _ v (by
      rw [List.length_insertIdx_of_le_length (by simp; omega)]; simp; omega), ins_getD y v hv v]
    simp
  · exact remove C.gates v hv y C.output ho


theorem two_readers (C : Circuit) (v : ℕ) (hv : v < 9) (hF : FT C.gates)
    (hnc : ∃ x y : Fin 8 → Bool, C.eval ((List.ofFn x).insertIdx v false) ≠
      C.eval ((List.ofFn y).insertIdx v false))
    (i j : ℕ) (hij : i ≠ j) (gi gj : Gate) (hgi : C.gates[i]? = some gi)
    (hgj : C.gates[j]? = some gj) (hvi : v ∈ eff gi) (hvj : v ∈ eff gj) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      circuitFun 8 D = fun y => C.eval ((List.ofFn y).insertIdx v false) := by
  obtain ⟨B, hB⟩ : ∃ B, B = 8 + C.gates.length := ⟨_, rfl⟩
  have hf1 : ∀ y : Fin 8 → Bool, (W (C.gates.map (Rm v B)) (List.ofFn y)).getD
      (rmI v B C.output) false = C.eval ((List.ofFn y).insertIdx v false) := by
    intro y; rw [hB]; exact remove_eval C v hv y
  have hF1 : FT (C.gates.map (Rm v B)) := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := hF g0 hg0
    exact ⟨h0.1, by simp only [Rm, List.length_map]; exact h0.2⟩
  have hklt : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → k < C.gates.length := by
    intro k g hg
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hA : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → v ∈ eff g →
      k < (C.gates.map (Rm v B)).length ∧ Red 8 (C.gates.map (Rm v B)) k := by
    intro k g hg hvg
    have hk := hklt k g hg
    have hm := hF g (List.mem_of_getElem? hg)
    refine ⟨by simpa using hk, gl 8 _ k (Rm v B g) (by rw [List.getElem?_map, hg]; rfl) hm.1
      (by simp only [Rm, List.length_map]; exact hm.2) B false ?_ ?_⟩
    · have : eff (Rm v B g) = (eff g).map (rmI v B) := by simp [eff, Rm, List.map_take]
      rw [this]
      exact List.mem_map.mpr ⟨v, hvg, by simp [rmI]⟩
    · intro x
      exact if_neg (by omega)
  obtain ⟨G', out', hF', hl', hf'⟩ :=
    iter 8 (fun y => C.eval ((List.ofFn y).insertIdx v false)) hnc 2 {i, j}
      (Finset.card_pair hij) _ _ hF1 hf1 (by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hA k gi hgi hvi
        · rw [Finset.mem_singleton] at hk; subst hk; exact hA k gj hgj hvj)
  refine ⟨⟨G', out'⟩, hF', ?_, funext fun y => hf' y⟩
  change G'.length + 2 ≤ C.gates.length
  simp at hl'; omega


theorem eval_eff (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (ρ ρ' : ℕ → Bool) (h : ∀ i ∈ eff g, ρ i = ρ' i) :
    g.op.eval (g.inputs.map ρ) = g.op.eval (g.inputs.map ρ') := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · rfl
  · cases op <;> simp_all [eff, GateOp.eval]
  · cases op <;> simp_all [eff, GateOp.eval]
  · simp at hlen

theorem agree (G : List Gate) (hF : FT G) (x x' : List Bool) (hx : x.length = 9)
    (hx' : x'.length = 9) (Ex : ℕ → Prop)
    (h1 : ∀ m, m < 9 → ¬ Ex m → x.getD m false = x'.getD m false)
    (h2 : ∀ (k : ℕ) (g : Gate), G[k]? = some g → ¬ Ex (9 + k) →
      (∀ i ∈ eff g, i < 9 + k → ¬ Ex i) ∨
        (W G x).getD (9 + k) false = (W G x').getD (9 + k) false) :
    ∀ m, ¬ Ex m → (W G x).getD m false = (W G x').getD m false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  rcases Nat.lt_or_ge m 9 with hm9 | hm9
  · rw [W_inp _ _ m (by omega), W_inp _ _ m (by omega)]; exact h1 m hm9 hm
  · obtain ⟨k, rfl⟩ : ∃ k, m = 9 + k := ⟨m - 9, by omega⟩
    rcases Nat.lt_or_ge k G.length with hk | hk
    · have hg : G[k]? = some G[k] := List.getElem?_eq_getElem hk
      rcases h2 k G[k] hg hm with hr | hr
      · have e1 := W_spec G x k _ hg
        have e2 := W_spec G x' k _ hg
        rw [hx] at e1
        rw [hx'] at e2
        rw [e1, e2]
        have hgF := hF G[k] (List.getElem_mem hk)
        apply eval_eff _ hgF.1 hgF.2
        intro i hi
        by_cases hik : i < 9 + k
        · rw [if_pos hik, if_pos hik]; exact ih i hik (hr i hi hik)
        · rw [if_neg hik, if_neg hik]
      · exact hr
    · rw [W_oob _ _ _ (by omega), W_oob _ _ _ (by omega)]


theorem ins_getD' (y : Fin 8 → Bool) (v : ℕ) (hv : v < 9) (b : Bool) (m : ℕ) :
    ((List.ofFn y).insertIdx v b).getD m false =
      if m < v then (List.ofFn y).getD m false else if m = v then b
      else (List.ofFn y).getD (m - 1) false := by
  have hl : v ≤ (List.ofFn y).length := by simp; omega
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_insertIdx_of_lt h1]
  · subst h2; rw [List.getElem?_insertIdx_self, if_pos hl]; rfl
  · rw [List.getElem?_insertIdx_of_gt (by omega)]

theorem ins_len (y : Fin 8 → Bool) (v : ℕ) (hv : v < 9) (b : Bool) :
    ((List.ofFn y).insertIdx v b).length = 9 := by
  rw [List.length_insertIdx_of_le_length (by simp; omega)]; simp

theorem red_reader (C : Circuit) (v : ℕ) (hF : FT C.gates) (k : ℕ) (g : Gate)
    (hg : C.gates[k]? = some g) (hvg : v ∈ eff g) :
    k < (C.gates.map (Rm v (8 + C.gates.length))).length ∧
      Red 8 (C.gates.map (Rm v (8 + C.gates.length))) k := by
  have hk : k < C.gates.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hm := hF g (List.mem_of_getElem? hg)
  refine ⟨by simpa using hk, gl 8 _ k (Rm v (8 + C.gates.length) g)
    (by rw [List.getElem?_map, hg]; rfl) hm.1
    (by simp only [Rm, List.length_map]; exact hm.2) (8 + C.gates.length) false ?_ ?_⟩
  · have : eff (Rm v (8 + C.gates.length) g) = (eff g).map (rmI v (8 + C.gates.length)) := by
      simp [eff, Rm, List.map_take]
    rw [this]
    exact List.mem_map.mpr ⟨v, hvg, by simp [rmI]⟩
  · intro x
    exact if_neg (by omega)

theorem red_later (C : Circuit) (v : ℕ) (hv : v < 9) (hF : FT C.gates) (k j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hkj : k < j) (hr : 9 + k ∈ eff g) (c : Bool)
    (hc : ∀ y : Fin 8 → Bool,
      (W C.gates ((List.ofFn y).insertIdx v false)).getD (9 + k) false = c) :
    j < (C.gates.map (Rm v (8 + C.gates.length))).length ∧
      Red 8 (C.gates.map (Rm v (8 + C.gates.length))) j := by
  have hk : j < C.gates.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hm := hF g (List.mem_of_getElem? hg)
  refine ⟨by simpa using hk, gl 8 _ j (Rm v (8 + C.gates.length) g)
    (by rw [List.getElem?_map, hg]; rfl) hm.1
    (by simp only [Rm, List.length_map]; exact hm.2) (8 + k) c ?_ ?_⟩
  · have : eff (Rm v (8 + C.gates.length) g) = (eff g).map (rmI v (8 + C.gates.length)) := by
      simp [eff, Rm, List.map_take]
    rw [this]
    exact List.mem_map.mpr ⟨9 + k, hr, by simp only [rmI]; split_ifs <;> omega⟩
  · intro x
    rw [if_pos (by omega)]
    have e := remove C.gates v hv x (9 + k) (by omega)
    have hr2 : rmI v (8 + C.gates.length) (9 + k) = 8 + k := by
      simp only [rmI]; split_ifs <;> omega
    rw [hr2] at e
    rw [e]; exact hc x

theorem two_red (C : Circuit) (v : ℕ) (hv : v < 9) (hF : FT C.gates)
    (hnc : ∃ x y : Fin 8 → Bool, C.eval ((List.ofFn x).insertIdx v false) ≠
      C.eval ((List.ofFn y).insertIdx v false))
    (i j : ℕ) (hij : i ≠ j)
    (hi : i < (C.gates.map (Rm v (8 + C.gates.length))).length ∧
      Red 8 (C.gates.map (Rm v (8 + C.gates.length))) i)
    (hj : j < (C.gates.map (Rm v (8 + C.gates.length))).length ∧
      Red 8 (C.gates.map (Rm v (8 + C.gates.length))) j) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      circuitFun 8 D = fun y => C.eval ((List.ofFn y).insertIdx v false) := by
  have hf1 : ∀ y : Fin 8 → Bool, (W (C.gates.map (Rm v (8 + C.gates.length))) (List.ofFn y)).getD
      (rmI v (8 + C.gates.length) C.output) false = C.eval ((List.ofFn y).insertIdx v false) := by
    intro y; exact remove_eval C v hv y
  have hF1 : FT (C.gates.map (Rm v (8 + C.gates.length))) := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := hF g0 hg0
    exact ⟨h0.1, by simp only [Rm, List.length_map]; exact h0.2⟩
  obtain ⟨G', out', hF', hl', hf'⟩ :=
    iter 8 (fun y => C.eval ((List.ofFn y).insertIdx v false)) hnc 2 {i, j}
      (Finset.card_pair hij) _ _ hF1 hf1 (by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hi
        · rw [Finset.mem_singleton] at hk; subst hk; exact hj)
  refine ⟨⟨G', out'⟩, hF', ?_, funext fun y => hf' y⟩
  change G'.length + 2 ≤ C.gates.length
  simp at hl'; omega

theorem rd_iff (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (v : ℕ) :
    (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains v = true ↔
      v ∈ eff g := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · cases op <;> simp_all [eff, GateOp.eval]
  · cases op <;> simp_all [eff, GateOp.eval]
  · cases op <;> simp_all [eff, GateOp.eval]
  · simp at hlen

theorem shape (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (v : ℕ) (hv : v ∈ eff g) :
    (g.op = GateOp.or ∧ ∃ a, a ≠ v ∧ (g.inputs = [v, a] ∨ g.inputs = [a, v])) ∨
      ∃ c : Bool, ∀ ρ : ℕ → Bool, ρ v = false → g.op.eval (g.inputs.map ρ) = c := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp [eff] at hv
  · cases op <;> simp_all [eff, GateOp.eval]
  · rcases op with _ | _ | _ | _ | _ <;> simp at hop
    · right; refine ⟨false, fun ρ hρ => ?_⟩
      simp [eff, GateOp.eval] at hv ⊢
      rcases hv with rfl | rfl <;> simp [hρ]
    · by_cases hab : a = b
      · subst hab
        simp [eff, GateOp.eval] at hv
        subst hv
        right; exact ⟨false, fun ρ hρ => by simp [GateOp.eval, hρ]⟩
      · left
        simp [eff, GateOp.eval] at hv
        rcases hv with rfl | rfl
        · exact ⟨rfl, b, Ne.symm hab, Or.inl rfl⟩
        · exact ⟨rfl, a, hab, Or.inr rfl⟩
    · right; refine ⟨true, fun ρ hρ => ?_⟩
      simp [eff, GateOp.eval] at hv ⊢
      subst hv; simp [hρ]
  · simp at hlen


theorem main (C : Circuit) (v : Fin 9) (hF : FT C.gates)
    (hnc : ∃ x y : Fin 8 → Bool, C.eval ((List.ofFn x).insertIdx v.val false) ≠
      C.eval ((List.ofFn y).insertIdx v.val false))
    (hdep : ∀ x7 : Fin 9, x7 ≠ v → ∃ x9 : Fin 8 → Bool,
      C.eval ((List.ofFn x9).insertIdx v.val false) ≠ C.eval ((List.ofFn x9).insertIdx v.val true) ∧
      ((List.ofFn x9).insertIdx v.val false).getD x7.val false = true) :
    (∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      circuitFun 8 D = fun y => C.eval ((List.ofFn y).insertIdx v.val false)) ∨
    ∃ (g : Fin C.size) (w : ℕ), 9 ≤ w ∧ w < 9 + g.val ∧ (C.gates.get g).op = GateOp.or ∧
      ((C.gates.get g).inputs = [v.val, w] ∨ (C.gates.get g).inputs = [w, v.val]) ∧
      ∀ h : Fin C.size, (if (C.gates.get h).op.eval [false, false] = true then
        (C.gates.get h).inputs.take 1 else (C.gates.get h).inputs).contains v.val = true → h = g := by
  have hv : v.val < 9 := v.isLt
  have noflip : (∀ y : Fin 8 → Bool, C.eval ((List.ofFn y).insertIdx v.val false) =
      C.eval ((List.ofFn y).insertIdx v.val true)) → False := by
    intro h
    obtain ⟨y, hy, _⟩ := hdep ⟨if v.val = 0 then 1 else 0, by split_ifs <;> omega⟩ (by
      intro h'
      have := congrArg Fin.val h'
      simp only at this
      split_ifs at this <;> omega)
    exact hy (h y)
  have noconst : ∀ c : Bool, (∀ y : Fin 8 → Bool,
      C.eval ((List.ofFn y).insertIdx v.val false) = c) → False := by
    intro c h
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((h x).trans (h y).symm)
  have h1 : ∀ (y : Fin 8 → Bool) (m : ℕ), m < 9 → m ≠ v.val →
      ((List.ofFn y).insertIdx v.val false).getD m false =
        ((List.ofFn y).insertIdx v.val true).getD m false := by
    intro y m _ hm
    rw [ins_getD' y v.val hv, ins_getD' y v.val hv]
    split_ifs <;> first | rfl | omega
  have outv : C.output = v.val → False := by
    intro ho
    apply noconst false
    intro y'
    change (W C.gates _).getD C.output false = false
    rw [ho, W_inp _ _ _ (by rw [ins_len _ _ hv]; omega), ins_getD' y' v.val hv]
    simp
  have hglt : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → k < C.gates.length := by
    intro k g hg
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  by_cases hA : ∃ (i j : ℕ) (gi gj : Gate), i ≠ j ∧ C.gates[i]? = some gi ∧
      C.gates[j]? = some gj ∧ v.val ∈ eff gi ∧ v.val ∈ eff gj
  · obtain ⟨i, j, gi, gj, hij, hgi, hgj, hvi, hvj⟩ := hA
    exact Or.inl (two_red C v.val hv hF hnc i j hij (red_reader C v.val hF i gi hgi hvi)
      (red_reader C v.val hF j gj hgj hvj))
  have huniq : ∀ (i j : ℕ) (gi gj : Gate), C.gates[i]? = some gi → C.gates[j]? = some gj →
      v.val ∈ eff gi → v.val ∈ eff gj → i = j := by
    intro i j gi gj hgi hgj hvi hvj
    by_contra hij
    exact hA ⟨i, j, gi, gj, hij, hgi, hgj, hvi, hvj⟩
  by_cases hB : ∃ (k : ℕ) (g : Gate), C.gates[k]? = some g ∧ v.val ∈ eff g
  swap
  · exfalso
    apply noflip
    intro y
    change (W C.gates _).getD C.output false = (W C.gates _).getD C.output false
    refine agree C.gates hF _ _ (ins_len y v.val hv false) (ins_len y v.val hv true)
      (fun m => m = v.val) (fun m hm hmv => h1 y m hm hmv) ?_ C.output outv
    intro k g hg _
    left
    intro i hi _ hiv
    subst hiv
    exact hB ⟨k, g, hg, hi⟩
  obtain ⟨k, g, hg, hvg⟩ := hB
  have hk := hglt k g hg
  have hgF := hF g (List.mem_of_getElem? hg)
  have spec : ∀ (b : Bool) (y : Fin 8 → Bool),
      (W C.gates ((List.ofFn y).insertIdx v.val b)).getD (9 + k) false =
        g.op.eval (g.inputs.map fun i => if i < 9 + k then
          (W C.gates ((List.ofFn y).insertIdx v.val b)).getD i false else false) := by
    intro b y
    have e := W_spec C.gates ((List.ofFn y).insertIdx v.val b) k g hg
    rw [ins_len _ _ hv] at e
    exact e
  have wv : ∀ y : Fin 8 → Bool,
      (W C.gates ((List.ofFn y).insertIdx v.val false)).getD v.val false = false := by
    intro y
    rw [W_inp _ _ _ (by rw [ins_len _ _ hv]; omega), ins_getD' y v.val hv]
    simp
  have constcase : ∀ c : Bool, (∀ y : Fin 8 → Bool,
      (W C.gates ((List.ofFn y).insertIdx v.val false)).getD (9 + k) false = c) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
        circuitFun 8 D = fun y => C.eval ((List.ofFn y).insertIdx v.val false) := by
    intro c hc
    by_cases hL : ∃ (j : ℕ) (g' : Gate), C.gates[j]? = some g' ∧ k < j ∧ 9 + k ∈ eff g'
    · obtain ⟨j, g', hg', hkj, hr⟩ := hL
      exact two_red C v.val hv hF hnc k j (by omega) (red_reader C v.val hF k g hg hvg)
        (red_later C v.val hv hF k j g' hg' hkj hr c hc)
    · exfalso
      apply noflip
      intro y
      change (W C.gates _).getD C.output false = (W C.gates _).getD C.output false
      by_cases ho2 : C.output = 9 + k
      · exfalso
        apply noconst c
        intro y'
        change (W C.gates _).getD C.output false = c
        rw [ho2]
        exact hc y'
      refine agree C.gates hF _ _ (ins_len y v.val hv false) (ins_len y v.val hv true)
        (fun m => m = v.val ∨ m = 9 + k) (fun m hm hmv => h1 y m hm (fun h => hmv (Or.inl h)))
        ?_ C.output (by rintro (h | h) <;> [exact outv h; exact ho2 h])
      intro k' g' hg' hne
      left
      intro i hi hik' hEx
      rcases hEx with rfl | rfl
      · have := huniq k' k g' g hg' hg hi hvg
        subst this
        exact hne (Or.inr rfl)
      · rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
        · exact hL ⟨k', g', hg', hlt, hi⟩
        · subst heq; exact hne (Or.inr rfl)
        · omega
  have hget : C.gates.get ⟨k, hk⟩ = g := by
    have := List.getElem?_eq_getElem hk
    rw [hg] at this
    exact (Option.some.inj this).symm
  rcases shape g hgF.1 hgF.2 v.val hvg with ⟨hor, a, hav, hin⟩ | ⟨c, hc⟩
  · rcases Nat.lt_or_ge a 9 with ha9 | ha9
    · exfalso
      obtain ⟨y, hy, hya⟩ := hdep ⟨a, ha9⟩ (fun h => hav (congrArg Fin.val h))
      apply hy
      change (W C.gates _).getD C.output false = (W C.gates _).getD C.output false
      refine agree C.gates hF _ _ (ins_len y v.val hv false) (ins_len y v.val hv true)
        (fun m => m = v.val) (fun m hm hmv => h1 y m hm hmv) ?_ C.output outv
      intro k' g' hg' _
      by_cases hkk : k' = k
      · subst hkk
        right
        have hgg : g' = g := by rw [hg] at hg'; exact (Option.some.inj hg').symm
        subst hgg
        rw [spec false y, spec true y]
        have ha1 : (W C.gates ((List.ofFn y).insertIdx v.val false)).getD a false = true := by
          rw [W_inp _ _ _ (by rw [ins_len _ _ hv]; omega)]; exact hya
        have ha2 : (W C.gates ((List.ofFn y).insertIdx v.val true)).getD a false = true := by
          rw [W_inp _ _ _ (by rw [ins_len _ _ hv]; omega), ← h1 y a ha9 hav]; exact hya
        have hlt : a < 9 + k' := by omega
        rw [hor]
        rcases hin with h | h <;> rw [h] <;> simp only [List.map_cons, List.map_nil, GateOp.eval,
          List.any_cons, List.any_nil, if_pos hlt, ha1, ha2, id, Bool.or_true, Bool.true_or,
          Bool.or_false]
      · left
        intro i hi _ hiv
        subst hiv
        exact hkk (huniq k' k g' g hg' hg hi hvg)
    · rcases Nat.lt_or_ge a (9 + k) with hak | hak
      · right
        refine ⟨⟨k, by exact hk⟩, a, ha9, hak, ?_, ?_, ?_⟩
        · show (C.gates.get ⟨k, hk⟩).op = _
          rw [hget]; exact hor
        · show (C.gates.get ⟨k, hk⟩).inputs = _ ∨ (C.gates.get ⟨k, hk⟩).inputs = _
          rw [hget]; exact hin
        · intro h hr
          have hmem : C.gates.get h ∈ C.gates := List.get_mem _ _
          have hh := (rd_iff _ (hF _ hmem).1 (hF _ hmem).2 v.val).mp hr
          have hgh : C.gates[h.val]? = some (C.gates.get h) := by
            rw [List.getElem?_eq_getElem h.isLt]; rfl
          exact Fin.ext (huniq h.val k _ g hgh hg hh hvg)
      · left
        apply constcase false
        intro y
        rw [spec false y, hor]
        have hna : ¬ a < 9 + k := by omega
        have hvk : v.val < 9 + k := by omega
        rcases hin with h | h <;> rw [h] <;> simp only [List.map_cons, List.map_nil, GateOp.eval,
          List.any_cons, List.any_nil, if_pos hvk, if_neg hna, wv y, id, Bool.or_false,
          Bool.false_or]
  · left
    apply constcase c
    intro y
    rw [spec false y]
    apply hc
    rw [if_pos (by omega), wv y]

end PEqualNP.Outside.L_meta_2822

theorem PEqualNP.Outside.L_meta_2822 : have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  exact fun C v hmin hnc hdep => PEqualNP.Outside.L_meta_2822.main C v hmin.1 hnc hdep
