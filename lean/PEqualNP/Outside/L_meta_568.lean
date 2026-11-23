import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace L568

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

theorem deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem fanInTwo_del (G : List Gate) (o : ℕ) (t p r o' : ℕ) (h : FanInTwo ⟨G, o⟩) :
    FanInTwo ⟨del G t p r, o'⟩ := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [renG] using h2⟩

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

theorem del_getElem_lt (G : List Gate) (t p r t' : ℕ) (h : t' < t) (ht : t < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r ht]; omega) = G[t']'(by omega) := by
  simp only [del]
  rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]

theorem del_getElem_ge (G : List Gate) (t p r t' : ℕ) (h : t ≤ t') (ht : t' + 1 < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r (by omega)]; omega) = renG p r (G[t' + 1]'ht) := by
  simp only [del]
  rw [List.getElem_append_right (by simp [List.length_take]; omega), List.getElem_map, List.getElem_drop]
  congr 2
  simp [List.length_take]
  omega

def delMany (m : ℕ) : List Gate → ℕ → List (ℕ × ℕ) → List Gate × ℕ
  | G, o, [] => (G, o)
  | G, o, d :: rest => delMany m (del G d.1 (m + d.1) d.2) (ren (m + d.1) d.2 o) rest

def Just (m : ℕ) (G : List Gate) (o : ℕ) (ds : List (ℕ × ℕ)) (d : ℕ × ℕ) : Prop :=
  (∀ x : List Bool, x.length = m →
      (G.foldl step x).getD (m + d.1) false = (G.foldl step x).getD d.2 false) ∨
  ((∀ t, (ht : t < G.length) → d.1 < t → (∀ d' ∈ ds, t ≠ d'.1) → m + d.1 ∉ deps (G[t])) ∧
    o ≠ m + d.1 ∧ ∀ d' ∈ ds, d' ≠ d → d'.2 ≠ m + d.1)

theorem delMany_spec (m : ℕ) : ∀ (ds : List (ℕ × ℕ)) (G : List Gate) (o : ℕ),
    ds.Pairwise (fun a b => b.1 < a.1) →
    (∀ d ∈ ds, d.1 < G.length) →
    (∀ d ∈ ds, d.2 < m + d.1 ∨ m + G.length ≤ d.2) →
    (∀ d ∈ ds, Just m G o ds d) →
    (delMany m G o ds).1.length = G.length - ds.length ∧
    (∀ o₀, FanInTwo ⟨G, o₀⟩ → FanInTwo ⟨(delMany m G o ds).1, (delMany m G o ds).2⟩) ∧
    (∀ x : List Bool, x.length = m →
      Circuit.eval ⟨(delMany m G o ds).1, (delMany m G o ds).2⟩ x = Circuit.eval ⟨G, o⟩ x) := by
  intro ds
  induction ds with
  | nil =>
    intro G o _ _ _ _
    exact ⟨by simp [delMany], fun o₀ h => by simpa [delMany, FanInTwo] using h, fun x _ => rfl⟩
  | cons d rest ih =>
    intro G o hsort hlt hval hjust
    obtain ⟨t, r⟩ := d
    rw [List.pairwise_cons] at hsort
    obtain ⟨hgt, hsort'⟩ := hsort
    simp only at hgt
    have ht : t < G.length := hlt (t, r) (by simp)
    have hr : r < m + t ∨ m + G.length ≤ r := hval (t, r) (by simp)
    have hjt := hjust (t, r) (by simp)
    have hhead : ∀ x : List Bool, x.length = m →
        (∀ g ∈ G.drop (t + 1), m + t ∈ deps g →
          (G.foldl step x).getD (m + t) false = (G.foldl step x).getD r false) ∧
        (o = m + t → (G.foldl step x).getD (m + t) false = (G.foldl step x).getD r false) := by
      intro x hx
      rcases hjt with hv | ⟨hun, ho, _⟩
      · exact ⟨fun _ _ _ => hv x hx, fun _ => hv x hx⟩
      · refine ⟨fun g hg hmem => ?_, fun h => absurd h ho⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
        rw [List.getElem_drop] at hmem
        exact absurd hmem (hun (t + 1 + i) (by simp at hi; omega) (by omega)
          (fun d' hd' => by
            simp only [List.mem_cons] at hd'
            rcases hd' with rfl | hd'
            · simp; omega
            · have := hgt d' hd'; omega))
    have hW' : ∀ x : List Bool, x.length = m →
        (del G t (m + t) r).foldl step x = (G.foldl step x).eraseIdx (m + t) := by
      intro x hx
      have := del_foldl G x t r ht (by rw [hx]; exact hr) (by rw [hx]; exact (hhead x hx).1)
      rwa [hx] at this
    have hlen' : (del G t (m + t) r).length = G.length - 1 := del_length G t (m + t) r ht
    have hlt' : ∀ d' ∈ rest, d'.1 < (del G t (m + t) r).length := by
      intro d' hd'; rw [hlen']; have := hgt d' hd'; omega
    have hval' : ∀ d' ∈ rest, d'.2 < m + d'.1 ∨ m + (del G t (m + t) r).length ≤ d'.2 := by
      intro d' hd'; rw [hlen']
      rcases hval d' (List.mem_cons_of_mem _ hd') with h | h
      · exact Or.inl h
      · right; omega
    have hjust' : ∀ d' ∈ rest, Just m (del G t (m + t) r) (ren (m + t) r o) rest d' := by
      intro d' hd'
      have hd't : d'.1 < t := hgt d' hd'
      rcases hjust d' (List.mem_cons_of_mem _ hd') with hv | ⟨hun, ho, hrep⟩
      · left
        intro x hx
        rw [hW' x hx, getD_eraseIdx_lt _ _ _ (by omega)]
        rcases hval d' (List.mem_cons_of_mem _ hd') with h | h
        · rw [getD_eraseIdx_lt ((G.foldl step x)) (m + t) d'.2 (by omega)]; exact hv x hx
        · rw [getD_of_length_le ((G.foldl step x).eraseIdx (m + t)) d'.2
            (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
            hv x hx, getD_of_length_le _ _ (by rw [foldl_step_length]; omega)]
      · right
        have hrt : r ≠ m + d'.1 := hrep (t, r) (by simp) (by intro h; rw [← h] at hd't; simp at hd't)
        refine ⟨fun t' ht' hd't' hnot => ?_, ?_, fun d'' hd'' hne => hrep d'' (List.mem_cons_of_mem _ hd'') hne⟩
        · by_cases htt : t' < t
          · rw [del_getElem_lt G t (m + t) r t' htt ht]
            exact hun t' (by omega) hd't' (fun d'' hd'' => by
              simp only [List.mem_cons] at hd''
              rcases hd'' with rfl | hd''
              · simp; omega
              · exact hnot d'' hd'')
          · have htt' : t ≤ t' := by omega
            rw [del_getElem_ge G t (m + t) r t' htt' (by rw [hlen'] at ht'; omega), deps_renG]
            intro hmem
            obtain ⟨i, hi, hreni⟩ := List.mem_map.1 hmem
            have hi' : m + d'.1 ∉ deps (G[t' + 1]'(by rw [hlen'] at ht'; omega)) :=
              hun (t' + 1) (by rw [hlen'] at ht'; omega) (by omega) (fun d'' hd'' => by
                simp only [List.mem_cons] at hd''
                rcases hd'' with rfl | hd''
                · simp; omega
                · have := hgt d'' hd''; omega)
            unfold ren at hreni
            split_ifs at hreni with h1 h2
            · exact hi' (hreni ▸ hi)
            · exact hrt hreni
            · omega
        · unfold ren
          split_ifs with h1 h2
          · exact ho
          · exact hrt
          · omega
    obtain ⟨ih1, ih2, ih3⟩ := ih (del G t (m + t) r) (ren (m + t) r o) hsort' hlt' hval' hjust'
    refine ⟨?_, fun o₀ h => ih2 _ (fanInTwo_del G o₀ t (m + t) r o₀ h), fun x hx => ?_⟩
    · simp only [delMany]
      rw [ih1, hlen']
      simp
      omega
    · simp only [delMany]
      rw [ih3 x hx]
      have := del_eval G o x t r ht (by rw [hx]; exact hr) (by rw [hx]; exact (hhead x hx).1)
        (by rw [hx]; exact (hhead x hx).2)
      rwa [hx] at this

theorem smaller (m : ℕ) (G : List Gate) (o : ℕ) (ds : List (ℕ × ℕ))
    (hsort : ds.Pairwise (fun a b => b.1 < a.1)) (hlt : ∀ d ∈ ds, d.1 < G.length)
    (hval : ∀ d ∈ ds, d.2 < m + d.1 ∨ m + G.length ≤ d.2) (hjust : ∀ d ∈ ds, Just m G o ds d)
    (hfan : FanInTwo ⟨G, o⟩) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = G.length - ds.length ∧
      ∀ x : List Bool, x.length = m → D.eval x = Circuit.eval ⟨G, o⟩ x := by
  obtain ⟨h1, h2, h3⟩ := delMany_spec m ds G o hsort hlt hval hjust
  exact ⟨⟨(delMany m G o ds).1, (delMany m G o ds).2⟩, h2 o hfan, h1, h3⟩

theorem just_congr (m : ℕ) (G : List Gate) (o : ℕ) (ds ds' : List (ℕ × ℕ))
    (h : ∀ d, d ∈ ds ↔ d ∈ ds') (d : ℕ × ℕ) (hj : Just m G o ds d) : Just m G o ds' d := by
  unfold Just at hj ⊢
  rcases hj with hj | ⟨h1, h2, h3⟩
  · exact Or.inl hj
  · exact Or.inr ⟨fun t ht hdt hnot => h1 t ht hdt (fun d' hd' => hnot d' ((h d').1 hd')),
      h2, fun d' hd' hne => h3 d' ((h d').2 hd') hne⟩

def V (G : List Gate) (x : List Bool) (i : ℕ) : Bool := (G.foldl step x).getD i false

def IsConstW (m : ℕ) (G : List Gate) (p : ℕ) : Prop :=
  ∃ c : Bool, ∀ x : List Bool, x.length = m → V G x p = c

def IsCopy (m : ℕ) (G : List Gate) (t : ℕ) : Prop :=
  ∃ b, b < m + t ∧ ∀ x : List Bool, x.length = m → V G x (m + t) = V G x b

def Triv (m : ℕ) (G : List Gate) (t : ℕ) : Prop := IsConstW m G (m + t) ∨ IsCopy m G t

theorem batch (m : ℕ) (G : List Gate) (o : ℕ) (hfan : FanInTwo ⟨G, o⟩)
    (U Q : ℕ → Prop) [∀ t, Decidable (U t ∨ Q t)] (ρ : ℕ → ℕ)
    (hUo : ∀ t, t < G.length → U t → o ≠ m + t)
    (hUr : ∀ t t' (ht' : t' < G.length), U t → t < t' → m + t ∈ deps (G[t']) → U t' ∨ Q t')
    (hQU : ∀ t, Q t → ¬ U t)
    (hQlt : ∀ t, Q t → ρ t < m + t)
    (hQv : ∀ t, Q t → ∀ x : List Bool, x.length = m → V G x (m + t) = V G x (ρ t))
    (hQne : ∀ t t'', Q t → t'' < G.length → U t'' → ρ t ≠ m + t'') :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + ((List.range G.length).filter (fun t => decide (U t ∨ Q t))).length = G.length ∧
      ∀ x : List Bool, x.length = m → D.eval x = Circuit.eval ⟨G, o⟩ x := by
  classical
  let repl : ℕ → ℕ := fun t => if U t then m + G.length else ρ t
  let ps := (List.range G.length).reverse.filter (fun t => decide (U t ∨ Q t))
  let ds := ps.map (fun t => (t, repl t))
  have hmem : ∀ d ∈ ds, d.1 < G.length ∧ (U d.1 ∨ Q d.1) ∧ d.2 = repl d.1 := by
    intro d hd
    simp only [ds, ps, List.mem_map, List.mem_filter, List.mem_reverse, List.mem_range,
      decide_eq_true_eq] at hd
    obtain ⟨t, ⟨ht, hu⟩, rfl⟩ := hd
    exact ⟨ht, hu, rfl⟩
  have hmem' : ∀ t, t < G.length → (U t ∨ Q t) → (t, repl t) ∈ ds := by
    intro t ht hu
    simp only [ds, ps, List.mem_map, List.mem_filter, List.mem_reverse, List.mem_range,
      decide_eq_true_eq]
    exact ⟨t, ⟨ht, hu⟩, rfl⟩
  have hsort : ds.Pairwise (fun a b => b.1 < a.1) := by
    simp only [ds, List.pairwise_map]
    apply List.Pairwise.filter
    rw [List.pairwise_reverse]
    exact List.pairwise_lt_range
  have hlt : ∀ d ∈ ds, d.1 < G.length := fun d hd => (hmem d hd).1
  have hval : ∀ d ∈ ds, d.2 < m + d.1 ∨ m + G.length ≤ d.2 := by
    intro d hd
    obtain ⟨_, hu, h2⟩ := hmem d hd
    rw [h2]
    by_cases hU : U d.1
    · right; simp [repl, hU]
    · left
      have hQ : Q d.1 := hu.resolve_left hU
      simp only [repl, hU, if_false]
      exact hQlt _ hQ
  have hjust : ∀ d ∈ ds, Just m G o ds d := by
    intro d hd
    obtain ⟨h1, hu, h2⟩ := hmem d hd
    by_cases hU : U d.1
    · right
      refine ⟨?_, hUo _ h1 hU, ?_⟩
      · intro t' ht' hlt' hnot hdep
        have := hUr d.1 t' ht' hU hlt' hdep
        exact hnot (t', repl t') (hmem' t' ht' this) rfl
      · intro d' hd' _
        obtain ⟨_, hu', h2'⟩ := hmem d' hd'
        rw [h2']
        by_cases hU' : U d'.1
        · simp only [repl, hU', if_true]; omega
        · simp only [repl, hU', if_false]
          exact hQne _ _ (hu'.resolve_left hU') h1 hU
    · left
      have hQ : Q d.1 := hu.resolve_left hU
      intro x hx
      rw [h2]
      simp only [repl, hU, if_false]
      exact hQv _ hQ x hx
  obtain ⟨D, hD1, hD2, hD3⟩ := smaller m G o ds hsort hlt hval hjust hfan
  refine ⟨D, hD1, ?_, hD3⟩
  have hlen : ds.length = ((List.range G.length).filter (fun t => decide (U t ∨ Q t))).length := by
    simp only [ds, ps, List.length_map, List.filter_reverse, List.length_reverse]
  have hle : ((List.range G.length).filter (fun t => decide (U t ∨ Q t))).length ≤ G.length := by
    have := List.length_filter_le (fun t => decide (U t ∨ Q t)) (List.range G.length)
    simpa using this
  rw [hD2, hlen]
  omega

theorem eval_shape (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : l.length ≤ 2)
    (a : ℕ) (ha : a ∈ deps ⟨op, l⟩) (c : Bool) :
    (∃ k : Bool, ∀ f : ℕ → Bool, f a = c → op.eval (l.map f) = k) ∨
    (∃ b, ∀ f : ℕ → Bool, f a = c → op.eval (l.map f) = f b) := by
  rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, l'⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [deps] at ha
  · have hp : a = p := by rcases hop with rfl | rfl | rfl <;> simpa [deps] using ha
    subst hp
    left
    exact ⟨op.eval [c], fun f hf => by simp [hf]⟩
  · rcases hop with rfl | rfl | rfl
    · simp only [deps, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · cases c
        · left; exact ⟨false, fun f hf => by simp [GateOp.eval, hf]⟩
        · right; exact ⟨q, fun f hf => by simp [GateOp.eval, hf]⟩
      · cases c
        · left; exact ⟨false, fun f hf => by simp [GateOp.eval, hf]⟩
        · right; exact ⟨p, fun f hf => by simp [GateOp.eval, hf]⟩
    · simp only [deps, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · cases c
        · right; exact ⟨q, fun f hf => by simp [GateOp.eval, hf]⟩
        · left; exact ⟨true, fun f hf => by simp [GateOp.eval, hf]⟩
      · cases c
        · right; exact ⟨p, fun f hf => by simp [GateOp.eval, hf]⟩
        · left; exact ⟨true, fun f hf => by simp [GateOp.eval, hf]⟩
    · simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton] at ha
      subst ha
      left
      exact ⟨!c, fun f hf => by simp [GateOp.eval, hf]⟩
  · simp at hlen

theorem gate_V (m : ℕ) (G : List Gate) (t : ℕ) (ht : t < G.length) (x : List Bool) (hx : x.length = m) :
    V G x (m + t) = (G[t]).op.eval ((G[t]).inputs.map fun i => if i < m + t then V G x i else false) := by
  have := gate_value G x t ht
  rw [hx] at this
  exact this

theorem triv_of_input (m : ℕ) (G : List Gate) (o : ℕ) (hfan : FanInTwo ⟨G, o⟩) (t : ℕ)
    (ht : t < G.length) (a : ℕ) (ha : a ∈ deps (G[t])) (c : Bool)
    (hc : ∀ x : List Bool, x.length = m → (if a < m + t then V G x a else false) = c) :
    Triv m G t := by
  obtain ⟨hop, hlen⟩ := hfan (G[t]) (List.getElem_mem ht)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hdeps : a ∈ deps ⟨(G[t]).op, (G[t]).inputs⟩ := ha
  rcases eval_shape _ _ hop hlen a hdeps c with ⟨k, hk⟩ | ⟨b, hb⟩
  · left
    exact ⟨k, fun x hx => by rw [gate_V m G t ht x hx]; exact hk _ (hc x hx)⟩
  · by_cases hbt : b < m + t
    · right
      refine ⟨b, hbt, fun x hx => ?_⟩
      rw [gate_V m G t ht x hx, hb _ (hc x hx)]
      simp [hbt]
    · left
      refine ⟨false, fun x hx => ?_⟩
      rw [gate_V m G t ht x hx, hb _ (hc x hx)]
      simp [hbt]

theorem gen_del (m : ℕ) (G : List Gate) (o : ℕ) (hfan : FanInTwo ⟨G, o⟩)
    (hnc : ¬ IsConstW m G o) (P : ℕ → Prop) (hP : ∀ t, P t → t < G.length ∧ Triv m G t) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ S : List ℕ, S.Nodup → (∀ t ∈ S, P t) →
      D.size + S.length ≤ G.length) ∧
      ∀ x : List Bool, x.length = m → D.eval x = Circuit.eval ⟨G, o⟩ x := by
  classical
  let U : ℕ → Prop := fun t => IsConstW m G (m + t)
  let Q : ℕ → Prop := fun t => ¬ U t ∧ IsCopy m G t ∧
    ((∃ t0, ∃ (ht : t < G.length), t0 < t ∧ U t0 ∧ m + t0 ∈ deps (G[t])) ∨ P t)
  let ρ : ℕ → ℕ := fun t => if h : IsCopy m G t then Classical.choose h else 0
  have hρ : ∀ t, IsCopy m G t → ρ t < m + t ∧ ∀ x : List Bool, x.length = m → V G x (m + t) = V G x (ρ t) := by
    intro t h
    simp only [ρ, h, dif_pos]
    exact Classical.choose_spec h
  obtain ⟨D, hD1, hD2, hD3⟩ := batch m G o hfan U Q ρ
    (by
      intro t _ hU heq
      exact hnc (heq ▸ hU))
    (by
      intro t t' ht' hU hlt hdep
      obtain ⟨c, hc⟩ := hU
      have htr := triv_of_input m G o hfan t' ht' (m + t) hdep c (fun x hx => by
        rw [if_pos (by omega)]; exact hc x hx)
      by_cases hU' : U t'
      · exact Or.inl hU'
      · right
        refine ⟨hU', htr.resolve_left hU', Or.inl ⟨t, ht', hlt, ⟨c, hc⟩, hdep⟩⟩)
    (fun t h => h.1)
    (fun t h => (hρ t h.2.1).1)
    (fun t h => (hρ t h.2.1).2)
    (by
      intro t t'' hQ _ hU heq
      apply hQ.1
      obtain ⟨c, hc⟩ := hU
      refine ⟨c, fun x hx => ?_⟩
      rw [(hρ t hQ.2.1).2 x hx, heq]
      exact hc x hx)
  refine ⟨D, hD1, ?_, hD3⟩
  intro S hS hSP
  set l := (List.range G.length).filter (fun t => decide (U t ∨ Q t)) with hl
  have hsub : S.toFinset ⊆ l.toFinset := by
    intro t ht
    rw [List.mem_toFinset] at ht ⊢
    obtain ⟨htl, htr⟩ := hP t (hSP t ht)
    rw [hl, List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨htl, ?_⟩
    by_cases hU : U t
    · exact Or.inl hU
    · exact Or.inr ⟨hU, htr.resolve_left hU, Or.inr (hSP t ht)⟩
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hS] at h1
  have h2 := List.toFinset_card_le l
  omega

theorem min_contra (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C) (D : Circuit) (hD : FanInTwo D)
    (hDe : ∀ x : List Bool, x.length = N → D.eval x = C.eval x) : C.size ≤ D.size := by
  apply hmin.2 D hD
  funext z
  simp only [circuitFun]
  exact hDe _ (by simp)

theorem min_no_triv (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C)
    (hnc : ¬ IsConstW N C.gates C.output) (t : ℕ) (ht : t < C.gates.length) :
    ¬ Triv N C.gates t := by
  intro htr
  obtain ⟨D, hD, hsz, hDe⟩ := gen_del N C.gates C.output hmin.1 hnc (fun s => s = t)
    (fun s hs => hs ▸ ⟨ht, htr⟩)
  have h1 := hsz [t] (by simp) (by simp)
  have h2 := min_contra N C hmin D hD hDe
  simp only [Circuit.size, List.length_singleton] at h1 h2
  omega

theorem min_nf (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C)
    (hnc : ¬ IsConstW N C.gates C.output) (t : ℕ) (ht : t < C.gates.length) (a : ℕ)
    (ha : a ∈ deps (C.gates[t])) : a < N + t := by
  by_contra hlt
  exact min_no_triv N C hmin hnc t ht
    (triv_of_input N C.gates C.output hmin.1 t ht a ha false (fun x hx => by simp [hlt]))

theorem min_ref (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C) (t : ℕ)
    (ht : t < C.gates.length) (ho : C.output ≠ N + t) :
    ∃ t', ∃ (h : t' < C.gates.length), t < t' ∧ N + t ∈ deps (C.gates[t']) := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨D, hD, hsz, hDe⟩ := batch N C.gates C.output hmin.1 (fun s => s = t) (fun _ => False)
    (fun _ => 0) (fun s _ hs => hs ▸ ho)
    (fun s t' ht' hs hlt hdep => absurd hdep (hs ▸ hno t' ht' (hs ▸ hlt)))
    (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) (fun _ _ h => h.elim)
  have hmem : t ∈ (List.range C.gates.length).filter (fun s => decide (s = t ∨ False)) := by
    simp [ht]
  have h1 := List.length_pos_of_mem hmem
  have h2 := min_contra N C hmin D hD hDe
  simp only [Circuit.size] at h2 hsz
  omega

theorem funnel (m : ℕ) (G : List Gate) (x x' : List Bool) (hx : x.length = m) (hx' : x'.length = m)
    (T E : ℕ → Prop)
    (hin : ∀ v, v < m → ¬ T v → ¬ E v → x.getD v false = x'.getD v false)
    (hE : ∀ v, E v → V G x v = V G x' v)
    (hcl : ∀ j (hj : j < G.length), ¬ T (m + j) → ¬ E (m + j) →
      ∀ a ∈ deps (G[j]), a < m + j → ¬ T a) :
    ∀ v, ¬ T v → V G x v = V G x' v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hTv
    by_cases hEv : E v
    · exact hE v hEv
    by_cases hvm : v < m
    · simp only [V]
      rw [foldl_step_getD _ _ _ (by omega), foldl_step_getD _ _ _ (by omega)]
      exact hin v hvm hTv hEv
    by_cases hvL : v < m + G.length
    · obtain ⟨j, rfl⟩ : ∃ j, v = m + j := ⟨v - m, by omega⟩
      have hj : j < G.length := by omega
      rw [gate_V m G j hj x hx, gate_V m G j hj x' hx']
      apply eval_congr
      intro i hi
      split_ifs with h
      · exact ih i h (hcl j hj hTv hEv i hi h)
      · rfl
    · simp only [V]
      rw [getD_of_length_le _ _ (by rw [foldl_step_length]; omega),
        getD_of_length_le _ _ (by rw [foldl_step_length]; omega)]

def mapG (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def sig (w M a : ℕ) : ℕ := if a = w then M else a

theorem deps_mapG (f : ℕ → ℕ) (g : Gate) : deps (mapG f g) = (deps g).map f := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, mapG]

theorem star_agree (m : ℕ) (G : List Gate) (x : List Bool) (hx : x.length = m) (w M : ℕ)
    (hM : m + G.length ≤ M) :
    ∀ v, (V G x w = false ∨ v ≤ w) → V (G.map (mapG (sig w M))) x v = V G x v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hP
    by_cases hvm : v < m
    · simp only [V]
      rw [foldl_step_getD _ _ _ (by omega), foldl_step_getD _ _ _ (by omega)]
    by_cases hvL : v < m + G.length
    · obtain ⟨j, rfl⟩ : ∃ j, v = m + j := ⟨v - m, by omega⟩
      have hj : j < G.length := by omega
      have hj' : j < (G.map (mapG (sig w M))).length := by simp; omega
      rw [gate_V m _ j hj' x hx, gate_V m G j hj x hx]
      simp only [List.getElem_map, mapG, List.map_map]
      apply eval_congr
      intro i _
      simp only [Function.comp]
      by_cases hiw : i = w
      · subst hiw
        have h1 : ¬ (sig i M i < m + j) := by simp [sig]; omega
        rw [if_neg h1]
        rcases hP with hP | hP
        · split_ifs <;> simp [hP]
        · rw [if_neg (by omega)]
      · have h1 : sig w M i = i := by simp [sig, hiw]
        rw [h1]
        split_ifs with h2
        · apply ih i h2
          rcases hP with hP | hP
          · exact Or.inl hP
          · right; omega
        · rfl
    · simp only [V]
      rw [getD_of_length_le _ _ (by rw [foldl_step_length]; simp; omega),
        getD_of_length_le _ _ (by rw [foldl_step_length]; omega)]

theorem V_append_lt (G : List Gate) (g : Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + G.length) : V (G ++ [g]) x i = V G x i := by
  simp only [V, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  exact getD_append_lt _ _ _ (by rw [foldl_step_length]; omega)

theorem D_eval (m : ℕ) (G : List Gate) (x : List Bool) (hx : x.length = m) (a b : ℕ)
    (ha : a < m + G.length) (hb : b < m + G.length) :
    V (G ++ [⟨GateOp.or, [a, b]⟩]) x (m + G.length) = (V G x a || V G x b) := by
  have hlt : G.length < (G ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]).length := by simp
  rw [gate_V m _ G.length hlt x hx]
  simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero,
    List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id]
  rw [if_pos ha, if_pos hb, V_append_lt _ _ _ _ (by omega), V_append_lt _ _ _ _ (by omega)]

theorem shape_or (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : l.length ≤ 2)
    (w M : ℕ) (hw : w ∈ deps ⟨op, l⟩) :
    (∃ k : Bool, ∀ f : ℕ → Bool, f M = false → op.eval ((l.map (sig w M)).map f) = k) ∨
    (op = GateOp.or ∧ l.length = 2 ∧ w ∈ l ∧ ∃ b ∈ l, b ≠ w ∧
      ∀ f : ℕ → Bool, f M = false → op.eval ((l.map (sig w M)).map f) = f b) := by
  have hsw : sig w M w = M := by simp [sig]
  rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, l'⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [deps] at hw
  · have hp : w = p := by rcases hop with rfl | rfl | rfl <;> simpa [deps] using hw
    subst hp
    left
    exact ⟨op.eval [false], fun f hf => by simp [hsw, hf]⟩
  · rcases hop with rfl | rfl | rfl
    · simp only [deps, List.mem_cons, List.not_mem_nil, or_false] at hw
      left
      refine ⟨false, fun f hf => ?_⟩
      rcases hw with rfl | rfl
      · simp [GateOp.eval, hsw, hf]
      · simp [GateOp.eval, hsw, hf]
    · simp only [deps, List.mem_cons, List.not_mem_nil, or_false] at hw
      by_cases hp : p = w <;> by_cases hq : q = w
      · subst hp; subst hq
        left
        exact ⟨false, fun f hf => by simp [GateOp.eval, hsw, hf]⟩
      · subst hp
        right
        refine ⟨rfl, rfl, by simp, q, by simp, hq, fun f hf => ?_⟩
        have : sig p M q = q := by simp [sig, hq]
        simp [GateOp.eval, hsw, hf, this]
      · subst hq
        right
        refine ⟨rfl, rfl, by simp, p, by simp, hp, fun f hf => ?_⟩
        have : sig q M p = p := by simp [sig, hp]
        simp [GateOp.eval, hsw, hf, this]
      · rcases hw with hw | hw
        · exact absurd hw.symm hp
        · exact absurd hw.symm hq
    · simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton] at hw
      subst hw
      left
      exact ⟨true, fun f hf => by simp [GateOp.eval, hsw, hf]⟩
  · simp at hlen

theorem out_lt (N : ℕ) (C : Circuit) (hnc : ¬ IsConstW N C.gates C.output) :
    C.output < N + C.gates.length := by
  by_contra h
  apply hnc
  refine ⟨false, fun x hx => ?_⟩
  simp only [V]
  exact getD_of_length_le _ _ (by rw [foldl_step_length]; omega)

theorem step_lemma (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C)
    (hnc : ¬ IsConstW N C.gates C.output) (w : ℕ) (hwlt : w < N + C.gates.length)
    (hwo : w ≠ C.output)
    (hw : ∀ x : List Bool, x.length = N → V C.gates x w = true → V C.gates x C.output = true)
    (hR : ∃ j, ∃ (_ : j < C.gates.length), w ∈ deps (C.gates[j])) :
    ∃ r, ∃ (hr : r < C.gates.length), w ∈ deps (C.gates[r]) ∧
      (∀ j (hj : j < C.gates.length), w ∈ deps (C.gates[j]) → j = r) ∧
      (C.gates[r]).op = GateOp.or ∧ (C.gates[r]).inputs.length = 2 ∧ w ∈ (C.gates[r]).inputs ∧
      ∃ b ∈ (C.gates[r]).inputs, b ≠ w ∧ b < N + r := by
  classical
  have hoL := out_lt N C hnc
  set G := C.gates with hG
  set o := C.output with ho
  set L := G.length with hL
  have hLC : L = C.gates.length := rfl
  have hoC : o = C.output := rfl
  set M := N + L + 1 with hM
  set Gs := G.map (mapG (sig w M)) with hGs
  have hGsL : Gs.length = L := by simp [hGs, hL]
  set DG := Gs ++ [(⟨GateOp.or, [w, o]⟩ : Gate)] with hDG
  have hDGL : DG.length = L + 1 := by simp [hDG, hGsL]
  have hDGj : ∀ j (hj : j < L), DG[j]'(by omega) = mapG (sig w M) (G[j]) := by
    intro j hj
    simp only [hDG, hGs]
    rw [List.getElem_append_left (by simp; omega), List.getElem_map]
  have hDGL' : DG[L]'(by omega) = (⟨GateOp.or, [w, o]⟩ : Gate) := by
    simp only [hDG]
    rw [List.getElem_append_right (by simp [hGsL])]
    simp [hGsL]
  have hfanC : FanInTwo C := hmin.1
  have hDfan : FanInTwo ⟨DG, N + L⟩ := by
    intro g hg
    simp only [hDG, List.mem_append, List.mem_singleton, hGs, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩ | rfl
    · obtain ⟨h1, h2⟩ := hfanC g' hg'
      exact ⟨h1, by simpa [mapG] using h2⟩
    · simp
  have hDV : ∀ x : List Bool, x.length = N → V DG x (N + L) = V G x o := by
    intro x hx
    have h1 := D_eval N Gs x hx w o (by rw [hGsL]; exact hwlt) (by rw [hGsL]; exact hoL)
    rw [hGsL] at h1
    rw [h1, star_agree N G x hx w M (by omega) w (Or.inr le_rfl)]
    cases hv : V G x w
    · rw [star_agree N G x hx w M (by omega) o (Or.inl hv)]
      simp
    · simp [hw x hx hv]
  have hDnc : ¬ IsConstW N DG (N + L) := by
    rintro ⟨c, hc⟩
    exact hnc ⟨c, fun x hx => by rw [← hDV x hx]; exact hc x hx⟩
  have key : ∀ t1 t2, t1 < L + 1 → t2 < L + 1 → t1 ≠ t2 → Triv N DG t1 → Triv N DG t2 → False := by
    intro t1 t2 h1 h2 hne ht1 ht2
    obtain ⟨D', hD'fan, hD'sz, hD'e⟩ := gen_del N DG (N + L) hDfan hDnc (fun t => t = t1 ∨ t = t2)
      (by
        intro t ht
        rcases ht with rfl | rfl
        · exact ⟨by omega, ht1⟩
        · exact ⟨by omega, ht2⟩)
    have hsz := hD'sz [t1, t2] (by simp [hne]) (by simp)
    have hmc := min_contra N C hmin D' hD'fan (fun x hx => by
      rw [hD'e x hx]
      exact hDV x hx)
    simp only [Circuit.size, List.length_cons, List.length_nil] at hsz hmc
    rw [hDGL] at hsz
    omega
  have hread : ∀ j (hj : j < L), w ∈ deps (G[j]) → Triv N DG j := by
    intro j hj hwj
    apply triv_of_input N DG (N + L) hDfan j (by omega) M _ false
    · intro x _
      rw [if_neg (by omega)]
    · rw [hDGj j hj, deps_mapG]
      exact List.mem_map.2 ⟨w, hwj, by simp [sig]⟩
  obtain ⟨r, hr, hwr⟩ := hR
  have hwr_lt : w < N + r := min_nf N C hmin hnc r hr w hwr
  have huniq : ∀ j (hj : j < L), w ∈ deps (G[j]) → j = r := by
    intro j hj hwj
    by_contra hne
    exact key j r (by omega) (by omega) hne (hread j hj hwj) (hread r hr hwr)
  have hnotc : ¬ IsConstW N DG (N + r) := by
    rintro ⟨c, hc⟩
    by_cases hro : o = N + r
    · apply key L r (by omega) (by omega) (by omega) _ (hread r hr hwr)
      apply triv_of_input N DG (N + L) hDfan L (by omega) (N + r) _ c
      · intro x hx
        rw [if_pos (by omega)]
        exact hc x hx
      · rw [hDGL']
        simp [deps, hro]
    · obtain ⟨t', ht', hrt', hdep⟩ := min_ref N C hmin r hr (by rw [← ho]; exact hro)
      apply key t' r (by omega) (by omega) (by omega) _ (hread r hr hwr)
      apply triv_of_input N DG (N + L) hDfan t' (by omega) (N + r) _ c
      · intro x hx
        rw [if_pos (by omega)]
        exact hc x hx
      · rw [hDGj t' ht', deps_mapG]
        refine List.mem_map.2 ⟨N + r, hdep, ?_⟩
        simp [sig]
        omega
  obtain ⟨hop, hlen⟩ := hfanC (G[r]) (List.getElem_mem hr)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hDr : ∀ x : List Bool, x.length = N → V DG x (N + r) =
      (G[r]).op.eval (((G[r]).inputs.map (sig w M)).map fun i => if i < N + r then V DG x i else false) := by
    intro x hx
    rw [gate_V N DG r (by omega) x hx, hDGj r hr]
    rfl
  have hwr' : w ∈ deps ⟨(G[r]).op, (G[r]).inputs⟩ := hwr
  rcases shape_or _ _ hop hlen w M hwr' with ⟨k, hk⟩ | ⟨h1, h2, h3, b, hb, hbw, hbf⟩
  · exact absurd ⟨k, fun x hx => by rw [hDr x hx]; exact hk _ (by rw [if_neg (by omega)])⟩ hnotc
  · refine ⟨r, hr, hwr, huniq, h1, h2, h3, b, hb, hbw, ?_⟩
    by_contra hbr
    apply hnotc
    refine ⟨false, fun x hx => ?_⟩
    rw [hDr x hx, hbf _ (by rw [if_neg (by omega)]), if_neg hbr]

def gt (G : List Gate) (j : ℕ) : Gate := G.getD j ⟨GateOp.and, []⟩

theorem gt_eq (G : List Gate) (j : ℕ) (hj : j < G.length) : gt G j = G[j] := by
  simp [gt, List.getD_eq_getElem?_getD, hj]

theorem V_input (G : List Gate) (x : List Bool) (v : ℕ) (hv : v < x.length) :
    V G x v = x.getD v false := by
  simp only [V]
  exact foldl_step_getD _ _ _ hv

theorem ofFn_getD_self (x : List Bool) (N : ℕ) (hx : x.length = N) :
    List.ofFn (fun i : Fin N => x.getD i false) = x := by
  apply List.ext_getElem
  · simp [hx]
  · intro i _ h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem eval_list (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hF : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)))
    (x : List Bool) (hx : x.length = n + 1) :
    V C.gates x C.output = (x.getD n false || H (fun i : Fin n => x.getD i false)) := by
  have h1 : V C.gates x C.output = circuitFun (n + 1) C (fun i : Fin (n + 1) => x.getD i false) := by
    simp only [circuitFun]
    rw [ofFn_getD_self x (n + 1) hx]
    rfl
  rw [h1, hF]
  simp

theorem eval_snoc (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hF : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)))
    (y : Fin n → Bool) (b : Bool) :
    V C.gates (List.ofFn y ++ [b]) C.output = (b || H y) := by
  rw [eval_list n C H hF _ (by simp)]
  have h1 : (List.ofFn y ++ [b]).getD n false = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have h2 : (fun i : Fin n => (List.ofFn y ++ [b]).getD i false) = y := by
    funext i
    rw [getD_append_lt _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  rw [h1, h2]

theorem or_eval_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l) (hf : f a = true) :
    GateOp.or.eval (l.map f) = true := by
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  exact ⟨a, ha, hf⟩

theorem deps_or (g : Gate) (h : g.op = GateOp.or) : deps g = g.inputs := by
  obtain ⟨op, l⟩ := g
  simp only at h
  subst h
  rfl

theorem mem_deps_iff (g : Gate) (a : ℕ) : a ∈ deps g ↔
    (g.op = GateOp.not ∧ g.inputs.head? = some a ∨ g.op ≠ GateOp.not ∧ a ∈ g.inputs) := by
  obtain ⟨op, l⟩ := g
  cases op <;> simp [deps]

def Inv (n : ℕ) (G : List Gate) (o : ℕ) (k : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ i, i ≤ k → c i < G.length) ∧
  (∀ i, i < k → c i < c (i + 1)) ∧
  (∀ i, i ≤ k → (gt G (c i)).op = GateOp.or ∧ (gt G (c i)).inputs.length = 2) ∧
  n ∈ (gt G (c 0)).inputs ∧
  (∀ i, i < k → n + 1 + c i ∈ (gt G (c (i + 1))).inputs) ∧
  (∀ j, j < G.length → n ∈ deps (gt G j) → j = c 0) ∧
  (∀ i, i < k → ∀ j, j < G.length → n + 1 + c i ∈ deps (gt G j) → j = c (i + 1)) ∧
  (∃ b ∈ (gt G (c 0)).inputs, b ≠ n ∧ b < n + 1 + c 0) ∧
  (∀ i, i < k → ∃ b ∈ (gt G (c (i + 1))).inputs, b ≠ n + 1 + c i ∧ b < n + 1 + c (i + 1)) ∧
  (∀ i, i < k → o ≠ n + 1 + c i)

theorem inv_or (n : ℕ) (C : Circuit) (k : ℕ) (c : ℕ → ℕ) (hI : Inv n C.gates C.output k c) :
    ∀ i, i ≤ k → ∀ x : List Bool, x.length = n + 1 → x.getD n false = true →
      V C.gates x (n + 1 + c i) = true := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -⟩ := hI
  intro i
  induction i with
  | zero =>
    intro _ x hx hxn
    have hc := h1 0 (Nat.zero_le _)
    rw [gate_V (n + 1) C.gates (c 0) hc x hx, ← gt_eq C.gates (c 0) hc, (h3 0 (Nat.zero_le _)).1]
    apply or_eval_true _ _ n h4
    rw [if_pos (by omega), V_input _ _ _ (by omega)]
    exact hxn
  | succ i ih =>
    intro hi x hx hxn
    have hc := h1 (i + 1) hi
    have hlt := h2 i (by omega)
    rw [gate_V (n + 1) C.gates (c (i + 1)) hc x hx, ← gt_eq C.gates (c (i + 1)) hc,
      (h3 (i + 1) hi).1]
    apply or_eval_true _ _ (n + 1 + c i) (h5 i (by omega))
    rw [if_pos (by omega)]
    exact ih (by omega) x hx hxn

theorem inv_funnel (n : ℕ) (C : Circuit) (k : ℕ) (c : ℕ → ℕ) (hI : Inv n C.gates C.output k c)
    (hon : C.output ≠ n) (x x' : List Bool) (hx : x.length = n + 1) (hx' : x'.length = n + 1)
    (hxx : ∀ v, v < n + 1 → v ≠ n → x.getD v false = x'.getD v false)
    (hw : V C.gates x (n + 1 + c k) = V C.gates x' (n + 1 + c k)) :
    V C.gates x C.output = V C.gates x' C.output := by
  obtain ⟨-, -, -, -, -, h6, h7, -, -, h10⟩ := hI
  apply funnel (n + 1) C.gates x x' hx hx' (fun v => v = n ∨ ∃ i, i < k ∧ v = n + 1 + c i)
    (fun v => v = n + 1 + c k)
  · intro v hv hT _
    exact hxx v hv (fun h => hT (Or.inl h))
  · intro v hv
    rw [hv]
    exact hw
  · intro j hj hT hE a ha _ hTa
    rw [← gt_eq C.gates j hj] at ha
    rcases hTa with rfl | ⟨i, hi, rfl⟩
    · have := h6 j hj ha
      subst this
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        exact hE rfl
      · exact hT (Or.inr ⟨0, hk, rfl⟩)
    · have := h7 i hi j hj ha
      subst this
      by_cases hik : i + 1 = k
      · subst hik
        exact hE rfl
      · exact hT (Or.inr ⟨i + 1, by omega, rfl⟩)
  · rintro (h | ⟨i, hi, h⟩)
    · exact hon h
    · exact h10 i hi h

theorem inv_noread (n : ℕ) (C : Circuit) (k : ℕ) (c : ℕ → ℕ) (hI : Inv n C.gates C.output k c)
    (hon : C.output ≠ n) (hok : C.output ≠ n + 1 + c k)
    (hno : ∀ j (hj : j < C.gates.length), n + 1 + c k ∉ deps (C.gates[j]))
    (x x' : List Bool) (hx : x.length = n + 1) (hx' : x'.length = n + 1)
    (hxx : ∀ v, v < n + 1 → v ≠ n → x.getD v false = x'.getD v false) :
    V C.gates x C.output = V C.gates x' C.output := by
  obtain ⟨-, -, -, -, -, h6, h7, -, -, h10⟩ := hI
  apply funnel (n + 1) C.gates x x' hx hx' (fun v => v = n ∨ ∃ i, i ≤ k ∧ v = n + 1 + c i)
    (fun _ => False)
  · intro v hv hT _
    exact hxx v hv (fun h => hT (Or.inl h))
  · intro v hv
    exact hv.elim
  · intro j hj hT _ a ha _ hTa
    rcases hTa with rfl | ⟨i, hi, rfl⟩
    · rw [← gt_eq C.gates j hj] at ha
      have := h6 j hj ha
      subst this
      exact hT (Or.inr ⟨0, Nat.zero_le _, rfl⟩)
    · by_cases hik : i < k
      · rw [← gt_eq C.gates j hj] at ha
        have := h7 i hik j hj ha
        subst this
        exact hT (Or.inr ⟨i + 1, by omega, rfl⟩)
      · have : i = k := by omega
        subst this
        exact hno j hj ha
  · rintro (h | ⟨i, hi, h⟩)
    · exact hon h
    · by_cases hik : i < k
      · exact h10 i hik h
      · have : i = k := by omega
        subst this
        exact hok h

theorem base_noread (n : ℕ) (C : Circuit) (hon : C.output ≠ n)
    (hno : ∀ j (hj : j < C.gates.length), n ∉ deps (C.gates[j]))
    (x x' : List Bool) (hx : x.length = n + 1) (hx' : x'.length = n + 1)
    (hxx : ∀ v, v < n + 1 → v ≠ n → x.getD v false = x'.getD v false) :
    V C.gates x C.output = V C.gates x' C.output := by
  apply funnel (n + 1) C.gates x x' hx hx' (fun v => v = n) (fun _ => False)
  · intro v hv hT _
    exact hxx v hv hT
  · intro v hv
    exact hv.elim
  · intro j hj _ _ a ha _ hTa
    subst hTa
    exact hno j hj ha
  · exact hon

theorem chain (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n + 1) C) (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hF : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ¬ IsConstW (n + 1) C.gates C.output ∧
      ∃ k c, Inv n C.gates C.output k c ∧ C.output = n + 1 + c k := by
  obtain ⟨y0, hy0⟩ : ∃ y, H y = false := by
    obtain ⟨y, y', hne⟩ := hH
    cases h : H y
    · exact ⟨y, h⟩
    · exact ⟨y', by rw [h] at hne; cases h' : H y' <;> simp_all⟩
  obtain ⟨y1, hy1⟩ : ∃ y, H y = true := by
    obtain ⟨y, y', hne⟩ := hH
    cases h : H y
    · exact ⟨y', by rw [h] at hne; cases h' : H y' <;> simp_all⟩
    · exact ⟨y, h⟩
  have hx0 : V C.gates (List.ofFn y0 ++ [false]) C.output = false := by
    rw [eval_snoc n C H hF]
    simp [hy0]
  have hx1 : V C.gates (List.ofFn y0 ++ [true]) C.output = true := by
    rw [eval_snoc n C H hF]
    simp
  have hx2 : V C.gates (List.ofFn y1 ++ [false]) C.output = true := by
    rw [eval_snoc n C H hF]
    simp [hy1]
  have hxx : ∀ v, v < n + 1 → v ≠ n →
      (List.ofFn y0 ++ [false]).getD v false = (List.ofFn y0 ++ [true]).getD v false := by
    intro v hv hvn
    rw [getD_append_lt _ _ _ (by simp; omega), getD_append_lt _ _ _ (by simp; omega)]
  have hl0 : (List.ofFn y0 ++ [false]).length = n + 1 := by simp
  have hl1 : (List.ofFn y0 ++ [true]).length = n + 1 := by simp
  have hnc : ¬ IsConstW (n + 1) C.gates C.output := by
    rintro ⟨c, hc⟩
    have e0 := hc _ hl0
    have e1 := hc _ hl1
    rw [hx0] at e0
    rw [hx1] at e1
    rw [← e0] at e1
    exact absurd e1 (by simp)
  have hon : C.output ≠ n := by
    intro h
    have := hx2
    rw [h, V_input _ _ _ (by simp), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp)] at this
    simp at this
  have hF1 : ∀ x : List Bool, x.length = n + 1 → x.getD n false = true →
      V C.gates x C.output = true := by
    intro x hx hxn
    rw [eval_list n C H hF x hx, hxn]
    rfl
  have base : ∃ c, Inv n C.gates C.output 0 c := by
    have hR : ∃ j, ∃ (_ : j < C.gates.length), n ∈ deps (C.gates[j]) := by
      by_contra hno
      push_neg at hno
      have := base_noread n C hon hno _ _ hl0 hl1 hxx
      rw [hx0, hx1] at this
      exact absurd this (by simp)
    obtain ⟨r, hr, _, huniq, hop, hlen, hmem, b, hb, hbn, hbl⟩ :=
      step_lemma (n + 1) C hmin hnc n (by omega) (Ne.symm hon)
        (fun x hx hv => hF1 x hx (by rwa [V_input _ _ _ (by omega)] at hv)) hR
    refine ⟨fun _ => r, fun _ _ => hr, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _), ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
      ?_, fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · intro i _
      dsimp only
      rw [gt_eq _ _ hr]
      exact ⟨hop, hlen⟩
    · dsimp only
      rw [gt_eq _ _ hr]
      exact hmem
    · intro j hj hd
      exact huniq j hj (by rwa [gt_eq _ _ hj] at hd)
    · dsimp only
      rw [gt_eq _ _ hr]
      exact ⟨b, hb, hbn, hbl⟩
  have ext : ∀ k c, Inv n C.gates C.output k c → C.output ≠ n + 1 + c k →
      ∃ c', Inv n C.gates C.output (k + 1) c' := by
    intro k c hI hok
    have hI' := hI
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hI'
    have hck := h1 k le_rfl
    have hR : ∃ j, ∃ (_ : j < C.gates.length), n + 1 + c k ∈ deps (C.gates[j]) := by
      by_contra hno
      push_neg at hno
      have := inv_noread n C k c hI hon hok hno _ _ hl0 hl1 hxx
      rw [hx0, hx1] at this
      exact absurd this (by simp)
    have hw : ∀ x : List Bool, x.length = n + 1 → V C.gates x (n + 1 + c k) = true →
        V C.gates x C.output = true := by
      intro x hx hv
      cases hxn : x.getD n false
      · have hx' : (x.set n true).length = n + 1 := by simp [hx]
        have hx'n : (x.set n true).getD n false = true := by
          simp [List.getD_eq_getElem?_getD, hx]
        have hxx' : ∀ v, v < n + 1 → v ≠ n → x.getD v false = (x.set n true).getD v false := by
          intro v _ hvn
          simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hvn]
        have hv' := inv_or n C k c hI k le_rfl (x.set n true) hx' hx'n
        rw [inv_funnel n C k c hI hon x (x.set n true) hx hx' hxx' (by rw [hv, hv'])]
        exact hF1 _ hx' hx'n
      · exact hF1 x hx hxn
    obtain ⟨r, hr, hwr, huniq, hop, hlen, hmem, b, hb, hbw, hbl⟩ :=
      step_lemma (n + 1) C hmin hnc (n + 1 + c k) (by omega) (Ne.symm hok) hw hR
    have hkr : c k < r := by
      have := min_nf (n + 1) C hmin hnc r hr _ hwr
      omega
    refine ⟨fun i => if i ≤ k then c i else r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i _
      dsimp only
      split_ifs with h
      · exact h1 i h
      · exact hr
    · intro i hi
      dsimp only
      by_cases hik : i < k
      · rw [if_pos (by omega), if_pos (by omega)]
        exact h2 i hik
      · have : i = k := by omega
        subst this
        rw [if_pos le_rfl, if_neg (by omega)]
        exact hkr
    · intro i hi
      dsimp only
      split_ifs with h
      · exact h3 i h
      · rw [gt_eq _ _ hr]
        exact ⟨hop, hlen⟩
    · dsimp only
      rw [if_pos (Nat.zero_le _)]
      exact h4
    · intro i hi
      dsimp only
      by_cases hik : i < k
      · rw [if_pos (by omega), if_pos (by omega)]
        exact h5 i hik
      · have : i = k := by omega
        subst this
        rw [if_pos le_rfl, if_neg (by omega), gt_eq _ _ hr]
        exact hmem
    · intro j hj hd
      dsimp only
      rw [if_pos (Nat.zero_le _)]
      exact h6 j hj hd
    · intro i hi j hj hd
      dsimp only at hd ⊢
      by_cases hik : i < k
      · rw [if_pos (by omega)] at hd
        rw [if_pos (by omega)]
        exact h7 i hik j hj hd
      · have : i = k := by omega
        subst this
        rw [if_pos le_rfl] at hd
        rw [if_neg (by omega)]
        exact huniq j hj (by rwa [gt_eq _ _ hj] at hd)
    · dsimp only
      rw [if_pos (Nat.zero_le _)]
      exact h8
    · intro i hi
      dsimp only
      by_cases hik : i < k
      · rw [if_pos (by omega), if_pos (by omega)]
        exact h9 i hik
      · have : i = k := by omega
        subst this
        rw [if_pos le_rfl, if_neg (by omega), gt_eq _ _ hr]
        exact ⟨b, hb, hbw, hbl⟩
    · intro i hi
      dsimp only
      rw [if_pos (by omega)]
      by_cases hik : i < k
      · exact h10 i hik
      · have : i = k := by omega
        subst this
        exact hok
  have hge : ∀ k c, Inv n C.gates C.output k c → k < C.gates.length := by
    intro k c hI
    have h1 := hI.1
    have h2 := hI.2.1
    have hle : ∀ i, i ≤ k → i ≤ c i := by
      intro i
      induction i with
      | zero => intro _; exact Nat.zero_le _
      | succ i ih =>
        intro hi
        have := h2 i (by omega)
        have := ih (by omega)
        omega
    have := hle k le_rfl
    have := h1 k le_rfl
    omega
  have main : ∀ m, ∃ k c, Inv n C.gates C.output k c ∧ (m ≤ k ∨ C.output = n + 1 + c k) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨c, hc⟩ := base
      exact ⟨0, c, hc, Or.inl le_rfl⟩
    | succ m ih =>
      obtain ⟨k, c, hI, hm⟩ := ih
      by_cases hok : C.output = n + 1 + c k
      · exact ⟨k, c, hI, Or.inr hok⟩
      · obtain ⟨c', hI'⟩ := ext k c hI hok
        exact ⟨k + 1, c', hI', Or.inl (by have := hm.resolve_right hok; omega)⟩
  refine ⟨hnc, ?_⟩
  obtain ⟨k, c, hI, hm⟩ := main C.gates.length
  rcases hm with hm | hm
  · exact absurd (hge k c hI) (by omega)
  · exact ⟨k, c, hI, hm⟩

end L568

end PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hH hF
  obtain ⟨hnc, k, c, hI, hok⟩ := L568.chain n C H hmin hH hF
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hI
  have hmono : ∀ i j, i < j → j ≤ k → c i < c j := by
    intro i j hij hjk
    induction j with
    | zero => omega
    | succ j ih =>
      have := h2 j (by omega)
      by_cases hij' : i = j
      · subst hij'
        exact this
      · have := ih (by omega) (by omega)
        omega
  have hmono_le : ∀ i j, i ≤ j → j ≤ k → c i ≤ c j := by
    intro i j hij hjk
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h
      exact le_rfl
    · exact le_of_lt (hmono i j h hjk)
  have hlast : c k + 1 = C.gates.length := by
    have := h1 k le_rfl
    by_contra hne
    obtain ⟨t', ht', hlt, _⟩ := L568.min_ref (n + 1) C hmin (C.gates.length - 1) (by omega)
      (by rw [hok]; omega)
    omega
  have hgt : ∀ j (hj : j < C.gates.length), C.gates.get ⟨j, hj⟩ = L568.gt C.gates j := by
    intro j hj
    rw [L568.gt_eq _ _ hj]
    rfl
  have hreads : ∀ (j : Fin C.gates.length) (a : ℕ),
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get j).inputs.head? = some a ∨
        (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
        a ∈ (C.gates.get j).inputs) ↔ a ∈ L568.deps (L568.gt C.gates j.val) := by
    intro j a
    rw [L568.mem_deps_iff, ← hgt j.val j.isLt]
  have hchar : ∀ b, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
      b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get j).inputs.head? = some a ∨
        (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
        a ∈ (C.gates.get j).inputs)) n b → ∃ i, i ≤ k ∧ b = n + 1 + c i := by
    intro b hb
    induction hb with
    | single h =>
      obtain ⟨j, rfl, hj⟩ := h
      exact ⟨0, Nat.zero_le _, by rw [h6 j.val j.isLt ((hreads j n).1 hj)]⟩
    | tail _ h ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨j, rfl, hj⟩ := h
      have hd := (hreads j _).1 hj
      by_cases hik : i < k
      · exact ⟨i + 1, hik, by rw [h7 i hik j.val j.isLt hd]⟩
      · have : i = k := by omega
        subst this
        have := L568.min_nf (n + 1) C hmin hnc j.val j.isLt _
          (by rwa [L568.gt_eq _ _ j.isLt] at hd)
        omega
  have hchain : ∀ i, i ≤ k → Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
      b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get j).inputs.head? = some a ∨
        (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
        a ∈ (C.gates.get j).inputs)) n (n + 1 + c i) := by
    intro i
    induction i with
    | zero =>
      intro _
      apply Relation.TransGen.single
      refine ⟨⟨c 0, h1 0 (Nat.zero_le _)⟩, rfl, (hreads _ n).2 ?_⟩
      rw [L568.deps_or _ (h3 0 (Nat.zero_le _)).1]
      exact h4
    | succ i ih =>
      intro hi
      apply Relation.TransGen.tail (ih (by omega))
      refine ⟨⟨c (i + 1), h1 _ hi⟩, rfl, (hreads _ _).2 ?_⟩
      rw [L568.deps_or _ (h3 (i + 1) hi).1]
      exact h5 i (by omega)
  refine ⟨k, fun i => ⟨c i.val, h1 i.val (by omega)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.2
    intro i
    rw [Fin.lt_def]
    exact h2 i.val i.isLt
  · exact hlast
  · exact hok
  · intro i
    rw [hgt]
    exact h3 i.val (by omega)
  · rw [hgt]
    exact h4
  · intro i
    rw [hgt]
    exact h5 i.val i.isLt
  · intro j hj
    apply Fin.ext
    exact h6 j.val j.isLt ((hreads j n).1 hj)
  · intro i j hj
    apply Fin.ext
    exact h7 i.val i.isLt j.val j.isLt ((hreads j _).1 hj)
  · intro j
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := hchar _ h
      exact ⟨⟨i, by omega⟩, Fin.ext (by dsimp only; omega)⟩
    · rintro ⟨i, rfl⟩
      exact hchain i.val (by omega)
  · obtain ⟨b, hb, hbn, hbl⟩ := h8
    refine ⟨b, by rw [hgt]; exact hb, hbn, hbl, fun h => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hchar b h
    have := hmono_le 0 i (Nat.zero_le _) hi
    omega
  · intro i
    obtain ⟨b, hb, hbw, hbl⟩ := h9 i.val i.isLt
    refine ⟨b, by rw [hgt]; exact hb, hbw, ?_, hbl, fun h => ?_⟩
    · intro hbn
      subst hbn
      have := h6 (c (i.val + 1)) (h1 _ (by omega))
        (by rw [L568.deps_or _ (h3 (i.val + 1) (by omega)).1]; exact hb)
      have := hmono 0 (i.val + 1) (by omega) (by omega)
      omega
    · obtain ⟨i', hi', rfl⟩ := hchar _ h
      have hlt : i' < i.val + 1 := by
        by_contra hge
        have := hmono_le (i.val + 1) i' (by omega) hi'
        omega
      by_cases hii : i' = i.val
      · subst hii
        exact hbw rfl
      · have := h7 i' (by omega) (c (i.val + 1)) (h1 _ (by omega))
          (by rw [L568.deps_or _ (h3 (i.val + 1) (by omega)).1]; exact hb)
        have := hmono (i' + 1) (i.val + 1) (by omega) (by omega)
        omega
