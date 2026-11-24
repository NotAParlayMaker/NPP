import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2502

def F3 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ev (ws : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr k => ws.getD k false

def look (cls : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ := cls.getD i (.inl false)

def hasB (b : Bool) : List (Bool ⊕ ℕ) → Bool
  | [] => false
  | (.inl c) :: vs => (c == b) || hasB b vs
  | (.inr _) :: vs => hasB b vs

def ks : List (Bool ⊕ ℕ) → List ℕ
  | [] => []
  | (.inl _) :: vs => ks vs
  | (.inr k) :: vs => k :: ks vs

theorem all_ev (ws : List Bool) (vs : List (Bool ⊕ ℕ)) :
    (vs.map (ev ws)).all id = (!hasB false vs && (ks vs).all fun k => ws.getD k false) := by
  induction vs with
  | nil => simp [hasB, ks]
  | cons v vs ih =>
    cases v with
    | inl c => cases c <;> simp_all [hasB, ks, ev]
    | inr k => simp_all [hasB, ks, ev, Bool.and_left_comm]

theorem any_ev (ws : List Bool) (vs : List (Bool ⊕ ℕ)) :
    (vs.map (ev ws)).any id = (hasB true vs || (ks vs).any fun k => ws.getD k false) := by
  induction vs with
  | nil => simp [hasB, ks]
  | cons v vs ih =>
    cases v with
    | inl c => cases c <;> simp_all [hasB, ks, ev]
    | inr k => simp_all [hasB, ks, ev, Bool.or_left_comm]

theorem ks_length (vs : List (Bool ⊕ ℕ)) : (ks vs).length ≤ vs.length := by
  induction vs with
  | nil => simp [ks]
  | cons v vs ih => cases v <;> simp [ks] <;> omega

theorem ks_length_of_hasB (b : Bool) (vs : List (Bool ⊕ ℕ)) (h : hasB b vs = true) :
    (ks vs).length + 1 ≤ vs.length := by
  induction vs with
  | nil => simp [hasB] at h
  | cons v vs ih =>
    cases v with
    | inl c =>
      have := ks_length vs
      simp [ks]; omega
    | inr k =>
      simp [hasB] at h
      have := ih h
      simp [ks]; omega

theorem mem_ks (vs : List (Bool ⊕ ℕ)) (k : ℕ) (h : k ∈ ks vs) : Sum.inr k ∈ vs := by
  induction vs with
  | nil => simp [ks] at h
  | cons v vs ih =>
    cases v with
    | inl c => simp [ks] at h; exact List.mem_cons_of_mem _ (ih h)
    | inr j =>
      simp [ks] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

def pick (op : GateOp) (l : List ℕ) (dflt : Bool) : (Bool ⊕ ℕ) ⊕ Gate :=
  match l with
  | [] => .inl (.inl dflt)
  | [k] => .inl (.inr k)
  | l => .inr ⟨op, l⟩

def res (op : GateOp) (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
  match op with
  | .and => if hasB false vs then .inl (.inl false) else pick .and (ks vs) true
  | .or => if hasB true vs then .inl (.inl true) else pick .or (ks vs) false
  | .not =>
    match vs.headD (.inl false) with
    | .inl b => .inl (.inl (!b))
    | .inr k => .inr ⟨.not, [k]⟩
  | op => .inr ⟨op, ks vs⟩

def outV (ws : List Bool) : (Bool ⊕ ℕ) ⊕ Gate → Bool
  | .inl v => ev ws v
  | .inr h => h.op.eval (h.inputs.map fun i => ws.getD i false)

theorem pick_and (ws : List Bool) (l : List ℕ) :
    outV ws (pick .and l true) = l.all fun k => ws.getD k false := by
  match l with
  | [] => rfl
  | [k] => simp [pick, outV, ev]
  | a :: b :: r => simp [pick, outV, GateOp.eval, List.all_map, Function.comp_def]

theorem pick_or (ws : List Bool) (l : List ℕ) :
    outV ws (pick .or l false) = l.any fun k => ws.getD k false := by
  match l with
  | [] => rfl
  | [k] => simp [pick, outV, ev]
  | a :: b :: r => simp [pick, outV, GateOp.eval, List.any_map, Function.comp_def]

theorem pick_inr (op : GateOp) (l : List ℕ) (d : Bool) (h : Gate) (hh : pick op l d = .inr h) :
    2 ≤ l.length := by
  match l with
  | [] => simp [pick] at hh
  | [k] => simp [pick] at hh
  | a :: b :: r => simp

theorem res_eval (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not)
    (ws : List Bool) (vs : List (Bool ⊕ ℕ)) :
    op.eval (vs.map (ev ws)) = outV ws (res op vs) := by
  rcases hop with rfl | rfl | rfl
  · show (vs.map (ev ws)).all id = _
    rw [all_ev]
    cases hf : hasB false vs
    · simp only [res, hf, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]
      rw [pick_and]
    · simp [res, hf, outV, ev]
  · show (vs.map (ev ws)).any id = _
    rw [any_ev]
    cases ht : hasB true vs
    · simp only [res, ht, Bool.false_or, Bool.false_eq_true, if_false]
      rw [pick_or]
    · simp [res, ht, outV, ev]
  · show (!((vs.map (ev ws)).headD false)) = _
    cases vs with
    | nil => rfl
    | cons v vs => cases v <;> rfl

def step (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  match res g.op (g.inputs.map (look st.1)) with
  | .inl v => (st.1 ++ [v], st.2)
  | .inr h => (st.1 ++ [.inr (8 + st.2.length)], st.2 ++ [h])

def Inv (x8 : Fin 8 → Bool) (st : List (Bool ⊕ ℕ) × List Gate) (w3 : List Bool) : Prop :=
  st.1.length = w3.length ∧
  (∀ i, w3.getD i false = ev (st.2.foldl F3 (List.ofFn x8)) (look st.1 i)) ∧
  (∀ v ∈ st.1, ∀ k, v = .inr k → k < 8 + st.2.length)

theorem foldl_F3_length (gs : List Gate) (w : List Bool) :
    (gs.foldl F3 w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [F3]; omega

theorem gd_lt (w : List Bool) (a : List Bool) (k : ℕ) (hk : k < w.length) :
    (w ++ a).getD k false = w.getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem gd_self (w : List Bool) (a : Bool) : (w ++ [a]).getD w.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem gd_ge (w : List Bool) (k : ℕ) (hk : w.length ≤ k) : w.getD k false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none]

theorem look_lt (cls : List (Bool ⊕ ℕ)) (v : Bool ⊕ ℕ) (i : ℕ) (h : i < cls.length) :
    look (cls ++ [v]) i = look cls i := by
  simp only [look, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem look_self (cls : List (Bool ⊕ ℕ)) (v : Bool ⊕ ℕ) : look (cls ++ [v]) cls.length = v := by
  simp [look, List.getD_eq_getElem?_getD]

theorem look_ge (cls : List (Bool ⊕ ℕ)) (i : ℕ) (h : cls.length ≤ i) : look cls i = .inl false := by
  simp only [look, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem look_bnd (cls : List (Bool ⊕ ℕ)) (B : ℕ) (hb : ∀ v ∈ cls, ∀ k, v = .inr k → k < B)
    (i k : ℕ) (hk : look cls i = .inr k) : k < B := by
  by_cases h : i < cls.length
  · simp only [look, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
      Option.getD_some] at hk
    exact hb _ (List.getElem_mem h) k hk
  · rw [look_ge cls i (by omega)] at hk; cases hk

theorem ev_stable (w : List Bool) (a : List Bool) (v : Bool ⊕ ℕ)
    (hv : ∀ k, v = .inr k → k < w.length) : ev (w ++ a) v = ev w v := by
  cases v with
  | inl b => rfl
  | inr k => exact gd_lt w a k (hv k rfl)

theorem res_inl_bnd (op : GateOp) (vs : List (Bool ⊕ ℕ)) (B : ℕ)
    (hb : ∀ v ∈ vs, ∀ k, v = .inr k → k < B) (u : Bool ⊕ ℕ) (hu : res op vs = .inl u) :
    ∀ k, u = .inr k → k < B := by
  intro k hk; subst hk
  have hks : ∀ k ∈ ks vs, k < B := fun k hk => hb _ (mem_ks vs k hk) k rfl
  cases op with
  | and =>
    simp only [res] at hu
    split at hu
    · cases hu
    · unfold pick at hu; split at hu
      · cases hu
      · rename_i j hj; cases hu; exact hks k (by rw [hj]; simp)
      · cases hu
  | or =>
    simp only [res] at hu
    split at hu
    · cases hu
    · unfold pick at hu; split at hu
      · cases hu
      · rename_i j hj; cases hu; exact hks k (by rw [hj]; simp)
      · cases hu
  | not =>
    simp only [res] at hu
    split at hu <;> cases hu
  | mod m => simp [res] at hu
  | maj => simp [res] at hu

theorem res_inr_bnd (op : GateOp) (vs : List (Bool ⊕ ℕ)) (B : ℕ)
    (hb : ∀ v ∈ vs, ∀ k, v = .inr k → k < B) (h : Gate) (hh : res op vs = .inr h) :
    ∀ k ∈ h.inputs, k < B := by
  have hks : ∀ k ∈ ks vs, k < B := fun k hk => hb _ (mem_ks vs k hk) k rfl
  cases op with
  | and =>
    simp only [res] at hh
    split at hh
    · cases hh
    · unfold pick at hh; split at hh
      · cases hh
      · cases hh
      · cases hh; exact hks
  | or =>
    simp only [res] at hh
    split at hh
    · cases hh
    · unfold pick at hh; split at hh
      · cases hh
      · cases hh
      · cases hh; exact hks
  | not =>
    simp only [res] at hh
    split at hh
    · cases hh
    · rename_i j hj
      cases hh
      intro k hk; simp at hk; subst hk
      cases vs with
      | nil => simp at hj
      | cons a l => simp at hj; subst hj; exact hb _ List.mem_cons_self _ rfl
  | mod m => simp only [res] at hh; cases hh; exact hks
  | maj => simp only [res] at hh; cases hh; exact hks

theorem step_inv (x8 : Fin 8 → Bool) (st : List (Bool ⊕ ℕ) × List Gate) (w3 : List Bool)
    (g : Gate) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (h : Inv x8 st w3) : Inv x8 (step st g) (F3 w3 g) := by
  obtain ⟨hlen, hval, hbnd⟩ := h
  set w7 := st.2.foldl F3 (List.ofFn x8) with hw7
  have hw7len : w7.length = 8 + st.2.length := by
    rw [hw7, foldl_F3_length]; simp
  have hmap : g.inputs.map (fun i => w3.getD i false) =
      (g.inputs.map (look st.1)).map (ev w7) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hval i)
  have hnew : g.op.eval (g.inputs.map fun i => w3.getD i false) =
      outV w7 (res g.op (g.inputs.map (look st.1))) := by
    rw [hmap]; exact res_eval g.op hg w7 _
  have hbndvs : ∀ v ∈ g.inputs.map (look st.1), ∀ k, v = .inr k → k < 8 + st.2.length := by
    intro v hv k hk
    rw [List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact look_bnd st.1 _ hbnd i k hk
  have hF3 : F3 w3 g = w3 ++ [g.op.eval (g.inputs.map fun i => w3.getD i false)] := rfl
  unfold step
  split
  · rename_i v hres
    refine ⟨by simp [hF3, hlen], ?_, ?_⟩
    · intro i
      show (F3 w3 g).getD i false = ev w7 (look (st.1 ++ [v]) i)
      rw [hF3]
      rcases lt_trichotomy i st.1.length with hi | rfl | hi
      · rw [look_lt _ _ _ hi, gd_lt w3 _ i (by omega)]
        exact hval i
      · rw [look_self, hlen, gd_self, hnew, hres]; rfl
      · rw [look_ge _ _ (by simp; omega), gd_ge _ _ (by simp; omega)]; rfl
    · intro u hu k hk
      rw [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hbnd u hu k hk
      · exact res_inl_bnd _ _ _ hbndvs u hres k hk
  · rename_i hgate hres
    have hin := res_inr_bnd _ _ _ hbndvs hgate hres
    have hw7' : (st.2 ++ [hgate]).foldl F3 (List.ofFn x8) =
        w7 ++ [hgate.op.eval (hgate.inputs.map fun i => w7.getD i false)] := by
      rw [List.foldl_append]; rfl
    refine ⟨by simp [hF3, hlen], ?_, ?_⟩
    · intro i
      show (F3 w3 g).getD i false =
        ev ((st.2 ++ [hgate]).foldl F3 (List.ofFn x8)) (look (st.1 ++ [.inr (8 + st.2.length)]) i)
      rw [hF3, hw7']
      rcases lt_trichotomy i st.1.length with hi | rfl | hi
      · rw [look_lt _ _ _ hi, gd_lt w3 _ i (by omega), hval i]
        symm; apply ev_stable
        intro k hk; rw [hw7len]; exact look_bnd st.1 _ hbnd i k hk
      · rw [look_self, hlen, gd_self, hnew, hres]
        show _ = (w7 ++ _).getD (8 + st.2.length) false
        rw [← hw7len, gd_self]
        show hgate.op.eval _ = _
        congr 1
      · rw [look_ge _ _ (by simp; omega), gd_ge _ _ (by simp; omega)]; rfl
    · intro u hu k hk
      rw [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · have := hbnd u hu k hk; simp; omega
      · cases hk; simp

def run (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) : List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl step st

theorem run_inv (x8 : Fin 8 → Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    ∀ st w3, Inv x8 st w3 → Inv x8 (run gs st) (gs.foldl F3 w3) := by
  induction gs with
  | nil => intro st w3 h; exact h
  | cons g gs ih =>
    intro st w3 h
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_inv x8 st w3 g (hgs g List.mem_cons_self) h)

def rel (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any
    fun i => decide (i = 6)

theorem step_fst (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    ∃ v, (step st g).1 = st.1 ++ [v] := by
  unfold step; split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem hasB_of_mem (vs : List (Bool ⊕ ℕ)) (b : Bool) (h : Sum.inl b ∈ vs) :
    hasB b vs = true := by
  induction vs with
  | nil => simp at h
  | cons v vs ih =>
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · simp [hasB]
    · cases v with
      | inl c => simp [hasB, ih h]
      | inr k => simp [hasB, ih h]

def OkG (h : Gate) : Prop := (h.op = .and ∨ h.op = .or ∨ h.op = .not) ∧ h.inputs.length ≤ 2

theorem res_ok (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not) (vs : List (Bool ⊕ ℕ))
    (hl : vs.length ≤ 2) (h : Gate) (hh : res op vs = .inr h) : OkG h := by
  have hk := ks_length vs
  rcases hop with rfl | rfl | rfl
  · simp only [res] at hh
    split at hh
    · cases hh
    · unfold pick at hh; split at hh
      · cases hh
      · cases hh
      · cases hh; exact ⟨Or.inl rfl, by simp; omega⟩
  · simp only [res] at hh
    split at hh
    · cases hh
    · unfold pick at hh; split at hh
      · cases hh
      · cases hh
      · cases hh; exact ⟨Or.inr (Or.inl rfl), by simp; omega⟩
  · simp only [res] at hh
    split at hh
    · cases hh
    · cases hh; exact ⟨Or.inr (Or.inr rfl), by simp⟩

theorem step_snd (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : OkG g) :
    (∃ h, (step st g).2 = st.2 ++ [h] ∧ OkG h) ∨ (step st g).2 = st.2 := by
  unfold step; split
  · exact Or.inr rfl
  · rename_i h hh
    exact Or.inl ⟨h, rfl, res_ok g.op hg.1 _ (by simpa using hg.2) h hh⟩

theorem step_rel (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : OkG g)
    (h6 : look st.1 6 = .inl false) (hr : rel g = true) : (step st g).2 = st.2 := by
  unfold step
  have key : ∀ vs, vs = g.inputs.map (look st.1) → ∀ h, res g.op vs ≠ .inr h := by
    intro vs hvs h hh
    rcases hg.1 with hop | hop | hop
    · rw [hop] at hh
      have hmem : Sum.inl false ∈ vs := by
        rw [hvs]; simp only [rel, hop, GateOp.eval] at hr
        simp at hr
        exact List.mem_map.mpr ⟨6, hr, h6⟩
      simp [res, hasB_of_mem vs false hmem] at hh
    · rw [hop] at hh
      have hmem : Sum.inl false ∈ vs := by
        rw [hvs]; simp only [rel, hop, GateOp.eval] at hr
        simp at hr
        exact List.mem_map.mpr ⟨6, hr, h6⟩
      have hlen : vs.length ≤ 2 := by rw [hvs]; simpa using hg.2
      have hk := ks_length_of_hasB false vs (hasB_of_mem vs false hmem)
      simp only [res] at hh
      split at hh
      · cases hh
      · have := pick_inr _ _ _ _ hh; omega
    · rw [hop] at hh
      simp only [rel, hop, GateOp.eval] at hr
      have hhd : vs.headD (Sum.inl false) = Sum.inl false := by
        rw [hvs]
        cases hin : g.inputs with
        | nil => simp
        | cons a l =>
          rw [hin] at hr
          simp at hr
          subst hr
          simp [h6]
      simp only [List.headD_eq_head?_getD] at hhd
      simp only [res, List.headD_eq_head?_getD, hhd] at hh
      cases hh
  split
  · rfl
  · rename_i h hh; exact absurd hh (key _ rfl h)

theorem run_props (gs : List Gate) (hgs : ∀ g ∈ gs, OkG g) :
    ∀ st, look st.1 6 = .inl false → 6 < st.1.length → (∀ h ∈ st.2, OkG h) →
      (run gs st).2.length + gs.countP rel ≤ st.2.length + gs.length ∧
      ∀ h ∈ (run gs st).2, OkG h := by
  induction gs with
  | nil => intro st _ _ hok; simp only [run, List.foldl_nil]; exact ⟨by simp, hok⟩
  | cons g gs ih =>
    intro st h6 hl hok
    have hg := hgs g List.mem_cons_self
    obtain ⟨v, hv⟩ := step_fst st g
    have h6' : look (step st g).1 6 = .inl false := by rw [hv, look_lt _ _ _ hl, h6]
    have hl' : 6 < (step st g).1.length := by rw [hv]; simp; omega
    have hok' : ∀ h ∈ (step st g).2, OkG h := by
      rcases step_snd st g hg with ⟨h, hh, hokh⟩ | hh
      · rw [hh]; intro h' hh'
        rw [List.mem_append, List.mem_singleton] at hh'
        rcases hh' with hh' | rfl
        · exact hok h' hh'
        · exact hokh
      · rw [hh]; exact hok
    obtain ⟨hlen, hokr⟩ := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step st g) h6' hl' hok'
    refine ⟨?_, hokr⟩
    simp only [run, List.foldl_cons] at hlen ⊢
    rw [List.countP_cons, List.length_cons]
    by_cases hr : rel g = true
    · have := step_rel st g hg h6 hr
      rw [this] at hlen
      simp only [hr, if_true]
      omega
    · have hle : (step st g).2.length ≤ st.2.length + 1 := by
        rcases step_snd st g hg with ⟨h, hh, _⟩ | hh
        · rw [hh]; simp
        · rw [hh]; omega
      simp only [Bool.not_eq_true] at hr
      simp only [hr, Bool.false_eq_true, if_false, ite_false]
      omega

def cls0 : List (Bool ⊕ ℕ) :=
  [.inr 1, .inr 0, .inr 4, .inr 7, .inr 5, .inr 2, .inl false, .inr 6, .inr 3, .inr 1]

theorem inv0 (x8 : Fin 8 → Bool) :
    Inv x8 (cls0, []) [x8 1, x8 0, x8 4, x8 7, x8 5, x8 2, false, x8 6, x8 3, x8 1 || false] := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    simp only [List.foldl_nil]
    rcases Nat.lt_or_ge i 10 with hi | hi
    · interval_cases i <;> simp [cls0, look, ev, List.getD_eq_getElem?_getD]
    · rw [look_ge _ _ (by simp [cls0]; omega), gd_ge _ _ (by simp; omega)]; rfl
  · intro v hv k hk
    simp only [cls0, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases hk <;> simp

end PEqualNP.Outside.L_meta_2502

theorem PEqualNP.Outside.L_meta_2502 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (2 : ℕ) ≤ List.countP x1 x3.gates → (∃ (x6 : Fin (8 : ℕ) → Bool), x3.eval (x2 Bool.false x6) = Bool.false) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size + (2 : ℕ) ≤ x3.size ∧ ∀ (x8 : Fin (8 : ℕ) → Bool), x7.eval (List.ofFn x8) = x3.eval (x2 Bool.false x8) := by
  intro x1 x2 C hfan hcount hex
  have hgs : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_2502.OkG g := by
    intro g hg
    obtain ⟨hop, hl⟩ := hfan g hg
    refine ⟨?_, hl⟩
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
  obtain ⟨hlen, hok⟩ := PEqualNP.Outside.L_meta_2502.run_props C.gates hgs
    (PEqualNP.Outside.L_meta_2502.cls0, []) rfl (by decide) (by simp)
  set st := PEqualNP.Outside.L_meta_2502.run C.gates (PEqualNP.Outside.L_meta_2502.cls0, [])
    with hst
  have hinv : ∀ x8 : Fin 8 → Bool, PEqualNP.Outside.L_meta_2502.Inv x8 st (C.wires (x2 false x8)) :=
    fun x8 => PEqualNP.Outside.L_meta_2502.run_inv x8 C.gates (fun g hg => (hgs g hg).1) _ _
      (PEqualNP.Outside.L_meta_2502.inv0 x8)
  have heval : ∀ x8 : Fin 8 → Bool, C.eval (x2 false x8) =
      PEqualNP.Outside.L_meta_2502.ev (st.2.foldl PEqualNP.Outside.L_meta_2502.F3 (List.ofFn x8))
        (PEqualNP.Outside.L_meta_2502.look st.1 C.output) :=
    fun x8 => (hinv x8).2.1 C.output
  let o : ℕ := match PEqualNP.Outside.L_meta_2502.look st.1 C.output with
    | .inr k => k
    | .inl _ => 8 + st.2.length
  refine ⟨⟨st.2, o⟩, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨hop, hl⟩ := hok h hh
    refine ⟨?_, hl⟩
    rcases hop with hop | hop | hop <;> simp [hop]
  · have hc : List.countP x1 C.gates = List.countP PEqualNP.Outside.L_meta_2502.rel C.gates := rfl
    show st.2.length + 2 ≤ C.gates.length
    simp only [List.length_nil, zero_add] at hlen
    omega
  · intro x8
    rw [heval x8]
    have hw : (⟨st.2, o⟩ : Circuit).eval (List.ofFn x8) =
        (st.2.foldl PEqualNP.Outside.L_meta_2502.F3 (List.ofFn x8)).getD o false := rfl
    rw [hw]
    have hlen7 : (st.2.foldl PEqualNP.Outside.L_meta_2502.F3 (List.ofFn x8)).length =
        8 + st.2.length := by
      rw [PEqualNP.Outside.L_meta_2502.foldl_F3_length]; simp
    cases hl : PEqualNP.Outside.L_meta_2502.look st.1 C.output with
    | inr k => simp only [o, hl]; rfl
    | inl b =>
      cases b with
      | false =>
        simp only [o, hl]
        rw [PEqualNP.Outside.L_meta_2502.gd_ge _ _ (by omega)]
        rfl
      | true =>
        exfalso
        obtain ⟨x6, hx6⟩ := hex
        rw [heval x6, hl] at hx6
        exact absurd hx6 (by simp [PEqualNP.Outside.L_meta_2502.ev])
