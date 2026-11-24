import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4003_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih => intro w; rw [run_cons, ih]; simp; omega

def sem (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr j => w.getD j false

def wiresOf (ss : List (Bool ⊕ ℕ)) : List ℕ := ss.filterMap Sum.getRight?

lemma wiresOf_length (ss : List (Bool ⊕ ℕ)) : (wiresOf ss).length ≤ ss.length :=
  List.length_filterMap_le _ _

lemma wiresOf_lt (ss : List (Bool ⊕ ℕ)) (b : Bool) (h : Sum.inl b ∈ ss) :
    (wiresOf ss).length < ss.length := by
  induction ss with
  | nil => cases h
  | cons s ss ih =>
    have hl := wiresOf_length ss
    rcases s with b' | j
    · have e : wiresOf (Sum.inl b' :: ss) = wiresOf ss := rfl
      rw [e, List.length_cons]; omega
    · have e : wiresOf (Sum.inr j :: ss) = j :: wiresOf ss := rfl
      rw [e, List.length_cons, List.length_cons]
      have h' : Sum.inl b ∈ ss := by
        rcases List.mem_cons.1 h with h0 | h0
        · cases h0
        · exact h0
      have := ih h'; omega

def look (σ : List (Bool ⊕ ℕ)) (g : Gate) : List (Bool ⊕ ℕ) :=
  g.inputs.map fun i => σ.getD i (Sum.inl false)

def mk (op : GateOp) (c : Bool) (k : ℕ) (ss : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
  if Sum.inl c ∈ ss then (none, Sum.inl c) else
  match wiresOf ss with
  | [] => (none, Sum.inl (!c))
  | [j] => (none, Sum.inr j)
  | j :: j' :: js => (some ⟨op, j :: j' :: js⟩, Sum.inr k)

def stepG (σ : List (Bool ⊕ ℕ)) (k : ℕ) (g : Gate) : Option Gate × (Bool ⊕ ℕ) :=
  match g.op with
  | GateOp.not =>
      match (look σ g).headD (Sum.inl false) with
      | Sum.inl b => (none, Sum.inl (!b))
      | Sum.inr j => (some ⟨GateOp.not, [j]⟩, Sum.inr k)
  | GateOp.and => mk GateOp.and false k (look σ g)
  | GateOp.or => mk GateOp.or true k (look σ g)
  | _ => (none, Sum.inl false)

lemma all_sem (w : List Bool) (ss : List (Bool ⊕ ℕ)) (h : Sum.inl false ∉ ss) :
    GateOp.and.eval (ss.map (sem w)) = GateOp.and.eval ((wiresOf ss).map fun j => w.getD j false) := by
  show (ss.map (sem w)).all id = ((wiresOf ss).map fun j => w.getD j false).all id
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have e := ih (fun hh => h (List.mem_cons_of_mem _ hh))
    rcases s with b | j
    · cases b
      · exact absurd List.mem_cons_self h
      · simpa [wiresOf, sem] using e
    · simp [wiresOf, sem] at e ⊢
      rw [e]

lemma all_sem_false (w : List Bool) (ss : List (Bool ⊕ ℕ)) (h : Sum.inl false ∈ ss) :
    GateOp.and.eval (ss.map (sem w)) = false := by
  show (ss.map (sem w)).all id = false
  rw [List.all_eq_false]
  exact ⟨false, List.mem_map.2 ⟨_, h, rfl⟩, by simp⟩

lemma any_sem (w : List Bool) (ss : List (Bool ⊕ ℕ)) (h : Sum.inl true ∉ ss) :
    GateOp.or.eval (ss.map (sem w)) = GateOp.or.eval ((wiresOf ss).map fun j => w.getD j false) := by
  show (ss.map (sem w)).any id = ((wiresOf ss).map fun j => w.getD j false).any id
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have e := ih (fun hh => h (List.mem_cons_of_mem _ hh))
    rcases s with b | j
    · cases b
      · simpa [wiresOf, sem] using e
      · exact absurd List.mem_cons_self h
    · simp [wiresOf, sem] at e ⊢
      rw [e]

lemma any_sem_true (w : List Bool) (ss : List (Bool ⊕ ℕ)) (h : Sum.inl true ∈ ss) :
    GateOp.or.eval (ss.map (sem w)) = true := by
  show (ss.map (sem w)).any id = true
  rw [List.any_eq_true]
  exact ⟨true, List.mem_map.2 ⟨_, h, rfl⟩, rfl⟩

lemma vals_eq (σ : List (Bool ⊕ ℕ)) (w : List Bool) (g : Gate) :
    (g.inputs.map fun i => (σ.map (sem w)).getD i false) = (look σ g).map (sem w) := by
  rw [look, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases σ[i]? <;> rfl

lemma wires_bound (σ : List (Bool ⊕ ℕ)) (n : ℕ) (g : Gate)
    (hb : ∀ s ∈ σ, ∀ j, s = Sum.inr j → j < n) : ∀ j ∈ wiresOf (look σ g), j < n := by
  intro j hj
  simp only [wiresOf, look, List.mem_filterMap, List.mem_map] at hj
  obtain ⟨a, ⟨i, -, rfl⟩, ha⟩ := hj
  rw [List.getD_eq_getElem?_getD] at ha
  cases h : σ[i]? with
  | none => rw [h] at ha; simp at ha
  | some s =>
    rw [h] at ha
    have hs : s ∈ σ := List.mem_of_getElem? h
    rcases s with b | j'
    · simp at ha
    · simp at ha; subst ha; exact hb _ hs _ rfl

lemma mk_ok (op : GateOp) (c : Bool) (w : List Bool) (ss : List (Bool ⊕ ℕ))
    (P1 : Sum.inl c ∈ ss → op.eval (ss.map (sem w)) = c)
    (P2 : Sum.inl c ∉ ss → op.eval (ss.map (sem w)) = op.eval ((wiresOf ss).map fun j => w.getD j false))
    (P3 : op.eval [] = !c) (P4 : ∀ b, op.eval [b] = b)
    (hb : ∀ j ∈ wiresOf ss, j < w.length) :
    (∀ s, mk op c w.length ss = (none, s) →
        op.eval (ss.map (sem w)) = sem w s ∧ ∀ j, s = Sum.inr j → j < w.length) ∧
    (∀ e s, mk op c w.length ss = (some e, s) →
        op.eval (ss.map (sem w)) = e.op.eval (e.inputs.map fun i => w.getD i false) ∧
        s = Sum.inr w.length ∧ e.op = op ∧ e.inputs.length ≤ ss.length) := by
  unfold mk
  by_cases hc : Sum.inl c ∈ ss
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    refine ⟨fun s hs => ?_, fun e s hs => ?_⟩
    · cases hs
      exact ⟨P1 hc, fun j hj => by cases hj⟩
    · cases hs
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have hW := wiresOf_length ss
    have hP := P2 hc
    rcases hw : wiresOf ss with _ | ⟨j, _ | ⟨j', js⟩⟩
    · rw [hw] at hP
      refine ⟨fun s hs => ?_, fun e s hs => ?_⟩
      · cases hs
        exact ⟨hP.trans P3, fun j hj => by cases hj⟩
      · cases hs
    · rw [hw] at hP
      refine ⟨fun s hs => ?_, fun e s hs => ?_⟩
      · cases hs
        refine ⟨hP.trans (P4 _), fun j0 hj => ?_⟩
        cases hj
        exact hb j (by rw [hw]; exact List.mem_cons_self)
      · cases hs
    · rw [hw] at hP hW
      refine ⟨fun s hs => ?_, fun e s hs => ?_⟩
      · cases hs
      · cases hs
        exact ⟨hP, rfl, rfl, hW⟩

def Good (e : Gate) : Prop :=
  (e.op = GateOp.and ∨ e.op = GateOp.or ∨ e.op = GateOp.not) ∧ e.inputs.length ≤ 2

lemma step_ok (σ : List (Bool ⊕ ℕ)) (w : List Bool) (g : Gate) (hg : Good g)
    (hb : ∀ s ∈ σ, ∀ j, s = Sum.inr j → j < w.length) :
    (∀ s, stepG σ w.length g = (none, s) →
        g.op.eval (g.inputs.map fun i => (σ.map (sem w)).getD i false) = sem w s ∧
        ∀ j, s = Sum.inr j → j < w.length) ∧
    (∀ e s, stepG σ w.length g = (some e, s) →
        g.op.eval (g.inputs.map fun i => (σ.map (sem w)).getD i false)
          = e.op.eval (e.inputs.map fun i => w.getD i false) ∧ s = Sum.inr w.length ∧ Good e) := by
  rw [vals_eq]
  have hwb := wires_bound σ w.length g hb
  have hlk : (look σ g).length ≤ 2 := by rw [look, List.length_map]; exact hg.2
  rcases hg.1 with h | h | h
  · have key := mk_ok GateOp.and false w (look σ g) (all_sem_false w _) (all_sem w _) rfl
      (by intro b; cases b <;> rfl) hwb
    simp only [stepG, h]
    refine ⟨fun s hs => key.1 s hs, fun e s hs => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := key.2 e s hs
    exact ⟨h1, h2, Or.inl h3, le_trans h4 hlk⟩
  · have key := mk_ok GateOp.or true w (look σ g) (any_sem_true w _) (any_sem w _) rfl
      (by intro b; cases b <;> rfl) hwb
    simp only [stepG, h]
    refine ⟨fun s hs => key.1 s hs, fun e s hs => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := key.2 e s hs
    exact ⟨h1, h2, Or.inr (Or.inl h3), le_trans h4 hlk⟩
  · simp only [stepG, h]
    have hv : ((look σ g).map (sem w)).headD false = sem w ((look σ g).headD (Sum.inl false)) := by
      cases look σ g <;> rfl
    have hval : GateOp.not.eval ((look σ g).map (sem w))
        = !(sem w ((look σ g).headD (Sum.inl false))) := by
      show (!(((look σ g).map (sem w)).headD false)) = _
      rw [hv]
    rw [hval]
    rcases (look σ g).headD (Sum.inl false) with b | j
    · refine ⟨fun s hs => ?_, fun e s hs => ?_⟩
      · cases hs
        exact ⟨rfl, fun j hj => by cases hj⟩
      · cases hs
    · refine ⟨fun s hs => ?_, fun e s hs => ?_⟩
      · cases hs
      · cases hs
        exact ⟨rfl, rfl, Or.inr (Or.inr rfl), by simp⟩

def comp (m : ℕ) : List Gate → List (Bool ⊕ ℕ) → List Gate → List Gate × List (Bool ⊕ ℕ)
  | [], σ, E => (E, σ)
  | g :: gs, σ, E =>
      comp m gs (σ ++ [(stepG σ (m + E.length) g).2]) (E ++ (stepG σ (m + E.length) g).1.toList)

lemma comp_cons (m : ℕ) (g : Gate) (gs : List Gate) (σ : List (Bool ⊕ ℕ)) (E : List Gate) :
    comp m (g :: gs) σ E
      = comp m gs (σ ++ [(stepG σ (m + E.length) g).2]) (E ++ (stepG σ (m + E.length) g).1.toList) := rfl

lemma sem_append (w : List Bool) (v : Bool) (s : Bool ⊕ ℕ) (h : ∀ j, s = Sum.inr j → j < w.length) :
    sem (w ++ [v]) s = sem w s := by
  rcases s with b | j
  · rfl
  · have hj := h j rfl
    simp [sem, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma sem_last (w : List Bool) (v : Bool) : sem (w ++ [v]) (Sum.inr w.length) = v := by
  simp [sem, List.getD_eq_getElem?_getD]

lemma comp_ok (m : ℕ) (x0 : List Bool) (hx : x0.length = m) :
    ∀ (gs : List Gate) (σ : List (Bool ⊕ ℕ)) (E : List Gate),
      (∀ g ∈ gs, Good g) →
      (∀ s ∈ σ, ∀ j, s = Sum.inr j → j < m + E.length) →
      (∀ e ∈ E, Good e) →
      run gs (σ.map (sem (run E x0))) = ((comp m gs σ E).2).map (sem (run (comp m gs σ E).1 x0)) ∧
      (∀ e ∈ (comp m gs σ E).1, Good e) := by
  intro gs
  induction gs with
  | nil => intro σ E _ _ hE; exact ⟨rfl, hE⟩
  | cons g gs ih =>
    intro σ E hg hb hE
    have hlen : (run E x0).length = m + E.length := by rw [run_length, hx]
    have hgg := hg g List.mem_cons_self
    have hb' : ∀ s ∈ σ, ∀ j, s = Sum.inr j → j < (run E x0).length := by rw [hlen]; exact hb
    obtain ⟨h1, h2⟩ := step_ok σ (run E x0) g hgg hb'
    rw [hlen] at h1 h2
    have hg' : ∀ g' ∈ gs, Good g' := fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')
    rw [run_cons, comp_cons]
    rcases hst : stepG σ (m + E.length) g with ⟨o, s⟩
    cases o with
    | none =>
      obtain ⟨hv, hbs⟩ := h1 s hst
      have hb2 : ∀ s' ∈ σ ++ [s], ∀ j, s' = Sum.inr j → j < m + E.length := by
        intro s' hs' j hj
        rcases List.mem_append.1 hs' with h | h
        · exact hb s' h j hj
        · rw [List.mem_singleton] at h; subst h; exact hbs j hj
      have key := ih (σ ++ [s]) E hg' hb2 hE
      rw [List.map_append, List.map_singleton, ← hv] at key
      simpa using key
    | some e =>
      obtain ⟨hv, hs, hgood⟩ := h2 e s hst
      subst hs
      have hb2 : ∀ s' ∈ σ ++ [Sum.inr (m + E.length)], ∀ j, s' = Sum.inr j → j < m + (E ++ [e]).length := by
        intro s' hs' j hj
        rw [List.length_append, List.length_singleton]
        rcases List.mem_append.1 hs' with h | h
        · have := hb s' h j hj; omega
        · rw [List.mem_singleton] at h; subst h; cases hj; omega
      have hE2 : ∀ e' ∈ E ++ [e], Good e' := by
        intro e' he'
        rcases List.mem_append.1 he' with h | h
        · exact hE e' h
        · rw [List.mem_singleton] at h; subst h; exact hgood
      have key := ih (σ ++ [Sum.inr (m + E.length)]) (E ++ [e]) hg' hb2 hE2
      have hrun : run (E ++ [e]) x0
          = run E x0 ++ [e.op.eval (e.inputs.map fun i => (run E x0).getD i false)] := by
        rw [run_append]; rfl
      have hold : σ.map (sem (run E x0 ++ [e.op.eval (e.inputs.map fun i => (run E x0).getD i false)]))
          = σ.map (sem (run E x0)) :=
        List.map_congr_left fun s' hs' => sem_append _ _ _ (fun j hj => hb' s' hs' j hj)
      have hlast : sem (run E x0 ++ [e.op.eval (e.inputs.map fun i => (run E x0).getD i false)])
          (Sum.inr (m + E.length)) = e.op.eval (e.inputs.map fun i => (run E x0).getD i false) := by
        rw [← hlen]; exact sem_last _ _
      rw [hrun, List.map_append, List.map_singleton, hold, hlast, ← hv] at key
      simpa using key

lemma toList_le (o : Option Gate) : o.toList.length ≤ 1 := by cases o <;> simp

lemma step_none (σ : List (Bool ⊕ ℕ)) (k : ℕ) (g : Gate) (hg : Good g)
    (hnot : g.op = GateOp.not → g.inputs.length ≤ 1) (i : ℕ) (b : Bool)
    (hi : σ[i]? = some (Sum.inl b)) (hr : i ∈ g.inputs) : (stepG σ k g).1 = none := by
  have hmem : Sum.inl b ∈ look σ g := by
    refine List.mem_map.2 ⟨i, hr, ?_⟩
    rw [List.getD_eq_getElem?_getD, hi]; rfl
  have hlk : (look σ g).length ≤ 2 := by rw [look, List.length_map]; exact hg.2
  have hw := wiresOf_lt _ b hmem
  rcases hg.1 with h | h | h
  · simp only [stepG, h, mk]
    split
    · rfl
    · rcases hw' : wiresOf (look σ g) with _ | ⟨j, _ | ⟨j', js⟩⟩
      · rfl
      · rfl
      · rw [hw'] at hw; simp at hw; omega
  · simp only [stepG, h, mk]
    split
    · rfl
    · rcases hw' : wiresOf (look σ g) with _ | ⟨j, _ | ⟨j', js⟩⟩
      · rfl
      · rfl
      · rw [hw'] at hw; simp at hw; omega
  · have h1 := hnot h
    have hin : g.inputs = [i] := by
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨a', t⟩⟩
      · rw [hgi] at hr; cases hr
      · rw [hgi] at hr; simp at hr; rw [hr]
      · rw [hgi] at h1; simp at h1
    have hh : (look σ g).headD (Sum.inl false) = Sum.inl b := by
      rw [look, hin]
      show σ.getD i (Sum.inl false) = Sum.inl b
      rw [List.getD_eq_getElem?_getD, hi]; rfl
    simp only [stepG, h, hh]

lemma comp_count (m : ℕ) (S : List ℕ) :
    ∀ (gs : List Gate) (σ : List (Bool ⊕ ℕ)) (E : List Gate),
      (∀ g ∈ gs, Good g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      (∀ i ∈ S, ∃ b, σ[i]? = some (Sum.inl b)) →
      (comp m gs σ E).1.length + (gs.filter fun g => S.any fun i => g.inputs.contains i).length
        ≤ E.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro σ E _ _; simp [comp]
  | cons g gs ih =>
    intro σ E hg hS
    have hS' : ∀ i ∈ S, ∃ b, (σ ++ [(stepG σ (m + E.length) g).2])[i]? = some (Sum.inl b) := by
      intro i hi
      obtain ⟨b, hb⟩ := hS i hi
      refine ⟨b, ?_⟩
      have hlt : i < σ.length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hb
        cases hb
      rw [List.getElem?_append_left hlt]; exact hb
    have ih' := ih (σ ++ [(stepG σ (m + E.length) g).2]) (E ++ (stepG σ (m + E.length) g).1.toList)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) hS'
    rw [comp_cons, List.filter_cons]
    have hle := toList_le (stepG σ (m + E.length) g).1
    rw [List.length_append] at ih'
    by_cases hP : (S.any fun i => g.inputs.contains i) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
      obtain ⟨i, hiS, hc⟩ := List.any_eq_true.1 hP
      obtain ⟨b, hb⟩ := hS i hiS
      have hnone := step_none σ (m + E.length) g (hg g List.mem_cons_self).1
        (hg g List.mem_cons_self).2 i b hb (by simpa using hc)
      rw [hnone] at ih' ⊢
      simp only [Option.toList_none, List.length_nil, List.length_cons, List.append_nil] at ih' ⊢
      omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
      simp only [List.length_cons] at ih' ⊢
      omega

lemma getD_map_sem (σ : List (Bool ⊕ ℕ)) (w : List Bool) (o : ℕ) :
    (σ.map (sem w)).getD o false = sem w (σ.getD o (Sum.inl false)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases σ[o]? <;> rfl

def norm (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma norm_eval (g : Gate) (F : ℕ → Bool) :
    (norm g).op.eval ((norm g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  rcases g with ⟨op, ins⟩
  cases op with
  | not =>
    show (!(((ins.take 1).map F).headD false)) = !((ins.map F).headD false)
    cases ins <;> rfl
  | and => rfl
  | or => rfl
  | mod m => rfl
  | maj => rfl

lemma norm_good (g : Gate) (hg : Good g) :
    Good (norm g) ∧ ((norm g).op = GateOp.not → (norm g).inputs.length ≤ 1) := by
  rcases g with ⟨op, ins⟩
  cases op with
  | not =>
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · show (ins.take 1).length ≤ 2
      rw [List.length_take]; omega
    · show (ins.take 1).length ≤ 1
      rw [List.length_take]; omega
  | and => exact ⟨hg, fun h => by have h' : GateOp.and = GateOp.not := h; cases h'⟩
  | or => exact ⟨hg, fun h => by have h' : GateOp.or = GateOp.not := h; cases h'⟩
  | mod m => exact ⟨hg, fun h => by have h' : GateOp.mod m = GateOp.not := h; cases h'⟩
  | maj => exact ⟨hg, fun h => by have h' : GateOp.maj = GateOp.not := h; cases h'⟩

lemma run_norm (gs : List Gate) : ∀ w : List Bool, run (gs.map norm) w = run gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.map_cons, run_cons, run_cons, norm_eval, ih]

lemma getD_snoc (w : List Bool) (v : Bool) (j : ℕ) :
    (w ++ [v]).getD j false
      = if j < w.length then w.getD j false else if j = w.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : j < w.length
  · rw [List.getElem?_append_left h, ite_eq_left h]
  · rw [ite_eq_right h, List.getElem?_append_right (Nat.le_of_not_lt h)]
    by_cases h2 : j = w.length
    · rw [ite_eq_left h2, h2]; simp
    · rw [ite_eq_right h2]
      obtain ⟨k, hk⟩ : ∃ k, j - w.length = k + 1 := ⟨j - w.length - 1, by omega⟩
      rw [hk]; simp

lemma run_prefix (gs : List Gate) : ∀ (w : List Bool) (j : ℕ), j < w.length →
    (run gs w).getD j false = w.getD j false := by
  induction gs with
  | nil => intro w j _; rfl
  | cons g gs ih =>
    intro w j hj
    rw [run_cons, ih _ j (by rw [List.length_append]; omega), getD_snoc, ite_eq_left hj]

lemma run_indep (k : ℕ) : ∀ (gs : List Gate) (w w' : List Bool),
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (run gs w).getD j false = (run gs w').getD j false := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hg hl h
    rw [run_cons, run_cons]
    have hv : (g.inputs.map fun i => w.getD i false) = (g.inputs.map fun i => w'.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hg g List.mem_cons_self (e ▸ hi))
    rw [hv]
    refine ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ ?_
    · rw [List.length_append, List.length_append, hl]
    · intro j hj
      rw [getD_snoc, getD_snoc, hl, h j hj]

lemma getD_ofFn (n : ℕ) (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

def sig0 (n : ℕ) (i : Fin n) : List (Bool ⊕ ℕ) :=
  List.ofFn (fun j : Fin n => if j = i then Sum.inl false else Sum.inr j.val)

lemma sig0_map (n : ℕ) (i : Fin n) (x : Fin n → Bool) :
    (sig0 n i).map (sem (List.ofFn x)) = List.ofFn (Function.update x i false) := by
  rw [sig0, List.map_ofFn]
  congr 1
  funext j
  show sem (List.ofFn x) (if j = i then Sum.inl false else Sum.inr j.val) = Function.update x i false j
  by_cases h : j = i
  · have e : sem (List.ofFn x) (Sum.inl false) = false := rfl
    rw [ite_eq_left h, h, Function.update_self, e]
  · rw [ite_eq_right h, Function.update_of_ne h]
    exact getD_ofFn n x j

lemma sig0_get (n : ℕ) (i : Fin n) : (sig0 n i)[i.val]? = some (Sum.inl false) := by
  rw [sig0, List.getElem?_ofFn, dite_eq_left i.isLt]
  simp

lemma sig0_bound (n : ℕ) (i : Fin n) : ∀ s ∈ sig0 n i, ∀ j, s = Sum.inr j → j < n := by
  intro s hs j hj
  rw [sig0, List.mem_ofFn] at hs
  obtain ⟨k, hk⟩ := hs
  subst hj
  have hk' : (if k = i then Sum.inl false else Sum.inr k.val) = (Sum.inr j : Bool ⊕ ℕ) := hk
  by_cases h : k = i
  · rw [ite_eq_left h] at hk'; cases hk'
  · rw [ite_eq_right h] at hk'; cases hk'; exact k.isLt

theorem partA (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hs : C.size ≤ s) (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) (i : Fin n) :
    HasCircuitSize n (fun x => f x || x i) (s + 1) := by
  refine ⟨⟨C.gates ++ [⟨GateOp.or, [C.output, i.val]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hf g h
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨by simp, by simp⟩
  · show (C.gates ++ [(⟨GateOp.or, [C.output, i.val]⟩ : Gate)]).length ≤ s + 1
    rw [List.length_append, List.length_singleton]
    have : C.gates.length ≤ s := hs
    omega
  · intro x
    have hw : (run C.gates (List.ofFn x)).length = n + C.gates.length := by
      rw [run_length, List.length_ofFn]
    have h1 : (run C.gates (List.ofFn x)).getD C.output false = f x := hC x
    have h2 : (run C.gates (List.ofFn x)).getD i.val false = x i := by
      rw [run_prefix C.gates (List.ofFn x) i.val (by simp)]
      exact getD_ofFn n x i
    show (run (C.gates ++ [(⟨GateOp.or, [C.output, i.val]⟩ : Gate)]) (List.ofFn x)).getD
      (n + C.gates.length) false = (f x || x i)
    rw [run_append]
    show ((run C.gates (List.ofFn x)) ++ [((run C.gates (List.ofFn x)).getD C.output false
      || ((run C.gates (List.ofFn x)).getD i.val false || false))]).getD (n + C.gates.length) false = _
    rw [getD_snoc, hw, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, h1, h2, Bool.or_false]

theorem partB (n s : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (C : Circuit) (hf : FanInTwo C)
    (hs : C.size ≤ s) (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (h2 : ∃ x, f (Function.update x i false) ≠ f (Function.update x i true))
    (h3 : ∃ x y, f (Function.update x i false) ≠ f (Function.update y i false)) :
    1 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x i false)) (s - 1) := by
  have hgood0 : ∀ g ∈ C.gates, Good g := by
    intro g hg
    obtain ⟨h1, h2'⟩ := hf g hg
    refine ⟨?_, h2'⟩
    simpa using h1
  have hgn : ∀ g ∈ C.gates.map norm, Good g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact norm_good g0 (hgood0 g0 hg0)
  have hb0 : ∀ s' ∈ sig0 n i, ∀ j, s' = Sum.inr j → j < n + ([] : List Gate).length := by
    intro s' hs' j hj
    have := sig0_bound n i s' hs' j hj
    simpa using this
  have hkey : ∀ x : Fin n → Bool, f (Function.update x i false)
      = sem (run (comp n (C.gates.map norm) (sig0 n i) []).1 (List.ofFn x))
          ((comp n (C.gates.map norm) (sig0 n i) []).2.getD C.output (Sum.inl false)) := by
    intro x
    have h := (comp_ok n (List.ofFn x) (by simp) (C.gates.map norm) (sig0 n i) []
      (fun g hg => (hgn g hg).1) hb0 (by simp)).1
    have h0 : run [] (List.ofFn x) = List.ofFn x := rfl
    rw [h0, sig0_map, run_norm] at h
    rw [← hC (Function.update x i false)]
    show (run C.gates (List.ofFn (Function.update x i false))).getD C.output false = _
    rw [h, getD_map_sem]
  have hfan := (comp_ok n (List.ofFn fun _ : Fin n => false) (by simp) (C.gates.map norm) (sig0 n i) []
    (fun g hg => (hgn g hg).1) hb0 (by simp)).2
  have hcnt := comp_count n [i.val] (C.gates.map norm) (sig0 n i) [] hgn (by
    intro k hk
    simp at hk
    subst hk
    exact ⟨false, sig0_get n i⟩)
  have hrun : ∀ x : Fin n → Bool,
      f x = (run (C.gates.map norm) (List.ofFn x)).getD C.output false := by
    intro x
    rw [run_norm, ← hC x]
    rfl
  have hread : ∃ g ∈ C.gates.map norm, i.val ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ C.gates.map norm, i.val ∉ g.inputs := fun g hg hi => hno ⟨g, hg, hi⟩
    by_cases ho : C.output = i.val
    · obtain ⟨a, b, hab⟩ := h3
      apply hab
      have hc : ∀ x : Fin n → Bool, f (Function.update x i false) = false := by
        intro x
        rw [hrun, ho, run_prefix (C.gates.map norm) (List.ofFn (Function.update x i false)) i.val
          (by simp), ← sig0_map, getD_map_sem, List.getD_eq_getElem?_getD, sig0_get]
        rfl
      rw [hc a, hc b]
    · obtain ⟨x, hx⟩ := h2
      apply hx
      rw [hrun, hrun]
      refine run_indep i.val _ _ _ hno' (by simp) ?_ _ ho
      intro j hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      by_cases hjn : j < n
      · have hne : (⟨j, hjn⟩ : Fin n) ≠ i := fun e => hj (congrArg Fin.val e)
        rw [dite_eq_left hjn, dite_eq_left hjn, Function.update_of_ne hne, Function.update_of_ne hne]
      · rw [dite_eq_right hjn, dite_eq_right hjn]
  have hpos : 0 < ((C.gates.map norm).filter fun g => [i.val].any fun k => g.inputs.contains k).length := by
    obtain ⟨g, hg, hi⟩ := hread
    exact List.length_pos_of_mem (List.mem_filter.2 ⟨hg, by simpa using hi⟩)
  have hsz : (comp n (C.gates.map norm) (sig0 n i) []).1.length + 1 ≤ s := by
    have hs' : C.gates.length ≤ s := hs
    simp only [List.length_nil, List.length_map] at hcnt
    omega
  rcases hsj : (comp n (C.gates.map norm) (sig0 n i) []).2.getD C.output (Sum.inl false) with b | j
  · exfalso
    obtain ⟨a, b', hab⟩ := h3
    apply hab
    rw [hkey a, hkey b', hsj]
    rfl
  · refine ⟨by omega, ⟨(comp n (C.gates.map norm) (sig0 n i) []).1, j⟩, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨h1, h2'⟩ := hfan e he
      refine ⟨?_, h2'⟩
      simpa using h1
    · show (comp n (C.gates.map norm) (sig0 n i) []).1.length ≤ s - 1
      omega
    · intro y
      show _ = f (Function.update y i false)
      rw [hkey y, hsj]
      rfl

end PEqualNP.Outside.L_meta_4003_aux

theorem PEqualNP.Outside.L_meta_4003 : (∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x2 x3 → ∀ (x5 : Fin x1), PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x6 : Fin x1 → Bool) => x2 x6 || x6 x5) (x3 + (1 : ℕ))) ∧ ∀ (x1 x2 : ℕ) (x3 : (Fin x1 → Bool) → Bool) (x4 : Fin x1), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x2 → (∃ (x6 : Fin x1 → Bool), x3 (Function.update x6 x4 Bool.false) ≠ x3 (Function.update x6 x4 Bool.true)) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x3 (Function.update x7 x4 Bool.false) ≠ x3 (Function.update x8 x4 Bool.false)) → (1 : ℕ) ≤ x2 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x8 : Fin x1 → Bool) => x3 (Function.update x8 x4 Bool.false)) (x2 - (1 : ℕ)) := by
  refine ⟨?_, ?_⟩
  · intro n f s h i
    obtain ⟨C, hf, hs, hC⟩ := h
    exact PEqualNP.Outside.L_meta_4003_aux.partA n f s C hf hs hC i
  · intro n s f i h h2 h3
    obtain ⟨C, hf, hs, hC⟩ := h
    exact PEqualNP.Outside.L_meta_4003_aux.partB n s f i C hf hs hC h2 h3
