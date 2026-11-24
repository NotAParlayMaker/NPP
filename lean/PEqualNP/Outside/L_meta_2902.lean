import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2902
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def rn (gs : List Gate) (w : List Bool) : List Bool := (Circuit.mk gs 0).wires w

theorem rn_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    rn (g :: gs) w = rn gs (w ++ [gv g w]) := rfl

theorem rn_app (gs hs : List Gate) (w : List Bool) : rn (gs ++ hs) w = rn hs (rn gs w) := by
  simp [rn, Circuit.wires, List.foldl_append]

theorem rn_len (gs : List Gate) (w : List Bool) : (rn gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [rn, Circuit.wires]
  | cons g gs ih => rw [rn_cons, ih, List.length_append, List.length_cons]; simp; omega

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

def mp (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def mg (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem mg_mp (f : ℕ → ℕ) (g : Gate) (h : mg g) : mg (mp f g) :=
  ⟨h.1, by simpa [mp] using h.2⟩

theorem gv_congr (f : ℕ → ℕ) (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ eff g, w'.getD (f i) false = w.getD i false) : gv (mp f g) w' = gv g w := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | not =>
    cases ins with
    | nil => rfl
    | cons a t =>
      have ha := h a (by simp [eff])
      simpa [gv, mp, GateOp.eval] using ha
  | _ =>
    have e : (ins.map f).map (fun i => w'.getD i false) = ins.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i hi => h i (by simpa [eff] using hi))
    simp only [gv, mp, e]

def sh (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def RC (p N r : ℕ) (P : List Bool) (v : Bool) : Prop :=
  (r < p ∧ P.getD r false = v) ∨ (p + N ≤ r ∧ v = false)

theorem rc_get {p N r : ℕ} {P t : List Bool} {v : Bool} (hp : P.length = p) (ht : t.length ≤ N)
    (h : RC p N r P v) : (P ++ t).getD r false = v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [List.getD_append _ _ _ _ (by omega), h2]
  · rw [List.getD_eq_default _ _ (by rw [List.length_append]; omega), h2]

theorem pt (P t : List Bool) (v : Bool) (r i : ℕ)
    (h : i = P.length → (P ++ t).getD r false = v) :
    (P ++ t).getD (sh P.length r i) false = ((P ++ [v]) ++ t).getD i false := by
  unfold sh
  rcases Nat.lt_trichotomy i P.length with hi | hi | hi
  · rw [if_pos hi, List.getD_append _ _ _ _ hi, List.append_assoc, List.getD_append _ _ _ _ hi]
  · subst hi
    rw [if_neg (lt_irrefl _), if_pos rfl, h rfl, List.append_assoc,
      List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    rfl
  · rw [if_neg (by omega), if_neg (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    have e : i - P.length = (i - 1 - P.length) + 1 := by omega
    rw [e]
    rfl

theorem sim_run (f : ℕ → ℕ) (A A' : List Bool) (N : ℕ) (ok : Gate → Prop)
    (hs : ∀ t : List Bool, t.length ≤ N → ∀ g, ok g → ∀ i ∈ eff g,
      (A' ++ t).getD (f i) false = (A ++ t).getD i false) :
    ∀ (gs : List Gate) (t : List Bool), t.length + gs.length ≤ N → (∀ g ∈ gs, ok g) →
      ∃ u, u.length = gs.length ∧ rn gs (A ++ t) = A ++ (t ++ u) ∧
        rn (gs.map (mp f)) (A' ++ t) = A' ++ (t ++ u) := by
  intro gs
  induction gs with
  | nil =>
    intro t _ _
    exact ⟨[], rfl, by rw [List.append_nil]; rfl, by rw [List.append_nil]; rfl⟩
  | cons g gs ih =>
    intro t ht hok
    have ht' : t.length + (gs.length + 1) ≤ N := by simpa using ht
    have hv : gv (mp f g) (A' ++ t) = gv g (A ++ t) :=
      gv_congr f g _ _ (hs t (by omega) g (hok g (by simp)))
    obtain ⟨u, hu, h1, h2⟩ := ih (t ++ [gv g (A ++ t)])
      (by rw [List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    refine ⟨gv g (A ++ t) :: u, by simp [hu], ?_, ?_⟩
    · rw [rn_cons, List.append_assoc, h1, List.append_assoc]; rfl
    · rw [List.map_cons, rn_cons, hv, List.append_assoc, h2, List.append_assoc]; rfl

theorem caseM (h : Gate) (hk : mg h) (c p N : ℕ) (hc : c ∈ h.inputs) (S : List Bool → Prop)
    (hl : ∀ P, S P → P.length = p) (hb : ∀ P, S P → P.getD c false = false) :
    ∃ r, ∀ P, S P → RC p N r P (gv h P) := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hk
  have hb' : ∀ P, S P → P[c]?.getD false = false := fun P hP => by
    rw [← List.getD_eq_getElem?_getD]; exact hb P hP
  have hc' : c ∈ ins := hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · refine ⟨p + N, fun P hP => Or.inr ⟨le_refl _, ?_⟩⟩
    simp only [gv, GateOp.eval, List.all_map, List.all_eq_false]
    exact ⟨c, hc', by simp [hb' P hP]⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
    · simp at hc'
    · obtain rfl : c = a := by simpa using hc'
      exact ⟨p + N, fun P hP => Or.inr ⟨le_refl _, by simp [gv, GateOp.eval, hb' P hP]⟩⟩
    · have hab : c = a ∨ c = b := by simpa using hc'
      rcases hab with rfl | rfl
      · by_cases hbp : b < p
        · exact ⟨b, fun P hP => Or.inl ⟨hbp, by simp [gv, GateOp.eval, hb' P hP]⟩⟩
        · refine ⟨p + N, fun P hP => Or.inr ⟨le_refl _, ?_⟩⟩
          have hb2 : P[b]?.getD false = false := by
            rw [← List.getD_eq_getElem?_getD]
            exact List.getD_eq_default _ _ (by rw [hl P hP]; omega)
          simp [gv, GateOp.eval, hb' P hP, hb2]
      · by_cases hap : a < p
        · exact ⟨a, fun P hP => Or.inl ⟨hap, by simp [gv, GateOp.eval, hb' P hP]⟩⟩
        · refine ⟨p + N, fun P hP => Or.inr ⟨le_refl _, ?_⟩⟩
          have ha2 : P[a]?.getD false = false := by
            rw [← List.getD_eq_getElem?_getD]
            exact List.getD_eq_default _ _ (by rw [hl P hP]; omega)
          simp [gv, GateOp.eval, hb' P hP, ha2]
    · simp at hlen

theorem del_eval (pre post : List Gate) (h : Gate) (a : List Bool) (r o : ℕ) (ha : a.length = 10)
    (hc : RC (10 + pre.length) post.length r (rn pre a) (gv h (rn pre a))) :
    (rn (pre ++ post.map (mp (sh (10 + pre.length) r))) a).getD (sh (10 + pre.length) r o) false =
      (rn (pre ++ h :: post) a).getD o false := by
  have hP : (rn pre a).length = 10 + pre.length := by rw [rn_len, ha]
  rw [rn_app, rn_app, rn_cons, ← hP]
  obtain ⟨u, hu, h1, h2⟩ := sim_run (sh (rn pre a).length r) (rn pre a ++ [gv h (rn pre a)])
    (rn pre a) post.length (fun _ => True)
    (fun t ht g _ i _ => pt _ _ _ _ _ (fun _ => rc_get hP ht hc))
    post [] (by simp) (fun _ _ => trivial)
  rw [List.append_nil] at h1 h2
  rw [h1, h2, List.nil_append]
  exact pt _ _ _ _ _ (fun _ => rc_get hP (by omega) hc)

def dang (th : ℕ) (g : Gate) : Bool := g.inputs.any fun i => decide (th ≤ i)

theorem del_one (gs : List Gate) (o : ℕ) (hm : ∀ g ∈ gs, mg g) (g : Gate) (hg : g ∈ gs)
    (hdg : dang (10 + gs.length) g = true) :
    ∃ gs' o', (∀ g ∈ gs', mg g) ∧ gs'.length + 1 = gs.length ∧
      (∀ a : List Bool, a.length = 10 → (rn gs' a).getD o' false = (rn gs a).getD o false) ∧
      gs.countP (dang (10 + gs.length)) ≤ gs'.countP (dang (10 + gs'.length)) + 1 := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    rw [List.length_append, List.length_cons]; omega
  obtain ⟨c, hc, hcth⟩ : ∃ c ∈ g.inputs, 10 + (pre ++ g :: post).length ≤ c := by
    simpa [dang] using hdg
  obtain ⟨r, hr⟩ := caseM g (hm g (by simp)) c (10 + pre.length) post.length hc
    (fun P => ∃ a : List Bool, a.length = 10 ∧ P = rn pre a)
    (by rintro P ⟨a, ha, rfl⟩; rw [rn_len, ha])
    (by
      rintro P ⟨a, ha, rfl⟩
      exact List.getD_eq_default _ _ (by rw [rn_len, ha]; omega))
  have hlen' : (pre ++ post.map (mp (sh (10 + pre.length) r))).length = pre.length + post.length := by
    rw [List.length_append, List.length_map]
  refine ⟨pre ++ post.map (mp (sh (10 + pre.length) r)), sh (10 + pre.length) r o, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hm g' (by simp [h])
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
      exact mg_mp _ _ (hm g0 (by simp [hg0]))
  · omega
  · intro a ha
    exact del_eval pre post g a r o ha (hr _ ⟨a, ha, rfl⟩)
  · rw [hlen, hlen', List.countP_append, List.countP_cons, List.countP_append, List.countP_map]
    have h1 : pre.countP (dang (10 + (pre.length + post.length + 1))) ≤
        pre.countP (dang (10 + (pre.length + post.length))) :=
      List.countP_mono_left (fun g' _ h => by
        simp only [dang, List.any_eq_true, decide_eq_true_eq] at h ⊢
        obtain ⟨i, hi, hle⟩ := h
        exact ⟨i, hi, by omega⟩)
    have h2 : post.countP (dang (10 + (pre.length + post.length + 1))) ≤
        post.countP (dang (10 + (pre.length + post.length)) ∘ mp (sh (10 + pre.length) r)) :=
      List.countP_mono_left (fun g' _ h => by
        simp only [dang, List.any_eq_true, decide_eq_true_eq, Function.comp, mp, List.mem_map,
          exists_exists_and_eq_and] at h ⊢
        obtain ⟨i, hi, hle⟩ := h
        refine ⟨i, hi, ?_⟩
        unfold sh
        rw [if_neg (by omega), if_neg (by omega)]
        omega)
    have h3 : (if dang (10 + (pre.length + post.length + 1)) g = true then 1 else 0) ≤ 1 := by
      split <;> omega
    omega

theorem del_k : ∀ (k : ℕ) (gs : List Gate) (o : ℕ), (∀ g ∈ gs, mg g) →
    k ≤ gs.countP (dang (10 + gs.length)) →
    ∃ gs' o', (∀ g ∈ gs', mg g) ∧ gs'.length + k = gs.length ∧
      ∀ a : List Bool, a.length = 10 → (rn gs' a).getD o' false = (rn gs a).getD o false := by
  intro k
  induction k with
  | zero => exact fun gs o hm _ => ⟨gs, o, hm, rfl, fun _ _ => rfl⟩
  | succ k ih =>
    intro gs o hm hk
    obtain ⟨g, hg, hdg⟩ := List.countP_pos_iff.mp (by omega : 0 < gs.countP (dang (10 + gs.length)))
    obtain ⟨gs1, o1, hm1, hl1, he1, hc1⟩ := del_one gs o hm g hg hdg
    obtain ⟨gs2, o2, hm2, hl2, he2⟩ := ih gs1 o1 hm1 (by omega)
    exact ⟨gs2, o2, hm2, by omega, fun a ha => (he2 a ha).trans (he1 a ha)⟩

theorem mono_gv (g : Gate) (hg : mg g) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    gv g w = true → gv g w' = true := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, -⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · intro hv
    simp only [gv, GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
    rintro b ⟨i, hi, rfl⟩
    exact h i (hv _ ⟨i, hi, rfl⟩)
  · intro hv
    simp only [gv, GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hv
    exact ⟨_, ⟨i, hi, rfl⟩, h i hb⟩

theorem mono_rn : ∀ (gs : List Gate), (∀ g ∈ gs, mg g) → ∀ (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (rn gs w).getD i false = true → (rn gs w').getD i false = true := by
  intro gs
  induction gs with
  | nil => exact fun _ w w' _ h => h
  | cons g gs ih =>
    intro hm w w' hlen h
    rw [rn_cons, rn_cons]
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    · rw [List.length_append, List.length_append, hlen]; rfl
    · intro i hi
      rcases Nat.lt_trichotomy i w.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hlen ▸ hlt)]
        exact h i hi
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at hi
        rw [hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        exact mono_gv g (hm g (by simp)) w w' h hi
      · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)] at hi
        exact absurd hi (by decide)

def EL : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7), (5, 7), (3, 8), (5, 8), (6, 8)]

def F (x : Fin 9 → Bool) : Bool := EL.any fun e => x e.1 && x e.2

def V (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 9 → Bool :=
  fun i => [b0, b1, b2, b3, b4, b5, b6, b7, b8].getD i.val false

theorem repr (x : Fin 9 → Bool) : x = V (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) := by
  funext i
  fin_cases i <;> rfl

def tests : List ℕ :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288,
    320, 385, 402]

def trueL : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def tb (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i.val

set_option maxRecDepth 100000 in
theorem covT : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool, F (V b0 b1 b2 b3 b4 b5 b6 b7 b8) = true →
    ∃ m ∈ tests, m ∈ trueL ∧ ∀ i : Fin 9, tb m i = true → V b0 b1 b2 b3 b4 b5 b6 b7 b8 i = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem covF : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool, F (V b0 b1 b2 b3 b4 b5 b6 b7 b8) = false →
    ∃ m ∈ tests, m ∉ trueL ∧ ∀ i : Fin 9, V b0 b1 b2 b3 b4 b5 b6 b7 b8 i = true → tb m i = true := by
  decide +kernel

def zx (v : Fin 9) (x : Fin 9 → Bool) : Fin 9 → Bool := fun i => if i = v then false else x i

set_option maxRecDepth 100000 in
theorem tgt : ∀ v ∈ ([1, 2, 3, 5, 8] : List (Fin 9)), ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    F (zx v (V b0 b1 b2 b3 b4 b5 b6 b7 b8)) =
      EL.any (fun e => e.1 != v && e.2 != v && V b0 b1 b2 b3 b4 b5 b6 b7 b8 e.1 &&
        V b0 b1 b2 b3 b4 b5 b6 b7 b8 e.2) := by
  decide +kernel

theorem le_a (x y : Fin 9 → Bool) (h : ∀ i : Fin 9, y i = true → x i = true) :
    ∀ i : ℕ, (List.ofFn y ++ [y 0 || y 4]).getD i false = true →
      (List.ofFn x ++ [x 0 || x 4]).getD i false = true := by
  intro i
  rcases Nat.lt_or_ge i 10 with hi | hi
  · interval_cases i
    · exact h 0
    · exact h 1
    · exact h 2
    · exact h 3
    · exact h 4
    · exact h 5
    · exact h 6
    · exact h 7
    · exact h 8
    · intro e
      have e' : (y 0 || y 4) = true := e
      show (x 0 || x 4) = true
      rw [Bool.or_eq_true] at e' ⊢
      exact e'.imp (h 0) (h 4)
  · intro e
    rw [List.getD_eq_default _ _ (by simp; omega)] at e
    exact absurd e (by decide)

theorem ptS : ∀ v ∈ ([1, 2, 3, 5, 8] : List (Fin 9)), ∀ (x : Fin 9 → Bool) (th : ℕ) (t : List Bool),
    10 + t.length ≤ th → ∀ i : ℕ,
    ((List.ofFn x ++ [x 0 || x 4]) ++ t).getD (if i = v.val then th else i) false =
      ((List.ofFn (zx v x) ++ [zx v x 0 || zx v x 4]) ++ t).getD i false := by
  intro v hv x th t hth i
  rcases Nat.lt_or_ge i 10 with hi | hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> interval_cases i <;>
      first
      | rfl
      | exact List.getD_eq_default _ _ (by simp; omega)
  · rw [if_neg (by have := v.isLt; omega), List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

theorem main (T : Circuit) (hm : Monotone2 T)
    (ht : ∀ m ∈ tests, T.eval (List.ofFn (tb m) ++ [tb m 0 || tb m 4]) = decide (m ∈ trueL))
    (v : Fin 9) (hv : v ∈ ([1, 2, 3, 5, 8] : List (Fin 9)))
    (hc : 4 ≤ (T.gates.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length) :
    ∃ T' : Circuit, Monotone2 T' ∧ T'.size + 4 ≤ T.size ∧ ∀ x : Fin 9 → Bool,
      T'.eval (List.ofFn x ++ [x 0 || x 4]) =
        EL.any (fun e => e.1 != v && e.2 != v && x e.1 && x e.2) := by
  obtain ⟨gs, o⟩ := T
  have hm' : ∀ g ∈ gs, mg g := hm
  have ht' : ∀ m ∈ tests, (rn gs (List.ofFn (tb m) ++ [tb m 0 || tb m 4])).getD o false =
      decide (m ∈ trueL) := ht
  have hfull : ∀ x : Fin 9 → Bool, (rn gs (List.ofFn x ++ [x 0 || x 4])).getD o false = F x := by
    intro x
    cases hF : F x with
    | true =>
      have h := covT (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
      rw [← repr x] at h
      obtain ⟨m, hmt, hmT, himp⟩ := h hF
      have e := ht' m hmt
      rw [decide_eq_true hmT] at e
      exact mono_rn gs hm' _ _ (by simp) (le_a x (tb m) himp) o e
    | false =>
      have h := covF (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
      rw [← repr x] at h
      obtain ⟨m, hmt, hmT, himp⟩ := h hF
      have e := ht' m hmt
      rw [decide_eq_false hmT] at e
      by_contra hne
      have hT : (rn gs (List.ofFn x ++ [x 0 || x 4])).getD o false = true := by
        simpa using hne
      have := mono_rn gs hm' _ _ (by simp) (le_a (tb m) x himp) o hT
      rw [e] at this
      exact absurd this (by decide)
  obtain ⟨ph, hph⟩ : ∃ f : ℕ → ℕ, f = fun i => if i = v.val then 10 + gs.length else i := ⟨_, rfl⟩
  have hm0 : ∀ g ∈ gs.map (mp ph), mg g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact mg_mp _ _ (hm' g0 hg0)
  have hcnt : 4 ≤ (gs.map (mp ph)).countP (dang (10 + (gs.map (mp ph)).length)) := by
    rw [List.length_map, List.countP_map]
    refine le_trans hc ?_
    rw [← List.countP_eq_length_filter]
    refine List.countP_mono_left (fun g _ h => ?_)
    have hv' : (v : ℕ) ∈ g.inputs := by simpa using h
    simp only [Function.comp, dang, mp, List.any_eq_true, List.mem_map, decide_eq_true_eq,
      exists_exists_and_eq_and]
    exact ⟨_, hv', by rw [hph]; simp⟩
  obtain ⟨gs', o', hm2, hl2, he2⟩ := del_k 4 (gs.map (mp ph)) (ph o) hm0 hcnt
  refine ⟨⟨gs', o'⟩, hm2, ?_, ?_⟩
  · have : gs'.length + 4 = gs.length := by rw [hl2, List.length_map]
    show gs'.length + 4 ≤ gs.length
    omega
  · intro x
    show (rn gs' (List.ofFn x ++ [x 0 || x 4])).getD o' false = _
    rw [he2 _ (by simp)]
    obtain ⟨u, hu, h1, h2⟩ := sim_run ph (List.ofFn (zx v x) ++ [zx v x 0 || zx v x 4])
      (List.ofFn x ++ [x 0 || x 4]) gs.length (fun _ => True)
      (fun t ht g _ i _ => by
        rw [hph]
        exact ptS v hv x _ t (by omega) i)
      gs [] (by simp) (fun _ _ => trivial)
    rw [List.append_nil, List.nil_append] at h1 h2
    have hout := ptS v hv x (10 + gs.length) u (by omega) o
    rw [h2, hph]
    show ((List.ofFn x ++ [x 0 || x 4]) ++ u).getD (if o = v.val then 10 + gs.length else o) false = _
    rw [hout, ← h1, hfull (zx v x)]
    have h := tgt v hv (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    rw [← repr x] at h
    exact h

end PEqualNP.Outside.L_meta_2902

theorem PEqualNP.Outside.L_meta_2902 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       ∀ x4 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], (4 : ℕ) ≤ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x4 ∈ x6.inputs)) x1.gates).length → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size + (4 : ℕ) ≤ x1.size ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x9.1 != x4 && x9.2 != x4 && x8 x9.1 && x8 x9.2 := 
  fun T hm ht v hv hc => PEqualNP.Outside.L_meta_2902.main T hm ht v hv hc
