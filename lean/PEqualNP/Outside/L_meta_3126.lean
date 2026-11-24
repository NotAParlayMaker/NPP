import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3126

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def inp (x2 : List (Option (Fin 7))) (x : Fin 7 → Bool) : List Bool :=
  List.map (fun o : Option (Fin 7) => o.elim Bool.false x) x2

def FT (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NC (x2 : List (Option (Fin 7))) (G : List Gate) (w : ℕ) : Prop :=
  ∃ a b : Fin 7 → Bool, ((Circuit.mk G 0).wires (inp x2 a)).getD w false ≠
    ((Circuit.mk G 0).wires (inp x2 b)).getD w false

def Live (x2 : List (Option (Fin 7))) (E : List Gate) (g : Gate) : Prop :=
  ∀ w ∈ g.inputs, g.op ≠ GateOp.not ∨ g.inputs[0]? = some w → NC x2 E w

lemma wires_cons (g : Gate) (G : List Gate) (y : List Bool) :
    (Circuit.mk (g :: G) 0).wires y =
      (Circuit.mk G 0).wires (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) := rfl

lemma wires_snoc (G : List Gate) (g : Gate) (y : List Bool) :
    (Circuit.mk (G ++ [g]) 0).wires y =
      (Circuit.mk G 0).wires y ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk G 0).wires y).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma wires_length (G : List Gate) : ∀ y : List Bool,
    ((Circuit.mk G 0).wires y).length = y.length + G.length := by
  induction G with
  | nil => intro y; rfl
  | cons g G ih => intro y; rw [wires_cons, ih]; simp; omega

lemma getD_ge (l : List Bool) (u : ℕ) (h : l.length ≤ u) : l.getD u false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_snoc (l : List Bool) (a : Bool) (u : ℕ) :
    (l ++ [a]).getD u false =
      if u < l.length then l.getD u false else if u = l.length then a else false := by
  by_cases h1 : u < l.length
  · rw [List.getD_append _ _ _ _ h1]; simp [h1]
  · by_cases h2 : u = l.length
    · subst h2; simp
    · have h3 : l.length ≤ u := by omega
      rw [List.getD_append_right _ _ _ _ h3]
      have h4 : ([a] : List Bool).length ≤ u - l.length := by simp; omega
      rw [getD_ge _ _ h4]
      simp [h1, h2]

lemma inp_length (x2 : List (Option (Fin 7))) (x : Fin 7 → Bool) : (inp x2 x).length = x2.length := by
  simp [inp]

lemma V_snoc (x2 : List (Option (Fin 7))) (E : List Gate) (g : Gate) (x : Fin 7 → Bool) (w : ℕ) :
    ((Circuit.mk (E ++ [g]) 0).wires (inp x2 x)).getD w false =
      if w < x2.length + E.length then ((Circuit.mk E 0).wires (inp x2 x)).getD w false
      else if w = x2.length + E.length then
        g.op.eval (g.inputs.map fun i => ((Circuit.mk E 0).wires (inp x2 x)).getD i false)
      else false := by
  rw [wires_snoc, getD_snoc, wires_length, inp_length]

lemma VD_snoc (D : List Gate) (g : Gate) (x : Fin 7 → Bool) (w : ℕ) :
    ((Circuit.mk (D ++ [g]) 0).wires (List.ofFn x)).getD w false =
      if w < 7 + D.length then ((Circuit.mk D 0).wires (List.ofFn x)).getD w false
      else if w = 7 + D.length then
        g.op.eval (g.inputs.map fun i => ((Circuit.mk D 0).wires (List.ofFn x)).getD i false)
      else false := by
  rw [wires_snoc, getD_snoc, wires_length, List.length_ofFn]

lemma NC_snoc_lt (x2 : List (Option (Fin 7))) (E : List Gate) (g : Gate) (w : ℕ)
    (h : w < x2.length + E.length) : NC x2 (E ++ [g]) w ↔ NC x2 E w := by
  simp only [NC, V_snoc, h, ↓reduceIte]

lemma NC_snoc_gt (x2 : List (Option (Fin 7))) (E : List Gate) (g : Gate) (w : ℕ)
    (h : x2.length + E.length < w) : ¬ NC x2 (E ++ [g]) w := by
  rintro ⟨a, b, hab⟩
  apply hab
  have h1 : ¬ w < x2.length + E.length := by omega
  have h2 : ¬ w = x2.length + E.length := by omega
  rw [V_snoc, V_snoc]
  simp [h1, h2]

def Inv (x2 : List (Option (Fin 7))) (E D : List Gate) : Prop :=
  ∀ w, NC x2 E w → ∃ u, u < 7 + D.length ∧ ∀ x : Fin 7 → Bool,
    ((Circuit.mk D 0).wires (List.ofFn x)).getD u false =
      ((Circuit.mk E 0).wires (inp x2 x)).getD w false

lemma ofFn_getD (x : Fin 7 → Bool) (j : Fin 7) : (List.ofFn x).getD j.val false = x j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

lemma eval_and1 (v : Bool) : GateOp.and.eval [v] = v := by simp [GateOp.eval]
lemma eval_and2 (v w : Bool) : GateOp.and.eval [v, w] = (v && w) := by simp [GateOp.eval]
lemma eval_or1 (v : Bool) : GateOp.or.eval [v] = v := by simp [GateOp.eval]
lemma eval_or2 (v w : Bool) : GateOp.or.eval [v, w] = (v || w) := by simp [GateOp.eval]
lemma eval_not (v : Bool) (l : List Bool) : GateOp.not.eval (v :: l) = !v := by
  simp [GateOp.eval]

lemma inv_zero (x2 : List (Option (Fin 7))) : Inv x2 [] [] := by
  intro w hw
  obtain ⟨a, b, hab⟩ := hw
  rcases hx : x2[w]? with _ | o
  · exfalso; apply hab
    simp [Circuit.wires, inp, hx, List.getD_eq_getElem?_getD]
  · rcases o with _ | j
    · exfalso; apply hab
      simp [Circuit.wires, inp, hx, List.getD_eq_getElem?_getD]
    · refine ⟨j.val, by simp, fun x => ?_⟩
      have e : ((Circuit.mk [] 0).wires (inp x2 x)).getD w false = x j := by
        simp [Circuit.wires, inp, hx, List.getD_eq_getElem?_getD]
      rw [e]
      exact ofFn_getD x j

lemma and_dich {X : Type} (p q : X → Bool) (hp : ∀ x y, p x = p y) :
    (∀ x y, (p x && q x) = (p y && q y)) ∨ (∀ x, (p x && q x) = q x) := by
  by_cases h : ∀ x, p x = true
  · right; intro x; simp [h x]
  · left
    obtain ⟨x0, hx0⟩ := not_forall.mp h
    have h0 : ∀ y, p y = false := fun y => by
      rw [← hp x0 y]; simpa using hx0
    intro x y; simp [h0 x, h0 y]

lemma or_dich {X : Type} (p q : X → Bool) (hp : ∀ x y, p x = p y) :
    (∀ x y, (p x || q x) = (p y || q y)) ∨ (∀ x, (p x || q x) = q x) := by
  by_cases h : ∀ x, p x = false
  · right; intro x; simp [h x]
  · left
    obtain ⟨x0, hx0⟩ := not_forall.mp h
    have h0 : ∀ y, p y = true := fun y => by
      rw [← hp x0 y]; simpa using hx0
    intro x y; simp [h0 x, h0 y]

lemma two_dich (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) {X : Type}
    (p q : X → Bool) (hp : ∀ x y, p x = p y) :
    (∀ x y, op.eval [p x, q x] = op.eval [p y, q y]) ∨ (∀ x, op.eval [p x, q x] = q x) := by
  rcases hop with rfl | rfl
  · simpa only [eval_and2] using and_dich p q hp
  · simpa only [eval_or2] using or_dich p q hp

lemma two_comm (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases hop with rfl | rfl
  · rw [eval_and2, eval_and2, Bool.and_comm]
  · rw [eval_or2, eval_or2, Bool.or_comm]

lemma two_dich' (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) {X : Type}
    (p q : X → Bool) (hq : ∀ x y, q x = q y) :
    (∀ x y, op.eval [p x, q x] = op.eval [p y, q y]) ∨ (∀ x, op.eval [p x, q x] = p x) := by
  rcases two_dich op hop q p hq with h | h
  · left; intro x y
    rw [two_comm op hop (p x) (q x), two_comm op hop (p y) (q y)]; exact h x y
  · right; intro x
    rw [two_comm op hop]; exact h x

lemma dead_cases (x2 : List (Option (Fin 7))) (E : List Gate) (g : Gate) (hg : FT g)
    (hdead : ¬ Live x2 E g) :
    (∀ a b : Fin 7 → Bool,
        g.op.eval (g.inputs.map fun i => ((Circuit.mk E 0).wires (inp x2 a)).getD i false) =
          g.op.eval (g.inputs.map fun i => ((Circuit.mk E 0).wires (inp x2 b)).getD i false)) ∨
    ∃ b ∈ g.inputs, NC x2 E b ∧ ∀ x : Fin 7 → Bool,
        g.op.eval (g.inputs.map fun i => ((Circuit.mk E 0).wires (inp x2 x)).getD i false) =
          ((Circuit.mk E 0).wires (inp x2 x)).getD b false := by
  have hex : ∃ w ∈ g.inputs, (g.op ≠ GateOp.not ∨ g.inputs[0]? = some w) ∧ ¬ NC x2 E w := by
    by_contra hcon
    apply hdead
    intro w hw hrel
    by_contra hn
    exact hcon ⟨w, hw, hrel, hn⟩
  obtain ⟨w0, hw0, hrel, hnc⟩ := hex
  have hconst : ∀ w, ¬ NC x2 E w → ∀ a b : Fin 7 → Bool,
      ((Circuit.mk E 0).wires (inp x2 a)).getD w false =
        ((Circuit.mk E 0).wires (inp x2 b)).getD w false := by
    intro w hw a b
    by_contra h
    exact hw ⟨a, b, h⟩
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hw0 hrel hlen
  rcases hop with rfl | rfl | rfl
  ·
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hw0
    · simp at hw0
      subst hw0
      left; intro x y
      simp only [List.map_cons, List.map_nil, eval_and1]
      exact hconst _ hnc x y
    · simp at hw0
      rcases hw0 with rfl | rfl
      · by_cases hb : NC x2 E b
        · rcases two_dich GateOp.and (Or.inl rfl)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD w0 false)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD b false)
              (hconst _ hnc) with h | h
          · left; exact h
          · right; exact ⟨b, by simp, hb, h⟩
        · left; intro x y
          simp only [List.map_cons, List.map_nil, eval_and2]
          rw [hconst _ hnc x y, hconst _ hb x y]
      · by_cases ha : NC x2 E a
        · rcases two_dich' GateOp.and (Or.inl rfl)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD a false)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD w0 false)
              (hconst _ hnc) with h | h
          · left; exact h
          · right; exact ⟨a, by simp, ha, h⟩
        · left; intro x y
          simp only [List.map_cons, List.map_nil, eval_and2]
          rw [hconst _ hnc x y, hconst _ ha x y]
    · simp at hlen
  ·
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hw0
    · simp at hw0
      subst hw0
      left; intro x y
      simp only [List.map_cons, List.map_nil, eval_or1]
      exact hconst _ hnc x y
    · simp at hw0
      rcases hw0 with rfl | rfl
      · by_cases hb : NC x2 E b
        · rcases two_dich GateOp.or (Or.inr rfl)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD w0 false)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD b false)
              (hconst _ hnc) with h | h
          · left; exact h
          · right; exact ⟨b, by simp, hb, h⟩
        · left; intro x y
          simp only [List.map_cons, List.map_nil, eval_or2]
          rw [hconst _ hnc x y, hconst _ hb x y]
      · by_cases ha : NC x2 E a
        · rcases two_dich' GateOp.or (Or.inr rfl)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD a false)
              (fun x : Fin 7 → Bool => ((Circuit.mk E 0).wires (inp x2 x)).getD w0 false)
              (hconst _ hnc) with h | h
          · left; exact h
          · right; exact ⟨a, by simp, ha, h⟩
        · left; intro x y
          simp only [List.map_cons, List.map_nil, eval_or2]
          rw [hconst _ hnc x y, hconst _ ha x y]
    · simp at hlen
  ·
    rcases ins with _ | ⟨a, rest⟩
    · simp at hw0
    · simp at hrel
      subst hrel
      left; intro x y
      simp only [List.map_cons, eval_not]
      rw [hconst _ hnc x y]


lemma step_live (x2 : List (Option (Fin 7))) (E D : List Gate) (g : Gate) (hg : FT g)
    (hlive : Live x2 E g) (hI : Inv x2 E D) :
    ∃ g' : Gate, FT g' ∧ Inv x2 (E ++ [g]) (D ++ [g']) := by
  classical
  let f : ℕ → ℕ := fun w => if h : NC x2 E w then Classical.choose (hI w h) else 0
  have hf : ∀ w, NC x2 E w → f w < 7 + D.length ∧ ∀ x : Fin 7 → Bool,
      ((Circuit.mk D 0).wires (List.ofFn x)).getD (f w) false =
        ((Circuit.mk E 0).wires (inp x2 x)).getD w false := by
    intro w hw
    simp only [f, hw, ↓reduceDIte]
    exact Classical.choose_spec (hI w hw)
  refine ⟨⟨g.op, g.inputs.map f⟩, ⟨hg.1, by simpa using hg.2⟩, ?_⟩
  intro w hw
  rcases lt_trichotomy w (x2.length + E.length) with hlt | heq | hgt
  · obtain ⟨u, hu, hu2⟩ := hI w ((NC_snoc_lt x2 E g w hlt).mp hw)
    have hu' : u < 7 + D.length := hu
    refine ⟨u, by simp; omega, fun x => ?_⟩
    rw [VD_snoc, V_snoc]
    simp only [hu', hlt, ↓reduceIte]
    exact hu2 x
  · subst heq
    refine ⟨7 + D.length, by simp, fun x => ?_⟩
    rw [VD_snoc, V_snoc]
    simp only [lt_self_iff_false, eq_self, ↓reduceIte]
    have key : ∀ i ∈ g.inputs, (g.op ≠ GateOp.not ∨ g.inputs[0]? = some i) →
        ((Circuit.mk D 0).wires (List.ofFn x)).getD (f i) false =
          ((Circuit.mk E 0).wires (inp x2 x)).getD i false :=
      fun i hi hr => (hf i (hlive i hi hr)).2 x
    show g.op.eval ((g.inputs.map f).map fun i =>
        ((Circuit.mk D 0).wires (List.ofFn x)).getD i false) =
      g.op.eval (g.inputs.map fun i => ((Circuit.mk E 0).wires (inp x2 x)).getD i false)
    rw [List.map_map]
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hlen⟩ := hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    simp only at key ⊢
    rcases hop with rfl | rfl | rfl
    · congr 1
      exact List.map_congr_left (fun i hi => key i hi (Or.inl (by simp)))
    · congr 1
      exact List.map_congr_left (fun i hi => key i hi (Or.inl (by simp)))
    · rcases ins with _ | ⟨a, rest⟩
      · rfl
      · simp only [List.map_cons, eval_not]
        have := key a (by simp) (Or.inr (by simp))
        simp only [Function.comp_apply]
        rw [this]
  · exact absurd hw (NC_snoc_gt x2 E g w hgt)

lemma step_dead (x2 : List (Option (Fin 7))) (E D : List Gate) (g : Gate) (hg : FT g)
    (hdead : ¬ Live x2 E g) (hI : Inv x2 E D) : Inv x2 (E ++ [g]) D := by
  intro w hw
  rcases lt_trichotomy w (x2.length + E.length) with hlt | heq | hgt
  · obtain ⟨u, hu, hu2⟩ := hI w ((NC_snoc_lt x2 E g w hlt).mp hw)
    exact ⟨u, hu, fun x => by rw [V_snoc]; simp only [hlt, ↓reduceIte]; exact hu2 x⟩
  · subst heq
    rcases dead_cases x2 E g hg hdead with hc | ⟨b, _, hnc, hval⟩
    · exfalso
      obtain ⟨a, b, hab⟩ := hw
      apply hab
      rw [V_snoc, V_snoc]
      simp only [lt_self_iff_false, eq_self, ↓reduceIte]
      exact hc a b
    · obtain ⟨u, hu, hu2⟩ := hI b hnc
      refine ⟨u, hu, fun x => ?_⟩
      rw [V_snoc]
      simp only [lt_self_iff_false, eq_self, ↓reduceIte]
      rw [hval x]
      exact hu2 x
  · exact absurd hw (NC_snoc_gt x2 E g w hgt)

lemma main (x2 : List (Option (Fin 7))) (gates : List Gate) (hF : ∀ g ∈ gates, FT g)
    (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k (h : k < gates.length), (P k ↔ Live x2 (gates.take k) gates[k])) :
    ∀ k, k ≤ gates.length → ∃ D : List Gate, (∀ g ∈ D, FT g) ∧
      D.length ≤ ((Finset.range k).filter P).card ∧ Inv x2 (gates.take k) D := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[], by simp, by simp, by simpa using inv_zero x2⟩
  | succ k ih =>
    intro hk
    have hk' : k < gates.length := hk
    obtain ⟨D, hD, hlen, hI⟩ := ih (by omega)
    have htake := List.take_succ_eq_append_getElem hk'
    have hg : FT gates[k] := hF _ (List.getElem_mem hk')
    rw [htake]
    by_cases hl : Live x2 (gates.take k) gates[k]
    · obtain ⟨g', hg', hI'⟩ := step_live x2 (gates.take k) D gates[k] hg hl hI
      refine ⟨D ++ [g'], ?_, ?_, hI'⟩
      · intro g hg0
        rcases List.mem_append.mp hg0 with h | h
        · exact hD g h
        · rw [List.mem_singleton] at h
          subst h; exact hg'
      · have hPk : P k := (hP k hk').mpr hl
        rw [Finset.range_add_one, Finset.filter_insert]
        simp only [hPk, ↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp)]
        simp only [List.length_append, List.length_singleton]
        omega
    · have hPk : ¬ P k := fun h => hl ((hP k hk').mp h)
      refine ⟨D, hD, ?_, step_dead x2 _ D _ hg hl hI⟩
      rw [Finset.range_add_one, Finset.filter_insert]
      simp only [hPk, ↓reduceIte]
      exact hlen


lemma final (x1 : Circuit) (x2 : List (Option (Fin 7))) (hF : FanInTwo x1)
    (hnc : ∃ a b : Fin 7 → Bool, x1.eval (inp x2 a) ≠ x1.eval (inp x2 b)) :
    ∃ S : Finset (Fin x1.gates.length),
      (∀ k ∈ S, Live x2 (x1.gates.take k) (x1.gates.get k)) ∧
        HasCircuitSize 7 (fun x => x1.eval (inp x2 x)) S.card := by
  classical
  obtain ⟨a, b, hab⟩ := hnc
  let P : ℕ → Prop := fun k =>
    ∃ h : k < x1.gates.length, Live x2 (x1.gates.take k) (x1.gates.get ⟨k, h⟩)
  have hP : ∀ k (h : k < x1.gates.length), (P k ↔ Live x2 (x1.gates.take k) x1.gates[k]) := by
    intro k h
    exact ⟨fun ⟨_, hx⟩ => hx, fun hl => ⟨h, hl⟩⟩
  obtain ⟨D, hD, hlen, hI⟩ :=
    main x2 x1.gates (fun g hg => hF g hg) P hP x1.gates.length le_rfl
  rw [List.take_length] at hI
  obtain ⟨u, hu, hu2⟩ := hI x1.output ⟨a, b, hab⟩
  have hs := Fin.sum_univ_eq_sum_range (fun k : ℕ => if P k then 1 else 0) x1.gates.length
  have hc : ((Finset.range x1.gates.length).filter P).card =
      (Finset.univ.filter fun k : Fin x1.gates.length =>
        Live x2 (x1.gates.take k) (x1.gates.get k)).card := by
    rw [Finset.card_filter, Finset.card_filter, ← hs]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : Live x2 (x1.gates.take i) (x1.gates.get i)
    · have h' : P i := ⟨i.2, h⟩
      simp only [h', h, ↓reduceIte]
    · have h' : ¬ P i := fun ⟨_, hx⟩ => h hx
      simp only [h', h, ↓reduceIte]
  refine ⟨Finset.univ.filter fun k : Fin x1.gates.length =>
      Live x2 (x1.gates.take k) (x1.gates.get k),
    fun k hk => (Finset.mem_filter.mp hk).2,
    ⟨⟨D, u⟩, fun g hg => hD g hg, hlen.trans hc.le, fun x => ?_⟩⟩
  exact hu2 x

end PEqualNP.Outside.L_meta_3126

theorem PEqualNP.Outside.L_meta_3126 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Option (Fin (7 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x1 →     have x4 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x4 : Fin (7 : ℕ) → Bool) => List.map (fun (x5 : Option (Fin (7 : ℕ))) => x5.elim Bool.false x4) x2;     have x5 : Fin x1.gates.length → Prop := fun (x5 : Fin x1.gates.length) =>       have x6 : PEqualNP.CircuitLowerBounds.Gate := x1.gates.get x5;       ∀ x7 ∈ x6.inputs, x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∨ x6.inputs[(0 : ℕ)]? = Option.some x7 → ∃ (x10 : Fin (7 : ℕ) → Bool) (x11 : Fin (7 : ℕ) → Bool), ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x10)).getD x7 Bool.false ≠ ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x11)).getD x7 Bool.false;     (∃ (x6 : Fin (7 : ℕ) → Bool) (x7 : Fin (7 : ℕ) → Bool), x1.eval (x4 x6) ≠ x1.eval (x4 x7)) → ∃ (x7 : Finset (Fin x1.gates.length)), (∀ x8 ∈ x7, x5 x8) ∧ PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x8 : Fin (7 : ℕ) → Bool) => x1.eval (x4 x8)) x7.card := by
  intro x1 x2 hF x4 x5 hnc
  exact PEqualNP.Outside.L_meta_3126.final x1 x2 hF hnc
