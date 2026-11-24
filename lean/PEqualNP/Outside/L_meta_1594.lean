import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1594

open PEqualNP.CircuitLowerBounds

-- Wire evaluation.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp only [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

-- The value of wire w (false if there is no such wire) after all gates are evaluated.
def value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

lemma eval_eq {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = value gs x w := rfl

lemma value_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    value gs x p = x p := by
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [value, run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma value_missing {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : value gs x w = false :=
  List.getD_eq_default _ _ (by simpa [run_length] using hw)

-- A wire does not depend on later gates.
lemma value_take {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j w : ℕ)
    (hj : j ≤ gs.length) (hw : w < n + j) : value (gs.take j) x w = value gs x w := by
  have h : run gs (List.ofFn x) = run (gs.drop j) (run (gs.take j) (List.ofFn x)) := by
    rw [← run_append, List.take_append_drop]
  have hlen : w < (run (gs.take j) (List.ofFn x)).length := by
    simp only [run_length, List.length_ofFn, List.length_take]
    omega
  unfold value
  rw [h]
  exact (run_getD _ _ w hlen).symm

-- What a gate at wire w reads when it names wire r.
def rd {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w r : ℕ) : Bool :=
  if r < w then value gs x r else false

lemma rd_true {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w r : ℕ) :
    rd gs x w r = true ↔ r < w ∧ value gs x r = true := by
  unfold rd; split_ifs with h <;> simp [h]

lemma value_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (g : Fin gs.length) :
    value gs x (n + (g : ℕ)) =
      (gs.get g).op.eval ((gs.get g).inputs.map (rd gs x (n + (g : ℕ)))) := by
  have hj : (g : ℕ) < gs.length := g.isLt
  have hread : ∀ r, (run (gs.take g) (List.ofFn x)).getD r false = rd gs x (n + (g : ℕ)) r := by
    intro r
    unfold rd
    split_ifs with hr
    · exact value_take gs x g r hj.le hr
    · exact List.getD_eq_default _ _ (by simp [run_length]; omega)
  have hlen : (run (gs.take g) (List.ofFn x)).length = n + (g : ℕ) := by
    simp [run_length]
  have hs : run gs (List.ofFn x) =
      run (gs.get g :: gs.drop (g + 1)) (run (gs.take g) (List.ofFn x)) := by
    rw [← run_append, List.get_eq_getElem, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  rw [value, hs, run_cons, run_getD _ _ _ (by simp [hlen]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.sub_self, List.getD_cons_zero]
  congr 2
  funext r
  exact hread r

lemma value_or {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (g : Fin gs.length)
    (hop : (gs.get g).op = GateOp.or) :
    value gs x (n + (g : ℕ)) = true ↔
      ∃ r ∈ (gs.get g).inputs, rd gs x (n + (g : ℕ)) r = true := by
  rw [value_gate, hop]
  simp [GateOp.eval]

lemma value_and {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (g : Fin gs.length)
    (hop : (gs.get g).op = GateOp.and) :
    value gs x (n + (g : ℕ)) = true ↔
      ∀ r ∈ (gs.get g).inputs, rd gs x (n + (g : ℕ)) r = true := by
  rw [value_gate, hop]
  simp [GateOp.eval]

-- Every wire is an input, a gate, or missing.
lemma wire_cases (n : ℕ) (gs : List Gate) (w : ℕ) :
    (∃ v : Fin n, w = v) ∨ (∃ g : Fin gs.length, w = n + (g : ℕ)) ∨ n + gs.length ≤ w := by
  by_cases h1 : w < n
  · exact Or.inl ⟨⟨w, h1⟩, rfl⟩
  by_cases h2 : w < n + gs.length
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp; omega⟩)
  · exact Or.inr (Or.inr (by omega))

lemma value_mono {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or))
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value gs x w = true → value gs y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have hr : ∀ r, rd gs x w r = true → rd gs y w r = true := by
      intro r
      rw [rd_true, rd_true]
      exact fun h => ⟨h.1, ih r h.1 h.2⟩
    rcases wire_cases n gs w with ⟨v, rfl⟩ | ⟨g, rfl⟩ | h
    · rw [value_input, value_input]; exact hxy v
    · rcases hG _ (List.get_mem gs g) with hop | hop
      · rw [value_and _ _ _ hop, value_and _ _ _ hop]
        exact fun h r hm => hr r (h r hm)
      · rw [value_or _ _ _ hop, value_or _ _ _ hop]
        rintro ⟨r, hm, h⟩
        exact ⟨r, hm, hr r h⟩
    · rw [value_missing _ _ _ h]; simp

-- Counting edges of a connected graph.

lemma edge_count {V L : Type} [Fintype V] [Nonempty V] (J : Finset L) (f h : L → V)
    (hc : ∀ u v : V, (SimpleGraph.fromRel
      (fun a b : V => ∃ g ∈ J, a = f g ∧ b = h g)).Reachable u v) :
    Fintype.card V ≤ J.card + 1 := by
  classical
  set G := SimpleGraph.fromRel (fun a b : V => ∃ g ∈ J, a = f g ∧ b = h g) with hGdef
  have hconn : G.Connected := ⟨hc⟩
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have hsub : G.edgeSet ⊆ ((J.image (fun g => s(f g, h g)) : Finset (Sym2 V)) : Set (Sym2 V)) := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rw [SimpleGraph.mem_edgeSet, hGdef, SimpleGraph.fromRel_adj] at he
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      rcases he.2 with ⟨g, hg, rfl, rfl⟩ | ⟨g, hg, rfl, rfl⟩
      · exact ⟨g, hg, rfl⟩
      · exact ⟨g, hg, Sym2.eq_swap⟩
  have h2 : Nat.card G.edgeSet ≤ J.card := by
    refine le_trans (Nat.card_mono (Finset.finite_toSet _) hsub) ?_
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact Finset.card_image_le
  rw [Nat.card_eq_fintype_card] at h1
  omega

noncomputable def pick {V : Type} [Nonempty V] (A : Set V) : V :=
  open Classical in if h : A.Nonempty then h.some else Classical.arbitrary V

lemma pick_mem {V : Type} [Nonempty V] (A : Set V) (h : A.Nonempty) : pick A ∈ A := by
  unfold pick
  rw [dite_eq_left h]
  exact h.some_mem

-- The rows (points of V) at which a gate at wire w reads true on wire r.
def rows {n : ℕ} {V : Type} (gs : List Gate) (y : V → Fin n → Bool) (w r : ℕ) : Set V :=
  {p | rd gs (y p) w r = true}

-- One line. The zero assignment is x, the one assignments are y p.
-- An input that is false at x is true at no more than one y p.
-- A wire false at x and true at every y p needs card V - 1 charged OR gates.
theorem line_charge {n : ℕ} {V : Type} [Fintype V] [Nonempty V] (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (y : V → Fin n → Bool)
    (hin : ∀ v : Fin n, x v = false → ∀ p p', y p v = true → y p' v = true → p = p')
    (o : ℕ) (hlow : value gs x o = false) (hone : ∀ p, value gs (y p) o = true) :
    ∃ J : Finset (Fin gs.length), Fintype.card V ≤ J.card + 1 ∧
      ∀ g ∈ J, (gs.get g).op = GateOp.or ∧ value gs x (n + (g : ℕ)) = false ∧
        (∃ a b, (gs.get g).inputs = [a, b] ∧
          (a < n + (g : ℕ) ∧ ∃ p, value gs (y p) a = true) ∧
          (b < n + (g : ℕ) ∧ ∃ p, value gs (y p) b = true)) ∧
        ∃ p p', p ≠ p' ∧ value gs (y p) (n + (g : ℕ)) = true ∧
          value gs (y p') (n + (g : ℕ)) = true := by
  classical
  let A : Fin gs.length → Set V := fun g =>
    rows gs y (n + (g : ℕ)) ((gs.get g).inputs.getD 0 0)
  let B : Fin gs.length → Set V := fun g =>
    rows gs y (n + (g : ℕ)) ((gs.get g).inputs.getD 1 0)
  let J : Finset (Fin gs.length) := Finset.univ.filter (fun g =>
    (gs.get g).op = GateOp.or ∧ value gs x (n + (g : ℕ)) = false ∧
    (gs.get g).inputs.length = 2 ∧ (A g).Nonempty ∧ (B g).Nonempty ∧ pick (A g) ≠ pick (B g))
  let G : SimpleGraph V := SimpleGraph.fromRel
      (fun a b : V => ∃ g ∈ J, a = pick (A g) ∧ b = pick (B g))
  have main : ∀ w, value gs x w = false → ∀ p p', value gs (y p) w = true →
      value gs (y p') w = true → G.Reachable p p' := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw p p' hp hp'
      -- reads of one input
      have hrd : ∀ r, rd gs x w r = false → ∀ u u', rd gs (y u) w r = true →
          rd gs (y u') w r = true → G.Reachable u u' := by
        intro r hr u u' hu hu'
        rw [rd_true] at hu hu'
        refine ih r hu.1 ?_ u u' hu.2 hu'.2
        unfold rd at hr
        rwa [ite_eq_left hu.1] at hr
      rcases wire_cases n gs w with ⟨v, rfl⟩ | ⟨g, rfl⟩ | h
      · rw [value_input] at hw hp hp'
        rw [hin v hw p p' hp hp']
      · have hlen := (hG _ (List.get_mem gs g)).2
        rcases (hG _ (List.get_mem gs g)).1 with hop | hop
        · rw [value_and _ _ _ hop] at hp hp'
          have : ¬ value gs x (n + (g : ℕ)) = true := by simp [hw]
          rw [value_and _ _ _ hop] at this
          push Not at this
          obtain ⟨r, hm, hr⟩ := this
          exact hrd r (by simpa using hr) p p' (hp r hm) (hp' r hm)
        · have hlowr : ∀ r ∈ (gs.get g).inputs, rd gs x (n + (g : ℕ)) r = false := by
            intro r hm
            by_contra hcon
            have : value gs x (n + (g : ℕ)) = true :=
              (value_or _ _ _ hop).2 ⟨r, hm, by simpa using hcon⟩
            rw [hw] at this
            exact absurd this (by simp)
          obtain ⟨r, hm, hr⟩ := (value_or _ _ _ hop).1 hp
          obtain ⟨r', hm', hr'⟩ := (value_or _ _ _ hop).1 hp'
          by_cases hrr : r = r'
          · subst hrr
            exact hrd r (hlowr r hm) p p' hr hr'
          -- two different inputs, so the list is a pair
          have key : ∀ a b, (gs.get g).inputs = [a, b] →
              ∀ u u', rd gs (y u) (n + (g : ℕ)) a = true →
                rd gs (y u') (n + (g : ℕ)) b = true → G.Reachable u u' := by
            intro a b hab u u' hu hu'
            have hA : A g = rows gs y (n + (g : ℕ)) a := by simp only [A, hab]; rfl
            have hB : B g = rows gs y (n + (g : ℕ)) b := by simp only [B, hab]; rfl
            have hAne : (A g).Nonempty := by rw [hA]; exact ⟨u, hu⟩
            have hBne : (B g).Nonempty := by rw [hB]; exact ⟨u', hu'⟩
            have ha : rd gs (y (pick (A g))) (n + (g : ℕ)) a = true := by
              have := pick_mem _ hAne
              rw [hA] at this ⊢
              exact this
            have hb : rd gs (y (pick (B g))) (n + (g : ℕ)) b = true := by
              have := pick_mem _ hBne
              rw [hB] at this ⊢
              exact this
            have e1 : G.Reachable u (pick (A g)) :=
              hrd a (hlowr a (by rw [hab]; simp)) _ _ hu ha
            have e2 : G.Reachable (pick (B g)) u' :=
              hrd b (hlowr b (by rw [hab]; simp)) _ _ hb hu'
            have e3 : G.Reachable (pick (A g)) (pick (B g)) := by
              by_cases hne : pick (A g) = pick (B g)
              · rw [hne]
              · refine SimpleGraph.Adj.reachable ?_
                refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨g, ?_, rfl, rfl⟩⟩
                refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hop, hw, ?_, hAne, hBne, hne⟩
                rw [hab]; rfl
            exact (e1.trans e3).trans e2
          have hpair : ∃ a b, (gs.get g).inputs = [a, b] := by
            generalize (gs.get g).inputs = l at hm hm' hlen
            match l, hm, hm', hlen with
            | [], hm, _, _ => simp at hm
            | [a], hm, hm', _ =>
              simp only [List.mem_singleton] at hm hm'
              exact absurd (hm.trans hm'.symm) hrr
            | [a, b], _, _, _ => exact ⟨a, b, rfl⟩
            | a :: b :: c :: t, _, _, hlen => simp at hlen
          obtain ⟨a, b, hab⟩ := hpair
          have hma : r = a ∨ r = b := by rw [hab] at hm; simpa using hm
          have hma' : r' = a ∨ r' = b := by rw [hab] at hm'; simpa using hm'
          rcases hma with rfl | rfl <;> rcases hma' with rfl | rfl
          · exact absurd rfl hrr
          · exact key _ _ hab p p' hr hr'
          · exact (key _ _ hab p' p hr' hr).symm
          · exact absurd rfl hrr
      · rw [value_missing _ _ _ h] at hp
        exact absurd hp (by simp)
  refine ⟨J, ?_, ?_⟩
  · exact edge_count J (fun g => pick (A g)) (fun g => pick (B g))
      (fun u v => main o hlow u v (hone u) (hone v))
  · intro g hg
    obtain ⟨-, hop, hl, hlen, hAne, hBne, hne⟩ := Finset.mem_filter.1 hg
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
    have hA : A g = rows gs y (n + (g : ℕ)) a := by simp only [A, hab]; rfl
    have hB : B g = rows gs y (n + (g : ℕ)) b := by simp only [B, hab]; rfl
    have ha : rd gs (y (pick (A g))) (n + (g : ℕ)) a = true := by
      have := pick_mem _ hAne
      rw [hA] at this ⊢
      exact this
    have hb : rd gs (y (pick (B g))) (n + (g : ℕ)) b = true := by
      have := pick_mem _ hBne
      rw [hB] at this ⊢
      exact this
    have ha' := (rd_true _ _ _ _).1 ha
    have hb' := (rd_true _ _ _ _).1 hb
    refine ⟨hop, hl, ⟨a, b, hab, ⟨ha'.1, _, ha'.2⟩, ⟨hb'.1, _, hb'.2⟩⟩, _, _, hne, ?_, ?_⟩
    · exact (value_or _ _ _ hop).2 ⟨a, by rw [hab]; simp, ha⟩
    · exact (value_or _ _ _ hop).2 ⟨b, by rw [hab]; simp, hb⟩

-- The charge set of line i, with each charged gate false at the complement of S i
-- and true at two different rows of line i.

-- Replacing gate t by the constant true gate changes nothing on inputs where gate t is true.
lemma value_set {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : value gs x (n + t) = true) (w : ℕ) :
    value (gs.set t ⟨GateOp.and, []⟩) x w = value gs x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_cases n gs w with ⟨v, rfl⟩ | ⟨g, rfl⟩ | h
    · rw [value_input, value_input]
    · have hg' : (g : ℕ) < (gs.set t ⟨GateOp.and, []⟩).length := by simp
      have e := value_gate (gs.set t ⟨GateOp.and, []⟩) x ⟨g, hg'⟩
      simp only at e
      by_cases hgt : t = (g : ℕ)
      · obtain ⟨k, hk⟩ := g
        simp only at hgt
        subst hgt
        simp only at e ⊢
        rw [e, ht]
        simp [List.get_eq_getElem, GateOp.eval]
      · rw [e, value_gate gs x g]
        have hget : (gs.set t ⟨GateOp.and, []⟩).get ⟨g, hg'⟩ = gs.get g := by
          simp [List.get_eq_getElem, List.getElem_set_ne hgt]
        rw [hget]
        congr 2
        funext r
        unfold rd
        split_ifs with hr
        · exact ih r hr
        · rfl
    · rw [value_missing gs x w h, value_missing _ x w (by simpa using h)]

def ind {n : ℕ} (y : Finset (Fin n)) : Fin n → Bool := fun q => decide (q ∈ y)

def single {n : ℕ} (s : Fin n) : Fin n → Bool := fun q => decide (q = s)

def Mono {n : ℕ} (v : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ p, x p = true → y p = true) → v x = true → v y = true

lemma Mono.ind {n : ℕ} {v : (Fin n → Bool) → Bool} (hv : Mono v) {y z : Finset (Fin n)}
    (h : y ⊆ z) (hy : v (ind y) = true) : v (ind z) = true :=
  hv _ _ (fun p hp => by
    simp only [L_meta_1594.ind, decide_eq_true_eq] at hp ⊢
    exact h hp) hy

def Conn {V : Type} (E : Finset (V × V)) (a b : V) : Prop :=
  (SimpleGraph.fromRel (fun a b : V => ∃ g ∈ E, a = g.1 ∧ b = g.2)).Reachable a b

lemma Conn.mono {V : Type} {E F : Finset (V × V)} (h : E ⊆ F) {a b : V} (hab : Conn E a b) :
    Conn F a b := by
  refine SimpleGraph.Reachable.mono ?_ hab
  intro u v huv
  rw [SimpleGraph.fromRel_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with ⟨g, hg, h1, h2⟩ | ⟨g, hg, h1, h2⟩
  · exact Or.inl ⟨g, h hg, h1, h2⟩
  · exact Or.inr ⟨g, h hg, h1, h2⟩

lemma Conn.edge {V : Type} {E : Finset (V × V)} {a b : V} (h : (a, b) ∈ E) : Conn E a b := by
  by_cases hab : a = b
  · subst hab; exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hab, Or.inl ⟨(a, b), h, rfl, rfl⟩⟩

-- A wire function v is represented by the point set Q, up to the fixed points X and edges E.
def Good {n : ℕ} (A X : Finset (Fin n)) (E : Finset (A × A)) (v : (Fin n → Bool) → Bool)
    (Q : Finset (Fin n)) : Prop :=
  (∀ y : Finset (Fin n), (∀ s ∈ y, s ∉ A) → (∃ s ∈ Q, s ∈ y) → v (ind (y ∪ X)) = true) ∧
  (∀ p ∈ A, v (single p) = true → p ∈ Q) ∧
  (Q ⊆ A → ∀ a b : A, (a : Fin n) ∈ Q → (b : Fin n) ∈ Q → Conn E a b)

lemma Good.mono {n : ℕ} {A X X' : Finset (Fin n)} {E E' : Finset (A × A)}
    {v : (Fin n → Bool) → Bool} {Q : Finset (Fin n)} (hv : Mono v) (hX : X ⊆ X') (hE : E ⊆ E')
    (h : Good A X E v Q) : Good A X' E' v Q :=
  ⟨fun y hy hq => hv.ind (Finset.union_subset_union (Finset.Subset.refl y) hX) (h.1 y hy hq),
    h.2.1, fun hQ a b ha hb => (h.2.2 hQ a b ha hb).mono hE⟩

lemma Good.congr {n : ℕ} {A X : Finset (Fin n)} {E : Finset (A × A)}
    {v v' : (Fin n → Bool) → Bool} {Q : Finset (Fin n)} (hv : ∀ x, v x = v' x)
    (h : Good A X E v Q) : Good A X E v' Q := by
  have : v = v' := funext hv
  rwa [← this]

lemma good_or {n : ℕ} {A X : Finset (Fin n)} {E : Finset (A × A)}
    {u v : (Fin n → Bool) → Bool} {P Q : Finset (Fin n)}
    (hu : Good A X E u P) (hv : Good A X E v Q) :
    ∃ E' : Finset (A × A), E ⊆ E' ∧ E'.card ≤ E.card + 1 ∧
      Good A X E' (fun x => u x || v x) (P ∪ Q) := by
  classical
  have J1 : ∀ y : Finset (Fin n), (∀ s ∈ y, s ∉ A) → (∃ s ∈ P ∪ Q, s ∈ y) →
      (u (ind (y ∪ X)) || v (ind (y ∪ X))) = true := by
    rintro y hy ⟨s, hs, hsy⟩
    rw [Bool.or_eq_true]
    rcases Finset.mem_union.mp hs with h | h
    · exact Or.inl (hu.1 y hy ⟨s, h, hsy⟩)
    · exact Or.inr (hv.1 y hy ⟨s, h, hsy⟩)
  have J2 : ∀ p ∈ A, (u (single p) || v (single p)) = true → p ∈ P ∪ Q := by
    intro p hp h
    rw [Bool.or_eq_true] at h
    rw [Finset.mem_union]
    exact h.imp (hu.2.1 p hp) (hv.2.1 p hp)
  by_cases hex : ∃ a b : A, (a : Fin n) ∈ P ∧ (b : Fin n) ∈ Q
  · obtain ⟨a, b, ha, hb⟩ := hex
    refine ⟨insert (a, b) E, Finset.subset_insert _ _, Finset.card_insert_le _ _, J1, J2, ?_⟩
    intro hPQ c d hc hd
    have hP : P ⊆ A := Finset.subset_union_left.trans hPQ
    have hQ : Q ⊆ A := Finset.subset_union_right.trans hPQ
    have hE : E ⊆ insert (a, b) E := Finset.subset_insert _ _
    have hab : Conn (insert (a, b) E) a b := Conn.edge (Finset.mem_insert_self _ _)
    have key : ∀ c : A, (c : Fin n) ∈ P ∪ Q → Conn (insert (a, b) E) a c := by
      intro c hc
      rcases Finset.mem_union.mp hc with h | h
      · exact (hu.2.2 hP a c ha h).mono hE
      · exact SimpleGraph.Reachable.trans hab ((hv.2.2 hQ b c hb h).mono hE)
    exact SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm (key c hc)) (key d hd)
  · refine ⟨E, Finset.Subset.refl _, Nat.le_succ _, J1, J2, ?_⟩
    intro hPQ c d hc hd
    have hP : P ⊆ A := Finset.subset_union_left.trans hPQ
    have hQ : Q ⊆ A := Finset.subset_union_right.trans hPQ
    rcases Finset.mem_union.mp hc with h | h <;> rcases Finset.mem_union.mp hd with h' | h'
    · exact hu.2.2 hP c d h h'
    · exact absurd ⟨c, d, h, h'⟩ hex
    · exact absurd ⟨d, c, h', h⟩ hex
    · exact hv.2.2 hQ c d h h'

lemma good_and {n : ℕ} {A X : Finset (Fin n)} {E : Finset (A × A)}
    {u v : (Fin n → Bool) → Bool} {P Q : Finset (Fin n)} (mv : Mono v)
    (hX : ∀ s ∈ X, s ∉ A) (hu : Good A X E u P) (hv : Good A X E v Q) :
    ∃ (X' : Finset (Fin n)) (R : Finset (Fin n)), X ⊆ X' ∧ (∀ s ∈ X', s ∉ A) ∧
      X'.card ≤ X.card + 1 ∧ Good A X' E (fun x => u x && v x) R := by
  classical
  have J2 : ∀ p ∈ A, (u (single p) && v (single p)) = true → p ∈ P ∧ p ∈ Q := by
    intro p hp h
    rw [Bool.and_eq_true] at h
    exact ⟨hu.2.1 p hp h.1, hv.2.1 p hp h.2⟩
  by_cases hP : P ⊆ A
  · refine ⟨X, P, Finset.Subset.refl _, hX, Nat.le_succ _, ?_, fun p hp h => (J2 p hp h).1,
      hu.2.2⟩
    rintro y hy ⟨s, hs, hsy⟩
    exact absurd (hP hs) (hy s hsy)
  · obtain ⟨s, hs, hsA⟩ := Finset.not_subset.mp hP
    refine ⟨insert s X, Q, Finset.subset_insert _ _, ?_, Finset.card_insert_le _ _, ?_,
      fun p hp h => (J2 p hp h).2, hv.2.2⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | h
      · exact hsA
      · exact hX r h
    · intro y hy hq
      rw [Bool.and_eq_true]
      refine ⟨?_, mv.ind (Finset.union_subset_union (Finset.Subset.refl y)
        (Finset.subset_insert s X)) (hv.1 y hy hq)⟩
      have := hu.1 (insert s y) (by
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | h
        · exact hsA
        · exact hy r h) ⟨s, hs, Finset.mem_insert_self _ _⟩
      have e : insert s y ∪ X = y ∪ insert s X := by
        ext r; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rwa [e] at this

def Cnt {n : ℕ} (gs : List Gate) (A : Finset (Fin n)) (h : Fin gs.length) : Prop :=
  (∀ s : Fin n, value gs (single s) (n + (h : ℕ)) = true → s ∈ A) ∧
    2 ≤ (Finset.univ.filter (fun s : Fin n => value gs (single s) (n + (h : ℕ)) = true)).card

open Classical in
theorem sweep {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A : Finset (Fin n)) (s0 : Fin n) (hs0 : s0 ∉ A) : ∀ j, j ≤ gs.length →
    ∃ (X : Finset (Fin n)) (E : Finset (A × A)) (P : ℕ → Finset (Fin n)),
      (∀ s ∈ X, s ∉ A) ∧
      X.card + E.card ≤
        (Finset.univ.filter (fun h : Fin gs.length => (h : ℕ) < j ∧ Cnt gs A h)).card ∧
      ∀ w, w < n + j → Good A X E (fun x => value gs x w) (P w) := by
  have hmono : ∀ w, Mono (fun x : Fin n → Bool => value gs x w) := fun w x y hxy h =>
    value_mono gs (fun g hg => (hG g hg).1) x y hxy w h
  have hrmono : ∀ W r, Mono (fun x : Fin n → Bool => rd gs x W r) := by
    intro W r x y hxy h
    simp only [rd_true] at h ⊢
    exact ⟨h.1, hmono r x y hxy h.2⟩
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨∅, ∅, fun w => if h : w < n then {⟨w, h⟩} else ∅, by simp, by simp, ?_⟩
    intro w hw
    have hw' : w < n := by omega
    have hval : ∀ x : Fin n → Bool, value gs x w = x ⟨w, hw'⟩ := fun x =>
      value_input gs x ⟨w, hw'⟩
    have hP : (if h : w < n then ({⟨w, h⟩} : Finset (Fin n)) else ∅) = {⟨w, hw'⟩} :=
      dite_eq_left hw'
    change Good A ∅ ∅ (fun x => value gs x w)
      (if h : w < n then ({⟨w, h⟩} : Finset (Fin n)) else ∅)
    rw [hP]
    refine ⟨?_, ?_, ?_⟩
    · rintro y hy ⟨s, hs, hsy⟩
      rw [Finset.mem_singleton] at hs
      subst hs
      change value gs _ w = true
      rw [hval]
      simp [ind, hsy]
    · intro p hp h
      change value gs _ w = true at h
      rw [hval] at h
      simp only [single, decide_eq_true_eq] at h
      rw [Finset.mem_singleton]; exact h.symm
    · intro _ a b ha hb
      rw [Finset.mem_singleton] at ha hb
      have : a = b := Subtype.ext (ha.trans hb.symm)
      subst this
      exact SimpleGraph.Reachable.refl _
  | succ j ih =>
    intro hj
    obtain ⟨X, E, P, hX, hcard, hgood⟩ := ih (by omega)
    let g : Fin gs.length := ⟨j, by omega⟩
    have hgj : (g : ℕ) = j := rfl
    -- reads of the new gate
    let R : ℕ → Finset (Fin n) := fun r => if r < n + j then P r else ∅
    have hread : ∀ r, Good A X E (fun x => rd gs x (n + j) r) (R r) := by
      intro r
      by_cases hr : r < n + j
      · have e : R r = P r := ite_eq_left hr
        rw [e]
        refine (hgood r hr).congr ?_
        intro x
        simp [rd, hr]
      · have e : R r = ∅ := ite_eq_right hr
        rw [e]
        refine ⟨by simp, ?_, by simp⟩
        intro p _ h
        simp [rd, hr] at h
    -- it is enough to find the new set, points and edges
    have finish : ∀ (X' : Finset (Fin n)) (E' : Finset (A × A)) (Q : Finset (Fin n)),
        X ⊆ X' → E ⊆ E' → (∀ s ∈ X', s ∉ A) →
        X'.card + E'.card ≤ (Finset.univ.filter
          (fun h : Fin gs.length => (h : ℕ) < j + 1 ∧ Cnt gs A h)).card →
        Good A X' E' (fun x => value gs x (n + j)) Q →
        ∃ (X : Finset (Fin n)) (E : Finset (A × A)) (P : ℕ → Finset (Fin n)),
          (∀ s ∈ X, s ∉ A) ∧
          X.card + E.card ≤ (Finset.univ.filter
            (fun h : Fin gs.length => (h : ℕ) < j + 1 ∧ Cnt gs A h)).card ∧
          ∀ w, w < n + (j + 1) → Good A X E (fun x => value gs x w) (P w) := by
      intro X' E' Q hXX hEE hX' hc hQ
      refine ⟨X', E', Function.update P (n + j) Q, hX', hc, ?_⟩
      intro w hw
      by_cases hwj : w = n + j
      · subst hwj
        rw [Function.update_self]
        exact hQ
      · rw [Function.update_of_ne hwj]
        exact (hgood w (by omega)).mono (hmono w) hXX hEE
    have hsub : (Finset.univ.filter (fun h : Fin gs.length => (h : ℕ) < j ∧ Cnt gs A h)) ⊆
        (Finset.univ.filter (fun h : Fin gs.length => (h : ℕ) < j + 1 ∧ Cnt gs A h)) := by
      intro h hh
      rw [Finset.mem_filter] at hh ⊢
      exact ⟨hh.1, by omega, hh.2.2⟩
    by_cases hC : Cnt gs A g
    · -- a counted gate pays for one new point or one new edge
      have hplus : X.card + E.card + 1 ≤ (Finset.univ.filter
          (fun h : Fin gs.length => (h : ℕ) < j + 1 ∧ Cnt gs A h)).card := by
        have hn : g ∉ (Finset.univ.filter
            (fun h : Fin gs.length => (h : ℕ) < j ∧ Cnt gs A h)) := by
          rw [Finset.mem_filter]; rintro ⟨_, h, _⟩; omega
        have hi : insert g (Finset.univ.filter
            (fun h : Fin gs.length => (h : ℕ) < j ∧ Cnt gs A h)) ⊆
            (Finset.univ.filter (fun h : Fin gs.length => (h : ℕ) < j + 1 ∧ Cnt gs A h)) := by
          intro h hh
          rcases Finset.mem_insert.mp hh with rfl | hh
          · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by omega, hC⟩
          · exact hsub hh
        have := Finset.card_le_card hi
        rw [Finset.card_insert_of_notMem hn] at this
        omega
      have hlen := (hG _ (List.get_mem gs g)).2
      rcases (hG _ (List.get_mem gs g)).1 with hop | hop
      · have hv : ∀ x : Fin n → Bool, value gs x (n + j) = true ↔
            ∀ r ∈ (gs.get g).inputs, rd gs x (n + j) r = true := fun x => value_and gs x g hop
        rcases hin : (gs.get g).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · exact absurd (hC.1 s0 ((hv _).2 (fun r hr => by rw [hin] at hr; simp at hr))) hs0
        · refine finish X E (R a) (Finset.Subset.refl _) (Finset.Subset.refl _) hX (by omega)
            ((hread a).congr ?_)
          intro x
          rw [Bool.eq_iff_iff, hv x, hin]; simp
        · obtain ⟨X', Q, hXX, hX', hc, hgd⟩ := good_and (hrmono (n + j) b) hX (hread a) (hread b)
          refine finish X' E Q hXX (Finset.Subset.refl _) hX' (by omega) (hgd.congr ?_)
          intro x
          rw [Bool.eq_iff_iff, hv x, hin]; simp
        · rw [hin] at hlen; simp at hlen
      · have hv : ∀ x : Fin n → Bool, value gs x (n + j) = true ↔
            ∃ r ∈ (gs.get g).inputs, rd gs x (n + j) r = true := fun x => value_or gs x g hop
        rcases hin : (gs.get g).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · refine finish X E ∅ (Finset.Subset.refl _) (Finset.Subset.refl _) hX (by omega)
            ⟨by simp, ?_, by simp⟩
          intro p _ h
          change value gs _ (n + j) = true at h
          rw [hv, hin] at h
          simp at h
        · refine finish X E (R a) (Finset.Subset.refl _) (Finset.Subset.refl _) hX (by omega)
            ((hread a).congr ?_)
          intro x
          rw [Bool.eq_iff_iff, hv x, hin]; simp
        · obtain ⟨E', hEE, hc, hgd⟩ := good_or (hread a) (hread b)
          refine finish X E' _ (Finset.Subset.refl _) hEE hX (by omega) (hgd.congr ?_)
          intro x
          rw [Bool.eq_iff_iff, hv x, hin]; simp
        · rw [hin] at hlen; simp at hlen
    · -- any other gate is kept as the set of its single points
      refine finish X E (Finset.univ.filter (fun s : Fin n => value gs (single s) (n + j) = true))
        (Finset.Subset.refl _) (Finset.Subset.refl _) hX
        (hcard.trans (Finset.card_le_card hsub)) ⟨?_, ?_, ?_⟩
      · rintro y hy ⟨s, hs, hsy⟩
        rw [Finset.mem_filter] at hs
        refine hmono (n + j) (single s) _ ?_ hs.2
        intro p hp
        simp only [single, decide_eq_true_eq] at hp
        subst hp
        simp [ind, hsy]
      · intro p _ h
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      · intro hQ a b ha hb
        have h1 : ¬ 2 ≤ (Finset.univ.filter
            (fun s : Fin n => value gs (single s) (n + j) = true)).card := by
          intro h2
          refine hC ⟨?_, h2⟩
          intro s hs
          exact hQ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
        have : a = b := Subtype.ext (Finset.card_le_one.mp (by omega) _ ha _ hb)
        subst this
        exact SimpleGraph.Reachable.refl _

open Classical in
theorem count {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A : Finset (Fin n)) (k o : ℕ) (hk : 2 ≤ k)
    (hone : ∀ p ∈ A, value gs (single p) o = true)
    (hlow : ∀ y : Finset (Fin n), y.card < k → (∀ s ∈ y, s ∉ A) → value gs (ind y) o = false) :
    min k A.card ≤ (Finset.univ.filter (fun h : Fin gs.length => Cnt gs A h)).card + 1 := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp
  have ho : o < n + gs.length := by
    by_contra h
    have := hone p0 hp0
    rw [value_missing gs _ o (by omega)] at this
    exact absurd this (by simp)
  by_cases hall : ∃ s0, s0 ∉ A
  · obtain ⟨s0, hs0⟩ := hall
    obtain ⟨X, E, P, hX, hcard, hgood⟩ := sweep gs hG A s0 hs0 gs.length le_rfl
    have hg := hgood o ho
    have hle : X.card + E.card ≤ (Finset.univ.filter (fun h : Fin gs.length => Cnt gs A h)).card :=
      hcard.trans (Finset.card_le_card (by
        intro h hh
        rw [Finset.mem_filter] at hh ⊢
        exact ⟨hh.1, hh.2.2⟩))
    by_cases hXk : X.card + 1 < k
    · have hPA : P o ⊆ A := by
        intro s hs
        by_contra hsA
        have h1 := hg.1 {s} (by
          intro r hr
          rw [Finset.mem_singleton] at hr
          rw [hr]; exact hsA) ⟨s, hs, Finset.mem_singleton_self s⟩
        have h2 := hlow ({s} ∪ X) (by
          have := Finset.card_union_le {s} X
          rw [Finset.card_singleton] at this
          omega) (by
          intro r hr
          rcases Finset.mem_union.mp hr with h | h
          · rw [Finset.mem_singleton] at h
            rw [h]; exact hsA
          · exact hX r h)
        simp only at h1
        rw [h2] at h1
        exact absurd h1 (by simp)
      have : Nonempty A := ⟨⟨p0, hp0⟩⟩
      have hc := edge_count E (fun e : A × A => e.1) (fun e : A × A => e.2) (by
        intro a b
        exact hg.2.2 hPA a b (hg.2.1 a a.2 (hone a a.2)) (hg.2.1 b b.2 (hone b b.2)))
      rw [Fintype.card_coe] at hc
      omega
    · omega
  · -- every point is in A: one zero input is enough
    have hall' : ∀ s, s ∈ A := fun s => by_contra fun h => hall ⟨s, h⟩
    have : Nonempty A := ⟨⟨p0, hp0⟩⟩
    obtain ⟨J, hJ, hJg⟩ := line_charge (V := A) gs hG (ind ∅) (fun p => single p.1)
      (by
        intro v _ p p' h h'
        simp only [single, decide_eq_true_eq] at h h'
        exact Subtype.ext (h.symm.trans h'))
      o (hlow ∅ (by simp; omega) (by simp)) (fun p => hone p.1 p.2)
    rw [Fintype.card_coe] at hJ
    have : J ⊆ Finset.univ.filter (fun h : Fin gs.length => Cnt gs A h) := by
      intro g hg
      obtain ⟨_, _, _, p, p', hne, h1, h2⟩ := hJg g hg
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun s _ => hall' s, ?_⟩
      refine Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨p.1, ?_, p'.1, ?_, ?_⟩)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
      · exact fun h => hne (Subtype.ext h)
    have := Finset.card_le_card this
    omega

open Classical in
theorem main {N M : ℕ} (A : Fin M → Finset (Fin N)) (D : Circuit) (u : Fin M → ℕ) (t : ℕ)
    (Y : Finset (Fin N))
    (hG : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hN : ∀ l : Fin D.gates.length, (D.gates.get l).op = GateOp.not → (l : ℕ) = t)
    (hu : ∀ (i : Fin M) (z : Fin N → Bool), value D.gates z (u i) =
      decide (∃ s ∈ A i, z s = true))
    (hw : ∀ z : Fin N → Bool, (Finset.univ.filter (fun v : Fin N => z v = true)).card < Y.card →
      value D.gates z (N + t) = true)
    (hY : 2 ≤ Y.card) (i : Fin M) :
    min Y.card (A i).card ≤
      (Finset.univ.filter (fun h : Fin D.gates.length => Cnt D.gates (A i) h)).card + 1 := by
  set gs' := D.gates.set t ⟨GateOp.and, []⟩ with hgs'
  have hlen : gs'.length = D.gates.length := by simp [hgs']
  have hind : ∀ y : Finset (Fin N),
      (Finset.univ.filter (fun v : Fin N => ind y v = true)) = y := by
    intro y; ext v; simp [ind]
  have hsingle : ∀ s : Fin N, (single s : Fin N → Bool) = ind {s} := by
    intro s; funext q; simp [single, ind]
  have hagree : ∀ (y : Finset (Fin N)) (w : ℕ), y.card < Y.card →
      value gs' (ind y) w = value D.gates (ind y) w := by
    intro y w hy
    exact value_set D.gates (ind y) t (hw _ (by rw [hind]; exact hy)) w
  have hagree1 : ∀ (s : Fin N) (w : ℕ), value gs' (single s) w = value D.gates (single s) w := by
    intro s w
    rw [hsingle]
    exact hagree {s} w (by rw [Finset.card_singleton]; omega)
  have hG' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
    have hl' : l < D.gates.length := by rw [← hlen]; exact hl
    by_cases hlt : t = l
    · subst hlt
      simp [hgs']
    · have e : gs'[l] = D.gates[l] := by simp [hgs', List.getElem_set_ne hlt]
      rw [e]
      obtain ⟨h1, h2⟩ := hG _ (List.getElem_mem hl')
      refine ⟨?_, h2⟩
      rcases h1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hN ⟨l, hl'⟩ (by simpa using h)).symm hlt
  have hmain := count gs' hG' (A i) Y.card (u i) hY
    (by
      intro p hp
      rw [hagree1, hu]
      exact decide_eq_true ⟨p, hp, by simp [single]⟩)
    (by
      intro y hy hyA
      rw [hagree y _ hy, hu]
      refine decide_eq_false ?_
      rintro ⟨s, hs, hsy⟩
      simp only [ind, decide_eq_true_eq] at hsy
      exact hyA s hsy hs)
  refine hmain.trans (Nat.add_le_add_right ?_ 1)
  refine Finset.card_le_card_of_injOn (fun h => Fin.cast hlen h) ?_ ?_
  · intro h hh
    have hh' := (Finset.mem_filter.mp (Finset.mem_coe.mp hh)).2
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    unfold Cnt at hh' ⊢
    simp only [hagree1] at hh'
    simpa using hh'
  · intro a _ b _ hab
    exact Fin.cast_injective hlen hab

end PEqualNP.Outside.L_meta_1594

theorem PEqualNP.Outside.L_meta_1594 : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → 2 ≤ Y.card → ∀ b4 : Fin M, min Y.card (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 = s3)))).getD (N + h1) false = true)).card)).card + 1 := by
  intro _ _ N M A D u t Y _ hG hN hu hw _ hY i
  have h := PEqualNP.Outside.L_meta_1594.main A D u t Y hG hN hu hw hY i
  refine h.trans (le_of_eq ?_)
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl
