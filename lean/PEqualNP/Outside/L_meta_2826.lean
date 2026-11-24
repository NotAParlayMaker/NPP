import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2826

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def lit (sig : List (ℕ × Bool)) (i : ℕ) : ℕ × Bool := sig.getD i (10, false)

def sand (c1 c2 : Bool) (a b : ℕ) : BinaryGate := ⟨fun u v => u == c1 && v == c2, a, b⟩

def tr (acc : List (ℕ × Bool) × List BinaryGate) (g : Gate) :
    List (ℕ × Bool) × List BinaryGate :=
  match g.op, g.inputs with
  | GateOp.not, [] => (acc.1 ++ [(10, true)], acc.2)
  | GateOp.not, a :: _ => (acc.1 ++ [((lit acc.1 a).1, !(lit acc.1 a).2)], acc.2)
  | GateOp.and, [] => (acc.1 ++ [(10, true)], acc.2)
  | GateOp.and, [a] => (acc.1 ++ [lit acc.1 a], acc.2)
  | GateOp.and, [a, b] => (acc.1 ++ [(11 + acc.2.length, false)],
      acc.2 ++ [sand (!(lit acc.1 a).2) (!(lit acc.1 b).2) (lit acc.1 a).1 (lit acc.1 b).1])
  | GateOp.or, [] => (acc.1 ++ [(10, false)], acc.2)
  | GateOp.or, [a] => (acc.1 ++ [lit acc.1 a], acc.2)
  | GateOp.or, [a, b] => (acc.1 ++ [(11 + acc.2.length, true)],
      acc.2 ++ [sand (lit acc.1 a).2 (lit acc.1 b).2 (lit acc.1 a).1 (lit acc.1 b).1])
  | _, _ => (acc.1 ++ [(10, false)], acc.2)

def bstep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def bw (bs : List BinaryGate) (y : List Bool) : List Bool := bs.foldl bstep y

def cstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma bw_length (bs : List BinaryGate) (y : List Bool) :
    (bw bs y).length = y.length + bs.length := by
  induction bs generalizing y with
  | nil => simp [bw]
  | cons b bs ih =>
    simp only [bw, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [bstep]
    omega

lemma bw_snoc (bs : List BinaryGate) (b : BinaryGate) (y : List Bool) :
    bw (bs ++ [b]) y = bstep (bw bs y) b := by
  simp [bw, List.foldl_append]

lemma bw_snoc_lt (bs : List BinaryGate) (b : BinaryGate) (y : List Bool) (j : ℕ)
    (h : j < y.length + bs.length) :
    (bw (bs ++ [b]) y).getD j false = (bw bs y).getD j false := by
  rw [bw_snoc]
  simp only [bstep]
  exact List.getD_append _ _ _ _ (by rw [bw_length]; exact h)

lemma bw_snoc_eq (bs : List BinaryGate) (b : BinaryGate) (y : List Bool) :
    (bw (bs ++ [b]) y).getD (y.length + bs.length) false =
      b.op ((bw bs y).getD b.left false) ((bw bs y).getD b.right false) := by
  rw [bw_snoc]
  simp only [bstep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [bw_length]), bw_length]
  simp

def Inv (y w : List Bool) (acc : List (ℕ × Bool) × List BinaryGate) : Prop :=
  w.length = acc.1.length ∧ ∀ i : ℕ, (lit acc.1 i).1 < 11 + acc.2.length ∧
    w.getD i false = ((bw acc.2 y).getD (lit acc.1 i).1 false ^^ (lit acc.1 i).2)

lemma lit_snoc_lt (sig : List (ℕ × Bool)) (e : ℕ × Bool) (i : ℕ) (h : i < sig.length) :
    lit (sig ++ [e]) i = lit sig i := List.getD_append _ _ _ _ h

lemma lit_snoc_eq (sig : List (ℕ × Bool)) (e : ℕ × Bool) : lit (sig ++ [e]) sig.length = e := by
  simp [lit]

lemma lit_snoc_gt (sig : List (ℕ × Bool)) (e : ℕ × Bool) (i : ℕ) (h : sig.length < i) :
    lit (sig ++ [e]) i = (10, false) := by
  unfold lit
  rw [List.getD_eq_default _ _ (by simp; omega)]

lemma extend (y w : List Bool) (sig : List (ℕ × Bool)) (bs bs' : List BinaryGate)
    (e : ℕ × Bool) (v : Bool) (hy : y.length = 11) (hI : Inv y w (sig, bs))
    (hbs : ∀ j < 11 + bs.length, (bw bs' y).getD j false = (bw bs y).getD j false)
    (hl : bs.length ≤ bs'.length) (he : e.1 < 11 + bs'.length)
    (hv : v = ((bw bs' y).getD e.1 false ^^ e.2)) :
    Inv y (w ++ [v]) (sig ++ [e], bs') := by
  obtain ⟨hlen, hinv⟩ := hI
  have hlen' : w.length = sig.length := hlen
  refine ⟨by simp [hlen'], ?_⟩
  intro i
  show (lit (sig ++ [e]) i).1 < 11 + bs'.length ∧
    (w ++ [v]).getD i false = ((bw bs' y).getD (lit (sig ++ [e]) i).1 false ^^
      (lit (sig ++ [e]) i).2)
  rcases lt_trichotomy i sig.length with hlt | heq | hgt
  · rw [lit_snoc_lt _ _ _ hlt]
    obtain ⟨h1, h2⟩ := hinv i
    have h1' : (lit sig i).1 < 11 + bs.length := h1
    have h2' : w.getD i false = ((bw bs y).getD (lit sig i).1 false ^^ (lit sig i).2) := h2
    refine ⟨by omega, ?_⟩
    rw [List.getD_append _ _ _ _ (by omega), h2', hbs _ h1']
  · subst heq
    rw [lit_snoc_eq]
    refine ⟨he, ?_⟩
    rw [← hlen']
    simp [hv]
  · rw [lit_snoc_gt _ _ _ hgt]
    have hd := hinv w.length
    have hdl : lit sig w.length = (10, false) := by
      unfold lit
      rw [List.getD_eq_default _ _ (by omega)]
    obtain ⟨h1, h2⟩ := hd
    have h1' : (lit sig w.length).1 < 11 + bs.length := h1
    have h2' : w.getD w.length false =
        ((bw bs y).getD (lit sig w.length).1 false ^^ (lit sig w.length).2) := h2
    rw [hdl] at h1' h2'
    simp only at h1' h2'
    refine ⟨by simp only; omega, ?_⟩
    rw [List.getD_eq_default _ _ (by simp; omega)]
    rw [List.getD_eq_default _ _ le_rfl] at h2'
    simp only
    rw [hbs _ h1']
    exact h2'

lemma bw_prefix (bs : List BinaryGate) (y : List Bool) (j : ℕ) (h : j < y.length) :
    (bw bs y).getD j false = y.getD j false := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    rw [bw_snoc_lt _ _ _ _ (by omega), ih]

lemma xor_and (p q a b : Bool) :
    ((p ^^ a) && (q ^^ b)) = ((p == !a) && (q == !b)) := by
  cases p <;> cases q <;> cases a <;> cases b <;> rfl

lemma xor_or (p q a b : Bool) :
    ((p ^^ a) || (q ^^ b)) = (((p == a) && (q == b)) ^^ true) := by
  cases p <;> cases q <;> cases a <;> cases b <;> rfl

lemma tr_step (y w : List Bool) (sig : List (ℕ × Bool)) (bs : List BinaryGate)
    (hy : y.length = 11) (hy10 : y.getD 10 false = false) (hI : Inv y w (sig, bs))
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) :
    Inv y (cstep w g) (tr (sig, bs) g) := by
  have hval : ∀ i, w.getD i false =
      ((bw bs y).getD (lit sig i).1 false ^^ (lit sig i).2) := fun i => (hI.2 i).2
  have hvalid : ∀ i, (lit sig i).1 < 11 + bs.length := fun i => (hI.2 i).1
  have h10 : (bw bs y).getD 10 false = false := by rw [bw_prefix _ _ _ (by omega), hy10]
  have same : ∀ j < 11 + bs.length, (bw bs y).getD j false = (bw bs y).getD j false :=
    fun _ _ => rfl
  have grow : ∀ b : BinaryGate, ∀ j < 11 + bs.length,
      (bw (bs ++ [b]) y).getD j false = (bw bs y).getD j false :=
    fun b j hj => bw_snoc_lt _ _ _ _ (by omega)
  have top : ∀ b : BinaryGate, (bw (bs ++ [b]) y).getD (11 + bs.length) false =
      b.op ((bw bs y).getD b.left false) ((bw bs y).getD b.right false) := by
    intro b
    rw [show 11 + bs.length = y.length + bs.length by omega, bw_snoc_eq]
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact extend y w sig bs bs (10, true) _ hy hI same le_rfl (by omega) (by
        show _ = ((bw bs y).getD 10 false ^^ _); rw [h10]; rfl)
    · exact extend y w sig bs bs (lit sig a) _ hy hI same le_rfl (hvalid a) (by
        rw [← hval a]; show List.all [w.getD a false] id = _; cases w.getD a false <;> rfl)
    · refine extend y w sig bs _ (11 + bs.length, false) _ hy hI (grow _) (by simp)
        (by simp) ?_
      rw [top]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id, Bool.and_true, sand, Bool.xor_false]
      rw [hval a, hval b, xor_and]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact extend y w sig bs bs (10, false) _ hy hI same le_rfl (by omega) (by
        show _ = ((bw bs y).getD 10 false ^^ _); rw [h10]; rfl)
    · exact extend y w sig bs bs (lit sig a) _ hy hI same le_rfl (hvalid a) (by
        rw [← hval a]; show List.any [w.getD a false] id = _; cases w.getD a false <;> rfl)
    · refine extend y w sig bs _ (11 + bs.length, true) _ hy hI (grow _) (by simp)
        (by simp) ?_
      rw [top]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id, Bool.or_false, sand]
      rw [hval a, hval b, xor_or]
    · simp at hlen
  · rcases ins with _ | ⟨a, rest⟩
    · exact extend y w sig bs bs (10, true) _ hy hI same le_rfl (by omega) (by
        show _ = ((bw bs y).getD 10 false ^^ _); rw [h10]; rfl)
    · exact extend y w sig bs bs ((lit sig a).1, !(lit sig a).2) _ hy hI same le_rfl
        (hvalid a) (by
        show (!((w.getD a false :: List.map _ rest).headD false)) = _
        rw [hval a]; cases (bw bs y).getD (lit sig a).1 false <;> cases (lit sig a).2 <;> rfl)

lemma tr_fold (y : List Bool) (hy : y.length = 11) (hy10 : y.getD 10 false = false)
    (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ (w : List Bool) (acc : List (ℕ × Bool) × List BinaryGate), Inv y w acc →
      Inv y (gs.foldl cstep w) (gs.foldl tr acc) := by
  induction gs with
  | nil => intro w acc h; exact h
  | cons g gs ih =>
    intro w acc h
    obtain ⟨sig, bs⟩ := acc
    have hg := hgs g List.mem_cons_self
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (tr_step y w sig bs hy hy10 h g hg.1 hg.2)

lemma tr_count (gs : List Gate) :
    ∀ acc : List (ℕ × Bool) × List BinaryGate,
      (gs.foldl tr acc).2.length + (gs.filter fun g : Gate =>
        @decide (g.op = GateOp.not) (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _)).length
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp
  | cons g gs ih =>
    intro acc
    have h := ih (tr acc g)
    rw [List.foldl_cons]
    obtain ⟨op, ins⟩ := g
    rcases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      simp [tr, List.filter_cons] at h ⊢ <;> omega

lemma tr_shape (gs : List Gate) :
    ∀ acc : List (ℕ × Bool) × List BinaryGate,
      (∀ b ∈ acc.2, ∃ c1 c2 : Bool, b.op = fun u v => u == c1 && v == c2) →
      ∀ b ∈ (gs.foldl tr acc).2, ∃ c1 c2 : Bool, b.op = fun u v => u == c1 && v == c2 := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    obtain ⟨op, ins⟩ := g
    rcases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      simp only [tr] <;>
      first
      | exact h
      | (intro b' hb'
         rcases List.mem_append.1 hb' with hb' | hb'
         · exact h b' hb'
         · simp only [List.mem_singleton] at hb'
           subst hb'
           exact ⟨_, _, rfl⟩)

lemma inv_init (x : List Bool) (hx : x.length = 10) :
    Inv (x ++ [false]) x (List.ofFn (fun i : Fin 10 => ((i : ℕ), false)), []) := by
  refine ⟨by simp [hx], ?_⟩
  intro i
  show (lit _ i).1 < 11 + 0 ∧ _
  by_cases hi : i < 10
  · have hl : lit (List.ofFn (fun i : Fin 10 => ((i : ℕ), false))) i = (i, false) := by
      unfold lit
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    rw [hl]
    refine ⟨by omega, ?_⟩
    simp only [bw, List.foldl_nil, Bool.xor_false]
    rw [List.getD_append _ _ _ _ (by omega)]
  · have hl : lit (List.ofFn (fun i : Fin 10 => ((i : ℕ), false))) i = (10, false) := by
      unfold lit
      rw [List.getD_eq_default _ _ (by simp; omega)]
    rw [hl]
    refine ⟨by omega, ?_⟩
    simp only [bw, List.foldl_nil, Bool.xor_false]
    rw [List.getD_eq_default _ _ (by omega)]
    simp [List.getD_eq_getElem?_getD, hx]

theorem main (C : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ (D : BinaryCircuit) (p : Bool),
      (∀ g ∈ D.gates, ∃ (c1 c2 : Bool), g.op = fun u v => u == c1 && v == c2) ∧
      D.size + PEqualNP.NotBracket.notCount C ≤ C.size ∧
      ∀ x : List Bool, x.length = 10 → (D.eval (x ++ [false]) != p) = C.eval x := by
  set acc0 : List (ℕ × Bool) × List BinaryGate :=
    (List.ofFn (fun i : Fin 10 => ((i : ℕ), false)), []) with hacc0
  set accF := C.gates.foldl tr acc0 with haccF
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hF g hg
    refine ⟨?_, h2⟩
    simpa using h1
  refine ⟨⟨accF.2, (lit accF.1 C.output).1⟩, (lit accF.1 C.output).2, ?_, ?_, ?_⟩
  · exact tr_shape C.gates acc0 (by simp [hacc0])
  · have := tr_count C.gates acc0
    simp only [hacc0, List.length_nil, zero_add] at this
    exact this
  · intro x hx
    have hI := tr_fold (x ++ [false]) (by simp [hx]) (by simp [List.getD_eq_getElem?_getD, hx])
      C.gates hgs x acc0 (inv_init x hx)
    have h := (hI.2 C.output).2
    show ((bw accF.2 (x ++ [false])).getD (lit accF.1 C.output).1 false !=
      (lit accF.1 C.output).2) = (C.gates.foldl cstep x).getD C.output false
    rw [h]

end PEqualNP.Outside.L_meta_2826

theorem PEqualNP.Outside.L_meta_2826 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Bool), (∀ x5 ∈ x3.gates, ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → (x3.eval (x5 ++ [Bool.false]) != x4) = x1.eval x5 := by
  intro C hF
  exact PEqualNP.Outside.L_meta_2826.main C hF
