import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds

def K (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3)
def mk (b : Bool) : GateOp := if b then GateOp.and else GateOp.or

lemma const_no (b : Bool) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b,[]⟩],4⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  cases b <;> decide
lemma one_no (b : Bool) (a : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b,[a.val]⟩],4⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases a <;> cases b <;> decide
lemma two_no (b : Bool) (a c : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b,[a.val,c.val]⟩],4⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases a <;> fin_cases c <;> cases b <;> decide
lemma readC_L (b0 b1 : Bool) (v : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b0,[]⟩,⟨mk b1,[4,v.val]⟩],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases v <;> cases b0 <;> cases b1 <;> decide
lemma readO_L (b0 b1 : Bool) (a v : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b0,[a.val]⟩,⟨mk b1,[4,v.val]⟩],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases a <;> fin_cases v <;> cases b0 <;> cases b1 <;> decide
lemma readT_L (b0 b1 : Bool) (a b v : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b0,[a.val,b.val]⟩,⟨mk b1,[4,v.val]⟩],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases a <;> fin_cases b <;> fin_cases v <;> cases b0 <;> cases b1 <;> decide
lemma readC_R (b0 b1 : Bool) (v : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b0,[]⟩,⟨mk b1,[v.val,4]⟩],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases v <;> cases b0 <;> cases b1 <;> decide
lemma readO_R (b0 b1 : Bool) (a v : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b0,[a.val]⟩,⟨mk b1,[v.val,4]⟩],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases a <;> fin_cases v <;> cases b0 <;> cases b1 <;> decide
lemma readT_R (b0 b1 : Bool) (a b v : Fin 4) : ∃ x : Fin 4 → Bool,
    (⟨[⟨mk b0,[a.val,b.val]⟩,⟨mk b1,[v.val,4]⟩],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  fin_cases a <;> fin_cases b <;> fin_cases v <;> cases b0 <;> cases b1 <;> decide

lemma one_gate_no (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hbound : ∀ i ∈ g.inputs, i < 4) :
    ∃ x : Fin 4 → Bool, (⟨[g],4⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  obtain ⟨b, hb⟩ : ∃ b, g.op = mk b := by
    rcases hop with h | h
    · exact ⟨true, by simp [mk, h]⟩
    · exact ⟨false, by simp [mk, h]⟩
  rcases g with ⟨op, inputs⟩
  simp only at hb
  subst hb
  rcases inputs with _ | ⟨a, inputs⟩
  · simpa using const_no b
  rcases inputs with _ | ⟨c, inputs⟩
  · have ha : a < 4 := hbound a (by simp)
    let af : Fin 4 := ⟨a, ha⟩
    simpa [af] using one_no b af
  rcases inputs with _ | ⟨d, inputs⟩
  · have ha : a < 4 := hbound a (by simp)
    have hc : c < 4 := hbound c (by simp)
    let af : Fin 4 := ⟨a, ha⟩
    let cf : Fin 4 := ⟨c, hc⟩
    simpa [af, cf] using two_no b af cf
  · simp at hlen

lemma two_gate_read_no (g0 g1 : Gate)
    (hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hop1 : g1.op = GateOp.and ∨ g1.op = GateOp.or)
    (hlen0 : g0.inputs.length ≤ 2) (hlen1 : g1.inputs.length ≤ 2)
    (hbound0 : ∀ i ∈ g0.inputs, i < 4) (hbound1 : ∀ i ∈ g1.inputs, i < 5)
    (hread : 4 ∈ g1.inputs) :
    ∃ x : Fin 4 → Bool, (⟨[g0,g1],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  obtain ⟨b0, hb0⟩ : ∃ b, g0.op = mk b := by
    rcases hop0 with h | h
    · exact ⟨true, by simp [mk, h]⟩
    · exact ⟨false, by simp [mk, h]⟩
  obtain ⟨b1, hb1⟩ : ∃ b, g1.op = mk b := by
    rcases hop1 with h | h
    · exact ⟨true, by simp [mk, h]⟩
    · exact ⟨false, by simp [mk, h]⟩
  rcases g0 with ⟨op0, in0⟩
  rcases g1 with ⟨op1, in1⟩
  simp only at hb0 hb1
  subst hb0
  subst hb1
  rcases in1 with _ | ⟨u, in1⟩
  · simp at hread
  rcases in1 with _ | ⟨v, in1⟩
  · have hu : u = 4 := by simpa [eq_comm] using hread
    subst hu
    have hfun : (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩,⟨mk b1,[4]⟩],5⟩ : Circuit).eval (List.ofFn x)) =
        (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩],4⟩ : Circuit).eval (List.ofFn x)) := by
      funext x
      cases b1 <;> simp [Circuit.eval, Circuit.wires, GateOp.eval, mk]
    obtain ⟨x, hx⟩ := one_gate_no ⟨mk b0,in0⟩ (by cases b0 <;> simp [mk]) hlen0 hbound0
    exact ⟨x, by rw [congrFun hfun x]; exact hx⟩
  rcases in1 with _ | ⟨w, in1⟩
  · simp at hread
    rcases hread with hu | hv
    · subst hu
      by_cases hv4 : v = 4
      · subst hv4
        have hfun : (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩,⟨mk b1,[4,4]⟩],5⟩ : Circuit).eval (List.ofFn x)) =
            (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩],4⟩ : Circuit).eval (List.ofFn x)) := by
          funext x
          cases b1 <;> simp [Circuit.eval, Circuit.wires, GateOp.eval, mk]
        obtain ⟨x, hx⟩ := one_gate_no ⟨mk b0,in0⟩ (by cases b0 <;> simp [mk]) hlen0 hbound0
        exact ⟨x, by rw [congrFun hfun x]; exact hx⟩
      · have hvlt : v < 4 := by
          have := hbound1 v (by simp)
          omega
        let vf : Fin 4 := ⟨v, hvlt⟩
        rcases in0 with _ | ⟨a, in0⟩
        · simpa [vf] using readC_L b0 b1 vf
        rcases in0 with _ | ⟨c, in0⟩
        · have ha : a < 4 := hbound0 a (by simp)
          let af : Fin 4 := ⟨a, ha⟩
          simpa [af, vf] using readO_L b0 b1 af vf
        rcases in0 with _ | ⟨d, in0⟩
        · have ha : a < 4 := hbound0 a (by simp)
          have hc : c < 4 := hbound0 c (by simp)
          let af : Fin 4 := ⟨a, ha⟩
          let cf : Fin 4 := ⟨c, hc⟩
          simpa [af, cf, vf] using readT_L b0 b1 af cf vf
        · simp at hlen0
    · subst hv
      by_cases hu4 : u = 4
      · subst hu4
        have hfun : (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩,⟨mk b1,[4,4]⟩],5⟩ : Circuit).eval (List.ofFn x)) =
            (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩],4⟩ : Circuit).eval (List.ofFn x)) := by
          funext x
          cases b1 <;> simp [Circuit.eval, Circuit.wires, GateOp.eval, mk]
        obtain ⟨x, hx⟩ := one_gate_no ⟨mk b0,in0⟩ (by cases b0 <;> simp [mk]) hlen0 hbound0
        exact ⟨x, by rw [congrFun hfun x]; exact hx⟩
      · have hult : u < 4 := by
          have := hbound1 u (by simp)
          omega
        let uf : Fin 4 := ⟨u, hult⟩
        rcases in0 with _ | ⟨a, in0⟩
        · simpa [uf] using readC_R b0 b1 uf
        rcases in0 with _ | ⟨c, in0⟩
        · have ha : a < 4 := hbound0 a (by simp)
          let af : Fin 4 := ⟨a, ha⟩
          simpa [af, uf] using readO_R b0 b1 af uf
        rcases in0 with _ | ⟨d, in0⟩
        · have ha : a < 4 := hbound0 a (by simp)
          have hc : c < 4 := hbound0 c (by simp)
          let af : Fin 4 := ⟨a, ha⟩
          let cf : Fin 4 := ⟨c, hc⟩
          simpa [af, cf, uf] using readT_R b0 b1 af cf uf
        · simp at hlen0
  · simp at hlen1

lemma two_gate_noread_no (g0 g1 : Gate)
    (hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hop1 : g1.op = GateOp.and ∨ g1.op = GateOp.or)
    (hlen0 : g0.inputs.length ≤ 2) (hlen1 : g1.inputs.length ≤ 2)
    (hbound0 : ∀ i ∈ g0.inputs, i < 4) (hbound1 : ∀ i ∈ g1.inputs, i < 5)
    (hnot : 4 ∉ g1.inputs) :
    ∃ x : Fin 4 → Bool, (⟨[g0,g1],5⟩ : Circuit).eval (List.ofFn x) ≠ K x := by
  obtain ⟨b0, hb0⟩ : ∃ b, g0.op = mk b := by
    rcases hop0 with h | h
    · exact ⟨true, by simp [mk, h]⟩
    · exact ⟨false, by simp [mk, h]⟩
  obtain ⟨b1, hb1⟩ : ∃ b, g1.op = mk b := by
    rcases hop1 with h | h
    · exact ⟨true, by simp [mk, h]⟩
    · exact ⟨false, by simp [mk, h]⟩
  rcases g0 with ⟨op0, in0⟩
  rcases g1 with ⟨op1, in1⟩
  simp only at hb0 hb1
  subst hb0
  subst hb1
  rcases in1 with _ | ⟨a, in1⟩
  · have hfun : (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩,⟨mk b1,[]⟩],5⟩ : Circuit).eval (List.ofFn x)) =
        (fun x : Fin 4 → Bool => (⟨[⟨mk b1,[]⟩],4⟩ : Circuit).eval (List.ofFn x)) := by
      funext x
      cases b1 <;> simp [Circuit.eval, Circuit.wires, GateOp.eval, mk]
    obtain ⟨x, hx⟩ := one_gate_no ⟨mk b1,[]⟩ (by cases b1 <;> simp [mk]) (by simp) (by intro i hi; simp at hi)
    exact ⟨x, by rw [congrFun hfun x]; exact hx⟩
  rcases in1 with _ | ⟨b, in1⟩
  · have ha4 : a ≠ 4 := by
      intro h; exact hnot (by simp [h])
    have ha5 : a < 5 := hbound1 a (by simp)
    have ha4lt : a < 4 := by omega
    let af : Fin 4 := ⟨a, ha4lt⟩
    have hfun : (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩,⟨mk b1,[a]⟩],5⟩ : Circuit).eval (List.ofFn x)) =
        (fun x : Fin 4 → Bool => (⟨[⟨mk b1,[a]⟩],4⟩ : Circuit).eval (List.ofFn x)) := by
      funext x
      interval_cases a <;> cases b1 <;> simp [Circuit.eval, Circuit.wires, GateOp.eval, mk]
    obtain ⟨x, hx⟩ := one_gate_no ⟨mk b1,[a]⟩ (by cases b1 <;> simp [mk]) (by simp) (by intro i hi; simp at hi; omega)
    exact ⟨x, by rw [congrFun hfun x]; exact hx⟩
  rcases in1 with _ | ⟨c, in1⟩
  · have ha4 : a ≠ 4 := by intro h; exact hnot (by simp [h])
    have hb4 : b ≠ 4 := by intro h; exact hnot (by simp [h])
    have ha5 : a < 5 := hbound1 a (by simp)
    have hb5 : b < 5 := hbound1 b (by simp)
    have ha4lt : a < 4 := by omega
    have hb4lt : b < 4 := by omega
    let af : Fin 4 := ⟨a, ha4lt⟩
    let bf : Fin 4 := ⟨b, hb4lt⟩
    have hfun : (fun x : Fin 4 → Bool => (⟨[⟨mk b0,in0⟩,⟨mk b1,[a,b]⟩],5⟩ : Circuit).eval (List.ofFn x)) =
        (fun x : Fin 4 → Bool => (⟨[⟨mk b1,[a,b]⟩],4⟩ : Circuit).eval (List.ofFn x)) := by
      funext x
      interval_cases a <;> interval_cases b <;> cases b1 <;> simp [Circuit.eval, Circuit.wires, GateOp.eval, mk]
    obtain ⟨x, hx⟩ := one_gate_no ⟨mk b1,[a,b]⟩ (by cases b1 <;> simp [mk]) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
    exact ⟨x, by rw [congrFun hfun x]; exact hx⟩
  · simp at hlen1

def grow {α β : Type*} (f : List α → β → α) (gs : List β) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem grow_prefix {α β : Type*} (f : List α → β → α) (gs : List β) :
    ∀ w : List α, ∃ t : List α, grow f gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [grow], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    change grow f gs (w ++ [f w g]) = w ++ f w g :: t
    rw [ht]
    simp

theorem grow_length {α β : Type*} (f : List α → β → α) (gs : List β) (w : List α) :
    (grow f gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := grow_prefix f gs w
  rw [ht]; simp [hl]

theorem grow_getD_lt {α β : Type*} (f : List α → β → α) (gs : List β) (w : List α)
    (i : ℕ) (d : α) (h : i < w.length) :
    (grow f gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := grow_prefix f gs w
  rw [ht, List.getD_append _ _ _ _ h]

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq_grow (C : Circuit) (x : List Bool) :
    C.wires x = grow gateValue C.gates x := rfl

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rw [wires_eq_grow, grow_length]; rfl

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  grow_getD_lt gateValue C.gates x i false hi

theorem wires_oob (C : Circuit) (x : List Bool) (i : ℕ)
    (hi : x.length + C.size ≤ i) :
    (C.wires x).getD i false = false := by
  obtain ⟨t, ht, hl⟩ := grow_prefix gateValue C.gates x
  rw [wires_eq_grow, ht]
  apply List.getD_eq_default
  simp only [List.length_append, hl]
  have hi' : x.length + C.gates.length ≤ i := by simpa [Circuit.size] using hi
  omega

lemma eval_input (C : Circuit) (h : C.output < 4) (x : Fin 4 → Bool) :
    C.eval (List.ofFn x) = x ⟨C.output, h⟩ := by
  unfold Circuit.eval
  rw [wires_input C (List.ofFn x) C.output (by simpa using h)]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_ofFn]
  simp [h]

lemma eval_oob (C : Circuit) (h : 4 + C.size ≤ C.output) (x : Fin 4 → Bool) :
    C.eval (List.ofFn x) = false := by
  unfold Circuit.eval
  rw [wires_oob C (List.ofFn x) C.output (by simpa [wires_length] using h)]

lemma input_no (i : Fin 4) :
    ∃ x : Fin 4 → Bool, x i ≠ K x := by
  fin_cases i <;> decide

lemma oob_no (C : Circuit) (h : 4 + C.size ≤ C.output) :
    ∃ x : Fin 4 → Bool, C.eval (List.ofFn x) ≠ K x := by
  refine ⟨fun j => decide (j = 0 ∨ j = 2), ?_⟩
  rw [eval_oob C h]
  decide

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_2122 :
    ¬ ∃ C : Circuit, Monotone2 C ∧ ReadsBack 4 C ∧ C.size ≤ 2 ∧
      (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = K x) := by
  rintro ⟨C, hM, hR, hsize, hfun⟩
  have hcontr : ∃ x : Fin 4 → Bool, C.eval (List.ofFn x) ≠ K x := by
    rcases C with ⟨gs, out⟩
    have hlen : gs.length ≤ 2 := by simpa [Circuit.size] using hsize
    rcases gs with _ | ⟨g0, gs⟩
    · by_cases hout : out < 4
      · obtain ⟨x, hx⟩ := input_no ⟨out, hout⟩
        exact ⟨x, by rw [eval_input ⟨[], out⟩ hout x]; exact hx⟩
      · have hoob : 4 + (⟨[], out⟩ : Circuit).size ≤ out := by
          simp [Circuit.size]; omega
        exact oob_no ⟨[], out⟩ hoob
    rcases gs with _ | ⟨g1, gs⟩
    · by_cases hout : out < 4
      · obtain ⟨x, hx⟩ := input_no ⟨out, hout⟩
        exact ⟨x, by rw [eval_input ⟨[g0], out⟩ hout x]; exact hx⟩
      · by_cases hout4 : out = 4
        · subst out
          have hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or := by
            simpa using (hM g0 (by simp)).1
          have hlen0 : g0.inputs.length ≤ 2 := (hM g0 (by simp)).2
          have hb0 : ∀ i ∈ g0.inputs, i < 4 := by
            intro i hi
            have := hR 0 (by simp) i (by simpa [gateAt] using hi)
            simpa using this
          obtain ⟨x, hx⟩ := one_gate_no g0 hop0 hlen0 hb0
          exact ⟨x, hx⟩
        · have hoob : 4 + (⟨[g0], out⟩ : Circuit).size ≤ out := by
            simp [Circuit.size]; omega
          exact oob_no ⟨[g0], out⟩ hoob
    · rcases gs with _ | ⟨g2, gs⟩
      · by_cases hout : out < 4
        · obtain ⟨x, hx⟩ := input_no ⟨out, hout⟩
          exact ⟨x, by rw [eval_input ⟨[g0,g1], out⟩ hout x]; exact hx⟩
        · by_cases hout4 : out = 4
          · subst out
            have hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or := by
              simpa using (hM g0 (by simp)).1
            have hlen0 : g0.inputs.length ≤ 2 := (hM g0 (by simp)).2
            have hb0 : ∀ i ∈ g0.inputs, i < 4 := by
              intro i hi
              have := hR 0 (by simp) i (by simpa [gateAt] using hi)
              simpa using this
            obtain ⟨x, hx⟩ := one_gate_no g0 hop0 hlen0 hb0
            have hfunEq : (fun x : Fin 4 → Bool => (⟨[g0,g1], 4⟩ : Circuit).eval (List.ofFn x)) =
                (fun x : Fin 4 → Bool => (⟨[g0], 4⟩ : Circuit).eval (List.ofFn x)) := by
              funext x; simp [Circuit.eval, Circuit.wires]
            exact ⟨x, by rw [congrFun hfunEq x]; exact hx⟩
          · by_cases hout5 : out = 5
            · subst out
              have hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or := by
                simpa using (hM g0 (by simp)).1
              have hop1 : g1.op = GateOp.and ∨ g1.op = GateOp.or := by
                simpa using (hM g1 (by simp)).1
              have hlen0 : g0.inputs.length ≤ 2 := (hM g0 (by simp)).2
              have hlen1 : g1.inputs.length ≤ 2 := (hM g1 (by simp)).2
              have hb0 : ∀ i ∈ g0.inputs, i < 4 := by
                intro i hi
                have := hR 0 (by simp) i (by simpa [gateAt] using hi)
                simpa using this
              have hb1 : ∀ i ∈ g1.inputs, i < 5 := by
                intro i hi
                have := hR 1 (by simp) i (by simpa [gateAt] using hi)
                simpa using this
              by_cases hread : 4 ∈ g1.inputs
              · exact two_gate_read_no g0 g1 hop0 hop1 hlen0 hlen1 hb0 hb1 hread
              · exact two_gate_noread_no g0 g1 hop0 hop1 hlen0 hlen1 hb0 hb1 hread
            · have hoob : 4 + (⟨[g0,g1], out⟩ : Circuit).size ≤ out := by
                simp [Circuit.size]; omega
              exact oob_no ⟨[g0,g1], out⟩ hoob
      · simp at hlen
  obtain ⟨x, hx⟩ := hcontr
  exact hx (hfun x)
