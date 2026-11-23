import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace EdgeBirth201

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

def run (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn x)

def wire (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (run gs x).getD i false

def step (g : Gate) (f : ℕ → Bool) : Bool :=
  g.op.eval (g.inputs.map f)

theorem run_snoc (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    run (gs ++ [g]) x = run gs x ++ [step g (wire gs x)] := by
  simp [run, Circuit.wires, List.foldl_append, step]
  rfl

theorem run_len (gs : List Gate) (x : Fin n → Bool) :
    (run gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run, Circuit.wires]
  | append_singleton gs g ih => simp [run_snoc, ih, Nat.add_assoc]

theorem wire_old (gs : List Gate) (g : Gate) (x : Fin n → Bool)
    {i : ℕ} (h : i ≠ n + gs.length) : wire (gs ++ [g]) x i = wire gs x i := by
  simp only [wire, run_snoc]
  by_cases hi : i < (run gs x).length
  · exact List.getD_append _ _ _ _ hi
  · have hl := run_len gs x
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem wire_new (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wire (gs ++ [g]) x (n + gs.length) = step g (wire gs x) := by
  rw [← run_len gs x]
  simp [wire, run_snoc]

theorem wire_nil (x : Fin n → Bool) (i : ℕ) :
    wire [] x i = if h : i < n then x ⟨i,h⟩ else false := by
  by_cases h : i < n
  · simp [wire, run, Circuit.wires, List.getD_eq_getElem?_getD, h]
  · simp [wire, run, Circuit.wires, List.getD_eq_getElem?_getD, h]

def cross (f h : ℕ → Bool) (a b : ℕ) : Prop :=
  (f a = true ∧ h a = false ∧ h b = true ∧ f b = false) ∨
  (h a = true ∧ f a = false ∧ f b = true ∧ h b = false)

def born (gs : List Gate) (x y : Fin n → Bool) : Prop :=
  ∃ j g a b, gs[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a,b] ∧
    a < n+j ∧ b < n+j ∧ cross (wire gs x) (wire gs y) a b

theorem carry {gs : List Gate} {x y : Fin n → Bool} (g : Gate) (h : born gs x y) :
    born (gs ++ [g]) x y := by
  obtain ⟨j,q,a,b,hq,hop,hi,ha,hb,hc⟩ := h
  have hj : j < gs.length := by
    by_contra! h
    simp [List.getElem?_eq_none h] at hq
  refine ⟨j,q,a,b,?_,hop,hi,ha,hb,?_⟩
  · rwa [List.getElem?_append_left hj]
  · simpa only [cross, wire_old gs g _ (show a ≠ n+gs.length by omega),
      wire_old gs g _ (show b ≠ n+gs.length by omega)] using hc

theorem in_range {gs : List Gate} {x : Fin n → Bool} {i : ℕ}
    (h : wire gs x i = true) : i < n + gs.length := by
  by_contra! hi
  have hl : (run gs x).length ≤ i := by rwa [run_len]
  simp only [wire, List.getD_eq_default _ _ hl] at h
  contradiction

theorem gate_case (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f h z : ℕ → Bool)
    (hc : ∀ a, z a = true → f a = true ∨ h a = true)
    (hz : step g z = true) :
    step g f = true ∨ step g h = true ∨
    ∃ a b, g.op = GateOp.and ∧ g.inputs = [a,b] ∧ z a = true ∧ z b = true ∧ cross f h a b := by
  rcases hop with hop | hop
  · cases hx : g.inputs with
    | nil => simp [step,hop,hx,GateOp.eval]
    | cons a tail =>
      cases tail with
      | nil =>
        have hza : z a = true := by simpa [step,hop,hx,GateOp.eval] using hz
        rcases hc a hza with ha | ha <;> simp [step,hop,hx,GateOp.eval,ha]
      | cons b tail =>
        cases tail with
        | cons c rest => simp [hx] at hlen
        | nil =>
          have hz' : z a = true ∧ z b = true := by simpa [step,hop,hx,GateOp.eval] using hz
          have hca := hc a hz'.1
          have hcb := hc b hz'.2
          by_cases hf : f a = true ∧ f b = true
          · left; simpa [step,hop,hx,GateOp.eval] using hf
          by_cases hh : h a = true ∧ h b = true
          · right; left; simpa [step,hop,hx,GateOp.eval] using hh
          refine Or.inr (Or.inr ⟨a,b,hop,rfl,hz'.1,hz'.2,?_⟩)
          unfold cross
          cases fa : f a <;> cases fb : f b <;> cases ha : h a <;> cases hb : h b <;> simp_all
  · have hz' : ∃ i ∈ g.inputs, z i = true := by simpa [step,hop,GateOp.eval] using hz
    obtain ⟨i,hi,ht⟩ := hz'
    rcases hc i ht with h1 | h1
    · left; simpa [step,hop,GateOp.eval] using (show ∃ j ∈ g.inputs, f j = true from ⟨i,hi,h1⟩)
    · right; left; simpa [step,hop,GateOp.eval] using (show ∃ j ∈ g.inputs, h j = true from ⟨i,hi,h1⟩)

theorem trace_gate (gs : List Gate) (x y z : Fin n → Bool)
    (hin : ∀ i, z i = true → x i = true ∨ y i = true)
    (ok : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    born gs x y ∨ ∀ i, wire gs z i = true → wire gs x i = true ∨ wire gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    right
    intro i h
    simp only [wire_nil] at h ⊢
    split at h
    next hlt => simpa [hlt] using hin ⟨i,hlt⟩ h
    next => contradiction
  | append_singleton gs g ih =>
    rcases ih (fun a ha => ok a (by simp [ha])) with h | h
    · exact Or.inl (carry g h)
    · by_cases hb : born (gs ++ [g]) x y
      · exact Or.inl hb
      right
      intro i hi
      by_cases he : i = n+gs.length
      · subst i
        rw [wire_new] at hi
        rw [wire_new,wire_new]
        have hg := ok g (by simp)
        rcases gate_case g hg.1 hg.2 _ _ _ h hi with hf | hh | ⟨a,b,ho,hi',ha,hb',hc⟩
        · exact Or.inl hf
        · exact Or.inr hh
        · exfalso; apply hb
          have al := in_range ha
          have bl := in_range hb'
          refine ⟨gs.length,g,a,b,by simp,ho,hi',al,bl,?_⟩
          simpa only [cross,wire_old gs g _ (ne_of_lt al),wire_old gs g _ (ne_of_lt bl)] using hc
      · rw [wire_old _ _ _ he] at hi
        rw [wire_old _ _ _ he,wire_old _ _ _ he]
        exact h i hi

end EdgeBirth201

open EdgeBirth201 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_201 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∀ u v : Fin n, G.Adj u v → ∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ (((C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = false) ∨ ((C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = false))) := by
  classical
  intro n G _ C hfan hnot hfun u v huv
  let one (a i : Fin n) := decide (i = a)
  let both (i : Fin n) := decide (i = u ∨ i = v)
  have hs (a : Fin n) : wire C.gates (one a) C.output = false := by
    change circuitFun n C (one a) = false
    rw [hfun]
    simp [one]
  have hz : wire C.gates both C.output = true := by
    change circuitFun n C both = true
    rw [hfun]
    apply decide_eq_true
    exact ⟨u,v,huv,by simp [both],by simp [both]⟩
  have hinput : ∀ i, both i = true → one u i = true ∨ one v i = true := by simp [both,one]
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hm
    obtain ⟨ho,hl⟩ := hfan g hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    exact ⟨ho.elim Or.inl (fun h => Or.inr (h.resolve_right (hnot g hm))),hl⟩
  rcases trace_gate C.gates (one u) (one v) both hinput hg with h | h
  · exact h
  · have bad := h C.output hz
    simp [hs] at bad
