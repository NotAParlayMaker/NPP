import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3606_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Le (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i : ℕ, v.getD i false = true → v'.getD i false = true

def Mono (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

theorem getD_lt {α : Type} (l : List α) (y : α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ [y]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_len {α : Type} (l : List α) (y : α) (d : α) :
    (l ++ [y]).getD l.length d = y := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp

theorem length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem length_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, length_step]
    simp
    omega

theorem eval_mono (g : Gate) (hg : Mono g) (v v' : List Bool)
    (h : ∀ i : ℕ, v.getD i false = true → v'.getD i false = true)
    (hv : g.op.eval (g.inputs.map fun i => v.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => v'.getD i false) = true := by
  rcases hg with h1 | h1
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
    rintro x ⟨a, ha, rfl⟩
    exact h a (hv _ ⟨a, ha, rfl⟩)
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨x, ⟨a, ha, rfl⟩, hx⟩ := hv
    exact ⟨_, ⟨a, ha, rfl⟩, h a hx⟩

theorem le_step (g : Gate) (hg : Mono g) (v v' : List Bool) (h : Le v v') :
    Le (step v g) (step v' g) := by
  obtain ⟨hl, hp⟩ := h
  refine ⟨by rw [length_step, length_step, hl], fun i hi => ?_⟩
  rcases lt_trichotomy i v.length with hlt | heq | hgt
  · rw [step, getD_lt _ _ _ _ hlt] at hi
    rw [step, getD_lt _ _ _ _ (hl ▸ hlt)]
    exact hp i hi
  · subst heq
    rw [step, getD_len] at hi
    rw [step, hl, getD_len]
    exact eval_mono g hg v v' hp hi
  · rw [getD_ge _ _ _ (by rw [length_step]; omega)] at hi
    exact absurd hi (by simp)

theorem le_foldl (gs : List Gate) (hgs : ∀ g ∈ gs, Mono g) (v v' : List Bool) (h : Le v v') :
    Le (gs.foldl step v) (gs.foldl step v') := by
  induction gs generalizing v v' with
  | nil => simpa using h
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (le_step g (hgs g (List.mem_cons_self ..)) v v' h)

theorem le_append (v v' : List Bool) (b b' : Bool) (h : Le v v') (hb : b = true → b' = true) :
    Le (v ++ [b]) (v' ++ [b']) := by
  obtain ⟨hl, hp⟩ := h
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rcases lt_trichotomy i v.length with hlt | heq | hgt
  · rw [getD_lt _ _ _ _ hlt] at hi
    rw [getD_lt _ _ _ _ (hl ▸ hlt)]
    exact hp i hi
  · subst heq
    rw [getD_len] at hi
    rw [hl, getD_len]
    exact hb hi
  · rw [getD_ge _ _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem le_ofFn {n : ℕ} (x x' : Fin n → Bool) (h : ∀ i, x i = true → x' i = true) :
    Le (List.ofFn x) (List.ofFn x') := by
  refine ⟨by simp, fun i hi => ?_⟩
  by_cases hin : i < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    simp [hin] at hi ⊢
    exact h _ hi
  · rw [getD_ge _ _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem headD_map (l : List ℕ) (f : ℕ → Bool) (d : ℕ) (hd : f d = false) :
    (l.map f).headD false = f (l.headD d) := by
  cases l with
  | nil => simp [hd]
  | cons a l => simp

theorem eval_not (g : Gate) (w : List Bool) (d : ℕ) (hd : w.length ≤ d) (hg : g.op = GateOp.not) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = !(w.getD (g.inputs.headD d) false) := by
  rw [hg]
  generalize g.inputs = l
  cases l with
  | nil => simp [GateOp.eval, List.getElem?_eq_none hd]
  | cons i l => simp [GateOp.eval]

open PEqualNP.MetaComplexity in
theorem main (gs : List Gate) (out a b : ℕ) (hfan : FanInTwo ⟨gs, out⟩) (hab : a < b)
    (hbL : b + 1 = gs.length) (hout : out = 9 + b)
    (hna : ∀ h : a < gs.length, gs[a].op = GateOp.not)
    (hnb : ∀ h : b < gs.length, gs[b].op = GateOp.not)
    (honly : ∀ k (hk : k < gs.length), gs[k].op = GateOp.not → k = a ∨ k = b)
    (h0 : circuitFun 9 ⟨gs, out⟩ (fun _ => false) = false)
    (h1 : circuitFun 9 ⟨gs, out⟩ (fun _ => true) = true) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ a ∧ circuitFun 9 D = circuitFun 9 ⟨gs, out⟩ := by
  have haL : a < gs.length := by omega
  have hbL' : b < gs.length := by omega
  have hmono : ∀ k (hk : k < gs.length), k ≠ a → k ≠ b → Mono gs[k] := by
    intro k hk hka hkb
    have hop := (hfan gs[k] (List.getElem_mem hk)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exfalso
      rcases honly k hk hop with h | h
      · exact hka h
      · exact hkb h
  obtain ⟨ga, hga⟩ : ∃ g, gs[a] = g := ⟨_, rfl⟩
  obtain ⟨gb, hgb⟩ : ∃ g, gs[b] = g := ⟨_, rfl⟩
  have hna' : ga.op = GateOp.not := hga ▸ hna haL
  have hnb' : gb.op = GateOp.not := hgb ▸ hnb hbL'
  obtain ⟨k, hk⟩ : ∃ k, k = b - (a + 1) := ⟨_, rfl⟩
  obtain ⟨mid, hmid⟩ : ∃ m, m = (gs.drop (a + 1)).take k := ⟨_, rfl⟩
  have hmidlen : mid.length = k := by
    rw [hmid, List.length_take, List.length_drop]
    omega
  have hmidmono : ∀ g ∈ mid, Mono g := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hi' : i < k := hmidlen ▸ hi
    have e : mid[i] = gs[a + 1 + i]'(by omega) := by
      subst hmid
      simp [List.getElem_take, List.getElem_drop]
    rw [e]
    exact hmono _ _ (by omega) (by omega)
  have htakemono : ∀ g ∈ gs.take a, Mono g := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hi' : i < a := by rw [List.length_take] at hi; omega
    rw [List.getElem_take]
    exact hmono _ _ (by omega) (by omega)
  have hsplit : gs = gs.take a ++ (ga :: (mid ++ [gb])) := by
    have e1 : gs.drop a = ga :: gs.drop (a + 1) := by
      rw [← hga]
      exact List.drop_eq_getElem_cons haL
    have e3 : (gs.drop (a + 1)).drop k = [gb] := by
      rw [List.drop_drop, show a + 1 + k = b by omega, ← hgb,
        List.drop_eq_getElem_cons hbL', List.drop_eq_nil_of_le (by omega)]
    have e2 : gs.drop (a + 1) = mid ++ [gb] := by
      calc gs.drop (a + 1)
          = (gs.drop (a + 1)).take k ++ (gs.drop (a + 1)).drop k :=
            (List.take_append_drop _ _).symm
        _ = mid ++ [gb] := by rw [e3, hmid]
    rw [← e2, ← e1, List.take_append_drop]
  have hPlen : ∀ x : Fin 9 → Bool, (List.foldl step (List.ofFn x) (gs.take a)).length = 9 + a := by
    intro x
    rw [length_foldl, List.length_take, List.length_ofFn]
    omega
  let u : (Fin 9 → Bool) → Bool := fun x =>
    (List.foldl step (List.ofFn x) (gs.take a)).getD (ga.inputs.headD (9 + a)) false
  let G : Bool → (Fin 9 → Bool) → Bool := fun c x =>
    (mid.foldl step (List.foldl step (List.ofFn x) (gs.take a) ++ [c])).getD
      (gb.inputs.headD (9 + b)) false
  have hVlen : ∀ (c : Bool) (x : Fin 9 → Bool),
      (mid.foldl step (List.foldl step (List.ofFn x) (gs.take a) ++ [c])).length = 9 + b := by
    intro c x
    rw [length_foldl, List.length_append, hPlen, hmidlen]
    simp
    omega
  have hGmono : ∀ c c' x x', (c = true → c' = true) → (∀ i, x i = true → x' i = true) →
      G c x = true → G c' x' = true := by
    intro c c' x x' hc hx hG
    have hle := le_foldl mid hmidmono _ _
      (le_append _ _ c c' (le_foldl (gs.take a) htakemono _ _ (le_ofFn x x' hx)) hc)
    exact hle.2 _ hG
  have hstepa : ∀ x : Fin 9 → Bool, step (List.foldl step (List.ofFn x) (gs.take a)) ga
      = List.foldl step (List.ofFn x) (gs.take a) ++ [!u x] := by
    intro x
    have h := eval_not ga (List.foldl step (List.ofFn x) (gs.take a)) (9 + a) (hPlen x).le hna'
    exact congrArg (fun v => List.foldl step (List.ofFn x) (gs.take a) ++ [v]) h
  have hC : ∀ x, circuitFun 9 ⟨gs, out⟩ x = !(G (!u x) x) := by
    intro x
    show (gs.foldl step (List.ofFn x)).getD out false = _
    rw [hout]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons, hstepa x, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    have hl := hVlen (!u x) x
    rw [step, ← hl, getD_len]
    exact eval_not gb _ (9 + b) hl.le hnb'
  rw [hC] at h0 h1
  have hT : ∀ x, G true x = true := by
    intro x
    have h : G (!u fun _ => false) (fun _ => false) = true := by simpa using h0
    exact hGmono _ true _ x (fun _ => rfl) (fun i hi => absurd hi (by simp)) h
  have hF : ∀ x, G false x = false := by
    intro x
    by_contra hne
    have hx : G false x = true := by simpa using hne
    have h := hGmono false (!u fun _ => true) x (fun _ => true) (fun h => absurd h (by simp))
      (fun _ _ => rfl) hx
    rw [h] at h1
    simp at h1
  refine ⟨⟨gs.take a, ga.inputs.headD (9 + a)⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact hfan g (List.mem_of_mem_take hg)
  · show (gs.take a).length ≤ a
    simp
  · funext x
    rw [hC x]
    show u x = !(G (!u x) x)
    cases hu : u x
    · simp [hT x]
    · simp [hF x]

end PEqualNP.Outside.L_meta_3606_aux

open PEqualNP.Outside.L_meta_3606_aux

theorem PEqualNP.Outside.L_meta_3606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin x1.gates.length), PEqualNP.MetaComplexity.FanInTwo x1 → x2 < x3 → ↑x3 + (1 : ℕ) = x1.size → x1.output = (9 : ℕ) + ↑x3 → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ (x10 : Fin x1.gates.length), (x1.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.not → x10 = x2 ∨ x10 = x3) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x11 : Fin (9 : ℕ)) => Bool.false) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => Bool.true) = Bool.true → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x13 ∧ x13.size ≤ ↑x2 ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x13 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  intro C a b hfan hab hlast hout hnota hnotb honly h0 h1
  exact main C.gates C.output a b hfan hab hlast hout (fun _ => by simpa using hnota)
    (fun _ => by simpa using hnotb)
    (fun k hk hk' => by simpa [Fin.ext_iff] using honly ⟨k, hk⟩ (by simpa using hk')) h0 h1
