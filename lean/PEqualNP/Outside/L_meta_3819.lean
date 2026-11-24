import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3819.Aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (l1 l2 : List Gate) (w : List Bool) :
    run (l1 ++ l2) w = run l2 (run l1 w) := List.foldl_append

theorem run_cons (g : Gate) (l : List Gate) (w : List Bool) :
    run (g :: l) w = run l (step w g) := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false =
      if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false :=
  List.getD_eq_default _ _ h

theorem length_run (l : List Gate) (w : List Bool) :
    (run l w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp [run]
  | cons g l ih => rw [run_cons, ih]; simp [step]; omega

theorem getD_run_of_lt (l : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (run l w).getD i false = w.getD i false := by
  induction l generalizing w with
  | nil => rfl
  | cons g l ih =>
    rw [run_cons, ih _ (by simp [step]; omega), step, getD_snoc, if_pos h]

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ eff g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rcases g with ⟨op, ins⟩
  cases op
  case not =>
    rcases ins with _ | ⟨a, t⟩
    · rfl
    · simp [GateOp.eval, h a (by simp [eff])]
  all_goals exact congrArg _ (List.map_congr_left (fun i hi => h i (by simpa [eff] using hi)))

def mapG (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

theorem step_mapG (φ : ℕ → ℕ) (E : Set ℕ) (g : Gate) (W W' : List Bool)
    (hg : ∀ i ∈ eff g, i ∉ E) (hinv : ∀ i, i ∉ E → W'.getD (φ i) false = W.getD i false) :
    step W' (mapG φ g) = W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := by
  simp only [step, mapG, List.map_map]
  rw [eval_congr g ((fun i => W'.getD i false) ∘ φ) (fun i => W.getD i false)
    (fun i hi => hinv i (hg i hi))]

theorem seg (φ : ℕ → ℕ) (E : Set ℕ) : ∀ (l : List Gate) (W W' : List Bool),
    (∀ g ∈ l, ∀ i ∈ eff g, i ∉ E) →
    (∀ i, W.length ≤ i → φ i + W.length = i + W'.length) →
    (∀ i, i < W.length → φ i < W'.length ∨ W'.length + l.length ≤ φ i) →
    (∀ i, i ∉ E → W'.getD (φ i) false = W.getD i false) →
    ∀ i, i ∉ E → (run (l.map (mapG φ)) W').getD (φ i) false = (run l W).getD i false := by
  intro l
  induction l with
  | nil => intro W W' _ _ _ hinv; simpa [run] using hinv
  | cons g l ih =>
    intro W W' hE hoff hrng hinv
    rw [List.map_cons, run_cons, run_cons, step_mapG φ E g W W' (hE g (by simp)) hinv]
    set v := g.op.eval (g.inputs.map fun i => W.getD i false)
    have hstep : step W g = W ++ [v] := rfl
    rw [hstep]
    apply ih
    · exact fun g' hg' => hE g' (by simp [hg'])
    · intro i hi
      simp at hi ⊢
      have := hoff i (by omega)
      omega
    · intro i hi
      simp at hi ⊢
      by_cases h : i < W.length
      · rcases hrng i h with h' | h'
        · left; omega
        · right; simp at h'; omega
      · have := hoff i (by omega)
        left; omega
    · intro i hiE
      rw [getD_snoc, getD_snoc]
      by_cases h : i < W.length
      · rw [if_pos h]
        rcases hrng i h with h' | h'
        · rw [if_pos h', hinv i hiE]
        · simp at h'
          rw [if_neg (by omega), if_neg (by omega), ← hinv i hiE, getD_ge _ _ (by omega)]
      · rw [if_neg h]
        have := hoff i (by omega)
        by_cases h2 : i = W.length
        · rw [if_neg (by omega), if_pos (by omega), if_pos h2]
        · rw [if_neg (by omega), if_neg (by omega), if_neg h2]


theorem mapG_id_map (l : List Gate) : l.map (mapG id) = l := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.map_cons, ih]; cases g; simp [mapG]

theorem drop (m : ℕ) (l1 l2 : List Gate) (G : Gate) (out q : ℕ) (E : Set ℕ)
    (hq : q < m + 1 + l1.length)
    (hEsub : ∀ i ∈ E, i = m + 1 + l1.length)
    (hE : ∀ g ∈ l2, ∀ i ∈ eff g, i ∉ E) (hout : out ∉ E)
    (hval : m + 1 + l1.length ∉ E → ∀ x : List Bool, x.length = m →
      G.op.eval (G.inputs.map fun i => (run l1 (x ++ [false])).getD i false) =
        (run l1 (x ++ [false])).getD q false) :
    ∃ D : Circuit, D.gates.length = l1.length + l2.length ∧
      (∀ g ∈ D.gates, ∃ g0 ∈ l1 ++ l2, g.op = g0.op ∧ g.inputs.length = g0.inputs.length) ∧
      ∀ x : List Bool, x.length = m →
        D.eval x = (Circuit.mk (l1 ++ G :: l2) out).eval (x ++ [false]) := by
  set p := m + 1 + l1.length with hp
  set B := p + l2.length + 1 with hB
  set φ1 : ℕ → ℕ := fun i => if i < m then i else if i = m then B else i - 1 with hφ1
  set φ2 : ℕ → ℕ := fun i => if i < p then φ1 i else if i = p then φ1 q else i - 2 with hφ2
  have r1 : ∀ i, i < p → φ1 i < m + l1.length ∨ m + l1.length + l2.length ≤ φ1 i := by
    intro i hi; simp only [hφ1]; split_ifs <;> omega
  refine ⟨⟨l1.map (mapG φ1) ++ l2.map (mapG φ2), φ2 out⟩, by simp, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g0, h0, rfl⟩ | ⟨g0, h0, rfl⟩
    · exact ⟨g0, by simp [h0], rfl, by simp [mapG]⟩
    · exact ⟨g0, by simp [h0], rfl, by simp [mapG]⟩
  · intro x hx
    have h1 := seg φ1 ∅ l1 (x ++ [false]) x (by simp)
      (by intro i hi; simp at hi ⊢; simp only [hφ1]; split_ifs <;> omega)
      (by intro i hi; simp at hi ⊢; simp only [hφ1]; split_ifs <;> omega)
      (by
        intro i _
        rw [getD_snoc]
        simp only [hφ1]
        split_ifs <;> first | rfl | (rw [getD_ge] <;> omega))
    simp only [Set.mem_empty_iff_false, not_false_eq_true, forall_const] at h1
    set W1 := run l1 (x ++ [false]) with hW1
    set W1' := run (l1.map (mapG φ1)) x with hW1'
    have lW1 : W1.length = p := by rw [hW1, length_run]; simp; omega
    have lW1' : W1'.length = m + l1.length := by rw [hW1', length_run]; simp; omega
    set v := G.op.eval (G.inputs.map fun i => W1.getD i false) with hv
    have hstep : step W1 G = W1 ++ [v] := rfl
    rw [Circuit.eval, Circuit.eval, wires_eq, wires_eq]
    simp only [List.map_append]
    rw [run_append, run_append, run_cons, hstep, ← hW1']
    apply seg φ2 E l2 (W1 ++ [v]) W1' hE
    · intro i hi; simp at hi; rw [lW1] at hi; simp only [hφ2]; split_ifs <;> simp <;> omega
    · intro i hi
      simp at hi
      rw [lW1'] 
      simp only [hφ2]
      split_ifs with h h'
      · exact r1 i h
      · exact r1 q hq
      · omega
    · intro i hiE
      rw [getD_snoc, lW1]
      simp only [hφ2]
      split_ifs with h h'
      · rw [h1]
      · subst h'
        rw [h1]
        exact (hval hiE x hx).symm
      · rw [getD_ge]; omega
    · exact hout

theorem Rf (H : Gate)
    (hop : H.op = GateOp.and ∨ H.op = GateOp.or ∨ H.op = GateOp.not)
    (hlen : H.inputs.length ≤ 2) (c z p' : ℕ) (hc : c ∈ eff H) (hz : z < p') :
    H.op = GateOp.not ∨ ∃ q < p', ∀ W : List Bool, W.length = p' →
      W.getD c false = false → W.getD z false = false →
        H.op.eval (H.inputs.map fun i => W.getD i false) = W.getD q false := by
  obtain ⟨op, ins⟩ := H
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl | rfl
  · right
    refine ⟨z, hz, fun W _ hWc hWz => ?_⟩
    rw [hWz]
    simp only [GateOp.eval]
    simpa using ⟨c, by simpa [eff] using hc, hWc⟩
  · right
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
    · simp [eff] at hc
    · simp [eff] at hc
      subst hc
      exact ⟨z, hz, fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · simp [eff] at hc
      rcases hc with rfl | rfl
      · refine ⟨if b < p' then b else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with hb
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W b (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
      · refine ⟨if a < p' then a else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with ha
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W a (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
    · simp at hlen
  · left; rfl

theorem Rt (H : Gate)
    (hop : H.op = GateOp.and ∨ H.op = GateOp.or ∨ H.op = GateOp.not)
    (hlen : H.inputs.length ≤ 2) (c z p' : ℕ) (hc : c ∈ eff H) (hc' : c < p') (hz : z < p') :
    ∃ q < p', ∀ W : List Bool, W.length = p' →
      W.getD c false = true → W.getD z false = false →
        H.op.eval (H.inputs.map fun i => W.getD i false) = W.getD q false := by
  obtain ⟨op, ins⟩ := H
  simp only at hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [eff] at hc
  · rcases hop with rfl | rfl | rfl <;> simp [eff] at hc <;> subst hc
    · exact ⟨c, hc', fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · exact ⟨c, hc', fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · exact ⟨z, hz, fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
  · rcases hop with rfl | rfl | rfl
    · simp [eff] at hc
      rcases hc with rfl | rfl
      · refine ⟨if b < p' then b else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with hb
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W b (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
      · refine ⟨if a < p' then a else z, by split_ifs <;> omega, fun W hW h1 h2 => ?_⟩
        split_ifs with ha
        · (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
        · have h3 := getD_ge W a (by omega)
          (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])
    · exact ⟨c, hc', fun W _ h1 h2 => by
        simp [eff] at hc
        rcases hc with rfl | rfl <;> (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
    · simp [eff] at hc
      subst hc
      exact ⟨z, hz, fun W _ h1 h2 => by (simp only [List.getD_eq_getElem?_getD] at *; simp_all [GateOp.eval])⟩
  · simp at hlen

theorem ofFn_snoc {n : ℕ} (y : Fin n → Bool) (c : Bool) :
    List.ofFn (Fin.snoc y c : Fin (n + 1) → Bool) = List.ofFn y ++ [c] := by
  rw [List.ofFn_succ']; simp

def fwd (n : ℕ) (C : Circuit) : Circuit :=
  let ψ : ℕ → ℕ := fun i => if i < n then i else if i = n then n + 2 else i + 2
  ⟨⟨GateOp.or, [n, n + 1]⟩ :: C.gates.map (mapG ψ), ψ C.output⟩

theorem fwd_eval (n : ℕ) (C : Circuit) (y : List Bool) (hy : y.length = n) (a b : Bool) :
    (fwd n C).eval (y ++ [a, b]) = C.eval (y ++ [a || b]) := by
  set ψ : ℕ → ℕ := fun i => if i < n then i else if i = n then n + 2 else i + 2 with hψ
  have hs : step (y ++ [a, b]) ⟨GateOp.or, [n, n + 1]⟩ = (y ++ [a, b]) ++ [a || b] := by
    subst hy
    simp [step, GateOp.eval, List.getD_eq_getElem?_getD]
  rw [Circuit.eval, Circuit.eval, wires_eq, wires_eq]
  simp only [fwd]
  rw [run_cons, hs]
  apply seg ψ ∅ C.gates (y ++ [a || b]) (y ++ [a, b] ++ [a || b]) (by simp)
  · intro i hi; simp at hi ⊢; simp only [hψ]; split_ifs <;> omega
  · intro i hi; simp at hi ⊢; simp only [hψ]; split_ifs <;> omega
  · intro i _
    subst hy
    simp only [hψ]
    split_ifs with h1 h2
    · rw [getD_snoc, if_pos (by simp; omega), getD_snoc, if_pos h1]
      exact List.getD_append _ _ _ _ h1
    · subst h2; simp [List.getD_eq_getElem?_getD]
    · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
  · simp


theorem conv (n s : ℕ) (g : (Fin (n + 1) → Bool) → Bool)
    (hdep : ∃ y : Fin n → Bool, g (Fin.snoc y false) ≠ g (Fin.snoc y true))
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ s + 1)
    (heval : ∀ x : Fin (n + 2) → Bool, C.eval (List.ofFn x) =
      g (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc)
        (x (Fin.last n).castSucc || x (Fin.last (n + 1))))) :
    PEqualNP.MetaComplexity.HasCircuitSize (n + 1) g s := by
  obtain ⟨y0, hy0⟩ := hdep
  have key : ∀ (yf : Fin n → Bool) (a b : Bool),
      C.eval (List.ofFn yf ++ [a, b]) = g (Fin.snoc yf (a || b)) := by
    intro yf a b
    have := heval (Fin.snoc (Fin.snoc yf a) b)
    rw [ofFn_snoc, ofFn_snoc] at this
    simpa using this
  have gx : ∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x ++ [false]) = g x := by
    intro x
    have hx : List.ofFn x = List.ofFn (Fin.init x) ++ [x (Fin.last n)] := by
      rw [← ofFn_snoc, Fin.snoc_init_self]
    have := key (Fin.init x) (x (Fin.last n)) false
    rw [Bool.or_false, Fin.snoc_init_self] at this
    rw [hx, List.append_assoc]
    exact this
  have finish : ∀ (l1 l2 : List Gate) (G : Gate), C.gates = l1 ++ G :: l2 →
      (∃ D : Circuit, D.gates.length = l1.length + l2.length ∧
        (∀ g ∈ D.gates, ∃ g0 ∈ l1 ++ l2, g.op = g0.op ∧ g.inputs.length = g0.inputs.length) ∧
        ∀ x : List Bool, x.length = n + 1 →
          D.eval x = (Circuit.mk (l1 ++ G :: l2) C.output).eval (x ++ [false])) →
      PEqualNP.MetaComplexity.HasCircuitSize (n + 1) g s := by
    rintro l1 l2 G hC ⟨D, hlen, hg, hD⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro gt hgt
      obtain ⟨g0, h0, hop, hl⟩ := hg gt hgt
      have := hfan g0 (by rw [hC]; simp only [List.mem_append, List.mem_cons] at h0 ⊢; tauto)
      exact ⟨hop ▸ this.1, hl ▸ this.2⟩
    · simp only [Circuit.size, hC, List.length_append, List.length_cons] at hsize ⊢; omega
    · intro x
      have hCm : Circuit.mk (l1 ++ G :: l2) C.output = C := by rw [← hC]
      rw [hD _ (by simp), hCm]
      exact gx x
  set m := n + 1 with hm
  have lW : ∀ (l : List Gate) (x : List Bool), (run l (x ++ [false])).length =
      x.length + 1 + l.length := by
    intro l x; rw [length_run]; simp
  have Wm : ∀ (l : List Gate) (x : List Bool), x.length = m →
      (run l (x ++ [false])).getD m false = false := by
    intro l x hx
    rw [getD_run_of_lt _ _ _ (by simp; omega), getD_snoc, if_neg (by omega), if_pos hx.symm]
  by_cases hread : ∃ G ∈ C.gates, m ∈ eff G
  · obtain ⟨G, hGmem, hGm⟩ := hread
    obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hGmem
    have hGf := hfan G hGmem
    have hop : G.op = GateOp.and ∨ G.op = GateOp.or ∨ G.op = GateOp.not := by simpa using hGf.1
    rcases Rf G hop hGf.2 m m (m + 1 + l1.length) hGm (by omega) with hnot | ⟨q, hq, hqv⟩
    · obtain ⟨t, ht⟩ : ∃ t, G.inputs = m :: t := by
        rcases hi : G.inputs with _ | ⟨a, t⟩
        · simp [eff, hnot, hi] at hGm
        · simp [eff, hnot, hi] at hGm
          exact ⟨t, by rw [hGm]⟩
      set p := m + 1 + l1.length with hp
      have Gtrue : ∀ x : List Bool, x.length = m →
          G.op.eval (G.inputs.map fun i => (run l1 (x ++ [false])).getD i false) = true := by
        intro x hx
        rw [hnot, ht]
        simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [Wm l1 x hx]
        rfl
      have Wp : ∀ x : List Bool, x.length = m → ∀ k : List Gate,
          (run (l1 ++ G :: k) (x ++ [false])).getD p false = true := by
        intro x hx k
        rw [run_append, run_cons, getD_run_of_lt _ _ _ (by simp [step, lW, hx]; omega), step,
          getD_snoc, if_neg (by rw [lW, hx]; omega), if_pos (by rw [lW, hx])]
        exact Gtrue x hx
      by_cases hout : C.output = p
      · exfalso
        apply hy0
        have hT : ∀ x : List Bool, x.length = m → C.eval (x ++ [false]) = true := by
          intro x hx
          rw [Circuit.eval, wires_eq, hsplit, hout]
          exact Wp x hx l2
        rw [← gx, ← gx, hT _ (by simp [hm]), hT _ (by simp [hm])]
      · by_cases hH : ∃ H ∈ l2, p ∈ eff H
        · obtain ⟨H, hHmem, hHp⟩ := hH
          obtain ⟨k1, k2, hk⟩ := List.append_of_mem hHmem
          have hC' : C.gates = (l1 ++ G :: k1) ++ H :: k2 := by rw [hsplit, hk]; simp
          have hHf := hfan H (by rw [hC']; simp)
          have hopH : H.op = GateOp.and ∨ H.op = GateOp.or ∨ H.op = GateOp.not := by
            simpa using hHf.1
          obtain ⟨q, hq, hqv⟩ := Rt H hopH hHf.2 p m (p + 1 + k1.length) hHp (by omega)
            (by omega)
          apply finish _ _ _ hC'
          refine drop m (l1 ++ G :: k1) k2 H C.output q ∅ (by simp; omega) (by simp) (by simp)
            (by simp) ?_
          intro _ x hx
          exact hqv _ (by rw [lW, hx]; simp; omega) (Wp x hx k1) (Wm _ x hx)
        · push_neg at hH
          apply finish l1 l2 G hsplit
          refine drop m l1 l2 G C.output m {p} (by omega) (by simp [hp]) ?_ (by simpa using hout) ?_
          · intro g' hg' i hi
            simp only [Set.mem_singleton_iff]
            rintro rfl
            exact hH g' hg' hi
          · intro h
            exact (h (Set.mem_singleton p)).elim
    · apply finish l1 l2 G hsplit
      refine drop m l1 l2 G C.output q ∅ hq (by simp) (by simp) (by simp) ?_
      intro _ x hx
      exact hqv _ (by rw [lW, hx]) (Wm l1 x hx) (Wm l1 x hx)
  · push_neg at hread
    exfalso
    by_cases hom : C.output = m
    · have hb : ∀ a b : Bool, C.eval (List.ofFn y0 ++ [a, b]) = b := by
        intro a b
        rw [Circuit.eval, wires_eq, hom, getD_run_of_lt _ _ _ (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, hm]
      have e1 := key y0 true false
      have e2 := key y0 false true
      rw [hb] at e1 e2
      simp only [Bool.true_or, Bool.false_or] at e1 e2
      rw [← e1] at e2
      exact absurd e2 (by decide)
    · have split : ∀ b : Bool, List.ofFn y0 ++ [false, b] = (List.ofFn y0 ++ [false]) ++ [b] := by
        intro b; simp
      have hs := seg id {m} C.gates (List.ofFn y0 ++ [false, false])
        (List.ofFn y0 ++ [false, true])
        (fun g' hg' i hi h => hread g' hg' (by rw [Set.mem_singleton_iff] at h; rw [← h]; exact hi))
        (by intro i _; simp)
        (by intro i hi; left; simpa using hi)
        (by
          intro i hi
          rw [Set.mem_singleton_iff] at hi
          show (List.ofFn y0 ++ [false, true]).getD i false =
            (List.ofFn y0 ++ [false, false]).getD i false
          have e : ∀ b : Bool, (List.ofFn y0 ++ [false, b]).getD i false =
              if i < (List.ofFn y0 ++ [false]).length then (List.ofFn y0 ++ [false]).getD i false
              else if i = (List.ofFn y0 ++ [false]).length then b else false := by
            intro b; rw [split b]; exact getD_snoc _ b i
          rw [e, e]
          by_cases h : i < (List.ofFn y0 ++ [false]).length
          · rw [if_pos h, if_pos h]
          · have : i ≠ (List.ofFn y0 ++ [false]).length := by simp; omega
            rw [if_neg h, if_neg h, if_neg this, if_neg this])
        C.output (by simpa using hom)
      rw [mapG_id_map] at hs
      have h1 := key y0 false true
      have h0 := key y0 false false
      rw [Circuit.eval, wires_eq] at h1 h0
      simp only [id] at hs
      rw [hs, h0] at h1
      exact hy0 (by simpa using h1)

end PEqualNP.Outside.L_meta_3819.Aux

namespace PEqualNP.Outside.L_meta_3819.Live

variable {α : Type} [DecidableEq α]

-- The ordinary circuit may consult any earlier result.
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

-- A live set contains just the wires actually read by the remaining computation.
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

-- Any pair of rows which the output separates must stay separated at each cut.
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

end PEqualNP.Outside.L_meta_3819.Live

namespace PEqualNP.Outside.L_meta_3819.Live
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end PEqualNP.Outside.L_meta_3819.Live

namespace PEqualNP.Outside.L_meta_3819.Check

abbrev W := BitVec 132
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 66)).setWidth 66
def cuts (ws : List W) : BitVec 66 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 66) ++ (0 : BitVec 66)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

def rawInputs : List W :=
  [0xfffff11089008100bffffc00000000000,
   0x11089fffff111000000003ffffc000000,
   0xff10022112fff2203fc00000003ffc000,
   0x22f90ff200222fe4003e03fc000003f80,
   0xf027844fa0f4045d3c01e003e03c00070,
   0x44422f04784f8f0b800003c01e03e3c0e,
   0x888448884488489240000000000000000]

def inputs := rawInputs.map canon

end PEqualNP.Outside.L_meta_3819.Check
namespace PEqualNP.Outside.L_meta_3819.Check
variable {α : Type}

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end PEqualNP.Outside.L_meta_3819.Check

namespace PEqualNP.Outside.L_meta_3819.Check
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 66) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (66+i.val)

theorem neg_differs (i : Fin 66) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 132 := by omega
  have hi : 66+i.val < 132 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 66) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 66) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (66+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (66+i.val) := by simpa [differs] using h.2
  have lo : i.val < 132 := by omega
  have hi : 66+i.val < 132 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 66) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬66 + i.val < 66 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 66) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : PEqualNP.Outside.L_meta_3819.Live.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := PEqualNP.Outside.L_meta_3819.Live.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 66)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end PEqualNP.Outside.L_meta_3819.Check

namespace PEqualNP.Outside.L_meta_3819.Check

def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

end PEqualNP.Outside.L_meta_3819.Check

namespace PEqualNP.Outside.L_meta_3819.Check
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 132) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 132) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩


theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)


def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 132 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 66) ++ (0 : BitVec 66))) :
    PEqualNP.Outside.L_meta_3819.Live.build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 66) ++ (0 : BitVec 66)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 66) ++ (0 : BitVec 66)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 66) ++ (0 : BitVec 66)) := by
      intro k; simpa only [List.foldl_cons,hstep] using he k
    have appendOK (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr h)) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
      · simp_all


def graph (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
  (x 0 && x 5) || x 6

def assignment (k : Fin 132) (i : Fin 7) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : PEqualNP.Outside.L_meta_3819.Live.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 66) := [1, 14, 7, 4, 2, 5, 0]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (66+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := PEqualNP.Outside.L_meta_3819.Live.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 132) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 132) : graph (assignment k) =
    bit k ((-1 : BitVec 66) ++ (0 : BitVec 66)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
      (x 4 &&& x 5) ||| (x 0 &&& x 5) ||| x 6 =
      ((-1 : BitVec 66) ++ (0 : BitVec 66)) := by decide
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 132) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 66) ++ (0 : BitVec 66)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = graph x) :
    PEqualNP.Outside.L_meta_3819.Live.build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : PEqualNP.Outside.L_meta_3819.Live.build basicOps goal k inputs.toFinset) :
    PEqualNP.Outside.L_meta_3819.Live.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := PEqualNP.Outside.L_meta_3819.Live.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : PEqualNP.Outside.L_meta_3819.Live.live basicOps goal m inputs.toFinset) :
    PEqualNP.Outside.L_meta_3819.Live.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end PEqualNP.Outside.L_meta_3819.Check

namespace PEqualNP.Outside.L_meta_3819.Check

def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩

end PEqualNP.Outside.L_meta_3819.Check

namespace PEqualNP.Outside.L_meta_3819.Check

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : PEqualNP.Outside.L_meta_3819.Live.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases PEqualNP.Outside.L_meta_3819.Live.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : PEqualNP.Outside.L_meta_3819.Live.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := PEqualNP.Outside.L_meta_3819.Live.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem lower_of_optimized (check : optimized 8 2 inputs = false) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize 7 graph s) : 9 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 8 := by change C.gates.length ≤ s at hsize; omega
  have searched := optimized_complete 8 inputs 2 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end PEqualNP.Outside.L_meta_3819.Check

namespace PEqualNP.Outside.L_meta_3819.Check
def rootF (i : Nat) : Bool :=
  ((pairs inputs)[i]?).any (fun (a,b,rest) => dispatch 2 (optimized 7) a b rest)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier0 : rootF 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier1 : rootF 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier2 : rootF 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier3 : rootF 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier4 : rootF 4 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier5 : rootF 5 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier6 : rootF 6 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier7 : rootF 7 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier8 : rootF 8 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier9 : rootF 9 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier10 : rootF 10 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier11 : rootF 11 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier12 : rootF 12 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier13 : rootF 13 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier14 : rootF 14 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier15 : rootF 15 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier16 : rootF 16 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier17 : rootF 17 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier18 : rootF 18 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier19 : rootF 19 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier20 : rootF 20 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem all_front : optimized 8 2 inputs = false := by
  have hlen : (pairs inputs).length = 21 := by decide
  have allRoots : ∀ i : Fin 21, rootF i.val = false := by
    intro i
    fin_cases i
    · exact frontier0
    · exact frontier1
    · exact frontier2
    · exact frontier3
    · exact frontier4
    · exact frontier5
    · exact frontier6
    · exact frontier7
    · exact frontier8
    · exact frontier9
    · exact frontier10
    · exact frontier11
    · exact frontier12
    · exact frontier13
    · exact frontier14
    · exact frontier15
    · exact frontier16
    · exact frontier17
    · exact frontier18
    · exact frontier19
    · exact frontier20
  apply Bool.eq_false_iff.mpr
  intro h
  change (_ || _) = true at h
  simp only [Bool.or_eq_true] at h
  rcases h with stop | step
  · exact (by decide : (inputs == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := allRoots (Fin.cast hlen i)
    simp only [Fin.val_cast, rootF, List.getElem?_eq_getElem i.isLt, Option.any_some] at no
    rw [← hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)

end PEqualNP.Outside.L_meta_3819.Check

namespace PEqualNP.Outside.L_meta_3819.Glue

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3819.Aux

-- The posted function: a six-cycle on the inputs 0, 1, 2, 3, 8, 5, OR-ed with the inputs 4, 6, 7.
def posted (x : Fin 9 → Bool) : Bool :=
  x 4 || x 6 || x 7 || x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 3 && x 8 ||
    x 8 && x 5

-- The seven-variable core with its last input split into an OR of two inputs, twice.
def G8 (z : Fin 8 → Bool) : Bool :=
  Check.graph (Fin.snoc (fun i : Fin 6 => z i.castSucc.castSucc)
    (z (Fin.last 6).castSucc || z (Fin.last 7)))

def G9 (x : Fin 9 → Bool) : Bool :=
  G8 (Fin.snoc (fun i : Fin 7 => x i.castSucc.castSucc)
    (x (Fin.last 7).castSucc || x (Fin.last 8)))

-- Renaming of the input wires that moves the cycle to 0..5 and the free inputs to 6, 7, 8.
def phi (i : ℕ) : ℕ :=
  if i = 4 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 4 else i

theorem phi_ge (i : ℕ) (h : 9 ≤ i) : phi i = i := by
  unfold phi
  split_ifs <;> omega

theorem phi_lt (i : ℕ) (h : i < 9) : phi i < 9 := by
  unfold phi
  split_ifs <;> omega

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

theorem posted_rename (y : Fin 9 → Bool) :
    posted (fun i : Fin 9 => (List.ofFn y).getD (phi i.val) false) = G9 y := by
  show (y 6 || y 7 || y 8 || y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 5 || y 3 && y 4 ||
      y 4 && y 5) =
    ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 5) ||
      (y 0 && y 5) || (y 6 || (y 7 || y 8)))
  ac_rfl

theorem rename (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 10)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = posted x) :
    HasCircuitSize 9 G9 10 := by
  refine ⟨⟨C.gates.map (mapG phi), phi C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hfan g0 h0).1, by simpa [mapG] using (hfan g0 h0).2⟩
  · simpa [Circuit.size] using hsize
  · intro y
    have key := seg phi ∅ C.gates
      (List.ofFn (fun i : Fin 9 => (List.ofFn y).getD (phi i.val) false)) (List.ofFn y)
      (fun _ _ _ _ => Set.notMem_empty _)
      (by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        rw [phi_ge i hi])
      (by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        exact Or.inl (phi_lt i hi))
      (by
        intro i _
        rw [getD_ofFn (fun j : Fin 9 => (List.ofFn y).getD (phi j.val) false) i]
        split
        · rfl
        · rename_i hlt
          rw [phi_ge i (by omega)]
          exact getD_ge _ _ (by simp only [List.length_ofFn]; omega))
      C.output (Set.notMem_empty _)
    have hC := heval (fun i : Fin 9 => (List.ofFn y).getD (phi i.val) false)
    rw [Circuit.eval, wires_eq] at hC
    show (run (C.gates.map (mapG phi)) (List.ofFn y)).getD (phi C.output) false = G9 y
    rw [key, hC]
    exact posted_rename y

theorem main (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 10) :
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ posted x := by
  by_contra hcon
  have heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = posted x := by
    intro x
    by_contra h
    exact hcon ⟨x, h⟩
  obtain ⟨C9, hf9, hs9, he9⟩ := rename C hfan hsize heval
  obtain ⟨C8, hf8, hs8, he8⟩ := conv 7 9 G8 ⟨fun _ => false, by decide⟩ C9 hf9 hs9 he9
  have h7 : HasCircuitSize 7 Check.graph 8 :=
    conv 6 8 Check.graph ⟨fun _ => false, by decide⟩ C8 hf8 hs8 he8
  have h9 := Check.lower_of_optimized Check.all_front 8 h7
  omega

end PEqualNP.Outside.L_meta_3819.Glue

theorem PEqualNP.Outside.L_meta_3819 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (10 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ (x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) || x4 (7 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C hfan hsize
  exact PEqualNP.Outside.L_meta_3819.Glue.main C hfan hsize
