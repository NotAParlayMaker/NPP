import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta201

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wf (gs ++ [g]) x = wf gs x ++ [g.op.eval (g.inputs.map fun i => (wf gs x).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_length : ∀ (gs : List Gate) (x : List Bool), (wf gs x).length = x.length + gs.length
  | [], x => by simp [wf]
  | g :: gs, x => by
    have h := wf_length gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    have e : wf (g :: gs) x = wf gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl
    rw [e, h]
    simp
    omega

theorem wf_ex : ∀ (gs : List Gate) (w : List Bool), ∃ t : List Bool, wf gs w = w ++ t
  | [], w => ⟨[], by simp [wf]⟩
  | g :: gs, w => by
    obtain ⟨t, ht⟩ := wf_ex gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    have e : wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [e, ht, List.append_assoc]⟩

theorem getD_app (W t : List Bool) (i : ℕ) (hi : i < W.length) :
    (W ++ t).getD i false = W.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wires_take (C : Circuit) (x : List Bool) (j i : ℕ)
    (hi : i < (wf (C.gates.take j) x).length) :
    (C.wires x).getD i false = (wf (C.gates.take j) x).getD i false := by
  have h1 : C.wires x = wf (C.gates.drop j) (wf (C.gates.take j) x) := by
    show wf C.gates x = _
    conv_lhs => rw [← List.take_append_drop j C.gates]
    unfold wf
    rw [List.foldl_append]
  obtain ⟨t, ht⟩ := wf_ex (C.gates.drop j) (wf (C.gates.take j) x)
  rw [h1, ht, getD_app _ _ _ hi]

theorem snoc_getD (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false =
      if i < W.length then W.getD i false else if i = W.length then v else false := by
  by_cases h1 : i < W.length
  · rw [if_pos h1, getD_app _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : i = W.length
    · rw [if_pos h2, h2]
      simp
    · rw [if_neg h2]
      exact List.getD_eq_default _ _ (by simp; omega)

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ)
    (h : (List.ofFn x).getD i false = true) : ∃ hi : i < n, x ⟨i, hi⟩ = true := by
  by_cases hi : i < n
  · refine ⟨hi, ?_⟩
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at h
    exact absurd h (by simp)

theorem ofFn_getD' {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) (h : x ⟨i, hi⟩ = true) :
    (List.ofFn x).getD i false = true := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi)]
  simpa using h

theorem ev_and0 : GateOp.and.eval [] = true := rfl

theorem ev_and1 (p : Bool) : GateOp.and.eval [p] = p := by simp [GateOp.eval]

theorem ev_and2 (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]

theorem ev_or0 : GateOp.or.eval [] = false := rfl

theorem ev_or1 (p : Bool) : GateOp.or.eval [p] = p := by simp [GateOp.eval]

theorem ev_or2 (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by simp [GateOp.eval]

def Good (n : ℕ) (C : Circuit) (xu xv : List Bool) : Prop :=
  ∃ j : ℕ, (∃ (g : Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
    g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
    (((C.wires xu).getD a false = true ∧ (C.wires xv).getD a false = false ∧
      (C.wires xv).getD b false = true ∧ (C.wires xu).getD b false = false) ∨
     ((C.wires xv).getD a false = true ∧ (C.wires xu).getD a false = false ∧
      (C.wires xu).getD b false = true ∧ (C.wires xv).getD b false = false)))

theorem inv (n : ℕ) (C : Circuit) (hC : FanInTwo C)
    (hnot : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (xu xv xt : List Bool)
    (hu : xu.length = n) (hv : xv.length = n) (ht : xt.length = n)
    (hbase : ∀ i : ℕ, xt.getD i false = true → xu.getD i false = true ∨ xv.getD i false = true)
    (hG : ¬ Good n C xu xv) :
    ∀ j : ℕ, j ≤ C.gates.length → ∀ i : ℕ, (wf (C.gates.take j) xt).getD i false = true →
      (wf (C.gates.take j) xu).getD i false = true ∨
      (wf (C.gates.take j) xv).getD i false = true := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    exact hbase i hi
  | succ j ih =>
    intro hj i hi
    have hinv := ih (by omega)
    have hjl : j < C.gates.length := hj
    obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hgm : g ∈ C.gates := List.mem_of_getElem? hg
    have htake : C.gates.take (j + 1) = C.gates.take j ++ [g] := by
      rw [List.take_succ, hg]
      rfl
    have hlu : (wf (C.gates.take j) xu).length = n + j := by
      rw [wf_length, List.length_take, hu]
      omega
    have hlv : (wf (C.gates.take j) xv).length = n + j := by
      rw [wf_length, List.length_take, hv]
      omega
    have hlt : (wf (C.gates.take j) xt).length = n + j := by
      rw [wf_length, List.length_take, ht]
      omega
    have eq : ∀ x : List Bool, wf (C.gates.take (j + 1)) x = wf (C.gates.take j) x ++
        [g.op.eval (g.inputs.map fun i => (wf (C.gates.take j) x).getD i false)] := by
      intro x
      rw [htake, wf_snoc]
    rw [eq xt, snoc_getD, hlt] at hi
    rw [eq xu, snoc_getD, hlu, eq xv, snoc_getD, hlv]
    by_cases h1 : i < n + j
    · simp only [if_pos h1] at hi ⊢
      exact hinv i hi
    · by_cases h2 : i = n + j
      · simp only [if_neg h1, if_pos h2] at hi ⊢
        obtain ⟨hop, hlen⟩ := hC g hgm
        have hn := hnot g hgm
        obtain ⟨op, ins⟩ := g
        cases op with
        | not => exact absurd rfl hn
        | mod q => simp at hop
        | maj => simp at hop
        | or =>
          rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · simp only [List.map_nil, ev_or0] at hi
            exact absurd hi (by simp)
          · simp only [List.map_cons, List.map_nil, ev_or1] at hi ⊢
            exact hinv a hi
          · simp only [List.map_cons, List.map_nil, ev_or2, Bool.or_eq_true] at hi ⊢
            rcases hi with hi | hi
            · rcases hinv a hi with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
            · rcases hinv b hi with h | h
              · exact Or.inl (Or.inr h)
              · exact Or.inr (Or.inr h)
          · simp at hlen
        | and =>
          rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · simp only [List.map_nil, ev_and0]
            exact Or.inl trivial
          · simp only [List.map_cons, List.map_nil, ev_and1] at hi ⊢
            exact hinv a hi
          · simp only [List.map_cons, List.map_nil, ev_and2, Bool.and_eq_true] at hi ⊢
            obtain ⟨hta, htb⟩ := hi
            have alt : a < n + j := by
              by_contra hc
              rw [List.getD_eq_default _ _ (by rw [hlt]; omega)] at hta
              exact absurd hta (by simp)
            have blt : b < n + j := by
              by_contra hc
              rw [List.getD_eq_default _ _ (by rw [hlt]; omega)] at htb
              exact absurd htb (by simp)
            have ha := hinv a hta
            have hb := hinv b htb
            by_contra hcon
            apply hG
            refine ⟨j, ⟨GateOp.and, [a, b]⟩, a, b, hg, rfl, rfl, alt, blt, ?_⟩
            rw [wires_take C xu j a (by rw [hlu]; exact alt),
              wires_take C xv j a (by rw [hlv]; exact alt),
              wires_take C xv j b (by rw [hlv]; exact blt),
              wires_take C xu j b (by rw [hlu]; exact blt)]
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact absurd (Or.inl ⟨ha, hb⟩) hcon
            · exact Or.inl ⟨ha, Bool.eq_false_iff.2 (fun h => hcon (Or.inr ⟨h, hb⟩)), hb,
                Bool.eq_false_iff.2 (fun h => hcon (Or.inl ⟨ha, h⟩))⟩
            · exact Or.inr ⟨ha, Bool.eq_false_iff.2 (fun h => hcon (Or.inl ⟨h, hb⟩)), hb,
                Bool.eq_false_iff.2 (fun h => hcon (Or.inr ⟨ha, h⟩))⟩
            · exact absurd (Or.inr ⟨ha, hb⟩) hcon
          · simp at hlen
      · simp only [if_neg h1, if_neg h2] at hi
        exact absurd hi (by simp)

end PEqualNP.Outside.Meta201

theorem PEqualNP.Outside.L_meta_201 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∀ u v : Fin n, G.Adj u v → ∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ (((C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = false) ∨ ((C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = false))) := by
  intro n G inst C hC hnot hfun u v huv
  by_contra hG
  have hbase : ∀ i : ℕ,
      (List.ofFn (fun i : Fin n => decide (i = u) || decide (i = v))).getD i false = true →
      (List.ofFn (fun i : Fin n => decide (i = u))).getD i false = true ∨
      (List.ofFn (fun i : Fin n => decide (i = v))).getD i false = true := by
    intro i hi
    obtain ⟨h, hx⟩ := PEqualNP.Outside.Meta201.ofFn_getD _ i hi
    rw [Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · exact Or.inl (PEqualNP.Outside.Meta201.ofFn_getD' _ i h hx)
    · exact Or.inr (PEqualNP.Outside.Meta201.ofFn_getD' _ i h hx)
  have hinv := PEqualNP.Outside.Meta201.inv n C hC hnot
    (List.ofFn (fun i : Fin n => decide (i = u))) (List.ofFn (fun i : Fin n => decide (i = v)))
    (List.ofFn (fun i : Fin n => decide (i = u) || decide (i = v)))
    (List.length_ofFn) (List.length_ofFn) (List.length_ofFn) hbase hG C.gates.length le_rfl
  rw [List.take_length] at hinv
  have ht : PEqualNP.MetaComplexity.circuitFun n C
      (fun i : Fin n => decide (i = u) || decide (i = v)) = true := by
    rw [congrFun hfun (fun i : Fin n => decide (i = u) || decide (i = v))]
    exact decide_eq_true ⟨u, v, huv, by simp, by simp⟩
  rcases hinv C.output ht with h | h
  · have h' : PEqualNP.MetaComplexity.circuitFun n C (fun i : Fin n => decide (i = u)) = true := h
    rw [congrFun hfun (fun i : Fin n => decide (i = u))] at h'
    obtain ⟨i, j, hij, hi, hj⟩ := of_decide_eq_true h'
    rw [of_decide_eq_true hi, of_decide_eq_true hj] at hij
    exact G.irrefl hij
  · have h' : PEqualNP.MetaComplexity.circuitFun n C (fun i : Fin n => decide (i = v)) = true := h
    rw [congrFun hfun (fun i : Fin n => decide (i = v))] at h'
    obtain ⟨i, j, hij, hi, hj⟩ := of_decide_eq_true h'
    rw [of_decide_eq_true hi, of_decide_eq_true hj] at hij
    exact G.irrefl hij
