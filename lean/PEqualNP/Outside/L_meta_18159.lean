import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18159

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




def wire (w : List Bool) : Option Nat → Bool
  | none => false
  | some i => w.getD i false

def ok (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem stable (hs e : List Gate) (x : List Bool) (w : Option Nat)
    (hb : ∀ i, w = some i → i < x.length + hs.length) :
    wire (run (hs ++ e) x) w = wire (run hs x) w := by
  cases w with
  | none => rfl
  | some i => exact run_prefix _ _ _ _ (hb i rfl)

theorem engine (n : ℕ) (C : Circuit) (a b : Fin n) (S T : Finset ℕ)
    (hC : FanInTwo C) (hd : Disjoint S T)
    (hsz : ∀ j ∈ S, j < C.size) (htz : ∀ j ∈ T, j < C.size)
    (hS : ∀ j ∈ S, ∃ w, (w < n+j ∨ n+C.size ≤ w) ∧ (∀ t ∈ T, w ≠ n+t) ∧
        ∀ x : Fin n → Bool, let u := C.wires (List.ofFn (Function.update (Function.update x a false) b false))
          u.getD (n+j) false = u.getD w false)
    (hT : ∀ j ∈ T, C.output ≠ n+j ∧ ∀ k g, C.gates[k]? = some g → n+j ∈ g.inputs → k ∈ S ∪ T) :
    HasCircuitSize n (fun x => C.eval (List.ofFn (Function.update (Function.update x a false) b false))) (C.size - S.card - T.card) := by
  classical
  let ρ := fun x : Fin n → Bool => Function.update (Function.update x a false) b false
  let F := S ∪ T
  let live := fun w : ℕ => ∀ t ∈ T, w ≠ n+t
  let V := fun (x : Fin n → Bool) => run C.gates (List.ofFn (ρ x))
  have hlen (x : Fin n → Bool) : (V x).length = n + C.size := by simp [V, run_length, Circuit.size]
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Option ℕ), (∀ g ∈ hs, ok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w i, w < n+k → m w = some i → i < n+hs.length) ∧
      ∀ x : Fin n → Bool, ∀ w < n+k, live w → (V x).getD w false = wire (run hs (List.ofFn x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      let m : ℕ → Option ℕ := fun w => if w = a.val ∨ w = b.val then none else some w
      refine ⟨[], m, by simp, by simp, ?_, ?_⟩
      · intro w i hw hm
        simp only [m] at hm
        split_ifs at hm <;> simp_all
      · intro x w hw _
        have hl : w < n := by omega
        rw [show (V x).getD w false = (List.ofFn (ρ x)).getD w false from run_input _ _ _ (by simpa using hl)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hl, Option.getD_some]
        by_cases hb : w = b.val
        · have he : (⟨w, hl⟩ : Fin n) = b := Fin.ext hb
          simp [ρ, he, m, hb, wire]
        · have hb' : (⟨w, hl⟩ : Fin n) ≠ b := fun e => hb (congrArg Fin.val e)
          by_cases ha : w = a.val
          · have he : (⟨w, hl⟩ : Fin n) = a := Fin.ext ha
            have hab : a ≠ b := he ▸ hb'
            simp [ρ, he, Function.update_of_ne hab, m, ha, wire]
          · have ha' : (⟨w, hl⟩ : Fin n) ≠ a := fun e => ha (congrArg Fin.val e)
            simp [ρ, Function.update_of_ne hb', Function.update_of_ne ha', m, ha, hb, wire, run, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hl]
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Option Nat) (e : List Gate), (∀ g ∈ e, ok g) → (∀ t, r = some t → t < n + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (live (n+k) → ∀ x : Fin n → Bool, (V x).getD (n+k) false = wire (run (hs ++ e) (List.ofFn x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Option ℕ), (∀ g ∈ hs, ok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = some t → t < n + hs.length) ∧
      ∀ x : Fin n → Bool, ∀ w < n + (k + 1), live w → (V x).getD w false = wire (run hs (List.ofFn x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw hwLive
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval hwLive x
          · rw [Function.update_of_ne hwe, h4 x w (by omega) hwLive]
            refine (stable hs e (List.ofFn x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            simpa using this

      by_cases hkF : k ∈ F
      · rcases Finset.mem_union.mp hkF with hkS | hkT
        · obtain ⟨w, hrange, hLive, heq⟩ := hS k hkS
          rcases hrange with hw | hw
          · refine fin (m w) [] (by simp) (fun i hi => by simpa using h3 w i hw hi) (by simp [hkF]) (fun _ x => ?_)
            rw [List.append_nil, ← h4 x w hw hLive]
            exact heq x
          · refine fin none [] (by simp) (by simp) (by simp [hkF]) (fun _ x => ?_)
            exact (heq x).trans (List.getD_eq_default _ _ (by change (V x).length ≤ w; rwa [hlen]))
        · exact fin none [] (by simp) (by simp) (by simp [hkF]) (fun h => False.elim (h k hkT rfl))
      · let ren := fun i => if i < n+k then (m i).getD (n+hs.length) else n+hs.length
        let g := C.gates[k]
        let g' : Gate := ⟨g.op, g.inputs.map ren⟩
        have hg := hC g (List.getElem_mem hk')
        have gok : ok g' := ⟨hg.1, by simpa [g'] using hg.2⟩
        refine fin (some (n+hs.length)) [g'] (by simpa using gok) (by simp) (by simp [hkF]) (fun _ x => ?_)
        have rg := run_gate C.gates (List.ofFn (ρ x)) k hk'
        rw [List.length_ofFn] at rg
        change (run C.gates _).getD (n+k) false = (run (hs ++ [g']) (List.ofFn x)).getD (n+hs.length) false
        rw [rg, run_snoc, show n+hs.length = (run hs (List.ofFn x)).length by simp [run_length], getD_at]
        change g.op.eval _ = g.op.eval ((g.inputs.map ren).map _)
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        have hfalse : (run hs (List.ofFn x)).getD (n+hs.length) false = false := List.getD_eq_default _ _ (by simp [run_length])
        simp only [Function.comp, ren]
        split_ifs with hw
        · have hLive : live i := by
            intro t ht he
            apply hkF
            apply (hT t ht).2 k g (by simp [g, hk'])
            simpa [← he] using hi
          have H := h4 x i hw hLive
          cases h : m i <;> simp [h, wire] at H ⊢ <;> simp_all [V]
        · exact hfalse.symm
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem (by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact hsz j h
    · exact htz j h)
  rw [hFc, show F = S ∪ T from rfl, Finset.card_union_of_disjoint hd] at h2
  let out := if C.output < n+C.gates.length then (m C.output).getD (n+hs.length) else n+hs.length
  refine ⟨⟨hs,out⟩, h1, ?_, ?_⟩
  · change hs.length ≤ C.gates.length - S.card - T.card
    omega
  · intro x
    change (run hs (List.ofFn x)).getD out false = (V x).getD C.output false
    have hfalse : (run hs (List.ofFn x)).getD (n+hs.length) false = false := List.getD_eq_default _ _ (by simp [run_length])
    by_cases ho : C.output < n+C.gates.length
    · have H := h4 x C.output ho (fun t ht => (hT t ht).1)
      cases e : m C.output <;> simp [out, ho, e, wire] at H ⊢ <;> simp_all
    · rw [show out = n+hs.length by simp [out, ho], hfalse]
      exact (List.getD_eq_default _ _ (by rw [hlen]; exact Nat.le_of_not_gt ho)).symm

end PEqualNP.Outside.L_meta_18159

theorem PEqualNP.Outside.L_meta_18159 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 x6 : Finset ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     Disjoint x5 x6 →       (∀ x9 ∈ x5, x9 < x2.size) →         (∀ x10 ∈ x6, x10 < x2.size) →           (∀ x11 ∈ x5,               ∃ (x13 : ℕ),                 (x13 < x1 + x11 ∨ x1 + x2.size ≤ x13) ∧                   (∀ x14 ∈ x6, x13 ≠ x1 + x14) ∧                     ∀ (x14 : Fin x1 → Bool),                       have x15 : List Bool := x2.wires (List.ofFn (Function.update (Function.update x14 x3 Bool.false) x4 Bool.false));                       x15.getD (x1 + x11) Bool.false = x15.getD x13 Bool.false) →             (∀ x12 ∈ x6, x2.output ≠ x1 + x12 ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x14]? = Option.some x15 → x1 + x12 ∈ x15.inputs → x14 ∈ x5 ∪ x6) → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => x2.eval (List.ofFn (Function.update (Function.update x13 x3 Bool.false) x4 Bool.false))) (x2.size - x5.card - x6.card)) := PEqualNP.Outside.L_meta_18159.engine
