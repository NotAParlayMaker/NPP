import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4861

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



def rho (n d i : ℕ) : ℕ := if i < n + d then i else i - 1

def fx (n d L j i : ℕ) : ℕ := if i < n + j then rho n d i else n + L

def ng (n : ℕ) (gs : List Gate) (d : ℕ) : List Gate :=
  List.ofFn fun k : Fin (gs.length - 1) =>
    let j := if k.val < d then k.val else k.val + 1
    let h := gs.getD j ⟨GateOp.or, []⟩
    ⟨h.op, h.inputs.map (fx n d gs.length j)⟩

theorem ng_len (n : ℕ) (gs : List Gate) (d : ℕ) : (ng n gs d).length = gs.length - 1 := by
  simp [ng]

theorem sem (n : ℕ) (gs : List Gate) (d : ℕ) (hd : d < gs.length)
    (hno : ∀ (j : ℕ) (hj : j < gs.length), d < j → n + d ∉ gs[j].inputs)
    (x : List Bool) (hx : x.length = n) :
    ∀ w, w < n + gs.length → w ≠ n + d →
      (run (ng n gs d) x).getD (rho n d w) false = (run gs x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwd
    by_cases h9 : w < n
    · rw [rho, if_pos (by omega), run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      have old := run_gate gs x j hj
      rw [hx] at old
      rw [old]
      obtain ⟨k, hkj, hkL, hr⟩ : ∃ k, (if k < d then k else k + 1) = j ∧
          k < gs.length - 1 ∧ rho n d (n + j) = n + k := by
        by_cases h : j < d
        · exact ⟨j, by rw [if_pos h], by omega, by unfold rho; split_ifs <;> omega⟩
        · exact ⟨j - 1, by rw [if_neg (by omega)]; omega, by omega, by
            unfold rho; split_ifs <;> omega⟩
      have new := run_gate (ng n gs d) x k (by rw [ng_len]; omega)
      rw [hx] at new
      have e : (ng n gs d)[k]'(by rw [ng_len]; omega) =
          ⟨gs[j].op, gs[j].inputs.map (fx n d gs.length j)⟩ := by
        have hgd : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := List.getD_eq_getElem _ _ hj
        simp only [ng, List.getElem_ofFn, hkj, hgd]
      rw [hr, new, e, List.map_map]
      refine congrArg _ (List.map_congr_left fun i hi => ?_)
      simp only [Function.comp]
      by_cases hij : i < n + j
      · have hne : i ≠ n + d := by
          rintro rfl
          exact hno j hj (by omega) hi
        have hlt : rho n d i < n + k := by
          by_cases hkd : k < d
          · rw [if_pos hkd] at hkj
            unfold rho; split_ifs <;> omega
          · rw [if_neg hkd] at hkj
            unfold rho; split_ifs <;> omega
        have hfx : fx n d gs.length j i = rho n d i := if_pos hij
        rw [hfx, if_pos hlt, if_pos hij]
        exact ih i hij (by omega) hne
      · have hfx : fx n d gs.length j i = n + gs.length := if_neg hij
        rw [hfx, if_neg hij, if_neg (by omega)]

theorem del (n : ℕ) (C : Circuit) (hC : FanInTwo C) (d : ℕ) (hd : d < C.gates.length)
    (hno : ∀ (j : ℕ) (hj : j < C.gates.length), d < j → n + d ∉ C.gates[j].inputs)
    (ho : C.output ≠ n + d) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  let o := if C.output < n + C.gates.length then rho n d C.output else n + C.gates.length
  refine ⟨⟨ng n C.gates d, o⟩, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hh
    have hj : (if k.val < d then k.val else k.val + 1) < C.gates.length := by
      have := k.isLt
      split_ifs <;> omega
    dsimp only
    rw [List.getD_eq_getElem _ _ hj]
    have := hC _ (List.getElem_mem hj)
    exact ⟨this.1, by simpa using this.2⟩
  · change (ng n C.gates d).length + 1 = C.gates.length
    rw [ng_len]; omega
  · funext x
    change (run (ng n C.gates d) (List.ofFn x)).getD o false =
      (run C.gates (List.ofFn x)).getD C.output false
    by_cases h : C.output < n + C.gates.length
    · simp only [o, if_pos h]
      exact sem n _ d hd hno _ (by simp) _ h ho
    · simp only [o, if_neg h]
      rw [List.getD_eq_default _ _ (by rw [run_length, ng_len, List.length_ofFn]; omega),
        List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]

def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi


def rd (g : Gate) : List ℕ := List.take (bif g.op.eval [false] then 1 else 2) g.inputs

def nm (g : Gate) : Gate := ⟨g.op, rd g⟩

theorem nm_eval (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (u : ℕ → Bool) :
    (nm g).op.eval ((nm g).inputs.map u) = g.op.eval (g.inputs.map u) := by
  have ht : List.take 2 g.inputs = g.inputs := List.take_of_length_le hlen
  rcases hop with h | h | h
  · simp [nm, rd, h, GateOp.eval, ht]
  · simp [nm, rd, h, GateOp.eval, ht]
  · simp only [nm, rd, h, GateOp.eval]
    cases hI : g.inputs with
    | nil => simp
    | cons a t => simp

theorem run_nm (gs : List Gate) (x : List Bool)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) : run (gs.map nm) x = run gs x := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc, ih fun g' h' => h g' (by simp [h']),
      nm_eval g (h g (by simp)).1 (h g (by simp)).2]

theorem slots (S : Finset ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∑ w ∈ S, gs.countP (fun g => (rd g).contains w) + gs.countP (fun g => g.op.eval [false]) ≤
      2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ih' := ih fun g' h' => h g' (by simp [h'])
    obtain ⟨hop, hlen⟩ := h g (by simp)
    have hb : ∑ w ∈ S, (if (rd g).contains w = true then 1 else 0) ≤ (rd g).length := by
      rw [← Finset.card_filter]
      refine le_trans (Finset.card_le_card (t := (rd g).toFinset) fun w hw => ?_)
        (List.toFinset_card_le _)
      simpa using (Finset.mem_filter.1 hw).2
    have hr : (rd g).length + (if g.op.eval [false] = true then 1 else 0) ≤ 2 := by
      have ht : (rd g).length ≤ bif g.op.eval [false] then 1 else 2 := List.length_take_le _ _
      cases hv : g.op.eval [false]
      · rw [hv] at ht
        simpa using ht
      · rw [hv] at ht
        have : (rd g).length ≤ 1 := ht
        simp
        omega
    simp only [List.countP_cons, Finset.sum_add_distrib, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_4861

open PEqualNP.Outside.L_meta_4861 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_4861 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x8 → x5.size ≤ x8) → x4.card + ∑ x9 ∈ x4ᶜ, (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs).contains ↑x9) x5.gates).length + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x9.op.eval [Bool.false]) x5.gates).length ≤ x5.size + (1 : ℕ) := by
  classical
  intro n G _ A C hC hf hmin
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  let C' : Circuit := ⟨C.gates.map nm, C.output⟩
  have hC' : FanInTwo C' := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨(hC g' hg').1, le_trans ?_ (hC g' hg').2⟩
    exact List.length_take_le' _ _
  have hf' : circuitFun n C' = circuitFun n C := by
    funext x
    change (run (C.gates.map nm) (List.ofFn x)).getD C.output false = _
    rw [run_nm _ _ hops]
    rfl
  have hL : C'.gates.length = C.gates.length := by simp [C']
  have hgate : ∀ d, d < C.gates.length → n + d ≠ C.output →
      ∃ g ∈ C.gates, n + d ∈ rd g := by
    intro d hd hne
    by_contra hcon
    push Not at hcon
    obtain ⟨D, h1, h2, h3⟩ := del n C' hC' d (by omega) (fun j hj _ hm => by
      have hj' : j < C.gates.length := by omega
      refine hcon _ (List.getElem_mem hj') ?_
      simpa [C', nm] using hm) (fun h => hne h.symm)
    have hD : HasCircuitSize n (NestedCover.graphFun G A) D.size :=
      ⟨D, h1, le_rfl, fun x => by
        have := congrFun (h3.trans (hf'.trans hf)) x
        exact this⟩
    have e1 := hmin _ hD
    have e2 : C'.size = C.size := hL
    omega
  have hinp : ∀ a ∈ A, a.val ≠ C.output → ∃ g ∈ C.gates, a.val ∈ rd g := by
    intro a ha hne
    by_contra hcon
    push Not at hcon
    have e := indep a.val C'.gates (fun g hg => by
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      exact (hops g' hg').1) (fun g hg hm => by
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      refine hcon g' hg' ?_
      have hsub : ∀ w ∈ rds (nm g'), w ∈ rd g' := by
        intro w hw
        unfold rds at hw
        split at hw
        · exact List.mem_of_mem_take hw
        · exact hw
      exact hsub _ hm) (List.ofFn fun _ : Fin n => false)
      (List.ofFn fun k : Fin n => decide (k = a)) (by simp) (fun k hk => by
        by_cases h : k < n
        · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
            List.getElem_ofFn, List.getElem_ofFn]
          exact (decide_eq_false fun e => hk (by rw [← e])).symm
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      C.output (Ne.symm hne)
    have e0 : circuitFun n C' (fun _ => false) = circuitFun n C' fun k => decide (k = a) := e
    rw [hf', hf] at e0
    have f0 : NestedCover.graphFun G A (fun _ => false) = false := by
      simp [NestedCover.graphFun]
    have f1 : NestedCover.graphFun G A (fun k => decide (k = a)) = true := by
      simp only [NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨a, ha, rfl⟩
    rw [f0, f1] at e0
    exact Bool.false_ne_true e0
  let cnt : ℕ → ℕ := fun w => C.gates.countP fun g => (rd g).contains w
  have hpos : ∀ w, (∃ g ∈ C.gates, w ∈ rd g) → 1 ≤ cnt w := by
    rintro w ⟨g, hg, hw⟩
    exact List.countP_pos_iff.2 ⟨g, hg, by simpa using hw⟩
  let W1 : Finset ℕ := A.image Fin.val
  let W2 : Finset ℕ := (Finset.range C.gates.length).image fun d => n + d
  let W0 : Finset ℕ := Aᶜ.image Fin.val
  have c1 : W1.card = A.card := Finset.card_image_of_injective _ Fin.val_injective
  have c2 : W2.card = C.gates.length := by
    rw [Finset.card_image_of_injective _ fun a b h => by simpa using h, Finset.card_range]
  have hd1 : Disjoint W1 W2 := by
    refine Finset.disjoint_left.2 fun w h1 h2 => ?_
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨d, _, hd⟩ := Finset.mem_image.1 h2
    have := a.isLt
    omega
  have hd2 : Disjoint W0 (W1 ∪ W2) := by
    refine Finset.disjoint_left.2 fun w h1 h2 => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h1
    rcases Finset.mem_union.1 h2 with h2 | h2
    · obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 h2
      rw [Fin.val_injective hab] at hb
      exact (Finset.mem_compl.1 ha) hb
    · obtain ⟨d, _, hd⟩ := Finset.mem_image.1 h2
      have := a.isLt
      omega
  have hlow : (W1 ∪ W2).card ≤ ∑ w ∈ W1 ∪ W2, cnt w + 1 := by
    have h1 : (W1 ∪ W2).card ≤ ∑ w ∈ W1 ∪ W2, (cnt w + if w = C.output then 1 else 0) := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun w hw => ?_
      by_cases ho : w = C.output
      · simp [ho]
      · have := hpos w (by
          rcases Finset.mem_union.1 hw with h | h
          · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
            exact hinp a ha ho
          · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 h
            exact hgate d (Finset.mem_range.1 hd) ho)
        omega
    have h2 : ∑ w ∈ W1 ∪ W2, (if w = C.output then 1 else 0) ≤ 1 := by
      rw [← Finset.card_filter]
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
    rw [Finset.sum_add_distrib] at h1
    omega
  have hs := slots (W0 ∪ (W1 ∪ W2)) C.gates hops
  have hsum : ∑ w ∈ W0 ∪ (W1 ∪ W2), cnt w = ∑ v ∈ Aᶜ, cnt v.val + ∑ w ∈ W1 ∪ W2, cnt w := by
    rw [Finset.sum_union hd2, Finset.sum_image fun a _ b _ h => Fin.val_injective h]
  have hcard : (W1 ∪ W2).card = A.card + C.gates.length := by
    rw [Finset.card_union_of_disjoint hd1, c1, c2]
  have hs' : ∑ w ∈ W0 ∪ (W1 ∪ W2), cnt w + C.gates.countP (fun g => g.op.eval [false]) ≤
      2 * C.gates.length := hs
  simp only [← List.countP_eq_length_filter]
  change A.card + ∑ v ∈ Aᶜ, cnt v.val + C.gates.countP (fun g => g.op.eval [false]) ≤
    C.gates.length + 1
  omega
