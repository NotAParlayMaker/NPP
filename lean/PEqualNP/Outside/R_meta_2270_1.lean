import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2270_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      ¬ G.Colorable 2 →
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool, f x = true ↔
        (∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
      PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ u v : Fin n, G.Adj u v →
        let rs := C.gates.filter fun g =>
          let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
          ins.contains u.val || ins.contains v.val
        rs.length ≤ 6 ∧
          (rs.length = 6 → ∀ g ∈ rs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            g.inputs.length = 2 ∧ g.inputs.Nodup ∧
            ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val))) →
      ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ G.Adj u v ∧
        ∃ t : ℕ, t + 7 ≤ C.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize n
            (fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)) t) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      ¬ G.Colorable 2 →
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool, f x = true ↔
        (∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
      PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ u v : Fin n, G.Adj u v →
        let rs := C.gates.filter fun g =>
          let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
          ins.contains u.val || ins.contains v.val
        rs.length ≤ 6 ∧
          (rs.length = 6 → ∀ g ∈ rs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            g.inputs.length = 2 ∧ g.inputs.Nodup ∧
            ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val))) →
      ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ G.Adj u v ∧
        ∃ t : ℕ, t + 7 ≤ C.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize n
            (fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)) t) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  intro hMono hNot n G A f hnon hdeg hgirth hA hedge hf s hs
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have eval_not (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have hex : ∃ t : ℕ, HasCircuitSize n f t := ⟨s, hs⟩
  obtain ⟨C, hCfan, hCbound, hCeval⟩ := Nat.find_spec hex
  have hCs : C.size ≤ s := hCbound.trans (Nat.find_min' hex hs)
  have hCfun : circuitFun n C = f := funext hCeval
  have hCmin : IsMinimalCircuit n C := by
    refine ⟨hCfan, ?_⟩
    intro D hDfan hDfun
    have hDsz : HasCircuitSize n f D.size := ⟨D, hDfan, le_rfl, fun x => by
      have hx := congrFun hDfun x
      exact hx.trans (hCeval x)⟩
    exact hCbound.trans (Nat.find_min' hex hDsz)
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len_foldW : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons, List.length_nil]
      omega
  have getD_app_lt : ∀ (w t : List Bool) (i : ℕ), i < w.length →
      (w ++ t).getD i false = w.getD i false := by
    intro w t i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_self : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have foldW_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
      exact getD_app_lt w _ i hi
  have foldW_getD_ge : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      w.length + gs.length ≤ i → (gs.foldl stepW w).getD i false = false := by
    intro gs w i hi
    have hlen : (gs.foldl stepW w).length ≤ i := by rw [len_foldW]; exact hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none]
  have nonconst : ∀ u v : Fin n, G.Adj u v →
      ∃ x y : Fin n → Bool,
        f (Function.update (Function.update x u false) v false) ≠
        f (Function.update (Function.update y u false) v false) := by
    intro u v huv
    have huA : u ∉ A := hA u v huv
    have hnu : (G.neighborSet u).ncard = 3 := hdeg u huA
    have hsub_u : ¬ G.neighborSet u ⊆ ({v} : Set (Fin n)) := by
      intro hsub
      have hle := Set.ncard_le_ncard hsub
      rw [hnu, Set.ncard_singleton] at hle
      omega
    obtain ⟨w, hw_adj, hw_ne_v⟩ : ∃ w : Fin n, G.Adj u w ∧ w ≠ v := by
      by_contra hno
      apply hsub_u
      intro w hw
      by_contra hne
      exact hno ⟨w, hw, hne⟩
    have hwA : w ∉ A := hA w u hw_adj.symm
    have hnw : (G.neighborSet w).ncard = 3 := hdeg w hwA
    have hsub_w : ¬ G.neighborSet w ⊆ ({u, v} : Set (Fin n)) := by
      intro hsub
      have hle := Set.ncard_le_ncard hsub
      have hpair : ({u, v} : Set (Fin n)).ncard ≤ 2 := by
        rw [Set.insert_eq]
        calc ({u} ∪ {v} : Set (Fin n)).ncard
            ≤ ({u} : Set (Fin n)).ncard + ({v} : Set (Fin n)).ncard := Set.ncard_union_le _ _
          _ = 2 := by simp
      omega
    obtain ⟨z, hz_adj, hz_ne_u, hz_ne_v⟩ : ∃ z : Fin n, G.Adj w z ∧ z ≠ u ∧ z ≠ v := by
      by_contra hno
      apply hsub_w
      intro z hz
      by_contra hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
      exact hno ⟨z, hz, hmem.1, hmem.2⟩
    have hw_ne_u : w ≠ u := hw_adj.ne.symm
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    have h0 : f (Function.update (Function.update (fun _ => false) u false) v false) = false := by
      cases hval : f (Function.update (Function.update (fun _ => false) u false) v false)
      · rfl
      · rcases (hf _).1 hval with ⟨a, _, ha⟩ | ⟨i, _, _, hi, _⟩
        · simp [Function.update] at ha
        · simp [Function.update] at hi
    have h1 : f (Function.update (Function.update (fun _ => true) u false) v false) = true := by
      apply (hf _).2
      refine Or.inr ⟨w, z, hz_adj, ?_, ?_⟩
      · simp [Function.update_of_ne hw_ne_v, Function.update_of_ne hw_ne_u]
      · simp [Function.update_of_ne hz_ne_v, Function.update_of_ne hz_ne_u]
    rw [h0, h1]
    decide
  let active (g : Gate) : List ℕ :=
    g.inputs.take (bif g.op.eval [false] then 1 else 2)
  have gate_used : ∀ (j : ℕ), j < C.gates.length → C.output ≠ n + j →
      ∃ k : ℕ, j < k ∧ k < C.gates.length ∧
        ∃ gk : Gate, C.gates[k]? = some gk ∧ (n + j) ∈ active gk := by
    intro j hj hout
    by_contra hno
    push Not at hno
    let red (i : ℕ) : ℕ := if i = n + j then 0 else if n + j < i then i - 1 else i
    let C' : Circuit := {
      gates := C.gates.take j ++
        (C.gates.drop (j + 1)).map (fun g => ⟨g.op, g.inputs.map red⟩)
      output := red C.output }
    have hC'_fan : FanInTwo C' := by
      intro g hg
      change g ∈ C.gates.take j ++ (C.gates.drop (j + 1)).map (fun g => ⟨g.op, g.inputs.map red⟩) at hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with hpre | ⟨g0, hpost, rfl⟩
      · exact hCfan g (List.mem_of_mem_take hpre)
      · have h0 := hCfan g0 (List.mem_of_mem_drop hpost)
        exact ⟨h0.1, by simpa using h0.2⟩
    have hC'_size : C'.gates.length = C.gates.length - 1 := by
      change (C.gates.take j ++ (C.gates.drop (j + 1)).map (fun g : Gate => (⟨g.op, g.inputs.map red⟩ : Gate))).length = C.gates.length - 1
      simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
      omega
    have hC'_eval : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
      intro x
      let pre := C.gates.take j
      let post := C.gates.drop (j + 1)
      have hsplit : C.gates = pre ++ C.gates[j] :: post := by
        simp only [pre, post, List.cons_getElem_drop_succ, List.take_append_drop]
      let w0 := pre.foldl stepW (List.ofFn x)
      have hw0_len : w0.length = n + j := by
        rw [len_foldW, List.length_ofFn]
        simp only [pre, List.length_take]
        omega
      let w1 := stepW w0 C.gates[j]
      have hw1_len : w1.length = n + j + 1 := by
        simp only [w1, stepW, List.length_append, List.length_cons, List.length_nil, hw0_len]
      have hpost_agree : ∀ (m : ℕ) (ps : List Gate) (va vb : List Bool),
          va.length = n + j + 1 + m → vb.length = n + j + m →
          (∀ i : ℕ, i < n + j + 1 + m → i ≠ n + j →
            vb.getD (red i) false = va.getD i false) →
          (∀ g ∈ ps, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g.inputs.length ≤ 2 ∧ (n + j) ∉ active g) →
          ∀ i : ℕ, i < n + j + 1 + (m + ps.length) → i ≠ n + j →
            ((ps.map (fun g => ⟨g.op, g.inputs.map red⟩)).foldl stepW vb).getD (red i) false =
            (ps.foldl stepW va).getD i false := by
        intro m ps
        induction ps generalizing m with
        | nil =>
          intro va vb _ _ hag _ i hi hne
          simpa using hag i hi hne
        | cons g ps ih =>
          intro va vb hva hvb hag hps
          have hg := hps g (by simp)
          have hval_eq : g.op.eval ((g.inputs.map red).map fun a => vb.getD a false) =
              g.op.eval (g.inputs.map fun a => va.getD a false) := by
            have hin_eq : ∀ a ∈ active g, vb.getD (red a) false = va.getD a false := by
              intro a ha
              have hne : a ≠ n + j := fun h => hg.2.2 (h ▸ ha)
              by_cases hlt : a < n + j + 1 + m
              · exact hag a hlt hne
              · have hge_a : va.length ≤ a := by omega
                have hge_b : vb.length ≤ red a := by
                  simp only [red, hne, ↓reduceIte]
                  split_ifs <;> omega
                simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge_a,
                  List.getElem?_eq_none hge_b, Option.getD_none]
            have hmem_op := hg.1
            have hlen_in := hg.2.1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem_op
            rcases hmem_op with hop_eq | hop_eq | hop_eq
            · have hact : active g = g.inputs := by
                simp only [active, hop_eq, eval_and, List.all_cons, List.all_nil, id_eq,
                  Bool.and_true, Bool.cond_false, List.take_of_length_le hlen_in]
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro a ha
              exact hin_eq a (hact ▸ ha)
            · have hact : active g = g.inputs := by
                simp only [active, hop_eq, eval_or, List.any_cons, List.any_nil, id_eq,
                  Bool.or_false, Bool.cond_false, List.take_of_length_le hlen_in]
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro a ha
              exact hin_eq a (hact ▸ ha)
            · rcases hins : g.inputs with _ | ⟨a, rest⟩
              · rfl
              · have ha_mem : a ∈ active g := by
                  simp [active, hop_eq, eval_not, hins]
                have h_eq := hin_eq a ha_mem
                simp only [hop_eq, eval_not, List.map_cons, List.headD_cons]
                rw [h_eq]
          have hstep_ag : ∀ i : ℕ, i < n + j + 1 + (m + 1) → i ≠ n + j →
              (stepW vb ⟨g.op, g.inputs.map red⟩).getD (red i) false =
              (stepW va g).getD i false := by
            intro i hi hne
            by_cases hlt : i < n + j + 1 + m
            · have hlt_b : red i < vb.length := by
                simp only [red, hne, ↓reduceIte]
                split_ifs <;> omega
              rw [getD_app_lt vb _ _ hlt_b, getD_app_lt va _ _ (by omega)]
              exact hag i hlt hne
            · have heq : i = n + j + 1 + m := by omega
              subst heq
              have hred : red (n + j + 1 + m) = vb.length := by
                simp only [red]
                split_ifs <;> omega
              rw [hred]
              dsimp only [stepW]
              rw [getD_app_self vb _, ← hva, getD_app_self va _, hval_eq]
          have hstep := ih (m + 1) (stepW va g) (stepW vb ⟨g.op, g.inputs.map red⟩)
            (by simp [stepW, hva]; omega) (by simp [stepW, hvb]; omega) hstep_ag
            (fun g' hg' => hps g' (List.mem_cons_of_mem g hg'))
          intro i hi hne
          simp only [List.map_cons, List.foldl_cons]
          exact hstep i (by simp only [List.length_cons] at hi; omega) hne
      have hpost_props : ∀ g ∈ post,
          g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2 ∧ (n + j) ∉ active g := by
        intro g hg
        have h0 := hCfan g (List.mem_of_mem_drop hg)
        refine ⟨h0.1, h0.2, ?_⟩
        obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hg
        have hk_lt : j + 1 + idx < C.gates.length := by
          simp only [post, List.length_drop] at hidx_lt; omega
        have hk_get : C.gates[j + 1 + idx]? = some g := by
          rw [List.getElem?_eq_getElem hk_lt]
          congr 1
          simpa only [post, List.getElem_drop] using hidx_eq
        exact hno (j + 1 + idx) (by omega) hk_lt g hk_get
      have hinit_ag : ∀ i : ℕ, i < n + j + 1 + 0 → i ≠ n + j →
          w0.getD (red i) false = w1.getD i false := by
        intro i hi hne
        have hlt : i < n + j := by omega
        have hred : red i = i := by
          simp only [red, hne, ↓reduceIte]
          split_ifs <;> omega
        rw [hred, getD_app_lt w0 _ i (by omega)]
      have hfinal := hpost_agree 0 post w1 w0 (by omega) (by omega) hinit_ag hpost_props
      have hwC : C.wires (List.ofFn x) = post.foldl stepW w1 := by
        dsimp only [Circuit.wires]
        rw [hsplit, List.foldl_append, List.foldl_cons]
      have hwC' : C'.wires (List.ofFn x) =
          (post.map (fun g => ⟨g.op, g.inputs.map red⟩)).foldl stepW w0 := by
        dsimp only [Circuit.wires, C']
        rw [List.foldl_append]
      dsimp only [Circuit.eval]
      rw [hwC, hwC']
      change ((post.map (fun g => ⟨g.op, g.inputs.map red⟩)).foldl stepW w0).getD (red C.output) false = _
      by_cases hlt : C.output < n + C.gates.length
      · have hlen_post : C.gates.length = j + 1 + post.length := by
          simp only [post, List.length_drop]; omega
        exact hfinal C.output (by omega) hout
      · have hge1 : (post.foldl stepW w1).length ≤ C.output := by
          rw [len_foldW, hw1_len]; simp only [post, List.length_drop]; omega
        have hge2 : ((post.map (fun g => ⟨g.op, g.inputs.map red⟩)).foldl
            stepW w0).length ≤ red C.output := by
          rw [len_foldW, hw0_len, List.length_map]
          simp only [red, hout, ↓reduceIte, post, List.length_drop]
          split_ifs <;> omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
          List.getElem?_eq_none hge2, Option.getD_none]
    have hmin_le : C.gates.length ≤ C'.gates.length := hCmin.2 C' hC'_fan (funext hC'_eval)
    omega
  have elim_edge : ∀ u v : Fin n, G.Adj u v →
      (7 ≤ (C.gates.filter fun g =>
        let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
        ins.contains u.val || ins.contains v.val).length ∨
        ((C.gates.filter fun g =>
          let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
          ins.contains u.val || ins.contains v.val).length = 6 ∧
          ∃ g ∈ (C.gates.filter fun g =>
            let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
            ins.contains u.val || ins.contains v.val),
            ¬ (g.op = GateOp.or ∧ g.inputs.length = 2 ∧
              g.inputs.Nodup ∧ ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val)))) →
      ∃ t : ℕ, t + 7 ≤ C.size ∧
        HasCircuitSize n (fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)) t := by
    intro u v huv hcond
    let evalSym (w' : List Bool) (sv : Bool ⊕ ℕ) : Bool :=
      Sum.elim id (fun i => w'.getD i false) sv
    let stepRes (syms : List (Bool ⊕ ℕ)) (gs : List Gate) (g : Gate) : (Bool ⊕ ℕ) × Option Gate :=
      let getS (i : ℕ) : Bool ⊕ ℕ := syms.getD i (Sum.inl false)
      GateOp.casesOn g.op
        (List.casesOn g.inputs (Sum.inl true, none) fun a rest =>
          List.casesOn rest (getS a, none) fun b _ =>
            Sum.elim
              (fun ba => bif ba then (getS b, none) else (Sum.inl false, none))
              (fun wa => Sum.elim
                (fun bb => bif bb then (Sum.inr wa, none) else (Sum.inl false, none))
                (fun wb => (Sum.inr (n + gs.length), some ⟨GateOp.and, [wa, wb]⟩))
                (getS b))
              (getS a))
        (List.casesOn g.inputs (Sum.inl false, none) fun a rest =>
          List.casesOn rest (getS a, none) fun b _ =>
            Sum.elim
              (fun ba => bif ba then (Sum.inl true, none) else (getS b, none))
              (fun wa => Sum.elim
                (fun bb => bif bb then (Sum.inl true, none) else (Sum.inr wa, none))
                (fun wb => (Sum.inr (n + gs.length), some ⟨GateOp.or, [wa, wb]⟩))
                (getS b))
              (getS a))
        (List.casesOn g.inputs (Sum.inl true, none) fun a _ =>
          Sum.elim
            (fun ba => (Sum.inl (!ba), none))
            (fun wa => (Sum.inr (n + gs.length), some ⟨GateOp.not, [wa]⟩))
            (getS a))
        (fun _ => (Sum.inl false, none))
        (Sum.inl false, none)
    let stepSym (st : List (Bool ⊕ ℕ) × List Gate × List Bool) (g : Gate) :
        List (Bool ⊕ ℕ) × List Gate × List Bool :=
      let r := stepRes st.1 st.2.1 g
      Option.elim r.2 (st.1 ++ [r.1], st.2.1, st.2.2 ++ [false])
        (fun ng => (st.1 ++ [r.1], st.2.1 ++ [ng], st.2.2 ++ [true]))
    let syms0 : List (Bool ⊕ ℕ) :=
      (List.range n).map fun i => if i = u.val ∨ i = v.val then Sum.inl false else Sum.inr i
    let stFinal := C.gates.foldl stepSym (syms0, [], [])
    let symsF := stFinal.1
    let gsF := stFinal.2.1
    let emitF := stFinal.2.2
    have hfold_inv : ∀ (pre : List Gate),
        (∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        let st := pre.foldl stepSym (syms0, [], [])
        st.1.length = n + pre.length ∧
        st.2.2.length = pre.length ∧
        st.2.1.length = st.2.2.count true ∧
        FanInTwo ⟨st.2.1, 0⟩ ∧
        (∀ i w, st.1.getD i (Sum.inl false) = Sum.inr w → w < n + st.2.1.length) ∧
        (∀ x : Fin n → Bool, ∀ i : ℕ,
          (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).getD i false =
          evalSym (st.2.1.foldl stepW (List.ofFn x)) (st.1.getD i (Sum.inl false))) := by
      intro pre
      induction pre using List.reverseRecOn with
      | nil =>
        intro _
        refine ⟨by simp [syms0], rfl, rfl, fun _ h => by simp at h, ?_, ?_⟩
        · intro i w hi
          simp only [List.foldl_nil] at hi ⊢
          by_cases hlt : i < n
          · simp only [syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range hlt, Option.map_some, Option.getD_some] at hi
            by_cases huv_i : i = u.val ∨ i = v.val
            · simp only [huv_i, ↓reduceIte] at hi; cases hi
            · simp only [huv_i, ↓reduceIte] at hi; cases hi; simpa using hlt
          · have hge : syms0.length ≤ i := by simp [syms0]; omega
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hi
            cases hi
        · intro x i
          by_cases hlt : i < n
          · simp only [List.foldl_nil, syms0, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
              List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some,
              hlt, ↓reduceDIte]
            split_ifs with h
            · rcases h with h1 | h2
              · have hu : (⟨i, hlt⟩ : Fin n) = u := Fin.ext h1
                subst hu
                by_cases huv_eq : (⟨i, hlt⟩ : Fin n) = v
                · subst huv_eq; simp [evalSym]
                · simp [evalSym, Function.update_of_ne huv_eq]
              · have hv : (⟨i, hlt⟩ : Fin n) = v := Fin.ext h2
                subst hv; simp [evalSym]
            · push Not at h
              have hu : (⟨i, hlt⟩ : Fin n) ≠ u := fun heq => h.1 (congrArg Fin.val heq)
              have hv : (⟨i, hlt⟩ : Fin n) ≠ v := fun heq => h.2 (congrArg Fin.val heq)
              simp [evalSym, Function.update_of_ne hv, Function.update_of_ne hu,
                List.getD_eq_getElem?_getD, hlt]
          · have hge1 : (List.ofFn (Function.update (Function.update x u false) v false)).length ≤ i := by
              simp; omega
            have hge2 : syms0.length ≤ i := by simp [syms0]; omega
            simp only [List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
              List.getElem?_eq_none hge2, Option.getD_none, evalSym]
            rfl
      | append_singleton pre g ih =>
        intro hfan
        have hpre_fan : ∀ g' ∈ pre, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
        have hg_fan := hfan g (by simp)
        obtain ⟨hlen1, hlen2, hcnt, hfan_gs, hbound, hsem⟩ := ih hpre_fan
        set st := pre.foldl stepSym (syms0, [], []) with hst_def
        have hfold_eq : (pre ++ [g]).foldl stepSym (syms0, [], []) = stepSym st g := by
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [hfold_eq]
        set r := stepRes st.1 st.2.1 g with hr_def
        have hstep_sem : ∀ x : Fin n → Bool,
            g.op.eval (g.inputs.map fun a =>
              (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).getD a false) =
            evalSym ((Option.elim r.2 st.2.1 (fun ng => st.2.1 ++ [ng])).foldl stepW (List.ofFn x)) r.1 ∧
            (∀ ng, r.2 = some ng →
              ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ng.inputs.length ≤ 2) ∧
            (∀ w, r.1 = Sum.inr w → w < n + (Option.elim r.2 st.2.1 (fun ng => st.2.1 ++ [ng])).length) := by
          intro x
          set wNew := st.2.1.foldl stepW (List.ofFn x)
          have hwNew_len : wNew.length = n + st.2.1.length := by
            rw [len_foldW, List.length_ofFn]
          have hget : ∀ a : ℕ,
              (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).getD a false =
              evalSym wNew (st.1.getD a (Sum.inl false)) := hsem x
          have hop := hg_fan.1
          have hlen_in := hg_fan.2
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop_eq | hop_eq | hop_eq
          · rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · simp [hr_def, stepRes, hop_eq, hins, eval_and, evalSym]
            · simp only [hr_def, stepRes, hop_eq, hins, eval_and, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true, hget a]
              exact ⟨rfl, fun _ h => (by cases h), fun w hw => hbound a w hw⟩
            · simp only [hr_def, stepRes, hop_eq, hins, eval_and, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true, hget a, hget b]
              cases hsa : st.1.getD a (Sum.inl false) with
              | inl ba =>
                cases ba with
                | false => simp [evalSym]
                | true =>
                  cases hsb : st.1.getD b (Sum.inl false) with
                  | inl bb => cases bb <;> simp [evalSym]
                  | inr wb =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound b wb hsb
              | inr wa =>
                cases hsb : st.1.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb with
                  | false => simp [evalSym]
                  | true =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound a wa hsa
                | inr wb =>
                  refine ⟨?_, ?_, ?_⟩
                  · change (evalSym wNew (Sum.inr wa) && evalSym wNew (Sum.inr wb)) =
                      ((st.2.1 ++ [Gate.mk GateOp.and [wa, wb]]).foldl stepW (List.ofFn x)).getD (n + st.2.1.length) false
                    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                    change (evalSym wNew (Sum.inr wa) && evalSym wNew (Sum.inr wb)) =
                      (stepW wNew (Gate.mk GateOp.and [wa, wb])).getD (n + st.2.1.length) false
                    rw [← hwNew_len]
                    dsimp only [stepW]
                    rw [getD_app_self wNew _]
                    simp only [eval_and, List.map_cons, List.map_nil, List.all_cons,
                      List.all_nil, id_eq, Bool.and_true, evalSym]
                    rfl
                  · intro ng hng; cases hng; simp
                  · intro w hw; cases hw; simp
            · rw [hins] at hlen_in; simp at hlen_in
          · rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · simp [hr_def, stepRes, hop_eq, hins, eval_or, evalSym]
            · simp only [hr_def, stepRes, hop_eq, hins, eval_or, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false, hget a]
              exact ⟨rfl, fun _ h => (by cases h), fun w hw => hbound a w hw⟩
            · simp only [hr_def, stepRes, hop_eq, hins, eval_or, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false, hget a, hget b]
              cases hsa : st.1.getD a (Sum.inl false) with
              | inl ba =>
                cases ba with
                | true => simp [evalSym]
                | false =>
                  cases hsb : st.1.getD b (Sum.inl false) with
                  | inl bb => cases bb <;> simp [evalSym]
                  | inr wb =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound b wb hsb
              | inr wa =>
                cases hsb : st.1.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb with
                  | true => simp [evalSym]
                  | false =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound a wa hsa
                | inr wb =>
                  refine ⟨?_, ?_, ?_⟩
                  · change (evalSym wNew (Sum.inr wa) || evalSym wNew (Sum.inr wb)) =
                      ((st.2.1 ++ [Gate.mk GateOp.or [wa, wb]]).foldl stepW (List.ofFn x)).getD (n + st.2.1.length) false
                    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                    change (evalSym wNew (Sum.inr wa) || evalSym wNew (Sum.inr wb)) =
                      (stepW wNew (Gate.mk GateOp.or [wa, wb])).getD (n + st.2.1.length) false
                    rw [← hwNew_len]
                    dsimp only [stepW]
                    rw [getD_app_self wNew _]
                    simp only [eval_or, List.map_cons, List.map_nil, List.any_cons,
                      List.any_nil, id_eq, Bool.or_false, evalSym]
                    rfl
                  · intro ng hng; cases hng; simp
                  · intro w hw; cases hw; simp
            · rw [hins] at hlen_in; simp at hlen_in
          · rcases hins : g.inputs with _ | ⟨a, rest⟩
            · simp [hr_def, stepRes, hop_eq, hins, eval_not, evalSym]
            · simp only [hr_def, stepRes, hop_eq, hins, eval_not, List.map_cons, List.headD_cons,
                hget a]
              cases hsa : st.1.getD a (Sum.inl false) with
              | inl ba => simp [evalSym]
              | inr wa =>
                refine ⟨?_, ?_, ?_⟩
                · change (!(evalSym wNew (Sum.inr wa))) =
                    ((st.2.1 ++ [Gate.mk GateOp.not [wa]]).foldl stepW (List.ofFn x)).getD (n + st.2.1.length) false
                  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                  change (!(evalSym wNew (Sum.inr wa))) =
                    (stepW wNew (Gate.mk GateOp.not [wa])).getD (n + st.2.1.length) false
                  rw [← hwNew_len]
                  dsimp only [stepW]
                  rw [getD_app_self wNew _]
                  simp only [eval_not, List.map_cons, List.map_nil, List.headD_cons, evalSym]
                  rfl
                · intro ng hng; cases hng; simp
                · intro w hw; cases hw; simp
        cases hr2 : r.2 with
        | none =>
          have hst_eq : stepSym st g = (st.1 ++ [r.1], st.2.1, st.2.2 ++ [false]) := by
            simp [stepSym, ← hr_def, hr2]
          rw [hst_eq]
          dsimp only
          refine ⟨by simp [hlen1]; omega, by simp [hlen2], by simp [hcnt, List.count_append],
            hfan_gs, ?_, ?_⟩
          · intro i w hi
            by_cases hlt : i < st.1.length
            · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
                ← List.getD_eq_getElem?_getD] at hi
              exact hbound i w hi
            · by_cases heq : i = st.1.length
              · subst heq
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)] at hi
                simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
                have := (hstep_sem (fun _ => false)).2.2 w hi
                simpa [hr2] using this
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
                  Option.getD_none] at hi
                cases hi
          · intro x i
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            by_cases hlt : i < n + pre.length
            · have hlt1 : i < st.1.length := by omega
              have hltW : i < (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).length := by
                rw [len_foldW, List.length_ofFn]; exact hlt
              rw [getD_app_lt _ _ i hltW]
              have hget1 : (st.1 ++ [r.1]).getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1]
              rw [hget1]
              exact hsem x i
            · by_cases heq : i = n + pre.length
              · subst heq
                have hlenW : (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).length = n + pre.length := by
                  rw [len_foldW, List.length_ofFn]
                have h1 : (stepW (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))) g).getD (n + pre.length) false =
                    g.op.eval (g.inputs.map fun a => (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).getD a false) := by
                  rw [← hlenW]; exact getD_app_self _ _
                rw [h1]
                have hget1 : (st.1 ++ [r.1]).getD (n + pre.length) (Sum.inl false) = r.1 := by
                  rw [List.getD_eq_getElem?_getD, ← hlen1, List.getElem?_append_right (le_refl _)]
                  simp
                rw [hget1]
                simpa [hr2] using (hstep_sem x).1
              · have hgeW : (stepW (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))) g).length ≤ i := by
                  simp only [stepW, List.length_append, List.length_cons, List.length_nil,
                    len_foldW, List.length_ofFn]
                  omega
                have hgeS : (st.1 ++ [r.1]).length ≤ i := by simp [hlen1]; omega
                simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgeW,
                  List.getElem?_eq_none hgeS, Option.getD_none, evalSym]
                rfl
        | some ng =>
          have hst_eq : stepSym st g = (st.1 ++ [r.1], st.2.1 ++ [ng], st.2.2 ++ [true]) := by
            simp [stepSym, ← hr_def, hr2]
          rw [hst_eq]
          dsimp only
          refine ⟨by simp [hlen1]; omega, by simp [hlen2],
            by simp [hcnt, List.count_append], ?_, ?_, ?_⟩
          · intro g' hg'
            simp only [List.mem_append, List.mem_singleton] at hg'
            rcases hg' with hg' | hg_eq
            · exact hfan_gs g' hg'
            · rw [hg_eq]; exact (hstep_sem (fun _ => false)).2.1 ng hr2
          · intro i w hi
            by_cases hlt : i < st.1.length
            · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
                ← List.getD_eq_getElem?_getD] at hi
              have := hbound i w hi
              simp; omega
            · by_cases heq : i = st.1.length
              · subst heq
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)] at hi
                simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
                have := (hstep_sem (fun _ => false)).2.2 w hi
                simpa [hr2] using this
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
                  Option.getD_none] at hi
                cases hi
          · intro x i
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            by_cases hlt : i < n + pre.length
            · have hlt1 : i < st.1.length := by omega
              have hltW : i < (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).length := by
                rw [len_foldW, List.length_ofFn]; exact hlt
              rw [getD_app_lt _ _ i hltW]
              have hget1 : (st.1 ++ [r.1]).getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1]
              rw [hget1, hsem x i]
              cases hsv : st.1.getD i (Sum.inl false) with
              | inl b => rfl
              | inr w =>
                have hw_lt : w < (st.2.1.foldl stepW (List.ofFn x)).length := by
                  rw [len_foldW, List.length_ofFn]
                  exact hbound i w hsv
                simp only [evalSym, List.foldl_append, List.foldl_cons, List.foldl_nil]
                exact (getD_app_lt _ _ w hw_lt).symm
            · by_cases heq : i = n + pre.length
              · subst heq
                have hlenW : (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).length = n + pre.length := by
                  rw [len_foldW, List.length_ofFn]
                have h1 : (stepW (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))) g).getD (n + pre.length) false =
                    g.op.eval (g.inputs.map fun a => (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))).getD a false) := by
                  rw [← hlenW]; exact getD_app_self _ _
                rw [h1]
                have hget1 : (st.1 ++ [r.1]).getD (n + pre.length) (Sum.inl false) = r.1 := by
                  rw [List.getD_eq_getElem?_getD, ← hlen1, List.getElem?_append_right (le_refl _)]
                  simp
                rw [hget1]
                simpa [hr2] using (hstep_sem x).1
              · have hgeW : (stepW (pre.foldl stepW (List.ofFn (Function.update (Function.update x u false) v false))) g).length ≤ i := by
                  simp only [stepW, List.length_append, List.length_cons, List.length_nil,
                    len_foldW, List.length_ofFn]
                  omega
                have hgeS : (st.1 ++ [r.1]).length ≤ i := by simp [hlen1]; omega
                simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgeW,
                  List.getElem?_eq_none hgeS, Option.getD_none, evalSym]
                rfl
    have hprefix_agree : ∀ (pre post : List Gate) (i : ℕ), i < n + pre.length →
        ((pre ++ post).foldl stepSym (syms0, [], [])).1.getD i (Sum.inl false) =
        (pre.foldl stepSym (syms0, [], [])).1.getD i (Sum.inl false) := by
      intro pre post
      have aux : ∀ (qs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate × List Bool) (i : ℕ),
          i < st.1.length → (qs.foldl stepSym st).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
        intro qs
        induction qs with
        | nil => intro st i _; rfl
        | cons q qs ih =>
          intro st i hi
          rw [List.foldl_cons]
          have hlen_st : (stepSym st q).1.length = st.1.length + 1 := by
            dsimp only [stepSym]
            cases (stepRes st.1 st.2.1 q).2 <;> simp
          rw [ih (stepSym st q) i (by omega)]
          dsimp only [stepSym]
          cases (stepRes st.1 st.2.1 q).2 <;>
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      intro i hi
      rw [List.foldl_append]
      have hlen_pre : (pre.foldl stepSym (syms0, [], [])).1.length = n + pre.length := by
        have auxlen : ∀ (ps : List Gate) (st : List (Bool ⊕ ℕ) × List Gate × List Bool),
            (ps.foldl stepSym st).1.length = st.1.length + ps.length := by
          intro ps
          induction ps with
          | nil => intro st; simp
          | cons p ps ih =>
            intro st
            rw [List.foldl_cons, ih]
            dsimp only [stepSym]
            cases (stepRes st.1 st.2.1 p).2 <;> simp <;> omega
        rw [auxlen]; simp [syms0]
      exact aux post _ i (by omega)
    have hstep_at : ∀ (j : ℕ) (hj : j < C.gates.length),
        let stPre := (C.gates.take j).foldl stepSym (syms0, [], [])
        let r := stepRes stPre.1 stPre.2.1 C.gates[j]
        symsF.getD (n + j) (Sum.inl false) = r.1 ∧
        emitF.getD j false = r.2.isSome := by
      intro j hj
      let pre := C.gates.take j
      let post := C.gates.drop (j + 1)
      have hsplit : C.gates = pre ++ C.gates[j] :: post := by
        simp only [pre, post, List.cons_getElem_drop_succ, List.take_append_drop]
      have hpre_len : pre.length = j := by simp only [pre, List.length_take]; omega
      let stPre := pre.foldl stepSym (syms0, [], [])
      let stMid := stepSym stPre C.gates[j]
      have hstPre_len : stPre.1.length = n + j ∧ stPre.2.2.length = j := by
        have h1 := hfold_inv pre (fun g hg => hCfan g (List.mem_of_mem_take hg))
        exact ⟨by rw [h1.1, hpre_len], by rw [h1.2.1, hpre_len]⟩
      have hfinal_eq : stFinal = post.foldl stepSym stMid := by
        dsimp only [stFinal]
        rw [hsplit, List.foldl_append, List.foldl_cons]
      have hpres : ∀ (qs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate × List Bool) (a b : ℕ),
          a < st.1.length → b < st.2.2.length →
          (qs.foldl stepSym st).1.getD a (Sum.inl false) = st.1.getD a (Sum.inl false) ∧
          (qs.foldl stepSym st).2.2.getD b false = st.2.2.getD b false := by
        intro qs
        induction qs with
        | nil => intro st a b _ _; exact ⟨rfl, rfl⟩
        | cons q qs ih =>
          intro st a b ha hb
          rw [List.foldl_cons]
          have h1 : a < (stepSym st q).1.length := by
            dsimp only [stepSym]; cases (stepRes st.1 st.2.1 q).2 <;> simp <;> omega
          have h2 : b < (stepSym st q).2.2.length := by
            dsimp only [stepSym]; cases (stepRes st.1 st.2.1 q).2 <;> simp <;> omega
          obtain ⟨p1, p2⟩ := ih (stepSym st q) a b h1 h2
          rw [p1, p2]
          dsimp only [stepSym]
          cases (stepRes st.1 st.2.1 q).2 <;>
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ha, List.getElem?_append_left hb]
      have hmid_len : n + j < stMid.1.length ∧ j < stMid.2.2.length := by
        dsimp only [stMid, stepSym]
        cases (stepRes stPre.1 stPre.2.1 C.gates[j]).2 <;> simp [hstPre_len.1, hstPre_len.2]
      obtain ⟨h1, h2⟩ := hpres post stMid (n + j) j hmid_len.1 hmid_len.2
      dsimp only [symsF, emitF]
      rw [hfinal_eq, h1, h2]
      dsimp only [stMid, stepSym]
      cases hr : (stepRes stPre.1 stPre.2.1 C.gates[j]).2 with
      | none =>
        simp only [Option.isSome_none, Option.elim_none]
        constructor
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), hstPre_len.1, Nat.sub_self]
          rfl
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), hstPre_len.2, Nat.sub_self]
          rfl
      | some ng =>
        simp only [Option.isSome_some, Option.elim_some]
        constructor
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), hstPre_len.1, Nat.sub_self]
          rfl
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), hstPre_len.2, Nat.sub_self]
          rfl
    obtain ⟨hlen1F, hlen2F, hcntF, hfanF, _, hsemF⟩ := hfold_inv C.gates hCfan
    have hsymsF_u : symsF.getD u.val (Sum.inl false) = Sum.inl false := by
      have h1 := hprefix_agree [] C.gates u.val (by simp [u.isLt])
      simpa [symsF, stFinal, syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range u.isLt] using h1
    have hsymsF_v : symsF.getD v.val (Sum.inl false) = Sum.inl false := by
      have h1 := hprefix_agree [] C.gates v.val (by simp [v.isLt])
      simpa [symsF, stFinal, syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range v.isLt] using h1
    have hout_inr : ∃ out' : ℕ, symsF.getD C.output (Sum.inl false) = Sum.inr out' := by
      cases ho : symsF.getD C.output (Sum.inl false) with
      | inr out' => exact ⟨out', rfl⟩
      | inl b =>
        obtain ⟨x, y, hxy⟩ := nonconst u v huv
        have hx := hsemF x C.output
        have hy := hsemF y C.output
        rw [ho] at hx hy
        have hfx : f (Function.update (Function.update x u false) v false) = b := by
          rw [← hCeval]; exact hx
        have hfy : f (Function.update (Function.update y u false) v false) = b := by
          rw [← hCeval]; exact hy
        exact False.elim (hxy (hfx.trans hfy.symm))
    obtain ⟨out', hout'⟩ := hout_inr
    let Cnew : Circuit := ⟨gsF, out'⟩
    have hCnew_fan : FanInTwo Cnew := hfanF
    have hCnew_eval : ∀ x : Fin n → Bool,
        Cnew.eval (List.ofFn x) = f (Function.update (Function.update x u false) v false) := by
      intro x
      rw [← hCeval]
      have hx := hsemF x C.output
      rw [hout'] at hx
      exact hx.symm
    let readsUV (g : Gate) : Bool :=
      let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
      ins.contains u.val || ins.contains v.val
    let dropped : Finset (Fin C.gates.length) :=
      Finset.univ.filter fun j => emitF.getD j.val false = false
    let readers : Finset (Fin C.gates.length) :=
      Finset.univ.filter fun j => readsUV C.gates[j.val] = true
    have hdrop_size : Cnew.size + dropped.card = C.size := by
      have hsum : emitF.count true + emitF.count false = emitF.length := by
        have aux : ∀ l : List Bool, l.count true + l.count false = l.length := by
          intro l
          induction l with
          | nil => simp
          | cons b l ih => cases b <;> simp <;> omega
        exact aux emitF
      have hcard_drop : dropped.card = emitF.count false := by
        have aux : ∀ (l : List Bool),
            (Finset.univ.filter fun j : Fin l.length => l.getD j.val false = false).card =
            l.count false := by
          intro l
          induction l with
          | nil => simp
          | cons b l ih =>
            rw [List.count_cons]
            have hbi : (Finset.univ.filter fun j : Fin (b :: l).length =>
                (b :: l).getD j.val false = false).card =
                (if b = false then 1 else 0) +
                (Finset.univ.filter fun j : Fin l.length => l.getD j.val false = false).card := by
              rw [Finset.card_filter, Finset.card_filter]
              change ∑ j : Fin (l.length + 1), (if (b :: l).getD j.val false = false then 1 else 0) = _
              rw [Fin.sum_univ_succ]
              simp only [Fin.val_zero, Fin.val_succ, List.getD_eq_getElem?_getD,
                List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ]
            rw [hbi, ih]
            cases b <;> simp; omega
        have hlen_eq : emitF.length = C.gates.length := hlen2F
        rw [← aux emitF]
        refine Finset.card_bij (fun j _ => (⟨j.val, by omega⟩ : Fin emitF.length)) ?_ ?_ ?_
        · intro j hj
          simp only [dropped, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact hj
        · intro j1 _ j2 _ h
          exact Fin.ext (congrArg (Fin.val : Fin emitF.length → ℕ) h)
        · intro j hj
          refine ⟨⟨j.val, by omega⟩, ?_, Fin.ext rfl⟩
          simp only [dropped, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact hj
      change gsF.length + dropped.card = C.gates.length
      rw [hcntF, hcard_drop, hsum, hlen2F]
    have hreaders_card : readers.card = (C.gates.filter readsUV).length := by
      have aux : ∀ (l : List Gate),
          (Finset.univ.filter fun j : Fin l.length => readsUV l[j.val] = true).card =
          (l.filter readsUV).length := by
        intro l
        induction l with
        | nil => simp
        | cons g l ih =>
          rw [List.filter_cons]
          have hbi : (Finset.univ.filter fun j : Fin (g :: l).length =>
              readsUV (g :: l)[j.val] = true).card =
              (if readsUV g = true then 1 else 0) +
              (Finset.univ.filter fun j : Fin l.length => readsUV l[j.val] = true).card := by
            rw [Finset.card_filter, Finset.card_filter]
            change ∑ j : Fin (l.length + 1), (if readsUV (g :: l)[j.val] = true then 1 else 0) = _
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]
            rfl
          rw [hbi, ih]
          cases readsUV g <;> simp; omega
      exact aux C.gates
    have hreaders_sub : readers ⊆ dropped := by
      intro j hj
      simp only [readers, dropped, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      obtain ⟨_, hemit⟩ := hstep_at j.val j.isLt
      rw [hemit]
      have hpre_u : ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD u.val (Sum.inl false) = Sum.inl false := by
        have h1 := hprefix_agree [] (C.gates.take j.val) u.val (by simp [u.isLt])
        simpa [syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range u.isLt] using h1
      have hpre_v : ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD v.val (Sum.inl false) = Sum.inl false := by
        have h1 := hprefix_agree [] (C.gates.take j.val) v.val (by simp [v.isLt])
        simpa [syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range v.isLt] using h1
      set g := C.gates[j.val]
      have hg_fan := hCfan g (List.getElem_mem j.isLt)
      have hop := hg_fan.1
      have hlen_in := hg_fan.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop_eq | hop_eq | hop_eq
      · rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
        · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
        · simp only [readsUV, hop_eq, hins, eval_and, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, Bool.cond_false, List.take_succ_cons, List.take_zero, List.contains_cons,
            List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hj
          have hab : ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) = Sum.inl false ∨
              ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) = Sum.inl false := by
            rcases hj with (rfl | rfl) | (rfl | rfl)
            · exact Or.inl hpre_u
            · exact Or.inr hpre_u
            · exact Or.inl hpre_v
            · exact Or.inr hpre_v
          rcases hab with ha | hb
          · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [ha]; rfl
          · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hb]
            cases ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) with
            | inl ba => cases ba <;> rfl
            | inr wa => rfl
        · rw [hins] at hlen_in; simp at hlen_in
      · rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
        · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
        · simp only [readsUV, hop_eq, hins, eval_or, List.any_cons, List.any_nil, id_eq,
            Bool.or_false, Bool.cond_false, List.take_succ_cons, List.take_zero, List.contains_cons,
            List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hj
          have hab : ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) = Sum.inl false ∨
              ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) = Sum.inl false := by
            rcases hj with (rfl | rfl) | (rfl | rfl)
            · exact Or.inl hpre_u
            · exact Or.inr hpre_u
            · exact Or.inl hpre_v
            · exact Or.inr hpre_v
          rcases hab with ha | hb
          · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [ha]
            cases ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) with
            | inl bb => cases bb <;> rfl
            | inr wb => rfl
          · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hb]
            cases ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) with
            | inl ba => cases ba <;> rfl
            | inr wa => rfl
        · rw [hins] at hlen_in; simp at hlen_in
      · rcases hins : g.inputs with _ | ⟨a, rest⟩
        · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
        · simp only [readsUV, hop_eq, hins, eval_not, List.headD_cons, Bool.not_false,
            Bool.cond_true, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil,
            Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hj
          have ha : ((C.gates.take j.val).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) = Sum.inl false := by
            rcases hj with rfl | rfl
            · exact hpre_u
            · exact hpre_v
          dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [ha]; rfl
    rcases hcond with hge7 | ⟨heq6, gbad, hgbad_mem, hgbad_prop⟩
    · refine ⟨Cnew.size, ?_, ⟨Cnew, hCnew_fan, le_rfl, hCnew_eval⟩⟩
      have hle := Finset.card_le_card hreaders_sub
      rw [hreaders_card] at hle
      dsimp only [readsUV] at hle
      dsimp only at hge7
      omega
    · have hK_nonempty : ∃ j : Fin C.gates.length, (symsF.getD (n + j.val) (Sum.inl false)).isLeft := by
        rw [List.mem_filter] at hgbad_mem
        obtain ⟨j0, hj0_lt, hj0_eq⟩ := List.getElem_of_mem hgbad_mem.1
        refine ⟨⟨j0, hj0_lt⟩, ?_⟩
        obtain ⟨hsym0, _⟩ := hstep_at j0 hj0_lt
        rw [hsym0, hj0_eq]
        have hpre_u : ((C.gates.take j0).foldl stepSym (syms0, [], [])).1.getD u.val (Sum.inl false) = Sum.inl false := by
          have h1 := hprefix_agree [] (C.gates.take j0) u.val (by simp [u.isLt])
          simpa [syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range u.isLt] using h1
        have hpre_v : ((C.gates.take j0).foldl stepSym (syms0, [], [])).1.getD v.val (Sum.inl false) = Sum.inl false := by
          have h1 := hprefix_agree [] (C.gates.take j0) v.val (by simp [v.isLt])
          simpa [syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range v.isLt] using h1
        have hg_fan := hCfan gbad hgbad_mem.1
        have hop := hg_fan.1
        have hlen_in := hg_fan.2
        have hread := hgbad_mem.2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop_eq | hop_eq | hop_eq
        · rcases hins : gbad.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · simp only [hop_eq, hins, eval_and, List.all_cons, List.all_nil, id_eq,
              Bool.and_true, Bool.cond_false, List.take_succ_cons, List.take_nil, List.contains_cons,
              List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hread
            rcases hread with rfl | rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hpre_u]; rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hpre_v]; rfl
          · simp only [hop_eq, hins, eval_and, List.all_cons, List.all_nil, id_eq,
              Bool.and_true, Bool.cond_false, List.take_succ_cons, List.take_zero, List.contains_cons,
              List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hread
            have hab : ((C.gates.take j0).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) = Sum.inl false ∨
                ((C.gates.take j0).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) = Sum.inl false := by
              rcases hread with (rfl | rfl) | (rfl | rfl)
              · exact Or.inl hpre_u
              · exact Or.inr hpre_u
              · exact Or.inl hpre_v
              · exact Or.inr hpre_v
            rcases hab with ha | hb
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [ha]; rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hb]
              cases ((C.gates.take j0).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) with
              | inl ba => cases ba <;> rfl
              | inr wa => rfl
          · rw [hins] at hlen_in; simp at hlen_in
        · rcases hins : gbad.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · simp only [hop_eq, hins, eval_or, List.any_cons, List.any_nil, id_eq,
              Bool.or_false, Bool.cond_false, List.take_succ_cons, List.take_nil, List.contains_cons,
              List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hread
            rcases hread with rfl | rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hpre_u]; rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hpre_v]; rfl
          · simp only [hop_eq, hins, eval_or, List.any_cons, List.any_nil, id_eq,
              Bool.or_false, Bool.cond_false, List.take_succ_cons, List.take_zero, List.contains_cons,
              List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hread
            have hab : ((C.gates.take j0).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) = Sum.inl false ∧
                ((C.gates.take j0).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) = Sum.inl false := by
              by_cases hne_ab : a = b
              · subst hne_ab
                rcases hread with (rfl | rfl) | (rfl | rfl)
                · exact ⟨hpre_u, hpre_u⟩
                · exact ⟨hpre_u, hpre_u⟩
                · exact ⟨hpre_v, hpre_v⟩
                · exact ⟨hpre_v, hpre_v⟩
              · have hboth : gbad.inputs.contains u.val ∧ gbad.inputs.contains v.val := by
                  by_contra hnotboth
                  apply hgbad_prop
                  refine ⟨hop_eq, by simp [hins], ?_, hnotboth⟩
                  simp [hins, hne_ab]
                simp only [hins, List.contains_cons, List.contains_nil, Bool.or_false,
                  Bool.or_eq_true, beq_iff_eq] at hboth
                rcases hboth.1 with h1 | h1 <;> rcases hboth.2 with h2 | h2
                · exact False.elim (huv.ne (Fin.ext (h1.trans h2.symm)))
                · rw [← h1, ← h2]; exact ⟨hpre_u, hpre_v⟩
                · rw [← h1, ← h2]; exact ⟨hpre_v, hpre_u⟩
                · exact False.elim (huv.ne (Fin.ext (h1.trans h2.symm)))
            dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hab.1, hab.2]; rfl
          · rw [hins] at hlen_in; simp at hlen_in
        · rcases hins : gbad.inputs with _ | ⟨a, rest⟩
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · simp only [hop_eq, hins, eval_not, List.headD_cons, Bool.not_false,
              Bool.cond_true, List.take_succ_cons, List.take_zero, List.contains_cons,
              List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hread
            rcases hread with rfl | rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hpre_u]; rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hpre_v]; rfl
      let K : Finset (Fin C.gates.length) :=
        Finset.univ.filter fun j => (symsF.getD (n + j.val) (Sum.inl false)).isLeft
      have hK_ne : K.Nonempty := by
        obtain ⟨j, hj⟩ := hK_nonempty
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      let jmax := K.max' hK_ne
      have hjmax_mem : jmax ∈ K := Finset.max'_mem K hK_ne
      have hjmax_left : (symsF.getD (n + jmax.val) (Sum.inl false)).isLeft :=
        (Finset.mem_filter.mp hjmax_mem).2
      have hjmax_out : C.output ≠ n + jmax.val := by
        intro heq
        rw [heq] at hout'
        rw [hout'] at hjmax_left
        simp at hjmax_left
      obtain ⟨k, hk_gt, hk_lt, gk, hgk_get, hgk_act⟩ := gate_used jmax.val jmax.isLt hjmax_out
      have hgk_eq : C.gates[k] = gk := by
        rw [List.getElem?_eq_getElem hk_lt] at hgk_get
        exact Option.some.inj hgk_get
      have hstPreK_jmax : ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD (n + jmax.val) (Sum.inl false) =
          symsF.getD (n + jmax.val) (Sum.inl false) := by
        have h1 := hprefix_agree (C.gates.take k) (C.gates.drop k) (n + jmax.val)
          (by simp only [List.length_take]; omega)
        rw [List.take_append_drop] at h1
        exact h1.symm
      obtain ⟨bmax, hbmax⟩ : ∃ b, ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD (n + jmax.val) (Sum.inl false) = Sum.inl b := by
        rw [hstPreK_jmax]
        cases h : symsF.getD (n + jmax.val) (Sum.inl false) with
        | inl b => exact ⟨b, rfl⟩
        | inr _ => rw [h] at hjmax_left; simp at hjmax_left
      have hk_drop : (⟨k, hk_lt⟩ : Fin C.gates.length) ∈ dropped := by
        simp only [dropped, Finset.mem_filter, Finset.mem_univ, true_and]
        obtain ⟨_, hemit⟩ := hstep_at k hk_lt
        rw [hemit, hgk_eq]
        have hgk_fan := hCfan gk (List.mem_of_getElem? hgk_get)
        have hop := hgk_fan.1
        have hlen_in := hgk_fan.2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop_eq | hop_eq | hop_eq
        · rcases hins : gk.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · simp only [active, hop_eq, hins, eval_and, List.all_cons, List.all_nil, id_eq,
              Bool.and_true, Bool.cond_false, List.take_succ_cons, List.take_zero, List.mem_cons,
              List.not_mem_nil, or_false] at hgk_act
            rcases hgk_act with rfl | rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]
              cases bmax <;> cases ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) with
              | inl bb => cases bb <;> rfl
              | inr _ => rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]
              cases bmax <;> cases ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ => rfl
          · rw [hins] at hlen_in; simp at hlen_in
        · rcases hins : gk.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · simp only [active, hop_eq, hins, eval_or, List.any_cons, List.any_nil, id_eq,
              Bool.or_false, Bool.cond_false, List.take_succ_cons, List.take_zero, List.mem_cons,
              List.not_mem_nil, or_false] at hgk_act
            rcases hgk_act with rfl | rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]
              cases bmax <;> cases ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) with
              | inl bb => cases bb <;> rfl
              | inr _ => rfl
            · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]
              cases bmax <;> cases ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ => rfl
          · rw [hins] at hlen_in; simp at hlen_in
        · rcases hins : gk.inputs with _ | ⟨a, rest⟩
          · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
          · simp only [active, hop_eq, hins, eval_not, List.headD_cons, Bool.not_false,
              Bool.cond_true, List.take_succ_cons, List.take_zero, List.mem_singleton] at hgk_act
            subst hgk_act
            dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]; rfl
      have hk_not_read : (⟨k, hk_lt⟩ : Fin C.gates.length) ∉ readers := by
        intro hmem
        simp only [readers, Finset.mem_filter, Finset.mem_univ, true_and, hgk_eq] at hmem
        have hk_in_K : (⟨k, hk_lt⟩ : Fin C.gates.length) ∈ K := by
          simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
          obtain ⟨hsymk, _⟩ := hstep_at k hk_lt
          rw [hsymk, hgk_eq]
          have hpre_u : ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD u.val (Sum.inl false) = Sum.inl false := by
            have h1 := hprefix_agree [] (C.gates.take k) u.val (by simp [u.isLt])
            simpa [syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range u.isLt] using h1
          have hpre_v : ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD v.val (Sum.inl false) = Sum.inl false := by
            have h1 := hprefix_agree [] (C.gates.take k) v.val (by simp [v.isLt])
            simpa [syms0, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range v.isLt] using h1
          have hgk_fan := hCfan gk (List.mem_of_getElem? hgk_get)
          have hop := hgk_fan.1
          have hlen_in := hgk_fan.2
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop_eq | hop_eq | hop_eq
          · rcases hins : gk.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
            · simp only [active, hop_eq, hins, eval_and, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, Bool.cond_false, List.take_succ_cons, List.take_nil,
                List.mem_singleton] at hgk_act
              subst hgk_act
              dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]; rfl
            · simp only [readsUV, hop_eq, hins, eval_and, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, Bool.cond_false, List.take_succ_cons, List.take_zero, List.contains_cons,
                List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
              have hab : ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) = Sum.inl false ∨
                  ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) = Sum.inl false := by
                rcases hmem with (rfl | rfl) | (rfl | rfl)
                · exact Or.inl hpre_u
                · exact Or.inr hpre_u
                · exact Or.inl hpre_v
                · exact Or.inr hpre_v
              rcases hab with ha | hb
              · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [ha]; rfl
              · dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hb]
                cases ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) with
                | inl ba => cases ba <;> rfl
                | inr wa => rfl
            · rw [hins] at hlen_in; simp at hlen_in
          · rcases hins : gk.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
            · simp only [active, hop_eq, hins, eval_or, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.cond_false, List.take_succ_cons, List.take_nil,
                List.mem_singleton] at hgk_act
              subst hgk_act
              dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]; rfl
            · simp only [active, hop_eq, hins, eval_or, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.cond_false, List.take_succ_cons, List.take_zero, List.mem_cons,
                List.not_mem_nil, or_false] at hgk_act
              simp only [readsUV, hop_eq, hins, eval_or, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.cond_false, List.take_succ_cons, List.take_zero, List.contains_cons,
                List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
              rcases hgk_act with rfl | rfl
              · have hb_uv : b = u.val ∨ b = v.val := by
                  rcases hmem with (h1 | h1) | (h1 | h1)
                  · omega
                  · exact Or.inl h1.symm
                  · omega
                  · exact Or.inr h1.symm
                have hb : ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD b (Sum.inl false) = Sum.inl false := by
                  rcases hb_uv with rfl | rfl <;> assumption
                dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax, hb]
                cases bmax <;> rfl
              · have ha_uv : a = u.val ∨ a = v.val := by
                  rcases hmem with (h1 | h1) | (h1 | h1)
                  · exact Or.inl h1.symm
                  · omega
                  · exact Or.inr h1.symm
                  · omega
                have ha : ((C.gates.take k).foldl stepSym (syms0, [], [])).1.getD a (Sum.inl false) = Sum.inl false := by
                  rcases ha_uv with rfl | rfl <;> assumption
                dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax, ha]
                cases bmax <;> rfl
            · rw [hins] at hlen_in; simp at hlen_in
          · rcases hins : gk.inputs with _ | ⟨a, rest⟩
            · dsimp only [stepRes]; rw [hop_eq, hins]; rfl
            · simp only [active, hop_eq, hins, eval_not, List.headD_cons, Bool.not_false,
                Bool.cond_true, List.take_succ_cons, List.take_zero, List.mem_singleton] at hgk_act
              subst hgk_act
              dsimp only [stepRes]; rw [hop_eq, hins]; dsimp only; rw [hbmax]; rfl
        have hle := Finset.le_max' K ⟨k, hk_lt⟩ hk_in_K
        exact absurd hle (not_le_of_gt hk_gt)
      have hssub : readers ⊂ dropped :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hreaders_sub, fun heq => hk_not_read (heq ▸ hk_drop)⟩
      have hlt := Finset.card_lt_card hssub
      rw [hreaders_card] at hlt
      dsimp only [readsUV] at hlt
      dsimp only at heq6
      rw [heq6] at hlt
      refine ⟨Cnew.size, ?_, ⟨Cnew, hCnew_fan, le_rfl, hCnew_eval⟩⟩
      omega
  by_cases hsparse : ∀ u v : Fin n, G.Adj u v →
      let rs := C.gates.filter fun g =>
        let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
        ins.contains u.val || ins.contains v.val
      rs.length ≤ 6 ∧
        (rs.length = 6 → ∀ g ∈ rs, g.op = GateOp.or ∧ g.inputs.length = 2 ∧
          g.inputs.Nodup ∧ ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val))
  · by_cases hhasNot : ∃ g ∈ C.gates, g.op = GateOp.not
    · obtain ⟨u, v, huA, hvA, huv, t, ht, hsz⟩ :=
        hNot n G A f C hnon hdeg hgirth hA hedge hf hCmin hCfun hhasNot hsparse
      exact ⟨u, v, huA, hvA, huv, t, ht.trans hCs, hsz⟩
    · have hmono : Monotone2 C := by
        intro g hg
        have h0 := hCfan g hg
        have hne : g.op ≠ GateOp.not := fun heq => hhasNot ⟨g, hg, heq⟩
        refine ⟨?_, h0.2⟩
        have hmem := h0.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact False.elim (hne h3)
      obtain ⟨u, v, huA, hvA, huv, t, ht, hsz⟩ :=
        hMono n G A f C hnon hdeg hgirth hA hedge hf hCmin hCfun hmono hsparse
      exact ⟨u, v, huA, hvA, huv, t, ht.trans hCs, hsz⟩
  · have hex_bad : ∃ u v : Fin n, G.Adj u v ∧
        ¬ ((C.gates.filter fun g =>
            let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
            ins.contains u.val || ins.contains v.val).length ≤ 6 ∧
          ((C.gates.filter fun g =>
            let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
            ins.contains u.val || ins.contains v.val).length = 6 →
            ∀ g ∈ (C.gates.filter fun g =>
              let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
              ins.contains u.val || ins.contains v.val),
              g.op = GateOp.or ∧ g.inputs.length = 2 ∧
                g.inputs.Nodup ∧ ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val))) := by
      by_contra hno
      apply hsparse
      intro u v huv
      by_contra hbad
      exact hno ⟨u, v, huv, hbad⟩
    obtain ⟨u, v, huv, hbad⟩ := hex_bad
    set rs := C.gates.filter fun g =>
      let ins := g.inputs.take (bif g.op.eval [false] then 1 else 2)
      ins.contains u.val || ins.contains v.val
    have htrig : 7 ≤ rs.length ∨
        (rs.length = 6 ∧ ∃ g ∈ rs, ¬ (g.op = GateOp.or ∧ g.inputs.length = 2 ∧
          g.inputs.Nodup ∧ ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val))) := by
      by_cases hle6 : rs.length ≤ 6
      · have hnot6 : ¬ (rs.length = 6 → ∀ g ∈ rs, g.op = GateOp.or ∧ g.inputs.length = 2 ∧
            g.inputs.Nodup ∧ ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val)) :=
          fun h => hbad ⟨hle6, h⟩
        have heq6 : rs.length = 6 := by
          by_contra hne
          exact hnot6 (fun h => False.elim (hne h))
        have hex_g : ∃ g ∈ rs, ¬ (g.op = GateOp.or ∧ g.inputs.length = 2 ∧
            g.inputs.Nodup ∧ ¬ (g.inputs.contains u.val ∧ g.inputs.contains v.val)) := by
          by_contra hno
          apply hnot6
          intro _ g hg
          by_contra hg_bad
          exact hno ⟨g, hg, hg_bad⟩
        exact Or.inr ⟨heq6, hex_g⟩
      · exact Or.inl (by omega)
    obtain ⟨t, ht, hsz⟩ := elim_edge u v huv htrig
    exact ⟨u, v, hA u v huv, hA v u huv.symm, huv, t, ht.trans hCs, hsz⟩
