import Mathlib.Order.Preorder.Finite
import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2280_1
    (flat :
      let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
        (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
      ∀ C : Circuit, Monotone2 C → ReadsBack 14 C →
        (¬∃ a b, (gateAt C a).op = .and ∧ (gateAt C b).op = .and ∧ InCone 14 C a b) →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true) → 27 ≤ C.size)
    (nestedSeed :
      let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
        (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
      ∀ (D : Circuit) (j : Fin 14), j = 7 ∨ j = 9 →
        Monotone2 D → ReadsBack 15 D → D.size ≤ 25 →
        let C : Circuit := ⟨⟨.or,[0,j.val]⟩ :: D.gates,D.output⟩
        (∃ a b, (gateAt C a).op = .and ∧ (gateAt C b).op = .and ∧ InCone 14 C a b) →
        ∃ x : Fin 14 → Bool, ¬ (D.eval (List.ofFn x ++ [x 0 || x j]) = true ↔
          ∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true)) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)), x5 = (7 : Fin (14 : ℕ)) ∨ x5 = (9 : Fin (14 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin (14 : ℕ) → Bool), x3 x8 → (x4.eval (List.ofFn x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8 (0 : Fin (14 : ℕ)), x8 x5]]) = Bool.true ↔ x2 x8)) → (26 : ℕ) ≤ x4.size := by
  intro E hit boundary D j hj hmono hboundary
  classical
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

  have getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
    simp

  have gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
      (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
      op.eval l₁ = true → op.eval l₂ = true := by
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.all_eq_true, id_eq]
      intro h b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        have hi1 : i < l₁.length := by omega
        rw [List.getD_eq_getElem _ _ hi1]
        exact h _ (List.getElem_mem hi1)
      have h2 := hle i h1
      rwa [List.getD_eq_getElem _ _ hi] at h2
    · simp only [GateOp.eval, List.any_eq_true, id_eq]
      rintro ⟨b, hb, rfl⟩
      obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        rw [List.getD_eq_getElem _ _ hi]; exact hbi
      have h2 := hle i h1
      have hi2 : i < l₂.length := by omega
      rw [List.getD_eq_getElem _ _ hi2] at h2
      exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

  have wiresFrom_mono (gs : List Gate)
      (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
    induction gs with
    | nil =>
      intro w₁ w₂ _ hle i hi
      exact hle i hi
    | cons g gs ih =>
      intro w₁ w₂ hlen hle i hi
      have hstep1 : wiresFrom (g :: gs) w₁ =
          wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
      have hstep2 : wiresFrom (g :: gs) w₂ =
          wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
      rw [hstep1] at hi
      rw [hstep2]
      apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle j hj
      · by_cases heq : j = w₁.length
        · subst heq
          rw [getD_snoc_eq] at hj
          rw [hlen, getD_snoc_eq]
          exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
            (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
            (by simp) (by
              intro t ht
              by_cases ht_lt : t < g.inputs.length
              · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
                rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
                simp only [List.getElem_map] at ht ⊢
                exact hle _ ht
              · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
                exact Bool.noConfusion ht) hj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj

  have getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : ℕ) (h : j < m) :
      (List.ofFn F).getD j d = F ⟨j, h⟩ := by
    simp [List.getD_eq_getElem?_getD, h]
  have orNotAnd : GateOp.or ≠ GateOp.and := by
    intro h
    cases h
  let fixG (n : ℕ) (g : Gate) : Gate :=
    if g.op = .and then
      if ∀ i ∈ g.inputs, i < n then g else ⟨.or, []⟩
    else ⟨.or, g.inputs.filter (· < n)⟩
  let fixGs (n : ℕ) (gs : List Gate) : List Gate :=
    (gs.zipIdx n).map fun (g,k) => fixG k g
  have fixCons (n : ℕ) (g : Gate) (gs : List Gate) :
      fixGs n (g :: gs) = fixG n g :: fixGs (n + 1) gs := rfl
  have lenFix (n : ℕ) (gs : List Gate) : (fixGs n gs).length = gs.length := by
    simp [fixGs]
  have mFix (n : ℕ) (g : Gate) (op : g.op = .and ∨ g.op = .or) (len : g.inputs.length ≤ 2) :
      (fixG n g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (fixG n g).inputs.length ≤ 2 := by
    rcases op with hop | hop
    · by_cases hall : ∀ i ∈ g.inputs, i < n
      · simp only [fixG, ite_eq_left hop, ite_eq_left hall]
        exact ⟨by simp [hop], len⟩
      · simp [fixG, ite_eq_left hop, ite_eq_right hall]
    · have hfilter : (g.inputs.filter (· < n)).length ≤ 2 :=
        (List.length_filter_le ..).trans len
      simpa [fixG, hop, orNotAnd] using hfilter
  have readFix (n : ℕ) (g : Gate) (i : ℕ) (hi : i ∈ (fixG n g).inputs) : i < n := by
    unfold fixG at hi
    split at hi
    · split at hi
      · rename_i h
        exact h i hi
      · simp at hi
    · exact of_decide_eq_true (List.mem_filter.mp hi).2
  have goodFix (n : ℕ) (g : Gate) (w : List Bool) (hw : w.length = n)
      (hop : g.op = .and ∨ g.op = .or) :
      (fixG n g).op.eval ((fixG n g).inputs.map (fun i => w.getD i false)) =
        g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
    rcases hop with h | h
    · by_cases hall : ∀ i ∈ g.inputs, i < n
      · simp only [fixG, ite_eq_left h, ite_eq_left hall]
      · simp only [fixG, ite_eq_left h, ite_eq_right hall, h]
        change false = (g.inputs.map (fun i => w.getD i false)).all id
        symm
        apply Bool.eq_false_iff.mpr
        intro hvalues
        apply hall
        intro i hi
        have hv := List.all_eq_true.mp hvalues (w.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
        by_contra! hout
        have hfalse := List.getD_eq_default w false (n := i) (by omega)
        exact Bool.noConfusion (show false = true by simpa only [id_eq, hfalse] using hv)
    · rw [show fixG n g = ⟨.or, g.inputs.filter (· < n)⟩ by simp [fixG, h, orNotAnd], h]
      change ((g.inputs.filter (· < n)).map (fun i => w.getD i false)).any id =
        (g.inputs.map (fun i => w.getD i false)).any id
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, id_eq]
      constructor
      · rintro ⟨v, ⟨i, ⟨hi, _⟩, rfl⟩, hv⟩
        exact ⟨_, ⟨i, hi, rfl⟩, hv⟩
      · rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
        have hlt : i < n := by
          by_contra! hout
          have hfalse := List.getD_eq_default w false (n := i) (by omega)
          exact Bool.noConfusion (show false = true by simpa only [id_eq, hfalse] using hv)
        exact ⟨_, ⟨i, ⟨hi, decide_eq_true hlt⟩, rfl⟩, hv⟩
  have wiresFix (gs : List Gate) (n : ℕ) (w : List Bool) (hw : w.length = n)
      (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      wiresFrom (fixGs n gs) w =
        wiresFrom gs w := by
    induction gs generalizing n w with
    | nil => rfl
    | cons g gs ih =>
      rw [fixCons]
      change wiresFrom (fixGs (n + 1) gs)
          (w ++ [(fixG n g).op.eval ((fixG n g).inputs.map fun i => w.getD i false)]) =
        wiresFrom gs
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      rw [goodFix n g w hw (hops g (by simp))]
      exact ih (n + 1) _ (by simp [hw]) (fun a ha => hops a (by simp [ha]))
  have gatesFix (gs : List Gate) (n k : ℕ) (hk : k < gs.length) :
      (fixGs n gs)[k]? = some (fixG (n + k) gs[k]) := by
    induction gs generalizing n k with
    | nil => simp at hk
    | cons g gs ih =>
      cases k
      · simp [fixCons]
      · rename_i k
        have hk' : k < gs.length := by simpa using hk
        simpa [fixCons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) k hk'
  let T : Circuit := ⟨fixGs 15 D.gates, D.output⟩
  have Tlen : T.size = D.size := lenFix 15 D.gates
  have Top : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or := fun g hg => by
    simpa using (hmono g hg).1
  have Tmono : Monotone2 T := by
    intro g hg
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    have hk' : k < D.gates.length := by simpa [T, lenFix] using hk
    have heq := gatesFix D.gates 15 k hk'
    have hm : T.gates[k]? = some T.gates[k] := by simp [hk]
    rw [hkg] at hm
    change (fixGs 15 D.gates)[k]? = some g at hm
    rw [hm] at heq
    have h := mFix (15 + k) D.gates[k] (Top _ (List.getElem_mem hk'))
      (hmono _ (List.getElem_mem hk')).2
    simpa [Option.some.inj heq] using h
  have Tread : ReadsBack 15 T := by
    intro k hk i hi
    have hk' : k < D.gates.length := by simpa [T, lenFix] using hk
    have heq := gatesFix D.gates 15 k hk'
    have he : gateAt T k = fixG (15 + k) D.gates[k] := by
      unfold gateAt T
      simp [List.getD, heq]
    rw [he] at hi
    exact readFix _ _ _ hi
  have Tval (w : List Bool) (hw : w.length = 15) : T.eval w = D.eval w :=
    congrArg (fun l : List Bool => l.getD D.output false) (wiresFix D.gates 15 w hw Top)
  let Q : Circuit := ⟨⟨.or,[0,j.val]⟩ :: T.gates,T.output⟩
  have Qlen : Q.size = D.size + 1 := by
    change T.size + 1 = _
    rw [Tlen]
  have Qmono : Monotone2 Q := by
    intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst g; simp
    · exact Tmono _ h
  have Qread : ReadsBack 14 Q := by
    intro k hk i hi
    cases k with
    | zero =>
      have hs : gateAt Q 0 = ⟨.or,[0,j.val]⟩ := rfl
      rw [hs] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · decide
      · exact j.isLt
    | succ n =>
      have hs : gateAt Q (n + 1) = gateAt T n := rfl
      rw [hs] at hi
      have hn : n < T.gates.length := by simpa [Q] using hk
      have hz := Tread n hn i hi
      omega
  have Qval (x : Fin 14 → Bool) :
      Q.eval (List.ofFn x) = T.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x j]]) := by
    have h0 : (List.ofFn x).getD 0 false = x 0 :=
      getD_ofFn 14 x false 0 (by decide)
    have hj : (List.ofFn x).getD j.val false = x j :=
      getD_ofFn 14 x false j.val j.isLt
    simp only [Circuit.eval, Circuit.wires, Q, List.foldl_cons, List.map_cons, List.map_nil,
      h0, hj]
  have onBoundary (x : Fin 14 → Bool) (hx : boundary x) :
      Q.eval (List.ofFn x) = true ↔ hit x := by
    rw [Qval, Tval _ (by simp)]
    exact hboundary x hx
  have monoEval (x y : Fin 14 → Bool) (hxy : x ≤ y)
      (hx : Q.eval (List.ofFn x) = true) : Q.eval (List.ofFn y) = true := by
    have hops : ∀ g ∈ Q.gates, g.op = .and ∨ g.op = .or :=
      fun g hg => by simpa using (Qmono g hg).1
    refine wiresFrom_mono Q.gates hops (List.ofFn x) (List.ofFn y)
      (by simp) ?_ Q.output hx
    intro i hi
    by_cases hb : i < 14
    · rw [getD_ofFn 14 x false i hb] at hi
      rw [getD_ofFn 14 y false i hb]
      exact Bool.eq_true_of_true_le (hi ▸ hxy ⟨i,hb⟩)
    · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt hb))] at hi
      contradiction
  have computes (x : Fin 14 → Bool) : Q.eval (List.ofFn x) = true ↔ hit x := by
    constructor
    · intro hx
      by_contra hn
      let S : Set (Fin 14 → Bool) := {y | x ≤ y ∧ ¬hit y}
      obtain ⟨y, hy⟩ := (Set.toFinite S).exists_maximal ⟨x, le_rfl, hn⟩
      have hyx : x ≤ y := hy.1.1
      have hyn : ¬hit y := hy.1.2
      have hb : boundary y := by
        refine Or.inr ⟨hyn, ?_⟩
        intro i hi
        by_contra hno
        have hyy : y ≤ Function.update y i true := by
          intro k
          by_cases hki : k = i
          · subst k; simp
          · simp [Function.update_of_ne hki]
        have hm : Function.update y i true ∈ S := ⟨hyx.trans hyy, hno⟩
        have hr := hy.2 hm hyy i
        exact (by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hi] using hr)
      exact hyn ((onBoundary y hb).mp (monoEval x y hyx hx))
    · intro hx
      let S : Set (Fin 14 → Bool) := {y | y ≤ x ∧ hit y}
      obtain ⟨y, hy⟩ := (Set.toFinite S).exists_minimal ⟨x, le_rfl, hx⟩
      have hyx : y ≤ x := hy.1.1
      have hyp : hit y := hy.1.2
      have hb : boundary y := by
        refine Or.inl ⟨hyp, ?_⟩
        intro i hi hyes
        have hyy : Function.update y i false ≤ y := by
          intro k
          by_cases hki : k = i
          · subst k; simp
          · simp [Function.update_of_ne hki]
        have hm : Function.update y i false ∈ S := ⟨hyy.trans hyx, hyes⟩
        have hr := hy.2 hm hyy i
        exact (by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hi] using hr)
      exact monoEval y x hyx ((onBoundary y hb).mpr hyp)
  by_contra! short
  by_cases nested : ∃ a b, (gateAt Q a).op = .and ∧ (gateAt Q b).op = .and ∧ InCone 14 Q a b
  · have hTsize : T.size ≤ 25 := by omega
    have hTval (x : Fin 14 → Bool) : T.eval (List.ofFn x ++ [x 0 || x j]) = true ↔ hit x := by
      rw [← show GateOp.or.eval [x 0, x j] = (x 0 || x j) by cases x 0 <;> cases x j <;> rfl]
      rw [← Qval]
      exact computes x
    obtain ⟨x, hx⟩ := nestedSeed T j hj Tmono Tread hTsize nested
    exact hx (hTval x)
  · have hbound := flat Q Qmono Qread nested computes
    omega
