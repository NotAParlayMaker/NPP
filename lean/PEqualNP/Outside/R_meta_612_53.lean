import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_612_53
    (noLeaves : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S, IsVertexCover G S ∧ S.card = t) →
      (∀ S, IsVertexCover G S → t ≤ S.card) → Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      let leaf := fun v u : Fin n => G.Adj v u ∧ ∀ w, G.Adj v w → w = u
      (¬ ∃ v u, leaf v u) → G.edgeSet.ncard + t ≤ C.size + 1)
    (critical : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S, IsVertexCover G S ∧ S.card = t) →
      (∀ S, IsVertexCover G S → t ≤ S.card) → Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      let leaf := fun v u : Fin n => G.Adj v u ∧ ∀ w, G.Adj v w → w = u
      (∃ v u, leaf v u) →
      (∀ v u, leaf v u → ∃ S, IsVertexCover (G.deleteEdges ({s(v,u)} : Set (Sym2 (Fin n)))) S ∧ S.card < t) →
      (∀ v u, leaf v u → C.gates.countP (fun g => g.inputs.any (· == v.val)) = 1) →
      G.edgeSet.ncard + t ≤ C.size + 1)
    : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  have readerNeeded (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (v u : Fin n)
      (uv : G.Adj v u) (fits : ∀ x : Fin n → Bool,
        C.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
      ∃ g ∈ C.gates, v.val ∈ g.inputs := by
    classical
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun p => w.getD p false)]
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    have raw (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      exact List.getElem_ofFn _
    have singleReject (a : Fin n) : ¬ C.eval (List.ofFn fun i => decide (i = a)) = true := by
      intro on
      obtain ⟨p,q,pq,hp,hq⟩ := (fits (fun i => decide (i = a))).mp on
      have pa : p = a := of_decide_eq_true hp
      have qa : q = a := of_decide_eq_true hq
      exact pq.ne (pa.trans qa.symm)
    have outNe : C.output ≠ v.val := by
      intro eq
      let s : Fin n → Bool := fun i => decide (i = v)
      apply singleReject v
      change (C.gates.foldl step (List.ofFn s)).getD C.output false = true
      rw [eq,keep _ _ _ (by simpa only [List.length_ofFn] using v.isLt),raw]
      exact decide_eq_true rfl
    by_contra no
    have avoids (g : Gate) (mem : g ∈ C.gates) : v.val ∉ g.inputs := fun h => no ⟨g,mem,h⟩
    let agrees (w z : List Bool) : Prop :=
      w.length = z.length ∧ ∀ i, i ≠ v.val → w.getD i false = z.getD i false
    have expand (w z : List Bool) (h : agrees w z) (a : Bool) :
        agrees (w ++ [a]) (z ++ [a]) := by
      refine ⟨by simp only [List.length_append,h.1],?_⟩
      intro i ne
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (h.1 ▸ hi),h.2 i ne]
      · have past := Nat.le_of_not_gt hi
        rw [List.getD_append_right _ _ _ _ past,List.getD_append_right _ _ _ _ (h.1 ▸ past),h.1]
    have folds (gs : List Gate) (free : ∀ g ∈ gs, v.val ∉ g.inputs) (w z : List Bool)
        (h : agrees w z) : agrees (gs.foldl step w) (gs.foldl step z) := by
      induction gs generalizing w z with
      | nil => exact h
      | cons g gs ih =>
        rw [List.foldl_cons,List.foldl_cons]
        apply ih (fun k hk => free k (List.mem_cons_of_mem _ hk))
        have eqArgs : g.inputs.map (fun p => w.getD p false) = g.inputs.map (fun p => z.getD p false) := by
          apply List.map_congr_left
          intro i hi
          exact h.2 i (fun eq => free g (List.mem_cons_self ..) (eq ▸ hi))
        change agrees (w ++ [g.op.eval _]) (z ++ [g.op.eval _])
        rw [eqArgs]
        exact expand w z h _
    let x : Fin n → Bool := fun i => decide (i = v ∨ i = u)
    let y : Fin n → Bool := fun i => decide (i = u)
    have base : agrees (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp only [List.length_ofFn],?_⟩
      intro i ne
      by_cases low : i < n
      · let k : Fin n := ⟨i,low⟩
        have hk : k ≠ v := fun eq => ne (congrArg Fin.val eq)
        exact (raw x k).trans ((by simp only [x,y,hk,false_or] : x k = y k).trans (raw y k).symm)
      · have hx : (List.ofFn x).length ≤ i := by
          rw [List.length_ofFn]
          omega
        have hy : (List.ofFn y).length ≤ i := by
          rw [List.length_ofFn]
          omega
        rw [List.getD_eq_default _ _ hx,List.getD_eq_default _ _ hy]
    have hit : C.eval (List.ofFn x) = true :=
      (fits x).mpr ⟨v,u,uv,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
    have same : C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
      (folds C.gates avoids _ _ base).2 C.output outNe
    exact singleReject u (same.symm.trans hit)

  have restrictCount (n : ℕ) (C : Circuit) (v : Fin n) (legal : Monotone2 C)
      (zero : C.eval (List.ofFn (fun _ : Fin n => false)) = false) :
      ∃ D : Circuit, Monotone2 D ∧
        D.size + C.gates.countP (fun g => g.inputs.any (· == v.val)) ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          C.eval (List.ofFn (fun i => if i = v then false else x i)) := by
    clear readerNeeded noLeaves critical
    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

    have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
        wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
      simp [wiresFrom, List.foldl_append]

    have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
        ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
        have : wiresFrom (g :: gs) w
            = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
        rw [this, ht]; simp

    have length_wiresFrom (gs : List Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
      rw [ht]; simp [hl]

    have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
        (L ++ [S]).getD j d = L.getD j d := by
      by_cases hj : j < L.length
      · exact List.getD_append _ _ _ _ hj
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp

    let MonoGate (g : Gate) : Prop :=
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

    let Stat := Bool ⊕ ℕ
    let readStat (w : List Bool) : Stat → Bool := Sum.elim id (fun j => w.getD j false)
    let validStat (m : ℕ) : Stat → Prop := Sum.elim (fun _ => True) (fun j => j < m)
    have evalAnd0 (l : List Bool) : GateOp.eval .and l = l.all id := rfl
    have evalOr0 (l : List Bool) : GateOp.eval .or l = l.any id := rfl

    let simpAnd (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      let both (a b : Stat) : Option Gate × Stat :=
        Sum.elim
          (fun c => Sum.elim
            (fun d => (none, Sum.inl (c && d)))
            (fun k => (none, bif c then Sum.inr k else Sum.inl false)) b)
          (fun j => Sum.elim
            (fun d => (none, bif d then Sum.inr j else Sum.inl false))
            (fun k => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)) b) a
      List.rec (motive := fun _ => Option Gate × Stat) (none, Sum.inl true)
        (fun a rest _ => List.rec (motive := fun _ => Option Gate × Stat) (none, a)
          (fun b tail _ => List.rec (motive := fun _ => Option Gate × Stat) (both a b)
            (fun _ _ _ => (none, Sum.inl false)) tail) rest) ins

    let simpOr (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      let both (a b : Stat) : Option Gate × Stat :=
        Sum.elim
          (fun c => Sum.elim
            (fun d => (none, Sum.inl (c || d)))
            (fun k => (none, bif c then Sum.inl true else Sum.inr k)) b)
          (fun j => Sum.elim
            (fun d => (none, bif d then Sum.inl true else Sum.inr j))
            (fun k => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)) b) a
      List.rec (motive := fun _ => Option Gate × Stat) (none, Sum.inl false)
        (fun a rest _ => List.rec (motive := fun _ => Option Gate × Stat) (none, a)
          (fun b tail _ => List.rec (motive := fun _ => Option Gate × Stat) (both a b)
            (fun _ _ _ => (none, Sum.inl false)) tail) rest) ins

    let simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
      GateOp.rec (motive := fun _ => Option Gate × Stat)
        (simpAnd m ins) (simpOr m ins) (none, Sum.inl false)
        (fun _ => (none, Sum.inl false)) (none, Sum.inl false) op

    have simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
        (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
        (hv : ∀ s ∈ ins, validStat w.length s) :
        validStat (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
        readStat (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
          = op.eval (ins.map (readStat w)) := by
      rcases hop with rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpAnd, validStat, readStat, evalAnd0]
        · cases a <;> simp_all [simplify, simpAnd, validStat, readStat, wiresFrom]
        · cases a <;> cases b <;> rename_i c e <;> cases c <;> cases e <;>
            simp_all [simplify, simpAnd, validStat, readStat, wiresFrom]
        · simp at hlen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [simplify, simpOr, validStat, readStat, evalOr0]
        · cases a <;> simp_all [simplify, simpOr, validStat, readStat, wiresFrom]
        · cases a <;> cases b <;> rename_i c e <;> cases c <;> cases e <;>
            simp_all [simplify, simpOr, validStat, readStat, wiresFrom]
        · simp at hlen

    let elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
      (acc.1 ++ [(simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
        acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

    let elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
      gs.foldl (elimStep n) acc

    have toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
      cases o <;> simp

    have validMono {m m' : ℕ} (h : m ≤ m') :
        ∀ s : Stat, validStat m s → validStat m' s := by
      intro s hs
      cases s with
      | inl b => trivial
      | inr j => exact lt_of_lt_of_le hs h

    have valAppend (w t : List Bool) : ∀ s : Stat, validStat w.length s →
        readStat (w ++ t) s = readStat w s := by
      intro s hs
      cases s with
      | inl b => rfl
      | inr j => exact List.getD_append _ _ _ _ hs

    let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
      acc.1.length = w.length ∧ ∀ i : ℕ,
        validStat (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
        readStat (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

    have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
        ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, MonoGate g) → Inv n y w acc →
          Inv n y (wiresFrom gs w) (elim n gs acc) := by
      induction gs with
      | nil => intro w acc _ h; exact h
      | cons g gs ih =>
        intro w acc hok h
        apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        obtain ⟨hl, hi⟩ := h
        set w' := wiresFrom acc.2 y with hw'
        have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
        set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
        have hgok := hok g List.mem_cons_self
        have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
          (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            rw [lw']; exact (hi a).1)
        rw [lw'] at hs
        set r := simplify g.op (n + acc.2.length) ins with hr
        have hvals : ins.map (readStat w') = g.inputs.map fun i => w.getD i false := by
          rw [hins, List.map_map]
          apply List.map_congr_left
          intro a _
          exact (hi a).2
        have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
          rw [wiresFrom_append]
        obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
        refine ⟨by simp [elimStep, hl], ?_⟩
        intro i
        show validStat (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
          readStat (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
        rw [hnew, List.length_append, ← Nat.add_assoc]
        by_cases hil : i = acc.1.length
        · subst hil
          rw [getD_snoc_eq, hl, getD_snoc_eq]
          exact ⟨hs.1, by rw [hs.2, hvals]⟩
        · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
          refine ⟨validMono (by omega) _ (hi i).1, ?_⟩
          rw [ht, valAppend _ _ _ (by rw [lw']; exact (hi i).1)]
          exact (hi i).2

    have simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
        (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
        (hc : ∃ c, Sum.inl c ∈ ins) :
        (simplify op m ins).1 = none := by
      obtain ⟨c, hc⟩ := hc
      rcases hop with rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpAnd]
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp_all [simplify, simpOr]

    have elimCountFrozen (n : ℕ) (frozen : ℕ → Bool) (gs : List Gate) :
        ∀ acc : List Stat × List Gate,
          (∀ g ∈ gs, MonoGate g) →
          (∀ k, frozen k = true → k < acc.1.length ∧
            ∃ b : Bool, acc.1.getD k (Sum.inl false) = Sum.inl b) →
          (elim n gs acc).2.length + gs.countP (fun g => g.inputs.any frozen) ≤
            acc.2.length + gs.length := by
      induction gs with
      | nil => intro acc _ _; simp [elim]
      | cons g gs ih =>
        intro acc hok hfrozen
        let update := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
        let acc' := (acc.1 ++ [update.2], acc.2 ++ update.1.toList)
        have htail := ih acc' (fun g' hg' => hok g' (List.mem_cons_of_mem g hg')) (by
          intro k hk
          obtain ⟨hlen, b, hval⟩ := hfrozen k hk
          refine ⟨by simp [acc']; omega, b, ?_⟩
          change (acc.1 ++ [update.2]).getD k (Sum.inl false) = Sum.inl b
          rwa [getD_snoc_ne _ _ _ _ (by omega)])
        have hstep : acc'.2.length + (if g.inputs.any frozen then 1 else 0) ≤ acc.2.length + 1 := by
          change (acc.2 ++ update.1.toList).length + _ ≤ _
          by_cases hread : g.inputs.any frozen = true
          · obtain ⟨k, hkg, hk⟩ := List.any_eq_true.mp hread
            have hg := hok g List.mem_cons_self
            have hnone : update.1 = none := by
              apply simplify_count _ _ _ hg.1
              · simpa using hg.2
              · obtain ⟨b, hb⟩ := (hfrozen k hk).2
                exact ⟨b, List.mem_map.2 ⟨k, hkg, hb⟩⟩
            simp [hnone, hread]
          · have hl := toList_length_le update.1
            simp only [List.length_append, ite_eq_right hread, Nat.add_zero]
            omega
        change (elim n gs acc').2.length + (g :: gs).countP (fun g => g.inputs.any frozen) ≤ _
        rw [List.countP_cons, List.length_cons]
        omega

    have simplifiedMono (op : GateOp) (m : ℕ) (ins : List Stat) (hop : op = .and ∨ op = .or) :
        ∀ g ∈ (simplify op m ins).1, MonoGate g := by
      intro g hg
      rcases hop with rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simplify, simpAnd] at hg
        subst g
        exact ⟨Or.inl rfl, le_rfl⟩
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
          simp [simplify, simpOr] at hg
        subst g
        exact ⟨Or.inr rfl, le_rfl⟩

    have elimMono (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
        (hgs : ∀ g ∈ gs, MonoGate g) (hacc : ∀ g ∈ acc.2, MonoGate g) :
        ∀ g ∈ (elim n gs acc).2, MonoGate g := by
      induction gs generalizing acc with
      | nil => exact hacc
      | cons g gs ih =>
        apply ih (elimStep n acc g) (fun d hd => hgs d (List.mem_cons_of_mem _ hd))
        let ins := g.inputs.map (fun i => acc.1.getD i (Sum.inl false))
        intro d hd
        change d ∈ acc.2 ++ (simplify g.op (n + acc.2.length) ins).1.toList at hd
        rcases List.mem_append.mp hd with hm | hm
        · exact hacc d hm
        · exact simplifiedMono g.op _ _ (hgs g List.mem_cons_self).1 d (by simpa using hm)


    let clamp (x : Fin n → Bool) (i : Fin n) := if i = v then false else x i
    let inputState (i : Fin n) : Stat := if i = v then Sum.inl false else Sum.inr i.val
    let initial := List.ofFn inputState
    let start : List Stat × List Gate := (initial, [])
    let acc := elim n C.gates start
    have readOf {α : Type} (f : Fin n → α) (i : Fin n) (d : α) :
        (List.ofFn f).getD i.val d = f i := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      exact List.getElem_ofFn _
    have initInv (x : Fin n → Bool) :
        Inv n (List.ofFn x) (List.ofFn (clamp x)) start := by
      refine ⟨by simp only [start, initial, List.length_ofFn], fun i => ?_⟩
      change validStat n (initial.getD i (Sum.inl false)) ∧
        readStat (List.ofFn x) (initial.getD i (Sum.inl false)) =
          (List.ofFn (clamp x)).getD i false
      by_cases hi : i < n
      · let j : Fin n := ⟨i, hi⟩
        have hst : initial.getD i (Sum.inl false) = inputState j := readOf inputState j _
        have hr : (List.ofFn (clamp x)).getD i false = clamp x j := readOf (clamp x) j _
        rw [hst, hr]
        by_cases hv : j = v
        · simp only [inputState, clamp, ite_eq_left hv]
          exact ⟨trivial, rfl⟩
        · simp only [inputState, clamp, ite_eq_right hv]
          exact ⟨hi, readOf x j false⟩
      · rw [List.getD_eq_default _ _ (by simpa only [initial, List.length_ofFn] using Nat.le_of_not_gt hi),
          List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]
        exact ⟨trivial, rfl⟩
    let mask (i : ℕ) := i == v.val
    have hbudget : acc.2.length + C.gates.countP (fun g => g.inputs.any (· == v.val)) ≤ C.size := by
      have bound := elimCountFrozen n mask C.gates start legal (by
        intro i hi
        have he : i = v.val := beq_iff_eq.mp hi
        subst i
        refine ⟨by simpa only [start, initial, List.length_ofFn] using v.isLt, false, ?_⟩
        change initial.getD v.val (Sum.inl false) = Sum.inl false
        rw [show initial.getD v.val (Sum.inl false) = inputState v from readOf inputState v _]
        simp only [inputState, ite_eq_left rfl])
      change acc.2.length + C.gates.countP (fun g => g.inputs.any mask) ≤ 0 + C.size at bound
      simpa only [Nat.zero_add, mask] using bound
    have hmono : ∀ g ∈ acc.2, MonoGate g :=
      elimMono n C.gates start legal (by intro g hg; cases hg)
    have hval (x : Fin n → Bool) :
        readStat (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          C.eval (List.ofFn (clamp x)) := by
      have result := inv_elim n (List.ofFn x) List.length_ofFn C.gates
        (List.ofFn (clamp x)) start legal (initInv x)
      exact (result.2 C.output).2
    cases hout : acc.1.getD C.output (Sum.inl false) with
    | inr k =>
      refine ⟨⟨acc.2, k⟩, hmono, hbudget, fun x => ?_⟩
      have eq := hval x
      rw [hout] at eq
      exact eq
    | inl b =>
      cases b
      · refine ⟨⟨[], n⟩, ?_, ?_, fun x => ?_⟩
        · intro g hg
          cases hg
        · change 0 + C.gates.countP (fun g => g.inputs.any (· == v.val)) ≤ C.size
          exact (Nat.add_le_add_right (Nat.zero_le _) _).trans hbudget
        · change (List.ofFn x).getD n false = _
          rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]), ← hval x, hout]
          rfl
      · let zeros : Fin n → Bool := fun _ => false
        have fixed : clamp zeros = zeros := by
          funext i
          simp [clamp, zeros]
        have eq := hval zeros
        rw [hout, fixed] at eq
        change true = C.eval (List.ofFn (fun _ : Fin n => false)) at eq
        rw [zero] at eq
        cases eq

  classical
  have solve (e : ℕ) : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S, IsVertexCover G S ∧ S.card = t) →
      (∀ S, IsVertexCover G S → t ≤ S.card) → Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      G.edgeSet.ncard = e → G.edgeSet.ncard + t ≤ C.size + 1 := by
    induction e using Nat.strong_induction_on with
    | ind e ih =>
      intro n t G C edges c4 minExists minBound legal fits ncard
      let leaf (v u : Fin n) : Prop := G.Adj v u ∧ ∀ w, G.Adj v w → w = u
      let drop (v u : Fin n) := G.deleteEdges ({s(v,u)} : Set (Sym2 (Fin n)))
      let readCount (v : Fin n) := C.gates.countP fun g => g.inputs.any (· == v.val)
      have countPos (v u : Fin n) (vu : G.Adj v u) : 0 < readCount v := by
        obtain ⟨g,hg,uses⟩ := readerNeeded n G C v u vu fits
        exact List.countP_pos_iff.mpr ⟨g,hg,List.any_eq_true.mpr ⟨v.val,uses,beq_self_eq_true _⟩⟩
      by_cases peel : ∃ v u, leaf v u ∧ ((∀ S, IsVertexCover (drop v u) S → t ≤ S.card) ∨ 2 ≤ readCount v)
      · obtain ⟨v,u,⟨vu,one⟩,budget⟩ := peel
        let H := drop v u
        have keep (a b : Fin n) : H.Adj a b ↔ G.Adj a b ∧ a ≠ v ∧ b ≠ v := by
          change (G.deleteEdges ({s(v,u)} : Set (Sym2 (Fin n)))).Adj a b ↔ _
          rw [SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff]
          constructor
          · rintro ⟨ab,notDrop⟩
            refine ⟨ab,?_,?_⟩
            · intro av
              subst a
              exact notDrop (Sym2.eq_iff.mpr (Or.inl ⟨rfl,one b ab⟩))
            · intro bv
              subst b
              exact notDrop (Sym2.eq_iff.mpr (Or.inr ⟨one a ab.symm,rfl⟩))
          · rintro ⟨ab,av,bv⟩
            refine ⟨ab,?_⟩
            intro eq
            rcases Sym2.eq_iff.mp eq with ⟨ha,_⟩ | ⟨_,hb⟩
            · exact av ha
            · exact bv hb
        have count : H.edgeSet.ncard + 1 = G.edgeSet.ncard := by
          change (G.deleteEdges ({s(v,u)} : Set (Sym2 (Fin n)))).edgeSet.ncard + 1 = _
          rw [SimpleGraph.edgeSet_deleteEdges]
          exact Set.ncard_sdiff_singleton_add_one (show s(v,u) ∈ G.edgeSet from vu)
        have c4H (a b c d : Fin n) (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
            (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) (hab : H.Adj a b)
            (hbc : H.Adj b c) (hcd : H.Adj c d) (hda : H.Adj d a) : False :=
          c4 a b c d ab ac ad bc bd cd ((keep a b).mp hab).1 ((keep b c).mp hbc).1
            ((keep c d).mp hcd).1 ((keep d a).mp hda).1
        obtain ⟨S,sCover,sCard⟩ := minExists
        have coverH : IsVertexCover H S := fun a b hit => sCover a b ((keep a b).mp hit).1
        have existsCover : ∃ k : ℕ, ∃ K : Finset (Fin n), IsVertexCover H K ∧ K.card = k :=
          ⟨t,S,coverH,sCard⟩
        let k := Nat.find existsCover
        obtain ⟨K,kCover,kCard⟩ := Nat.find_spec existsCover
        have minH (L : Finset (Fin n)) (lCover : IsVertexCover H L) : k ≤ L.card :=
          Nat.find_min' existsCover ⟨L,lCover,rfl⟩
        have addLeaf : IsVertexCover G (insert v K) := by
          intro a b ab
          by_cases av : a = v
          · exact Or.inl (Finset.mem_insert.mpr (Or.inl av))
          by_cases bv : b = v
          · exact Or.inr (Finset.mem_insert.mpr (Or.inl bv))
          rcases kCover a b ((keep a b).mpr ⟨ab,av,bv⟩) with ha | hb
          · exact Or.inl (Finset.mem_insert_of_mem ha)
          · exact Or.inr (Finset.mem_insert_of_mem hb)
        have loss : t ≤ k + 1 := by
          have upper := (minBound (insert v K) addLeaf).trans (Finset.card_insert_le v K)
          change K.card = k at kCard
          omega
        have zero : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
          cases e : C.eval (List.ofFn (fun _ : Fin n => false)) with
          | false => rfl
          | true =>
            obtain ⟨a,b,ab,ha,hb⟩ := (fits (fun _ => false)).mp e
            exact Bool.noConfusion ha
        obtain ⟨D,dLegal,save,dEval⟩ := restrictCount n C v legal zero
        change D.size + readCount v ≤ C.size at save
        have saving : D.size + 1 + t ≤ C.size + k := by
          rcases budget with preserve | multiple
          · have lower := preserve K kCover
            have pos := countPos v u vu
            change K.card = k at kCard
            omega
          · omega
        have fitH (x : Fin n → Bool) : D.eval (List.ofFn x) = true ↔
            ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
          rw [dEval x,fits]
          constructor
          · rintro ⟨a,b,ab,ha,hb⟩
            have av : a ≠ v := by
              intro eq
              subst a
              simp at ha
            have bv : b ≠ v := by
              intro eq
              subst b
              simp at hb
            exact ⟨a,b,(keep a b).mpr ⟨ab,av,bv⟩,by simpa only [ite_eq_right av] using ha,
              by simpa only [ite_eq_right bv] using hb⟩
          · rintro ⟨a,b,ab,ha,hb⟩
            obtain ⟨orig,av,bv⟩ := (keep a b).mp ab
            exact ⟨a,b,orig,by simpa only [ite_eq_right av] using ha,by simpa only [ite_eq_right bv] using hb⟩
        by_cases hasH : ∃ a b, H.Adj a b
        · have bound := ih H.edgeSet.ncard (by omega) n k H D hasH c4H ⟨K,kCover,kCard⟩ minH dLegal fitH rfl
          omega
        · have bot : H = ⊥ := by
            by_contra ne
            exact hasH (SimpleGraph.ne_bot_iff_exists_adj.mp ne)
          have hzero : H.edgeSet.ncard = 0 := by rw [bot]; simp
          have kzero : k = 0 := by
            have empty : IsVertexCover H (∅ : Finset (Fin n)) := fun a b h => False.elim (hasH ⟨a,b,h⟩)
            have le := minH ∅ empty
            rw [Finset.card_empty] at le
            omega
          omega
      · by_cases someLeaf : ∃ v u, leaf v u
        · have allDrop (v u : Fin n) (hleaf : leaf v u) :
              ∃ S, IsVertexCover (drop v u) S ∧ S.card < t := by
            by_contra none
            refine peel ⟨v,u,hleaf,Or.inl ?_⟩
            intro S sc
            exact Nat.le_of_not_gt (fun lt => none ⟨S,sc,lt⟩)
          have readOnce (v u : Fin n) (hleaf : leaf v u) : readCount v = 1 := by
            have pos := countPos v u hleaf.1
            have few : ¬ 2 ≤ readCount v := fun multiple => peel ⟨v,u,hleaf,Or.inr multiple⟩
            omega
          exact critical n t G C edges c4 minExists minBound legal fits someLeaf allDrop readOnce
        · exact noLeaves n t G C edges c4 minExists minBound legal fits someLeaf
  intro n t G C edges c4 minExists minBound legal fits
  exact solve G.edgeSet.ncard n t G C edges c4 minExists minBound legal fits rfl
