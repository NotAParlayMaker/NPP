import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def readBit (w : List Bool) (i : ℕ) : Bool := w.getD i false

private def nextBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (readBit w))

private def pushGate (w : List Bool) (g : Gate) : List Bool := w ++ [nextBit w g]

private def runGates (gs : List Gate) (w : List Bool) : List Bool := gs.foldl pushGate w

private def trueLe (w z : List Bool) : Prop := ∀ i, readBit w i = true → readBit z i = true

private def gateOK (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

-- A binary OR is counted when both of its incoming wires are true.
private def liveOr (gs : List Gate) (w : List Bool) (i : ℕ) : Prop :=
  ∃ g a b, gs[i]? = some g ∧ g.op = .or ∧ g.inputs = [a, b] ∧
    readBit (runGates (gs.take i) w) a = true ∧
    readBit (runGates (gs.take i) w) b = true

private lemma readBit_push (w : List Bool) (g : Gate) (i : ℕ) :
    readBit (pushGate w g) i = if i = w.length then nextBit w g else readBit w i := by
  unfold readBit pushGate
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases h : i = w.length
    · simp [h]
    · rw [ite_eq_right h, List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega),
        List.getD_eq_default _ _ (by omega)]

private lemma nextBit_mono {g : Gate} (hg : gateOK g) {w z : List Bool} (h : trueLe w z) :
    nextBit w g = true → nextBit z g = true := by
  obtain ⟨hg | hg, _⟩ := hg
  · simp only [nextBit, hg, GateOp.eval, List.all_eq_true, List.mem_map]
    intro hw x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (hw _ ⟨i, hi, rfl⟩)
  · simp only [nextBit, hg, GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨_, ⟨i, hi, rfl⟩, hw⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hw⟩

private lemma pushGate_mono {g : Gate} (hg : gateOK g) {w z : List Bool}
    (hlen : w.length = z.length) (hle : trueLe w z) :
    trueLe (pushGate w g) (pushGate z g) := by
  intro i
  simp only [readBit_push, hlen]
  split
  · exact nextBit_mono hg hle
  · exact hle i

private lemma runGates_mono {gs : List Gate} (hgs : ∀ g ∈ gs, gateOK g)
    {w z : List Bool} (hlen : w.length = z.length) (hle : trueLe w z) :
    trueLe (runGates gs w) (runGates gs z) := by
  induction gs generalizing w z with
  | nil => exact hle
  | cons g gs ih =>
    exact ih (fun h hm => hgs h (List.mem_cons_of_mem _ hm))
      (by simp [pushGate, hlen]) (pushGate_mono (hgs g (by simp)) hlen hle)

private lemma liveOr_mono {gs : List Gate} (hgs : ∀ g ∈ gs, gateOK g)
    {w z : List Bool} (hlen : w.length = z.length) (hle : trueLe w z) (i : ℕ) :
    liveOr gs w i → liveOr gs z i := by
  rintro ⟨g, a, b, hgi, hop, hins, ha, hb⟩
  have hrun := runGates_mono (gs := gs.take i) (fun g hg => hgs g (List.mem_of_mem_take hg)) hlen hle
  exact ⟨g, a, b, hgi, hop, hins, hrun _ ha, hrun _ hb⟩

private lemma liveOr_cons_zero (g : Gate) (gs : List Gate) (w : List Bool) :
    liveOr (g :: gs) w 0 ↔
      ∃ a b, g.op = .or ∧ g.inputs = [a, b] ∧
        readBit w a = true ∧ readBit w b = true := by
  simp [liveOr, runGates]

private lemma liveOr_cons_succ (g : Gate) (gs : List Gate) (w : List Bool) (i : ℕ) :
    liveOr (g :: gs) w (i + 1) ↔ liveOr gs (pushGate w g) i := by
  simp [liveOr, runGates, List.take_succ_cons]

-- Compare a set containing an old edge, a new edge, and the singleton it extends.
private def mix (small edge single : List Bool) (i : ℕ) : Prop :=
  readBit small i = true ∧ readBit edge i = true ∧ readBit single i = false

private def gateMix (small edge single : List Bool) (g : Gate) : Prop :=
  nextBit small g = true ∧ nextBit edge g = true ∧ nextBit single g = false

private lemma mixedGate {g : Gate} (hg : gateOK g) {large small edge single : List Bool}
    (hlarge : trueLe small large) (hedge : trueLe edge large)
    (hm : gateMix small edge single g) :
    (∃ i, mix small edge single i) ∨
      ((∃ a b, g.op = .or ∧ g.inputs = [a, b] ∧
        readBit large a = true ∧ readBit large b = true) ∧
        ¬ (∃ a b, g.op = .or ∧ g.inputs = [a, b] ∧
          readBit small a = true ∧ readBit small b = true)) := by
  obtain ⟨hop | hop, hlen⟩ := hg
  · left
    obtain ⟨hs, he, hn⟩ := hm
    have hnot : ¬ (g.inputs.map (readBit single)).all id = true := by
      unfold nextBit at hn
      simp only [hop, GateOp.eval] at hn
      simp [hn]
    simp only [List.all_eq_true, List.mem_map, id_eq, not_forall] at hnot
    obtain ⟨_, ⟨i, hi, rfl⟩, hfalse⟩ := hnot
    simp only [nextBit, hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hs he
    exact ⟨i, hs _ ⟨i, hi, rfl⟩, he _ ⟨i, hi, rfl⟩, Bool.eq_false_of_not_eq_true hfalse⟩
  · cases hins : g.inputs with
    | nil => simp [gateMix, nextBit, hop, GateOp.eval, hins] at hm
    | cons a rest =>
      cases rest with
      | nil =>
        left
        exact ⟨a, by simpa [gateMix, mix, nextBit, hop, GateOp.eval, hins] using hm⟩
      | cons b rest =>
        have hempty : rest = [] := by
          simp [hins] at hlen
          exact hlen
        subst rest
        obtain ⟨hs, he, hn⟩ := hm
        simp only [nextBit, hop, GateOp.eval, hins, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true,
          Bool.or_eq_false_iff] at hs he hn
        by_cases ha : readBit small a = true
        · by_cases ha' : readBit edge a = true
          · exact Or.inl ⟨a, ha, ha', hn.1⟩
          · have hb' := he.resolve_left ha'
            by_cases hb : readBit small b = true
            · exact Or.inl ⟨b, hb, hb', hn.2⟩
            · refine Or.inr ⟨⟨a, b, hop, rfl, hlarge a ha, hedge b hb'⟩, ?_⟩
              rintro ⟨a', b', _, h', _, hb''⟩
              simp only [List.cons.injEq] at h'
              exact hb (h'.2.1 ▸ hb'')
        · have hb := hs.resolve_left ha
          by_cases hb' : readBit edge b = true
          · exact Or.inl ⟨b, hb, hb', hn.2⟩
          · have ha' := he.resolve_right hb'
            refine Or.inr ⟨⟨a, b, hop, rfl, hedge a ha', hlarge b hb⟩, ?_⟩
            rintro ⟨a', b', _, h', ha'', _⟩
            simp only [List.cons.injEq] at h'
            exact ha (h'.1 ▸ ha'')

-- The first mixed wire forces a newly counted OR.
private lemma runGates_newLive {gs : List Gate} (hgs : ∀ g ∈ gs, gateOK g)
    {large small edge single : List Bool}
    (hls : small.length = large.length) (hle : edge.length = large.length)
    (hln : single.length = large.length)
    (hs : trueLe small large) (he : trueLe edge large)
    (hno : ∀ i, ¬ mix small edge single i)
    (hm : ∃ i, mix (runGates gs small) (runGates gs edge) (runGates gs single) i) :
    ∃ i, liveOr gs large i ∧ ¬ liveOr gs small i := by
  induction gs generalizing large small edge single with
  | nil => obtain ⟨i, hi⟩ := hm; exact (hno i hi).elim
  | cons g gs ih =>
    have hg := hgs g (by simp)
    by_cases hb : gateMix small edge single g
    · obtain ⟨i, hi⟩ | ⟨hLg, hSm⟩ := mixedGate hg hs he hb
      · exact (hno i hi).elim
      · exact ⟨0, (liveOr_cons_zero _ _ _).mpr hLg, fun h =>
          hSm ((liveOr_cons_zero _ _ _).mp h)⟩
    · have hnone : ∀ i, ¬ mix (pushGate small g) (pushGate edge g) (pushGate single g) i := by
        intro i
        simp only [mix, readBit_push, hls, hle, hln]
        by_cases hh : i = large.length
        · simpa only [ite_eq_left hh, gateMix] using hb
        · simpa only [ite_eq_right hh, mix] using hno i
      obtain ⟨i, hi, hn⟩ := ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
        (by simp [pushGate, hls]) (by simp [pushGate, hle]) (by simp [pushGate, hln])
        (pushGate_mono hg hls hs) (pushGate_mono hg hle he) hnone hm
      exact ⟨i+1, (liveOr_cons_succ _ _ _ _).mpr hi, fun h => hn ((liveOr_cons_succ _ _ _ _).mp h)⟩

private def onSet {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

private lemma onSet_true {n : ℕ} {S : Finset (Fin n)} {v : Fin n} :
    onSet S v = true ↔ v ∈ S := by
  simp [onSet]

private lemma readBit_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    readBit (List.ofFn x) i = if hi : i < n then x ⟨i, hi⟩ else false := by
  unfold readBit
  split
  next hi =>
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  next hi =>
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]

private lemma onSet_mono {n : ℕ} {S T : Finset (Fin n)} (h : S ⊆ T) :
    trueLe (List.ofFn (onSet S)) (List.ofFn (onSet T)) := by
  intro i hi
  simp only [readBit_ofFn] at hi ⊢
  split at hi
  next hlt =>
    simp only [dite_eq_left hlt, onSet_true] at hi ⊢
    exact h hi
  next => contradiction

private noncomputable def liveSet {n : ℕ} (C : Circuit) (A : Finset ℕ)
    (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact A.filter (liveOr C.gates (List.ofFn (onSet S)))

private lemma mem_liveSet {n : ℕ} {C : Circuit} {A : Finset ℕ} {S : Finset (Fin n)} {j : ℕ} :
    j ∈ liveSet C A S ↔ j ∈ A ∧ liveOr C.gates (List.ofFn (onSet S)) j := by
  classical
  simp [liveSet]

private lemma walks_stay {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (h : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) {a b : Fin n} (p : G.Walk a b) :
    a ∈ S → b ∈ S := by
  induction p with
  | nil => exact id
  | cons hAdj walk ih =>
    intro ha
    exact ih (h _ ha _ hAdj)

private lemma add_adjacent_increases {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    {A : Finset ℕ} (hC : Monotone2 C)
    (hEval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .or → j ∈ A)
    {S : Finset (Fin n)} {v w : Fin n} (hv : v ∉ S) (hw : w ∈ S) (hEdge : G.Adj v w)
    (hTrue : ∃ a ∈ S, ∃ b ∈ S, G.Adj a b) :
    (liveSet C A S).card < (liveSet C A (insert v S)).card := by
  let T := insert v S
  let E : Finset (Fin n) := {v, w}
  let N : Finset (Fin n) := {w}
  have hST : S ⊆ T := Finset.subset_insert _ _
  have hET : E ⊆ T := by
    intro i hi
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact hST hw
  have hgs : ∀ g ∈ C.gates, gateOK g := by
    intro g hg
    simpa [gateOK] using hC g hg
  have hNo : ∀ i, ¬ mix (List.ofFn (onSet S)) (List.ofFn (onSet E))
      (List.ofFn (onSet N)) i := by
    intro i hi
    simp only [mix, readBit_ofFn] at hi
    by_cases hlt : i < n
    · simp only [dite_eq_left hlt, onSet_true, E, Finset.mem_insert, Finset.mem_singleton] at hi
      obtain ⟨hiS, rfl | hiw, hn⟩ := hi
      · exact hv hiS
      · exact Bool.false_ne_true (hn ▸ show onSet N ⟨i, hlt⟩ = true from
          onSet_true.mpr (by simp [N, hiw]))
    · simp [hlt] at hi
  have hS : C.eval (List.ofFn (onSet S)) = true := by
    obtain ⟨a, ha, b, hb, hab⟩ := hTrue
    exact (hEval _).mpr ⟨a, b, hab, onSet_true.mpr ha, onSet_true.mpr hb⟩
  have hE : C.eval (List.ofFn (onSet E)) = true := by
    exact (hEval _).mpr ⟨v, w, hEdge, onSet_true.mpr (by simp [E]),
      onSet_true.mpr (by simp [E])⟩
  have hN : C.eval (List.ofFn (onSet N)) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    obtain ⟨a, b, hab, ha, hb⟩ := (hEval _).mp h
    have haw : a = w := by simpa [N] using onSet_true.mp ha
    have hbw : b = w := by simpa [N] using onSet_true.mp hb
    exact hab.ne (haw.trans hbw.symm)
  have hMix : ∃ i, mix (runGates C.gates (List.ofFn (onSet S)))
      (runGates C.gates (List.ofFn (onSet E))) (runGates C.gates (List.ofFn (onSet N))) i := by
    exact ⟨C.output, hS, hE, hN⟩
  obtain ⟨j, hj, hnj⟩ := runGates_newLive hgs (by simp) (by simp) (by simp)
    (onSet_mono hST) (onSet_mono hET) hNo hMix
  have hjA : j ∈ A := by
    obtain ⟨g, _, _, hg, hop, _⟩ := hj
    exact hA j g hg hop
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨hiA, hLive⟩ := mem_liveSet.mp hi
    exact mem_liveSet.mpr ⟨hiA, liveOr_mono hgs (by simp) (onSet_mono hST) i hLive⟩
  · intro heq
    exact hnj (mem_liveSet.mp (heq ▸ (mem_liveSet.mpr ⟨hjA, hj⟩ : j ∈ liveSet C A T))).2

theorem L_meta_598 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → {v : Fin n | ∃ w : Fin n, G.Adj v w}.ncard ≤ A.card + {K : G.ConnectedComponent | ∃ v w : Fin n, G.connectedComponentMk v = K ∧ G.Adj v w}.ncard + 1 := by
  classical
  intro n G C A hC hEval hA
  let P : Set (Fin n) := {v | ∃ w : Fin n, G.Adj v w}
  let V : Finset (Fin n) := P.toFinite.toFinset
  let K : Set G.ConnectedComponent :=
    {k | ∃ v w : Fin n, G.connectedComponentMk v = k ∧ G.Adj v w}
  change P.ncard ≤ A.card + K.ncard + 1
  have hV : ∀ v, v ∈ V ↔ ∃ w, G.Adj v w := by simp [V, P]
  have hcardV : P.ncard = V.card := Set.ncard_eq_toFinset_card P
  rw [hcardV]
  by_cases hEdge : ∃ u v : Fin n, G.Adj u v
  · obtain ⟨u₀, v₀, h₀⟩ := hEdge
    let : Fintype K := Fintype.ofFinite K
    have hr : ∀ k : K, ∃ r, G.connectedComponentMk r = k.val ∧ ∃ v, G.Adj r v := by
      intro k
      obtain ⟨r, v, hc, hrv⟩ := k.property
      exact ⟨r, hc, v, hrv⟩
    choose root hroot hAdj using hr
    let R : Finset (Fin n) := Finset.univ.image root
    have hRV : R ⊆ V := by
      intro v hv
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
      exact (hV _).mpr (hAdj k)
    have hRcard : R.card ≤ K.ncard := by
      simpa [R, Set.fintypeCard_eq_ncard K] using
        (Finset.card_image_le (s := (Finset.univ : Finset K)) (f := root))
    let k₀ : K := ⟨G.connectedComponentMk u₀, u₀, v₀, rfl, h₀⟩
    obtain ⟨b, hAb⟩ := hAdj k₀
    -- Begin with one root per component and one root neighbor to obtain the first edge.
    let S₀ := insert b R
    have hr₀ : root k₀ ∈ R := Finset.mem_image.mpr ⟨k₀, Finset.mem_univ _, rfl⟩
    have hbV : b ∈ V := (hV _).mpr ⟨root k₀, hAb.symm⟩
    have hSV : S₀ ⊆ V := Finset.insert_subset_iff.mpr ⟨hbV, hRV⟩
    have hSCard : S₀.card ≤ K.ncard + 1 :=
      (Finset.card_insert_le _ _).trans (by omega)
    have hstep (S : Finset (Fin n)) (hstart : S₀ ⊆ S) (hSV' : S ⊆ V) (hne : S ≠ V) :
        ∃ v ∉ S, ∃ w ∈ S, G.Adj v w ∧ v ∈ V := by
      by_contra! hnone
      have hclosed (a : Fin n) (ha : a ∈ S) (z : Fin n) (haz : G.Adj a z) : z ∈ S := by
        by_contra hn
        exact hnone z hn a ha haz.symm ((hV _).mpr ⟨a, haz.symm⟩)
      apply hne
      refine Finset.Subset.antisymm hSV' ?_
      intro v hv
      obtain ⟨w, hvw⟩ := (hV v).mp hv
      let k : K := ⟨G.connectedComponentMk v, v, w, rfl, hvw⟩
      have hrk : root k ∈ S :=
        hstart (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
      obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact (hroot k)
      exact walks_stay hclosed p hrk
    have hbound : V.card + (liveSet C A S₀).card ≤ (liveSet C A V).card + S₀.card := by
      refine Finset.strongDownwardInductionOn
        (p := fun S => S₀ ⊆ S → S ⊆ V →
          V.card + (liveSet C A S).card ≤ (liveSet C A V).card + S.card)
        S₀ (n := V.card) ?_ (Finset.card_le_card hSV) (Finset.Subset.refl _) hSV
      intro S ih _ hstart hSV'
      by_cases hEq : S = V
      · rw [hEq, Nat.add_comm V.card]
      obtain ⟨v, hv, w, hw, hadj, hvV⟩ := hstep S hstart hSV' hEq
      have htV : insert v S ⊆ V := Finset.insert_subset_iff.mpr ⟨hvV, hSV'⟩
      have hlt := Finset.ssubset_insert hv
      have hnext := ih (Finset.card_le_card htV) hlt (hstart.trans (Finset.subset_insert _ _)) htV
      have hTrue : ∃ a ∈ S, ∃ b ∈ S, G.Adj a b :=
        ⟨root k₀, hstart (Finset.mem_insert_of_mem hr₀), b, hstart (Finset.mem_insert_self _ _), hAb⟩
      have hNew := add_adjacent_increases hC hEval hA hv hw hadj hTrue
      rw [Finset.card_insert_of_notMem hv] at hnext
      omega
    have hAcard : (liveSet C A V).card ≤ A.card :=
      Finset.card_le_card (fun _ h => (mem_liveSet.mp h).1)
    omega
  · have hEmpty : V = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro v hv
      obtain ⟨w, hw⟩ := (hV _).mp hv
      exact hEdge ⟨v, w, hw⟩
    simp [hEmpty]

end PEqualNP.Outside
