import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1519_aux

open PEqualNP.CircuitLowerBounds

private def runGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma runGates_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    runGates (g :: gs) x = runGates gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma runGates_length (gs : List Gate) (x : List Bool) :
    (runGates gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [runGates]
  | cons g gs ih => rw [runGates_cons, ih]; simp; omega

private lemma runGates_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (runGates gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [runGates_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma runGates_split (gs : List Gate) (x : List Bool) (k : ℕ) :
    runGates gs x = runGates (gs.drop k) (runGates (gs.take k) x) := by
  simpa only [runGates, List.foldl_append] using
    congrArg (fun l : List Gate => runGates l x) (List.take_append_drop k gs).symm

private def wval (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false

private lemma eval_eq_wval (gs : List Gate) (o : ℕ) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = wval gs x o := rfl

private lemma wval_input (gs : List Gate) (x : Fin 13 → Bool) (p : Fin 13) :
    wval gs x p.val = x p := by
  change (runGates gs (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp [p.isLt]
  rw [runGates_getD _ _ _ hp, List.getD_eq_getElem _ _ hp, List.getElem_ofFn]

private lemma wval_oob (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : 13 + gs.length ≤ w) :
    wval gs x w = false := by
  change (runGates gs (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [runGates_length] using hw)

private lemma wval_gate (gs : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : k < gs.length) :
    wval gs x (13 + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < 13 + k then wval gs x r else false) := by
  let earlier := runGates (gs.take k) (List.ofFn x)
  have hlen : earlier.length = 13 + k := by
    simp [earlier, runGates_length, Nat.min_eq_left hk.le]
  have hsplit : runGates gs (List.ofFn x) = runGates (gs[k] :: gs.drop (k + 1)) earlier := by
    rw [runGates_split gs (List.ofFn x) k, List.drop_eq_getElem_cons hk]
  have hread (r : ℕ) : earlier.getD r false = if r < 13 + k then wval gs x r else false := by
    by_cases hr : r < 13 + k
    · rw [ite_eq_left hr]
      change earlier.getD r false = (runGates gs (List.ofFn x)).getD r false
      rw [hsplit]
      exact (runGates_getD _ earlier r (by simpa only [hlen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (runGates gs (List.ofFn x)).getD (13 + k) false = _
  rw (occs := [1]) [hsplit]
  rw (occs := [1]) [runGates_cons]
  rw [runGates_getD _ _ _ (by simp [hlen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.sub_self, List.getD_cons_zero, hread]

private lemma wval_or (gs : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    wval gs x (13 + k) = true ↔ ∃ r ∈ gs[k].inputs, r < 13 + k ∧ wval gs x r = true := by
  rw [wval_gate gs x k hk, hop]
  simp [GateOp.eval]

private lemma wval_and (gs : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    wval gs x (13 + k) = true ↔ ∀ r ∈ gs[k].inputs, r < 13 + k ∧ wval gs x r = true := by
  rw [wval_gate gs x k hk, hop]
  simp [GateOp.eval]

private lemma wval_not_cons (gs : List Gate) (x : Fin 13 → Bool) (j h : Fin gs.length)
    (hop : (gs.get j).op = GateOp.not) (hhj : h < j)
    (hins : ∃ r : List ℕ, (gs.get j).inputs = (13 + (h : ℕ)) :: r) :
    wval gs x (13 + (j : ℕ)) = !(wval gs x (13 + (h : ℕ))) := by
  obtain ⟨r, hr⟩ := hins
  rw [wval_gate gs x j.val j.isLt]
  have hop' : gs[j.val].op = GateOp.not := by simpa using hop
  have hr' : gs[j.val].inputs = (13 + h.val) :: r := by simpa using hr
  have hlt : 13 + h.val < 13 + j.val := by
    have : h.val < j.val := hhj
    omega
  rw [hop', hr']
  simp [GateOp.eval, hlt]

private lemma wval_gate_mono (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or)
    (x y : Fin 13 → Bool)
    (h : ∀ r ∈ gs[k].inputs, r < 13 + k → wval gs x r = true → wval gs y r = true) :
    wval gs x (13 + k) = true → wval gs y (13 + k) = true := by
  rcases hop with hop | hop
  · rw [wval_and gs x k hk hop, wval_and gs y k hk hop]
    intro hx r hr
    obtain ⟨hlt, hrx⟩ := hx r hr
    exact ⟨hlt, h r hr hlt hrx⟩
  · rw [wval_or gs x k hk hop, wval_or gs y k hk hop]
    rintro ⟨r, hr, hlt, hrx⟩
    exact ⟨r, hr, hlt, h r hr hlt hrx⟩

private lemma wval_mono_lt (gs : List Gate) (j : Fin gs.length)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true) :
    ∀ w : ℕ, w < 13 + j.val → wval gs x w = true → wval gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hlt hxw
    by_cases hw13 : w < 13
    · let p : Fin 13 := ⟨w, hw13⟩
      change wval gs x p.val = true at hxw
      change wval gs y p.val = true
      rw [wval_input] at hxw ⊢
      exact hxy p hxw
    · have hk : w - 13 < gs.length := by omega
      have hwk : w = 13 + (w - 13) := by omega
      rw [hwk] at hxw ⊢
      have hne : (⟨w - 13, hk⟩ : Fin gs.length) ≠ j := by
        intro heq
        have hv := congrArg Fin.val heq
        simp at hv; omega
      have hop : gs[w - 13].op = GateOp.and ∨ gs[w - 13].op = GateOp.or := by
        rcases (hbasis _ (List.getElem_mem hk)).1 with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exfalso; exact hne (huniq ⟨w - 13, hk⟩ (by simpa using h3))
      exact wval_gate_mono gs (w - 13) hk hop x y (fun r _ hr => ih r (by omega) (by omega)) hxw

private lemma wval_mono_of_not_false (gs : List Gate) (j : Fin gs.length)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true)
    (hjfalse : wval gs x (13 + j.val) = false) :
    ∀ w : ℕ, wval gs x w = true → wval gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hxw
    by_cases hw13 : w < 13
    · let p : Fin 13 := ⟨w, hw13⟩
      change wval gs x p.val = true at hxw
      change wval gs y p.val = true
      rw [wval_input] at hxw ⊢
      exact hxy p hxw
    · by_cases hwlen : w < 13 + gs.length
      · have hk : w - 13 < gs.length := by omega
        have hwk : w = 13 + (w - 13) := by omega
        rw [hwk] at hxw ⊢
        by_cases hkj : w - 13 = j.val
        · rw [hkj, hjfalse] at hxw; cases hxw
        · have hne : (⟨w - 13, hk⟩ : Fin gs.length) ≠ j := fun heq => hkj (congrArg Fin.val heq)
          have hop : gs[w - 13].op = GateOp.and ∨ gs[w - 13].op = GateOp.or := by
            rcases (hbasis _ (List.getElem_mem hk)).1 with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr h2
            · exfalso; exact hne (huniq ⟨w - 13, hk⟩ (by simpa using h3))
          exact wval_gate_mono gs (w - 13) hk hop x y (fun r _ hr => ih r (by omega)) hxw
      · rw [wval_oob gs x w (by omega)] at hxw; cases hxw

-- Frontier lower bound for fan-in 2 OR gates
private def Sv (gs : List Gate) (l : Fin 13 → Fin 13 → Bool) (y : Fin 13 → Bool) (p : Fin 13) (w : ℕ) : Prop :=
  wval gs (l p) w = true ∧ wval gs y w = false

private def Multi (gs : List Gate) (T : Finset (Fin 13)) (l : Fin 13 → Fin 13 → Bool)
    (y : Fin 13 → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv gs l y p w ∧ Sv gs l y p' w

private lemma list_le2_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

private lemma step_cases (gs : List Gate) (T : Finset (Fin 13)) (l : Fin 13 → Fin 13 → Bool)
    (y : Fin 13 → Bool) (k : ℕ) (hk : k < gs.length)
    (hopk : gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or)
    (hfank : gs[k].inputs.length ≤ 2) (hm : Multi gs T l y (13 + k)) :
    (∃ r ∈ gs[k].inputs, r < 13 + k ∧ ∀ p ∈ T, Sv gs l y p (13 + k) → Sv gs l y p r) ∨
    (gs[k].op = GateOp.or ∧ gs[k].inputs.length = 2 ∧
      (∀ r ∈ gs[k].inputs, ∃ p ∈ T, wval gs (l p) r = true) ∧
      ∀ p ∈ T, Sv gs l y p (13 + k) → ∃ r ∈ gs[k].inputs, r < 13 + k ∧ Sv gs l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases hopk with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ gs[k].inputs, r < 13 + k ∧ wval gs y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((wval_and gs (l p0) k hk hop).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((wval_and gs (l p) k hk hop).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(wval_and gs y k hk hop).mpr hall] at hy
    cases hy
  · have hyall : ∀ r ∈ gs[k].inputs, r < 13 + k → wval gs y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : wval gs y (13 + k) = true :=
        (wval_or gs y k hk hop).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      cases h2
    have hsv : ∀ p ∈ T, Sv gs l y p (13 + k) →
        ∃ r ∈ gs[k].inputs, r < 13 + k ∧ wval gs (l p) r = true ∧ Sv gs l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (wval_or gs (l p) k hk hop).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_le2_cases gs[k].inputs hfank
      (fun r => ∃ p ∈ T, r < 13 + k ∧ wval gs (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

private lemma frontier_bound (gs : List Gate) (T : Finset (Fin 13)) (l : Fin 13 → Fin 13 → Bool)
    (y : Fin 13 → Bool)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hopM : ∀ k, ∀ hk : k < gs.length, Multi gs T l y (13 + k) →
      gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < gs.length, Multi gs T l y (13 + k) →
      gs[k].op = GateOp.or → gs[k].inputs.length = 2 →
      (∀ r ∈ gs[k].inputs, ∃ p ∈ T, wval gs (l p) r = true) → 13 + k ∈ W)
    (hlen : ∀ w, Multi gs T l y w → 13 ≤ w ∧ w < 13 + gs.length)
    (bound : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi gs T l y w → w < bound)
    (hs : ∀ p ∈ T, ∃ w ∈ F, Sv gs l y p w) :
    T.card ≤ F.card + (W.filter (· < bound)).card := by
  classical
  induction bound generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi gs T l y (f p) :=
        ⟨p, hp, p', hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ b ih =>
    have hle : (W.filter (· < b)).card ≤ (W.filter (· < b + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : b ∈ F ∧ Multi gs T l y b
    · obtain ⟨h1, h2⟩ := hlen b hex.2
      have hk : b - 13 < gs.length := by omega
      have hbk : b = 13 + (b - 13) := by omega
      have hm : Multi gs T l y (13 + (b - 13)) := by rw [← hbk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases gs T l y (b - 13) hk (hopM _ hk hm) (hfan _ (List.getElem_mem hk)) hm with
        ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← hbk] at hlt hall
        let F' := insert r (F.erase b)
        have hF' : ∀ w ∈ F', Multi gs T l y w → w < b := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt' := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T, ∃ w ∈ F', Sv gs l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases hwb : w = b
          · subst hwb
            exact ⟨r, Finset.mem_insert_self _ _, hall p hp hsvp⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwb, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase b)
        change F'.card ≤ _ at hu
        omega
      · rw [← hbk] at hsv
        have hbW : b ∈ W := by
          have := hW (b - 13) hk hm hop hlen2 hQ
          rwa [← hbk] at this
        let P : Finset ℕ := (gs[b - 13].inputs.filter (· < b)).toFinset
        have hPcard : P.card ≤ 2 := by
          have hP1 := List.toFinset_card_le (gs[b - 13].inputs.filter (· < b))
          have hP2 := List.length_filter_le (fun r => decide (r < b)) gs[b - 13].inputs
          change P.card ≤ _ at hP1
          omega
        let F' := F.erase b ∪ P
        have hF' : ∀ w ∈ F', Multi gs T l y w → w < b := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt' := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have hmem := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using hmem
        have hs' : ∀ p ∈ T, ∃ w ∈ F', Sv gs l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases hwb : w = b
          · subst hwb
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p hp hsvp
            refine ⟨r, Finset.mem_union_right _ ?_, hsr⟩
            exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwb, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase b) P
        change F'.card ≤ _ at hu
        have hWinc : (W.filter (· < b)).card + 1 ≤ (W.filter (· < b + 1)).card := by
          have hsub : insert b (W.filter (· < b)) ⊆ W.filter (· < b + 1) := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Finset.mem_filter.mpr ⟨hbW, by omega⟩
            · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
          have hnot : b ∉ W.filter (· < b) := by simp
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hnot] at hcard
          exact hcard
        omega
    · have hF' : ∀ w ∈ F, Multi gs T l y w → w < b := by
        intro w hw hg
        have hne : w ≠ b := by intro hwb; subst hwb; exact hex ⟨hw, hg⟩
        have hlt := hF w hw hg
        omega
      have hi := ih F hF' hs
      omega

-- Combinatorics of PG(2, 3) on Fin 13
private def line13 (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

private lemma line13_card : ∀ t : Fin 13, (line13 t).card = 4 := by decide

private lemma line13_inter_card : ∀ t1 t2 : Fin 13, t1 ≠ t2 → (line13 t1 ∩ line13 t2).card = 1 := by decide

private lemma line13_not_mem_count : ∀ t0 : Fin 13, (Finset.univ.filter (fun t : Fin 13 => t0 ∉ line13 t)).card = 9 := by decide

private lemma line13_mem_count : ∀ t0 : Fin 13, (Finset.univ.filter (fun t : Fin 13 => t0 ∈ line13 t)).card = 4 := by decide

private lemma line13_ne_exists : ∀ t1 t2 : Fin 13, t1 ≠ t2 → ∃ v : Fin 13, v ∈ line13 t1 ∧ v ∉ line13 t2 := by decide

private lemma line13_two_pts : ∀ t : Fin 13, ∀ v : Fin 13, ∃ u : Fin 13, u ∈ line13 t ∧ u ≠ v := by decide

-- Main proof
private lemma main_proof :
    ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ t0 : Fin 13,
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t0))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      29 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 4 I.card ≤ gates.length := by
  classical
  intro L hL gates o j h hbasis hjnot huniq hhj hjins heval hcoline t0 ht0 I hI
  have hLeq : L = line13 := funext hL
  subst hLeq
  let e1 : Fin 13 → Fin 13 → Bool := fun p v => decide (v = p)
  let lp : Fin 13 → Fin 13 → Bool := fun p v => decide (v = t0 ∨ v = p)
  let col : Fin 13 → Fin 13 → Bool := fun t v => decide (v ∉ line13 t)
  have hval_j (x : Fin 13 → Bool) : wval gates x (13 + j.val) = !(wval gates x (13 + h.val)) :=
    wval_not_cons gates x j h hjnot hhj hjins
  have hh_t0 : wval gates (e1 t0) (13 + h.val) = true := ht0
  have hh_of_t0 : ∀ x : Fin 13 → Bool, x t0 = true → wval gates x (13 + h.val) = true := by
    intro x hxt0
    refine wval_mono_lt gates j hbasis huniq (e1 t0) x ?_ (13 + h.val) (by have : h.val < j.val := hhj; omega) hh_t0
    intro v hv
    simp only [e1, decide_eq_true_eq] at hv
    subst hv; exact hxt0
  have hj_of_t0 : ∀ x : Fin 13 → Bool, x t0 = true → wval gates x (13 + j.val) = false := by
    intro x hxt0
    rw [hval_j, hh_of_t0 x hxt0]; rfl
  have hh_col (t : Fin 13) : wval gates (col t) (13 + h.val) = true := hcoline t
  -- Define W_t for each line t not through t0
  let Wt (t : Fin 13) : Finset (Fin gates.length) :=
    Finset.univ.filter fun g : Fin gates.length =>
      (gates.get g).op = GateOp.or ∧ (gates.get g).inputs.length = 2 ∧
      Multi gates (line13 t) lp (col t) (13 + g.val) ∧
      ∀ r ∈ (gates.get g).inputs, ∃ p ∈ line13 t, wval gates (lp p) r = true
  let offT : Finset (Fin 13) := Finset.univ.filter (fun t : Fin 13 => t0 ∉ line13 t)
  let onT : Finset (Fin 13) := Finset.univ.filter (fun t : Fin 13 => t0 ∈ line13 t)
  have hWt_card : ∀ t ∈ offT, 3 ≤ (Wt t).card := by
    intro t ht
    have ht0_not : t0 ∉ line13 t := (Finset.mem_filter.mp ht).2
    let Wnat : Finset ℕ := (Wt t).image (fun g : Fin gates.length => 13 + g.val)
    have hhopM : ∀ k, ∀ hk : k < gates.length, Multi gates (line13 t) lp (col t) (13 + k) →
        gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or := by
      intro k hk hm
      rcases (hbasis _ (List.getElem_mem hk)).1 with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exfalso
        have hkj : (⟨k, hk⟩ : Fin gates.length) = j := huniq ⟨k, hk⟩ (by simpa using h3)
        have hkv : k = j.val := congrArg Fin.val hkj
        obtain ⟨p, _, _, _, _, ⟨hp1, _⟩, _⟩ := hm
        rw [hkv, hj_of_t0 (lp p) (by simp [lp])] at hp1
        cases hp1
    have hWmem : ∀ k, ∀ hk : k < gates.length, Multi gates (line13 t) lp (col t) (13 + k) →
        gates[k].op = GateOp.or → gates[k].inputs.length = 2 →
        (∀ r ∈ gates[k].inputs, ∃ p ∈ line13 t, wval gates (lp p) r = true) → 13 + k ∈ Wnat := by
      intro k hk hm hop hlen2 hQ
      refine Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, hm, ?_⟩, rfl⟩
      · simpa using hop
      · simpa using hlen2
      · simpa using hQ
    have hlenM : ∀ w, Multi gates (line13 t) lp (col t) w → 13 ≤ w ∧ w < 13 + gates.length := by
      intro w hm
      obtain ⟨p1, hp1, p2, hp2, hne, ⟨h1t, h1f⟩, ⟨h2t, _⟩⟩ := hm
      constructor
      · by_contra hlt
        push_neg at hlt
        let v : Fin 13 := ⟨w, hlt⟩
        have hvf : col t v = false := by rw [← wval_input gates (col t) v]; exact h1f
        have hvL : v ∈ line13 t := by simpa [col] using hvf
        have hv1 : lp p1 v = true := by rw [← wval_input gates (lp p1) v]; exact h1t
        have hv2 : lp p2 v = true := by rw [← wval_input gates (lp p2) v]; exact h2t
        simp only [lp, decide_eq_true_eq] at hv1 hv2
        have hvp1 : v = p1 := hv1.resolve_left (fun h => ht0_not (h ▸ hvL))
        have hvp2 : v = p2 := hv2.resolve_left (fun h => ht0_not (h ▸ hvL))
        exact hne (hvp1.symm.trans hvp2)
      · by_contra hge
        push_neg at hge
        rw [wval_oob gates (lp p1) w hge] at h1t
        cases h1t
    have hsF : ∀ p ∈ line13 t, ∃ w ∈ ({o t} : Finset ℕ), Sv gates lp (col t) p w := by
      intro p hp
      refine ⟨o t, Finset.mem_singleton_self _, ?_, ?_⟩
      · rw [← eval_eq_wval, heval t (lp p)]
        simp only [decide_eq_true_eq]
        exact ⟨p, hp, by simp [lp]⟩
      · rw [← eval_eq_wval, heval t (col t)]
        simp [col]
    have hfb := frontier_bound gates (line13 t) lp (col t) (fun g hg => (hbasis g hg).2)
      hhopM Wnat hWmem hlenM (13 + gates.length) {o t}
      (fun w hw hm => (hlenM w hm).2) hsF
    have hcard_lt : (Wnat.filter (· < 13 + gates.length)).card ≤ (Wt t).card := by
      calc (Wnat.filter (· < 13 + gates.length)).card
          ≤ Wnat.card := Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ (Wt t).card := Finset.card_image_le
    have hL4 : (line13 t).card = 4 := line13_card t
    have hF1 : ({o t} : Finset ℕ).card = 1 := Finset.card_singleton _
    omega
  -- Pairwise disjointness of Wt across offT
  have hWt_disj : Set.PairwiseDisjoint (offT : Set (Fin 13)) Wt := by
    intro t1 ht1 t2 ht2 hne
    change Disjoint (Wt t1) (Wt t2)
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have ht1_not : t0 ∉ line13 t1 := (Finset.mem_filter.mp ht1).2
    have ht2_not : t0 ∉ line13 t2 := (Finset.mem_filter.mp ht2).2
    obtain ⟨p1, hp1, p2, hp2, hpne, ⟨h1t, _⟩, ⟨h2t, _⟩⟩ := (Finset.mem_filter.mp hg1).2.2.2.1
    obtain ⟨_, _, _, _, _, ⟨_, hg2f⟩, _⟩ := (Finset.mem_filter.mp hg2).2.2.2.1
    have hinter := line13_inter_card t1 t2 hne
    have hex_out : ∃ p ∈ line13 t1, p ∉ line13 t2 ∧ wval gates (lp p) (13 + g.val) = true := by
      by_cases h1 : p1 ∈ line13 t2
      · by_cases h2 : p2 ∈ line13 t2
        · have hsub : ({p1, p2} : Finset (Fin 13)) ⊆ line13 t1 ∩ line13 t2 := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hp1, h1⟩
            · exact Finset.mem_inter.mpr ⟨hp2, h2⟩
          have h2le : 2 ≤ (line13 t1 ∩ line13 t2).card := by
            have hc := Finset.card_le_card hsub
            rw [Finset.card_pair hpne] at hc
            exact hc
          omega
        · exact ⟨p2, hp2, h2, h2t⟩
      · exact ⟨p1, hp1, h1, h1t⟩
    obtain ⟨p, _, hp_not2, hgp⟩ := hex_out
    have hle_in : ∀ v : Fin 13, lp p v = true → col t2 v = true := by
      intro v hv
      simp only [lp, decide_eq_true_eq] at hv
      simp only [col, decide_eq_true_eq]
      rcases hv with rfl | rfl
      · exact ht2_not
      · exact hp_not2
    have hg2t := wval_mono_of_not_false gates j hbasis huniq (lp p) (col t2) hle_in
      (hj_of_t0 (lp p) (by simp [lp])) (13 + g.val) hgp
    rw [hg2t] at hg2f
    cases hg2f
  let W9 : Finset (Fin gates.length) := offT.biUnion Wt
  have hW9_card : 27 ≤ W9.card := by
    rw [Finset.card_biUnion hWt_disj]
    calc 27 = 9 * 3 := by decide
      _ = offT.card * 3 := by rw [line13_not_mem_count t0]
      _ = ∑ _t ∈ offT, 3 := by simp
      _ ≤ ∑ t ∈ offT, (Wt t).card := Finset.sum_le_sum hWt_card
  let K : Finset (Fin gates.length) :=
    Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)
  -- Key properties of W9
  have hW9_or : ∀ g ∈ W9, (gates.get g).op = GateOp.or := by
    intro g hg
    obtain ⟨t, _, hgt⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hgt).2.1
  have hW9_not_h : h ∉ W9 := by
    intro hhW
    obtain ⟨t, _, hht⟩ := Finset.mem_biUnion.mp hhW
    obtain ⟨_, _, _, _, _, ⟨_, hf⟩, _⟩ := (Finset.mem_filter.mp hht).2.2.2.1
    rw [hh_col t] at hf
    cases hf
  have hW9_not_j : j ∉ W9 := by
    intro hjW
    have := hW9_or j hjW
    rw [hjnot] at this
    cases this
  have hW9_disj_K : Disjoint W9 K := by
    rw [Finset.disjoint_left]
    intro g hgW hgK
    obtain ⟨t, _, hgt⟩ := Finset.mem_biUnion.mp hgW
    have hreads : 13 + j.val ∈ (gates.get g).inputs := (Finset.mem_filter.mp hgK).2.2
    obtain ⟨p, _, hjp⟩ := (Finset.mem_filter.mp hgt).2.2.2.2 (13 + j.val) hreads
    rw [hj_of_t0 (lp p) (by simp [lp])] at hjp
    cases hjp
  have hW9_t0_false : ∀ g ∈ W9, wval gates (e1 t0) (13 + g.val) = false := by
    intro g hgW
    obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.mp hgW
    have ht0_not : t0 ∉ line13 t := (Finset.mem_filter.mp ht).2
    obtain ⟨_, _, _, _, _, ⟨_, hgf⟩, _⟩ := (Finset.mem_filter.mp hgt).2.2.2.1
    by_contra htrue
    have hgt0 : wval gates (e1 t0) (13 + g.val) = true := by simpa using htrue
    have hle : ∀ v : Fin 13, e1 t0 v = true → col t v = true := by
      intro v hv
      simp only [e1, decide_eq_true_eq] at hv
      subst hv
      simp [col, ht0_not]
    have hcolt := wval_mono_of_not_false gates j hbasis huniq (e1 t0) (col t) hle
      (hj_of_t0 (e1 t0) (by simp [e1])) (13 + g.val) hgt0
    rw [hcolt] at hgf
    cases hgf
  have hh_ne_j : h ≠ j := ne_of_lt hhj
  have hh_not_K : h ∉ K := by
    intro hK
    have hjh : j < h := (Finset.mem_filter.mp hK).2.1
    exact lt_asymm hhj hjh
  have hj_not_K : j ∉ K := by
    intro hK
    exact lt_irrefl j (Finset.mem_filter.mp hK).2.1
  let base : Finset (Fin gates.length) := insert h (insert j (W9 ∪ K))
  have hbase_card : 29 + K.card ≤ base.card := by
    have h1 : (W9 ∪ K).card = W9.card + K.card := Finset.card_union_of_disjoint hW9_disj_K
    have hj_not : j ∉ W9 ∪ K := by simp [hW9_not_j, hj_not_K]
    have hh_not : h ∉ insert j (W9 ∪ K) := by simp [hh_ne_j, hW9_not_h, hh_not_K]
    rw [Finset.card_insert_of_notMem hh_not, Finset.card_insert_of_notMem hj_not, h1]
    omega
  -- Bound 1: 29 + K.card + I.card <= gates.length
  have hbound1 : 29 + K.card + I.card ≤ gates.length := by
    have hdisj : Disjoint base I := by
      rw [Finset.disjoint_right]
      intro g hgI hgB
      have hglth : g < h := by
        let Tlt : Finset (Fin gates.length) := Finset.univ.filter (fun i => i < h)
        have hmem := (hI g hgI).2 Tlt (fun i g' hi _ hgi => by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases hi with rfl | hiT
          · exact hgi
          · exact lt_trans hgi (Finset.mem_filter.mp hiT).2)
        exact (Finset.mem_filter.mp hmem).2
      simp only [base, Finset.mem_insert, Finset.mem_union] at hgB
      rcases hgB with rfl | rfl | hgW | hgK
      · exact lt_irrefl g hglth
      · exact lt_asymm hglth hhj
      · have hor := hW9_or g hgW
        have hand := (hI g hgI).1
        rw [hor] at hand; cases hand
      · have hjg : j < g := (Finset.mem_filter.mp hgK).2.1
        exact lt_asymm (lt_trans hglth hhj) hjg
    have hcard := Finset.card_union_of_disjoint hdisj
    have hle : (base ∪ I).card ≤ gates.length := by
      simpa using Finset.card_le_univ (base ∪ I)
    omega
  -- Bound 2: 29 + K.card + 4 <= gates.length
  have hbound2 : 29 + K.card + 4 ≤ gates.length := by
    let computes (t : Fin 13) (g : Fin gates.length) : Prop :=
      ∀ x : Fin 13 → Bool, wval gates x (13 + g.val) = decide (∃ v ∈ line13 t, x v = true)
    have hwire_not_in : ∀ (t : Fin 13) (w : ℕ),
        (∀ x : Fin 13 → Bool, wval gates x w = decide (∃ v ∈ line13 t, x v = true)) →
        13 ≤ w ∧ w < 13 + gates.length := by
      intro t w hcomp
      constructor
      · by_contra hlt
        push_neg at hlt
        let v : Fin 13 := ⟨w, hlt⟩
        obtain ⟨u, huL, huv⟩ := line13_two_pts t v
        have h1 := hcomp (e1 u)
        have h2 : wval gates (e1 u) v.val = false := by
          rw [wval_input]; simp [e1, huv.symm]
        have h3 : decide (∃ p ∈ line13 t, e1 u p = true) = true := by
          simp only [decide_eq_true_eq]
          exact ⟨u, huL, by simp [e1]⟩
        change wval gates (e1 u) v.val = _ at h1
        rw [h2, h3] at h1
        cases h1
      · by_contra hge
        push_neg at hge
        obtain ⟨u, huL, _⟩ := line13_two_pts t t0
        have h1 := hcomp (e1 u)
        rw [wval_oob gates (e1 u) w hge] at h1
        have h3 : decide (∃ p ∈ line13 t, e1 u p = true) = true := by
          simp only [decide_eq_true_eq]
          exact ⟨u, huL, by simp [e1]⟩
        rw [h3] at h1
        cases h1
    have hex_gate : ∀ t : Fin 13, ∃ g : Fin gates.length, computes t g := by
      intro t
      have hcomp : ∀ x : Fin 13 → Bool, wval gates x (o t) = decide (∃ v ∈ line13 t, x v = true) :=
        fun x => by rw [← eval_eq_wval]; exact heval t x
      obtain ⟨h1, h2⟩ := hwire_not_in t (o t) hcomp
      refine ⟨⟨o t - 13, by omega⟩, fun x => ?_⟩
      have heq : 13 + (o t - 13) = o t := by omega
      simpa [heq] using hcomp x
    -- Pick the minimum gate computing each line t in onT
    have hmin_gate : ∀ t ∈ onT, ∃ g : Fin gates.length, computes t g ∧ g ∉ base := by
      intro t ht
      have ht0L : t0 ∈ line13 t := (Finset.mem_filter.mp ht).2
      let S : Finset (Fin gates.length) := Finset.univ.filter (fun g => computes t g)
      have hSne : S.Nonempty := by
        obtain ⟨g, hg⟩ := hex_gate t
        exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩⟩
      let g := S.min' hSne
      have hg_mem : g ∈ S := Finset.min'_mem S hSne
      have hg_comp : computes t g := (Finset.mem_filter.mp hg_mem).2
      have hg_min : ∀ g' : Fin gates.length, computes t g' → g ≤ g' := fun g' hg' =>
        Finset.min'_le S g' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg'⟩)
      refine ⟨g, hg_comp, ?_⟩
      intro hgB
      simp only [base, Finset.mem_insert, Finset.mem_union] at hgB
      rcases hgB with rfl | rfl | hgW | hgK
      · have h1 := hg_comp (col t)
        rw [hh_col t] at h1
        have h2 : decide (∃ v ∈ line13 t, col t v = true) = false := by simp [col]
        rw [h2] at h1; cases h1
      · have h1 := hg_comp (e1 t0)
        rw [hj_of_t0 (e1 t0) (by simp [e1])] at h1
        have h2 : decide (∃ v ∈ line13 t, e1 t0 v = true) = true := by
          simp only [decide_eq_true_eq]
          exact ⟨t0, ht0L, by simp [e1]⟩
        rw [h2] at h1; cases h1
      · have h1 := hg_comp (e1 t0)
        rw [hW9_t0_false g hgW] at h1
        have h2 : decide (∃ v ∈ line13 t, e1 t0 v = true) = true := by
          simp only [decide_eq_true_eq]
          exact ⟨t0, ht0L, by simp [e1]⟩
        rw [h2] at h1; cases h1
      · have hjg : j < g := (Finset.mem_filter.mp hgK).2.1
        have hreads : 13 + j.val ∈ (gates.get g).inputs := (Finset.mem_filter.mp hgK).2.2
        have hreads' : 13 + j.val ∈ gates[g.val].inputs := by simpa using hreads
        have hne : g ≠ j := ne_of_gt hjg
        have hlt_jg : 13 + j.val < 13 + g.val := by
          have : j.val < g.val := hjg
          omega
        rcases (hbasis _ (List.getElem_mem g.isLt)).1 with hand | hor | hnot
        · have ht0_true : wval gates (e1 t0) (13 + g.val) = true := by
            rw [hg_comp (e1 t0)]
            simp only [decide_eq_true_eq]
            exact ⟨t0, ht0L, by simp [e1]⟩
          have hjt := ((wval_and gates (e1 t0) g.val g.isLt hand).mp ht0_true (13 + j.val) hreads').2
          rw [hj_of_t0 (e1 t0) (by simp [e1])] at hjt
          cases hjt
        · -- Gate g is an OR gate reading 13 + j; check input all-false
          let z0 : Fin 13 → Bool := fun _ => false
          have hz0_false : wval gates z0 (13 + g.val) = false := by
            rw [hg_comp z0]; simp [z0]
          have hj_z0 : wval gates z0 (13 + j.val) = false := by
            by_contra hjt
            have hjt' : wval gates z0 (13 + j.val) = true := by simpa using hjt
            have hgt := (wval_or gates z0 g.val g.isLt hor).mpr ⟨13 + j.val, hreads', hlt_jg, hjt'⟩
            rw [hz0_false] at hgt; cases hgt
          have hh_z0 : wval gates z0 (13 + h.val) = true := by
            rw [hval_j z0] at hj_z0
            cases hhv : wval gates z0 (13 + h.val) <;> simp [hhv] at hj_z0 ⊢
          have hj_always_false : ∀ x : Fin 13 → Bool, wval gates x (13 + j.val) = false := by
            intro x
            rw [hval_j x]
            have hhx := wval_mono_lt gates j hbasis huniq z0 x (fun v hv => by simp [z0] at hv)
              (13 + h.val) (by have : h.val < j.val := hhj; omega) hh_z0
            rw [hhx]; rfl
          -- Since gates[g].inputs has length <= 2 and contains 13 + j (which is always false),
          -- examine the input list of gates[g]
          have hlen2 := (hbasis _ (List.getElem_mem g.isLt)).2
          have hex_other : ∃ w, w < 13 + g.val ∧ ∀ x : Fin 13 → Bool, wval gates x w = wval gates x (13 + g.val) := by
            rcases hins : gates[g.val].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
            · rw [hins] at hreads'; simp at hreads'
            · rw [hins] at hreads'
              have ha : a = 13 + j.val := (List.mem_singleton.mp hreads').symm
              subst ha
              have ht0_true : wval gates (e1 t0) (13 + g.val) = true := by
                rw [hg_comp (e1 t0)]; simp only [decide_eq_true_eq]; exact ⟨t0, ht0L, by simp [e1]⟩
              obtain ⟨r, hr, _, hrt⟩ := (wval_or gates (e1 t0) g.val g.isLt hor).mp ht0_true
              rw [hins] at hr
              have hreq : r = 13 + j.val := by simpa using hr
              rw [hreq, hj_always_false] at hrt; cases hrt
            · rw [hins] at hreads'
              have hpair : 13 + j.val = a ∨ 13 + j.val = b := by simpa using hreads'
              rcases hpair with rfl | rfl
              · by_cases hblt : b < 13 + g.val
                · refine ⟨b, hblt, fun x => ?_⟩
                  rw [wval_gate gates x g.val g.isLt, hor, hins]
                  simp [GateOp.eval, hlt_jg, hblt, hj_always_false x]
                · have ht0_true : wval gates (e1 t0) (13 + g.val) = true := by
                    rw [hg_comp (e1 t0)]; simp only [decide_eq_true_eq]; exact ⟨t0, ht0L, by simp [e1]⟩
                  rw [wval_gate gates (e1 t0) g.val g.isLt, hor, hins] at ht0_true
                  simp [GateOp.eval, hlt_jg, hblt, hj_always_false (e1 t0)] at ht0_true
              · by_cases halt : a < 13 + g.val
                · refine ⟨a, halt, fun x => ?_⟩
                  rw [wval_gate gates x g.val g.isLt, hor, hins]
                  simp [GateOp.eval, hlt_jg, halt, hj_always_false x]
                · have ht0_true : wval gates (e1 t0) (13 + g.val) = true := by
                    rw [hg_comp (e1 t0)]; simp only [decide_eq_true_eq]; exact ⟨t0, ht0L, by simp [e1]⟩
                  rw [wval_gate gates (e1 t0) g.val g.isLt, hor, hins] at ht0_true
                  simp [GateOp.eval, hlt_jg, halt, hj_always_false (e1 t0)] at ht0_true
            · rw [hins] at hlen2; simp at hlen2
          obtain ⟨w, hwlt, hweq⟩ := hex_other
          have hwcomp : ∀ x : Fin 13 → Bool, wval gates x w = decide (∃ v ∈ line13 t, x v = true) :=
            fun x => (hweq x).trans (hg_comp x)
          obtain ⟨hw13, _⟩ := hwire_not_in t w hwcomp
          let g' : Fin gates.length := ⟨w - 13, by omega⟩
          have hg'_comp : computes t g' := fun x => by
            have heq : 13 + g'.val = w := by simp [g']; omega
            rw [heq]; exact hwcomp x
          have hgle : g ≤ g' := hg_min g' hg'_comp
          have : g.val ≤ g'.val := hgle
          simp [g'] at this
          omega
        · exact hne (huniq g (by simpa using hnot))
    choose f hf_comp hf_notB using hmin_gate
    have hfinj : Set.InjOn (fun x : {t // t ∈ onT} => f x.1 x.2) (onT.attach : Set {t // t ∈ onT}) := by
      intro x _ y _ heq
      apply Subtype.ext
      by_contra hne
      obtain ⟨v, hv1, hv2⟩ := line13_ne_exists x.1 y.1 hne
      have h1 := hf_comp x.1 x.2 (e1 v)
      have h2 := hf_comp y.1 y.2 (e1 v)
      dsimp only at heq
      rw [heq] at h1
      have hr1 : decide (∃ u ∈ line13 x.1, e1 v u = true) = true := by
        simp only [decide_eq_true_eq]; exact ⟨v, hv1, by simp [e1]⟩
      have hr2 : decide (∃ u ∈ line13 y.1, e1 v u = true) = false := by
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro u hu he
        simp only [e1, decide_eq_true_eq] at he
        subst he; exact hv2 hu
      rw [hr1] at h1; rw [hr2] at h2
      rw [h1] at h2; cases h2
    let G4 : Finset (Fin gates.length) := onT.attach.image (fun x => f x.1 x.2)
    have hG4_card : G4.card = 4 := by
      rw [Finset.card_image_of_injOn hfinj, Finset.card_attach, line13_mem_count t0]
    have hdisj : Disjoint base G4 := by
      rw [Finset.disjoint_right]
      intro g hgG4
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hgG4
      exact hf_notB x.1 x.2
    have hcard := Finset.card_union_of_disjoint hdisj
    have hle : (base ∪ G4).card ≤ gates.length := by
      simpa using Finset.card_le_univ (base ∪ G4)
    omega
  change 29 + K.card + max 4 I.card ≤ gates.length
  omega

end PEqualNP.Outside.L_meta_1519_aux

theorem PEqualNP.Outside.L_meta_1519 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ t : Fin 13,
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      29 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 4 I.card ≤ gates.length :=
  PEqualNP.Outside.L_meta_1519_aux.main_proof
