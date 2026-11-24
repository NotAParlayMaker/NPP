import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3087
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def rn (gs : List Gate) (w : List Bool) : List Bool := (Circuit.mk gs 0).wires w

theorem rn_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    rn (g :: gs) w = rn gs (w ++ [gv g w]) := rfl

theorem rn_app (gs hs : List Gate) (w : List Bool) : rn (gs ++ hs) w = rn hs (rn gs w) := by
  simp [rn, Circuit.wires, List.foldl_append]

theorem rn_len (gs : List Gate) (w : List Bool) : (rn gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [rn, Circuit.wires]
  | cons g gs ih => rw [rn_cons, ih, List.length_append, List.length_cons]; simp; omega

theorem rn_pres (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (rn gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [rn_cons, ih _ (by rw [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

def mp (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def okg (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem okg_mp (f : ℕ → ℕ) (g : Gate) (h : okg g) : okg (mp f g) :=
  ⟨h.1, by simpa [mp] using h.2⟩

theorem gv_congr (f : ℕ → ℕ) (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ eff g, w'.getD (f i) false = w.getD i false) : gv (mp f g) w' = gv g w := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | not =>
    cases ins with
    | nil => rfl
    | cons a t =>
      have ha := h a (by simp [eff])
      simpa [gv, mp, GateOp.eval] using ha
  | _ =>
    have e : (ins.map f).map (fun i => w'.getD i false) = ins.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i hi => h i (by simpa [eff] using hi))
    simp only [gv, mp, e]

def sh (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def RC (p N r : ℕ) (P : List Bool) (v : Bool) : Prop :=
  (r < p ∧ P.getD r false = v) ∨ (p + N ≤ r ∧ v = false)

theorem rc_get {p N r : ℕ} {P t : List Bool} {v : Bool} (hp : P.length = p) (ht : t.length ≤ N)
    (h : RC p N r P v) : (P ++ t).getD r false = v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [List.getD_append _ _ _ _ (by omega), h2]
  · rw [List.getD_eq_default _ _ (by rw [List.length_append]; omega), h2]

theorem pt (P t : List Bool) (v : Bool) (r i : ℕ)
    (h : i = P.length → (P ++ t).getD r false = v) :
    (P ++ t).getD (sh P.length r i) false = ((P ++ [v]) ++ t).getD i false := by
  unfold sh
  rcases Nat.lt_trichotomy i P.length with hi | hi | hi
  · rw [if_pos hi, List.getD_append _ _ _ _ hi, List.append_assoc, List.getD_append _ _ _ _ hi]
  · subst hi
    rw [if_neg (lt_irrefl _), if_pos rfl, h rfl, List.append_assoc,
      List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    rfl
  · rw [if_neg (by omega), if_neg (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    have e : i - P.length = (i - 1 - P.length) + 1 := by omega
    rw [e]
    rfl

theorem sim_run (f : ℕ → ℕ) (A A' : List Bool) (N : ℕ) (ok : Gate → Prop)
    (hs : ∀ t : List Bool, t.length ≤ N → ∀ g, ok g → ∀ i ∈ eff g,
      (A' ++ t).getD (f i) false = (A ++ t).getD i false) :
    ∀ (gs : List Gate) (t : List Bool), t.length + gs.length ≤ N → (∀ g ∈ gs, ok g) →
      ∃ u, u.length = gs.length ∧ rn gs (A ++ t) = A ++ (t ++ u) ∧
        rn (gs.map (mp f)) (A' ++ t) = A' ++ (t ++ u) := by
  intro gs
  induction gs with
  | nil =>
    intro t _ _
    exact ⟨[], rfl, by rw [List.append_nil]; rfl, by rw [List.append_nil]; rfl⟩
  | cons g gs ih =>
    intro t ht hok
    have ht' : t.length + (gs.length + 1) ≤ N := by simpa using ht
    have hv : gv (mp f g) (A' ++ t) = gv g (A ++ t) :=
      gv_congr f g _ _ (hs t (by omega) g (hok g (by simp)))
    obtain ⟨u, hu, h1, h2⟩ := ih (t ++ [gv g (A ++ t)])
      (by rw [List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    refine ⟨gv g (A ++ t) :: u, by simp [hu], ?_, ?_⟩
    · rw [rn_cons, List.append_assoc, h1, List.append_assoc]; rfl
    · rw [List.map_cons, rn_cons, hv, List.append_assoc, h2, List.append_assoc]; rfl


theorem del_eval (pre post : List Gate) (h : Gate) (a : List Bool) (r o : ℕ) (ha : a.length = 10)
    (hc : RC (10 + pre.length) post.length r (rn pre a) (gv h (rn pre a)) ∨
      ((∀ g ∈ post, (10 + pre.length) ∉ eff g) ∧ o ≠ 10 + pre.length)) :
    (rn (pre ++ post.map (mp (sh (10 + pre.length) r))) a).getD (sh (10 + pre.length) r o) false =
      (rn (pre ++ h :: post) a).getD o false := by
  have hP : (rn pre a).length = 10 + pre.length := by rw [rn_len, ha]
  rw [rn_app, rn_app, rn_cons, ← hP]
  obtain ⟨u, hu, h1, h2⟩ := sim_run (sh (rn pre a).length r) (rn pre a ++ [gv h (rn pre a)])
    (rn pre a) post.length
    (fun g => (rn pre a).length ∈ eff g →
      RC (10 + pre.length) post.length r (rn pre a) (gv h (rn pre a)))
    (fun t ht g hg i hi => pt _ _ _ _ _ (fun e => rc_get hP ht (hg (e ▸ hi))))
    post [] (by simp) (fun g hg hp => by
      rcases hc with hc | ⟨hd, _⟩
      · exact hc
      · exact absurd (hP ▸ hp) (hd g hg))
  rw [List.append_nil] at h1 h2
  rw [h1, h2, List.nil_append]
  exact pt _ _ _ _ _ (fun e => by
    rcases hc with hc | ⟨_, hne⟩
    · exact rc_get hP (by omega) hc
    · exact absurd (e.trans hP) hne)


theorem eff_sub (g : Gate) (i : ℕ) (hi : i ∈ eff g) : i ∈ g.inputs := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | not => exact List.mem_of_mem_take (by simpa [eff] using hi)
  | _ => simpa [eff] using hi

theorem eff_len (g : Gate) : (eff g).length ≤ g.inputs.length := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | not =>
    show (ins.take 1).length ≤ ins.length
    rw [List.length_take]
    exact Nat.min_le_right _ _
  | _ => exact le_refl _

def trim (g : Gate) : Gate := ⟨g.op, eff g⟩

theorem gv_trim (g : Gate) (w : List Bool) : gv (trim g) w = gv g w := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | not =>
    cases ins with
    | nil => rfl
    | cons a t => rfl
  | _ => rfl

theorem rn_map_congr (h : Gate → Gate) (hh : ∀ g w, gv (h g) w = gv g w) :
    ∀ (gs : List Gate) (w : List Bool), rn (gs.map h) w = rn gs w := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; rw [List.map_cons, rn_cons, rn_cons, hh, ih]

theorem clamp_get (l : List Bool) (th i : ℕ) (h : l.length ≤ th) :
    l.getD (min i th) false = l.getD i false := by
  rcases Nat.le_total i th with hi | hi
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right hi, List.getD_eq_default _ _ h, List.getD_eq_default _ _ (le_trans h hi)]

theorem norm_eval (gs : List Gate) (o : ℕ) (A : List Bool) (hA : A.length = 10) :
    (rn (gs.map (fun g => mp (fun i => min i (10 + gs.length)) (trim g))) A).getD
      (min o (10 + gs.length)) false = (rn gs A).getD o false := by
  obtain ⟨u, hu, h1, h2⟩ := sim_run (fun i => min i (10 + gs.length)) A A gs.length (fun _ => True)
    (fun t ht g _ i _ => clamp_get _ _ _ (by rw [List.length_append, hA]; omega))
    (gs.map trim) [] (by simp) (fun _ _ => trivial)
  rw [List.append_nil, List.nil_append] at h1 h2
  rw [List.map_map] at h2
  rw [rn_map_congr trim gv_trim] at h1
  have e : (fun g => mp (fun i => min i (10 + gs.length)) (trim g)) =
      (mp fun i => min i (10 + gs.length)) ∘ trim := rfl
  rw [e, h2, h1]
  exact clamp_get _ _ _ (by simp [hA, hu])

theorem agree_app (A A' t : List Bool) (k : ℕ) (hl : A'.length = A.length)
    (hag : ∀ j, j ≠ k → A'.getD j false = A.getD j false) (j : ℕ) (hj : j ≠ k) :
    (A' ++ t).getD j false = (A ++ t).getD j false := by
  rcases Nat.lt_or_ge j A.length with h | h
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact h), List.getD_append _ _ _ _ h]
    exact hag j hj
  · rw [List.getD_append_right _ _ _ _ (by rw [hl]; exact h), List.getD_append_right _ _ _ _ h, hl]

theorem mp_id : mp id = id := by
  funext g
  cases g
  simp [mp]

theorem indep (gs : List Gate) (k : ℕ) (hk : ∀ g ∈ gs, k ∉ g.inputs) (A A' : List Bool)
    (hl : A'.length = A.length) (hag : ∀ j, j ≠ k → A'.getD j false = A.getD j false)
    (j : ℕ) (hj : j ≠ k) : (rn gs A').getD j false = (rn gs A).getD j false := by
  obtain ⟨u, -, h1, h2⟩ := sim_run id A A' gs.length (fun g => k ∉ g.inputs)
    (fun t _ g hg i hi => agree_app A A' t k hl hag i (fun e => hg (e ▸ eff_sub g i hi)))
    gs [] (by simp) hk
  rw [List.append_nil, List.nil_append] at h1 h2
  rw [mp_id, List.map_id] at h2
  rw [h1, h2]
  exact agree_app A A' u k hl hag j hj

theorem ofFn_agree (x y : Fin 10 → Bool) (i : Fin 10) (h : ∀ j : Fin 10, j ≠ i → x j = y j) :
    ∀ j : ℕ, j ≠ i.val → (List.ofFn y).getD j false = (List.ofFn x).getD j false := by
  intro j hj
  rcases Nat.lt_or_ge j 10 with hlt | hge
  · interval_cases j
    · exact (h 0 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 1 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 2 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 3 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 4 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 5 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 6 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 7 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 8 (fun e => hj (congrArg Fin.val e))).symm
    · exact (h 9 (fun e => hj (congrArg Fin.val e))).symm
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem slot_ok (f : ℕ → ℕ) (g : Gate) (h : okg g) :
    (mp f (trim g)).inputs.length +
      (if ((mp f (trim g)).op.eval [false] && !(mp f (trim g)).op.eval [true]) = true
        then 1 else 0) ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := h
  have hlen' : ins.length ≤ 2 := hlen
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · have e : (mp f (trim ⟨GateOp.and, ins⟩)).inputs.length = ins.length := by
      show (ins.map f).length = ins.length
      rw [List.length_map]
    rw [e, if_neg (by simp [mp, trim, GateOp.eval])]
    omega
  · have e : (mp f (trim ⟨GateOp.or, ins⟩)).inputs.length = ins.length := by
      show (ins.map f).length = ins.length
      rw [List.length_map]
    rw [e, if_neg (by simp [mp, trim, GateOp.eval])]
    omega
  · have e : (mp f (trim ⟨GateOp.not, ins⟩)).inputs.length ≤ 1 := by
      show ((ins.take 1).map f).length ≤ 1
      rw [List.length_map, List.length_take]
      exact Nat.min_le_left _ _
    rw [if_pos (by simp [mp, trim, GateOp.eval])]
    omega

theorem slots (gs : List Gate)
    (h : ∀ g ∈ gs, g.inputs.length +
      (if (g.op.eval [false] && !g.op.eval [true]) = true then 1 else 0) ≤ 2) :
    (gs.flatMap Gate.inputs).length +
      (gs.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ih' := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    by_cases hc : (g.op.eval [false] && !g.op.eval [true]) = true
    · rw [if_pos hc] at hg
      rw [List.flatMap_cons, List.length_append, List.filter_cons_of_pos (by exact hc),
        List.length_cons, List.length_cons]
      omega
    · rw [if_neg hc] at hg
      rw [List.flatMap_cons, List.length_append, List.filter_cons_of_neg (by exact hc),
        List.length_cons]
      omega

theorem main (T : Circuit) (hf : FanInTwo T)
    (hdep : ∀ i : Fin 10, ∃ x y : Fin 10 → Bool, (∀ j : Fin 10, j ≠ i → x j = y j) ∧
      circuitFun 10 T x ≠ circuitFun 10 T y) :
    ∃ T' : Circuit, FanInTwo T' ∧ circuitFun 10 T' = circuitFun 10 T ∧ T'.size ≤ T.size ∧
      (T'.output ≤ 10 + T'.size ∧ ∀ g ∈ T'.gates, ∀ k ∈ g.inputs, k ≤ 10 + T'.size) ∧
      (∀ k < 10 + T'.size, k ∈ T'.output :: List.flatMap Gate.inputs T'.gates) ∧
      9 + (T'.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length +
        ∑ k ∈ Finset.range (10 + T'.size),
          (List.count k (T'.output :: List.flatMap Gate.inputs T'.gates) - 1) ≤ T'.size := by
  classical
  have hP : ∃ s, ∃ C : Circuit, FanInTwo C ∧ circuitFun 10 C = circuitFun 10 T ∧ C.size = s :=
    ⟨T.size, T, hf, rfl, rfl⟩
  obtain ⟨C, hCf, hCe, hCs⟩ := Nat.find_spec hP
  have hmin : ∀ D : Circuit, FanInTwo D → circuitFun 10 D = circuitFun 10 T → C.size ≤ D.size := by
    intro D hD hDe
    rw [hCs]
    exact Nat.find_min' hP ⟨D, hD, hDe, rfl⟩
  obtain ⟨gs, o⟩ := C
  have hgsf : ∀ g ∈ gs, okg g := hCf
  have hev : ∀ x : Fin 10 → Bool, (rn gs (List.ofFn x)).getD o false = circuitFun 10 T x :=
    fun x => congrFun hCe x
  obtain ⟨gs1, hgs1⟩ : ∃ l, l = gs.map (fun g => mp (fun i => min i (10 + gs.length)) (trim g)) :=
    ⟨_, rfl⟩
  obtain ⟨o1, ho1⟩ : ∃ k, k = min o (10 + gs.length) := ⟨_, rfl⟩
  have hlen1 : gs1.length = gs.length := by rw [hgs1, List.length_map]
  have hok1 : ∀ g ∈ gs1, okg g := by
    intro g hg
    rw [hgs1] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact okg_mp _ _ ⟨(hgsf g0 hg0).1, le_trans (eff_len g0) (hgsf g0 hg0).2⟩
  have hev1 : ∀ x : Fin 10 → Bool, (rn gs1 (List.ofFn x)).getD o1 false = circuitFun 10 T x := by
    intro x
    rw [hgs1, ho1, norm_eval gs o _ (by simp)]
    exact hev x
  have hb1 : ∀ g ∈ gs1, ∀ k ∈ g.inputs, k ≤ 10 + gs1.length := by
    intro g hg k hk
    rw [hgs1] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hk
    rw [hlen1]
    exact Nat.min_le_right _ _
  have hall : ∀ k < 10 + gs1.length, k ∈ o1 :: List.flatMap Gate.inputs gs1 := by
    intro k hk
    by_contra hnot
    have ho : o1 ≠ k := fun e => hnot (by rw [e]; simp)
    have hin : ∀ g ∈ gs1, k ∉ g.inputs := fun g hg hkg =>
      hnot (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hkg⟩))
    rcases Nat.lt_or_ge k 10 with hk10 | hk10
    · obtain ⟨x, y, hxy, hne⟩ := hdep ⟨k, hk10⟩
      apply hne
      rw [← hev1 x, ← hev1 y]
      exact (indep gs1 k hin (List.ofFn x) (List.ofFn y) (by simp)
        (ofFn_agree x y ⟨k, hk10⟩ hxy) o1 ho).symm
    · have hp : k - 10 < gs1.length := by omega
      have hdec : gs1 = gs1.take (k - 10) ++ gs1[k - 10] :: gs1.drop (k - 10 + 1) := by
        rw [← List.drop_eq_getElem_cons hp, List.take_append_drop]
      have hpre : (gs1.take (k - 10)).length = k - 10 := by
        rw [List.length_take]; omega
      have hsub : ∀ g, g ∈ gs1.take (k - 10) ∨ g ∈ gs1.drop (k - 10 + 1) → g ∈ gs1 := by
        intro g hg
        rcases hg with h | h
        · exact List.mem_of_mem_take h
        · exact List.mem_of_mem_drop h
      have hk' : 10 + (gs1.take (k - 10)).length = k := by rw [hpre]; omega
      have hD := hmin ⟨gs1.take (k - 10) ++
          (gs1.drop (k - 10 + 1)).map (mp (sh (10 + (gs1.take (k - 10)).length) 0)),
          sh (10 + (gs1.take (k - 10)).length) 0 o1⟩
        (by
          intro g hg
          rcases List.mem_append.mp hg with h | h
          · exact hok1 g (hsub g (Or.inl h))
          · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
            exact okg_mp _ _ (hok1 g0 (hsub g0 (Or.inr hg0))))
        (by
          funext x
          show (rn _ (List.ofFn x)).getD _ false = _
          rw [del_eval _ _ gs1[k - 10] (List.ofFn x) 0 o1 (by simp)
            (Or.inr ⟨fun g hg hkg => hin g (hsub g (Or.inr hg)) (hk' ▸ eff_sub g _ hkg),
              by rw [hk']; exact ho⟩), ← hdec]
          exact hev1 x)
      have hl : gs1.length =
          (gs1.take (k - 10)).length + (gs1.drop (k - 10 + 1)).length + 1 := by
        rw [List.length_take, List.length_drop]; omega
      have hD' : gs.length ≤ (gs1.take (k - 10)).length + (gs1.drop (k - 10 + 1)).length := by
        have h := hD
        simp only [Circuit.size, List.length_append, List.length_map] at h
        exact h
      omega
  have hslot : (gs1.flatMap Gate.inputs).length +
      (gs1.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length ≤ 2 * gs1.length := by
    apply slots
    intro g hg
    rw [hgs1] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact slot_ok _ g0 (hgsf g0 hg0)
  have hcount : ∀ k ∈ Finset.range (10 + gs1.length),
      1 ≤ List.count k (o1 :: List.flatMap Gate.inputs gs1) := by
    intro k hk
    exact List.count_pos_iff.mpr (hall k (Finset.mem_range.mp hk))
  have hsum1 : ∑ k ∈ Finset.range (10 + gs1.length),
      (List.count k (o1 :: List.flatMap Gate.inputs gs1) - 1) =
      ∑ k ∈ Finset.range (10 + gs1.length), List.count k (o1 :: List.flatMap Gate.inputs gs1) -
        (10 + gs1.length) := by
    rw [Finset.sum_tsub_distrib _ hcount]
    simp
  have hsum2 : ∑ k ∈ Finset.range (10 + gs1.length),
      List.count k (o1 :: List.flatMap Gate.inputs gs1) ≤
      (o1 :: List.flatMap Gate.inputs gs1).length := by
    rw [← List.sum_toFinset_count_eq_length (o1 :: List.flatMap Gate.inputs gs1)]
    apply Finset.sum_le_sum_of_subset
    intro k hk
    exact List.mem_toFinset.mpr (hall k (Finset.mem_range.mp hk))
  rw [List.length_cons] at hsum2
  have hsum3 : 10 + gs1.length ≤ ∑ k ∈ Finset.range (10 + gs1.length),
      List.count k (o1 :: List.flatMap Gate.inputs gs1) := by
    calc 10 + gs1.length = ∑ _k ∈ Finset.range (10 + gs1.length), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hcount
  refine ⟨⟨gs1, o1⟩, hok1, ?_, ?_, ⟨?_, hb1⟩, hall, ?_⟩
  · funext x
    exact hev1 x
  · show gs1.length ≤ T.size
    rw [hlen1]
    exact hmin T hf rfl
  · show o1 ≤ 10 + gs1.length
    rw [ho1, hlen1]
    exact Nat.min_le_right _ _
  · show 9 + (gs1.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length +
        ∑ k ∈ Finset.range (10 + gs1.length),
          (List.count k (o1 :: List.flatMap Gate.inputs gs1) - 1) ≤ gs1.length
    rw [hsum1]
    omega

end PEqualNP.Outside.L_meta_3087

theorem PEqualNP.Outside.L_meta_3087 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x4 ≠ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x5) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x4.size ≤ x1.size ∧ (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧ (∀ x5 < (10 : ℕ) + x4.size, x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧ (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length + ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size), (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ x4.size := 
  fun T hf hdep => PEqualNP.Outside.L_meta_3087.main T hf hdep
