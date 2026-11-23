import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282_aux

def mis : Fin 8 → Finset (Fin 6) :=
  ![{0,3}, {0,4}, {0,5}, {1,3}, {1,4}, {1,5}, {2,4}, {2,5}]

def hit (U V : Finset (Fin 6)) : Bool := decide (∃ p ∈ U, p ∈ V)

def hasEdge (U : Finset (Fin 6)) : Prop :=
  ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(2,3)] : List (ℕ × ℕ)) ∧ u ∈ U ∧ v ∈ U

theorem mis_false : ∀ i, ¬ hasEdge (mis i) := by unfold hasEdge; decide

theorem mis_union_true : ∀ i j, i ≠ j → hasEdge (mis i ∪ mis j) := by unfold hasEdge; decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem noBalanced (B F : Finset (Fin 6))
    (h : (Finset.univ.filter (fun i : Fin 8 => hit B (mis i))).card = 4) :
    ¬ (∀ i : Fin 8, hit B (mis i) = !(hit F (mis i))) := by
  have allPairs : ∀ B ∈ (Finset.univ : Finset (Finset (Fin 6))),
      ∀ F ∈ (Finset.univ : Finset (Finset (Fin 6))),
        (Finset.univ.filter (fun i : Fin 8 => hit B (mis i))).card = 4 →
        ¬ (∀ i : Fin 8, hit B (mis i) = !(hit F (mis i))) := by decide
  exact allPairs B (Finset.mem_univ _) F (Finset.mem_univ _) h

theorem first_conflict (B F : Finset (Fin 6)) (f : Fin 8 → Fin 3 → Bool)
    (balanced : (Finset.univ.filter (fun i : Fin 8 => f i 0 = true)).card = 4)
    (different : ∀ i, hit B (mis i) ≠ hit F (mis i))
    (selected : ∀ i, (if f i 0 then hit F (mis i) else hit B (mis i)) =
      (hit B (mis i) && hit F (mis i))) : False := by
  have vals (i : Fin 8) : hit B (mis i) = f i 0 ∧ hit B (mis i) = !(hit F (mis i)) := by
    have h := selected i
    have hn := different i
    cases a : hit B (mis i) <;> cases b : hit F (mis i) <;> cases c : f i 0 <;> simp_all
  apply noBalanced B F _ (fun i => (vals i).2)
  simpa only [fun i => (vals i).1] using balanced


open PEqualNP.CircuitLowerBounds
private def isAnd282 (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

private lemma isAnd282_iff (g : Gate) : isAnd282 g = true ↔ g.op = GateOp.and := by
  unfold isAnd282
  cases g.op <;> simp

private lemma and_length (gs : List Gate) (A : Finset ℕ) (size : A.card ≤ 3)
    (covered : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → j ∈ A) :
    (gs.filter isAnd282).length ≤ 3 := by
  let p := isAnd282
  let T := Finset.univ.filter (fun j : Fin gs.length => p (gs.get j))
  have eq : (gs.filter p).length = T.card := by
    rw [← List.countP_eq_length_filter]
    simpa only [List.ofFn_get] using List.countP_ofFn gs.get p
  have map : Set.MapsTo (fun j : Fin gs.length => j.val) (T : Set (Fin gs.length)) (A : Set ℕ) := by
    intro j hj
    apply covered j (gs.get j)
    · exact List.getElem?_eq_getElem j.isLt
    · exact (isAnd282_iff _).mp (Finset.mem_filter.mp hj).2
  exact eq ▸ (Finset.card_le_card_of_injOn Fin.val map Fin.val_injective.injOn).trans size

private lemma first_and (gs : List Gate) (existsAnd : ∃ g ∈ gs, g.op = GateOp.and) :
    ∃ pre g tail, gs = pre ++ g :: tail ∧ g.op = GateOp.and ∧
      ∀ h ∈ pre, h.op ≠ GateOp.and := by
  induction gs with
  | nil => simp at existsAnd
  | cons x xs ih =>
    by_cases hx : x.op = GateOp.and
    · exact ⟨[], x, xs, rfl, hx, by simp⟩
    · obtain ⟨g, hg, hop⟩ := existsAnd
      have hxs : g ∈ xs := (List.mem_cons.mp hg).resolve_left (fun eq => hx (eq ▸ hop))
      obtain ⟨pre, t, tail, heq, ht, hpre⟩ := ih ⟨g, hxs, hop⟩
      refine ⟨x :: pre, t, tail, ?_, ht, ?_⟩
      · rw [heq]; rfl
      · intro h hm
        rcases List.mem_cons.mp hm with rfl | hp
        · exact hx
        · exact hpre h hp

private lemma code_balance (pred : Fin 8 → (Fin 3 → Bool) → Prop)
    (existsCode : ∀ i, ∃ b, pred i b)
    (disjointCode : ∀ i j b, pred i b → pred j b → i = j) :
    ∃ f : Fin 8 → (Fin 3 → Bool),
      (∀ i b, pred i b ↔ f i = b) ∧
      ∀ j : Fin 3, (Finset.univ.filter (fun i : Fin 8 => f i j = true)).card = 4 := by
  classical
  choose f hf using existsCode
  have inj : Function.Injective f := by
    intro i j eq
    exact disjointCode i j (f j) (eq ▸ hf i) (hf j)
  have bij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨inj, by simp⟩
  refine ⟨f, ?_, ?_⟩
  · intro i b
    constructor
    · intro h
      obtain ⟨j, rfl⟩ := bij.surjective b
      rw [disjointCode i j _ h (hf j)]
    · rintro rfl
      exact hf i
  · intro j
    let T := Finset.univ.filter (fun i : Fin 8 => f i j = true)
    have image : T.image f = Finset.univ.filter (fun b : Fin 3 → Bool => b j = true) := by
      ext b
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, h, rfl⟩
        exact h
      · intro h
        obtain ⟨i, rfl⟩ := bij.surjective b
        exact ⟨i, h, rfl⟩
    change T.card = 4
    rw [← Finset.card_image_of_injective T inj, image]
    exact (by decide : ∀ k : Fin 3, (Finset.univ.filter (fun b : Fin 3 → Bool => b k = true)).card = 4) j

private def run (gs : List Gate) (xs : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) xs

private def charSet (S : Finset (Fin 6)) (p : Fin 6) := decide (p ∈ S)

private theorem prefix_run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    simpa [run, List.foldl_append, Nat.add_assoc] using congrArg Nat.succ ih

private theorem prefix_support (gs : List Gate) (h : ∀ g ∈ gs, g.op = GateOp.or) (i : ℕ) :
    ∃ T : Finset (Fin 6), ∀ S, (run gs (List.ofFn (charSet S))).getD i false = hit T S := by
  classical
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < 6
    · refine ⟨{⟨i,hi⟩}, fun S => ?_⟩
      interval_cases i <;> simp [run, charSet, hit]
    · refine ⟨∅, fun S => ?_⟩
      simp [run, hit, List.getD_eq_getElem?_getD, hi]
  | append_singleton gs g ih =>
    have prior := ih (fun a ha => h a (by simp [ha]))
    choose T hT using prior
    have hlen (S : Finset (Fin 6)) :
        (run gs (List.ofFn (charSet S))).length = 6 + gs.length := by
      simp [prefix_run_length]
    have snoc (S : Finset (Fin 6)) :
        run (gs ++ [g]) (List.ofFn (charSet S)) =
        run gs (List.ofFn (charSet S)) ++
          [g.op.eval (g.inputs.map fun k => (run gs (List.ofFn (charSet S))).getD k false)] := by
      simp [run, List.foldl_append]
    by_cases hi : i = 6 + gs.length
    · refine ⟨g.inputs.toFinset.biUnion T, fun S => ?_⟩
      rw [snoc, List.getD_eq_getElem?_getD, List.getElem?_append]
      simp only [hlen, hi, lt_self_iff_false, ite_false, Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some, h g (by simp), GateOp.eval]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_map, id_eq, hit, decide_eq_true_eq,
        Finset.mem_biUnion, List.mem_toFinset]
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, hv⟩
        rw [hT j S] at hv
        obtain ⟨p,hp,hps⟩ := (of_decide_eq_true hv : ∃ p ∈ T j, p ∈ S)
        exact ⟨p, ⟨j,hj,hp⟩,hps⟩
      · rintro ⟨p, ⟨j,hj,hp⟩,hps⟩
        exact ⟨_, ⟨j,hj,rfl⟩, (hT j S).trans (decide_eq_true ⟨p,hp,hps⟩)⟩
    · refine ⟨T i, fun S => ?_⟩
      rw [← hT i S, snoc]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hlen]
      split
      · rfl
      · rename_i hnot
        have hpos : 0 < i - (6 + gs.length) := by omega
        have hge : (run gs (List.ofFn (charSet S))).length ≤ i := by rw [hlen]; omega
        rw [List.getElem?_eq_none hge, List.getElem?_eq_none (by simp; omega)]

private def args (g : Gate) (w : List Bool) := g.inputs.map fun j => w.getD j false

private def step (g : Gate) (w : List Bool) := w ++ [g.op.eval (args g w)]

private def pick (b : Bool) : List Bool → Bool
  | [] => true
  | [a] => a
  | a :: c :: _ => if b then c else a


private def fits (bits : List Bool) : List Gate → List Bool → Prop
  | [], _ => True
  | g :: gs, w =>
    if isAnd282 g then
      (pick (bits.headD false) (args g w) = g.op.eval (args g w) ∧
        fits bits.tail gs (step g w))
    else fits bits gs (step g w)

private lemma pick_exists (xs : List Bool) (hlen : xs.length ≤ 2) :
    ∃ b, pick b xs = GateOp.and.eval xs := by
  cases xs with
  | nil => exact ⟨false, rfl⟩
  | cons a t =>
    cases t with
    | nil => exact ⟨false, by cases a <;> rfl⟩
    | cons c t =>
      have he : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
      subst t
      cases a <;> cases c <;> first | exact ⟨false,rfl⟩ | exact ⟨true,rfl⟩

private lemma fits_exists (gs : List Gate) (w : List Bool) (n : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hcount : (gs.filter isAnd282).length ≤ n) :
    ∃ bits : List Bool, bits.length = n ∧ fits bits gs w := by
  induction gs generalizing w n with
  | nil => exact ⟨List.replicate n false, by simp, trivial⟩
  | cons g gs ih =>
    have hgs : ∀ h ∈ gs, h.inputs.length ≤ 2 := fun h hh => hg h (by simp [hh])
    by_cases hop : isAnd282 g = true
    · have h' : (gs.filter isAnd282).length + 1 ≤ n := by
        simpa [List.filter_cons, hop] using hcount
      obtain ⟨l, hl, hfit⟩ := ih (step g w) (n-1) hgs (by omega)
      obtain ⟨b, hb⟩ := pick_exists (args g w) (by simpa [args] using hg g (by simp))
      refine ⟨b :: l, by simp [hl]; omega, ?_⟩
      have hgop : g.op = .and := by cases hh : g.op <;> simp_all [isAnd282]
      simpa [fits, hop, hgop, hb] using hfit
    · have h' : (gs.filter isAnd282).length ≤ n := by
        simpa [List.filter_cons, hop] using hcount
      obtain ⟨l, hl, hfit⟩ := ih (step g w) n hgs h'
      exact ⟨l, hl, by simpa [fits, hop] using hfit⟩

private def SubUnion (x y z : List Bool) : Prop :=
  x.length = z.length ∧ y.length = z.length ∧
    ∀ j, z.getD j false = true → x.getD j false = true ∨ y.getD j false = true

private lemma subUnion_snoc {x y z : List Bool} (hh : SubUnion x y z) {a b c : Bool}
    (hv : c = true → a = true ∨ b = true) : SubUnion (x ++ [a]) (y ++ [b]) (z ++ [c]) := by
  obtain ⟨hx, hy, hh⟩ := hh
  refine ⟨by simp [hx], by simp [hy], ?_⟩
  intro j
  by_cases hj : j < z.length
  · simpa only [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (hx.symm ▸ hj),
      List.getD_append _ _ _ _ (hy.symm ▸ hj)] using hh j
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hx, hy]
    cases j-z.length <;> simp_all

private lemma picked_subUnion (g : Gate) {x y z : List Bool} (hh : SubUnion x y z)
    (b : Bool) (h : GateOp.and.eval (args g z) = true) :
    pick b (args g x) = true ∨ pick b (args g y) = true := by
  rcases hInputs : g.inputs with _ | ⟨a,t⟩
  · simp [args, hInputs, pick]
  · cases t with
    | nil =>
      simpa [args, hInputs, pick] using hh.2.2 a (by simpa [args, hInputs, GateOp.eval] using h)
    | cons c t =>
      have htr : ∀ j ∈ g.inputs, z.getD j false = true := by
        simpa [args, GateOp.eval] using h
      cases b
      · simpa [args, hInputs, pick] using hh.2.2 a (htr a (by simp [hInputs]))
      · simpa [args, hInputs, pick] using hh.2.2 c (htr c (by simp [hInputs]))

private lemma fits_union (gs : List Gate) (bits x y z : List Bool)
    (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h1 : fits bits gs x) (h2 : fits bits gs y) (hh : SubUnion x y z) :
    SubUnion (run gs x) (run gs y) (run gs z) := by
  induction gs generalizing bits x y z with
  | nil => exact hh
  | cons g gs ih =>
    have hgs : ∀ h ∈ gs, h.op = .and ∨ h.op = .or := fun h hm => hg h (by simp [hm])
    change SubUnion (run gs (step g x)) (run gs (step g y)) (run gs (step g z))
    rcases hg g (by simp) with hop | hop
    · simp only [fits, isAnd282, hop, ite_true] at h1 h2
      apply ih _ _ _ _ hgs h1.2 h2.2
      apply subUnion_snoc hh
      intro ht
      rw [hop] at ht ⊢
      simpa only [h1.1, h2.1] using picked_subUnion g hh (bits.headD false) ht
    · simp only [fits, isAnd282, hop, Bool.false_eq_true, ite_false] at h1 h2
      apply ih _ _ _ _ hgs h1 h2
      apply subUnion_snoc hh
      simp only [hop, GateOp.eval, args, List.any_map, List.any_eq_true, Function.comp_apply,
        id_eq]
      rintro ⟨j,hj,hz⟩
      exact (hh.2.2 j hz).imp (fun hx => ⟨j,hj,hx⟩) (fun hy => ⟨j,hj,hy⟩)

private lemma fits_prefix (pre rest : List Gate) (w bits : List Bool)
    (hp : ∀ h ∈ pre, h.op = .or) :
    fits bits (pre ++ rest) w ↔ fits bits rest (run pre w) := by
  induction pre generalizing w with
  | nil => rfl
  | cons a t ih =>
    have ha := hp a (by simp)
    change fits bits (a :: (t ++ rest)) w ↔ fits bits rest (run t (step a w))
    simp only [fits, isAnd282, ha, Bool.false_eq_true, ite_false]
    exact ih _ (fun g hg => hp _ (by simp [hg]))

private lemma inputs_union (S T : Finset (Fin 6)) :
    SubUnion (List.ofFn (charSet S)) (List.ofFn (charSet T)) (List.ofFn (charSet (S ∪ T))) := by
  refine ⟨by simp, by simp, ?_⟩
  intro j
  by_cases hj : j < 6
  · have val (U : Finset (Fin 6)) : (List.ofFn (charSet U)).getD j false = charSet U ⟨j,hj⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    rw [val, val, val]
    simp [charSet]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
    simp

private lemma to_bits {n : ℕ} (l : List Bool) (h : l.length = n) : ∃ b : Fin n → Bool, List.ofFn b = l := by
  subst n
  exact ⟨l.get, List.ofFn_get _⟩

private lemma code_flip (b : Fin 3 → Bool) :
    ∃ b' : Fin 3 → Bool, b ≠ b' ∧ (List.ofFn b).tail = (List.ofFn b').tail := by
  let b' : Fin 3 → Bool := fun i => if i = 0 then !(b 0) else b i
  refine ⟨b', ?_, ?_⟩
  · intro heq
    have hz := congrFun heq 0
    change b 0 = !(b 0) at hz
    cases h : b 0 <;> simp [h] at hz
  · rfl

private lemma selected_unique (gs : List Gate) (g : Gate) (w : List Bool) (b : Fin 3 → Bool)
    (ha : g.op = .and) (hf : fits (List.ofFn b) (g :: gs) w)
    (hu : ∀ b' : Fin 3 → Bool, fits (List.ofFn b') (g :: gs) w → b = b') :
    pick false (args g w) ≠ pick true (args g w) := by
  intro heq
  obtain ⟨b', hne, htail⟩ := code_flip b
  apply hne
  apply hu
  have const (x y : Bool) : pick x (args g w) = pick y (args g w) := by
    cases x <;> cases y <;> first | rfl | exact heq | exact heq.symm
  simp only [fits, isAnd282, ha, ite_true] at hf ⊢
  exact ⟨(const _ _).trans hf.1, htail ▸ hf.2⟩

private lemma impossible (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (hc : (C.gates.filter isAnd282).length ≤ 3)
    (hev : ∀ T, C.eval (List.ofFn (charSet T)) = true ↔ hasEdge T) : False := by
  classical
  let x (i : Fin 8) := List.ofFn (charSet (mis i))
  let pred (i : Fin 8) (b : Fin 3 → Bool) := fits (List.ofFn b) C.gates (x i)
  have op : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := fun g h => (mono g h).1
  have lengthBound : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g h => (mono g h).2
  have ex (i : Fin 8) : ∃ b, pred i b := by
    obtain ⟨l, hl,hf⟩ := fits_exists C.gates (x i) 3 lengthBound hc
    obtain ⟨b, rfl⟩ := to_bits l hl
    exact ⟨b,hf⟩
  have dis (i j : Fin 8) (b) (hi : pred i b) (hj : pred j b) : i = j := by
    by_contra h
    have hsup := fits_union C.gates (List.ofFn b) _ _ _ op hi hj (inputs_union (mis i) (mis j))
    have hu := (hev _).mpr (mis_union_true i j h)
    rcases hsup.2.2 C.output hu with left | right
    · exact mis_false i ((hev _).mp left)
    · exact mis_false j ((hev _).mp right)
  obtain ⟨f, huniq, hbal⟩ := code_balance pred ex dis
  by_cases he : ∃ g ∈ C.gates, g.op = .and
  · obtain ⟨pre, g, tail, hsplit, ha, hp⟩ := first_and C.gates he
    have hpOr : ∀ k ∈ pre, k.op = .or := by
      intro k hk
      exact (op k (hsplit ▸ List.mem_append_left _ hk)).resolve_left (hp k hk)
    let w (i : Fin 8) := run pre (x i)
    have eqv (i : Fin 8) (b : Fin 3 → Bool) :
        fits (List.ofFn b) (g :: tail) (w i) ↔ f i = b := by
      rw [← huniq]
      change _ ↔ fits (List.ofFn b) C.gates (x i)
      rw [hsplit]
      exact (fits_prefix _ _ _ _ hpOr).symm
    have dif (i : Fin 8) := selected_unique tail g (w i) (f i) ha
      ((eqv i _).mpr rfl) (fun b hb => (eqv i b).mp hb)
    obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := by
      have len := lengthBound g (hsplit ▸ List.mem_append_right _ (List.mem_cons_self ..))
      have hn := dif 0
      cases h : g.inputs with
      | nil => simp [args,h,pick] at hn
      | cons a t =>
        cases t with
        | nil => simp [args,h,pick] at hn
        | cons b t =>
          have ht : t = [] := by apply List.length_eq_zero_iff.mp; simp only [h, List.length_cons] at len; omega
          exact ⟨a,b,by simp [ht]⟩
    obtain ⟨B,hB⟩ := prefix_support pre hpOr a
    obtain ⟨F,hF⟩ := prefix_support pre hpOr b
    apply first_conflict B F f (hbal 0)
    · intro i
      rw [← hB (mis i), ← hF (mis i)]
      simpa [args,hab,pick,w,x] using dif i
    · intro i
      have hi := (eqv i (f i)).mpr rfl
      simp only [fits, isAnd282, ha, ite_true] at hi
      rw [← hB (mis i), ← hF (mis i)]
      simpa [args,hab,pick,w,x,GateOp.eval] using hi.1
  · have hp : ∀ g ∈ C.gates, g.op = .or := fun g h => (op g h).resolve_left (fun hx => he ⟨g,h,hx⟩)
    have all (b : Fin 3 → Bool) : pred 0 b := by
      change fits (List.ofFn b) C.gates (x 0)
      have hh := (fits_prefix C.gates [] (x 0) (List.ofFn b) hp).mpr trivial
      simpa only [List.append_nil] using hh
    obtain ⟨b,hne,_⟩ := code_flip (f 0)
    exact hne ((huniq 0 b).mp (all b))

end PEqualNP.Outside.L_meta_282_aux
open PEqualNP.Outside.L_meta_282_aux
theorem PEqualNP.Outside.L_meta_282 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨hmono, ⟨A, hcard, hcover⟩⟩, hcorrect⟩
  apply impossible C hmono (and_length C.gates A hcard hcover)
  intro T
  simpa only [hasEdge, charSet, decide_eq_true_eq] using hcorrect (charSet T)
