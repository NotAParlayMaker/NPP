import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1611

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem stepLength (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega

theorem stepRead (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

theorem evalInput {N : ℕ} (gs : List Gate) (w : ℕ) (hw : w < N)
    (a : Fin N → Bool) : Circuit.eval ⟨gs, w⟩ (List.ofFn a) = a ⟨w, hw⟩ := by
  change (gs.foldl step (List.ofFn a)).getD w false = _
  rw [stepRead _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem evalPast {N : ℕ} (gs : List Gate) (w : ℕ) (hw : N + gs.length ≤ w)
    (a : Fin N → Bool) : Circuit.eval ⟨gs, w⟩ (List.ofFn a) = false := by
  change (gs.foldl step (List.ofFn a)).getD w false = _
  apply List.getD_eq_default
  rw [stepLength]
  simpa using hw

theorem evalGate {N : ℕ} (gs : List Gate) (i : Fin gs.length) (a : Fin N → Bool)
    (horder : ∀ w ∈ (gs.get i).inputs, w < N + i.val) :
    Circuit.eval ⟨gs, N + i.val⟩ (List.ofFn a) =
      (gs.get i).op.eval ((gs.get i).inputs.map fun w =>
        Circuit.eval ⟨gs, w⟩ (List.ofFn a)) := by
  let pre := (gs.take i.val).foldl step (List.ofFn a)
  let post := step pre (gs.get i)
  have hsplit : gs = gs.take i.val ++ gs.get i :: gs.drop (i.val + 1) := by
    simp
  have hpre : pre.length = N + i.val := by
    dsimp [pre]
    rw [stepLength]
    simp
  have hpost : post.length = N + i.val + 1 := by simp [post, step, hpre]
  have hfold : gs.foldl step (List.ofFn a) = (gs.drop (i.val + 1)).foldl step post := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  change (gs.foldl step (List.ofFn a)).getD (N + i.val) false = _
  rw [hfold, stepRead (gs.drop (i.val + 1)) post (N + i.val) (by omega)]
  have hval : post.getD (N + i.val) false =
      (gs.get i).op.eval ((gs.get i).inputs.map fun w => pre.getD w false) := by
    simp only [post, step, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hpre]
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro w hw
  change pre.getD w false = (gs.foldl step (List.ofFn a)).getD w false
  have hw' := horder w hw
  rw [hfold, stepRead (gs.drop (i.val + 1)) post w (by omega)]
  simp only [post, step, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

section Labels

variable {V : Type} [DecidableEq V]

def fuse (f : V → V) (x y : V) (z : V) : V :=
  if f z = f y then f x else f z

def Respects (T : Finset V) (f : V → V) (X : Finset V) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, f x = f y → (x ∈ X ↔ y ∈ X)

theorem fuseCoarsens (f : V → V) (x y u v : V) (h : f u = f v) :
    fuse f x y u = fuse f x y v := by simp [fuse, h]

theorem fuseRespects (T X : Finset V) (f : V → V) (x y : V)
    (hx : x ∈ T) (hy : y ∈ T) (hne : f x ≠ f y) :
    Respects T (fuse f x y) X ↔ Respects T f X ∧ (x ∈ X ↔ y ∈ X) := by
  constructor
  · intro h
    exact ⟨fun u hu v hv huv => h u hu v hv (fuseCoarsens f x y u v huv),
      h x hx y hy (by simp [fuse, hne])⟩
  · rintro ⟨h, hxy⟩ u hu v hv huv
    by_cases a : f u = f y <;> by_cases b : f v = f y
    · exact h u hu v hv (a.trans b.symm)
    · have e : f x = f v := by simpa [fuse, a, b] using huv
      exact (h u hu y hy a).trans (hxy.symm.trans (h x hx v hv e))
    · have e : f u = f x := by simpa [fuse, a, b] using huv
      exact (h u hu x hx e).trans (hxy.trans (h y hy v hv b.symm))
    · exact h u hu v hv (by simpa [fuse, a, b] using huv)

theorem fuseImage (T : Finset V) (f : V → V) (x y : V) (hx : x ∈ T)
    (hne : f x ≠ f y) : T.image (fuse f x y) = (T.image f).erase (f y) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_cases h : f u = f y
    · simpa [fuse, h, hne] using (show ∃ a ∈ T, f a = f x from ⟨x, hx, rfl⟩)
    · simpa [fuse, h] using (show ∃ a ∈ T, f a = f u from ⟨u, hu, rfl⟩)
  · rintro ⟨hne', u, hu, rfl⟩
    exact ⟨u, hu, by simp [fuse, hne']⟩

end Labels

section Scan

variable {N : ℕ}

def Good (L : Finset (Fin N)) (gs : List Gate) (w : ℕ) : Prop :=
  Circuit.eval ⟨gs, w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L)) = false

def Active (gs : List Gate) (w : ℕ) (x : Fin N) : Prop :=
  Circuit.eval ⟨gs, w⟩ (List.ofFn fun v : Fin N => decide (v = x)) = true

def OneLabel (T : Finset (Fin N)) (f : Fin N → Fin N) (P : Fin N → Prop) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, P x → P y → f x = f y

def Cut (L T : Finset (Fin N)) (gs : List Gate) (n : ℕ) (X : Finset (Fin N)) : Prop :=
  ∀ i : Fin gs.length, i.val < n → (gs.get i).op = GateOp.or →
    Good L gs (N + i.val) → ∀ a b : ℕ, (gs.get i).inputs = [a, b] →
    ∀ y ∈ T, ∀ y' ∈ T, (Active gs a y ∨ Active gs b y) →
      (Active gs a y' ∨ Active gs b y') → (y ∈ X ↔ y' ∈ X)

def Core (L T : Finset (Fin N)) (gs : List Gate) (i : Fin gs.length) : Prop :=
  (gs.get i).op = GateOp.or ∧ Good L gs (N + i.val) ∧
    ∃ a b : ℕ, (gs.get i).inputs = [a, b] ∧
      ∃ x ∈ T, ∃ y ∈ T, Active gs a x ∧ Active gs b y ∧
        ∃ X : Finset (Fin N), x ∈ X ∧ y ∉ X ∧ Cut L T gs i.val X

def AtGate (L T : Finset (Fin N)) (gs : List Gate) (i : Fin gs.length)
    (X : Finset (Fin N)) : Prop :=
  (gs.get i).op = GateOp.or → Good L gs (N + i.val) →
    ∀ a b : ℕ, (gs.get i).inputs = [a, b] →
      ∀ y ∈ T, ∀ y' ∈ T, (Active gs a y ∨ Active gs b y) →
        (Active gs a y' ∨ Active gs b y') → (y ∈ X ↔ y' ∈ X)

theorem cutSucc (L T : Finset (Fin N)) (gs : List Gate) (i : Fin gs.length)
    (X : Finset (Fin N)) :
    Cut L T gs (i.val + 1) X ↔ Cut L T gs i.val X ∧ AtGate L T gs i X := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
  · rintro ⟨h, hnow⟩ j hj
    by_cases hj' : j.val < i.val
    · exact h j hj'
    · have e : j = i := Fin.ext (by omega)
      subst j
      exact hnow

theorem prefixCard {l : ℕ} (K : Finset (Fin l)) (i : Fin l) :
    (K.filter (fun j => j.val < i.val + 1)).card =
      (K.filter (fun j => j.val < i.val)).card + if i ∈ K then 1 else 0 := by
  by_cases h : i ∈ K
  · have e : K.filter (fun j => j.val < i.val + 1) =
        insert i (K.filter (fun j => j.val < i.val)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      by_cases hj : j = i
      · subst j; simp [h]
      · have hne : j.val ≠ i.val := fun e => hj (Fin.ext e)
        simp [hj]
        omega
    rw [e, Finset.card_insert_of_notMem (by simp), ite_eq_left h]
  · have e : K.filter (fun j => j.val < i.val + 1) =
        K.filter (fun j => j.val < i.val) := by
      ext j
      simp only [Finset.mem_filter]
      by_cases hj : j = i
      · subst j; simp [h]
      · have hne : j.val ≠ i.val := fun e => hj (Fin.ext e)
        constructor <;> rintro ⟨hjK, hlt⟩ <;> exact ⟨hjK, by omega⟩
    rw [e, ite_eq_right h, Nat.add_zero]

theorem apartIff (L T : Finset (Fin N)) (gs : List Gate) (n : ℕ)
    (f : Fin N → Fin N) (hcut : ∀ X, Cut L T gs n X ↔ Respects T f X)
    (x y : Fin N) (hx : x ∈ T) (hy : y ∈ T) :
    (∃ X, x ∈ X ∧ y ∉ X ∧ Cut L T gs n X) ↔ f x ≠ f y := by
  constructor
  · rintro ⟨X, hxX, hyX, hX⟩ h
    exact hyX (((hcut X).mp hX x hx y hy h).mp hxX)
  · intro h
    let X := T.filter (fun z => f z = f x)
    refine ⟨X, by simp [X, hx], by simp [X, hy, Ne.symm h], (hcut X).mpr ?_⟩
    intro u hu v hv huv
    simp [X, hu, hv, huv]

theorem inputOneLabel (T : Finset (Fin N)) (gs : List Gate) (f : Fin N → Fin N)
    (w : ℕ) (hw : w < N) : OneLabel T f (Active gs w) := by
  intro x _ y _ hx hy
  have hx' : (⟨w, hw⟩ : Fin N) = x := by
    simpa [Active, evalInput gs w hw] using hx
  have hy' : (⟨w, hw⟩ : Fin N) = y := by
    simpa [Active, evalInput gs w hw] using hy
  rw [← hx', ← hy']

theorem orPair (L : Finset (Fin N)) (gs : List Gate) (i : Fin gs.length) (a b : ℕ)
    (horder : ∀ w ∈ (gs.get i).inputs, w < N + i.val)
    (hop : (gs.get i).op = GateOp.or) (hin : (gs.get i).inputs = [a, b])
    (hgood : Good L gs (N + i.val)) :
    Good L gs a ∧ Good L gs b ∧ ∀ x : Fin N,
      Active gs (N + i.val) x ↔ Active gs a x ∨ Active gs b x := by
  have hg : Good L gs a ∧ Good L gs b := by
    unfold Good at hgood ⊢
    rw [evalGate gs i _ horder, hop, hin] at hgood
    simpa [GateOp.eval] using hgood
  refine ⟨hg.1, hg.2, fun x => ?_⟩
  unfold Active
  rw [evalGate gs i _ horder, hop, hin]
  simp [GateOp.eval]

theorem falseAnd (a b : Bool) (h : (a && b) = false) : a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

theorem otherGate (L T : Finset (Fin N)) (gs : List Gate) (i : Fin gs.length)
    (f : Fin N → Fin N) (horder : ∀ w ∈ (gs.get i).inputs, w < N + i.val)
    (hshape : ((gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or) ∧
      (gs.get i).inputs.length ≤ 2)
    (hprev : ∀ w < N + i.val, Good L gs w → OneLabel T f (Active gs w))
    (hnot : ¬ ((gs.get i).op = GateOp.or ∧ Good L gs (N + i.val) ∧
      ∃ a b : ℕ, (gs.get i).inputs = [a, b]))
    (hgood : Good L gs (N + i.val)) :
    OneLabel T f (Active gs (N + i.val)) := by
  generalize hin : (gs.get i).inputs = ws
  cases ws with
  | nil =>
    rcases hshape.1 with hop | hop
    · unfold Good at hgood
      rw [evalGate gs i _ horder, hop, hin] at hgood
      simp [GateOp.eval] at hgood
    · intro x _ _ _ hx
      unfold Active at hx
      rw [evalGate gs i _ horder, hop, hin] at hx
      simp [GateOp.eval] at hx
  | cons a tail =>
    cases tail with
    | nil =>
      have ha := horder a (by rw [hin]; simp)
      have he (x : Fin N → Bool) : Circuit.eval ⟨gs, N + i.val⟩ (List.ofFn x)
          = Circuit.eval ⟨gs, a⟩ (List.ofFn x) := by
        rcases hshape.1 with hop | hop <;>
          rw [evalGate gs i _ horder, hop, hin] <;> simp [GateOp.eval]
      have ha' : Good L gs a := by simpa [Good, he] using hgood
      simpa [OneLabel, Active, he] using hprev a ha ha'
    | cons b tail =>
      cases tail with
      | nil =>
        rcases hshape.1 with hop | hop
        · have h : Good L gs a ∨ Good L gs b := by
            unfold Good at hgood ⊢
            rw [evalGate gs i _ horder, hop, hin] at hgood
            apply falseAnd
            simpa only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
              List.all_nil, id_eq, Bool.and_true] using hgood
          have he (x : Fin N) : Active gs (N + i.val) x →
              Active gs a x ∧ Active gs b x := by
            unfold Active
            rw [evalGate gs i _ horder, hop, hin]
            simp [GateOp.eval]
          intro x hx y hy hax hay
          rcases h with ha | hb
          · exact hprev a (horder a (by rw [hin]; simp)) ha x hx y hy (he x hax).1 (he y hay).1
          · exact hprev b (horder b (by rw [hin]; simp)) hb x hx y hy (he x hax).2 (he y hay).2
        · exact (hnot ⟨hop, hgood, a, b, hin⟩).elim
      | cons c tail =>
        have hs := hshape.2
        rw [hin] at hs
        simp at hs

theorem unionLabel (T : Finset (Fin N)) (f : Fin N → Fin N) (A B : Fin N → Prop)
    (ha : OneLabel T f A) (hb : OneLabel T f B)
    (hab : ∀ x ∈ T, ∀ y ∈ T, A x → B y → f x = f y) :
    OneLabel T f (fun x => A x ∨ B x) := by
  intro x hx y hy hax hay
  rcases hax with hax | hax <;> rcases hay with hay | hay
  · exact ha x hx y hy hax hay
  · exact hab x hx y hy hax hay
  · exact (hab y hy x hx hay hax).symm
  · exact hb x hx y hy hax hay

theorem labelAfterFuse (T : Finset (Fin N)) (f : Fin N → Fin N)
    (P : Fin N → Prop) (h : OneLabel T f P) (x y : Fin N) :
    OneLabel T (fuse f x y) P :=
  fun u hu v hv hpu hpv => fuseCoarsens f x y u v (h u hu v hv hpu hpv)

def State (L T : Finset (Fin N)) (gs : List Gate) (K : Finset (Fin gs.length))
    (n : ℕ) (f : Fin N → Fin N) : Prop :=
  (∀ X, Cut L T gs n X ↔ Respects T f X) ∧
    (∀ w < N + n, Good L gs w → OneLabel T f (Active gs w)) ∧
    (T.image f).card + (K.filter (fun i => i.val < n)).card = T.card

-- Each label represents one component of the singleton inputs seen so far.
-- A gate counted in K identifies two distinct labels and removes one image value.
theorem scan (L T : Finset (Fin N)) (gs : List Gate) (K : Finset (Fin gs.length))
    (hshape : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (horder : ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < N + i.val)
    (hK : ∀ i, i ∈ K ↔ Core L T gs i) (n : ℕ) (hn : n ≤ gs.length) :
    ∃ f, State L T gs K n f := by
  classical
  induction n with
  | zero =>
    refine ⟨id, ?_, ?_, ?_⟩
    · intro X
      constructor
      · intro _ x _ y _ e
        change x = y at e
        subst y
        rfl
      · intro _ i hi
        omega
    · intro w hw _
      exact inputOneLabel T gs id w (by omega)
    · simp
  | succ n ih =>
    let i : Fin gs.length := ⟨n, by omega⟩
    obtain ⟨f, hcut, hprev, hcount⟩ := ih (by omega)
    have hnext (X : Finset (Fin N)) :
        Cut L T gs (n + 1) X ↔ Cut L T gs n X ∧ AtGate L T gs i X :=
      cutSucc L T gs i X
    have hcnt :
        (K.filter (fun j => j.val < n + 1)).card =
          (K.filter (fun j => j.val < n)).card + if i ∈ K then 1 else 0 :=
      prefixCard K i
    have before (w : ℕ) (hw : w < N + (n + 1)) (h : ¬ w < N + n) :
        w = N + i.val := by
      change w = N + n
      omega
    have noMerge (hki : i ∉ K)
        (hnow : ∀ X, Respects T f X → AtGate L T gs i X)
        (hout : Good L gs (N + i.val) → OneLabel T f (Active gs (N + i.val))) :
        ∃ f, State L T gs K (n + 1) f := by
      refine ⟨f, ?_, ?_, ?_⟩
      · intro X
        rw [hnext X, hcut X]
        exact ⟨And.left, fun h => ⟨h, hnow X h⟩⟩
      · intro w hw hg
        by_cases h : w < N + n
        · exact hprev w h hg
        · rw [before w hw h] at hg ⊢
          exact hout hg
      · rw [hcnt, ite_eq_right hki, Nat.add_zero]
        exact hcount
    by_cases hpair : (gs.get i).op = GateOp.or ∧ Good L gs (N + i.val) ∧
        ∃ a b : ℕ, (gs.get i).inputs = [a, b]
    · obtain ⟨hop, hgood, a, b, hin⟩ := hpair
      obtain ⟨hga, hgb, heval⟩ := orPair L gs i a b (horder i) hop hin hgood
      have ha : OneLabel T f (Active gs a) := hprev a (horder i a (by rw [hin]; simp)) hga
      have hb : OneLabel T f (Active gs b) := hprev b (horder i b (by rw [hin]; simp)) hgb
      have sameInputs (a' b' : ℕ) (hin' : (gs.get i).inputs = [a', b']) :
          a = a' ∧ b = b' := by
        simpa using hin.symm.trans hin'
      by_cases hjoin : ∃ x ∈ T, ∃ y ∈ T, Active gs a x ∧ Active gs b y ∧ f x ≠ f y
      · obtain ⟨x, hx, y, hy, hax, hby, hne⟩ := hjoin
        let f' := fuse f x y
        have hki : i ∈ K := (hK i).mpr
          ⟨hop, hgood, a, b, hin, x, hx, y, hy, hax, hby,
            (apartIff L T gs n f hcut x y hx hy).mpr hne⟩
        have hxy : f' x = f' y := by simp [f', fuse, hne]
        have hu : OneLabel T f' (fun z => Active gs a z ∨ Active gs b z) := by
          apply unionLabel T f' _ _ (labelAfterFuse T f _ ha x y)
            (labelAfterFuse T f _ hb x y)
          intro u hut v hvt hau hbv
          exact (fuseCoarsens f x y u x (ha u hut x hx hau hax)).trans
            (hxy.trans (fuseCoarsens f x y y v (hb y hy v hvt hby hbv)))
        refine ⟨f', ?_, ?_, ?_⟩
        · intro X
          rw [hnext X, hcut X]
          constructor
          · rintro ⟨hr, hnow⟩
            exact (fuseRespects T X f x y hx hy hne).mpr
              ⟨hr, hnow hop hgood a b hin x hx y hy (.inl hax) (.inr hby)⟩
          · intro hr'
            refine ⟨((fuseRespects T X f x y hx hy hne).mp hr').1, ?_⟩
            intro _ _ a' b' hin' u hut v hvt hu' hv'
            obtain ⟨rfl, rfl⟩ := sameInputs a' b' hin'
            exact hr' u hut v hvt (hu u hut v hvt hu' hv')
        · intro w hw hg
          by_cases h : w < N + n
          · exact labelAfterFuse T f _ (hprev w h hg) x y
          · rw [before w hw h]
            intro u hut v hvt hau hav
            exact hu u hut v hvt ((heval u).mp hau) ((heval v).mp hav)
        · have hy' : f y ∈ T.image f := Finset.mem_image.mpr ⟨y, hy, rfl⟩
          change (T.image (fuse f x y)).card + _ = _
          rw [fuseImage T f x y hx hne, Finset.card_erase_of_mem hy', hcnt, ite_eq_left hki]
          have hp : 0 < (T.image f).card := Finset.card_pos.mpr ⟨f y, hy'⟩
          omega
      · have hu : OneLabel T f (fun z => Active gs a z ∨ Active gs b z) := by
          apply unionLabel T f _ _ ha hb
          intro x hx y hy hax hby
          by_contra hne
          exact hjoin ⟨x, hx, y, hy, hax, hby, hne⟩
        have hki : i ∉ K := by
          intro h
          obtain ⟨_, _, a', b', hin', x, hx, y, hy, hax, hby, hsep⟩ := (hK i).mp h
          obtain ⟨rfl, rfl⟩ := sameInputs a' b' hin'
          exact hjoin ⟨x, hx, y, hy, hax, hby, (apartIff L T gs n f hcut x y hx hy).mp hsep⟩
        apply noMerge hki
        · intro X hr _ _ a' b' hin' u hut v hvt hu' hv'
          obtain ⟨rfl, rfl⟩ := sameInputs a' b' hin'
          exact hr u hut v hvt (hu u hut v hvt hu' hv')
        · intro _ u hut v hvt hau hav
          exact hu u hut v hvt ((heval u).mp hau) ((heval v).mp hav)
    · have hki : i ∉ K := by
        intro h
        obtain ⟨hop, hgood, a, b, hin, _⟩ := (hK i).mp h
        exact hpair ⟨hop, hgood, a, b, hin⟩
      apply noMerge hki
      · intro X _ hop hgood a b hin
        exact (hpair ⟨hop, hgood, a, b, hin⟩).elim
      · exact otherGate L T gs i f (horder i)
          (hshape _ (List.get_mem _ _)) hprev hpair

theorem countCore (L T : Finset (Fin N)) (gs : List Gate) (o : ℕ)
    (hT : T.Nonempty)
    (hshape : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (horder : ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < N + i.val)
    (hgood : Good L gs o) (hout : ∀ x ∈ T, Active gs o x)
    (K : Finset (Fin gs.length)) (hK : ∀ i, i ∈ K ↔ Core L T gs i) :
    K.card = T.card - 1 ∧ ∀ i ∈ K, ∃ a b : ℕ, (gs.get i).inputs = [a, b] ∧
      ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ Active gs a x ∧ Active gs b y := by
  obtain ⟨x, hx⟩ := hT
  have ho : o < N + gs.length := by
    by_contra! h
    have ha := hout x hx
    simp [Active, evalPast gs o h] at ha
  obtain ⟨f, _, hlabel, hcount⟩ := scan L T gs K hshape horder hK gs.length le_rfl
  have he : T.image f = {f x} := by
    ext z
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hlabel o ho hgood y hy x hx (hout y hy) (hout x hx)
    · rintro rfl
      exact ⟨x, hx, rfl⟩
  have hfilter : K.filter (fun i => i.val < gs.length) = K := by
    ext i
    simp
  rw [he, Finset.card_singleton, hfilter] at hcount
  refine ⟨by omega, ?_⟩
  intro i hi
  obtain ⟨_, _, a, b, hin, u, hu, v, hv, hau, hbv, X, huX, hvX, _⟩ := (hK i).mp hi
  exact ⟨a, b, hin, u, hu, v, hv, fun e => hvX (e ▸ huX), hau, hbv⟩

end Scan

end PEqualNP.Outside.L_meta_1611

theorem PEqualNP.Outside.L_meta_1611 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ x ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = true) →
    ∀ K : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ K ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ T0, ∃ r' ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin N => decide (v = r))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin N => decide (v = r'))) = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (i : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ T0, ∀ y' ∈ T0,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true) → (y ∈ X ↔ y' ∈ X)))) →
      K.card = m - 1 ∧ ∀ g ∈ K, ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧
        ∃ x ∈ T0, ∃ y ∈ T0, x ≠ y ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true := by
  intro q m N L i0 T0 hq hm hmq hN hlines hinter hpoints hsubset hT gates o hshape horder hgood hout K hK
  have hnonempty : T0.Nonempty := Finset.card_pos.mp (by omega)
  have h := PEqualNP.Outside.L_meta_1611.countCore
    (L i0) T0 gates o hnonempty hshape horder hgood hout K hK
  rw [hT] at h
  exact h
