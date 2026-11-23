import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta278

open PEqualNP.CircuitLowerBounds

abbrev Signal (n : ℕ) := (Fin n → Bool) → Bool
def single {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)
def supp {n : ℕ} (f : Signal n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => f (single p) = true)
def ordered {n : ℕ} (x y : Fin n → Bool) : Prop := ∀ p, x p = true → y p = true
def mono {n : ℕ} (f : Signal n) : Prop := ∀ x y, ordered x y → f x = true → f y = true
def good {n : ℕ} (S : Finset (Fin n)) (f : Signal n) : Prop :=
  supp f ⊆ S ∧ 2 ≤ (supp f).card

private def zsig {n : ℕ} : Signal n := fun _ => false
private def isAnd : GateOp → Bool
  | .and => true
  | _ => false
private def leftWire {n : ℕ} (w : List (Signal n)) (g : Gate) : Signal n :=
  w.getD (g.inputs.getD 0 0) zsig
private def rightWire {n : ℕ} (w : List (Signal n)) (g : Gate) : Signal n :=
  w.getD (g.inputs.getD 1 0) zsig
private def step {n : ℕ} (w : List (Signal n)) (g : Gate) : Signal n :=
  fun x => if isAnd g.op then leftWire w g x && rightWire w g x
    else leftWire w g x || rightWire w g x
private def outs {n : ℕ} : List Gate → List (Signal n) → List (Signal n)
  | [], _ => []
  | g :: gs, w => step w g :: outs gs (w ++ [step w g])
private def inputs (n : ℕ) : List (Signal n) := List.ofFn fun p : Fin n => fun x => x p
private noncomputable def countGood {n : ℕ} (S : Finset (Fin n)) (l : List (Signal n)) : ℕ := by
  classical
  exact (l.filter (fun v => decide (good S v))).length

private theorem read_wire {n : ℕ} (w : List (Signal n)) (j : ℕ) :
    w.getD j zsig ∈ w ∨ w.getD j zsig = zsig := by
  by_cases hj : j < w.length
  · left
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  · right
    exact List.getD_eq_default _ _ (by omega)

private theorem zbad {n : ℕ} (S : Finset (Fin n)) : ¬good S zsig ∧ mono (zsig (n := n)) := by
  constructor
  · simp [good, supp, zsig]
  · intro x y h hfalse
    exact hfalse

private theorem respect_step {n : ℕ} {w : List (Signal n)} {g : Gate} {x y : Fin n → Bool}
    (hl : leftWire w g x = true → leftWire w g y = true)
    (hr : rightWire w g x = true → rightWire w g y = true) :
    step w g x = true → step w g y = true := by
  cases h : isAnd g.op
  · simpa [step, h] using Or.imp hl hr
  · simpa [step, h] using And.imp hl hr

-- Trace a finite set of outputs back through the circuit. Expanding a counted
-- gate removes its signal from the boundary and adds at most two inputs.
private theorem cut_aux {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (w : List (Signal n)) (hw : ∀ f ∈ w, mono f) (Q : Finset (Signal n))
    (hq : ∀ f ∈ Q, f ∈ w ++ outs gs w ∨ f = zsig) :
    ∃ F : Finset (Signal n), F.card ≤ Q.card + countGood S (outs gs w) ∧
      (∀ f ∈ F, f ∈ w ∨ (¬good S f ∧ mono f)) ∧
      (∀ x y : Fin n → Bool, (∀ f ∈ F, f x = true → f y = true) →
        ∀ f ∈ Q, f x = true → f y = true) := by
  classical
  induction gs generalizing w Q with
  | nil =>
    refine ⟨Q, by simp [outs, countGood], ?_, fun _ _ h => h⟩
    intro f hf
    rcases hq f hf with h | rfl
    · exact Or.inl (by simpa [outs] using h)
    · exact Or.inr (zbad S)
  | cons g gs ih =>
    let v := step w g
    let a := leftWire w g
    let b := rightWire w g
    have read (j : ℕ) : w.getD j zsig ∈ w ∨ (¬good S (w.getD j zsig) ∧ mono (w.getD j zsig)) := by
      rcases read_wire w j with hm | he
      · exact Or.inl hm
      · rw [he]; exact Or.inr (zbad S)
    have ha : a ∈ w ∨ (¬good S a ∧ mono a) := read _
    have hb : b ∈ w ∨ (¬good S b ∧ mono b) := read _
    have hvm : mono v := by
      intro x y h
      exact respect_step ((ha.elim (hw a) And.right) x y h) ((hb.elim (hw b) And.right) x y h)
    have hw' : ∀ f ∈ w ++ [v], mono f := by
      intro f hf
      rcases List.mem_append.mp hf with h | h
      · exact hw _ h
      · obtain rfl := List.mem_singleton.mp h; exact hvm
    obtain ⟨F,hcount,hbase,hcut⟩ := ih (w ++ [v]) hw' Q (by
      intro f hf
      simpa [outs, v, List.append_assoc] using hq f hf)
    have drop (f : Signal n) (hf : f ∈ F) (hne : f ≠ v) :
        f ∈ w ∨ (¬good S f ∧ mono f) := by
      rcases hbase f hf with h | h
      · exact Or.inl ((List.mem_append.mp h).resolve_right (fun h' => hne (List.mem_singleton.mp h')))
      · exact Or.inr h
    by_cases hactive : v ∈ F ∧ good S v
    · let T := insert a (insert b (F.erase v))
      refine ⟨T, ?_, ?_, ?_⟩
      · have h1 := Finset.card_insert_le a (insert b (F.erase v))
        have h2 := Finset.card_insert_le b (F.erase v)
        have h3 := Finset.card_erase_add_one hactive.1
        have hc : countGood S (outs (g :: gs) w) = countGood S (outs gs (w ++ [v])) + 1 := by
          change countGood S (v :: outs gs (w ++ [v])) = _
          simp [countGood, hactive.2]
        dsimp only [T]
        omega
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact ha
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact hb
        exact drop _ (Finset.mem_erase.mp hf).2 (Finset.mem_erase.mp hf).1
      · intro x y hT
        apply hcut x y
        intro f hf
        by_cases he : f = v
        · subst f
          exact respect_step (hT a (by simp [T])) (hT b (by simp [T]))
        · exact hT _ (by simp [T, he, hf])
    · refine ⟨F, ?_, ?_, hcut⟩
      · have hc : countGood S (outs gs (w ++ [v])) ≤ countGood S (outs (g :: gs) w) := by
          change countGood S (outs gs (w ++ [v])) ≤ countGood S (v :: outs gs (w ++ [v]))
          by_cases h : good S v <;> simp [countGood, h]
        omega
      · intro f hf
        by_cases he : f = v
        · subst f
          exact Or.inr ⟨fun hv => hactive ⟨hf,hv⟩,hvm⟩
        · exact drop _ hf he

private def boolRun278 (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private theorem mapGet278 {n : ℕ} (x : Fin n → Bool) (w : List (Signal n)) (i : ℕ) :
    (w.map (fun f => f x)).getD i false = (w.getD i zsig) x := by
  by_cases hi : i < w.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rfl

private theorem evalStep278 {n : ℕ} (x : Fin n → Bool) (w : List (Signal n)) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    g.op.eval (g.inputs.map fun i => (w.map (fun f => f x)).getD i false) =
    step w g x := by
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hg.2
  simp only [he, List.map_cons, List.map_nil, mapGet278]
  rcases hg.1 with hand | hor
  · simp [step, leftWire, rightWire, he, hand, GateOp.eval, isAnd]
  · simp [step, leftWire, rightWire, he, hor, GateOp.eval, isAnd]

private theorem evalRun278 {n : ℕ} (x : Fin n → Bool) (gs : List Gate) (w : List (Signal n))
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    boolRun278 gs (w.map (fun f => f x)) = (w ++ outs gs w).map (fun f => f x) := by
  induction gs generalizing w with
  | nil => simp [boolRun278, outs]
  | cons g gs ih =>
    have hs := evalStep278 x w g (hg _ List.mem_cons_self)
    change boolRun278 gs (w.map (fun f => f x) ++ [_]) = _
    rw [hs]
    have he := ih (w ++ [step w g]) (fun t ht => hg t (List.mem_cons_of_mem _ ht))
    simpa [outs, List.append_assoc] using he

private theorem eval_wire {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (x : Fin n → Bool) (j : ℕ) :
    (C.wires (List.ofFn x)).getD j false = ((inputs n ++ outs C.gates (inputs n)).getD j zsig) x := by
  have hbase : List.ofFn x = (inputs n).map (fun f => f x) := by simp [inputs, Function.comp_def]
  change (boolRun278 C.gates (List.ofFn x)).getD j false = _
  rw [hbase,evalRun278 x _ _ hg,mapGet278]

private theorem outLen278 {n : ℕ} (gs : List Gate) (w : List (Signal n)) :
    (outs gs w).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [outs, ih]

open Classical in
private theorem countRange278 {n : ℕ} (S : Finset (Fin n)) (l : List (Signal n)) :
    countGood S l = ((Finset.range l.length).filter (fun j => good S (l.getD j zsig))).card := by
  classical
  let f := fun j : ℕ => l.getD j zsig
  have hm : (List.range l.length).map f = l := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simp [f, hj']
  have hr : (List.range l.length).toFinset = Finset.range l.length := by ext j; simp
  have hc := List.Nodup.card_eq_countP (P := fun j => good S (f j)) (List.nodup_range (n := l.length))
  calc
    countGood S l = l.countP (fun v => decide (good S v)) := by
      simp only [countGood,List.countP_eq_length_filter]
    _ = ((List.range l.length).map f).countP (fun v => decide (good S v)) := by rw [hm]
    _ = (List.range l.length).countP (fun j => decide (good S (f j))) := by
      rw [List.countP_map]
      rfl
    _ = _ := by rw [hr] at hc; exact hc.symm

private theorem count_wire {n : ℕ} (S : Finset (Fin n)) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    countGood S (outs C.gates (inputs n)) =
    ((Finset.range C.size).filter (fun j =>
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧
      2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card := by
  classical
  let os := outs C.gates (inputs n)
  have read (j : ℕ) (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).getD (n+j) false = (os.getD j zsig) x := by
    rw [eval_wire C hg, List.getD_append_right]
    · simp [inputs, os]
    · simp [inputs]
  have masks (j : ℕ) : (Finset.univ.filter (fun p : Fin n =>
      (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n+j) false = true)) =
      supp (os.getD j zsig) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, supp, read]
    rfl
  simp_rw [masks]
  simpa only [outLen278,Circuit.size,good,os] using countRange278 S os

private theorem boundary_contra {n k : ℕ} (S : Finset (Fin n)) (F : Finset (Signal n))
    (out : Signal n) (hsize : F.card < S.card) (hk : F.card ≤ k)
    (hbad : ∀ f ∈ F, ¬good S f) (hmono : ∀ f ∈ F, mono f)
    (hcut : ∀ x y, (∀ f ∈ F, f x = true → f y = true) → out x = true → out y = true)
    (hsing : ∀ p, out (single p)=true ↔ p ∈ S)
    (hout : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q=true)).card ≤ k →
      (∀ q∈S, x q=false) → out x=false) : False := by
  classical
  let small := F.filter (fun f => supp f ⊆ S)
  let covered := small.biUnion supp
  have hcovered : covered.card ≤ F.card := by
    calc
      covered.card ≤ ∑ f ∈ small, (supp f).card := Finset.card_biUnion_le
      _ ≤ ∑ _f ∈ small, 1 := by
        apply Finset.sum_le_sum
        intro f hf
        have hm := Finset.mem_filter.mp hf
        have hn : ¬2 ≤ (supp f).card := fun h => hbad f hm.1 ⟨hm.2,h⟩
        omega
      _ = small.card := by simp
      _ ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨p,hp,hnp⟩ : ∃ p ∈ S, p ∉ covered := by
    by_contra! h
    have hh := Finset.card_le_card (show S ⊆ covered from h)
    omega
  let active := F.filter (fun f => f (single p) = true)
  have witnesses : ∀ f : ↥active, ∃ q ∈ supp f.val, q ∉ S := by
    intro f
    obtain ⟨hf, hfp⟩ := Finset.mem_filter.mp f.property
    have hnot : ¬ supp f.val ⊆ S := by
      intro hs
      apply hnp
      exact Finset.mem_biUnion.mpr ⟨f.val,Finset.mem_filter.mpr ⟨hf,hs⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfp⟩⟩
    by_contra! h
    exact hnot h
  choose pick hinside houtside using witnesses
  let T := Finset.univ.image pick
  let y : Fin n → Bool := fun q => decide (q ∈ T)
  have hweight : (Finset.univ.filter (fun q => y q = true)).card ≤ k := by
    have heq : Finset.univ.filter (fun q => y q = true) = T := by ext q; simp [y]
    rw [heq]
    calc
      T.card ≤ Finset.univ.card := Finset.card_image_le
      _ = active.card := by simp
      _ ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ k := hk
  have hyoff : ∀ q ∈ S, y q = false := by
    intro q hq
    have hn : q ∉ T := by
      intro hmem
      obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hmem
      exact houtside b (hb ▸ hq)
    simp [y,hn]
  have hyes := hcut (single p) y (by
    intro f hf hfp
    let b : ↥active := ⟨f,Finset.mem_filter.mpr ⟨hf,hfp⟩⟩
    have hsingle : f (single (pick b)) = true := (Finset.mem_filter.mp (hinside b)).2
    apply hmono f hf (single (pick b)) y _ hsingle
    intro q hq
    have he : q = pick b := by simpa [single] using hq
    have hT : q ∈ T := Finset.mem_image.mpr ⟨b,Finset.mem_univ _,he.symm⟩
    simp [y,hT]) ((hsing p).mpr hp)
  rw [hout y hweight hyoff] at hyes
  contradiction

end PEqualNP.Outside.Meta278

open PEqualNP.Outside.Meta278

theorem PEqualNP.Outside.L_meta_278 : ∀ (n k c o : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true ↔ p ∈ S) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false) → c ≤ k → c + 1 ≤ S.card → c ≤ ((Finset.range C.size).filter (fun j => (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card := by
  classical
  intro n k c o S C hg hsingle hout hck hS
  rw [← count_wire S C hg]
  by_contra! hsmall
  let w := inputs n
  let out := (w ++ outs C.gates w).getD o zsig
  have geom (f : Signal n) (hf : f ∈ w) : ¬good S f ∧ mono f := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    constructor
    · have hsupport : supp (fun x : Fin n → Bool => x i) = {i} := by
        ext p
        simp [supp, single, eq_comm]
      simp [good, hsupport]
    · intro x y h
      exact h i
  have hread := read_wire (w ++ outs C.gates w) o
  obtain ⟨F,hsize,hbase,hcut⟩ := cut_aux S C.gates w (fun f hf => (geom f hf).2) {out}
    (by intro f hf; obtain rfl := Finset.mem_singleton.mp hf; exact hread)
  simp only [Finset.card_singleton] at hsize
  have heval (x : Fin n → Bool) : (C.wires (List.ofFn x)).getD o false = out x :=
    eval_wire C hg x o
  have hsmall' : countGood S (outs C.gates w) < c := hsmall
  apply boundary_contra (k := k) S F out (by omega) (by omega)
  · intro f hf
    exact ((hbase f hf).elim (geom f) id).1
  · intro f hf
    exact ((hbase f hf).elim (geom f) id).2
  · intro x y hF
    exact hcut x y hF out (Finset.mem_singleton_self out)
  · intro p
    rw [← heval]
    exact hsingle p
  · intro x hx hs
    rw [← heval]
    exact hout x hx hs
