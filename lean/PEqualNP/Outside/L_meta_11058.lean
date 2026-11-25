import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Eval
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11058

open PEqualNP.CircuitLowerBounds

abbrev Signal (α : Type) := α → Bool

def zero {α : Type} : Signal α := fun _ => false
def one {α : Type} : Signal α := fun _ => true

def port {α : Type} (ws : List (Signal α)) (inputs : List ℕ) : Signal α :=
  fun x => inputs.any fun i => ws.getD i zero x

def reads {α : Type} (ws : List (Signal α)) (f : Signal α) : Prop :=
  ∃ is : List ℕ, (∀ i ∈ is, i < ws.length) ∧ f = port ws is

def ready {α : Type} (ws : List (Signal α)) (f : Signal α) : Prop :=
  f = one ∨ reads ws f

abbrev Instruction := Bool × List ℕ × List ℕ

def instr {α : Type} (w : List (Signal α)) (st : Instruction) : Signal α :=
  if st.1 then fun x => !port w st.2.1 x
  else fun x => port w st.2.1 x && port w st.2.2 x

def appendInstr {α : Type} (w : List (Signal α)) (st : Instruction) : List (Signal α) :=
  w ++ [instr w st]

def run {α : Type} (w : List (Signal α)) (p : List Instruction) : List (Signal α) :=
  p.foldl appendInstr w

def ands (p : List Instruction) : ℕ := p.countP (fun st => !st.1)
def nots (p : List Instruction) : ℕ := p.countP (fun st => st.1)

def wellStep (m : ℕ) (s : Instruction) : Prop :=
  ∀ i ∈ s.2.1 ++ s.2.2, i < m

def wellRun : ℕ → List Instruction → Prop
  | _, [] => True
  | m, s :: p => wellStep m s ∧ wellRun (m+1) p

private theorem getD_append_left {α : Type} (l r : List α) (d : α) {i : ℕ}
    (h : i < l.length) : (l ++ r).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

private theorem reads_append {α : Type} {ws : List (Signal α)} {f : Signal α}
    (h : reads ws f) (r : List (Signal α)) : reads (ws ++ r) f := by
  obtain ⟨is, hi, hf⟩ := h
  refine ⟨is, fun i h => by simp; have := hi i h; omega, ?_⟩
  rw [hf]
  funext x
  unfold port
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨i, hi', hv⟩
    exact ⟨i, hi', by rwa [getD_append_left _ _ _ (hi i hi')]⟩
  · rintro ⟨i, hi', hv⟩
    exact ⟨i, hi', by rwa [← getD_append_left _ r _ (hi i hi')]⟩

private theorem ready_append {α : Type} {ws : List (Signal α)} {f : Signal α}
    (h : ready ws f) (r : List (Signal α)) : ready (ws ++ r) f := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (reads_append h r)

private theorem read_zero {α : Type} (w : List (Signal α)) : reads w zero :=
  ⟨[], by simp, rfl⟩

private theorem read_last {α : Type} (w : List (Signal α)) (a : Signal α) :
    reads (w ++ [a]) a := by
  refine ⟨[w.length], ?_, ?_⟩
  · simp
  · funext x
    simp [port, List.getD]

private theorem read_union {α : Type} {w : List (Signal α)} {a b : Signal α}
    (ha : reads w a) (hb : reads w b) : reads w (fun x => a x || b x) := by
  obtain ⟨is, hi, rfl⟩ := ha
  obtain ⟨js, hj, rfl⟩ := hb
  refine ⟨is ++ js, ?_, ?_⟩
  · intro i h
    rcases List.mem_append.1 h with h | h
    · exact hi i h
    · exact hj i h
  · funext x
    simp [port]

private theorem ready_union {α : Type} {w : List (Signal α)} {a b : Signal α}
    (ha : ready w a) (hb : ready w b) : ready w (fun x => a x || b x) := by
  rcases ha with rfl | ha
  · left; funext x; simp [one]
  rcases hb with rfl | hb
  · left; funext x; simp [one]
  · exact Or.inr (read_union ha hb)

private theorem ready_union_list {α : Type} {w : List (Signal α)} (fs : List (Signal α))
    (hf : ∀ f ∈ fs, ready w f) : ready w (fun x => fs.any (· x)) := by
  induction fs with
  | nil => exact Or.inr (read_zero _)
  | cons f fs ih =>
    exact ready_union (hf _ (by simp)) (ih fun a ha => hf _ (by simp [ha]))

private theorem prepare_and {α : Type} (w : List (Signal α)) {a b : Signal α}
    (ha : ready w a) (hb : ready w b) : ∃ p,
    wellRun w.length p ∧ ands p ≤ 1 ∧ nots p = 0 ∧
      ready (run w p) (fun x => a x && b x) := by
  rcases ha with rfl | ha
  · exact ⟨[], trivial, by simp [ands], rfl, by simpa [one, run] using hb⟩
  rcases hb with rfl | hb
  · refine ⟨[], trivial, by simp [ands], rfl, ?_⟩
    change ready w (fun x => a x && one x)
    rw [show (fun x => a x && one x) = a from by funext x; simp [one]]
    exact Or.inr ha
  · obtain ⟨is, hi, rfl⟩ := ha
    obtain ⟨js, hj, rfl⟩ := hb
    refine ⟨[(false, is, js)], ?_, by simp [ands], rfl, Or.inr (read_last _ _)⟩
    simp only [wellRun, wellStep, List.mem_append, and_true]
    intro i h
    rcases h with h | h
    · exact hi _ h
    · exact hj _ h

private theorem prepare_not {α : Type} (w : List (Signal α)) {a : Signal α}
    (ha : ready w a) : ∃ p,
    wellRun w.length p ∧ ands p = 0 ∧ nots p ≤ 1 ∧
      ready (run w p) (fun x => !a x) := by
  rcases ha with rfl | ha
  · exact ⟨[], trivial, rfl, by simp [nots], Or.inr (read_zero _)⟩
  · obtain ⟨is, hi, rfl⟩ := ha
    refine ⟨[(true, is, [])], ?_, rfl, by simp [nots], Or.inr (read_last _ _)⟩
    simpa [wellRun, wellStep] using hi

private theorem wellRun_append {m : ℕ} {p q : List Instruction}
    (hp : wellRun m p) (hq : wellRun (m+p.length) q) : wellRun m (p ++ q) := by
  induction p generalizing m with
  | nil => simpa using hq
  | cons s p ih =>
    refine ⟨hp.1, ih hp.2 ?_⟩
    convert hq using 1; simp; omega

private theorem run_length {α : Type} (w : List (Signal α)) (p : List Instruction) :
    (run w p).length = w.length + p.length := by
  induction p generalizing w with
  | nil => simp [run]
  | cons s p ih =>
    change (run (appendInstr w s) p).length = _
    simp [ih, appendInstr]
    omega

private theorem run_append {α : Type} (w : List (Signal α)) (p q : List Instruction) :
    run w (p ++ q) = run (run w p) q := by
  simp [run]

private theorem run_wires_append {α : Type} (w : List (Signal α)) (p : List Instruction) :
    ∃ tail, run w p = w ++ tail := by
  induction p generalizing w with
  | nil => exact ⟨[], by simp [run]⟩
  | cons s p ih =>
    obtain ⟨t, ht⟩ := ih (appendInstr w s)
    exact ⟨[instr w s] ++ t, by
      change run (appendInstr w s) p = _
      rw [ht, appendInstr, List.append_assoc]⟩

def flip (d b : Bool) : Bool := if d then !b else b

def flipOp (d : Bool) (op : GateOp) : GateOp :=
  match d, op with
  | true, .and => .or
  | true, .or => .and
  | _, op => op

def gateShape (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def isNot : GateOp → Bool
  | .not => true
  | _ => false

def gateFn {α : Type} (d : Bool) (w : List (Signal α)) (g : Gate) : Signal α :=
  fun x =>
    let args := g.inputs.map (fun i => (w.getD i (fun _ => flip d false)) x)
    match flipOp d g.op with
    | .not => !(args.headD (flip d false))
    | op => op.eval args

def extend {α : Type} (d : Bool) (w : List (Signal α)) (g : Gate) : List (Signal α) :=
  w ++ [gateFn d w g]

def runGates {α : Type} (d : Bool) (w : List (Signal α)) (gs : List Gate) :
    List (Signal α) := gs.foldl (extend d) w

private theorem shape_flip {d op} (h : op = .and ∨ op = .or ∨ op = .not) :
    flipOp d op = .and ∨ flipOp d op = .or ∨ flipOp d op = .not := by
  rcases h with rfl | rfl | rfl <;> cases d <;> simp [flipOp]

private theorem lookup_ready {α : Type} {raw ws : List (Signal α)}
    (h : ∀ f ∈ raw, ready ws f) (d : Bool) (i : ℕ) :
    ready ws (raw.getD i (fun _ => flip d false)) := by
  by_cases hi : i < raw.length
  · apply h
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  · rw [List.getD_eq_default _ _ (by omega)]
    cases d
    · exact Or.inr (read_zero _)
    · exact Or.inl rfl

private theorem prepare_gate {α : Type} (d : Bool) (raw ws : List (Signal α)) (g : Gate)
    (hg : gateShape g) (h : ∀ f ∈ raw, ready ws f) : ∃ p,
    wellRun ws.length p ∧ ands p ≤ (isAnd (flipOp d g.op)).toNat ∧
    nots p ≤ (isNot (flipOp d g.op)).toNat ∧
    ready (run ws p) (gateFn d raw g) := by
  have hr (i : ℕ) := lookup_ready h d i
  obtain ⟨hok, hlen⟩ := hg
  rcases shape_flip (d := d) hok with hop | hop | hop
  · have hgate : gateFn d raw g =
        fun x => (g.inputs.map (fun i => raw.getD i (fun _ => flip d false) x)).all id := by
      funext x
      simp [gateFn, hop, GateOp.eval]
    rw [hgate, hop]
    simp only [isAnd, isNot, Bool.toNat_true, Bool.toNat_false]
    rcases hinputs : g.inputs with _ | ⟨i, _ | ⟨j, rest⟩⟩
    · exact ⟨[], trivial, by simp [ands], by simp [nots], Or.inl rfl⟩
    · refine ⟨[], trivial, by simp [ands], by simp [nots], ?_⟩
      simpa [run] using hr i
    · have hrest : rest = [] := by simp [hinputs] at hlen; exact hlen
      subst rest
      obtain ⟨p, hp, hpA, hpN, hpR⟩ := prepare_and ws (hr i) (hr j)
      exact ⟨p, hp, hpA, by omega, by simpa using hpR⟩
  · have hgate : gateFn d raw g =
        fun x => g.inputs.any fun i => raw.getD i (fun _ => flip d false) x := by
      funext x
      simp [gateFn, hop, GateOp.eval, List.any_map]
    rw [hgate, hop]
    simp only [isAnd, isNot, Bool.toNat_false]
    refine ⟨[], trivial, by simp [ands], by simp [nots], ?_⟩
    have hr' : ∀ f ∈ g.inputs.map (fun i => raw.getD i (fun _ => flip d false)), ready ws f := by
      intro f hf
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
      exact hr i
    simpa only [run, List.foldl_nil, List.any_map, Function.comp_def] using ready_union_list _ hr'
  · have hgate : gateFn d raw g = fun x =>
        !((g.inputs.map fun i => raw.getD i (fun _ => flip d false) x).headD (flip d false)) := by
      funext x
      simp [gateFn, hop]
    rw [hgate, hop]
    simp only [isAnd, isNot, Bool.toNat_true, Bool.toNat_false]
    rcases hinputs : g.inputs with _ | ⟨i, rest⟩
    · have he : ready ws (fun _ => flip d false) := by
        cases d
        · exact Or.inr (read_zero _)
        · exact Or.inl rfl
      obtain ⟨p, hp, hpA, hpN, hpR⟩ := prepare_not ws he
      exact ⟨p, hp, by omega, hpN, hpR⟩
    · obtain ⟨p, hp, hpA, hpN, hpR⟩ := prepare_not ws (hr i)
      exact ⟨p, hp, by omega, hpN, hpR⟩

theorem flatten {α : Type} (d : Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, gateShape g) (raw ws : List (Signal α))
    (h : ∀ f ∈ raw, ready ws f) :
    ∃ p, wellRun ws.length p ∧
      ands p ≤ gs.countP (fun g => isAnd (flipOp d g.op)) ∧
      nots p ≤ gs.countP (fun g => isNot (flipOp d g.op)) ∧
      ∀ f ∈ runGates d raw gs, ready (run ws p) f := by
  induction gs generalizing raw ws with
  | nil => exact ⟨[], trivial, le_refl _, le_refl _, h⟩
  | cons g gs ih =>
    obtain ⟨p, hp, hpA, hpN, hpR⟩ := prepare_gate d raw ws g (hgs g (by simp)) h
    have hn : ∀ f ∈ extend d raw g, ready (run ws p) f := by
      intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨t, ht⟩ := run_wires_append ws p
        rw [ht]
        exact ready_append (h f hf) t
      · simp only [List.mem_singleton] at hf
        exact hf ▸ hpR
    obtain ⟨q, hq, hqA, hqN, hqR⟩ :=
      ih (fun g hg => hgs g (by simp [hg])) _ _ hn
    refine ⟨p ++ q, wellRun_append hp (by rwa [run_length] at hq), ?_, ?_, ?_⟩
    · have eql : ands (p ++ q) = ands p + ands q := List.countP_append
      have eqr : (g :: gs).countP (fun g => isAnd (flipOp d g.op)) =
          (isAnd (flipOp d g.op)).toNat + gs.countP (fun g => isAnd (flipOp d g.op)) := by
        cases h : isAnd (flipOp d g.op) <;> simp [List.countP_cons, h, Nat.add_comm]
      rw [eql, eqr]
      exact Nat.add_le_add hpA hqA
    · have eql : nots (p ++ q) = nots p + nots q := List.countP_append
      have eqr : (g :: gs).countP (fun g => isNot (flipOp d g.op)) =
          (isNot (flipOp d g.op)).toNat + gs.countP (fun g => isNot (flipOp d g.op)) := by
        cases h : isNot (flipOp d g.op) <;> simp [List.countP_cons, h, Nat.add_comm]
      rw [eql, eqr]
      exact Nat.add_le_add hpN hqN
    · change ∀ f ∈ runGates d (extend d raw g) gs, ready (run ws (p ++ q)) f
      simpa only [run_append] using hqR


private theorem eval_dual (d : Bool) (op : GateOp) (vs : List Bool)
    (hop : op = .and ∨ op = .or ∨ op = .not) :
    (match flipOp d op with
    | .not => !((vs.map (flip d)).headD (flip d false))
    | op => op.eval (vs.map (flip d))) = flip d (op.eval vs) := by
  rcases hop with rfl | rfl | rfl <;> cases d
  · rw [show flip false = id from rfl]; simp [flipOp, flip, GateOp.eval]
  · induction vs with
    | nil => rfl
    | cons a vs ih =>
      cases a <;> simp_all [flipOp, flip, GateOp.eval]
  · rw [show flip false = id from rfl]; simp [flipOp, flip, GateOp.eval]
  · induction vs with
    | nil => rfl
    | cons a vs ih =>
      cases a <;> simp_all [flipOp, flip, GateOp.eval]
  · cases vs <;> simp [flipOp, flip, GateOp.eval]
  · cases vs <;> simp [flipOp, flip, GateOp.eval]

private theorem lookup_dual {α : Type} (d : Bool) (x : α)
    (w : List (Signal α)) (v : List Bool) (h : w.map (· x) = v.map (flip d)) (i : ℕ) :
    (w.getD i (fun _ => flip d false)) x = flip d (v.getD i false) := by
  calc
    (w.getD i (fun _ => flip d false)) x = (w.map (· x)).getD i (flip d false) := by
      symm
      exact List.getD_map w (fun _ => flip d false) (n := i) (fun f : Signal α => f x)
    _ = (v.map (flip d)).getD i (flip d false) := by rw [h]
    _ = flip d (v.getD i false) := List.getD_map v false (n := i) (flip d)

private theorem gateFn_eval {α : Type} (d : Bool) (x : α)
    (w : List (Signal α)) (v : List Bool) (h : w.map (· x) = v.map (flip d))
    (g : Gate) (hg : gateShape g) :
    gateFn d w g x = flip d (g.op.eval (g.inputs.map fun i => v.getD i false)) := by
  unfold gateFn
  simp only
  have he : g.inputs.map (fun i => (w.getD i (fun _ => flip d false)) x) =
      (g.inputs.map fun i => v.getD i false).map (flip d) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact lookup_dual d x w v h i
  rw [he]
  exact eval_dual d _ _ hg.1

theorem runGates_eval {α : Type} (d : Bool) (x : α) (gs : List Gate)
    (hgs : ∀ g ∈ gs, gateShape g) (w : List (Signal α)) (v : List Bool)
    (h : w.map (· x) = v.map (flip d)) :
    (runGates d w gs).map (· x) = (Circuit.wires ⟨gs, 0⟩ v).map (flip d) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change (runGates d (extend d w g) gs).map (· x) =
      (Circuit.wires ⟨gs, 0⟩
        (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).map (flip d)
    apply ih (fun g hg => hgs g (by simp [hg]))
    simp only [extend, List.map_append, List.map_cons, List.map_nil, h]
    rw [gateFn_eval d x w v h g (hgs g (by simp))]

theorem flatCircuit {α : Type} (d : Bool) (gates : List Gate) (out : ℕ)
    (hgs : ∀ g ∈ gates, gateShape g) (raw base : List (Signal α))
    (inputs : α → List Bool)
    (hrow : ∀ x, raw.map (· x) = (inputs x).map (flip d))
    (h : ∀ f ∈ raw, ready base f) :
    ∃ p, wellRun base.length p ∧
      ands p ≤ gates.countP (fun g => isAnd (flipOp d g.op)) ∧
      nots p ≤ gates.countP (fun g => isNot (flipOp d g.op)) ∧
      ready (run base p) (fun x => flip d (Circuit.eval ⟨gates, out⟩ (inputs x))) := by
  obtain ⟨p, hp, ha, hn, hr⟩ := flatten d gates hgs raw base h
  refine ⟨p, hp, ha, hn, ?_⟩
  have he : (fun x => flip d (Circuit.eval ⟨gates, out⟩ (inputs x))) =
      (runGates d raw gates).getD out (fun _ => flip d false) := by
    funext x
    symm
    exact lookup_dual d x _ _ (runGates_eval d x gates hgs _ _ (hrow x)) out
  rw [he]
  exact lookup_ready hr d out


def amongAnd (i : ℕ) (p : List Instruction) : Prop :=
  ∃ s ∈ p, s.1 = false ∧ i ∈ s.2.1 ++ s.2.2

private theorem port_mono {α : Type} (w : List (Signal α)) (js : List ℕ) (a b : α)
    (h : ∀ j ∈ js, w.getD j zero a = true → w.getD j zero b = true) :
    port w js a = true → port w js b = true := by
  intro he
  obtain ⟨j, hj, he⟩ := List.any_eq_true.1 he
  exact List.any_eq_true.2 ⟨j, hj, h j hj he⟩

private theorem getD_snoc_other {α : Type} (w : List α) (e d : α)
    {i : ℕ} (hn : i ≠ w.length) : (w ++ [e]).getD i d = w.getD i d := by
  by_cases hlt : i < w.length
  · exact getD_append_left _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

private theorem snoc_comp_except {α : Type} (w : List (Signal α)) (a b : α)
    (i : ℕ) (f : Signal α)
    (hw : ∀ j, j ≠ i → w.getD j zero a = true → w.getD j zero b = true)
    (hf : f a = true → f b = true) :
    ∀ j, j ≠ i → (w ++ [f]).getD j zero a = true → (w ++ [f]).getD j zero b = true := by
  intro j hj ht
  by_cases h : j = w.length
  · subst j
    have ht' : f a = true := by simpa [List.getD] using ht
    simpa [List.getD] using hf ht'
  · rw [getD_snoc_other _ _ _ h] at ht ⊢
    exact hw j hj ht

private theorem run_no_not_comp {α : Type} (a b : α) (i : ℕ) (p : List Instruction)
    (hn : nots p = 0) (ha : ¬amongAnd i p) (w : List (Signal α))
    (hw : ∀ j, j ≠ i → w.getD j zero a = true → w.getD j zero b = true) :
    ∀ j, j ≠ i → (run w p).getD j zero a = true → (run w p).getD j zero b = true := by
  induction p generalizing w with
  | nil => exact hw
  | cons s p ih =>
    have hs : s.1 = false := by
      cases h : s.1 <;> simp_all [nots, List.countP_cons]
    have hnp : nots p = 0 := by simpa [nots, List.countP_cons, hs] using hn
    have hap : ¬amongAnd i p := by
      rintro ⟨v, hv, hvN, hvI⟩
      exact ha ⟨v, by simp [hv], hvN, hvI⟩
    have hl : i ∉ s.2.1 := fun h => ha ⟨s, by simp, hs, by simp [h]⟩
    have hr : i ∉ s.2.2 := fun h => ha ⟨s, by simp, hs, by simp [h]⟩
    change ∀ j, j ≠ i →
      (run (w ++ [instr w s]) p).getD j zero a = true →
      (run (w ++ [instr w s]) p).getD j zero b = true
    apply ih hnp hap
    apply snoc_comp_except _ _ _ _ _ hw
    simp only [instr, hs, Bool.false_eq_true, ite_false, Bool.and_eq_true]
    intro h
    exact ⟨port_mono w _ a b (fun j hj => hw j (fun he => hl (he ▸ hj))) h.1,
        port_mono w _ a b (fun j hj => hw j (fun he => hr (he ▸ hj))) h.2⟩

private theorem run_no_not_agree {α : Type} (a b : α) (i : ℕ) (p : List Instruction)
    (hn : nots p = 0) (ha : ¬amongAnd i p) (w : List (Signal α))
    (hw : ∀ j, j ≠ i → w.getD j zero a = w.getD j zero b) :
    ∀ j, j ≠ i → (run w p).getD j zero a = (run w p).getD j zero b := by
  intro j hj
  rw [Bool.eq_iff_iff]
  exact ⟨run_no_not_comp a b i p hn ha w (fun j hj he => by simpa only [← hw j hj] using he) j hj,
    run_no_not_comp b a i p hn ha w (fun j hj he => by simpa only [hw j hj] using he) j hj⟩

private theorem nots_append (p q : List Instruction) : nots (p ++ q) = nots p + nots q :=
  List.countP_append

private theorem nots_cons (s : Instruction) (q : List Instruction) :
    nots (s :: q) = nots q + s.1.toNat := by
  cases hs : s.1 <;> simp [nots, List.countP_cons, hs]

private theorem nots_zero {p : List Instruction} (h : ¬∃ s ∈ p, s.1 = true) :
    nots p = 0 := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    have hs : s.1 = false := by
      cases he : s.1
      · rfl
      · exact False.elim (h ⟨s, by simp, he⟩)
    rw [nots_cons, hs, ih (fun ⟨s, hs, h'⟩ => h ⟨s, by simp [hs], h'⟩)]
    rfl

theorem positive_read_of_flat {α : Type} (w : List (Signal α)) (p : List Instruction)
    (out : List ℕ) (a b : α) (i : ℕ) (hi : i < w.length)
    (hn : nots p ≤ 1) (ho : i ∉ out)
    (hw : ∀ j, j ≠ i → w.getD j zero a = w.getD j zero b)
    (hle : w.getD i zero a = true → w.getD i zero b = true)
    (hh : port (run w p) out a = false ∧ port (run w p) out b = true) :
    amongAnd i p := by
  by_contra ha
  have hc : ∀ j, j ≠ i → (run w p).getD j zero b = true → (run w p).getD j zero a = true := by
    by_cases he : ∃ s ∈ p, s.1 = true
    · obtain ⟨s, hs, hst⟩ := he
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hs
      have hn' : nots pre + (nots post + 1) ≤ 1 := by
        simpa only [nots_append, nots_cons, hst, Bool.toNat_true] using hn
      have hpre : nots pre = 0 := by omega
      have hpost : nots post = 0 := by omega
      have hda : ¬amongAnd i pre := fun ⟨g, hg, hN, hI⟩ =>
        ha ⟨g, by simp [hg], hN, hI⟩
      have hdb : ¬amongAnd i post := fun ⟨g, hg, hN, hI⟩ =>
        ha ⟨g, by simp [hg], hN, hI⟩
      have heq := run_no_not_agree a b i pre hpre hda w hw
      have hmono : ∀ j, (run w pre).getD j zero a = true → (run w pre).getD j zero b = true := by
        intro j h
        by_cases hj : j = i
        · subst j
          obtain ⟨t, ht⟩ := run_wires_append w pre
          rw [ht, getD_append_left _ _ _ hi] at h ⊢
          exact hle h
        · rwa [← heq j hj]
      rw [run_append]
      change ∀ j, j ≠ i →
        (run (run w pre ++ [instr (run w pre) s]) post).getD j zero b = true →
        (run (run w pre ++ [instr (run w pre) s]) post).getD j zero a = true
      apply run_no_not_comp b a i post hpost hdb
      apply snoc_comp_except
      · exact fun j hj he => by simpa only [heq j hj] using he
      · simp only [instr, hst, ite_true]
        have hv := port_mono (run w pre) s.2.1 a b (fun j _ => hmono j)
        cases ha : port (run w pre) s.2.1 a <;>
          cases hb : port (run w pre) s.2.1 b <;> simp_all
    · exact run_no_not_comp b a i p (nots_zero he) ha w
        (fun j hj he => by simpa only [hw j hj] using he)
  have hh' := port_mono (run w p) out b a
    (fun j hj => hc j (fun he => ho (he ▸ hj))) hh.2
  rw [hh.1] at hh'
  contradiction


private theorem port_ready {α : Type} {raw ws : List (Signal α)} (js : List ℕ)
    (h : ∀ f ∈ raw, ready ws f) : ready ws (port raw js) := by
  have h' : ∀ f ∈ js.map (raw.getD · zero), ready ws f := by
    intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
    by_cases hlt : i < raw.length
    · apply h
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Or.inr (read_zero _)
  change ready ws (fun x => js.any fun i => raw.getD i zero x)
  simpa only [List.any_map, Function.comp_def] using ready_union_list _ h'

private theorem port_one {α : Type} {w : List (Signal α)} {i : ℕ}
    (hi : w.getD i zero = one) {js : List ℕ} (h : i ∈ js) : port w js = one := by
  funext x
  apply List.any_eq_true.2
  exact ⟨i, h, by rw [hi]; rfl⟩

def retained (i : ℕ) (s : Instruction) : Bool :=
  !s.1 && !(s.2.1 ++ s.2.2).contains i

def retainedAnds (i : ℕ) (p : List Instruction) : ℕ :=
  p.countP (retained i)

private theorem retainedAnds_cons (i : ℕ) (s : Instruction) (p : List Instruction) :
    retainedAnds i (s :: p) = retainedAnds i p + (retained i s).toNat := by
  cases h : retained i s <;> simp [retainedAnds, h]

private theorem ands_cons (s : Instruction) (p : List Instruction) :
    ands (s :: p) = ands p + (!s.1).toNat := by
  cases h : s.1 <;> simp [ands, h]

private theorem retained_head (i : ℕ) (s : Instruction) :
    (retained i s).toNat ≤ (!s.1).toNat := by
  cases h : s.1 <;> cases h' : (s.2.1 ++ s.2.2).contains i <;>
    simp only [retained, h, h', Bool.not_true, Bool.not_false, Bool.and_true,
      Bool.and_false, Bool.true_and, Bool.false_and, Bool.toNat_true, Bool.toNat_false] <;> decide

private theorem retained_le (i : ℕ) (p : List Instruction) :
    retainedAnds i p ≤ ands p := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    rw [retainedAnds_cons, ands_cons]
    exact Nat.add_le_add ih (retained_head i s)

theorem retained_lt {i : ℕ} {p : List Instruction} (h : amongAnd i p) :
    retainedAnds i p + 1 ≤ ands p := by
  induction p with
  | nil => obtain ⟨s, h, _⟩ := h; simp at h
  | cons s p ih =>
    obtain ⟨t, ht, htf, hti⟩ := h
    rw [retainedAnds_cons, ands_cons]
    rcases List.mem_cons.1 ht with he | ht
    · subst t
      have he : (s.2.1 ++ s.2.2).contains i = true := List.contains_iff_mem.2 hti
      have hp := retained_le i p
      simp only [retained, htf, he, Bool.not_true, Bool.not_false, Bool.and_false,
        Bool.toNat_true, Bool.toNat_false, Nat.add_zero]
      omega
    · have hp := ih ⟨t, ht, htf, hti⟩
      have hs := retained_head i s
      omega

private theorem prepare_fixed_instr {α : Type} (raw ws : List (Signal α)) (i : ℕ)
    (hi : raw.getD i zero = one) (h : ∀ f ∈ raw, ready ws f)
    (s : Instruction) : ∃ q,
    wellRun ws.length q ∧ ands q ≤ (retained i s).toNat ∧ nots q ≤ s.1.toNat ∧
    ready (run ws q) (instr raw s) := by
  have ha := port_ready s.2.1 h
  have hb := port_ready s.2.2 h
  cases hs : s.1
  · by_cases hread : i ∈ s.2.1 ++ s.2.2
    · have htest := List.contains_iff_mem.2 hread
      have hr : (retained i s).toNat = 0 := by rw [retained, hs, htest]; rfl
      rw [hr]
      rcases List.mem_append.1 hread with he | he
      · refine ⟨[], trivial, by simp [ands], by simp [nots], ?_⟩
        simpa [instr, hs, run, port_one hi he, one] using hb
      · refine ⟨[], trivial, by simp [ands], by simp [nots], ?_⟩
        simpa [instr, hs, run, port_one hi he, one] using ha
    · have htest : (s.2.1 ++ s.2.2).contains i = false := by simpa using hread
      obtain ⟨q, hq, hA, hN, hR⟩ := prepare_and ws ha hb
      have he : (retained i s).toNat = 1 := by rw [retained, hs, htest]; rfl
      exact ⟨q, hq, he ▸ hA, by simp [hN], by simpa [instr, hs] using hR⟩
  · obtain ⟨q, hq, hA, hN, hR⟩ := prepare_not ws ha
    exact ⟨q, hq, by simp [hA], by simpa using hN, by simpa [instr, hs] using hR⟩

theorem flat_fixed_one {α : Type} (p : List Instruction) (raw ws : List (Signal α))
    (i : ℕ) (hi : i < raw.length) (hf : raw.getD i zero = one)
    (h : ∀ f ∈ raw, ready ws f) : ∃ q,
    wellRun ws.length q ∧ ands q ≤ retainedAnds i p ∧ nots q ≤ nots p ∧
    ∀ f ∈ run raw p, ready (run ws q) f := by
  induction p generalizing raw ws with
  | nil => exact ⟨[], trivial, le_refl _, le_refl _, h⟩
  | cons s p ih =>
    obtain ⟨q, hq, hA, hN, hR⟩ := prepare_fixed_instr raw ws i hf h s
    have hstep : ∀ f ∈ appendInstr raw s, ready (run ws q) f := by
      intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨t, ht⟩ := run_wires_append ws q
        rw [ht]
        exact ready_append (h f hf) t
      · simp only [List.mem_singleton] at hf
        exact hf ▸ hR
    have hi' : i < (appendInstr raw s).length := by simp [appendInstr]; omega
    have hf' : (appendInstr raw s).getD i zero = one := by
      rw [appendInstr, getD_append_left _ _ _ hi, hf]
    obtain ⟨r, hr, hAr, hNr, hRr⟩ := ih _ _ hi' hf' hstep
    refine ⟨q ++ r, wellRun_append hq (by rwa [run_length] at hr), ?_, ?_, ?_⟩
    · have eql : ands (q ++ r) = ands q + ands r := List.countP_append
      rw [eql, retainedAnds_cons, Nat.add_comm]
      exact Nat.add_le_add hAr hA
    · rw [nots_append, nots_cons]
      omega
    · change ∀ f ∈ run (appendInstr raw s) p, ready (run ws (q ++ r)) f
      simpa only [run_append] using hRr


def reparam {α β : Type} (w : List (Signal β)) (f : α → β) : List (Signal α) :=
  w.map (fun g => g ∘ f)

private theorem getD_reparam {α β : Type} (w : List (Signal β)) (f : α → β) (i : ℕ) :
    (reparam w f).getD i zero = (w.getD i zero) ∘ f :=
  List.getD_map w zero (n := i) (fun g => g ∘ f)

private theorem port_reparam {α β : Type} (w : List (Signal β)) (f : α → β) (is : List ℕ) :
    port (reparam w f) is = port w is ∘ f := by
  funext x
  simp only [port, getD_reparam, Function.comp_apply]

private theorem instr_reparam {α β : Type} (w : List (Signal β)) (f : α → β)
    (s : Instruction) : instr (reparam w f) s = instr w s ∘ f := by
  funext x
  cases hs : s.1 <;> simp [instr, hs, port_reparam, Function.comp_apply]

private theorem append_reparam {α β : Type} (w : List (Signal β)) (f : α → β)
    (s : Instruction) : appendInstr (reparam w f) s = reparam (appendInstr w s) f := by
  unfold appendInstr reparam
  rw [List.map_append, List.map_cons, List.map_nil]
  exact congrArg (fun g => reparam w f ++ [g]) (instr_reparam w f s)

theorem run_reparam {α β : Type} (w : List (Signal β)) (f : α → β)
    (p : List Instruction) : run (reparam w f) p = reparam (run w p) f := by
  induction p generalizing w with
  | nil => rfl
  | cons s p ih =>
    change run (appendInstr (reparam w f) s) p = reparam (run (appendInstr w s) p) f
    rw [append_reparam]
    exact ih _

theorem save_and_on_fixed_one {α β : Type} {w : List (Signal β)} {base : List (Signal α)}
    {f : Signal β} (p : List Instruction) (i : ℕ) (hi : i < w.length)
    (fix : α → β) (hf : (reparam w fix).getD i zero = one)
    (hread : ∀ g ∈ reparam w fix, ready base g)
    (hn : nots p ≤ 1) (hout : ready (run w p) f)
    (a b : β) (haz : ∃ z : α, f (fix z) = false)
    (hw : ∀ j, j ≠ i → w.getD j zero a = w.getD j zero b)
    (hwle : w.getD i zero a = true → w.getD i zero b = true)
    (hfa : f a = false) (hfb : f b = true) :
    ∃ q, wellRun base.length q ∧ ands q + 1 ≤ ands p ∧ nots q ≤ nots p ∧
      ready (run base q) (f ∘ fix) := by
  obtain ⟨z, hz⟩ := haz
  rcases hout with he | ⟨out, _, he⟩
  · rw [he] at hfa
    contradiction
  · have hfi : i ∉ out := by
      intro hin
      have hp' : port (run (reparam w fix) p) out = one := by
        apply port_one (i := i) _ hin
        obtain ⟨t, ht⟩ := run_wires_append (reparam w fix) p
        rw [ht, getD_append_left _ _ _ (by simpa [reparam] using hi), hf]
      rw [run_reparam, port_reparam] at hp'
      have hv : port (run w p) out (fix z) = true := congrFun hp' z
      have hh : f (fix z) = true := by rw [he]; exact hv
      rw [hz] at hh
      contradiction
    have hAnd := positive_read_of_flat w p out a b i hi hn hfi hw hwle
      ⟨by simpa [he] using hfa, by simpa [he] using hfb⟩
    obtain ⟨q, hq, ha, hN, hqR⟩ := flat_fixed_one p (reparam w fix) base i
      (by simpa [reparam] using hi) hf hread
    refine ⟨q, hq, by have hh := retained_lt hAnd; omega, hN, ?_⟩
    rw [he, ← port_reparam, ← run_reparam]
    exact port_ready out hqR


def basis (n : ℕ) : List (Signal (Fin n → Bool)) :=
  List.ofFn fun i x => x i

private theorem basis_read {n : ℕ} (i : Fin n) : ready (basis n) (fun x => x i) := by
  refine Or.inr ⟨[i.val], ?_, ?_⟩
  · simp [basis, i.isLt]
  · funext x
    simp [port, basis, List.getD, i.isLt]

private theorem basis_members {n : ℕ} : ∀ f ∈ basis n, ready (basis n) f := by
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
  exact basis_read i

private def edgeEndpoints : List ℕ :=
  [0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6]

def edgeTarget (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edgeEndpoints.length / 2,
    (List.ofFn x).getD (edgeEndpoints.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeEndpoints.getD (2*i+1) 0) false = true)

def putFalse0 (x : Fin 6 → Bool) : Fin 7 → Bool :=
  ![false, x 0, x 1, x 2, x 3, x 4, x 5]

def putTrue2 (x : Fin 6 → Bool) : Fin 7 → Bool :=
  ![x 0, x 1, true, x 2, x 3, x 4, x 5]

def putTrue4 (x : Fin 5 → Bool) : Fin 6 → Bool :=
  ![x 0, x 1, x 2, x 3, true, x 4]

def delete0Target : Signal (Fin 6 → Bool) := edgeTarget ∘ putFalse0
def dualTarget (x : Fin 7 → Bool) : Bool := !(edgeTarget (fun i => !(x i)))
def dualDelete2Target : Signal (Fin 6 → Bool) := dualTarget ∘ putTrue2
def dualGemTarget : Signal (Fin 5 → Bool) := dualDelete2Target ∘ putTrue4

def lowerFor {n : ℕ} (f : Signal (Fin n → Bool)) (k : ℕ) : Prop :=
  ∀ p, wellRun n p → nots p ≤ 1 → ready (run (basis n) p) f → k ≤ ands p

private theorem ready_false0 : ∀ g ∈ reparam (basis 7) putFalse0, ready (basis 6) g := by
  intro g hg
  change g ∈ [zero, (fun x => x 0), (fun x => x 1), (fun x => x 2),
    (fun x => x 3), (fun x => x 4), (fun x => x 5)] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (read_zero _)
  all_goals exact basis_read _

private theorem ready_true2 : ∀ g ∈ reparam (basis 7) putTrue2, ready (basis 6) g := by
  intro g hg
  change g ∈ [(fun x => x 0), (fun x => x 1), one, (fun x => x 2),
    (fun x => x 3), (fun x => x 4), (fun x => x 5)] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
  | exact Or.inl rfl
  | exact basis_read _

private theorem ready_true4 : ∀ g ∈ reparam (basis 6) putTrue4, ready (basis 5) g := by
  intro g hg
  change g ∈ [(fun x => x 0), (fun x => x 1), (fun x => x 2),
    (fun x => x 3), one, (fun x => x 4)] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> first
  | exact Or.inl rfl
  | exact basis_read _

private def a2 : Fin 7 → Bool := ![true, true, false, true, false, true, true]
private def b2 : Fin 7 → Bool := ![true, true, true, true, false, true, true]
private def a4 : Fin 6 → Bool := ![false, true, true, true, false, true]
private def b4 : Fin 6 → Bool := ![false, true, true, true, true, true]

private theorem a2_b2_agree (j : ℕ) (h : j ≠ 2) :
    (basis 7).getD j zero a2 = (basis 7).getD j zero b2 := by
  by_cases hj : j < 7
  · interval_cases j <;> first | contradiction | rfl
  · rw [List.getD_eq_default _ _ (by simp [basis]; omega)]
    rfl

private theorem a4_b4_agree (j : ℕ) (h : j ≠ 4) :
    (basis 6).getD j zero a4 = (basis 6).getD j zero b4 := by
  by_cases hj : j < 6
  · interval_cases j <;> first | contradiction | rfl
  · rw [List.getD_eq_default _ _ (by simp [basis]; omega)]
    rfl

set_option maxRecDepth 10000 in
theorem restrict_dual_to_gem (p : List Instruction) (hn : nots p ≤ 1)
    (he : ready (run (basis 7) p) dualTarget) : ∃ q,
    wellRun 5 q ∧ ands q + 2 ≤ ands p ∧ nots q ≤ nots p ∧ ready (run (basis 5) q) dualGemTarget := by
  obtain ⟨q, hq, hA, hN, hR⟩ :=
    save_and_on_fixed_one p 2 (by simp [basis]) putTrue2 (by rfl)
      ready_true2 hn he a2 b2 ⟨![false, true, false, true, true, true], by decide +kernel⟩
      a2_b2_agree (by decide) (by decide +kernel) (by decide +kernel)
  obtain ⟨r, hr, hAr, hNr, hRr⟩ :=
    save_and_on_fixed_one q 4 (by simp [basis]) putTrue4 (by rfl)
      ready_true4 (by omega) hR a4 b4 ⟨![false, true, false, true, true], by decide +kernel⟩
      a4_b4_agree (by decide) (by decide +kernel) (by decide +kernel)
  exact ⟨r, by simpa [basis] using hr, by omega, by omega, hRr⟩

private theorem not_op_flip (d : Bool) (op : GateOp) : isNot (flipOp d op) = isNot op := by
  cases d <;> cases op <;> rfl

private theorem and_op_flip_true (op : GateOp) :
    isAnd (flipOp true op) = (match op with | .or => true | _ => false) := by
  cases op <;> rfl

theorem lower_and_from_delete0 (small : lowerFor delete0Target 4) (gs : List Gate) (o : ℕ)
    (hgs : ∀ g ∈ gs, gateShape g)
    (hn : gs.countP (fun g => isNot g.op) ≤ 1)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeTarget x) :
    4 ≤ gs.countP (fun g => isAnd g.op) := by
  obtain ⟨p, hp, hA, hN, hR⟩ :=
    flatCircuit false gs o hgs (reparam (basis 7) putFalse0) (basis 6)
      (fun x => List.ofFn (putFalse0 x)) (by intro x; rfl) ready_false0
  have hre : (fun x => flip false (Circuit.eval ⟨gs, o⟩ (List.ofFn (putFalse0 x)))) =
      delete0Target := by
    funext x
    exact he _
  rw [hre] at hR
  have hp' : wellRun 6 p := by simpa [basis] using hp
  have hn' : nots p ≤ 1 := by simp only [not_op_flip] at hN; omega
  have hA' : 4 ≤ ands p := small p hp' hn' hR
  exact le_trans hA' hA

theorem lower_or_from_gem (small : lowerFor dualGemTarget 5) (gs : List Gate) (o : ℕ)
    (hgs : ∀ g ∈ gs, gateShape g)
    (hn : gs.countP (fun g => isNot g.op) ≤ 1)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeTarget x) :
    7 ≤ gs.countP (fun g => match g.op with | .or => true | _ => false) := by
  obtain ⟨p, hp, hA, hN, hR⟩ :=
    flatCircuit true gs o hgs (basis 7) (basis 7)
      (fun x => List.ofFn (fun i => !(x i))) (by
        intro x
        simp [basis, List.map_ofFn, Function.comp_def, flip]) basis_members
  have hre : (fun x => flip true (Circuit.eval ⟨gs, o⟩ (List.ofFn (fun i => !(x i))))) =
      dualTarget := by
    funext x
    rw [he]
    rfl
  rw [hre] at hR
  have hn' : nots p ≤ 1 := by simp only [not_op_flip] at hN; omega
  obtain ⟨q, hq, hqA, hqN, hqR⟩ := restrict_dual_to_gem p hn' hR
  have h := small q hq (by omega) hqR
  simp only [and_op_flip_true] at hA
  omega


open PEqualNP.CircuitLowerBounds

private def endpoints : List ℕ :=
  [0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6]

def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < endpoints.length / 2,
    (List.ofFn x).getD (endpoints.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (endpoints.getD (2 * i + 1) 0) false = true)

def mono12 : List Gate :=
  [⟨.or, [0, 1]⟩,      -- 7
   ⟨.or, [0, 2]⟩,      -- 8
   ⟨.or, [3, 7]⟩,      -- 9
   ⟨.or, [2, 9]⟩,      -- 10
   ⟨.or, [4, 9]⟩,      -- 11
   ⟨.and, [3, 7]⟩,     -- 12
   ⟨.and, [4, 8]⟩,     -- 13
   ⟨.and, [5, 10]⟩,    -- 14
   ⟨.and, [6, 11]⟩,    -- 15
   ⟨.or, [12, 13]⟩,    -- 16
   ⟨.or, [14, 15]⟩,    -- 17
   ⟨.or, [16, 17]⟩]    -- 18

theorem mono12_len : mono12.length = 12 := rfl

theorem mono12_allowed : ∀ g ∈ mono12,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono12, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mono12_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨mono12, 18⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem replacement_if_size_ge_12 (gates : List Gate) (h : 12 ≤ gates.length) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = target x :=
  ⟨mono12, 18, mono12_allowed, by simpa [mono12_len] using h, mono12_eval⟩


def isOr : GateOp → Bool
  | .or => true
  | _ => false

def AndCount (gates : List Gate) : ℕ := gates.countP (fun g => isAnd g.op)
def OrCount (gates : List Gate) : ℕ := gates.countP (fun g => isOr g.op)
def NotCount (gates : List Gate) : ℕ := gates.countP (fun g => isNot g.op)

def Allowed (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def OneNot (gates : List Gate) : Prop :=
  ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i = j

def Computes (gates : List Gate) (o : ℕ) : Prop :=
  ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target x


private theorem is_not_iff (op : GateOp) : isNot op = true ↔ op = .not := by
  cases op <;> simp [isNot]

theorem one_not_count (gs : List Gate) (h : OneNot gs) : NotCount gs ≤ 1 := by
  induction gs with
  | nil => simp [NotCount]
  | cons g rest ih =>
    have htail : OneNot rest := by
      intro i j hi hj
      have hij := h i.succ j.succ (by simpa using hi) (by simpa using hj)
      exact Fin.succ_inj.1 hij
    by_cases hg : g.op = .not
    · have hnone : rest.countP (fun g => isNot g.op) = 0 := by
        apply List.countP_eq_zero.2
        intro s hs ht
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
        have hh := h ⟨0, by simp⟩ (Fin.succ ⟨i, hi⟩)
          (by simpa using hg) (by simpa using (is_not_iff _).1 ht)
        have hh' := congrArg Fin.val hh
        simp at hh'
      change (g :: rest).countP (fun g => isNot g.op) ≤ 1
      rw [List.countP_cons, hnone, (is_not_iff _).2 hg]
      decide
    · have hn : isNot g.op = false := by
        cases he : isNot g.op
        · rfl
        · exact False.elim (hg ((is_not_iff _).1 he))
      have hi := ih htail
      simpa [NotCount, hn] using hi

theorem countPartition (gs : List Gate) (h : Allowed gs) :
    AndCount gs + OrCount gs + NotCount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := (h g (by simp)).1
    have he := ih (fun u hu => h u (by simp [hu]))
    have ha : AndCount (g :: gs) = AndCount gs + (isAnd g.op).toNat := by
      unfold AndCount
      cases hg : isAnd g.op <;> simp [hg]
    have ho : OrCount (g :: gs) = OrCount gs + (isOr g.op).toNat := by
      unfold OrCount
      cases hg : isOr g.op <;> simp [hg]
    have hn : NotCount (g :: gs) = NotCount gs + (isNot g.op).toNat := by
      unfold NotCount
      cases hg : isNot g.op <;> simp [hg]
    have sum : (isAnd g.op).toNat + (isOr g.op).toNat + (isNot g.op).toNat = 1 := by
      rcases hg with hg | hg | hg <;> simp [hg, isAnd, isOr, isNot]
    rw [ha, ho, hn, List.length_cons]
    omega

theorem not_uses_count (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) : 1 ≤ NotCount gs := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases hg : g.op = .not
    · simp [NotCount, isNot, hg]
    · rcases h with ⟨u, hu, hop⟩
      have h' : u ∈ gs := by
        rcases List.mem_cons.1 hu with rfl | hu
        · exact False.elim (hg hop)
        · exact hu
      have := ih ⟨u, h', hop⟩
      unfold NotCount at *
      rw [List.countP_cons]
      omega

theorem replace_from_two_counts
    (andLower : ∀ gs o, Allowed gs → OneNot gs → Computes gs o → 4 ≤ AndCount gs)
    (orLower : ∀ gs o, Allowed gs → OneNot gs → Computes gs o → 7 ≤ OrCount gs) :
    ∀ gs o, Allowed gs → OneNot gs → Computes gs o →
    ∃ (gs' : List Gate) (o' : ℕ),
      (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ Computes gs' o' := by
  intro gs o ha hn hc
  by_cases h : ∃ g ∈ gs, g.op = .not
  · apply replacement_if_size_ge_12 gs
    have hAnd := andLower gs o ha hn hc
    have hOr := orLower gs o ha hn hc
    have hNot := not_uses_count gs h
    have hl := countPartition gs ha
    omega
  · refine ⟨gs, o, ?_, le_rfl, hc⟩
    intro g hg
    have hok := ha g hg
    obtain ⟨hop | hop | hop, hlo⟩ := hok
    · exact ⟨Or.inl hop, hlo⟩
    · exact ⟨Or.inr hop, hlo⟩
    · exact False.elim (h ⟨g, hg, hop⟩)


theorem exact_negation_from_counts
    (andLower : ∀ gs o, Allowed gs → OneNot gs → Computes gs o → 4 ≤ AndCount gs)
    (orLower : ∀ gs o, Allowed gs → OneNot gs → Computes gs o → 7 ≤ OrCount gs) :
    ¬ (¬ (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true))) := by
  intro contrary
  exact contrary (replace_from_two_counts andLower orLower)


theorem reduced_cases_imply_exact_negation
    (lowerDelete : lowerFor delete0Target 4) (lowerGem : lowerFor dualGemTarget 5) :
    ¬ (¬ (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true))) := by
  apply exact_negation_from_counts
  · intro gs o hg hu hc
    exact lower_and_from_delete0 lowerDelete gs o hg (one_not_count gs hu) hc
  · intro gs o hg hu hc
    exact lower_or_from_gem lowerGem gs o hg (one_not_count gs hu) hc


def increasing {α : Type} (rel : α → α → Prop) (s : Signal α) : Prop :=
  ∀ x y, rel x y → s x = true → s y = true

def decreasing {α : Type} (rel : α → α → Prop) (s : Signal α) : Prop :=
  ∀ x y, rel x y → s y = true → s x = true

private theorem port_ascending {α : Type} {rel : α → α → Prop}
    {w : List (Signal α)} (h : ∀ f ∈ w, increasing rel f) (is : List ℕ) :
    increasing rel (port w is) := by
  intro x y hxy
  apply port_mono
  intro i _
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _) x y hxy
  · rw [List.getD_eq_default _ _ (by omega)]
    exact id

private theorem run_ascending {α : Type} {rel : α → α → Prop}
    (p : List Instruction) (w : List (Signal α)) (h : ∀ f ∈ w, increasing rel f)
    (hn : nots p = 0) : ∀ f ∈ run w p, increasing rel f := by
  induction p generalizing w with
  | nil => exact h
  | cons s p ih =>
    have hs : s.1 = false := by cases hs : s.1 <;> simp_all [nots, List.countP_cons]
    apply ih (appendInstr w s) _ (by simpa [nots, hs, List.countP_cons] using hn)
    intro f hf
    rcases List.mem_append.1 hf with hold | hnew
    · exact h f hold
    · obtain rfl := List.mem_singleton.1 hnew
      intro x y hxy
      simp only [instr, hs, Bool.false_eq_true, ite_false, Bool.and_eq_true]
      exact fun hh => ⟨port_ascending h _ x y hxy hh.1, port_ascending h _ x y hxy hh.2⟩

def isZeroAt {α : Type} (x0 : α) (s : Signal α) := s x0 = false

private theorem port_zeroAt {α : Type} {x0 : α} {w : List (Signal α)}
    (hw : ∀ f ∈ w, isZeroAt x0 f) (is : List ℕ) : isZeroAt x0 (port w is) := by
  change is.any (fun i => w.getD i zero x0) = false
  rw [List.any_eq_false]
  intro i _
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    have hh : w[i] x0 = false := hw _ (List.getElem_mem _)
    simp [hh]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [zero]

private theorem run_zeroAt {α : Type} {x0 : α} (p : List Instruction)
    (w : List (Signal α)) (hw : ∀ f ∈ w, isZeroAt x0 f)
    (hn : nots p = 0) : ∀ f ∈ run w p, isZeroAt x0 f := by
  induction p generalizing w with
  | nil => exact hw
  | cons s p ih =>
    have hs : s.1 = false := by cases hs : s.1 <;> simp_all [nots, List.countP_cons]
    apply ih (appendInstr w s) _ (by simpa [nots, hs, List.countP_cons] using hn)
    intro f hf
    rcases List.mem_append.1 hf with hold | hnew
    · exact hw f hold
    · obtain rfl := List.mem_singleton.1 hnew
      change instr w s x0 = false
      simp [instr, hs, show port w s.2.1 x0 = false from port_zeroAt hw _]

private theorem replay_ands {α : Type} (p : List Instruction) (raw base : List (Signal α))
    (hr : ∀ f ∈ raw, ready base f) (hn : nots p = 0) :
    ∃ ps, wellRun base.length ps ∧ ps.length ≤ ands p ∧ nots ps = 0 ∧
      ∀ f ∈ run raw p, ready (run base ps) f := by
  induction p generalizing raw base with
  | nil => exact ⟨[], trivial, by simp [ands], rfl, hr⟩
  | cons s p ih =>
    have hs : s.1 = false := by cases hs : s.1 <;> simp_all [nots, List.countP_cons]
    have hn' : nots p = 0 := by simpa [nots, hs, List.countP_cons] using hn
    obtain ⟨q,hq,hqa,hqn,hqR⟩ := prepare_and base (port_ready s.2.1 hr) (port_ready s.2.2 hr)
    have ext : ∀ f ∈ appendInstr raw s, ready (run base q) f := by
      intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨t, ht⟩ := run_wires_append base q
        rw [ht]
        exact ready_append (hr _ hf) t
      · obtain rfl := List.mem_singleton.1 hf
        simpa only [instr, hs, Bool.false_eq_true, ite_false] using hqR
    obtain ⟨r,hrw,hrl,hrn,hrR⟩ := ih (appendInstr raw s) (run base q) ext hn'
    have qpart : ands q + nots q = q.length := by
      clear hqa hqn hq hqR ext hrw hrl hrn hrR
      induction q with
      | nil => rfl
      | cons i ls iq =>
        cases hi : i.1 <;> simp_all [ands,nots,List.countP_cons,hi] <;> omega
    refine ⟨q ++ r, wellRun_append hq (by rwa [run_length] at hrw), ?_, ?_, ?_⟩
    · simp only [List.length_append]
      have hp : ands (s :: p) = ands p + 1 := by simp [ands,List.countP_cons,hs]
      omega
    · rw [nots_append,hqn,hrn]
    · change ∀ f ∈ run (appendInstr raw s) p, ready (run base (q ++ r)) f
      rw [run_append]; exact hrR

def coordLe {n : ℕ} (x y : Fin n → Bool) : Prop := ∀ i, x i = true → y i = true

theorem move_not_to_input {n : ℕ} (p : List Instruction) (f : Signal (Fin n → Bool))
    (hn : nots p ≤ 1) (hf : ready (run (basis n) p) f) :
    ∃ u : Signal (Fin n → Bool), decreasing coordLe u ∧ u (fun _ => false) = true ∧
    ∃ m, wellRun (n+1) m ∧ m.length ≤ ands p ∧ nots m = 0 ∧
      ready (run (basis n ++ [u]) m) f := by
  have original (u : Signal (Fin n → Bool)) : ∀ g ∈ basis n, ready (basis n ++ [u]) g := by
    intro g hg
    exact ready_append (basis_members g hg) _
  by_cases hp : ∃ s ∈ p, s.1 = true
  · obtain ⟨s, hsp,hs⟩ := hp
    obtain ⟨pre,post,rfl⟩ := List.append_of_mem hsp
    have nh : nots pre + (nots post + 1) ≤ 1 := by
      simpa only [nots_append, nots_cons,hs,Bool.toNat_true] using hn
    have npre : nots pre = 0 := by omega
    have npost : nots post = 0 := by omega
    let bw := run (basis n) pre
    let u := instr bw s
    have asc : ∀ g ∈ bw, increasing coordLe g := by
      apply run_ascending pre _ _ npre
      intro g hg
      obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hg
      exact fun x y hxy => hxy i
    have desc : decreasing coordLe u := by
      intro x y hxy
      simp only [u,instr,hs,ite_true,Bool.not_eq_true']
      intro hy
      cases hx : port bw s.2.1 x
      · rfl
      · have ht := port_ascending asc s.2.1 x y hxy hx
        simp_all
    have zu : u (fun _ => false) = true := by
      have hz : ∀ g ∈ bw, isZeroAt (fun _ => false) g := by
        apply run_zeroAt pre _ _ npre
        intro g hg
        obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hg
        rfl
      simp [u,instr,hs,show port bw s.2.1 (fun _ => false) = false from port_zeroAt hz _]
    obtain ⟨q,hqw,hql,hqn,hqR⟩ := replay_ands pre (basis n) _ (original u) npre
    have hr : ∀ g ∈ appendInstr bw s, ready (run (basis n ++ [u]) q) g := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hqR _ hg
      · obtain rfl := List.mem_singleton.1 hg
        obtain ⟨tail,ht⟩ := run_wires_append (basis n ++ [u]) q
        rw [ht]
        exact ready_append (Or.inr (read_last _ u)) _
    obtain ⟨r,hrw,hrl,hrn,hrR⟩ := replay_ands post _ _ hr npost
    refine ⟨u,desc,zu,q ++ r,?_,?_,?_,?_⟩
    · simpa [basis] using wellRun_append hqw (by rwa [run_length] at hrw)
    · have ha : ands (pre ++ s::post) = ands pre + ands post := by
        simp [ands,List.countP_cons,hs]
      simp only [List.length_append,ha]; omega
    · rw [nots_append,hqn,hrn]
    · rw [run_append] at hf ⊢
      rcases hf with hf | ⟨is,_,hf⟩
      · exact Or.inl hf
      · rw [hf]
        exact port_ready is hrR
  · obtain ⟨q,hq,hl,hqn,hR⟩ := replay_ands p (basis n) _ (original one) (nots_zero hp)
    refine ⟨one,fun _ _ _ => id,rfl,q, by simpa [basis] using hq,hl,hqn,?_⟩
    rcases hf with hf | ⟨is,_,hf⟩
    · exact Or.inl hf
    · rw [hf]; exact port_ready is hR


def selectPort {α : Type} (w : List (Signal α)) (sel : ℕ → Bool) : Signal α :=
  port w ((List.range w.length).filter sel)

private theorem selectPort_contains {α : Type} (w : List (Signal α)) (js : List ℕ) :
    selectPort w js.contains = port w js := by
  funext x
  unfold selectPort port
  rw [Bool.eq_iff_iff,List.any_eq_true,List.any_eq_true]
  constructor
  · rintro ⟨i,hi,hv⟩
    exact ⟨i, by simpa using (List.mem_filter.1 hi).2, hv⟩
  · rintro ⟨i,hi,hv⟩
    have hlt : i < w.length := by
      by_contra h
      rw [List.getD_eq_default _ _ (by omega)] at hv
      contradiction
    exact ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hlt,by simpa using hi⟩, hv⟩

abbrev Selectors := ℕ → Bool → ℕ → Bool

def evalLayers {α : Type} : ℕ → Selectors → List (Signal α) → List (Signal α)
  | 0, _, w => w
  | k+1, sels, w =>
    let v := fun x => selectPort w (sels 0 false) x && selectPort w (sels 0 true) x
    evalLayers k (fun i => sels (i+1)) (w ++ [v])

private theorem evalLayers_appends {α : Type} (k : ℕ) (s : Selectors) (w : List (Signal α)) :
    ∃ tail, evalLayers k s w = w ++ tail := by
  induction k generalizing s w with
  | zero => exact ⟨[], by simp [evalLayers]⟩
  | succ k ih =>
    let v := fun x => selectPort w (s 0 false) x && selectPort w (s 0 true) x
    obtain ⟨t,h⟩ := ih (fun i => s (i+1)) (w ++ [v])
    exact ⟨v :: t,by simpa [evalLayers, v, List.append_assoc] using h⟩

theorem fill_ands {α : Type} (p : List Instruction) (k : ℕ) (w : List (Signal α))
    (hk : p.length ≤ k) (hn : nots p = 0) :
    ∃ sels : Selectors, ∃ tail, evalLayers k sels w = run w p ++ tail := by
  induction p generalizing w k with
  | nil =>
    obtain ⟨t,h⟩ := evalLayers_appends k (fun _ _ _ => false) w
    exact ⟨_,t,h⟩
  | cons s p ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hs : s.1 = false := by cases hs : s.1 <;> simp_all [nots]
      have hn' : nots p = 0 := by simpa [nots,hs] using hn
      obtain ⟨ss,t,h⟩ := ih k (appendInstr w s) (by simpa using hk) hn'
      let picks : Selectors
        | 0, false => s.2.1.contains
        | 0, true => s.2.2.contains
        | j+1, b => ss j b
      refine ⟨picks,t,?_⟩
      change evalLayers k ss (w ++ [fun x => selectPort w s.2.1.contains x &&
        selectPort w s.2.2.contains x]) = run (appendInstr w s) p ++ t
      simpa only [selectPort_contains,appendInstr,instr,hs,Bool.false_eq_true,ite_false] using h

def tableEval {n : ℕ} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors)
    (out : ℕ → Bool) : Signal (Fin n → Bool) :=
  selectPort (evalLayers k s (basis n ++ [u])) out

theorem small_program_gives_table {n k : ℕ} (p : List Instruction) (f : Signal (Fin n → Bool))
    (hn : nots p ≤ 1) (hf : ready (run (basis n) p) f) (hk : ands p ≤ k)
    (hf0 : f (fun _ => false) = false) :
    ∃ u : Signal (Fin n → Bool), decreasing coordLe u ∧ u (fun _ => false) = true ∧
      ∃ (s : Selectors) (out : ℕ → Bool), tableEval k u s out = f := by
  obtain ⟨u,hd,hu,m,_,hm,hnm,hout⟩ := move_not_to_input p f hn hf
  obtain ⟨s,t,ht⟩ := fill_ands m k (basis n ++ [u]) (by omega) hnm
  have ext := ready_append hout t
  rw [← ht] at ext
  rcases ext with he | ⟨o,_,he⟩
  · rw [he] at hf0
    contradiction
  · exact ⟨u,hd,hu,s,o.contains,by simpa only [tableEval,selectPort_contains] using he.symm⟩

def inputRow (n row : ℕ) : Fin n → Bool := fun j => row.testBit j.val

def sampleDoesNotMatch (n k : ℕ) (yes no : List ℕ) : Prop :=
  ∀ (u : Signal (Fin n → Bool)), decreasing coordLe u → u (fun _ => false) = true →
    ∀ (s : Selectors) (out : ℕ → Bool),
      (∀ r ∈ yes, tableEval k u s out (inputRow n r) = true) →
      (∀ r ∈ no, tableEval k u s out (inputRow n r) = false) → False

theorem sample_implies_lower {n k : ℕ} {f : Signal (Fin n → Bool)}
    {yes no : List ℕ} (hz : f (fun _ => false) = false)
    (hy : ∀ r ∈ yes, f (inputRow n r) = true)
    (hn : ∀ r ∈ no, f (inputRow n r) = false)
    (hbad : sampleDoesNotMatch n k yes no) : lowerFor f (k+1) := by
  intro p _ hp h
  by_contra hl
  obtain ⟨u,hd,hu,s,o,he⟩ := small_program_gives_table p f hp h (by omega : ands p ≤ k) hz
  exact hbad u hd hu s o (by simpa only [he] using hy) (by simpa only [he] using hn)


abbrev Key := ℕ × ℕ × ℕ × ℕ
abbrev Lit := Key × Bool
abbrev Cl := List Lit

def qKey (r : ℕ) : Key := (0,r,0,0)
def sKey (g : ℕ) (b : Bool) (j : ℕ) : Key := (1,g,b.toNat,j)
def wKey (r g : ℕ) : Key := (2,r,g,0)
def aKey (r g : ℕ) (b : Bool) (j : ℕ) : Key := (3,r,2*g+b.toNat,j)
def pKey (r g : ℕ) (b : Bool) : Key := (4,r,g,b.toNat)

def conjCs (z : Key) (ls : List Lit) : List Cl :=
  ls.map (fun l => [(z,false),l]) ++ [[(z,true)] ++ ls.map (fun l => (l.1,!l.2))]

def valueLit (v : Key → Bool) (l : Lit) : Bool := v l.1 == l.2
def satCl (v : Key → Bool) (c : Cl) : Prop := c.any (valueLit v) = true

private theorem conjCs_valid (v : Key → Bool) (z : Key) (ls : List Lit)
    (h : v z = ls.all (valueLit v)) : ∀ c ∈ conjCs z ls, satCl v c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨l,hl,rfl⟩ := List.mem_map.1 hc
    cases hv : v z
    · simp [satCl,valueLit,hv]
    · have hall : ls.all (valueLit v) = true := h.symm.trans hv
      have hlv := List.all_eq_true.1 hall l hl
      simpa [satCl,valueLit,hv] using hlv
  · obtain rfl := List.mem_singleton.1 hc
    cases hv : v z
    · have hx : ¬ ∀ l ∈ ls, valueLit v l = true := by
        intro hh
        have h' := List.all_eq_true.2 hh
        rw [← h,hv] at h'
        contradiction
      push_neg at hx
      obtain ⟨l,hl,he⟩ := hx
      apply List.any_eq_true.2
      refine ⟨(l.1,!l.2), List.mem_append.2 (Or.inr (List.mem_map.2 ⟨l,hl,rfl⟩)),?_⟩
      cases l with | mk key b =>
        cases b <;> cases hb : v key <;> simp_all [valueLit]
    · simp [satCl,valueLit,hv]

def stepSignal {α : Type} (w : List (Signal α)) (sel : Bool → ℕ → Bool) : Signal α :=
  fun x => selectPort w (sel false) x && selectPort w (sel true) x

def front {α : Type} (w : List (Signal α)) (s : Selectors) : ℕ → List (Signal α)
  | 0 => w
  | g+1 => let v := front w s g; v ++ [stepSignal v (s g)]

private theorem front_shift {α : Type} (w : List (Signal α)) (s : Selectors) (g : ℕ) :
    front w s (g+1) = front (w ++ [stepSignal w (s 0)]) (fun i => s (i+1)) g := by
  induction g with
  | zero => rfl
  | succ g ih =>
    change front w s (g+1) ++ [_] = front _ _ g ++ [_]
    rw [ih]

private theorem front_eq_evaluate {α : Type} (w : List (Signal α)) (s : Selectors) (g : ℕ) :
    front w s g = evalLayers g s w := by
  induction g generalizing w s with
  | zero => rfl
  | succ g ih => rw [front_shift,ih]; rfl

private theorem front_len {α : Type} (w : List (Signal α)) (s : Selectors) (g : ℕ) :
    (front w s g).length = w.length + g := by
  induction g with
  | zero => simp [front]
  | succ g ih => simp [front,ih,Nat.add_assoc]

private theorem front_preserve {α : Type} (w : List (Signal α)) (s : Selectors)
    (g h : ℕ) (hle : g ≤ h) (j : ℕ) (hj : j < (front w s g).length) :
    (front w s h).getD j zero = (front w s g).getD j zero := by
  induction h,hle using Nat.le_induction with
  | base => rfl
  | succ h hle ih =>
    change (front w s h ++ [_]).getD j zero = _
    rw [getD_append_left _ _ _ (by rw [front_len] at hj ⊢; omega),ih]

def selectAt (s : Selectors) (out : ℕ → Bool) (k g : ℕ) (b : Bool) : ℕ → Bool :=
  if g = k then out else s g b

def negativePort (n r g : ℕ) (b : Bool) : List Lit :=
  ((List.range (n+1+g)).filterMap fun j =>
    if j < n then (if r.testBit j then some (sKey g b j,false) else none)
    else some (aKey r g b j,false))

def termCs (n r g : ℕ) (b : Bool) (j : ℕ) : List Cl :=
  conjCs (aKey r g b j) [(sKey g b j,true),
    ((if j = n then qKey r else wKey r (j-(n+1))),true)]

def portCs (n r g : ℕ) (b : Bool) : List Cl :=
  ((List.range (n+1+g)).filter (fun j => decide (n ≤ j))).flatMap (termCs n r g b) ++
    conjCs (pKey r g b) (negativePort n r g b)

def paidCs (n r g : ℕ) : List Cl :=
  portCs n r g false ++ portCs n r g true ++
    conjCs (wKey r g) [(pKey r g false,false),(pKey r g true,false)]

def rowCs (n k r : ℕ) (wanted : Bool) : List Cl :=
  (List.range k).flatMap (paidCs n r) ++ portCs n r k false ++ [[(pKey r k false,!wanted)]]

def antiCs (rows : List ℕ) : List Cl :=
  rows.flatMap fun a => rows.filterMap fun b =>
    if a ≠ b ∧ a &&& b = a then some [(qKey b,false),(qKey a,true)] else none

def sampleCs (n k : ℕ) (yes no : List ℕ) : List Cl :=
  let rows := yes ++ no
  [[(qKey 0,true)]] ++ antiCs rows ++ rows.flatMap (fun r => rowCs n k r (yes.contains r))

def getVal {n : ℕ} (u : Signal (Fin n → Bool)) (s : Selectors) (r g j : ℕ) : Bool :=
  (front (basis n ++ [u]) s g).getD j zero (inputRow n r)

def keyVal {n : ℕ} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors) (out : ℕ → Bool) :
    Key → Bool
  | (0,r,_,_) => u (inputRow n r)
  | (1,g,b,j) => selectAt s out k g (b != 0) j
  | (2,r,g,_) => stepSignal (front (basis n ++ [u]) s g) (s g) (inputRow n r)
  | (3,r,h,j) => selectAt s out k (h/2) (h%2 != 0) j && getVal u s r (h/2) j
  | (4,r,g,b) => !(selectPort (front (basis n ++ [u]) s g) (selectAt s out k g (b != 0)) (inputRow n r))
  | _ => false

private theorem val_a {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors) (out : ℕ → Bool)
    (r g : ℕ) (b : Bool) (j : ℕ) : keyVal k u s out (aKey r g b j) =
    (selectAt s out k g b j && getVal u s r g j) := by
  cases b <;> simp [keyVal,aKey,Nat.mul_comm,Nat.add_mod]
  rw [show (g*2+1)/2=g by omega]

private theorem val_s {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors) (out : ℕ → Bool)
    (g : ℕ) (b : Bool) (j : ℕ) : keyVal k u s out (sKey g b j) =
    selectAt s out k g b j := by cases b <;> rfl

private theorem val_p {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors) (out : ℕ → Bool)
    (r g : ℕ) (b : Bool) : keyVal k u s out (pKey r g b) =
    !(selectPort (front (basis n ++ [u]) s g) (selectAt s out k g b) (inputRow n r)) := by
  cases b <;> rfl

private theorem getVal_primary {n} (u : Signal (Fin n → Bool)) (s : Selectors)
    (r g j : ℕ) (hj : j < n) : getVal u s r g j = r.testBit j := by
  unfold getVal
  rw [front_preserve _ _ 0 g (by omega) _ (by simp [front,basis]; omega)]
  change (basis n ++ [u]).getD j zero (inputRow n r) = _
  rw [getD_append_left _ _ _ (by simpa [basis] using hj)]
  simp [basis,List.getD,hj,inputRow]

private theorem getVal_aux {n} (u : Signal (Fin n → Bool)) (s : Selectors)
    (r g : ℕ) : getVal u s r g n = u (inputRow n r) := by
  unfold getVal
  rw [front_preserve _ _ 0 g (by omega) _ (by simp [front,basis])]
  simp [front,basis,List.getD]

private theorem getVal_paid {n} (u : Signal (Fin n → Bool)) (s : Selectors)
    (r g h : ℕ) (hh : h < g) : getVal u s r g (n+1+h) =
    stepSignal (front (basis n ++ [u]) s h) (s h) (inputRow n r) := by
  unfold getVal
  rw [front_preserve _ _ (h+1) g (by omega) _ (by simp [front_len,basis])]
  change ((front (basis n ++ [u]) s h) ++ [_]).getD (n+1+h) zero _ = _
  rw [show n+1+h = (front (basis n ++ [u]) s h).length by simp [front_len,basis]]
  simp [List.getD]

private theorem termCs_valid {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors)
    (out : ℕ → Bool) (r g : ℕ) (b : Bool) (j : ℕ) (hlo : n ≤ j) (hhi : j < n+1+g) :
    ∀ c ∈ termCs n r g b j, satCl (keyVal k u s out) c := by
  apply conjCs_valid
  simp only [List.all_cons,List.all_nil,Bool.and_true,valueLit,val_s,val_a]
  by_cases he : j = n
  · subst j; simp [qKey,keyVal,getVal_aux]
  · simp only [he,ite_false]
    have hj : j = n+1+(j-(n+1)) := by omega
    have hp := getVal_paid u s r g (j-(n+1)) (by omega)
    rw [← hj] at hp
    rw [hp]; rfl

private theorem negativePort_valid {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors)
    (out : ℕ → Bool) (r g : ℕ) (b : Bool) :
    keyVal k u s out (pKey r g b) = (negativePort n r g b).all (valueLit (keyVal k u s out)) := by
  rw [val_p,Bool.eq_iff_iff]
  simp only [Bool.not_eq_true',selectPort,port,List.any_eq_false,List.all_eq_true,negativePort]
  constructor
  · intro h l hl
    obtain ⟨j,hj,hL⟩ := List.mem_filterMap.1 hl
    have hj' : j < (front (basis n ++ [u]) s g).length := by simpa [front_len,basis] using List.mem_range.1 hj
    by_cases hsel : selectAt s out k g b j = true
    · have hzero : getVal u s r g j ≠ true :=
        h j (List.mem_filter.2 ⟨List.mem_range.2 hj', hsel⟩)
      by_cases hprim : j < n
      · cases hbit : r.testBit j <;> simp_all [valueLit,val_s,getVal_primary]
      · simp [hprim] at hL
        subst l; simp [valueLit,val_a,hzero]
    · by_cases hprim : j < n
      · cases hbit : r.testBit j
        · simp [hprim,hbit] at hL
        · simp [hprim,hbit] at hL
          subst l; simp [valueLit,val_s,hsel]
      · simp [hprim] at hL
        subst l; simp [valueLit,val_a,hsel]
  · intro h j hj
    obtain ⟨hr,hsel⟩ := List.mem_filter.1 hj
    have hj' : j ∈ List.range (n+1+g) := by simpa [front_len,basis] using hr
    change getVal u s r g j ≠ true
    by_cases hp : j < n
    · rw [getVal_primary u s r g j hp]
      intro he
      have hi := h (sKey g b j,false) (List.mem_filterMap.2 ⟨j,hj',by simp [hp,he]⟩)
      simp [valueLit,val_s,hsel] at hi
    · have hi := h (aKey r g b j,false) (List.mem_filterMap.2 ⟨j,hj',by simp [hp]⟩)
      simpa [valueLit,val_a,hsel] using hi

private theorem portCs_valid {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors)
    (out : ℕ → Bool) (r g : ℕ) (b : Bool) :
    ∀ c ∈ portCs n r g b, satCl (keyVal k u s out) c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨j,hj,hh⟩ := List.mem_flatMap.1 hc
    obtain ⟨hi,hl⟩ := List.mem_filter.1 hj
    exact termCs_valid k u s out r g b j (by simpa using hl) (List.mem_range.1 hi) c hh
  · exact conjCs_valid _ _ _ (negativePort_valid k u s out r g b) c hc

private theorem paidCs_valid {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors)
    (out : ℕ → Bool) (r g : ℕ) (hg : g < k) :
    ∀ c ∈ paidCs n r g, satCl (keyVal k u s out) c := by
  intro c h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · exact portCs_valid k u s out r g false c h
    · exact portCs_valid k u s out r g true c h
  · apply conjCs_valid _ _ _ _ c h
    simp [valueLit, pKey, wKey, keyVal, stepSignal,selectAt,Nat.ne_of_lt hg]

private theorem rowCs_valid {n} (k : ℕ) (u : Signal (Fin n → Bool)) (s : Selectors)
    (out : ℕ → Bool) (r : ℕ) (wanted : Bool)
    (hv : tableEval k u s out (inputRow n r) = wanted) :
    ∀ c ∈ rowCs n k r wanted, satCl (keyVal k u s out) c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨g,hg,h⟩ := List.mem_flatMap.1 hc
      exact paidCs_valid k u s out r g (List.mem_range.1 hg) c h
    · exact portCs_valid k u s out r k false c hc
  · obtain rfl := List.mem_singleton.1 hc
    simpa [satCl,valueLit,val_p,selectAt,front_eq_evaluate,tableEval] using hv

theorem sampleCs_satisfied {n k : ℕ} {yes no : List ℕ} (u : Signal (Fin n → Bool))
    (hd : decreasing coordLe u) (hu : u (fun _ => false) = true) (s : Selectors) (out : ℕ → Bool)
    (hy : ∀ r ∈ yes, tableEval k u s out (inputRow n r) = true)
    (hn : ∀ r ∈ no, tableEval k u s out (inputRow n r) = false) :
    ∀ c ∈ sampleCs n k yes no, satCl (keyVal k u s out) c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · obtain rfl := List.mem_singleton.1 hc
      have hz : inputRow n 0 = fun _ => false := by funext j; simp [inputRow]
      simp [satCl,valueLit,qKey,keyVal,hz,hu]
    · obtain ⟨a, _,hh⟩ := List.mem_flatMap.1 hc
      obtain ⟨b, _,hh⟩ := List.mem_filterMap.1 hh
      split at hh
      next hcond =>
        obtain rfl := Option.some.inj hh
        have le : coordLe (inputRow n a) (inputRow n b) := by
          intro j hi
          have hv := congrArg (fun z : ℕ => z.testBit j.val) hcond.2
          simp only [Nat.testBit_and] at hv
          change a.testBit j.val = true at hi
          simpa [inputRow,hi] using hv
        cases hq : u (inputRow n b)
        · simp [satCl,valueLit,qKey,keyVal,hq]
        · have ha := hd _ _ le hq
          simp [satCl,valueLit,qKey,keyVal,ha]
      next hcond => contradiction
  · obtain ⟨r,hr,h⟩ := List.mem_flatMap.1 hc
    apply rowCs_valid k u s out r (yes.contains r) _ c h
    by_cases hp : r ∈ yes
    · simpa [hp] using hy r hp
    · have hn' : r ∈ no := (List.mem_append.1 hr).resolve_left hp
      simpa [hp] using hn r hn'


def selectorsAt (n k g : ℕ) : List Key :=
  (if g = k then [false] else [false,true]).flatMap fun b =>
    (List.range (n+1+g)).map (sKey g b)

def intermediatesAt (n k r g : ℕ) : List Key :=
  ((if g = k then [false] else [false,true]).flatMap fun b =>
    ((List.range (n+1+g)).filter (fun j => decide (n ≤ j))).map (aKey r g b) ++ [pKey r g b]) ++
    (if g = k then [] else [wKey r g])

def originalKeys (n k : ℕ) (rows : List ℕ) : List Key :=
  rows.map qKey ++ (List.range (k+1)).flatMap (selectorsAt n k) ++
    rows.flatMap fun r => (List.range (k+1)).flatMap (intermediatesAt n k r)

def deleteYes : List ℕ := [7,11,13,14,17,28,35,38,50,56]
def deleteNo : List ℕ := [0,1,3,6,9,12,16,24,34,48]
def gemYes : List ℕ := [15,21,27,28]
def gemNo : List ℕ := [0,7,11,13,14,17,20,24]


def atomValue (a : ℕ → Bool) (i : ℕ) : Bool :=
  if i % 2 = 0 then a (i/2) else !(a (i/2))

def otherAtom (i : ℕ) : ℕ :=
  if i % 2 = 0 then i+1 else i-1

theorem atom_other (a : ℕ → Bool) (i : ℕ) :
    atomValue a (otherAtom i) = !(atomValue a i) := by
  by_cases h : i % 2 = 0
  · have hz : (i+1)%2 ≠ 0 := by omega
    have hd : (i+1)/2 = i/2 := by omega
    simp [otherAtom,atomValue,h,hz,hd]
  · have hz : (i-1)%2 = 0 := by omega
    have hd : (i-1)/2 = i/2 := by omega
    simp [otherAtom,atomValue,h,hz,hd]

def HoldsBits (a : ℕ → Bool) (c : ℕ) : Prop :=
  ∃ i, c.testBit i = true ∧ atomValue a i = true

def FalseBits (a : ℕ → Bool) (s : ℕ) : Prop :=
  ∀ i, s.testBit i = true → atomValue a i = false

theorem falseBits_of_not {a c} (h : ¬ HoldsBits a c) : FalseBits a c := by
  intro i hi
  cases he : atomValue a i
  · rfl
  · exact False.elim (h ⟨i,hi,he⟩)

theorem covered_bit {c s : ℕ} (h : (c ||| s) = s) (i : ℕ) (hc : c.testBit i = true) :
    s.testBit i = true := by
  have hh := congrArg (fun x : ℕ => x.testBit i) h
  simpa [Nat.testBit_lor,hc] using hh.symm

theorem conflict_bits {a c s} (hf : FalseBits a s) (hc : HoldsBits a c) (h : (c ||| s) = s) :
    False := by
  obtain ⟨i,hi,ha⟩ := hc
  have hn := hf i (covered_bit h i hi)
  simp_all

theorem falseBits_add {a s k} (hf : FalseBits a s) (hk : atomValue a k = false) :
    FalseBits a (s ||| 2^k) := by
  intro i hi
  rw [Nat.testBit_lor,Nat.testBit_two_pow,Bool.or_eq_true] at hi
  rcases hi with hs | hs
  · exact hf _ hs
  · obtain rfl : k = i := by simpa using hs
    exact hk

theorem force_bits {a c s k} (hf : FalseBits a s) (hc : HoldsBits a c)
    (h : (c ||| (s ||| 2^k)) = (s ||| 2^k)) : FalseBits a (s ||| 2^(otherAtom k)) := by
  apply falseBits_add hf
  rw [atom_other,Bool.not_eq_false']
  obtain ⟨i,hi,ha⟩ := hc
  have hh := covered_bit h i hi
  rw [Nat.testBit_lor,Nat.testBit_two_pow,Bool.or_eq_true] at hh
  rcases hh with hs | hs
  · have hn := hf i hs
    simp_all
  · obtain rfl : k = i := by simpa using hs
    exact ha

def HasPrefix (a : ℕ → Bool) (db : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i, 0 < i → i < n → HoldsBits a (db i)

def hintWalk (db : ℕ → ℕ) (bound : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel+1, hints, s =>
      let w := hints % 4294967296
      let id := w % 65536
      let t := w / 65536
      if 0 < id ∧ id < bound then
        if t = 0 then
          (db id ||| s) == s
        else
          let k := t-1
          let withUnit := s ||| 2^k
          (db id ||| withUnit) == withUnit &&
            hintWalk db bound fuel (hints / 4294967296) (s ||| 2^(otherAtom k))
      else false

theorem walk_sound {db bound a} (hm : HasPrefix a db bound) (fuel : ℕ) :
    ∀ hints s, FalseBits a s → hintWalk db bound fuel hints s = false := by
  induction fuel with
  | zero => intro hints s hf; rfl
  | succ n ih =>
    intro hints s hf
    unfold hintWalk
    dsimp only
    split
    next hid =>
      obtain ⟨hpos,hlt⟩ := hid
      have hc := hm _ hpos hlt
      split
      next =>
        apply Bool.eq_false_iff.2
        intro h
        exact conflict_bits hf hc (beq_iff_eq.mp h)
      next =>
        rw [Bool.and_eq_false_iff]
        cases hh : (db (hints % 4294967296 % 65536) |||
          (s ||| 2^(hints % 4294967296 / 65536 - 1))) ==
          (s ||| 2^(hints % 4294967296 / 65536 - 1))
        · exact Or.inl rfl
        · exact Or.inr (ih _ _ (force_bits hf hc (beq_iff_eq.mp hh)))
    next => rfl

def checkLine (db hs : ℕ → ℕ) (i : ℕ) : Bool :=
  let h := hs i
  hintWalk db i (h.log2/32 + 1) h (db i)

theorem prefix_step {a db hs i} (hm : HasPrefix a db i) (hc : checkLine db hs i = true) :
    HasPrefix a db (i+1) := by
  intro j hj hj'
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with h | rfl
  · exact hm j hj h
  · by_contra hn
    have he := walk_sound hm ((hs j).log2 / 32 + 1) (hs j) (db j) (falseBits_of_not hn)
    unfold checkLine at hc
    change hintWalk db j ((hs j).log2 / 32 + 1) (hs j) (db j) = true at hc
    rw [hc] at he
    contradiction

def checkSpan (db hs : ℕ → ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | start, len+1 => checkLine db hs start && checkSpan db hs (start+1) len

theorem span_sound {a db hs} (len : ℕ) :
    ∀ start, HasPrefix a db start → checkSpan db hs start len = true → HasPrefix a db (start+len) := by
  induction len with
  | zero => intro start hp hc; simpa using hp
  | succ len ih =>
    intro start hp hc
    rw [checkSpan,Bool.and_eq_true] at hc
    have hh := ih (start+1) (prefix_step hp hc.1) hc.2
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

abbrev Table (α : Type) := List (List (List (List α)))
abbrev Rom := Table ℕ

def tableLookup {α : Type} (r : Table α) (i : ℕ) (fallback : α) : α :=
  (((r.getD (i/4096) []).getD (i/256%16) []).getD (i/16%16) []).getD (i%16) fallback

def romLookup (r : Rom) (i : ℕ) : ℕ :=
  tableLookup r i 0

def makeTable {α : Type} (xs : Array α) : Table α := Id.run do
  let mut top := []
  for i in [:(xs.size+4095)/4096] do
    let mut second := []
    for j in [:16] do
      let mut third := []
      for k in [:16] do
        let n := 4096*i+256*j+16*k
        third := (xs.extract n (n+16)).toList :: third
      second := third.reverse :: second
    top := second.reverse :: top
  return top.reverse

def makeRom (xs : Array ℕ) : Rom := makeTable xs


def atomNumber (ks : List Key) (l : Lit) : Int :=
  let a : Int := ks.idxOf l.1 + 1
  if l.2 then a else -a

def sampleNumbers (n k : ℕ) (yes no : List ℕ) : Array (Array Int) :=
  let keys := originalKeys n k (yes ++ no)
  (sampleCs n k yes no).toArray.map (fun c => c.toArray.map (atomNumber keys))


def unpackLearnt (size : ℕ) (tree bits : Array ℕ) : Array (Array Int) := Id.run do
  let mut readAt := 0
  let mut byteAcc := 0
  let mut shift := 0
  let mut tokens := #[]
  for _ in [:size] do
    let mut node := 255 + tree.size
    for _ in [:40] do
      if node < 256 then break
      let pair := tree[node-256]!
      let bit := (bits[readAt / 512]!).testBit (readAt % 512)
      readAt := readAt + 1
      node := if bit then pair / 512 else pair % 512
    byteAcc := byteAcc ||| ((node % 128) <<< shift)
    if node < 128 then
      tokens := tokens.push byteAcc
      byteAcc := 0
      shift := 0
    else
      shift := shift + 7
  let aliasCount := tokens[0]!
  let mut clauses := #[]
  let mut clause := #[]
  let mut last := 0
  for j in [1+aliasCount:tokens.size] do
    let tok := tokens[j]!
    if tok = 0 then
      clauses := clauses.push clause
      clause := #[]
      last := 0
    else
      last := last + (tok-1)/2
      let old : Int := tokens[last]!
      clause := clause.push (if (tok-1)%2 = 1 then -old else old)
  return clauses

def litIndex (l : Int) : ℕ := 2*l.natAbs + (decide (l < 0)).toNat

def clauseStatus (values : Array Int) (lits : Array Int) : Int × Int := Id.run do
  let mut remain := 0
  let mut oneLit := 0
  for l in lits do
    let w := values[l.natAbs]!
    if w = l then return (2,0)
    if w = 0 then
      remain := remain + 1
      oneLit := l
      if remain = 2 then return (2,0)
  return (remain,oneLit)

def selectReasons (db : Array (Array Int)) (refs : Array ℕ) (reason : Array ℕ)
    (conflict : ℕ) : Array ℕ := Id.run do
  let mut used := Array.replicate db.size false
  used := used.set! conflict true
  let mut backwards := #[]
  for j in [:refs.size] do
    let h := refs[refs.size-1-j]!
    if used[h]! then
      backwards := backwards.push h
      for l in db[h]! do
        let r := reason[l.natAbs]!
        if r != 0 && r != h then used := used.set! r true
  return backwards.reverse

def rupHints (nv : ℕ) (db : Array (Array Int)) (occ : Array (Array ℕ))
    (units : Array ℕ) (goal : Array Int) : Array ℕ := Id.run do
  let mut values : Array Int := Array.replicate (nv+1) 0
  let mut reason : Array ℕ := Array.replicate (nv+1) 0
  let mut assigned := #[]
  for l in goal do
    values := values.set! l.natAbs (-l)
    assigned := assigned.push (-l)
  let mut refs := #[]
  let mut head := 0
  let mut scan := units
  for _ in [:nv+3] do
    for c in scan do
      let (count,l) := clauseStatus values db[c]!
      if count = 0 then
        refs := refs.push c
        return selectReasons db refs reason c
      if count = 1 then
        refs := refs.push c
        values := values.set! l.natAbs l
        reason := reason.set! l.natAbs c
        assigned := assigned.push l
    if head = assigned.size then break
    scan := occ[litIndex (-assigned[head]!)]!
    head := head+1
  return #[]

def addOccurrence (occ : Array (Array ℕ)) (c : Array Int) (id : ℕ) : Array (Array ℕ) := Id.run do
  let mut next := occ
  for l in c do
    let i := litIndex l
    next := next.modify i (fun items => items.push id)
  return next

def zeroTail (ns : Array Int) : String :=
  String.intercalate (String.singleton ' ') (ns.toList.map toString ++ [toString (0:ℕ)])

def mkTrace (nv : ℕ) (input learned : Array (Array Int)) : String := Id.run do
  let mut db : Array (Array Int) := #[#[]]
  let mut occ := Array.replicate (2*nv+2) #[]
  let mut units := #[]
  for c in input do
    let id := db.size
    db := db.push c
    occ := addOccurrence occ c id
    if c.size ≤ 1 then units := units.push id
  let mut out := #[]
  for c in learned do
    let hints := rupHints nv db occ units c
    let id := db.size
    let fields := [toString id,zeroTail c,zeroTail (hints.map Int.ofNat)]
    out := out.push (String.intercalate (String.singleton ' ') fields)
    db := db.push c
    occ := addOccurrence occ c id
    if c.size ≤ 1 then units := units.push id
  return String.intercalate (String.singleton (Char.ofNat 10)) out.toList

def printDimacs (nv : ℕ) (cs : Array (Array Int)) : String :=
  let sp := String.singleton ' '
  let nl := String.singleton (Char.ofNat 10)
  let header := String.intercalate sp [String.singleton 'p',String.ofList ['c','n','f'],toString nv,toString cs.size]
  String.intercalate nl (header :: cs.toList.map zeroTail)

def setWatches (wa : Array (Array ℕ)) (c : Array Int) (id : ℕ) : Array (Array ℕ) := Id.run do
  if c.size < 2 then return wa
  let a := litIndex (c.getD 0 0)
  let b := litIndex (c.getD 1 0)
  return (wa.modify a (fun w => w.push id)).modify b (fun w => w.push id)

def watchedHints (nv : ℕ) (initialDb : Array (Array Int)) (initialW : Array (Array ℕ))
    (units : Array ℕ) (goal : Array Int) : Array (Array Int) × Array (Array ℕ) × Array ℕ := Id.run do
  let mut db := initialDb
  let mut watches := initialW
  let mut values : Array Int := Array.replicate (nv+1) 0
  let mut why := Array.replicate (nv+1) 0
  let mut trail := #[]
  let mut refs := #[]
  for l in goal do
    values := values.set! l.natAbs (-l)
    trail := trail.push (-l)
  for id in units do
    let cl := db[id]!
    if cl.isEmpty then return (db,watches,#[id])
    let l := cl[0]!
    let old := values[l.natAbs]!
    if old = -l then
      return (db,watches,selectReasons db (refs.push id) why id)
    if old = 0 then
      values := values.set! l.natAbs l
      why := why.set! l.natAbs id
      trail := trail.push l
      refs := refs.push id
  for head in [:nv+1] do
    if head ≥ trail.size then break
    let bad := -trail[head]!
    let idx := litIndex bad
    let todo := watches[idx]!
    watches := watches.set! idx #[]
    let mut keep := #[]
    for j in [:todo.size] do
      let id := todo[j]!
      let c := db[id]!
      let c := if (c.getD 0 0) = bad then c.swapIfInBounds 0 1 else c
      if (c.getD 1 0) != bad then continue
      let other := (c.getD 0 0)
      let old := values[other.natAbs]!
      if old = other then
        keep := keep.push id
        continue
      let mut next := c.size
      for t in [2:c.size] do
        let candidate := (c.getD t 0)
        if values[candidate.natAbs]! != -candidate then
          next := t
          break
      if next < c.size then
        let dest := litIndex (c.getD next 0)
        watches := watches.modify dest (fun group => group.push id)
        db := db.set! id (c.swapIfInBounds 1 next)
      else
        keep := keep.push id
        if old = -other then
          watches := watches.set! idx (keep ++ todo.extract (j+1) todo.size)
          return (db,watches,selectReasons db (refs.push id) why id)
        values := values.set! other.natAbs other
        why := why.set! other.natAbs id
        trail := trail.push other
        refs := refs.push id
    watches := watches.set! idx keep
  return (db,watches,#[])

def mkWatchedTrace (nv : ℕ) (input learned : Array (Array Int)) : String := Id.run do
  let mut db : Array (Array Int) := #[#[]]
  let mut wa := Array.replicate (2*nv+2) #[]
  let mut units := #[]
  for c in input do
    let id := db.size
    db := db.push c
    wa := setWatches wa c id
    if c.size ≤ 1 then units := units.push id
  let mut out := #[]
  for c in learned do
    let (newDb,newW,hints) := watchedHints nv db wa units c
    let id := db.size
    let fields := [toString id,zeroTail c,zeroTail (hints.map Int.ofNat)]
    out := out.push (String.intercalate (String.singleton ' ') fields)
    db := newDb.push c
    wa := setWatches newW c id
    if c.size ≤ 1 then units := units.push id
  return String.intercalate (String.singleton (Char.ofNat 10)) out.toList


def delTree : Array Nat := #[
  119992,123118,51446,107638,69862,108750,111832,127212,129275,52480,92328,99520,124100,131838,87204,118998,58617,81026,
  95392,78048,93362,106700,119516,121579,129780,62540,103598,132301,55386,96388,102590,118500,47363,101486,115911,63748,
  71806,128156,134405,135431,68692,85154,112307,117473,135935,70772,136368,137483,44301,65656,93844,124638,49399,72802,
  96912,139022,54352,75536,107203,110293,140017,37138,88730,141027,62064,90785,122591,142100,143126,31000,48216,94870,
  111325,144665,38171,53326,125586,146204,147230,96032,148769,79485,149203,149676,150821,34087,98975,106046,152360,153386,
  36140,104075,154925,89903,156464,157490,157778,85631,158405,159542,87687,70212,159885,68160,160421,52792,83609,160969,
  162107,50781,63091,162453,162913,98111,80442,164672,165698,52036,58181,167750,167988,168617,77457,54090,92815,169603,
  170828,60238,25719,171629,56907,172880,27986,173675,174932,48982,176471,177497,177712,179036,180062,46636,181088,182114,
  36708,183653,183897,44904,185705,186731,186961,188270,189296,37461,190322,34676,191059,192374,40824,193153,194426,21884,
  195965,196991,23937,198530,33318,199556,199720,200253,201608,201779,203147,203300,203845,32655,30608,27537,205901,207251,
  29589,208790,209816,24474,211355,28192,14749,212894,213022,25505,214050,18339,215972,13734,12711,218024,20394,19371,
  22444,219693,221102,222128,222241,222761,224180,225206,226232,1466,226836,15292,228797,16319,230336,230425,230934,231451,
  231952,233414,10770,234440,235466,236492,12238,238031,239057,7187,240083,241109,8716,241167,242648,243674,243725,5128,
  245213,6111,246752,994,248291,249317,249350,249865,251369,252395,252423,3054,254447,255473,255488,256003,256516,258038,
  259064,260090,261116
]
def delBitBlock0 : Array Nat := #[
  0x2a330c733cdbe98666d77bf38be6f2c044a80fd65d94d3ff41f8df48667c888c72e1d7b3cecf0fe58f98c8917e3f5990ad726a687ba40e1f6f35b921faec5b65,
  0xf6296545659d126caa46709110ce3f1187c999f652577a66ef07b597ce97ccaa985ddfb771fecfbfb1759c76ed47b9748ae7127da19fc4abb2befc43f13fbbb7,
  0x199fad7710f3fe919c99f94ed19e63f1aee20b2fb6cb45c9d7711467100100ce250feb7fd33f896bbdb1fcbedaef20fa177e619af330cf2631dd04ceb17ffed9,
  0xee4cc63f787fc867ed19adae4fc9e7ef8b13f93c16791aee247b88577e8b1699c4f455467b2efc33ff297efb19dc4790ddb2239f88e40aa0cd13de2399c49aef,
  0xff01f43b9f87e9638979ff463f5e5401d1307fdfc891cf55949dc4a634d1624024441f8901de2bab2f0d94b7d7887ee5e9e60cfd067794333e7e4f399900e899,
  0xcf229ae5009e40ef3048866788a67d1ecf345f5ec83bc7b14ce23f217e488165048843f88cc694bfebcfb6fe099a5d9a1ffa98e27aef2d9530fcdae19c48b0b9,
  0x4cd697dbed51174ec88ce25115304f40244c669acb1231fb4cfd81de45f88e1ff4d74461fc4daebe45eb945910467ee77e96589a5f89cc711a2f80397aec9aef,
  0xd5cbd152648846445f6bacbe2b2fbd77d8e250ffa45de2d8e2518998fcfd8587fe4c9100fa4c67b2fd3de2353366617d2b1fb133f70cfc2c6b467e6b2f97dc4c,
  0xc1129dfb322be9c8a67e66ffb17d67bf87bc4edf898bbd3ee236ff987e7b88a7713aca9cfc4fecf15d9c664acbefecf0021919c400e2c3327e24199c1f58bff9,
  0x4be5744f5ddf7cc6443b22699d8cf10ffe7c8b2c4db2970fc4222afe44fdd5e53c335cc6413d8cd0c67a6caa7cc59efee82cbdd10ff7dd9f89b3f886bb88c13d,
  0xf7e2308b188b907b23187f92268ce262f9abb884f75fdfd57663da5b2a41f812c8b19ad6327644e084c7e08bea22a8c7e7278633cc3ff11162599c4e19fbd77b,
  0x88fd89fb076858cf53507fe80e3e8b139df85dadb299aef731f9133f50ff8f3fe6a673de22d77b3de25e5f12fc4099a792265d90b22559515da5ae897b176fa9,
  0x43f1087e22cfe21596222fba2fb87e822a59fab3338b94df892c64f3f12b633c111e55e1fd7e20454762c1f5b3f34c68b635c110d949e52dbe6f3ea45dbb0fb7,
  0x6261ff60ffa6fa8ab1778ece33c07feeb2faccfc2338907f10f2f8f2a25f301d1303a212fc403f88d6589c3f8937d50f91efed9ff998fdedd7b721ec84535652,
  0x67ebd81701c1735c113ffbd35e3638816145f3a671358d0021a317f6444c91332447efea3223aef4fc416375de363443f2d17d1ee2226697d903f107b9cbf10f,
  0x2e1bfd80faec2f6b82d4be16e660f0cc2c67e17d650917cf0b6b285baec21199e175650b91705f0fc79a9afcff7e8b3d97fd7942d87e34b631e6a697a7dadfde,
  0x9be5744e77e176173650b4c60f0b29e1445aef65ff01f1a07fcd142f4661789985e563f753887942d1330745d858d942eb630bf5d8d9f7e73304125c1681c25d,
  0x315d86cbb0de8a37f902eb291a467a594351146d59435318d9198dbcf8d2b2867ec1b22e1a01c19c3e360386cd70f47b5e9bfebcb114ec2c26617b650b9651e,
  0x7e10f7d3bf4027a8c1ed9ffa0cfd797cf20f393c43f1da7fe79055d13b7fc1143a083dd4fcb5c3279e40dbfb67fec5da7f3e35aca431998f2cffd07fe3630c7b,
  0x2d6440f615ce6231e222f88cc384499ffb07c9d85b70f1e7cde51229cbe144d63fce8b551fa4639febf1097f7ff7d07e05ba80e1114be78206764f8711c3f1fa,
  0xfa7fb177a8cdd8f5e5d73317c9ec5fe31ca119ae0cec3f30ffce4fe8c98f39f891eff9f2064c7af679b7f1553d3e717b1dfb3279c81de8c98546794be1322f87,
  0xc796cb1117c780fef71f5e8ee3d81c4f8573988c77edd7bd0a8c0c95bfeab286ab9b8aa31ec5f974475dc73b8f345f4072e15cd7655c38f62fc460817473b853,
  0xbb3c7b327bccfd7b07a0ce5c110fcf1e6087888e667842c6cee230f8ee4a0859ec5dea1f0bc6c7102c06594833652220b2d92cfc1315fd68bbb847e7205d78dd,
  0x97fc07c2fc98f12ffba9c43ca376b88433f20c0710965c157982c108f4199e1986642fd77b2ec2f3dfc6663debb3c6decf21980c3636c72e1105dfb2ffaf2846,
  0x1817f7ac72a468c14e049edb7f41f860d5bb967fddc7822effefa0fc1e17745aa8fd231ebd9eb33f1ec383b6521b98cf1e3cbebcb114ec15d139df85d88807fd,
  0xa77c2c8a2236ff3ff68cf50b588c2c0e7788fc9a85ac46221183bd42d62304fcd155fd69fb1e3b2677d8ab97960ab8cd9413f34557f5a2eee3c07d5ff1d9e176,
  0xbbefced3b3771584f605b867de5d7917dcf87c6fddbc7f7e0c59efec0b46ca27796caf9db0c0fb397c782cf1ec965f75b8f60fe9f88e4f787e60f4df5eb8337,
  0xeb7fbf11063282408650c44a1ff30ff7f39ce8e6701aa77b8ab8c47acccff6051ee12f263cfdd7679e4728581c4fcc50932443331025174421f5b8dd93d802ef,
  0xb87fd3f1116b910fc7bfb36f604645c35f8389f4fdcecd18f2d77b17eb2b1cb3118be4ce0432863c43e4c71097d450cefd79662bfaff770b07f50ddcb7c0fb76,
  0x839f95c8cf970fcf4ff9fbafae5145dfb88cc6b7113b7d6f1cacddc36eb4ff9fbafae513bce7d4cddd830b17f584b61888796597dd6e3d79fd27b829f887d6ed,
  0xe9f9fbfaf28df461bce7d19ddf6cfc1e35d9e082f5f5ca2b0a71267e73a5c33a7e0d197afae51e53bf3911f9c8efc6ee223f77ced863dfde7b0bbce40baf1ae1,
  0x6ef9eae5113b7d3f66ae5111f935a98f20f9230b7e9cfcf1ee765aca0fb908a02eed70898cf698c44bca6e32864c7bfbc4b334fc9cc1eb334bb961b1e3b2b2cf,
  0xb029fdf48cf5f6fbdd8033d55f27d6e13f7f30fd67b2fc7fc072fc43b37701069dfa013d460d2c3f08f6b6313880708816200417dc9ff2b1adf4db5b6ee3c2ed,
  0x463d8bfec6710631cecfc09fe1dd9447fe80e13df7edd7bd7c461cd4ff9b7dcf5ce220fbb71e727f5aaf08bcc048cf4d947a7df9b7dcf5ce21e5d376e3dfd8b3,
  0xd466ec10b37ff7d07e08127b6dfd07e182250fcbbc3dc2d33308e394ff93273fd3841110cf48c1e233c81d126f8f633d388116cf8fb84440ef1d865462044865,
  0x28a19bc7f53994301545acb3fa713320df463cf212b28882ef698c442d8f48c1ecbe4aca2250ff48c13dbb772bce60f5e7d6d4c2f5d11a9a1cbc3dc29fdf48cf,
  0xd8f0bb43b5b61a31aff85da1dadb0d183683df9e44622059e3b23f76e706ed7fc2efcf2230a2c6c970f699c461985be5c1450cde3e16f970439dbdf75b8f207,
  0xdf12c883dc6ff18e51ed638943fdff68cdb7feb0e780ffbbdebbce477e3771a694fa8ba764b3e4d182bbc23317c9e4c958dbd0d8597dd74999c253fe4c967c9d,
  0xfa77b8fff771e53b39946bbce4b23b8e7f114bfe9be0c63f08cc4403f38998ac335c3c07e4f15e615f4733b8794efc117d37ce95184397db61a31af3f88a5ff4,
  0xfddc79a9fbd7391d4514790ce9116b821cedfc2c6282408650c6be9624df0a2c0c6831e5632cc613915373cc4403f10ccc236388117bf630e35933f4df1ef5c6,
  0x6887e34fc4727bc3f3044f6fdce5b0c7cbe4c958dbe9e6c7af2a3f40747fe5b3feee221e5967858c52fb2f5f83673dc397d1efca33ff575ee623016fb871187f,
  0x23946cb0fdc70a2e9d92cf93463de667c3e3ce4501c3d43fed2f87e363771e45f5d9ed631077bfbccdf2cdc38f264bdc8a8c291e7247f096e1a861d30e6c1e17,
  0x5611c460334ffc7c9f4ac22e7a3018a3bfc7eb11baa42b88c6e5f886663dc13bfebcb1ff01fc167f8fd6472aaa539e8c6ef50da38b7c7958ff7a7c9fee0bb3cf,
  0x27711dff5e5b66ef01a33d3651be59b9ab0cec389b5dade6c78d1d45bfdf8d4368e2df07bc3d845f7fbf0afa914de180cd3ff1f4fd5847118f2630334ffc7d3f,
  0x53afcdce1cbe5630be7fe7fd7dee0a3d8df6dfdefc7a8c5b91d4fdefc4427ba2bb1e3b2211875dcd7a1b9c44c0e73278991f898cdcef1127dc4c5dbf27305ee3,
  0xf41f835370d671fcdc2ff9e45fddc1cb5dd5230df85ff207077beab5d8e61bf73fdf903b9feae6c730518e7b6fbf4df0907c383bdeb90e3aee7fc2de71573817,
  0x6e61728fdcaefab1b5c30270fc72f6ce3f32c3f1e8f7e519ff5f4fdece9518eff8f67a6f9d2ff580be1c7ce854615aee262ef79981900cf77072d743ee23feab,
  0x7734faf7b5d6aa4634faf7bd39348c77d06b38f1184f85f3727ebe9b38f11911c8cdbf216dc2230fc8b45bfdf859e27f671b1e18377fbacd5bcd4f711e03f374,
  0xe3b1b75eb09b065b3883945acdffcfeb2f6366e71076be9fe99f3c7d8d9b9c44563443f113cce39ca2a7e03fdfd18fdedf5f0fc1ea316e4e5f7fbf07df08522f,
  0x7cf76e7112466dbfb2f9e7dce71e1eff9854c650b95b516cc9b1b77138ca177f516cd55b1b771122cf0f783bdeb8777bb327fddc796bbd97cc19aec1e73f38cb,
  0xf67e089ceeb3d37c3f0780fd92586c47fed2fb3bf058ee224b1f80fd92586c47db7b7e723ba3c30bb88981caf7139823edbdbf391dd1e184dce204892336dfd9,
  0x4c2df2e0a664c2df2e1e7917e3279e40df71f9f2c970abbd992c959e0b03463c1ecf13fb275ec786088e1f5fcac6e506558bf8703dbf1cba70e3d8bfec67109e,
  0x19cf637fd79604d7fbb8966ada75dc0ecfc1df4aa9cb82df39708807ea66a9cb81f2c970d7fce672c970f2d70c9e7905174421f5b88807ef9add5397032df2e0,
  0x19fefc07c8f39f46777db3f01cbebf33e70a7ef925c3c68ed6dfdefc0527679706709d9e5c3fb387d92e1ae632f9704394cf5970bef9708fadc6bbd07f1ff07b,
  0xe1096ef7c397bd88f01f93961b06fc5d99122a7e18c30e543a23f70c84c50dbf98239405b69b175bc472ed661ace03729ef6c44bca6ef974d9c23986c9e3bfee,
  0x4c6723fe0377cba6ce355fa0fc11ce5153f06f8e5d589c1d30e6c17b9151852262bfad3f61bef5f964b83b772bce60033d7c3dd6e22799cc6723fe0f01fb2424,
  0x9e9be42fc2b9cc70e3d83e4ec2db84b356db6e0767e0bddcd3ebded75f88c55ce05d4ebf771a7d7bde9cda31efef337cb370e3ce4feb55e11dc79cfa3acdb3f0,
  0x8f65ff2d720bccfd07fe3631e83ff40221ef33f799a094efde67ebd8101fff20fb79c418b19d90b9dc46a642cbf420fb7f47b2111888f463407e444963732085,
  0x62ef50f8f62ef10fa1eea7126fa08d8fdd4e21e51a899fa5941d63f65ff5e51ecbfecbe84472785d95c22393c4bee62230fd5d7b888c3fe7eee60cb1fb2ff80f,
  0x7a59429f6a2cf6330a87fe4330cefdfdfd18c33b88b3f604d77ecbb06ef65ff01f019ecbfe03e3d79624fbab87af2c4ea6e62dde433f1b1829f803bc6c60e64f,
  0x164f731faf6089c3ff19985a8cfcd1444e0819e73306f3fe733065f65ff5e51ddecbfebca2f7e3d910f28b3f331c43ca25dec5dea1f03efd8bbd43e3dac71382,
  0x45de9651e61facf119ace37d31e61fefaf119ace1d89cdef5ca2b944e5177ea2b942a1f29bb9ce150f94d1ff3884266c71ffddfbccc06ba1ca2b9439edaef5ec,
  0xfff4ecddc7a31fe7e8b2769d9bb84bee23935c838199fe9eb9070f3999bbde8a11114de1c150fca5111a9dbb7ebc3dc7887f7e872f0f71e75da99f9ccc78aec,
  0x9bd118d3f3f727d3f73b34608027998fce6622799fa013bf30773044f33befe1773077306ecf697fcd1436fe4c9e7205d78ddc36fe4c9e723bf1b9fc7a31c40b,
  0x9b0d8ddf80ff87b87ff5fa0ddf80faddb70ffa7e1cf46383b5ddd11873d18eb077aebe8c44d33f1999b844edff059c6a628a227aeffe8b14c51469f9fbfbfbb9,
  0x53ff995cb712677fb4662ae9ee615cb704ff3f98572dc780ff94eeaebdb94463c07fca77dfb75ee62317dfd99204d7fcea0befecc9315fd7fbb8880097930a03,
  0x1c1459e23270337edd7b638337edd67fce1f3364c6c58c3b0c31b1635ee930765ee2635ce207b0ae73118d7388795cdbfa31e6a7133236a8a3cd4e2664a2de70,
  0xfcfafcc1139dfb198ee94463dac71ffb198eeda311287ea9b8168a4c7870899efaf80ff7f67bb1133dfd07ee69d9eec794be93d9760ecfe27b79d4b63b12c966,
  0x6c794efc116dc6ee5988c794efc160ec2fb966230887e9a7adb8221fa6994e7036f35f837b2f66ed30062de612c473300671346634fc40b3767d7e60d3f57780,
  0x403f75de9f6afffdb208807f13dbd669ffdb202df8936517c4c4cc135da5de1c155dabfe8c7fba05576af99f53fbb0067e3d8a82f247e1afa82f247fb498178a,
  0x75b8f7049ef5fbeeb711317fdac6e4c51425b2ff72628a3dc3fc5f22f8f633f519ee77ab9b9a63d8cfd4639e73fab9efc2c1f8fe9a338583f1f77fe706e5afc4,
  0xa7ce11e529f1ced3e707dc64f2198581d6fc7b07a88b12f6788c11158d2f88c0af867f36fb94257c3f3c8e50907fc4bfb6e9f98483fe25fdb7bbe31e36353ddf,
  0xdf1888ac7f293e99d9c2cbf67c699d9c6f0fc64328407ccfb6f1c1ce1d8407e389fb3e1ce1d889ac7ea1ff3911ebfba089ac7ee093bce447aeec4499fefdb79d,
  0xef6ffc9f5b822c73dff27d6e2234589a67ecbb0bfbfba9ffd4fa85fdfdd4ffeabf8279b1107bdb93f5fd37c44d6344fafe9be227f7476053e85f113fbaf5c7db,
  0x9af7ba4c113d764cca3cc3feedfd7761571073aef76feb7bae226d97bbc1107bf85dfaaed39070883de24b1f1a720e0bb7d59ebf6c2edf567bb9c1dbaa942bd9,
  0xedae1ae6c1ed3322cb8a14b1ef1f1db0a58f78edf184a9128ab89f61e7efc6c2dd575ee2dde7eee63d1ed10fe985c13aeefb0ca3c4f7898cd7730b30789ef131,
  0x8a3c2ec76c3c4bfc6c1b70b8ae0dbf9a9b98882efbf5bfc639444f33b747f8c7283162d3e572dc2963fcf9f95cb711319f8f2ffd3299b8f6cfe3ff459a653371,
  0xefe03eb7a7fd1e163813c07ef7ffa1531b62c7967eef66b7f73b1133decffeffdcec786cbdf7e73311258e262fcf7a3b98224b1f9b7fc117477307998fd977e6,
  0xee59ff771e08bebd9f2d9ff73f888009e6288833ff30ffd97629ec5df2c7ffcea0a7b1769dee3ffddc7af66f85dccd3e71ebd9e6df7799a7ce17ef0ff90cc44f,
  0xc1e27bcf7ffd37c7a6ba45f4b28d9f7dfdbeee04b5de61fdbeee0f28cfc8be907967f022e31ca220f7dfae31ca3cf27a012882e1e793d008bcf7c63c117d7b16,
  0xe215d888116247b5bd987bf11022c48f68706d580c59bffe7e7e0fbd0432889e66177a3df183b113cce25188ec83b1e68b09e3331f9fbd739ea30787b93ee7a8,
  0x39374e3f301abbf39353fa4c1eb5daa6651f2e9c46a6e51e3b145f36fb9469df8aefce662239facf73bb7a7ce220bb43ab2de9f38f0581622fb23ba215d8f30c,
  0xc440f710ecb7b7be311398f0e328d56f67ee762dcbd9fb9d8277e7a45c3ce4f059eabb4e0ed18f393c167aaed5bbfa30bb7fc4bebfa6f8443ff199fa5941abbf,
  0x7edeec2c5d6fc4bf7bb7bb14f50fb7a8c0ae22fa59456fc408a7a23fcc56fc408a7a5ef382d330c6bf1ecc9bff1d94438e22058a7f8e8871c440f710ecb7b4bd,
  0x139f4393fe31013c57665113fbc7f8c728f0b1f9e4e31ca3dc33a7bf9ccc4459fa0fd97d1f1bb889b3f0fdebb4d1f1bb89ef4fdf75b8f9f0cf4b2858badb9f98,
  0x6cbed2fafc7bfbc1df9889462bec3dfdfdfddcc44177c6c3dfde24fbefea4fcc1efeff2fb326a4fcc1a77e68be68a28a2c7f8c728da7bfbf18e509cfdedcb5be,
  0x83aae1e73feb33731ea1fe9dfa5947a2cf633f3c82267b93fe7907b824408b4375b9c7b824408b4bdff9c4093dd17f4df1a7ecf7a2fe9be110fc459fdba0e110,
  0x7e2250fe250ffa2c111fbbb7f45820437f058b70a7782c5b80335ff867e0f6fe9f5bce018c0cd7e3deba7bfedea305bbcdbffdbd460893ef8c6113a9f1b0f39f,
  0x6fd45728f70ffda67e7331ee7689f53eb70dbd913f53eb707d84efd2ca39feefd43f1e8b311659e8b079f912efd2ca3d8bfe41ff518222fbd3fea30118cddfa8,
  0x7efc07d0f4596fc7b047edf8f60f62fba2aecf1183d97f77e41f23c133f4d7076fe9ae1e59f93f64f0f7113177f8ff87b8f0d977679ccc7a31fa2c515ca220c6,
  0x877eedf1ee631dfbb7c0efd8cd0f1ec88fdd87998e23f76111fbea1e3d816207b1e6630b103d80b13dba1e433f13dd87803bc4f761e433fdfba98f0077efdd4c,
  0xf88393f43c81de9bee63c33ff4df731e9bf6687bd775bff28f04ceb7fe515bea7d0f7aefd1edcc78267e8f6e63d1eecd0f6d77a0fd87b98fd07ec3d07fa87b6b,
  0xfbfbfbb9db5e88c79fb93e9fccd6cd18f3f727d3f73b7fd18f1117cbeff63cd65f2fbfd8f2fb29a1e222f9cfb98f3597ce7dcc79cfd9a1e40e8395f1e19fc1ca,
  0x1867e608a8f12f94ddce703b29bb9ce3c4be5347fce0765347fce3c79f5331be3d99204d68bcea0f6648135fee2f41ecc9315fd7fb9fc79fbfbfbccd4de88c79,
  0x3331e08b6e3772b94463c116b353772cc463c160ec2fb95ca231e0b0775958e5988c6be03fdfd9fee823faf80ff7f67bb1e83f734ecff7411ff41fb9a767bb11,
  0x437f0f70ffebf41e03fe0b3f87ff5fa0f3c86eb76dc3fe9f8f01f5bc7ffc3fe9f8f0586e3ba51188ffc161b8eeda307bdfb198eeda31efe4db1aa63cd17dfd9e
]
def delBitBlock1 : Array Nat := #[
  0xf39fd5cdab07a8c73c7639ab9efc7a0fef66ed3077ef66ed307a467df63ec39fa0fc28573988c39effd83e15ce6230e7e83fac736fe8c39effd33f736fe8c79e,
  0x77575ef43a231e53befdbaf6dfd18f753ffa9da83d8cfdd4ffea7d47ba9ffd52f41ec67eea7ff55fc23cf93547a8cf73bd5cd97d31ea33ce7dcd5cdcd31ea31c,
  0x145f533370972608a8f0f7567afdb1c6acf5fb638d59eee70f699931d041e4c9e7205d78e750793279c8efc6e2f41e41f47e723bf1b9fc794eeaebdb2f4463ca,
  0x70ec19f6de3839c6fa62389f99f28738762389fb3e1ce37d31e2bbf345370881656067d7e6088166ecfbba4c1577b07c33ebf3055de03f3eee93044119c99994,
  0xb875de230df5bdd7067e9eedfd6f75c78597d445f03aef4fb57ffe8ee81d75bb5f57ffed9044f6f59a7ff47741eabbd7eb34ffed907803bdb655419f98e58e0e,
  0x371947b9dc72de9ff46eca7e03f7bffd1027b9dc75efff47bacbe2bb58889938c29f42f8f459e8c614fa17c444c9bb3edef8c7a2cf6071f6f7c63c461bebbb0a,
  0xbb985983dedfd1ed7730b307987f76bdee9307bdbfa3daf7ba4c1ead8d3319b844c5f9ef7ff7e60898bf3dedee93079b7fc1177ff7e60f36ff822edee9302cbb,
  0x7615f75c9ffee815f33f44ff7615f33ea7ddff8745c45c5159ee776e3f667159ee776d6ffce10eacb71fb33843ab2dadff9c780112afc4453b8ffcd147987f76,
  0xe76fdcce0a7c7396ffce3cfc98abf1594d3d6dc3d07f4d3d6dc2b29a6539c3c233d3b2762b20437d671be9872b3c466b38df4c77d4086face1d873bebc466b38,
  0x5defee7e3076225188ec96eb0440b0e8ec83b17ba2e1c3c116dd7b638e3b75ed8e3c116dd67fce38edd67fce3cfc9bb2c60dfb6f3b7ee671bf6de72dff9c14f8,
  0x74e0ed1875ce7aaed383b463c167a6f9bab77f461d739eabb56efe8c445f7e03fa617089977e433f3451ed9fc7f4d19c5647f4d19c5647ddff9c7803bbefe7c0,
  0x3cb7ba2de70f5ecf2075e413b5d4d2911087fde8a4160880fc87cfca5ff65d827b3da5f547af62ddcb3ff3a83d7b3e5b3fee2f41e61fdf96cffb9fc782cf4df3,
  0xdcc51fcc17dfc2ee65ee9306f85dafae9f38df0bb98b7fe71e6df775f5d3e71e6df7798b7fe71e75dd045f8f353f4636d514443cb7b6d51479a9fa31d16f3844,
  0x7fe9b86e6e3c797fe994e9fc47fe8b34dc373711ffa2cd329d3f86c571444f6f3a96cdf4c794ec39d4b63b04e821b87a013bf3147f307a013bf32f74982fbf85,
  0xdb74fcc69fb2fedba7e63d1677f6deef8c69fb2fedbddf183778f679a28f50fa9fd347afee802e517ce447afee83dc12729fd347aeec05cb79de7223d7763c79,
  0x6dcfcc3f6ddff8b7e25f9d32deec5bf12fdeedbbff1ebcff867fe33303bf393e58fff9d41e177afff8fff9d403bf3934ef71ffeee3c2ef4f4ffc7ffbb8f459df,
  0xec263f3451e8c6af9bebbba230cec9f83b5ddd118f463acd337d75f4619d93f583bd75f463dac6e6855147f7342a8a3176c6bf05867ea63545b73f10fccb7bb1,
  0x61d8618f5ec61d86181db5ee9307af635ee9307887fd8f760f01ff7f7b741c3dfc9eb5df90cc27fdfdd38fcc0b7f39374e3f3027fdfd4fe9302dfce4d4fe9302,
  0xd8eeb7b30f7e2247b438365f4c443b1dd0e0dab077f63fdf707987f63fdf707987f53fb6e0844a9006effcfcfc785defff9f9f8f4d713f3450a9fb87fecbb03b,
  0xb7b7be3111c9ae4c6dc44726b97bce1a7ae4c6dc0c90117e37fe3b286f7b9c6ffc76502fff3853fc7437bdce14ff1d02fff38f3f27655f8891ed6f661b9a6221,
  0x97bce1e3cffb2efc8663c1671a48d451e0b38d4c5bce1ffd16248d451ffd16298b79c3d79fdd8bf1ec1f29dbda5ee37fe18cb7b4bdc7b07ca76f6f7c637fe18c,
  0x9d2f7fe7083f65f47c73a8107025911f1bb80fdebb4d1f1cea00e04b3d347c6ee29efe7e45478f2fa2c3d11fe62247b773d11fe63c797d161e97bce1123dbb9e,
  0x79fb29ef010449f7dfd6f7fe60893efbfacf74983e5f664d6f7fe60f97d99359ee930270ff865113fbd650dd6e71e9f7eea74375b9c44fef594bdff9c7a7dfba,
  0x4983c6bbf387df31f293e9cb1f9c7ca4fae33f9c59f1a72c7e7167c6b8cfe71e2bb972fc2f0ffb6bbcd144f7bc7c76c780fef1f1db13def1dbe31e03fbc76f8c,
  0x3dfc86e1e5f7a7d6f384e1dade70f65daffc8660a7eea744170f75329d105c0a7eea6bcf7c63dd4ca6bcf7c6064f22ff9a28ddc7e1afa8f2b1c7e1afa8ddc7fb,
  0x1e177eabb4e4ebdc785dfaaed397bce11258f8d393af711258f8d397bce1102c3ffd3b39d41e563ef9ffe9d9bb8fcfd164ed3b39d41f9f83df7e769d9bb8f263,
  0x3d3efbeedc23fc6399b1e7938c73362825bf159751e8b25da85bf9826a27bffe9f69448b2cf55ddb13bc79fb63f7e833b62f7429d6f8e310e4ff8c77df63f345,
  0xe5be3f3dd85bf570f47bf531d5c3c4beb8ecfb02ec9efccc6db8f7f7ec6db8f5184edb70afa8ca2ef1d83d18de7e3b05efe165f1d8031c7fd79fb70dffbfb2dc,
  0x4cff11834e235346f30a2f9b7d1bcc78aecfb82470f1e5848e035dee091c3d1628bdf2637ea2f7c98f9f8ffb87e18f66454c31577917c304fd937e5be3fc7f7,
  0xa1dbf88c9c34ec3259e8b069d9eedfd160f7f7f3cf201df9e790622cb17f5aec3b75fd6bb097618bb3c4604bb9334be2307907dbc7b069f6f1ec0e8bf3e7f88c,
  0xef66b727c820b3ffbf27c820d3efbf5116f71e41f2777b85bfa03af70877bc3f7b8b727ebc7f45c113ebc7f45c19df998ff31e4c83eff31ec1f6fbfcc6ed7e68,
  0x7bdd8630a7df3b3e033c1eecf8f7b7fe4fa3e413dff27d1f2043bbecae1e5f64c6570f264257081171879146fd71879147af2819fec448f77fec7907e9effb0,
  0x6fea6316e5333ecf7b71e83f6cf7b70877917fdedc227d5fbd6e2c89fabf7adc13b4be2315f18be2315f1e230ebb03964cd5f1dfadfb376ee516e8fd9bb7728f,
  0xe10a63d8bb6c6530a7b57d22dc4f7afabe916e145f787fe51e163933f94440f6e2ec1e963dd9d51ac3ee691c1bb5cf11117d20f0cfc9d8b76fd1bfa98c6fd0e4,
  0x588d4c8efbb713f36f8bda5f1d8bf1efef6e5d070b23988b87b2ee38dfbd7029d2fb0ca0a7df1ae1ecbeae985c169f2b918c83f3e7e57231905efefe429889ed,
  0xb6753ea3dd4d8deabf80dc26a82f206c6e01e99e2ff5189485fda5fbc8f34537f7a291f993b216c3ff47b217659ff1ec20cfa99bcc875c976a991ea1f9148436,
  0x759cbbfe8d9cd8b0422ec7d51ae53c782c37b384b68c782c375c6fdb462f7ec6767096d18bdfb19ae37eda31391aa6e1a99276ed513a3f3c7ba9b1bd4fa8f753,
  0xe6b0f523c33f0339c41b37388374e209dce216cc7388f7f2425e45177a0cef211e7dd152907fbd14829f80ff7e59ff414fc07ece5dff47b9dc777e59ff47b9dc,
  0x906f1ed8c788c37d589dae3c461beaeea9ae29eedfd589dae29eedfd5dd535c4777d5e4477feef0477ecf1e663f387e84233357906fa11412846f596840fba10,
  0xe54bb238c9148771f694826875e444d33f19d90b965676477c9d90177611391e9de47b87fa76e6405bfc216c11cc86c73218ca47b6b8337cd4c694c64328d72f,
  0x9c35f01fb61d67bb1af85dc26fecf763d07ede69d9eec7887e11cd3b3dd846d073cc8467f82c541bfb3dcf1e52fafe3d8444619d9f79913098d53208027a6f90,
  0xbdf8d700dbcfe47bfb3117f91dc72641fe41fe4fe42fff91b1f3d11e52ffa0cd11e24446b0444019a20dc880be5bedaa28916f6daa280be5bf45bce122dee8b7,
  0x3dffdf983ce4263dbdd2608e0b8dc651a771cbf9a288e4ff6c623af74bb073eebb9859820e3eebb985980e7dd7bdd260838fbaf7ba4c1bbab899946ee3f4bb1b,
  0x38698d71bf90cc788c83831afc3656067d7e606cdd9f774983ce427619f5f983ce4d3b3eee9307bdb93f266651ef6ff28d70f27bdffdf983c9ef6f74983ce426,
  0xe2f7641170bd8efda6628271853e85f0b7f3f6053e85f1413767dbdf185bf8594fb7be31bff73b4bb01758c3d11fe61b1dcf447f980bac61e97bce0d8ee7a5ef,
  0x3041c3b1ae1077edd145b9d15393af716e7454e5ef38104e34e4ebdc104e34e5ef3821cebbd06612d650dd6e71e0f7d8e86eb7384b594bdff9c783df63a5effc,
  0x61b9a63cc11dd6f661efc780390e0d97d31e608ee8706d580fefeb7bff301fdfd67ba4c1e1ef22eb7bff30787bc8bacf749820e677e19461d07379a2883bce7c,
  0xae6de66a6f4460ae6ddcede9e88c15cc9fccd6cd182b993f73b7ae231bb3bf3147f306ecefccbdd260acf30498a3f982b3cc1265ee93061cc17fcd14780396f6,
  0x230db8ecdd383b461c6df9fa70768c36e3b3756ed711871b7e7eaddae231feaebdb2f4b6c3fd5d7bd0e96d87fefdbaf6dfd1827d3f73b7ae2304fa7f335b3460,
  0x8c5ef3ab1ca91a30e77cddcab5a230e77cddcb43d1187276a6ee548d187276a6ee5a388c0edcb23956b446076e591cb43d1181db93ab1ca91a303b727563968e,
  0x73bd5cd979cc1bce7dcd5cdc9cc19cf39fd5cdab0339e3b1cd5cf7e2b353772d1c460775958e5a388c6a6ee548d1883ab1ca91a313b53772a468c5ef6472ad68,
  0x88f5dd80be6ff2c7ffced606fafff8fff9dac02f9be9dee3ffddc1be9e9ff8fff7708fce4778ed73f8370be175e39d406e17dde3b5c5e8119b85f778ed73f86f,
  0x61bf5bfef8c736fe8c47d6ee59ff9dac23ff2d9ff717d61fbdf96cffb9fc39e3b1cd5cf7e37ea7f4d1ebfbd61fbdff9c88f5fdeb00b394fe9a3d7763f616779c,
  0x8c736fe8c78ec0b828573996d878ecfdc7c28573988c6fd6fef6e15ce65b61bf5bfec9f0ae73118f1d8175639b7fb6c3c767ee3f58e6dfd18dfadfd37dcdbfdb,
  0xb9fc05c142b9b94b6c16fef6e15cdca5b60175639b2f4b6c16fe9bee6cbd2db05bfec9f0ae732db0fdc7c28573988c2dff64f8573988c7ee3f58e6dfd185bfef,
  0x3a81bbe7ff1cacddc377cfff4f8f5dc79c9fb9d1cace75079c9fb9da7c7b3a83ce46efce8e566ee3ce46efced3e3d770a04d68bcea05026ae6b8bd0298afeae6,
  0xeee88c3bcb20ed77744625959a66faebe8c3bcb2b077aebe8c056dfc666f321b7ffe3959bb8f3913f8e5673a83ce465bc72b3771fb3ff8e5673a83f67ffa7c7b,
  0x2782cfe1ffd7e80fb9baddb70ffa7e0822de3ffe1ff4fc79c97abfff477416eb75eafffdb20beb34ffe8ee82dd7d669ffdb203bbf62ebc8dda1cbb08962be6fa,
  0x15ce6231e7213e15ce6230eeb7b30f7e262bfab9ae7f1df3ffd3e3d771e0f7df9da7c7aee37ffe3959bb8f07b5bc72b3770187c8e8a9483ee6fe1ee1ffd7e808,
  0x9cdda8966adb6cdecfc0e5ff1cace750050ae6e52db0f60f85737296d879c84f8573996d82ddcb3ff3b5879cfb9ab9b939877cddcab5a231575ef43a5b611f0a,
  0xef4638e76fd76c3837962be916e1de6528ba7076e1c79e48fd120df8c97afc7a8c8fb2f7bb3794b7a42b7aaade47e7bbc61af686fc223ff2a9d4d59cb6415ca2,
  0xc79c96447b1cee3c33f58f0bb6d6fd78ddc13f1291ebd9aee726e0b6c74744ee1efc4b211291e08bb4bd93481cffd65606d1c9262e79c39a43de47e757599336,
  0xdfb5151c70f0b185ffa75d1ff8ec3aed6d9d5f280cfefef3e820ed773933d01bfcbf293d616fce45c82056d7346f32107e363988e4763b30ca4c1e7eeefe73f6,
  0x26072bae2193dfe053ef333fa881356da2d7b879a9c72e5c0fc1583bd7f65c462247b9720c33bb3d3471daee3be67cdf59c15cc7a2c491874101eb933ef22705,
  0x8eda1c3380c618c3098533209c6969307b86690fbeec981b7b76b093879fb9b7cc985cf1f3efe7ee18a087dd830909bbeec982cfb31b6cfd9d5191e72243efbb,
  0xe691fd5593c86c0a9b55cf441cff664e3988e436a37d36b6c8f0bb6fee476aa37f07dd831ef180a1776bb9a405f46d59dffdad385dc1fbf08833db23dc128777,
  0x6b40b30131fa98f151fbf99e2f913f3ee942a57470322cddf77010f38ec6572319041c77fc6238e07533e323b665081dc25b621b3767bdc21b1e3d8e6405ddae,
  0x79dbdfa11d8f9f8c837e90daef22fb212f2367425e42ec5bd9377ad0291bfac73a42239c93bb48d35bce5ade2e635e4499baeb19e1c6bf59a7ff639cc5bddaee,
  0xfecec67870b772b254d88f01f5e3fc38e38cff597ae773b81bebffe3ec1b9dc1e7ec678a32250e6d9f65eff8b9b463c7963fd73fac6feb119ebeeec837ea7f4d,
  0x96ff069df63d43772df10706e759ae1e93c0dbe9ad768e6defb51b3c1abe8549348dd51a4488dd43f12691ecbb997d96dccf01fe74371c3ca333c33df66a3e54,
  0xcbcf2791ac7fda67f985b703ec2b15cd8316c388165b77fe1e7096c303ef7eba4c1a9bb6e8e6c104e34b4981b7890663dc1158427ab43ba1c1b6b980a8c2cca1,
  0xf1f5ffad2a23754695104ed5fbd79d1c3c8be42db8059c5713bd7760312cfa4eab23c3dcdce5bce1eea6e07cfcdcf07fffd858e2df1bfac375f7766f3207db97,
  0x7ffe3dc128ba7076e1c47622904014fd775d473871f917bce996f762ce3b114820efafc3575fd4b106f07425e47f8e566bd120f459c73919ee0ec7666ca638cf,
  0xf736ddca28f599933b66a0c782c9dbf5db0e3d992f343eec18efa7fe2bbf0fbb063d97c349dffac4e29d5ca2f7c3140dcff089518f7f7a38beff4a8c5ef7bb6e,
  0xfe87a9ff18b27a87fbb4bc635f731ce0ec6251cfe67e6748e20c29ff39f7784d3b65b04c708948bd459ed1c89cb36956e9198c7ccda5a101def1758442bb58f0,
  0xef6fbf0ce30e8b6c2bb79c0cf9beabb83b0e58e0cffc762c819f1c5be0fe917256c466847a2c9c1bb7a251e73eef09a7481ea0c5ea933c7897c2eeeda412ef60,
  0x65bdd88fdeebae53556aa18c453ddbfadeeaf213f72b12629e29eedfd6f763c780392a957360c5f22f152986212ff08b70efc3df5ded850223466ce478012711,
  0xc762ec3669e7fb1e21f5e2ae6c18f7aea1c987d94d9d71bfac372bacfba8479821b4ab748f63353a76ae06e311ec5c7feabb83b0ceedfcaadff68fe901b3b83a,
  0x3a391eb5d9b34f337b623fefb1be7366d6e86e74722822ec3669e7fb1c6063d3a87876a4d54723c3dce4c3eca6ceb8f3c86cd3ccded81bebd3a87876a4d54723,
  0xd4332d0e757555ba41b34f337b62fbdb292dfd9554887a42becbf444ae375b17dffcef1b0b8aea523d1efb29d430c568c4eaeaa8e447fdf637f74ea1f88e9a9b,
  0xabad85f56943a86979cb3ead6daad08dd0a1a5472b0eb8f7f22e6c86f6c79466cb9b21bdb17ddc47fab669554887a44e51433cead7a549cb39d6c91d490ceed9,
  0x131aeb35fd179cbb62d9537033fad1b4ce479826fe75edf31f29bf1eece754347213f79ab6cea1873967d5abaaa391d94a5bce551c8f97fafcff3d632b7b1708,
  0x359946b0849a523de8bac7d5f3587bfb9beeabeb15ea0a47e7ee767526ffeb06fcfce7ee4720df8f7673aa1a3904fcc112fdb68750d4ed595367a11ab6d19e64,
  0x473f8f002223c7974dcdb08f1e527d7eb1e3ca4ff8948f304ff7fca3bfafd9b6511c759907dd864a23d439a1ceddcf51e18cb7b4d9ed1c80fc6c7311c80c708f,
  0xae8ffc7637ffb3a4d64bd0362e6e2b4dd623b8dc831072b39cc88f7f799abcc0cfa91335798b852427eafdebce8e0ee67ecf8738df4c7b9dcf72c3623e1a33e0,
  0xce09f2b82c716f80bbe50cffc763b1d9efd5b478843c9909776772abea3f3dd92cd3f11812edbc8be1b6d991e8c74e30db439c315b5f197a9b98dce23cf27fd3,
  0xff5769a50ce75f6f23fd5da694339d7d5e91ed337029f7b8b617253e45f4d1e4d55d060dd6edb87ff8dcc47edaeba95a1344243efbb260fdaddfbb7ba3fa260,
  0x6ee50067e8b16e16f661b939836a37cdfc22cfb59a536c737791ff9fb59a555982de47fe7ed6695566b7b791e7ee6d7fb1fe39cceb709c7a03bf901d3c7951c7,
  0x3b86df23590345cc55e048e61e2b8943a3194299c25e47efbe19f669b1be13ff69995cb711c19ff9bce61e8f7a67d0f5773576a5089931db86e4ed23d467e677,
  0xc7defd6f384cf731a56a019afc47427f57c228b94570ae9ba405717a75e9f98f41fb9a7671f3c05ffa75d1ffeed86b788cfe73b1942d12899cff5647e10c6d73,
  0x64d202dfee26b9b1ef6e8fbdb1e99f9ddf5910dcf06fd4fd90a6b7485e726abfae720a64fd91cd70b84b3dc1150be0f7f62dc986f5fa2a3c1efcfd93df18efb5,
  0x6c1af8caf9167e5f7427db70ef38b9f771a4f0338bae7eed90399d744817db6ba3a410279e43c33ff4afd5e90dadfa9bb9909350f430f5886dc9f849c07ded2f,
  0x469b55ef237eb7ee3b60dd89e7aadf933e842e8dd1a5a10b78fff8619d3f16f55db78cde845669af40a19bd08c452e7bb9c2f913f3e40935491f9844b3c2cb1f,
  0x67b9c6e782455dbf9b5af80769faf1f96dc59f3fe6391ff04e0ef64dc1fbd3d3dfd1c4e562feb0e6abbcfc0dadf58e64426beafe9d89ef5fdfd16b6eb1230ddf,
  0xcefb03b6aab648c452538fce09feedf39c2fac277fb58e5089679c9391bcfc0df7a6327f38f463718e959efc33394eff83d8b96ce4cb61f810eb3f22b91ff02a,
  0xd119c9c7e413b3bffbf307bf91cc8987dd8f735a059811f96bb69a8774211df74bbda6a1dd086d0bdfa10e4c49af82135fdfff1bef9ac6bfbfff7b939f358736
]
def delBitBlock2 : Array Nat := #[
  0xfb037089485eab9b0ba4884677fc6fbe6b1ee19b9e98ee60520767737beb95d0520fff8ef5c9a0a473f2bb5a1b7351ea316abbb744783d9b54d23bbc8f633773,
  0x2c49fcb6482617d8fbeed773482617d8facddaee691e7216fb61dc604a7becd42fdca7dd88da05dda6eebfa47a3dbb75dcf518114e891db8fe91e18cd7769bba,
  0xf12d2cdff58f33199f27cb838e7427bfc81f6e74273052f98952a30e56f9b8f647acdd17588feaed637793172610edff188e387888bbe1c323d8bb4d294c3e6b,
  0xa1f7bb663699cf7b6a479a9a371cd3db6d339ef65f489d0114f852bbf91bfa1b9225a4fe469d9c7e3ffb5acef12f51b5c311fdfd0dde25a59bfeb1bf8fefe86e,
  0xd49b7f3eab4b397d195bf50688a6ff5d3cfabfb1e876d6deb7b0688f331deecc9af7cbeda2349b7f0dc6fe4f55eb068874584bc8d749ead3734db526bac857f5,
  0x51b5c9833f667289a47363fd9dbbc29afe7beb936548f65f5fcf723fe09ee72444ab7db442812f9705c31ea4d8339dcd2b5cbe8cadfa96de88d773937078b863,
  0x15e88f30f9ddbb9ea0337b26ba6ecbaeb53d1db4744788c37d4353d9d11576aa9afe75a2cae9d2bd113d9bb5606a382db4423f3533739e595544bc0e76e7cd8e,
  0xd1067db0295dfc8b6322ee1eba5ab7d288846d3b4fff22ae44db5c0d75dc5954d5efa23a22b02e397118f3c8e708bad4f5d14b274a2237f631e6bafeba296aed,
  0xd904370cb2a83f059efcdfe5e373fff705b92387ae9693f9067cdce7c7fc9d68a5ad2f4e95e88e3811cf8ff93ad14b5a5e9d2bd110239f1ff275a296b44e9d2b,
  0x75e7135a2c7963aa220dfe5a365b3a3d1073968b5eb4e9723f71ff1c73223d4647eb4d18688a7cfd16d272d16574e9722cccb45b49cb4595d3a5423117d37c8f,
  0x787b9b51670b19bf19270b71b9225a4fe47a8cb6aad7c9c9deb4f4591f2ff47fe8b86922ab45af5a747d20827cb46c6ff4a20d062d16bd69d2e435b82ff464e8,
  0x7e455cb8c399431e7f1df72ba70c85bc7ffc3ffc6e628229c7d296daab25af5b6d11bf8febc74371ec75de75c31013671d8986cc4c90d6ae7ac8f5ecd26de230,
  0xf7e3c46175e3b76d10bdedb78c3df89c18c7ca2e6da39e707bf1d8d67a23fcc28e56f54da224ce8cdad192db5564b1e56db4458cd5754c8998bab6a1ff4d8b5d,
  0xfa325d56aac963efb688c5d5b5d3418b5b1fe242272fd64f5a8daae7d542312bad1918bab6ba69b16c7f8ade428b8bab6a1ff4d8b5d7e44e0c62745cdb473ce0,
  0xb45ae4c3447fd3639d7bcec7d4851714e76d43ff1cb5c986889648abafdad9488c847ff54baa52964ff909ffaf3e40fba777fa325b6aac963cadb6881f6af77,
  0x3eb9bbcda87eaee8865d0454c8fda329ef187bf14d58dd2ea94a56ffe46fe3fad61b8f662b37fd6314e76d43ffadf45b3062215f1dd7375b2911918a73b6a1ff,
  0x191fb50fd5193445671e9f5550e1ce387a9ebad727b444565b845d3bfa4bad17e8889466ccb191f91e21fa09a69dc3df8adf277b51207a52b50f5c9b76d11df5,
  0xf4baa5295bff908edb89754a524fe47bfbccd5c49754a524fe413bff7b273032577e3b76d114fe6e9754a52b7ff23d83f7c908948d35bf1818683fe89e2a3707,
  0xf75b442fe7b91ff05b8dc95693f90e8b2e26dfd1b6a73a95ab7eea889c65627abfb2f7ae8e8ca4ddd5116e37255aa7fe45b92ea94a49fc8b725d52ad53ff229b,
  0x7db441be9dee3f7b4461c172346fff1af7b0688f60725d4ea56adffc8fddb3b43e6528bea8eb317cd11ef6fa6e1efb824cf5295593e5f6d11ea323fa57ddafeb,
  0x66e8bce3d738b6d108fb09a5dfe45f7fee36360191729638944f6da228b913ffb5c6e670c84ba9d4ad5bff91bf809a70f52bac93beda224cf7f0137fea575927,
  0x27b2d3a20cfd66ee3e7a734eb45af3a74af444ebdae72e954e5a29779d3aa2216ebab1eb5fd10b54ac7862212ea90ad5bff90d86e951b3656aaf6da20dfbe433,
  0x74a7441f70da622952b4e95e8858c8ba8e4578b4e95e88f2fb5e455a2d7a544b906cdd2eab3652a4f38641cdce49754a52a4f386413e1a5d3fc66cebad4e8657,
  0x52dbd117bd9ffdad3890eba212ea94a56f386413e1a553ee7e2ebad4e866889ecb4e88f50fc36a24452a58ea88832eb20d1bf168b1e569d2a11e230df5d5b5d5,
  0xddac298952074584fef3f9ba1f9fef58737cfef9ac5b37d3bdc7ffbb837d333f7b445baf74726425d52ad5bff909754ab56f386447d36e7ff3764739d5d2d5bf,
  0xea7d7e1cebdde459f729efeec1cdbda4ee10819e9e14f523b1f9447f98f6b1de19ce7c377991e0f7e0fb9700c43bc76f08948ac0bfd97fd9ea3a41db8fe91be2,
  0xdb4e391132efc188bea63145dee631df7ed2f827e7e412cf1e7c44e633c448f66e5c13fdf3fad25b2453f68f8f527ac15a3bc1d423dedf4dc1f62c639d09d833,
  0x970f2b1e9edfd5f7b9a890a7fcf21b0be1ceb242e3edce9c61b687382bfdcc68c64015579ea3b921fc2479c879b6916c83e5735a509cc0e053f67b47203f65fb,
  0xeeac4a44a480ef8ffffdd375afdd5894891121b7e7f6ff358b617776b1fd92be6b14ddd37cd51cca48a7eff6da90d9e47f64aab62c53f66f6db5224d2227b76c,
  0x78ddffefd29afb53c65eeb15f9c91bbffdfa535f6a78cbdd62bf64485d239ad0d85203be3fff77bade1ceb4932922dad5a4b64837ff08f9ac077c7fffee9bad7,
  0x1fc1d89168877be1c321738eecfcfdc30afaf1d4a2a06bf387ff55b6c3a112e54d9cc89ce53bfe0ddff7354a6bed434d53132923cf214e3a882e0d67313b8758,
  0xa4ca487177376df7e840ee81ea34b43d634a06be32077471c3a5ac7d634a06be32077471c3a5ac7d634a06b9c72077471c3a5ac73934a06b9c723cb65dfe19d,
  0x3a4b08a3922b2effe899510e772dd378a88a392e3b79aad44d867443cdb43f15b492d9446f93037188a38f3a2e7cd56a26ffa20ffd1d9a230e39f23f23ce43cf,
  0x479c879e14cb08f2fb37ff63005d6d7f39e9ab1278c8f3902a0edb9328407adb3a3f0e882b8de3a93ada9c7575a4b08a3922b2ef0a4ca889158d3562658438e2,
  0xf4488d4ede39a8f1a219dcb870d765a4436e9970e1aecb488d4ede39a8e99447f6d75a2d58861511fdb5d68b5621ff488fed6614a5f432b486b3fed668dc0d7a,
  0xa5d76dd238c3556ab490f152219dffd4eca9d531d3488d3ff2bb9eb5539b3a23c1607ab9fe10e6f2126b339fd5374bc833ec7d4fbc6b56a76e91aadd42970e1a,
  0xf7ddcac54df471afc6eee1b9f53b2a91e192b612f238ca6eee3bea765523c3256f71bc8bdce77702d19dd1da856f71bc8b214ecc35d6f870c846e4f8696ea8d1,
  0x9bc25b56f5bc6a2f1da4056f354c74c92283edb8db5451fdb77771df50fc39d31e344519dd38c74ca23fb6eeee3bea1f873a63a6911df4b4699396ad919e88d3,
  0xe4df51237f67f53b78cda726fa89111cfea76f19b4e671e891dfd4ede2eb4c78c90e1ba639a5eff1ae8e5fac8917bb86e996eb7ac15c68fe91b39c8ff810e3e9,
  0x989bea2405c6f1fefea765da874a4f512239747fe53f185b0fc43e51a5cffd91a436405371daffc2b2ebed0df748b363c3d3d23ce43cf0af991bfb3fa9dbc5f4,
  0x7639ff8696a4873d25a433bacb3489adafe4719b9e52d55b091a7e62d8ab362478eca3699c8b248b4b33913155ae6e241bc7fbfa9d970c9de7a891dfd4ecbafa,
  0xe23cbee8a8cefa86bea99e7ba477f53b2faad25b37483727dcdd4ecbea72d9a911e5f7454677d435f54c4df748f2fba2a33bea1afaa626fa890afaee74545a8d,
  0xb2f5c3c913189fe30c729316bbba975ca645af5ade4362b13fc637f5d3ad777435ca6d6bd51af21830a73115ccbb9a756ffae575be1c323cd4da76d2cc3d62ac,
  0xadacbfd21acd7fa739bbc80c5d9dc2b6de19d5ebfebd216ecb9bd9af2868c72688f1197b5d1ff94d200c5d9dc2b6de19d5ebfeb44833fc618e69bb53b2eb94c8,
  0xf481dce26d444def20a63b8e4ba7a85d815cd5b5b17a44edda52b2f219cecc3d62a866c872b8b9c9f155018bb3b856dbc33abe117a4475e19d16593bd7a459af,
  0xece23d33f730c33616f9cc03f39f736735ff768db5979018bb3b856dbc33a79af485b87319b59df48f95cd6947cc2a7dff85a5ffd3cd7a43e6aaec0b4bffa79a,
  0xa4d7a42fe9f65373470d951b4ecbdbdc5e907f65dd6246196f6f6d516c5e91330edbffa27ea3d203f39f29a3717f3d1b6b2f2261b986c2df39828b4ddbf55ba7,
  0xa3d0fac7f488e33f09454efea3aa1b6a2d57ce448da053d3775fd23cbee8b5d57773d1159e6df9c6e17c0ce52b2f228535fb6d497d348f73b98539ea56dbffa4,
  0xf20dfc765ec186e52020f3f7549cc72959791e73e1930c9b97bbc836bd3f94fc61e7ee4e4ff9ee52f63cbee8a8cef3b6ffe8cba42e8fff4c3f3488396ecb86e6,
  0xa3628748f901b9b44ddd43b5eb277ad2203da5ec9a41e73ffece870ef3656911e73ffecd97ace3f480ec8bb5f7f7220daec8ff9bd25ebd20778ba7729aff5612,
  0x32abfd2191b2abbcfbd50efbfca7c743ea5ce75a6f47791664f7697bbc847df5f1b8e1ceb4dfa4c9a219dea4d4ecbb9a5e6bd219dea4d4ecbb9a6f845e9019d7,
  0xe92f5e91d8dca067a6ab4de92f5e90ce6da6ee313698d90b9e814e8d95f2f65e90e1e814f4d58df08bd220e5bb2e1b814fab2d95f126911fb6c7d0cf40a7a31d,
  0x6f4879eb23deb8f33552c463d166eb9adac8e8c9af59e73d69642dd0b44743e9bd21e7ac83db0c4676bd21e7ac8f2fba2a33bcedbcfa99748ecbae518ee6ab4d,
  0xabedb5bfd7fcf88d6459b2f4b3a6d99eb216ff6a23a32d37a43cf59096ff6a23a32d37a43cf590747361ea3fe613c3c6ed17a70cffc763de667eeff6d647465a,
  0x47376b211b6db4affe7cc55ac8b3a31b9e727e2c837db69367979359e3fea73abaa684f1642b34745cdfa19e7ac8557db6c8e8b9f2d9eb234f6dce6f2f26b3c2,
  0x4ede077ad6477f6dadfebfe7c46b228f3febfe7c0fc5906dcdb6a873a7a51defbc8a2a3298654b8617a5f59e34c1e2ee567930f0db6d2bff9f3156b22cd97a32,
  0xac8d3fbfe94d3d2876f03bd6b22dddfdb68fff4e7111cc957fc5590dfc2b6dffcbcd6b21bfea73d1cd3e6d2f5ac85f1775c0a7a50ede077ad642f8bbae053d1b,
  0x8ab590e4c0adb78579ad6439302b6de17cfeb590e24615b6f0be7f5ac871230adab585f3fad64783da3ffd30cd914ddbf55abada5f790e2dfe7d52d51c6f35c5,
  0x3d2f7ab23be15b6f0af35ac8efd036dbc2bcd6b22da3a06db78579ad645b4740db56b0af35ac8a6edfaad56d2fbc8b7bfce834b5471bcdd52d6438c1592bc2f9,
  0x7718a4636453177feb7fa6a9a12fd591bdc1b2ede07e2c841e9ed2f391e6dfb68e8e14af0a655911fd4930b086c8f1186ed5e9b311f7d644e988e6243c2f4a13,
  0x55906fadac72ce4fc5911fc7d4e5ceb78c7f16455c6fadac72ce4fc3c79cfae1db703b3f01beffa36b40f58f778b227bd393291436d1d2da578579eac86736d3,
  0x98fed43ece4cb393f1647f6d27ab75908eb36cfc1074c992291fd95ebf1ace4fc590d8e559c9f878f07b3c2be647858f5e3d344793b7e7cc590bdb4615b6f0a6,
  0x3d385fe4fcd23b2effb74c5a2ce4fcd22f8fa3fe9b168b393f348ff643af460a973932191fec875e8c1531e7264323c2cb643ed6265fea11e85ee5dfd202e4ca,
  0x6c59c99b20286b0ab277918ad8bbbd123b71fd23cf214e3a9570ecbb674c5a2ce4fcd22b1997ab277ee912eb7b1c73ff4932ce4fcd2353eabd12475397a45bde,
  0x1c6a70bdcda688ec61a53eb08b3935f486dcfb6ecd1ceb6c91fdd73ba5479e91fbfeebacd1d2de64797db6e9eb91cd9e133647f75c15c4746523cbedb74f5c8e,
  0x1122f773ecbb1c746c93127bd97d22f70bb8d7a31eda756f3d34860bfd1d9a21472d485fee0e3b6d4d72f65f48d5f5186bd23b2ec71f5368e49ef65f4873393a,
  0x76ce86da9e5ecbe90c15dd23b9a9d23b1c71edae93147bd97d23b1c71f5368e51ef65d2208215dac18536a8b53ae88b23956abff202f87a78b43aeb790be9dc7,
  0x6d0eb723ce45d9aeed376c82662d3cbcf5d64797db6aa4c7238db53c84d23b9cdc0b4c5a7979f45a47a7df63b3a62d2fdbcf5f48f3c9a1ce4b1ee773d9e531d9,
  0xade1e75d64765d98c73749bcbd8fab23c764c0e98b4f099d6b23b1cc639ba4c55bd97591d8e631cdd1c93935d6476399a8e6e8e49c9aeb2377572def20fbed26,
  0x69ccf1e0f6bf7cc87ccfbb52639ad9a6f2f3d7d229fba4c0d1d21b3c819031b368739996726b9e1ca4fb6aa4c7238db53c5f91ebd8f30c9f3c7a6fa1dac73ff3,
  0x7729aa895594c847bd866c85e9ab499d1f7d644e5face4fc3c25c34915f2262ab5cca46b9b8acbff37f9e3fd3564aa994f1ebcb66ab10f07b5fcb823e30dc6f6,
  0xebd20999750ffa717fdbdaf20822fa93c59cec903e73adcbea4f3c3b78c3c9d1d6f174f5cd2f5518f275b97d26fcbd676483b1cc267a47e846ec49e194f1ef5c,
  0x41ecbe1a5bb580a1ad732904117d49e2ce1a41f2afa596de79b4bd6963f7ff51db4fa9f143bd7a47accd230e8201176add6d3f7c3bd7a46afbac99686b55ba7d,
  0x48ff643af463b8a87264323e7d1a5afd6727e3097687babebbb84cf3f48bd2e8d2d7e6561ae23adec99e7e9067ecfae4dca77cde46ec49e781a4198cd49e781a,
  0x704d5350e739d96835c9af48d3f7dd97d5a8b868cf446a70d682f7107dfea3d22b3d97cdc2f811b2fd6726bb0dd893c844837624f210f5c5ff2d18e1ad384cd3,
  0xd6879ec754ca560ca93c847079fbd35d57fe5ecbad1c7aa5a797b2eb405fd52d17bb7b2ec1927908e037649e423803d4e156a4f2f9cc2ddbb47fc8dd893c970f,
  0x3344883d7f25c38d2792e1c693c32b0d6dce5355d73129203a1e9aff7cd635ffaa4f0cac175c76a4f0cac3318bb6a0f77e1f9a424f211c17dffe98706be91646,
  0x6e693bd7a407e73ee6ce617768db59790afd2cc30f7c38647fdd74ffd9c277ad223fea0f4e17f93bd7a414d91933d11ff56aba70bff157a424f25c11af49cad9,
  0x7d5ff908b414edcbeaffc845a3bf6da3a891861fec85fafa969e422d075fdec99ef20a6e76f4ffd1b64cf790beaffc27e2d1fbddafa968b393bd6c3e55cfa7a0,
  0x61ca754993242ffc27e1585f57fe62d07fd774fff5386db52c7fb7a7ffb6c99f5647fb7bbf26cb5642fabff03342fd6727e1e17d5ff84ce7e85f57fe422d1d95,
  0xdc565c923b1f1ead2779e7658d57fe629eb133b9dffea95559c99d50beaffc6c0bea5a78d817d4b4f2f0a0decd6ad25b242fa968b3dee30639b9e485ff84ef3d,
  0xd57fe13481cdb71dab9ef63a57a46abff3168355ff84cf4017676dbbd98f591aaffcbcf3d0063d51a5556726b9e355ff818b094e7cc5658e34969326762471ea,
  0x9ef2286e8eade1de44ed3aa4cd914375ab56f63de46abff1b06abff2fee1a9fdde5fdc17491d436148acdfcf67fdbe365aa4d8af4877e34cb5f9ec2452b8ef98,
  0x58e3d5a4cf6c91c7ab499d83242ffc6c0bf5ded835fa4cd5a4c9ea46bf498da79c99ce45ba25f51ce39018bc6c1499a9cc5bc8a4cd4e5e1de4783da4a31bb1c9,
  0xac85fa50f52c31dcb6480c2f3a00c2b9d41ec67bdf5f994e80c2bfe7a00c308c79d03b3727f8cf3b58f3867d4880c2b9ccb01861172b01857fef6580c2bff7ea,
  0x48c0fbffa53e8981b0f58328a9cf3af485fcb342fd2dbd0bf4ae1d0bf79d059add489510bf79b2c4e0a74d8691c38466f4e89b8ac2fd286cb179f69ae6adbdcb,
  0xcb85bd8e5baa9c35a2423d7030c90bf4bdc0f5fa5ee0b5f994f0bf4a9186afd2a461fd89d12133c917ff4a9182effe952305f6ffe952305eff4a9186ec5affa5,
  0xe86447f84e89646ea63a814dcf372590a9f2e018992b2e490acb25c238287e1366591e6a992b2e4901f9aa64acb92477d2d0e9e074845d641dcdefae5741485f,
  0xa856440426b48553b2e5101874acb924061d2b51124050c3927acb924250c3927acb9246ff6ca6be6a8f291832462b1caabd65c922c61f2e0187f2f6a22488fa,
  0x754f667f215bff3352910ad9c9ccd56880c3a56a6a23f39d6e60779166156e244797db245ff2030e95975915be70b6e3974e259017474ca11b2c0cf462030e95,
  0x48fe187bfc6d48fe18727f8da91bbd5c0c34588bd29c9c5647923f861c9fe31ce4061c9df18e72030e95834462861d2b0688c50c3dfe3068872f61f84da84591,
  0xa907bfc6a311e255ba4061d2b6a42f1fa2ff6dcbd64cebd22dcbb71b685b71fd2030ebd5b5203192f56d484a764bd5b52343192f56d480c3debb6a47f0c3a56d,
  0xc620f5ae8e901d2ea790729353c8299ca4d4f20f7f9a9e44e267293f90322d747480f7f81a3c83dfe068e91e791148d79c837f4fb8e59d74be80e95b520f7aed,
  0x133db480bf64b34adae7f212c33de9691ec67666d6dfff91f994d96e7f20a7446ff913adb62ff231661cb9fc8190e95cd209f5aed870191c1b8c4408ba4d5c0d,
  0x7b43adc881276ae06e25915bfa6e6ed90507db4751251434f6971875878e33d67f0ee2c8299cb8e691f9ff64a72b5670d7a42554e5c1cda6e866e19eda45b27e,
  0x1cdeb8b20e527f20e49bfe4763371d4996d838439c1ca47348393ab9a461c7293f91871c937fc884ff436e2591ab8187a9644c3973f916e61cb9fc8f04cf687b
]
def delBitBlock3 : Array Nat := #[
  0x970d77d49a91b1dfcad755a46c753c5eabead23cfc8d1cbab6902a5fe47ed0ef08cef970f9f7ce5c368ce67ee383a5fe41d2b8b20e6f5c590d9fb3a5716469d6,
  0x93e5c3d18f4f93e5c2dded63ee79df2e0d1cbab691c3d2ff223bf95aeab48c565bf5ef8bad691f3f7cb814d1b47512e30f7e3b2faf2bcc9f2e0e1f7b9efd37ef,
  0x528dae97a47b58fb9e77cb8787bc04a5b5eab70a361af48f0f780945cebd56e2cd86bd21d7248fce3c99357030f588d3fe5c7348d3fe5cd4e91a7fca36e690f9,
  0x691ee768e7362af55e845ecb9aad22f651bd5690a3b14a5f81962354bf5753a48c54a1a5a43cf14b9aad21e78a5c0cad22382b685b7bb06f3b4f87791e03ef3c,
  0xee79df2e0df66e1bb7380b7f9aa4482e39a439612fb6c4171bcd23fd23a9796be8da9123fd261f4bcb5f466d202e72abef9c96172e39a478f2ae51bfe45ecb8e,
  0x9095cd212b89117f8e6912677f8e691fb0b7f8e69179f22bfc7348bfc711215fbfc71122ff354891fbbfcd522439eb48097aefd5690e76f4ee6b4bef5933af48,
  0x5bbdd4e891dbdd85a67dbefb8957472275ba2476f7614ef0eb9f63a97b623913b149376c91e0524ddb247b19abebd6d9215f5ead79c857d7a8679215f5eac73c,
  0x6b215f24ddb2441db437a1c77791fb8e5dba13ccb08f753a2476f763d9efa8ec936c6c857d66c36246bea94ad7b1235ff0deb5ec4857d66d8ec4857c936c7624,
  0xfe5ebff217d7fc4b6d11ec66afa5b648b39ca94a19e48da5ec9a401cc26bd638c459ce54a5639e48f67b9effed7bd4a5907a5632a52db247b3dd1e75bab7fd3b,
  0xffaebbe1099212ff23cbec33b6a831ac84b6d10bd756215f4bfc857d2db2439d5d1f2af366d9e15f293f90bedbdbd38c42be526a791bbc5292da215fbd7fe46b,
  0xeddf4c6e4d5843641bc5248dff8bf25848d2aef8652485dcac6cee148465cdf865248a7f190d914a427f5d7799492174b42b996447edb475120a187fb2355261,
  0xc61bee2458cbefee2447edb475120a1c7e41b48c4839bee242ce6fb8916ce6d2e921193697491bf24d6732a242a7aeb2e03eff7448edc7f48b7a85843d691216,
  0x3ee96120cf98fcb09019aa45d0523b8ca490a8665248ee79b121e7dcf36247fe359f17582e62a199492277eef59d6918ee6c4c48f3bb4904edcc99b980df7122,
  0x38de2ac896120ca890d97923c81cd87a24361e4910819ff94d7591e40e6c27923db5c5b09e48f207361d4484f3d448bdcb0917b6c3923d796f6d8724774b090f,
  0x11ecc6e323b919cdff591e363fedc61d21175916e63fbe88f1b1ff0cead94d7590ee6e3e1bb6964535c50e865591ad099ba1ea90d8cb22f6c65904eef66ff9e2,
  0xac8b7422eb21cb8a65590a756369a2125b5906f15641ccab20e6ffac8b35afdf44368599872c831f3683f0784f17c60d52119cdff5908ce6e9e2c86c64658459,
  0x47ed52ace23f7fd68b65e453f6a9a4e203fdabe4e21c475e84cf59f3fde47ed6c5dc843ed54f3bc87ce3f3cd27101fed52ace2147d1a5441956479c86559108b,
  0x627ae7113d962ace20f9388b34cb7cc1349c42fb43b2a92244561f2710e6b3e4e2164d35191584ab38857c9c406e6c6d0520306497037ece21caf3391fb57c9c,
  0xd7fef23cf21bece3c359c9ad2217af9debff790bd799ef5ffbc8190ab3888e39b877aed92c4796ca7d5f57357fcb10e7ecca72ace23be727ece235f62ace235f,
  0xc47ee13c9c47ed25fe4e22b197487a22b34cad107bf6711e7205b6e2dbff8af20ca7bf671032793887ceff27106e39e672064bd7fef216edc6dae67acd217dfb,
  0x179de42439fac43136e5e41b4e310c4dd0e4f20fb9de77916fb919843de47966779de479585e7791ff5664a613521bede77906f76f3bc8f271164f27113d9fc9,
  0xe7c44d331e4c6097037301f2e1ec5f8ff14f07970266e602df73278f5ecc389f3c3e640ed193d60d97cb83cef20b65e41de77913df909a90784bef2191ee3643,
  0x27bfcf0f5885d91feb6441b6ab3ef49fcf0f588736d76f46220e6d967fa310171ef7388d5499e6ee0677432907a6de645a1c1e9aac8b4dd03b37736fd8f92221,
  0x4b079e4f531afa726dcd42737ce4f119aefba8e3d279e34accb4e3ff80fff386d8b6d9e9ab38a788cfe73b19639289ecdf71320ae4fc7ddb11febafb20db556f,
  0xecbe98acf5fc4759015315b8bbd1d645eeafa6f8573d427e15315b8bbd1d64239caae783f7cdabfef2642bea29cbcd063d167ee7b0c3dc478d8e84fdbcf88fbd,
  0x80eef619d2d8b40c83aa7ab9ea0def89c0c3d623f99ff1d894aa919945e11ffc07e706d8b6d9e9ab3873ab82ff202e3a55c980a98e2aefa2c80a98e2aef47591,
  0x29db8ec5d37f089ef75fdf9b2ba06bf8478ec8fe59fce0def891b0e81901531c5f28b23cd4d72ae94552744b90a853936e20c2f4632bb5a1bb618f45938376f3,
  0x55906d68fb8846ddd8ab23cac74775caab5f85229fb2aad7f4264230f4d5b92868e4c80a9bbb1564252aa4d9793237e6d7ea93202a6eef28b2129552590b40c8,
  0x67e7b611e9bef33979a0c3cce4db88308e7629e11cec559094aa92db1714859bd96c6c30846bb98ab228ee7595756ce64719a7eb0f574a660d75c8a3b85bd9cc,
  0x3ae37afece0deb7f53ea3d3440ecaed373d6481db23b6484fcf37bfd55510cef8ce3994213fb3b19e1c79c9c648abf847858c77dc478ecb30bf3e0e165ddc47a,
  0x5b67261a2270536d8d82f7bca6951aa864728436f7ddcac4a8c79fbea7ddda23d35ca29c9b7113089bbdb0e79a99d5d31ad15f29e10ab23489106e568aaeffe4,
  0x9ce537917b9f766c2f8480da12f20faefe10ebbc8677e0b2650872f85975728b27fb73376b1eedfa1f6c33a41badb393706d0fb673ffa2287db4c79c9a22b7f7,
  0x3533efe5e4e8bdf6f4de9aeb465916e3efff7c6994d40ef8f6da5474229ee3be3db6951d0827c9d2e9e4c84fdcaac603875ea921b0dad185223bfc25e44b3ce4,
  0x58fdb1f9d5cee55d28f4b441859cf3b175625cbc8baa5a0f5a32c8972f22ea96975ad19642bf2e5e45d52c34bee9ecb215ff1b17be8aeb1363f5834bed352c8f,
  0xc827685efb2c88ec54aef9abc556d8a24143ef9b591e16529a5e3133e50e769ce22dcbb966c6ddc2f8b8a89f9abc556d8f0453e3b1661db3751bfd373f393769,
  0x3d48277ee086ebd6adfc8f29db5ee4572f5ac4248e99ac43788c712a7e877d28b9166d87ea4a46ff7759bb0bc7e64520ae0b1c5be0aedb71c5be3c319aeed376,
  0xebe317d83edc98b39f0995a225cf99ba35d286523d6421cbf684dfea6e710b768ed6d733efc4ba5d6d5637f0ebea4b5a479cfbb935f4ed96c530e0cf5483d2b0,
  0x4dfd113125e33739338c462f87bce8e16e4ff8ced87a59ce6a03811c7272fbbbac739f49819d101c08e39397e33e9fdbfa21e6c7a7853d483675546c151122a7,
  0x8fe022b8a02eac26d420f99ada7efafc8a1bb69fbf09a4765f60fde574384ab784626c437daec5ef7c637e151d1d1d1217b67b1a2a123575ca50d6713a022a6e,
  0x1e73fe25f1efefe8c6222cfd836feb331ecbec2dde17617f08520334ffc7d3f565c8c78f6053ef71eab2df8bfd69cacee1d2932d7904116f640bafafc847ea1f,
  0xced604fa7ee76ffa305736ee76d7a2306fc54c8abaf6cbd2db0efdbaf6dfd18d43d8cd0f96cffb8beb0df96cffb9fc5639b2f4b6c3c07d0f65f43cb5c84461f6,
  0xd8f73bd5cd979cc35089edd071b7e7eaddfd1847e723bf1b9fc1b85f77e3717a06dc766eaddfd18f10fa1127db0f3934ef71ffeee3ce4f963ffe76b0d7ffc7ff,
  0x3f73b4ece7500eeb2b1cb31185bcef3911ebbb1fb3ffd3b39d41e99fb9b2f4b6c3ce4e31cdbfa31315fd7fb9fc39e73fab9b560517ce447afef584e53fa68f5d,
  0x73afb791586e5759f7508ac375f7766f3203467c08e7f167d98db67ed223235fff1f60dcee159a9bb9662311fac736fe8c783df7e769d9bb8ef9ffe9d9bb8f39,
  0x58fffff585bbf76f747f44c19c1bf3fd7b91c86d46f9f5b647bfb9beeabd0af50521dd0e0dab07caa7535672d91a6b79cb5bc6c6bc8f3538e5d287e0abb4d286,
  0xe9a3e377138ae277aeec7a3de99f43d5ffaed4a10976de45f0dbbe477ccf9beb38763bfafd9b6511adc8549370322b1ce9088e724eed23f3dde30efa1bf08f1e,
  0xdc569bac46bf59a7ff6c83e5f949eb056109ead1e176dfdce3546fe1b029f55cf4447edadb4ad09a23fc7d7feb4a88b3ed59dffdad385dc560ef5fda54619dd9,
  0xe723dc128777e3a1c3383f7e1353db22f7bddb77fe3d18e9c61b39381baddb70ffa7e1239878ae250f53285facfa4eab23fcef1b0b8aea523f6749ac97a06c5c,
  0xbc067ecceb2691cd8ff676ef0a6bf9bd9365487cd658abe5b2416fb1f7ddaee690ddf467d57bc8b7aaedb3dd0888fdcf0cffd2bf57a429fb214d6e90bce4d42a,
  0xddb447191fb50fb32688f1185d6f76d10b78fff87fd3f1fb8ff5f6447a8c8fd6ec3447ec821b877aa83f059deff2f1b9fffb82b02e3a54611f9a99b9cfbd5544,
  0xba44713e1a5baa346975db74889edcd85f0e7592171f6e74e30d9c9c0f36d22d907ef4ef71ffeee34ccfded10b75fe7ad7f442d610f0c4469dee3f7b4432577b,
  0x39cda1122556a610bc2053eb9aeec24bab9e9a1deef21dd6f32db9485bb71b685b7bb0da16dc7cf17ba1d1c7c7600c79b958955166ab108f8ed7fe15975f686f,
  0x37eb5f36fce71f3d55773d418f01f0c312104d5844aaacf656f209f59f089555f89081f64d5844aaacf656f2374d278cbd56b3cf39b20afbdce2d68f39b223f8,
  0x8b40e77dcdafabd12348918f1d8b715773acd9fa74ec4475b3d8d12e47af638cbd3ded8b7572dc55dceb367e9d3b111fb6d4545ccf18ebad5c23686425dc2252,
  0x69d50913bd1eca742032bf97ae7623d1eca6b7489ed2aa7b1fc241e9566dae47917cf5dbf2942412bf4ae1057e7b611ec676665cbaab06c9d2ae4c104f0b1ebf,
  0x9fc769566e22deeb6cf7423d1ed7bf5f4fba43ff4acb215eeae5efd7b3d521f53d2b2c85e7917bf5dbbb42a43ea7f819e1cda3a8bbe7df827dd9ba89c7ee9fe3,
  0xce6638f64197b129104d1dbb76a185dd91eb3ef5f4de41e72bff7b15a22c8baa6959de45b82ff8e3d91bb492910e6becc261a22b2b1cb3bf90e787bb99b94847,
  0x830d8bd6d9fb8e2b0e7ffbd8ad1159389bbcde41ffa735cae8291bbefa5d4f641979ca44535f76f8691834c8995934913d10b7d363cd1548b5d7372aa5a6f22d,
  0x354acea23f32622ed842b3a888ea1cf3658872dbbdcc9c37687c77f4419fdfcc71dd73edd18aea8a5efe8b1cf50a853979a0c7872b73c5a7a23c7647ea9ca526,
  0x26b79b1e159d4477d54a8e7c20fac7f5d57790df7a74967f383eee678577900666c6f9c7aaecdd44815f3eee62e8bbc8bdb6be1d0991aae1d1b5bc8730cf4620,
  0x14c6424d291c614c2ff202e9ce1d5313d86787b2227b55cf0f644158ae76c48ae7b3adbcd91a523439d6f752227230d5bf5910163fa9d764405efcb0ad9117bb,
  0x31d25c9d54c6d86d44414f5d27497555d3ed86c18f2fb5e2ae6c189ed55f9fa91018adfa97a8f3f748d74644af9ac11df74be1c9917abcf2db4d4883a9675b0c,
  0x1d86354e655eea5ad36b23bfffdedf666ccf0ecb20c7e581b060c7c9c206c18a1b862b7aac7acf288f62ff3fe3709877aa999783cfd8e35171af7e23f6d82ed1,
  0x11e5f7a7bc7bb47384a11e9bee3314accf6c291e41fbdf8ecb627b557e7b223f38e3bf47ded8733ad38c459862a918f54a22cefb6aa463d5288d5bbf4acb223f,
  0xad9113ada548934eb2219d9f6d2aa73efdd272881da3516da5bd065b58e510bb02be6ee78614de8f7b6b8442055dcb6a9d08f4df0ac76ccf6c3548f4fb4edf59,
  0xeaa73510e386ddfaead446ab9eb191139dd224d3d91014f7748934f6443652dc7af7eab54f8a4e510976a9ebdecaaef4beb50e511e727f7173d2aee0c4f69314,
  0xcde98673a4bead440efdedf666cc5556591e333532dafce741eb223d8bb0e375bd44065fadb3aed9c78ec3dc989359107d93b8ed9d5b389cee9314f6441bb5f,
  0x2206f8631e75910b53c7e8848acb992c36386c3f72a79ec88efabdc79321b0ea86a9e759113dcb0f6444e77961ec8873d339cebad44066ddef473ad57eb2238c,
  0xe4eb22dded554ea9e9695d252a447f661a5faae796d2a471db4a736968b1d586174a7369695d26f5906e75591e4c9bd645efcbcea9e968fdd27c206f8631e7b,
  0x34ee0563abe2d66272889dc6a8563d911dcb663ac88ef93ab79eb6d24e510aa59d6c3037c3173d9101a9fa7b3dd829e720da363a455b4aa511ee77aafe6ca45d,
  0x7d56413e9fb9b99c991ddacc7ea447cac6f581a3ce462b331d64462b3693ac8837d6fee49976447cac6e6fa86739094f8accc75911e0f738f8acda4eb2227be3,
  0xa64b63d559018cc7b223bb598f644561fb9b58af4a23d461f2471d21e762aac8f519a7734aa45f58de51018cc759111feed9539cfa944313f6618da839c1b50e,
  0xa909314f6443cd8f6442436b27b2237e4994847fa0849a5203173d91018b9fa91090d9e7c23d43f4a241dcb5cf6442f1f556992d8f3ce42e4d9c0a9110bc7d55,
  0x7f17b7f846a4555595a6441f7f65f48aaab2b6288f5595c733d91ec511e9f7ae2a4eb2b4c8875caa5d72f44eb2b65914f4fb73518675a9112c3d9117d12d331e,
  0x73d657aa96445ef6d1d62b6beebb85dd5911bf77469ff1ead5cf595eaa5911bf8feae5756b8513689c86fb37b6f5565e0dd97b5ff363d3effaaaacad3223d37d,
  0x6916b1d9508dfaa6b3de79323ce4728e2b7ba910767178c88d564f6442f5593d91089ac9ec88469fb895b573d657aa96445f205c8deb8513689c8711a7fc7ab5,
  0xb65107eaab47c20f916aa79d6440fb3b2a79dd28857ff86b655689ca22045bd6387d543be8734440fb733ae30da879c2d9b2b573caa101591f899964067f5dcb,
  0xb6e2a8e47bd762ff5a7152098cdde6b3a575a26432a79ec88361819e52a795ee904c644af9ba432a79fa510ca9e774a21dc35b2ab44e510b553cf64407a90b2e,
  0x457e74c0a567206f954dc92ffa21f3644cfd4887cf5226774a229fb47a9a8774a23be93c37555d49a0d1dd5916ed98bb32d7a1ec88d4f3d911a9e7ea447a58f5,
  0x956bc94436a7b2219a87b2219a8759104fc096efb7badf449764b230e4763f5223e5dd874d4f390b644cf6445b82ff8887cf52267b221f3d49743d911ad65ee9,
  0x5b55b13d9164b219dd1cef7356c4f4ca944765fe7b2206fdffcf6445bd686eaaae2cad44f2c79c8d68bdb4bfcad44f2c7d01b54f2b685695c837255aa6fc442d,
  0xc0fc2da97db6ba63d085ad29e88f96cf5657de7f08ac0f57d48bb528478f62ebac29b9f1c0535d773483d911f2de7eb0fe7b2219dd1ceffeb627a654a2204981,
  0x44b4885febdc15c5f57a9925a444c75cee1ef97b8ba3d9923d10a9aa4c2b8bead9923d11fd52615c5cecc91e8832b8ba26ba221ccd0367192ceca845eadeaf21,
  0xed11e88efc7f6444377f57a1e8cf2e23d10dbe1c6ec8e1d68ee9d23d10dbe1c6ec8e1d68eea648f4461cdf6f33af7753247a230e487bf7688f442ff51f67bd7b,
  0xd8fe844b1df14bbb148af23f69fff9142f9ce75cf44783d95c175f39cfb7de42ff51f67f368969108733be2eae1cf2e23d10e1cf27795a21b7c38deecdb873ce,
  0xd21c4caa440198c9fce122aaf8759bc857fa6552212ace9bc442a1de996c911aba3eccff287a21f3543bd32d922175d2eb48876f1fdda4d4ec6fa23d116ebd45,
  0xa5a4406efab36e2e8f6648f4471e9e58eaa4479fbb8eef9e95de8f59d10ee97fedec759e9103be3d3cb1d54881df1e9e58eb6488fdf1ae997ac92d2234ec286b,
  0xf3aa910b9f5d6852bf5b56911ec6743727d97907dc399a73a773fc3a3d11a7963aa911a7963ad9222cf74eb3d25f45a2caf54202eeaeb3b2c4a965c86c5f6f4a,
  0x88ee6f18aa91018f9feabd73ef23cfde7771b9716b5ab2b3a20dc9d559fab2b5791df55225de965548898ebb7fa650cfd59e8f4478f2eb1cfe223499d5488d3e,
  0x71e8cade7aac554447eee9532a75e9d73d10e1d5488f3f7dfe99433f567a3d10de1d54880dcd6f30cfd551e884a70c3cff110de3155223cfde77cfea5af52cf8,
  0x5d8d111dd7deaa444c3aa7a5a2b4ead15e914b3ee7a8532ab67d21f3bdf16638ab8d88de4783b99a7d32a7a5a5b693b791e394ea2af54cadeb4ab15511e394f5,
  0x3515e44ef2fbb7baf874ba59c4e9ec9b1b356d24bd5ba4e9622b7f56cd5ade47e6e61a3a8ab0ca657c546f1115bf58e6d316954f4568fabf08d6f798b0ca657c,
  0xfb35feadb47839c3dd5596aef442355223d3ed8da3a8f42bd23d18d5d75b695d55e452ae0d6ca86b7573d10b46aa4419568d5488f7ae55c576d9fa479c8c6d1d,
  0x90ab2bce89ac89dbaab3788872cedd559bc44063d49eeaa9b7c4413dd265bc445b48aeeeacf590a6766ab38c4c867764bdb7191a87baab378885595e7579eb22,
  0x7e223bb51f8880c55679ef5ab2558a2343f3c446db6f111a1b37888dd0cb7888dd559bc446eaba9bc4425dd575378888eb7aaea6f111ef5c7d55b20dcab6a989,
  0x47822b6ff68b9a220fdf9dc34441fbfd5b868883f7e7a1cd1116cff110e7f36522e8728f591ba9fe221cdded9fe2235d3b67f888d47e220fbb32665a9640dfd4
]
def delBitBlock4 : Array Nat := #[
  0x7fc63aab22b076db87e06dc9f961b08fc446fff111afa41a655641dcf1107a5fe220f339fb2a7b336937ac8f07b5c2b422e8f5483b86888df9dc3444567e6726,
  0x5dd6e3acf288bcf7eedb4a628857d8ea9447af2eafa5c9cbc47c447b9dc75efa9e88f0f7ff7ea8f914ebea21b15f63aa511a7abb566a7c446dfbf3b694c511ac,
  0xea94423d528863aa511ac727288d639645104eca9441b2d4395421b73aa5109f9e754a213f3ce6f288d7c267c72ed9447e6754a237ea99a1e72642eeb71d5288,
  0xab209d926a9447e64ec9354a223fc61ccb64eaea360ea59d1c3f327655d54a207dae8daa511646dd1329868daa511dc37c9354a21cdca53fe1485ffec9ad8a20,
  0xa510f3bdb029327288730ac6c39da158e7a259073772e9e9b2cbadbd883e9f9d6cb2ecaac824d52880c649aa511e363fe1d34deced575917bae6d2ab6591bf52,
  0x510dbb3b5fa88f1d87c44307587d57ea21746eb2e6a3cad2197190ed7ea22c8e35166e2e6abd8854a23c54ca8ee2209aa5103b26a944394764d528873728ec9a,
  0x2c407e221aff1109aff111d8c3f111d8d8fe221b71dbcedc92a303ecb1fc44361b98fe2203bd688f35364ab56ffe45b37d4e7deb446ec3f1107adfc4436ec3bf,
  0xc42ec61bfe1efd4469dedbd29992ce1dbb6e7f111085361bfe1efd4427f8ab370be62a3bcf7ea209ccdfcba8ba06b0adaaa4f64b25885330c6bd4adade89ec8f,
  0xbfe1efd447a2cf3ff7fcddf11015e7ffc3dfa880af3ffe32bf510c37fc3dfa88737b8f8b38e7dd4430df343dfa88bd9b82ae76ae5915e93622594773a4522b52,
  0x90ee7fe76cb8c6c1b0c37f110e77dcb8b79d98d2f6595e90ee7ffec7fd76fe291f0c72e37f111e41f59d10eb8efd1f7b62cf98096d8e0fe220f7ea23c3dfa881,
  0x3ce9f7ea3ef20e6f7b9d78679d3efd47de4068933f5487537906fe2224537f11158e5f96ced96dbf52c9623e5d33ed96dbf51e5880c37f111ee76d46e36a4c5e,
  0x87db2db7ea3cb103b2ba66933ab758f2935f437917ebf302b233e32bc8ef86a9d556f209cdd6788846573eea72dd0b107376def0cf3a7dfa8f5e907371ddbbc3,
  0x27907efc713f55de406f9924e84cad11e22177a22cd77a20f5bf7ed0f3ad7ea595e9157420679a5ec7de41b49e1ef22cd674429fa38756eb1e526bf58af48f1d,
  0xdd476577d327ab51d34dce220ae2772e3c9aabea3d8bb4c9a30f51a64e9a7a7861a2644063d3d3690d0e8875d4dc5a50f8ba79ab443e64db8831ef6e8e389aab,
  0x844da5a1d110967667e299439a9d525843685268e4e88d3690d0e88717d48bb528469e9b486874429ffcfb1e9f98a187a215f3cf1dce266d6187a22207b268c3,
  0x89489658cd72aaab2c8f67beac148f3f60529c041e73e168eeb37bfc234dafce8848dafce883713299b8fda11aa45f5a11a6d22e7446d8cda44a9d11a6d2d0e8,
  0xfb1f5fd4843a3a58b46e7a8d8da55ea3a2258bf99aeecc36956c7444cd77661bee66488c565d7f312fbc66eab2c8f28bb1f5fd480ddbad63e9ce63ad223d4c70,
  0xd88a39ef23f34ab2cf3795a91e885e9faf3d44d2e1b24b48853fc613694b23a237fee777af3a3859cb8eedf4370da55ea3a22ae3c74ba7bd0d7636957a8e88f3,
  0x6536949ce881dfbdbe9bcc5556591e21f0e3fa6a9e94ad47441fb2aac949d1e883f655595549d1e88fcd1e92df2f2c91e88dd97b5f18e3fda3d25be5e5923d10,
  0x79e427fc55bca326288eff3ffffd106d2939d113245d36b5d223aa23d6678b88a7067dcd4ba9b2bad11eb33c45fe7096581b060dff327c7791eb33c56cd4183f,
  0x287791a8faf9b2156c5648f441b855a73d11afaade2ac91e88bff876745fd2b517ab65ab51442ad793648f4469fb4cd7d3c5d6f3cdf28c92ca212ad793648f44,
  0x35ecd955f9a7a594433bdfdef4b645e1b055f7ecf99e156c539d10df763213ff84d96b0d931442ad79339d10ab629d1e880ba738e77911ff4dfd569567a234ec,
  0xade96f20dde4ce8f445f67181a1dd0db56f5ce7a209f5b7511c7bf0d6bbea34ab4ef9acb5914479a990d5d7760c1bbc9a3d1e88813f86c157dfb1b3ad522036d,
  0xde29d1e88fe1e9474d63e9b1ba6ea4409a82c213af526579e8837e2a747a2030eb0e856888437e2a747a2210daa553a3d1079ed53675de46aa5625b239b2258,
  0x8eb89d906d7e7441bc539d10a7c35aefa8d2ad3ab5af5969ca20de2a3ce88d7e45ff3af5cf64b7d0f420df8a9ce88f07b0d91d294d55565b135d266590b5f71e,
  0x2c8f3a23c07e8157db67d5db28883831c0a925150f4963a3d11e723bb1267aada7dfa80c702a0c5b07a4b1d1e8856943a3ce8898e6e1cb3aa224cf578ff89209,
  0x444725ab6eead8ec511b4c54cad0ebd2747a236890fa332ebd274b488d34945589b665cf5e2d220dceeadbbab63b1440d731278bb0888981747f388a2e962ae1,
  0xdfdef68fa546b81d9bd575aeb9e191c669b8d45ba4e744502afa1b31fbbe1e881dbce398933cb9a8a44405c14e4cef723e1e88a055f4365f74d9442b43ad91e7,
  0x442b4711e744055c2afab36511e8c7a76f4fa7f8744055c29f4f48510ad176479d116676375e9143737ab2ba9d2222392d56e9f749d8a234cdcdeaca854888d7,
  0x253aa8f3a2129d6c8f3a211eb9de9922129d547b1442fe255d91e74469b8565fb16474425d523ce889cd8a939efa1d10cb75c87439b96c7eeeaf5b59641f5cdc,
  0x906129efd63a234d29efd63a21b033c39b4c70ad0f7eb1d11e7ee94e79a23d11e5f615c3707a7ad39e88f55de99f4ab4451095c479d109576479d1095c47b144,
  0xebab43aa73a20dd756875b1ce886768dd7f17a8e915ae911ab14d5f35222dded63987a1e7542e6e2c99221cfceb02df7f841fba626d5b1d96425d758e884ab9b,
  0xe6ad0ea9ce8837c565d7ab63a23be94336e6a1536e6a28dbdf7b3c5497fe8f3f75f582906f8acbaf57a8e88f954554dc76d5eaf5508f393570f3afdb7c5cf06,
  0x7ad75a24da6e910ad0eb63b144771b0f750aabceb639d10bab43aa73a20763bb33ad488f9fd8455c2915b23d10f32b567bc8810302adc4b5d220776cfab3ae51,
  0x94eb639d10f9deb5555d8ec911a93ee694ddddd67bd1abc8d4a75b1ce885b9dc267a2129d6c762885c317a591d10ad0ea9ce8856875b1ce882aaa1ea1db16e0a,
  0x9a2ec7dd442bf1f3ea570e7446ed8ee2461e4c9abaa674447cfa523873a212b8762884abb1d8a215a2ec762884a19b7350ba55d8ec51094ea9ce884a754ec510,
  0x93f7af9ab154e884abb1ce88568bb1ce885d6b4f4621dd6beae95f7e91a957639d11c7397f47afa413fe5f67d2ae2a5b32445bb52aec73a22ddaad17639d11b7,
  0x991530ce1ab6c4d5568a8b23c1ed64355cf5063bbc48f6288adff7f73c2ecb9062fb8edb55e62a742275ee3061d1d8a2150fc48f62885cdc8ec51095c39d11e7,
  0x8bee3b6fed3153a106e476288f59993f3bb554cc510d8b4762886cd48f62880c5ea47b1442bff523d8a23d06618bd48f6288f0bbbf7b8ec8f6288eef11d8a23d,
  0xd1133f7bfcfa352fd4ba5a4479c9e1653eec189d4962a2d2237bafd48f3a20e866cced4968e88b7a8a21aa70f56d495e43bef75fa91e7446ae8e850f7c6579e8,
  0x91e7440c979e1af485db3523ce886cd5ae9964a441f5b3523f75107d6c4923f7511e519aed892479d107d0c5ea479d11dde2479d11dd7ea479d11c6d9dde2479,
  0x3ce880c5a291e74479326a37e36323ce88d6c4923ce88f01fdec6e8c7d423d6c4923ce885d921c339cebd5e91e4c9acbf8d8c8f3a211e95fa491e74423d57fa4,
  0xbbc9aa7a5ab4eb488277dbd5aab59922176cd473a23f67d52dd3a9222b029b5de41b923ce88f2b1afdc1b23a23cf22a7ee5de4366a479d1018bd48f3a235b352,
  0x4975a44062d2473a2210ad2473a202f1af0e73a4936a488d0c5a48e744797dadcdead248e751019abbd2499922272ef3d22cea492dd5a44395262ab7db3d101d,
  0x20316b51ec510b994e7442ed8c73a21dd56be8c96c51f42176c63b1442e65647446f895fe106e473a21737239d10d9a8e7442eeb9e6b3b2bc86c491ce88c3926,
  0xc5ad479d11a862d6a3ce88308b5a8f3a235308b5a8f3a234c22d6a3ce886c5a76288f1d865d4a442062ab53144362d47b14405f37aac2eb23d8a235b16a3d8a,
  0x9ce883acf366fa2d1657a5791e9f6f3dd5d1880c5ad39d106116b4e7446a18b5a73a21b16a3ce88d5b16a3ce882bf5a8f3a20df56c5a8f3a20cf86325ecbcbc8,
  0xe7446a6539d10d8c73a22dd6d7dd5d1144062d8e744062d8ec510d8c8f3a2210f6479d10b73b89122350c5b23ce88f1188e450d290d8c8f62886c5a73a20afd6,
  0xa190cd4b91e608daf771aa37f1c77df4c866f8e57751aff0cfd94d90a99d10d819d11fd8a6e1da631dcd7bfc27483d443606c511ea3178ea6ea7ee9e75c44194,
  0xc96c8f47a2034e7f3facbd4ba9b4b5a8ea5e901a73f9fda6a56a62b23acb21cbe32c5a6b8c656c56ddd623ce43aaaba866a5c83860740d8cb7f19d2c8f35321a,
  0xd5ea47b1442be6d2d09a21207abd48f628857ce181b8b8c8152d5514479827f48951ae3825b3f7afc7a3d9dcf775966e9e74469dec8f3a2035aeff3fb4d4baaa,
  0xf799c764b474407ecc9a9376fe885bd9281ff27c8f4635a4b38360c7b07c98ffdb81b96acd90d87d48f62886cd5ea47b1443952b66b8d7f97ea916dbacb2356c,
  0x4d2348910af9b91c9a21cd91ec510874224bed9346f638eaea288773b96f6c47e9479d10e6ba39b23c4e6c8f6288ab8df8c5cf11ec762883db356c8f62883fec,
  0xdb357a91ec9107b622bd48f6488d30cfe69dea12ed5bd2de45efcc389b60641ca7dc7d5cf37489e925ad4910afea1b86eaecebef3dea897a47a98d5bd2de431e,
  0x5ad28f3a234d2163a3b6ad22c52f4877f18ceb699220f3a87a5323d9221cf523ce884819f523d9221b357a91ec911e8335ddcf6633adead221207abd48f64883,
  0xf7592d32442426cb4a3d92228269d35df57bcce47ad4b496910903d2b4a3d9221207a56947a5a4441c53485922bf5969479d115907067197910714d2164b7ea,
  0xdfa5bd250eb65a98a21cd91e74459a6479d10d8cb4a3d9222b3dc10b25f3774a3d1d4479a9b2adad97a441ed8cb4a3d9222b267a6f93cb9e6ee947a3d11e1e75,
  0xaa21cd8fa8a20d99749b112cd4998a20dcbd4998a23e529a547e1b3fbf420a69f9f7ed8cc98ecb21b2fd4998a209f63b91c7bca33aac8e884fc318aa998a209f,
  0xd1d9221cd8ec511786771b65a98a22c8e747153f1924445e19dde2d93314435e186e5b2d4c511312e6dce8a9ca237f7aa3b4e5f571db70a5fc846ba2657265d3,
  0x1b7bbc75624a2659d91e883a77ea39d10b7808aaba9b5f56af4827d8ffb3de519d56474471bbbb95c4f3aaac554c8f441ff45f51ce886dfbec9430c99e880c39,
  0xed29e28fb0ddf466ebbc8558ab319c8fddd3a441775ea39d1102783d932eeb23d11bf9edb09b508d3bf51ce8875c74fe896dd17bd50f445eee9f9d5563e323d1,
  0xfd5ea4b4883a6e5b1ce88632b1ce88d6d93275a911a4cac747a22769c25e439ea39d101b9ea39d11785f0c6576a10eebd473a203775ea39d10cd88af7599222a,
  0xd10b49c29395a92d222cfcc5aeb550cf3ce5925a441b7363eea21dd6c73a234dcb639d11a6e5b1d1e88d48e2d8e8f446bccad8e7446bccad8e8f443ba3d475d4,
  0x39d10f33f523ce886c5a73510e6c73a2340cceace0ce9911b2c639d11b2c63a3d110247e3b3aeab4e73d107658c747a23cfdf55a7a311af33d8e7446bccf63a3,
  0x9bd0f51e3b9698f46456c8f65907ea39d107ea479d1037d4fbb933d9c4aa63b2c83a8e74414fd9efe4ec53c3ccf639d105c63d18ec9b52c8799ec8f3a21e67ea,
  0x90af79446a479d10ee978f51d8a20dd8a7441ec73a20f6479d10e5f7b7654cde87a7056c8f3a22636f7b54867df115e947abc83d8ec5107b23d8a21cbef6eca9,
  0xdc76e064cf444f743a21d758cf0e18e74431d8a2351ce88b7599f303492f4f7a446a3b144323ce880b010e880f7f8aa7d2f6ff08dd9371b57e244323d8a216fa,
  0x896788ec51019d11b59ae1edce239cfa7935c323d067fb3d989ff855a4432adad97a4419433a2036288ff1f65cde72e6e96cfbed9ca22f0ce88d7f5374726886,
  0x431446ea23dd4c9f3a2316f7ba88d451143a22459c6dcdff4bd313c239d108fba88f1e53617c5ad22132dd444b3c473a211d8a211f514436e6e61c9d10996a28,
  0xb39442bef32ad9441b4a9cd44377dcb66ab6aeaa2b531ca218f3a896f26e555b4445ee3b551e9e992f4f442bef32b53a88f633b336b99fc8c56cd4183a20ca74,
  0xc6eab3737b7af4a267270ca223e7d35759914455c15727398eba9f74345101add3dfb2b4a78510174de7bab10dbbba5befd5ef5ad98e510ddfbee6f575eaca64,
  0x26ba288fd93b74d498f4510d1fa54e75a92e8a20fa64d9914414bbefb57ce650c79a2b4e0ce304cf6cd936645109766fee765e683018cadf30def89158aa9cf3,
  0x7ddb17ab296a59ca21557c575991442aaf8b3f599144598673e9fb6374d4a2376b76a06c8ffda6bd21eb4344408bce0ce7d3f6c6e8e2211de75277b25d1107d3,
  0xa19cfa05d5614f08885baf6651dd7b6ceb6664510af8672ba1baab662ac7288c50b59b31b756703bbccebd92e8884be2baba2884be2bacc8a215feb5ad664511,
  0x36a21cd74f78c2ea90fd47ad6ad6d4436f6ed57c6c717afcdec9744469c22288f0f7bfb97e88d326ba2884be1366451097c5aacc8a20a6b3b2a75e868a216ecd,
  0xebda2f16b66d3a88f0fe2d6ccc92212f8b5ad5d2441d9dabfd6b5acda8873f76e27bcea7ad1eb65b44469de855b6eace1557c5ad6ae9223ce7ceced557c5ad6b,
  0xf16b65d24425f16b66649117afe2d6ccc9222dcdb4d39b56c9ef283379d55bab4886d0ce7d02eab0a8f4a7a23ce7d9570318af48bcb9e5ec967488f38c0a736e,
  0xcf54e9101d65ed6ad08c1ea20f5ea2922d557ad220dea5d3eaf5248a3656aa3caf485bb5264cd56c922b15539fa45fac22aaad29743aa8f2bd21b16b65d24425,
  0x967a488915dc3be84e96b524ba488adf0d7a9d2d6a4b9e88d6cbd99b511e1b39c3d446afcdeccda88fd8edcd2068829acf57526ba336a21b16aae9221cc30fd5,
  0x76c98ef63ea5b2488361436de3647ad305befddcdea64b6d4439f3f57b1f52db511ad84d7d446b65ecbea21527f17abaa886cbd6b1e92239fb9a9a89221b2f5a,
  0x2488f41fabe4ed5e7a556ea49117de5c6dcffdf79fa96c92225c6dcffde4f3f52d92447b17ef3de9b52488579ef4b7524885bfc31a3b33f599af479fac96c44f,
  0x5f511e70fd12d331ea91e9f66e36c9332488276af3d32496c92214f9d2ecad747aa421c16f76f76c6dbf913dc7e6e36dab592447b17cddea892447b17cdde9b5,
  0x88f7ae6477ad6a5b2288adf28d7ab5a96c8a2153b7a53325a3c590dd75ada5144593fd1766d28a21876aa3d64c97a7a234e13511e75d9bb5eb38d3575d446993,
  0x88bee6526eeb48a5b22880a9524da51442437af756a5e94511ee09c614aec6f532a8a216f64775ad6d28a223e6c2a0cea23fa4a926d28a22ae5bd91dd6b5b4a2,
  0xcdd5a96c8a23deb9dd6b5b52288f7ae775a452d914447cd855aa288f7ae775a49b522885bd91dd6b52d9144054ab5b4a2884be6ea452f4a288f7ae775a45b4a2,
  0x42d1d9e7ac8db74c37f2632d497444366ad2d9914427ed9ab4b664510152ad5d144251ae0a536a2b4780a956b322884897cdd48a5b2288b2054ab59914427e97,
  0xc3d4f292d914439b2e8a23d18d692ce0ed8736664510e6b5991447bd73bad6a5b22880a9597451122f7d87a53259e8a2258b9e119692a3dd343a84be1d2d9914,
  0xda4792967288773e61bd3a4a5b2288a777ec36a1ef4a41b5afa79496c8a20323f40e9a6d23d69672888fac547d3692a967288c5a37d9b97e035a3a0df5e1b20a,
  0x9722fe37281eb5b48f5a59ca23dcc65de12dc030ae2c549bfae96728826c73f53aa97228b3f53aa9720dad7d3d696c8a225cb7760ba6d23c94b39442ddd83574,
  0xcd7c7dc7d59d7a8e96c8a23d3ef9fb94fa56ba544b6451087471b47fce02bcd7c7dcc75675ea3a59ca22f73eaf528877552d914435375d59e9672883c33f53aa,
  0x8e25b22880a975a446d428d906f5457e96c8a23f9f1433f1526fe8e52ce510e55429d679eb20ae37a92d25b228889eddf371061579af767d59d7a8e96c8a202b,
  0x64510534b64511ac725b2288277c6bbd74c70d1ca5b2288c50cff28931c347296c8a20d92b35d8449692a8a22dafd2d91446babf4b64511aef8e25b228837aef,
  0xc8a202e8e7cd2916f4c6feb40bfcf1e41f9d6e473cffd67aa228872ad773288dfdeab5f981afe52559035cbd575d2d645108761d3dc27f38f20ff18bd57dbd2d,
  0x1ed3ff9f0a78d5a118f3b117bfcf5323e14478594fe23c69eaa56728829ae8a218e6e5a5a5bbdcf03bc22e4d87ba8f3c9e3d8b936e6a17ff393c466bbeea0a6c,
  0x88d372f525b6a237cee5ea4b6d445937c39b5b25b6a22c9be387ad92f4ea23664b0f548dda2888fb2288f20ff7cae37a4e7591447ed6c8a20ae37a8e56c8a23c,
  0x9a96f496da885be68f373673adfd2a8f2bd209cdcdd35ded8fd9d9726d2e97ab4885e3eedd8e1abcb2ebd23cd59f74f29789103bec61df42d6c82b63ea794bc4
]
def delBitBlock5 : Array Nat := #[
  0x67af12234df87552db510bb35657acf3f487727434df3756b2bc488627d5eb794b6d4469baf496da88df02de92db5107d0f6dd3b23ca5e24469b4b7a4b6d446f,
  0x3e1ce38e30fbb5e6e78646ad305552db51142936ae73c94b64911ab3855b25b6a23d467ef52234aa1554b6d4469b4aaa5b6a21766b7dea9fa42a6ee4e869a6f5,
  0x6d2af4abd6a21473e6b3646a149d2db51164d4293a5b6a20f1c76d5a88d372a96da886c0ce6d475bfeb4a5e9d446f81554b6d446aef0aaa5b6a23ce7e7b7355e,
  0x34d7c5a97a7510eeaa5b6a2350aaa5b6a2258cbd63a4413d64ba947aa4259ccba1d22153f35223e5542af4a552443b93d25b6a22da5552db5116d2ad92db510d,
  0x6932692db511b7ee932692db5118ba4c932692db5116439d8ae7a23658c96da88df26325b6a237c98c97a7511be4c5a97a7511be4cd496da88df266a4bd3a88d,
  0x2f4a488df357e96da88df3499b4b6d446dfba4cda5b6a219766a4f3aaa91be6f88da5b6a23fefc31a88f5cf5485429d6795e91be1ba4b6d446f9a1892db511be,
  0xdab5115892db510bd985587bacda88b61892db511aa9a5b6a203e7e6dcd47bdbace974eb9d446f91c96da884ffb92d06b4b8b47297a5244387d8c834917168e5,
  0xda88d364cfbd336a23ce4d257585ddd3a88f73b5bfd757a9cfa7511eb335d73bc39e8829a5b6a22cce96da88b6bf4b6d4459fdd5d6bdba222dc26a5b6a236cce,
  0xaa6d3a88b6bf66d4459fdd4d9fca2217e6cfaba6a23cdbfba9b63f74e911a6d7ecda8899b4273f48d364cf559b511bf62badc65ee9d4469b0c4cda88d3696f4c,
  0x688d799559b511aaf71559b511aa9b69d442fbb46c75e91af3f1b4ea2365c99b511b2e4da7511bb0d773484fcd87a4f74a488d5f934da7510e5368d22446afd6,
  0x72ef4a875111ff1d8d9a53bf752d67a20a6cda88e3f19b511bbb18bc7dc5d6c6dada238caacda880fb8aacda88d54d9b511af3f19b511bbb18bc7dc4aad8996b,
  0x84bcfa76215357c2eed53da85523ce43d163d24414d5e56b48775afaa57dfa44773ffe79e8b1fa88e3bf6875111cbbf68751179c3f116594911fcf3d1659d444,
  0x523d35d315f287ea23be950ea238fc5f511c7e50ea21ca6d92b6cdebbbaacdd7a52ba88e3552fa88e33f52fa888e5aa97d44472cfd4bea238efd5f5109245f9f,
  0xd0ea22b12fa88b357578fb87dbd64a48f45a4439ea5f510cacc2b56aa1e88efeafa88f2fbb3b7aaf945ad223be92fa88d3ddeabe369e92212797deef55bf5965,
  0xac5cea22d862e75116c30fa7510d4e3dbcea23c4bf643af0a379e88e35573a886d7f536bbc88e5aab9d445b26b5573a88b69153e9d447801135eb3829afa8829,
  0x222dbe7a88b66e6d445b48ce6a2221d91f2649ea90e53a888e843a88b64e10ea23767d2656b137ad223c4be6f1f2649ea90ab84c93caf485592d8f39c5607a88,
  0x2db510b765d4f9326f492d91440529aecfc05346d4d34c798b4b4b37e226880e45375f5b74856ea5b228846e6b3ef6b575c2883aaaa1aff506377a884b5abf75,
  0x163f6649b56911c78a737a496c8a23d3ec7d93d2b752db5104c955369d441326f49b4ea20354f7edb93595ba97a75104c955369451016db5039cbea54bde6d9,
  0xb3a8836553e9d447e77ea54ea223ecdb7ad8837ea54ea20d955369d4427ed98acd7acb6ea4bd3a888fe7b4b563ae7a23f7a6d98abdebf192d91441b37a4da751,
  0xdafea73aef22b2fd496b3a88fd9bebceddb595753a880b6da81d2df19d737fd1067c2ed4925acea20cf85c92492d6751067efb9fa924b59d4479fbdb8f492496,
  0x924bd3a8847abb4c0c9620d9fe315a492f4ea23cebb37a9f504d656924bd3a88375bb77f5b64c947cd46f495d445bb766bf891db556ad66cde9c20d95573a884,
  0x7dfb79e88fcfc3de9bae39db483fea42b452bcea21cb6d5d25126b37a579d441b299530b76efeb6d5d251f351bd257510cefc465b77fe1215a492f4ea20f4856,
  0xbb24da7a23c7636dbf17eb6df1156f3eada1e884857a92f4ea23ce49ce53791e724e46f3f06ab7b5c74e3689e73fc2b4f2e2216edb87afb6055c775d66a70fc6,
  0xd117adaf59c6bc6d4466f20df7e530a1de4299a3559134738487ea4bd3a88a13a475f79d1d4925e9e885575c9b0f751e9f7a7ddaef88ab7b1d492bcf4405ef86,
  0x3d8ab226989c7ba99b3eead67511e03f5b15acea23c4be922b59d44796b82ad8ac92c47ba99b3ea4b59d44243f4fa7511e8c7b8b79d15b1bcea235df17a2e833,
  0x26d3d111fd0d9fb7aef5a97a7510a7ffa1dc7a6bf8bff54fbadb3b751a4f4b6f3a8879e93d2dbcea2122ab9d444b8da3d7abd3d11afb1c32b9e88487eae7511e,
  0x56a5e9d444ea4b150f441949e96de7510baa7a177f901fef4c9ffd449365cf3a924bd3d10e50ce770e9c7c0cf441ba30bafb24da7a23c7949ae6f43f04f68d2d,
  0x388fe86cf5ef5ad4bd3a88375b8674ced790f362bd497a75106d2315ea4bd3a88bdd15c8c99e8827a5b79d446293d2dbcea20a787265a36bc872b2ecffaa6ebf,
  0x4bd3a88d35f1715421db375057a92f4ea23d4648baa2b5a97a75112c2bd497a7511586e79ba35de7b85108dac92cb68de405f0f49a5aa23ce437ff5b34156da7,
  0xd4b4b56a5b107eede7511ee63d4b56b3a883f757a7511e8b1534915e9d447a2c7cd6b4af4ea20ff3e6e4183f525e9d44771fa92f4ea22587ea4bd3a8837dc7ea,
  0xc853d4e7933bc9d0f1c6996bff01e91f4ea20abf2cb68de47ed1ea19cdf186149ea1cef0dc2b4b75b5109af59c39de1b856925ada884a7fecba51106e94fab6f,
  0xa1e8a21b671ebb12931cea220e5f9ba369beac4a39ca48857f766e8da6fab128f44510df67d97be31c669f638ed510171d7e6e8da6fab128f4d441fa7d3a88f3,
  0xa7e2954d3d10aae7510943ddbe8ad1107eae7511e721d7345aebbc83d25cea21dcfff45cbb7f06f3b319b45a445b5fea6f43d2440df6dac62526394910a9a35a,
  0xc496ee9d445986737fb6374d5ca23b92d5e9d4462a4b57a75108aed3e3595cdb3d325e9e883a47d3a880ce9925cf441b3a47d3a884a6d6948fa7a23c07ddcab,
  0x385e9f4ea21e66f7cdd3d10bae77873d11babd3a88c5dd5e9d442ff757a7510bfa0df4b3df790a39b03364247d3a884b774ea21c264f14b247d3d1092ddd3a88,
  0x73a883b6259d8de42d25cea210e59d6b3d11a7d3a8856109ad8a5ba7510af7148c52dd3a88b3e4d2a2a8fa73d10ac21328e96b2288e7faad3d3511ee773dc27f,
  0xaa3cde47b3dc2b422e8f548f059bf3d2a8f3d646ae751092e7511572b6f53aa76a2cea23f34ad97b50e76d65ad2215d3a1c3d63d14462de92e7511bb79d442f5,
  0x6dc3c4beb94d8de45fabd3a88f76f8607fed8746d5aad7579d44397eaf4ea22cd62b6ad56ba3cde469d85df1691eb4b3944425fabd3a8873a1ebc3cde439d0f4,
  0xd7bc3d4bc166784dbfcbd3694511412fee3c6eacfba9cb68e52c8bdcbd369451143de9b4a288be87bd3694510e7b175bd99391f81cacf353b7b32723f0472521,
  0x595179dc5fce373463aeb276f4b7569117b97a6d3a88f1b56b864cae91ca488a1ef4da75117d0f7a6d3a8872f4da51446987667845fcbd3694510e50d19a5351,
  0xef3e945107c5a1bb67ac837487bcfa51443979f4ea23cdbf2c24d9e887770b1f4ea21cbcfa51447aaeeb0ab44510eee163e94510e5e9b4ea23becdc4e75b0c57,
  0xa88299cb1f4ea20e6d91ae73f48374872c7d3a887ccec73a90e9ac155395e907d4dd74c6f22f3e945117bbcfa51441bc25e7d28a203033b53521d35a38fe0299,
  0x8e1bd34474b22f77aa1d441ec61b735167ec8687dd6c27646944510eee5ea8751167ec8687ddf2da39c9d511445e7d3a8896127b69e88bd963e9d4477d72c7d3,
  0xe75117ba77373ffaba7a23f6e7aee9ad53f58ec8a21dd1ae7510ee8d728a23d9ef3929e19ea917ae751111cfdeb9d4427fe1efb6732723f05eef5cea22c85c3f,
  0xb851444cf22f94a87a28877a3121e94511e0f6cc9433af52e9a72886acd624e8e5144565189a2f4a288bdde8c4b8514461d46269794510b9d44763f02fce11fa,
  0x514422b91933d10167247752d914459f299e4d17a51443bd0e5c28a21de8721e94510ab2e8d7b6a21ddb4e4eda51442999fca4c4879e2c94d5b45eaca21de8c4,
  0x10f4a2880dc0b6e97a5275ba51440606e055cf4bef5cead1ca2889c14fe6e9ad2b5b511a8ef515ac8a21df5243d28a234c377461a0d2f756b2288b3e53bcd17a,
  0xa8877a1c87a7510ef4393b69d443bd1974dd292211d9d196c56b248846c94354d4bdd4cb5a423d99fd64d9521de87345e9d443bd189a2f4ea21ddc2e14510eee,
  0xe91759cad1a6e94910181876d8dbd47d5ae186910efa921e9d4459d0f24eb74a488b3a1e4eeadd29221ddc345e9d443bb87597a7510efa9345e9d443bd0e5c3,
  0xcf5ea7511e7ec39f5de8caacf2bd21de874a51443bd18a528a22dd7df556f7c66a2f4a1e3160e5d8eafd69aacf252c8377d1754d3a887770b87510eee10f4ea2,
  0x97b13fcbcf4578910eee2528a23d9efae2f87a27528a21df5294a2880ecda979cf219d9991446fd763c9b0d13443bd0e94ea21dd73aeba33463f529223f38084,
  0xe94ea20d0e94ea22874a51441a1d29451143af53a88fcd2efeabc3fe450ebd4a288a1cad4a288777129d447b3df8fc3d2d7d3a8877d4a53a88e33a94a7511ecc,
  0xfd92cd2855ff20e94a2883af528a20eb4194510729065144312906514469873970d5a6eac992ce511e1d2945111fa074df3523ab4b39441c5d4a2887129d4450,
  0x5ea5d11442d35e5144698766169bae94c96c8a20e94ea20ebd4ea20eb419d44315a0cea20eb4d79d441ca4d79d447874a7511123d9555eafbcea212af5292202,
  0x4833a882520cea212a53a88f2f3a8834bcea212f979d4436e4fad1f8cc468598b5d1ea9094a2884a94a288f2f28a217a94510b419451092a4974451167b1c91b,
  0xef28a23cfd873ebbd3559e6f23b992f4a288f0f7db338fb555218dfb992f4a288acacfcff914bca288a2f4a288c5a5e51441b654d59c253a882e1d4415a9d441,
  0xea23fad6d292229fd6b694911dc7bcea23b8ebd3a88ee64bd3a885d1f725abcea2296ee33fd2d5e751158e5372677b91f0f44772d4bd3a88bca2883de5144771,
  0x9d444c579d447858f6d92657a452d9d5e75107bcea22583b3739a7a67eab3d1075e9d44325e9d4447cdf433c7074d45643556a5751015afd59325b6a20dd92f4,
  0x91e35da5dff186d4bce948d4a2886a145109a851447f6a145116d350a288fe5356da48b2a88de3b697d28a2363b755e8651446cc464d8f59179d4452f3a889d7,
  0x88eed4ea20db3d0ea20a2889614511428a217f428a21dd7f428a22650a288d69439ebf0b11e0b1f37728a21159b28836cf428a216edffcda38923264ba5e73a1,
  0xa21350ea234d75a7bb1c9c5ad4ea234d75a7ba6fae2d6a75116cf43a886b67a1d443879b3a88b69a87510d6d350ea22cdbfb369d442fe87511abfa1d4419943a,
  0x3a2eb5a4b6d441b6b52fa8873ff8f662ad4ba288fe7b35ae4d36a88f2fb36a9bd5cfd446eaaa86bf4b39443ae76ffce0ea21c3a88961d4462b8751143a883d0e,
  0xf4274f72b53ab5ac8a212d099319ece15ab390d914413f67c29044656ae756a88a209fb3e1431a4d35ba7275445106db24aea20b8592575105c2c92db511e790,
  0xecfa6929a5114439a67d5c9b0d2e5118ac92a8a216e90e73f5118ab525b2288f3f6065224c96c8a212964954511ab0d1e525b228836d92fa882e164bea209fb3,
  0xc53a5514425275d1441709d74511632677f8d1f52e6f55ddf025274aa288c564bea231592e8a227b0ae66d2d498f45118ac99914462ad4cc8a212964ba2880a3,
  0xd2551442437a4aa2882690de92a8a216eddfd6d93251f351bd257511ecbfaaec79368aabc2889c499ebd611118a75f5118a75d144629d2a8a20db3ae8a23de1f,
  0x2aa9545106e9554aa288372e2a9545117bbcedef8bb8bd3651018974511ea32cc3a2e83d506969618954511ea32cc3a2e83d50696966fc4aa2884b7a5d14425b,
  0xa5d24425552ba884ab64aea23d07e19b9e1a4885fae8a217e954510aff1a55b879b2882b932fb391d0993d6974a26882b932fb3936871c92eacf5484aaae8a21,
  0xb9a888ee7e53f3575dec884b8a8a2129b68a212f8aa2884b787a884b7868a23cac695c24d10bf5f5106c35f5106cecbea217e95d4477325751094e97d442ceb3,
  0x5cdad92d91447a3d9e5c5325b22887cf511dce6a21b15d44782cbc309bd910f9a2886c55144771d54510181ea203034510f98607a88f2b1994934425c5d44255,
  0x3a5b2288d349545117eaa8a2377bf4511e80454f8510bd4954510dafea6ef5906d7a92a8a203aba3fd52f1159362b65e1447e7dcc992ba88bee6d6759e8a23f3,
  0x8a20daf52e8a20daf5332288f6cfc2a545104c95a99914412924cc8a212b1f53b265a591aaea2355451092a8a23c4954511e7892a8a23cf125b22889eff3f0da,
  0x5e9745117a664510149d96cd52cf664510942863b67cb6e2cf6645105cb24c3da945ae2a288d0d1446a5d1446a664510bd4ba288b706f30d922d50f4510bd4cc,
  0x55d1442d974510b666451108b6664510b64b6451122efdb37694bce52dc5e94b394414c96c8a203d44068a23c2cb645499e12e8a21cd97d63677764c89a4ddf0,
  0x6d1441ba445107a28836c8a2086c8a217451131745106e62e8a21974510ccc8a23662ae69f591447b67facbe9e88a2192d9144264b64510aae8a21c557451131,
  0x34e1441b92ad5bff90b39ca217a98e5106cceb5d8e6c34b9442d24c7288d442fa8866d441d9b511e99fad95bcebea2155f5104ebea21c275f510b93afa884511,
  0x4d52ed944383bb651166b8738fd219442d6b1ca20ad6b1ca2131ca2154c7288f6645cdb1e6c30ceb290fa190931ca20ae270a1435cdaee105614e72885bfa8cd,
  0xccdabe9a7a23de8a1a4da7a2032885bb528e516a8d75592d8fd42a6b5fe9aaa90c72885fb1ca217a3d8fb55523dedc6b95548374a1ca20fe1ca216cc72885f55,
  0xa23d4606253a8ad5117a4d44452f49a88837a6a2236f3d26a221af49a888486f4d4440c8cb770d7bd6795b239e8819196ee1af7acacad91cf442427a4d44479c,
  0xa8885aa23cf2053aa88c5a5e9109a888d3a2ff933d11a7fc3d14cda7a2126a2238d26a220f49a888778426b5443422f43a441b9e935110aa6a223d4661c7515a,
  0xd44462ea7ad1e89cfd21e7ad44455d7b5cdeac9a228a99e79e9291adb5d6acd917eb5110f3bf5a888bf5b5910f327eb69e88e3d6a223bebb9a4424bf5a8885f5,
  0xa2219a888559a8883d6cd4447f6a223566a2219566a2209df7b5110c794cd44413267ad9a888f1a8885bb5b729a4d1d28a9edaa237ee3126bf10688a5ebd511a,
  0x473f5fc22ef57d111f3fea3125eafa220f5ce5117b467a26ca2264762de4d9441048fc9c99e0f5439441fa7a220f48f4441fa739447a6f9ea87288d511e6a886,
  0x8abf3a507ee48f4446abd111a855ead4888c5feb98885ce511dfa7b86422bf58f39e0f5e8888fffb4e26b488726472ef3d779f0f4439fcf448911ed2fdeaf3a4,
  0x44f581ccf135085d73121d2ab578aa86b2111fd10dfd11484488b65116d10e223bed076779e13888a2ed6cef3c51106ea2238e8883d110bd111a7a22123d110e,
  0x9149aa67adb4dac9bd2745905381035f518aaa39d642a56abcdcac629bd1ceb23be171db013f85539d647887f38338c1b89fc2a9d32c8f419affb8ea06c8f1bf,
  0xd6591e9f7a61a671758744b4ddfe2345906efd0d1ceb20df9ab54c9641bf35064320ddfad7a39d641b5af5af473ac836b5eb5e991d647bd16f47aefd4ab23ac8,
  0xbbdc4c8eb211bf17a95d60ddf4bd323ac876fa6dba8d6bf8b44e91da118a7d945bce0877f37aec231f6845eeb2d9fe2d1bdb596479c87d30d34706bad364ff11,
  0xebbd89d4c8eb23fb9ae87aa7e9354586d27bf52db4a4cb20ddee239d6479a9a35522d2ba49d6479a9d35555bd6be927591bffcedbbdb20f57dccd83736262641,
  0xdad4322fa5e991d645f45ea647591abac38ff1240bedfab44b323ac8bf5af4c8eb20aba4ebf5458bf597a991d647bd1687f8c4ea647591afa35592d73b1164a1,
  0x9168269b2c6fd2932c8bdc473ac8bdc4c8eb217d7354a8976bcda5d1da104cff18e991d642f666cf5af43a5c8f05958b7cd21a657e9d6590066b39ff7ab1e230,
  0x5969d659198cd3ead1bd91d64590eaeb449a47ac8a08da7d5a37b24cb2282369d15a37b24cb21766ba43279bf4eb2c8d6bd323ac83d66cf712e4066cf65d2548,
  0x2153fe969aaf5acda52d4b21d152d26027f142ff4adbaaf60d14b52c898a94cf9ac52f4c8eb21bf6ae2d0e91eb21ca5e9926590e2bef4c932c8f387e87eab79e,
  0x44b93fd664c4e32e97a4e96b52c8d337a75ad5b68952267f3dca512d6b694b52c8d3f33f9ee52897a4e8a5a9647ec2af4d0ae69e921e896c7452d4b23434c8eb,
  0x52b449a4cb238ed9f7ad6af5a75964240d324cb20d90d324cb20d939e9926591bf364fe38a8b09035a526590e239d6438991d644b93fd664c41574bd274b5a96,
  0x399adef74ffcdd92ab3c87acb209df213a18b21b1323ac86c4c932c847e2d6ae74b23f67a371641eadf7a6499640573d37e3fdee5fa44c899fe6eb2c8d49d165
]
def delBitBlock6 : Array Nat := #[
  0x6fd3ba96425bdaf4c932c8f7f7fdaf66e675cf659096f627a6499640ed89ebd46fd3ba9642a991d642a99265917ba3c9d1f52c83fd4455e861e0f55324cb20e5,
  0x473a5c85d7a8321905af4c932c843a3e6d619d2d622452c4f4c932c8799f6f627a649964783daa830f377b26623cb3f9cbb19b9e357cd53a8dfa92d4b212ebd4,
  0xa590b56fd4ac8b68eb5ad1bf4eea590ba0b3175c9b5e22762034c932c839e9926591471b7c5ba9647caeff9b8b52d7d6590434c932c8df17a2efa1d2e4253d3c,
  0x65904ef5a526590949deb4a4cb21cff731cbedeeeb7ae7b2c8adff17e369cec405f99a928cfadeb9ecb23f76c2aa166394211d6b5a37b25a96423ad6b46fd296,
  0xa7dae52d2bd92659164d68e537c2b9f75835ce7a11a61d9db0d72dbe24b52c8bd324cb235ff22f94b44f3a4cb217297a90c8c54c932c8a2d6b476297209de992,
  0x2c836aaeb646b21af4c8eb23c8be595ec925a591ef45a2d7aaf3a47ac80c9eaf3a47ac84c932c873b3f7eede52d20f5964348b3956c591e833d5ad263a5a9647,
  0xe2296a590af86f3a4cb211ceb215f37773ad21d52b08e8f5917a3a65904ef474cb2032c86d997a18b21323ac80ef473a4b4b22f4c8eb2034c8eb237fdf46492d,
  0xa521befbf2cfe70e64f5c55c590e50a7aa747591a6f3a4cb231553a3ac854ef74a69f56c4629bce932c8dfe2a472f4a42d2b6594b52c89c95bc47d08d4ac754f,
  0x2c8a7bc22a6efbd8a5a9647714d34e58744b4dde554759642427367b8972153a3ac854e91eb20de74996405dd6d63df5f9079bce932c837b1499646fd262d2f3,
  0x77753fd67935eeea3ac8a2f4e96a59082eeea52eb936bcd0c85eb14b52c8d8ff88f6590e66e3af4bd4b3ba964517ac52d4b215ebd6296a591ef4554ddf7b14b5,
  0xa5fe8f6d3a5c8373134b22f3a3ac85e9d1d642f4e992c8dd9e8ce91eb217a74b52c826bd3a5a96459935e9d2d4b23cbd97a74b52c80bbba94657e25b1d475901,
  0xe9d2d4b23dcef59c60d2dd4b2368bded42bac07a74b52c80f58a5a96473fe3a265ba967752c8e7e6ed44cb752ceea5911cedf42af57a6b2ceea591abbd09ac3b,
  0xb20eb5ff4e91eb20e96a590d2c735577757d5e9cdb5d67752c8914de891c775c9b93622026aaeeeae7d39491759dd4b2266a75b6bd5a24dd67eb11a74b52c8dd,
  0x9fb45a9641d1d6442512ede8e8fd6591fbb30ca71af0dcdac8b21c9af7eb3eb6a26d73f6843653536b5a939d1facb2272b45df43a5c83a64b234e992c8373a64,
  0xc74b5421224c5a23caa111cbeba9644c555ee3c9913b8c867ae7aab23b97b44cb21526bda265907ed0eb20f795907ea3d67ac88946629fa8f55641fb45a96462,
  0xc8a69d27194d7eaaad516476359f79396467a4cb234f6594b52c839ecc932c8a1d646d0eb22de1de3b38e58a9e368996424da2659019b44cb23ce4ddd0d50a96,
  0xb23d6bb45503542ae7452e4771cf5d1d647ba9b2d763d9b4f590df7e49985bd55aec79f68b23bfcfcfc641cf5d26591e6dfdfe6e3d9652d4b20822b8a7b1e932,
  0x901ae8eb238d6e36959d3d6406ba4cb2375c543a331d1f420366475903b37dc70ac416ff1adc6d3a74f590aff72f436406cc932c8ddd0de696c74b5420e7ae8e,
  0x27b59a14c9641eba5a96479e4d59eab0527a932c83e852d4b238fce43aaaae7a8307b323ac83d99325907b694c9641ecc932c84be6087ae96a591ed330c5d265,
  0xff173966648f3d6432d4b52c829b9b6ae8ed94b66d21907ae8eb21186bf29d084fef68086ca4cbf3f59641eba64b216574c96437dc8b4bcfb69644f67d0a64b2,
  0x9fff709c995ade36abba7ac89607a98ac8a1b996a3ac8d6ffedd9480ba39b2710da51d643324cb2196a4cb235fd6daf436433264b2196a64b20766fb8dd88f65,
  0xb22f7fd95cd9aaa4cad72890f591dccb51d645b0b8eb5685756fa15a190b8fb73a2de705bdf7d31f645effb72935fb8a932b5bc6d5774f5912c3ebebac8bdff6,
  0x74d528599967752c89edc0c9a398436d6593b11ec1fd0f6dd3f31dcba4cb20ae79f7d2d0ea5c8d3d272e92656f5cfd65918a57499641b97499643323ac865a8e,
  0x591a6b9dd4ba0f430ce4d223acb217475914f0f7473b12ce27724d641f51d6459f1daa9739663a3d523be7d47591ffb8fa8eb234dc36f9a5217499643bdb4ff1,
  0xac833fe7ec5ac22d0cbd23cf591e5f62eb5848eee3c6a8e54cd91fdccdd09ab0bf48a3ac8f4dffee6ba2cdca8b1a6b51d64324cb2153f62e5514996405f79a47,
  0x7591b6671f6aaa427e16710e8b4d8eb386c451d640659f27f5252f28f5484996414996432e83729a9657eb3acb2197d6ddeb456bf59d6590c8eb23523ac848a3,
  0x75628eeefe55591c696c96423263ef9fbff174a5a3c05d3122a77cd92c88fe72ef556426590e6996478ccef2785ad4b20f916b52c8f0bbf153c23ac828eb2114,
  0xb21f364b2030364b20348f9b25908724d57dee32cf590b3ac85b259096c9641b92d92c80c3a5b2591bb176c0c5d53c6aaab7706969522ddf9936c79d15ad2c8b,
  0x7549f533107a37e3694b5885f1715421db37509fb9b7878a97e52d5e727d4dab08d9fe694b5883ac864b21cd92c85ffdb6bdb0e6e9644e7364b23175bd5bd6b4,
  0x23bab48d4f3e852e4236934a5ac4237e3694b588f60fefe021ed7af48d0a7b50a5c847a8df8c914b588439ca1afffb2e1524c6d7e23ada42dd976d5e85f11b5e,
  0x42dfa7dd6235cf192296b10a67c6bacf7316fa3165e9139cf192296b107dd768ea2476cf59a47a2c3cc2ad12e19321eb1623ffbccff6e24858b10bae7ad56599,
  0x353cd94b906d2694b58837e3694b5881f7a67b6ee6ef2975b791df0ced3262a6da43ae3e587d0871dcdb0c4b0e24d296b10e78da52d62374d55efd48647a6f86,
  0x6ba4b75691081a449a5966d5bab48419d554cdcf87bc8dd865291269657d5bab48b67b78972166cf712e4246fc664b58846d6754922c41b3fc64b58849a52d62,
  0xd992d620dc7b897212712325ac40625bbe1d5f52542170bfe1b3ddd91622c9437ac7cd60ff192d623b1d9b61f301b48c96b10c6d2325ac42f45b84f53656944d,
  0xa42f50ab4bd188dfb9b2facbb6bb9aa644d26b5e42be3325ac432f45a717d4d94c8f8b5d25bab485dbff9a7b6976d322779d6d3485a712e438bbd992d62138bb,
  0x9f7a520309ae8c4782cfdf873679d4b4b6f22b17b724b59cd2852d62029bf875ba4562fbb492d67f2852458848c96b11e3325ac46b1fee3edb5ca644c9b4b515,
  0xbd1fab748ac5874620eb9d6b5cabd1fab748d5f98a52d62125f98a52d620f4896b10b5cf4ab904f5ff22d9e7ae96b1079ce51248fc3b691a6cf3d74b588c548b,
  0x67ee4b58854ceb3f725ac41d75d53cabd1fa92d211ff26b645883f98a52d6234df725ac4066fcfe88ebb2ab5ea556e91bfb3d99652a11abf3b92d620eb9d66ca,
  0xd6926f76b11dc96b116fb92d622de294b588375dada33aece2db67f88f6d2194c27ad7545444c87ba8b10197b13620fe7725ac416f9fcee4b5883f87fa5ac41d,
  0xcc27d0a48b10aff76dee16211ea4f49790748912d623c765e74b7964b58877d7d75a4874bac41cd94896b11fbe33d6964d9e73f7588f4b1eb6f4f94d621df5f5,
  0x949fa96b516217f291245880a4d9491623bfe3b12db3e842fe4d949162119b9fdcc44ad91e191bbfd9eb12aab05f1652a1067d1afa4f842029f192d62377e299,
  0xd70c3726a9c5b9dd5ff173deaad620294896b11b6f49e747add202948922c43bd91b36624d27ea5ad4588f39f8fe12dc1dc3b7366ccc527ea5ad458856e6c372,
  0x8846912d6211b38b27791ec5da61c7fac4ceb3a3a8b108fc64b588971ddff6164cce3e5468d997595ef21b7f73b4f9ac37dbcc9f5eb133ae8751621ce5c78ff8,
  0xb423774a67f88fa10b73491623d3efb9cd645885d994916217c7a52458859de65245885d76dcd3d1621673690a48b10d31cd6ddeb449bacfd5a42ebb7a4f4f45,
  0xa5245880c693c99aab2a11df656891ff20cfa0cd3aa6ad5d3a8ad20e6c9e9491622b3c9142b10bade925da11b63efccd3f8895f4a4af217d735d5d763c9b4ba3,
  0xf718ca7a11dfdefc742788fa113192331d1da10d8149e94916217f27a524588f2fb3abc22a8a47ea2922c42ee419627b791ebcabfdeda5245886c387acc192cd,
  0xe08b3175d2d96525a579132f7a3945f554d4752f48b7bb334e6c35a96b10d9c7a5245880a4f4a48b11cfe631ebe95d23a8b11e4b8cb08c91227a768477f5c98a,
  0xdc0878e5f9dd54cb32ca48b104ef8cbd7264d1fed086f5b4add47b1622cfc76f0878642fd571bf966594916238f4a48b11c69149162265ef498beaa9a8ea5e91,
  0x65245880aa9b967d086cb32922c40548524588915cf675b799ba522669fcd2baca4af23764d763c932baced085bb4c735a32a6a2b48baceb690d815214916209,
  0x922c46ede7ef6e55989749248b107c8b73aab312e9249162029364916202935a922c4797dc7d7eb7672a6dedab52f489ce6b441f9fc8bc2fdeb361d1833eb116,
  0x6ff197a439a5ac45efcbed7478e0cb35db53a92d21cd24588b35f9dfe1752eb5a8ad202a5491620f1deeb2fae9e156e85c526b5bac477ddeb361d1833eb11c6c,
  0x6f3fe4d94916209b248b10bf5bb39536f6d5a97a478594f7a2c41348a48b1037c9a452458855532691491623f617f9348a48b107c6491623c992397d758872fd,
  0xad217eb7639726b5a8b11df675bb1d08485245881be90a48b10aaa690a48b11e3248b9ee562a2bac4ec478c6e7681cba10fda1037c9b2922c479325ebdb879d7,
  0x8f45691f3fa524588f459bfd2ebe9f5cbd7a42a7fd72150ba7a52458854285f34a48b109524588ee5a6fe2a8a6c7af688ec42fd6ef7c9ad6a2c436694cf8b5a8,
  0x25c86491621cee3f8b6f211eae748bd216a48b11e2d491623e7d9245882922c41f21491620cc57ff9e067ea5e91e9f66dc6d3e86b5a4588d2922c4055d7d3eea,
  0xd621e64874621214b58833e8d7d49d0055f49b3d25a4248b11efef3adabddaa54a70783d9955378abc5a495e42ec491623bedf3a32556c8b1167e75b54cabc29,
  0x1e1c55d648fa749d1d2bd23c3de9669523fe42be7b89988b67b8998826cad2c46bfa7a4d9e4b104f364b10149f42b4b10dbdbd27d0f258859365331096b10952,
  0x3a523790e41d30fa1bd3a7948a46f214f9de76e5ae8f548b33e84cf43a5c80b7d0ad2c43b85d1c322bacbe966d3a4ad21dc2e8e1915d6d3e96a1d25690ee171d,
  0x2dd978ed33db6ff0d0e94cc4233427fb65f5773550898de9b47ad88e31cd532cf56ad7e15f4a662175d215a588b247e79cde7d3a7ad148de439e230f3937a74f,
  0x91c3f572588ddaeb2787b79090ad2c47ecdfc160c8aeb2a6966d3a4b10ba42b4b11fb378391e1c55d648fa749d1d379015215a588f391cdb7dcbd65f8ce2a2c,
  0x7a1749f4feca906fbb6f70b10e4e0d7fd734837981aa3cf48291696223ee6ee1aa924a56a94923791ef6ea9bfe6d2d25881dc09fbd5fcda6548f6cff52aae4b1,
  0xf0f7d46547aa438e7a93f5cd21b0f3a299881bfe163feaf58967907e81f81b7e7f1fb9ac255a588bfc5a588bcfab4b10c8d74b538ebae2496c9d6cc7622cfeba,
  0x331079f53310931684f3a521b0f3ea662355bcb528d7ad2489c82d43a479e5263ba42fafed03a25b10db93ebe3638f4fbeed3fc3a62173cf0d2a41e74533103b,
  0xcc4449f6d9abf8ba5e2d628a4a916fd8bacf5ee39c363a426b2191e2bb27de948b61fa87e62e7386c8d21b23b97a1b22759affb44b622cd53b933109133104f5,
  0xef27ac1474b0fbf748f20fae93230d55a69a8ad3907d4cc45bd3e7d8533cb2dbb9fa8893ecf0ada7f033e331d49521455cff17a32a2474b48b35ff6896c41d14,
  0xeeda4131afbffd6dce391a9988dfea66202ad92662350ab4bd188dfa2998829ea29988f3c8b5b67c5d61fdb353311fdb114cc41db74b935ffeae891e7748d6d9,
  0x496906d779d25a4b485de74b662166db4b10bbceda5885de74bd2c42ca45748f3c84ea948aa589153f843613311302eefb8de2d390e25aceb4e41b93311e5b2e,
  0x20f7ef3b249884a4fdd66623cbefcfdecc35cad316493104fdd6d2c41eb2b75922c4313f75b4b10b36ccc42ef3b33103bf1d9c6aaa97c585de765ac41eb24fab,
  0xccc45b1bf67f8d2deb94bd58bf7596b1096fdd65ac45fbada588b78778ece34a94fbc8bf75922c4362d2dbba52bc86c5a5b52d295e436248b69ca57904fdd666,
  0x59e7eb7706b52a47186ec6f4b36ad12c46abceda588279d9988d27eaf5652d2122774a394b48515693c344b1179d96b10d79d96b104f3b2d62189e765ac45fba,
  0xd59ca57a5a41b6d2c45eb39320285d35a94fbc8bceccc45e74b6623555582a5d2d1bc8bceda9889c7dc30fd2b4e96952274b9555bf94954b4a90d79db4b11bfd,
  0x81e9620a72c5432f21777a77dccfad43a2c42e757486dfd8cfb89918acc41b862d36b3cb11786cc461de792f4a95abdec45e759e58836b36b5abc836ccc44c8e,
  0x752f48dda5cdb6abf5aaf8ba1b555e7eeea5e909fb1ee6b40b306b6d7a1b22cfcb6bf589ddc611721988d66212d9880f4b1145e962031af4fb0d8e9d9968b101,
  0x32ef4c7768427ed094f349f4fbceea5e906fdf9cdab66abe2e86ef3aa5ba97a4299ab2fd6aab3ae9e6ab457752f4829aa6b5fd0dd422736ad9aaf8ba1b2c754b,
  0x92d95d96a542093d495e41332867b6af879d68eba23ef3baaf23cdd495e47efc7189a5570cdb1d2da11aafc253cd2c7499dd4bd23de8bdfd46dc74a69e79b5b3,
  0xbd495e44c9ddf6b6af3d2cd6b2a5973a9508993bbed6d5e7a05716b2a5973a95088fa5f9eea129c3a4ceea5e90b7644c99bf8928adfb79d4a8477e73226f9ef8,
  0x1302fed97d484d1932b5ca2a98af48fdd92945d6e1b36cb38b6f21c9cd8bf5866373e674b91f9d17bff3584a92bc8f0e92bc847bdf4a95d74b90e2fdc5bcb641,
  0x31f97a5c86c5fff26aaa41a13a54884c55ea1aabd39cfd234dc36d93882ade97212a5420af15722f491c8c5dbc84ab6f209b2dbc826b56de4517c397bdc5b79,
  0x6da3d7badb790c4fa6ad7918ab90adbf0e4c84a972354bf41f830e5d0f5fd76cfd215965f8bfd76d523cbd2e473f714c9168b143c2f8553ba42e87855d09cfd2,
  0xf6f20645b7907b9adbc8bdeb6d92daf5c854645b79143f8d96de41f315d4b6f235fd4dcb54bef712e436245b790f99d6de46ab9b717228786c7bd1f6f22f784d,
  0xb6f21cd6de459f0d2e7970fb7906dcd6de4136becd573ca3dbc82617e5c7aa4f76f234ceb6f221355efd51f6f21537aaf7ea8fb790b9badbc8ac77840d384ea9,
  0xf22aebd970f75e478630aa7d57916c0cf158e9eb536abc84a553eabc8208ade74afd4daaf235b7b7b8588f2cfdc842790b2a877904359eebc85c84b90b6f2363,
  0xa5235e45f7b3371eebc84a55f0de4471b8abe2a40529355e47814a4d5790bf3fc2daaf2352949aaf21dd22bf4b6abc83694ab7eabc8f599cf77ac9de4052a9da,
  0xebaf7ea5e90aa54adfaaf20dc3ed2534b6abc854b895bf55e47b038de2ab7eabc846a9daf22aebd9b7dcb5908d53eabc8f11aa7d5790754fa96b23766cd9d080,
  0x1f516211a46bc8bef66650c5918aaf856b2238caaf87ac8469355e4797dd176a766cbc8f11a4d5791dcc7ae5b55e41e7a349aaf20fee2de515e46e2a4d5791ad,
  0xf7420da5343eabc85f9dcd57911c912784fd5790bf3d0faaf20da5543eabc8f0bb3674db9a96b23d4c6ab32fa8b1017cf0d7fe42fd8d0faaf21e6efaa354de9a,
  0x8e7aaf217e7ae5b55e478152eabc8f34cfaaf23cd34daaf220e845550faaf23c0be1f55e4422a687d5791e5f7bf3a7b38471fabc72f7ea4323114a8b386bea2c,
  0x30e5cf2e6a2c44e62e6abc89cc687d5791398d136abc87727bd1f3089cc74f4daaf2122ee5610f6f46461cccc76f6d57917be1cc96c749eabc8f304ffd976387,
  0x45292a1f51621c47aaf2035a3d5790e2e77355e4254c9d6b53819138f43eabc89ce39de44e3b69f5162122ee5610cdd8846b3b69f516234cb9aaf234cd0faaf2,
  0x1c6f0ed790e0ece90f6f3eb1621cf55e421d4d74cebc8810dcdc3253559673758843a875ccebc89d7d0faaf23e57746e55d0f292a1f55e43366acbc711f2b3cd,
  0x7ff3791e50f7d1737907b5032d463791e388daf2145971ba673fe29a13bc8f1c70ed7917b3c32ba2a1f5523436d75af22ccf5d978e23c703d3b5e4243ada388f,
  0x6a4b10cb86bb5e438e1daf22b1b51f4fa6f21c64ad790b9f52b16217ffc9d17458e73791e39b5e471faf2aaba62dfcde478152b5e47af2aaba63a7f9bc8f1b4f,
  0xe4772e4fd3eabc866bd7d5790bf64baaf21cdaf228f36bc87362c4054ad790152b16217376bc85d74ad79139ca6f21c0d76bc870867d6663a3cde47b03bfa3b3,
  0xc64e73f6858e73790bdebb5e41baf5daf23ce7cae543a69da262588ee5ef5daf22f5f55e42f7afaaf20cfb2d1543bc8ee5ef5f55e4772e4f5f55e4772f7e9f55,
  0x516209afa8b10c1afa8b11c743eabc83d7d4588c53d7d45883f4faaf225cbeabc89769f55e4194f5f55e4194fd3eabc84ad7917aed7917e9daf22fd3b16237d2,
  0xf56f53791e8c77bd3f5bd625cbb5e41bfba9ae72da9a8b4b23c9911c55e2fa754843bf3d367af175d523cfdec9e2aadea6f23d81c65c55485f55e41ebeabc85f
]
def delBitBlock7 : Array Nat := #[
  0x72e4fd3ed08fcefc453713f4facb221152aff21af23d577667b9df23c07e76eef206feabc854faaf2176bc85d8b10bb14b211aec52c8d3b1620334ec588f6077,
  0x7d6591dc95bf4facb23b833d7da11dc19ebeb2c8ee5e1ebeb2c8ee0cfd3ed0848c954d84772e4f5f684772e4f5f5964772549ebeb2c829d1cd767287d2943647,
  0x9091adafacb21235b66d65909192466d6591dcbdebed08ee5ef5f596477256f5f596416fb63350eb2c8ee5efd3ed08ee4adfa7da104fdf7f0965f75691dcbdfa,
  0xeed39eb20f32e9e8b23badae1917bd2cf151ff23badaf459037f684775b368e4782c3dc469480cf5b9a4775bc55912e5f684775b5f684775b5f5964775b66d65,
  0x5f752c88e5694659f422de9f59645bd3eea590cbc65f752c80cfd3eea590e1fc0c590e067862c81be19037e8b22ccf73be44b970c8972f45912ed3d1647ece2a,
  0xd4b88b6beeb11f9eb7eb6904c6bdec4d8846a955cd20fe2fbac456783d933a4f756916d7d65916d7dd4b21245f752c8b6dab752c80cf5f5964067afba9642f0f,
  0x9eb234e74b20ab692eae7ac85f6842fbac46b94a776eeeb116d70c8b6b9d88496d73b1019eb9d884819eb9d8849173b11bfffaaf9fc8b6bd1645b5f684782c5f,
  0xdc320dcec44cd3b11391d880c4d1f5a551ea91382a7cd63d1efb832170c8c55c3217a2c85cec4398539da695ba9fa42e74b23dd4d8f46f755a590ca87465a73,
  0xaafee691a7a9647769ea5909e7ac46fd1abe7f20cfb7725431884f3d4b202fd9a54dc591dc9e7a9641e9717f9073290779e91dc75bcc83f9fd64771fcfeb2032,
  0x1dd2c83b875bd9abfdc0d2c876fec5cb9eb23cfdf0e5cf5908cac42372623b919588377a799fa4232a591dc9e67ac8d3d623c3eab53d76d23bb4f5886fb0a726,
  0x80c6215623b2b111f76f79097b2b1094dc18c4055fb9694f3480c7ac42590a853a50d9187259065a2591df22cd646a790eec4773bb10175622f0bab11dc17562,
  0xe099889e8a3db5c3dd6511387e227318f15d8f20f888460f7f71eb331e8c6227b71103d8f7531eedf0c3c07c7a87c7af28885762268cc7a6b810c45f231037d8,
  0x3cc14c7ca03181ae0181d1444f5d8bee098b311f8fd8362c601be3e7c1c4e38eca707385ce712e5ce712e5d31c772e98e28b9ce3c5b2e98e3b2a52831
]
def delBits : Array Nat := delBitBlock0 ++ delBitBlock1 ++ delBitBlock2 ++ delBitBlock3 ++ delBitBlock4 ++ delBitBlock5 ++ delBitBlock6 ++ delBitBlock7
def delSteps : Array (Array Int) := unpackLearnt (65093) delTree delBits
def gemTree : Array Nat := #[
  124136,122060,123128,120034,101628,107700,116956,126697,126174,131321,95414,121050,125681,91386,117984,121579,130291,115408,
  128756,73985,102594,110798,64731,108719,132335,76490,98472,61643,106158,129765,94467,130791,87300,93875,71879,110270,
  116445,96876,133849,134918,94862,109777,85140,114367,135944,56424,79000,136354,88235,95920,136897,51468,108166,52493,
  84128,109237,67700,138441,139535,79990,105121,140561,140969,74876,100017,142100,100507,101142,88855,143548,66672,80522,
  144665,144992,146204,146568,147102,78464,148256,44322,48220,76914,84643,149795,65122,150175,151334,54391,151693,40233,
  75409,153386,60204,56999,70445,155438,69259,46384,156285,156794,157264,34100,158331,159542,159887,161081,162107,34967,
  36157,162904,163461,164672,67130,165698,32883,165983,166484,36985,42058,167750,168065,169289,169585,55901,170828,52046,
  171627,172084,173393,51027,174932,175958,39256,176727,178010,179036,179297,46681,179815,180286,181601,28003,183140,184166,
  54120,23913,185404,41835,20844,24941,187434,188783,188984,22898,36723,191348,192374,35704,37753,194426,195452,42878,
  196991,38785,43906,199043,200069,200269,200769,202121,202301,40515,203660,203826,204326,17467,205712,205879,207251,208277,
  209303,209444,210842,26165,29216,211868,212031,15775,213920,214946,25508,14757,11686,217511,218537,24491,13740,219693,
  19374,220696,222128,20011,222249,1459,224180,225206,226232,17338,226834,18364,10685,229310,230336,231362,231453,231963,
  13254,232991,8648,234953,235979,7191,237005,238031,238092,239570,10771,239633,241109,242135,243161,243210,8156,7133,
  990,4575,246752,247778,247819,249317,250343,4614,251369,4075,252908,252932,495,254960,254981,256499,257525,2039,
  259064,260090,261116
]
def gemBitBlock0 : Array Nat := #[
  0xf54b649a412d7670b27902d2506d74d99ecbf70bb07df2582f30d7de2c9f16ed7993229db7192776bc71c997164ebb3abb7f3326cbf49c78eb3e2c9f3cb1ff3e,
  0xb235932ece36ce50670cc4c5e1d4f26e714d8db85fb81e3e704c4a317126bcf13e035e516de7838f3b65466e3e19f743b49f92e7f8dbd4d7954c59e2624a7751,
  0xfb817e84ebf723c727d79f68f3c896e32fdc353e28ccd7994f884df067325b83b26671f30edc44dc076e1e2c339989aa3ffb8e67826b36709f227cf33c23b72b,
  0x4f8af28b2764b27126e35e795326082930f1e6e76ce79f72ed7978bce79dc593cf1f08a7ca92ff13e1412c47fcff7a2c289b892c88ed7947d7fc5349fa33bf3,
  0x6332664bc8a634fbddaec5cc9ade3e56ce6bb738d870d7d8cc9d1dba5fa4d09a96f8e4e2fdf9880c9320c93926e209f249b8e4a7178f19e541167518373e33c3,
  0xc91f29ac9a78f8905a990b73bb398338876ecf326af3c07914c5ecc5db669ba09f7b5a027ca7c1aa7c20cf24dd1b72c67d1f718a7c576e029a76e721e7967d26,
  0xba937b24cd4e4ca0819fc53ed0526525e1d9cbb389b9e731116390d7e64e1e619e69373ff2f86332612dcf53e376264f26bc626461586dc679ac8abb5d4f33ab,
  0x11f4bf5e78c5b94539374649b14fa4d64e8a727e2fd2697e93bc5f84dc46cd3e31da10b99f1e3e792c9da9f09349e9349f31179e84dce2dc89370bb24dbb391d,
  0x93e9369ac9b16fc13f0f224fb864be24c3c1393c96e51da4d9e7e4d7bc67964bd7854d26126e67de833b9f70f1c9b4671bf49d1f4da4f0649d98a4fe33c5261e,
  0x693b04f8e33fc964ca9ab7e79bef453e429f1a324d4602dc4354d278769329ac9fa9c9c29ff53f6a726e7c267df0ecf51b5e92dcfb5f609f719dc9a3693e3613,
  0x1d86b649a09c983cc9f2fdd8ed249b1da4ccc527e7d27e2726d052609b9d4fe1af04dcc964ea0a4e833d767f3e93eecfa4d2626a278bdd1927535f12de9aa897,
  0xa6bcf4672a6bc29ac9d717f7649b7e93c4d26609f1ed7ebb7ffdea4b26e324945b673c5f0a7c25b8359323ee47c27649b6cf476930bf63e937334bcd4c729c9f,
  0xb3efc5bd92f3b3a2693c2693e9ac99d4e4daf3260ed27c53dda4dc964d0ed26a4d27525cb0d982e34171cfb9898e9c983593576932ed26c4e4d13733c7ce3b71,
  0xecfa4fff49e1ac9bdafa7d2638e4e9f7725f9e393ed92667dca0b8298b13fd05c8bf7a82630713098c88e31a2dda6bf97ee5c5fe8cff6bcc13e905cbb0fddbf7,
  0x26d5914f57dd9ab096d1d35d11d05b2626bd3c7bc725078bbc1c61c6758c012db58024dbca7c0c976bf0519a3ea7cb314993e93d76f2745bfc67d717e26e98a4,
  0xbf466aec13d5f5e757662d5b2fdabc9aeae8edab3316ad26bab0bf6ac8edab6bceaf8a7aba3ed5d066af0edab0f1ead8a7ab304f565d9aba29eae24dabb53d5a,
  0xb4841d6dec991f3fc7650a9163adbdf4aeda04c3ba7cf25e731179daaa6da6d9b498b68f176b0d76ab66d226d5f4d756126d5949756e8cd5c5fb569e3d5f2fda,
  0x7af7945809d64eca168d5dee778f9a4c8c8152af48ca708a7271e3867442c95d8ac9d4a774e512b43ba726419858bcead6b8827091539555abbd9329abfc7650,
  0x1fb37a698bd86d964cc98ea34ecf5ec2e5a98555d9be5ec36c982aa9c27cf5ef2a0b386dca3b2c436ce3e7c679c5a957af7c545c1029bd34c5ea79f9305553b6,
  0x77b69642a2a3f7b295ce9593518c7820f3280e3ab6f7917e1d8a8c43be4743e12dc7c8bf6bdf144dc5e09aaf64c1a96610d5821eca3f6d93ca606616f6dbfec1,
  0xb8db2b838c083df6e36cae0350e19bc679e18c81996d85a72df6f19edcaa6e53ed80752ef73e39f72c96919b6e37c77da0d8bc9dca7db00ea5def2c6705bb6d2,
  0x2647c7564eca99bce859323e3a86c3b2c6bb493f3e3ab2765a5a5b9c991f1d593b288466f329f2498e45d2c854547ee313d2384945ce29ef2c6705bb6d28ba0d,
  0xa52ddbfe291e99fd4cc2691c20bc33ece109b26c4fab47273bb688e1730601aecdb4470b9cf3750776d11c28d6f1e79aedff153cbfa8266de7fee1a9ece45d0b,
  0x55fc37984de7fee5929d472de53e3a7f19c9a7bb48e1739e6ea97bb48e146a4642e77d2c91e98fc26670ef3ff738277c722e9648eb21ab2a52dda59234cd60fe,
  0xb1364c1e4e45d93e2d4722ede33ab27650b59d9335344722ec983c8ea8bbf0986eafb688e3eacafb64d8b6ce45de7fe970131c8ba5923d3356436266d2c91a65,
  0x86a601d4bbde4931c8ba8b9898e45d9b22e62639177e39b22e62639174bc9cff0103a943d02f8a1fea5babfda69f3ad93c9ac360ff52ddbfb4b9ade5161b4a76,
  0xc9b94faaba44f76ef26e53eaae913dda73fd9940722efc793729f5574a68269c9026040e45d6ac9ffe2384178db03e3341b056338ce19f39bc6765a363adbd3b,
  0x722ee4dca7d4722ee4dca7d4765bb4e3bdb4614faab55d0898e3bdb468a6722e9cff164e45d86c38c4f3a4ed39e75bce29f19bb11c2e60cceecda73fc040e45d,
  0x1349cf23c68ba36701349e1aa2ef01349e1a844f4e45de626391779898ecb7db9f1cfaff96b54866daa4daef3a08e45df8f9d04722e91c20bc719ba826f38ed4,
  0xaa2e81306dcb2545deaf3d4f91e345d4edc3316675378c0272786a8bbc04d2e74d51778c027273c8f1a2ee6f8f964ae791e345de03502727205cb2545de51f70,
  0x6525d55721f2a7da6a9d86c066981b2a863d8513d2ddbd1809e92833b3672a9b7cbb1fb4794fb90f29a50d2de516e36ccc948bd2d1e53ee43ca522f4b409c9e1,
  0xf56e5a8ba95cedcd5e09ae6576c7ba4cafa4974d90418f76dc4a0eedef125b4c0d95431ec289e96edefaec93f466b1790f3be5d8fdbc660ba8cde078d8bc7332,
  0xb2fdc325d1a3b49b3cef1cfb80d53c73ed937330db373a0b4a60fee1536ec5c626773c9773135ab309b6362a99bc733fccc27ba5de18c959b116a512ec339609,
  0x6f1d19c096de935e192ee3e55d9332545becfbaef43b70c974e2df6c9d92c9be4986df67dc325d2cbc7b27e2659bd9e57bfbb3864bbf15a7b26633f3bdc66b68,
  0x593319de37e178ce810ad9bcbc5178cec9d3e15b37fa33864bb38f717671f2c13dbfe93a29ef33170c97529fa7b27c13eaefe0989746a9b864ba3479de61d841,
  0x70cc59aafaef149bd3a3e114faee5a6c8d58f355f5d1b8e4bd19067aed69344dd764d1b7096d86159b116c16e6cce24149d531fb657356ea573bcd261a0cdf53,
  0x8a7165e58912d575ce726c76453a94b1ee799df275c55ae58635515f2aef0a082e091973a36538ca3e176d5aa2d38e4a9ba11f81984c7bc06ac7c6fc1c202dcb,
  0x4ad9b34f866245db6e14d66d74c27514e6a86f70ec96c9fdae5bdf669e7514e6a86f26119b26d1889d2a79d93e3662a274a9e751393fb5cb7beccfcc5df2684c,
  0xef86348b78e7df0edb6dc518e791e345dbc72712c18f619e74d733a9b27cc52612d9e6f6979e198b3cdedcb75792b5c564674a7532895b1a95ae2b233a53a994,
  0xf01e73b719c325e28cb83ebf780f39d98d9fe0bc304c07d7eb1b4d89db262aabf78a308f8609afe764c14f4d474b6e83bb58e4d04f333ca9ad367426f56e6a91,
  0xabef11b64dc353f969e813066b21b499a9a2e8d1f109b99e3848bb592697eeaee977d318b6738b68dcb3150977d3e1726b4d9d09bc079cedc670c978a32e0d16,
  0xa4f8b709f6e97635cd27c5b84fb74ba9e5537aec3f6f1ccc9992c33ab5cb44698bd912ed67338bcb19ac3a55222dee9b3ca10d44d45acac58f82d6656db796b8,
  0xec00b372169eb37ac68b9ab24f1349176b32712c1ed8a6fe2c11529b59e392f18b07b629a5342e516fce2cc7b599b49e1add977954debb0fdb266a736ba613b9,
  0x6daee68a590a96d37a731305ef2ec33c73254b24604a3577b599b49e1aa2ec32d52ce633562e6e42d3676bded664e25aed8a6f2c673f4ce950a7e76196a96731,
  0xd63f63b9cc50be761b232f56d6b26c9d4d9ad5bc518e791e345dacc9c4b675b7b6b29db91e3ceb6f6a32f700521c9cc4a3fab419e653bbabcf53734d86dedc62,
  0xcf01da4435b9e0f6b35ca0c910d6ecbbc2edc0762ca3e1d837dacc9c4b6754a6833cca7c07644eea69c5e58cd66c692445bdacc9c4b6798a6d6780ed24d8d345,
  0x65de799e176fcffc5769e2ade55365b61331fab789058fbab245d93ad9cc4cb5ef2ed65fdbcb70f1f5c656e13ef3066c8de7bea6b8c426abf4b2151573d4e4da,
  0x9993629b945d2ce653e03b226f3db26f6a473673a0b05a4977c51894fceb1dc69c7ddf92955fa4943e28c4e6d24a1f1465d974928625e18cdd9749286abce2d7,
  0xed4f204da9d46e535a469e409b53a8dca6b42a24f204da9d46e535a9da9190a351fd5b2786a8bb265d88bb26f6bf0d74414f79dd2ee7cfb5a4b32323a3c1895a,
  0x958e5ed9329a9cb5f93b316bf3bceece32b1cbdbf13179be2cd93c350bceec910d5cbdb905829c62b1cbda3649c4b675b7b42a16e2c14e31588bbc6bcf1958e5,
  0x651a7945be8edb9a4dccf1c2dd2ef5419e693499a9ee9764fe331e7875385f72691b57867d9dc031350d6559ac4d6de03b48a98acbb2e85e39f48a98acbb2ef1,
  0x3e1e2ef94584ba71796a79602025df78b26a33533cb53cb01012ec927c5b7ca2c25da3b6e693733c70b74ba5923e1769504059b27f6bd4455d93ae2f33edd4dc,
  0x94293733941958e57269649b13ac72b934b3983d31fab37d64c9938093be94a57769648f88d844ace1d1353930936f3d1996d9317b225d1e592d232155619b75,
  0x822b2716f64d8a6e5177e3e592b9e478d1778a339d048ba73543d8a432d576b276ae0e3e37c77dbcca7c5197524d63b8d38fb264c21bec9b13acba926c9b13cc,
  0x93abf4a5b4cd8ce75e6b271f913937917ee43ca336c751875b85b884dccf1b1d2ec6bc44dccf1b1d2ef0584bc1da974e2e0bc78cfdbc229c9b4636a33d4538b3,
  0x9054798321ef0ea7f26bb2b9ab73fb788d9fe932eccc91dcc7bc63b03623b98f4e9c9ba30627be42a7784539368cba613a74d8b4e63593a3e0a9da73ccf3af35,
  0x828167b3a9db809b3f9ad6eae9d93703c79e61fce9d93703c741cc3f9dea4df26ba764dc0f1e7ba3d93c4dc0f1e7ba3d7b96a79b7e35dee4c5b332635f2d4ed,
  0xbc9f7ad9b9bd591b76d33cab4482da9db9e26e5a79d1ef726cde06776d351d1303def6b27e8cd4edc04d9e09107bb10dcf1372d3cf677964bca7cc660b7621b2,
  0x48f3a63d8670d4f976b711e74c7a7ee74115933a63de5a9e6df8d77a47cc26e64d736f8c5a7ee31daf88f3a63da57ab236eda6cc482db4af5646ddb4d474482d,
  0x7b7dc7b593f250209dc7d26dfb3d9d84cac9b7ecf676132bc62dc6279ecec2656b3c076cf67531ee176e514f737ab29e7898167b3a7ee74111e74c7a7ee31686,
  0x7226f3db0c0ee13c5de313e392f5e078f8c05b529c9ebb07274f9b5de76c11a8cdeced931677fd764447b4ef0c67c78cfdafe065edbcf564337bbcf08a7d04c6,
  0xf1a6abd11a8cdeced4b09676ea65947c3b24dddaea782465cef3d4e1b71bf7187ecf64d5e68ed77d3bd255afbeade7a9c36e37ee3333f6f1ccf3d4c71c67854c,
  0x6467ead23ba9c793f52e1685bc40cf329a673ed61689c2edcf53e13e7f6cb4dfdad5f9349b4111ee86e66674ca69b132bde76c3f6c872c7474b154cddc337969,
  0xd5013bc576acf1627bc7b5932a61b369dddada4c14e19da3f78a59989db8f76b6930538677e134998cef0c964ccfb75da69e74e6a86f70ec96f0c964ccfb75da,
  0x1bc209fd9f197bc496a3e54973a2f40b8ce8270cef29f69ae9b1f7e7f67c65eecf329836930535eaf892dc896ce8bdff5d9b5da75abf26e0d404eb57e4d27e4a,
  0x2a61b067bef14bcb4d16f6fc5e7e39364c1dbd804ee7b4518b95d9f29f8bb27c6dc651e620babbd17d14f69d238d6b24fc95ef93b69deaf1ccef9763f6e9ae9b,
  0x64c1aec960a1b0b947c75c8b5b61b22e0e305b78dfa88e11dcaec178fef29af679d84473672bb32c5533c6df84d8fb3505b7a93179f6f9d93076f6091bc7b593,
  0xdb4ecf1b09a76a466d8ed9ad4cc991f1d3cb4bed21bdb786a7f327b377097617197ecb0131ef149e26ddff1fb56bc896b98e9dfb4db3f7be13647d93e362c143,
  0xdf19e64bd6650b253115ecb1657ea9c6d06c85b8da57496eeaf3d4d2753789e393ad9ced8bbb8da99e5a9e58b225de17606c7fdaccf3098e9855c2d1e7994522,
  0x4a2d38a8f65b0570dab523ba7c494c45d8796c11dc6d23664789298981e5b04771b7838d2988bbe516929c6d93ca6cccd94b4a2d38a8f65b0570dacccd95b8b4,
  0xbc62dc1c76d46b9b235a06db3a9525766c3656a6f4d8c7ced981afd669de11f0938bf6a535f556adab1d37cbb5b93bc1c7cf53f8a2719c54df2ed6e4edd3ad4b,
  0x48cc15c9dcedc3535cd91ad036d89092576d96a47265911183f5e516f64ea53591974d8f6533ecb93b364a6b232e9b18fc926b93b364a6b2316dab18fc926b93,
  0xf2d6b537a68bf3b66072acd3b6de9c2ecb9b2916ec18fd7976b7276dbd385d973652160c7ea46166ae4ef2ed56bc526ea466d6a553a94edbd385d973656e28fd,
  0x9b2b8ce2a3c98ab82b86de6265919ca2c99a5eadc9d127d794eec56de814e9ae6ca45e9c20c7e4935c9d06788d8e9d1ae6cadc5aeba62cd5c9dfa4c89854e853,
  0x3c16a3ea85a17b556c71b64f8b6f9e268a9c6d93bc538ab51235729e0b51f5713557b638da7156b0da8fd6eaf3d4dcd37838d2988af658b2bdd38db0a4f0d599,
  0x5342d9db864a028dbd5024f05a8faa1685ed4a71b79aedb0f2db3a958f6ea7cd76ddff1fb5697f9ecb167d86d5919d78989334bd52bbcaecd331ad532bba6725,
  0xa466d6a02a779ea7be2bb2d16e93bced8f65bd3631f3b6606bf59a779db2b537a6c63e76cc0d7eb34e81508caebc5760e559a7561f22f902237fbab70dbdf8aa,
  0xd4bd52babd32d130223cc84faa5740ad83e5f35da84accef31629b1d3bdf8acb317c73e06db3a94054ef11b524eed78c664098f57c73eea85b303a6e93bcb53e,
  0xa6e1b7666db20da926827bc2ec85914799c6e2636f0bb31b02d47d50b42f6a6c71b7878bbe33c8db9db964bec36f2d4f2c0404bb9dbaf28b7b0da04faf131660,
  0x2b86d5918b198ac7711805fcae1b537fc99cc1982de5dab993f8c9fb66cdc5a6c8c021ec36ac8c58cc563b83ac382897eee1b79c76e1d936549318eef8a70512,
  0x8042ae1b69673c04dc8931c12364f25be1aef3d4d0b7e7164d65defd9ad2836f4df3c4d8f409ac662b1ddc33ef2b86da6d533f16e32c1b409ac662b1dc46017f,
  0xf0800b86de0352ca2aecae81358cc563b88c23befbb86dcbc27dc0bf25fc03c0ede6d026b198ac777c5380beee1b56462c662b1ddf14e02fbb86d42db8b4d91,
  0xbdf409ac6e2620b78f35c36f12fd4e2e3daafeeb638dbc4bf5389196aad35b1c6d937b5464af55ea5368f8126464098f79ea785b9c59354a681358cc563b81b0,
  0x2a0a6c4f36d82dcc936ec72e619734bec28f2ec5c953aea748da9e38cf30660b65366658b7d9401739ec2e7c4457e91b74d9919cff42dfb085870172146eba9f,
  0x2c2dec266bb149c3354b4e43688e151e0a17cdc8a1fd02f639865cd2fb0a3cbb17254e48d4ff721ae7809b809b0435cb9865cd2fb0a3cbb17215675d4ff636f,
  0x8c5bdcc5a7396a7ebb29b332c544d7b185d405cc7b0db29b332c544d7b1723a80b98f61b7e0c93519b08e991c2aceeb3aa529a545f6107db2d3bae4aafd8d553,
  0xa392d26a336bf4d98b4e2bafb2dd24b3172731c57fbe36a79b6e44b73d4dcfb048d6658a89af62938752b9951b6e9219ca470ab0b2b3aa5292b48be965fe233b,
  0x6610e2b9534d6021b142f6d7ee399f624bd190263defd29b332c5beb97b14d6cc00b98f4fbe36e729b06f52b16faeea99259801731d23d236c9d767013226267,
  0x306d55b5339609a3256124aeb565ec799962df5cbd8a6b66005cc7a748dbd53e0354f329aacbd8f2537f5d0a4bedd60bef22fdcbc5e714f31bcd767f262c4362,
  0x9af62e47501732a36bfc4674e16fd842c380a6b39b921fa7fe9fec33ac9ced90b6c52c380a6b39b921fa719fd7f88ce9c2dfb085870172e6e487e9f84ffb2645,
  0xe6bf61b48caf15db79904eb724ef61b6ffb35dc8275b939aeb0636f6ec1b35cd56b6cbd8f332c544d7b185d405cca8dbf4991338ede04b067048d97b1e6658a8,
  0x86756658a89af630ba80a8a36ca6cccb15135ec5227501732c1b73908578aec89c82984005a57a7fb1b7338af3cb19dc8275a6d39aa8636b32c544d7b1489d4a,
  0x49c7c4ab8ae36d38ae45ba8252bc4b62b8dac563b9fd41ba87939895031b58ac773fa83750f27312a4b8db70584eb05f58e6d71a6aa5c6d639b5b424d54b8db2,
  0xcc7ac5a715c8b7506ea1e4e62570dac5a715d765ba9f21e4d3811bff636d4306f8ae45ba9f294a69c4b62b87f58b4e2baecb753e43c9a7022bffb1b69c5722dd,
  0x96946b169c572d5341ab05cc5525c6defdc725a5a2ec714dae31598e36f7ee392d2d17638a6d6d0856638dab545a518d90c4dd0870130842974b38e7d59edc6f,
  0x55031b7953585083e10968bb1c5ce2c2aa85ede54d61420f8425a2ec71232042aa85ede54d614286612d176389192b085550bdbcd764ca3f9a6c416983db994e
]
def gemBitBlock1 : Array Nat := #[
  0xe9fd71b40ae3be66c1a5345849a092cc0ae189c6d349fa0b6caaeed26e4bbcca71a8c489dd4d9b3169c4c796ea4b314da731c6ffae36b169c5722a5341ab05cc,
  0x6fa5a8fecfaa7e62ec7152fc6e4ea6f28ae9ef6d2d4a31b2194bba10f6e65310852ecbd8f332c5bae5ec530800b4e3d3fae36cbd8f332c5bae5ec52766005a71,
  0xd431951b795054b51cd2e61fcad69ede78774faa6417272730d8a7bef329f12fc28dcd1a27c926f63f07cb1b49db26767c7cfb512767db9b6bcb3ee2464081c7,
  0xd42cccf15d765ba49662e4e638dff5c6dcc1e68599962dd96e92598a6d398f4ff636a60a6b0ea02e620636f104f9e269830ab05cc40c6dd4cf5d384d8d7b1489,
  0x2ea79cd93261958a6d5b054e36353052abd405cc40c6d42ccc8c268bb14aaf50f651570da85999184d17629ac3a87b28ab86d9b560fbf5de24d78a6d58081dde,
  0xa715c8b74921d6e4e6254ae3694c3954d4e2b91614b309184e046fef8dae69c5369243e6ecd34ae1fd4f3cf3298672fb26d2487cdd96a55bff7494fd23ae1381,
  0x6d95cfe6663caf7209d405cc3551b785da4fb6428f3b10fef2a0a6c4f2c66ea67ae9c26c6bd8c2ea18ca8dba6e126de553538ae45ba490ea1e4e6254d8dbcaa6,
  0x7834c62dd7482938e157538e91fbfbfbcaec58c376798bb1edee5aa4e0203f7ba77812c58286814d94f6f36380939d2766cc7363809398e9d027d7898b391c4c,
  0x40543625d3bed753e71612b6eecf0698c5bae905271c2aea71e9fcbefef38b34ee855d7ef512c2866e3e571766c639b1c049aaadbcb19a714d8e024d54ba7776,
  0xae5ec52766005a7aa7f2e9d97b1e6658b75cbd8a4ecc00b4f54fe5f7f766b716ca557ebcccc8ebb2812ecbd8f332c5bae9052766005a71e9fcbefea274e29b52,
  0xd8d19024d556d3b96339fb232049aa90a7786a61b1d38aebb28a4d3882d38e37fca4d0fb65a775c9922fb2f63cccb16eb97b14c2002d3d53f974ecbd8f332c5b,
  0x2f63ccc8c2775cbd8a6100169ea9f869ddd9e664613bae5ec5271c02d3d53f90a778d19bb3cc5a715d765149a4840a91e38dff214ef024c8c8152af44b0a19b8,
  0xac21e3e7fa2de25f85422ca27c57673ec59489d5843c7cf9db58756610107bcde3ac901269c537767834c62dd7482938e0169e923f7f7f749492f12320426d3b,
  0x8b75cbd8a4e3805a7a48ff5f7f787669b95b39c53013a16b24fb63df27009d85ce2986254578f2c2eab1dc8b7978bc04c898813a2a1167809be688bd88f2a44e,
  0x99db4ef01342f6dd0dac3763f7b08c72487660528f1def5bfbcc267bdb348ebb2b1eb57e44aceea3fbc6fdbb3c1a274f6ec79529a49aa3c715ffebe9ddd9e665,
  0x6b09433aa531ec1f1db855afabd275b597b2958d8ac724876600548f1e82befed6780f2c68c8126a94ddd9e0f7962dd72f6293b302947d27ff5f7f7978bc04c8,
  0x7d2446d3bf2479a470781dd8f650ceaccb16eb97b14c2002d3d53fae9d9433ab32c5bae5ec52766005a7aa7f5d3b286756658b75cbd8a4ecc00b4f54febefe89,
  0x48f1e8369d848b2385244e1a7f656d71fbe7e58e490ecc00a91e29c6d3bb1729f7b22a26c6f4d92ced93bd8cbde141220ce013bec97b3d9bf9f96390b33002a4,
  0x15fc731d65a69b4ef1208b672cc5b286756658ac6bd8a44ea02e6553b2b6bbd9bf9f985b9243b3002a47d506d3ae26366a9cce93656d77b37f3f2c7248766005,
  0x74366d58092157a04fadff05ce490e0263d026b4dff05ce492e363de7a3389354eca18b199962bf8e63554d369d9433ab32c549649209d405ccaa7650c58cccb,
  0xf3ff390ad5c9afab3882d36910beba04fadff05ce4c2cc7bb17309a4b54f32ba04fadff05ce492e363d027d6ff82e72160131eec49d98dfe9054c24aef025bdb,
  0xb664834f2a6e4edc6c5a715ded47419a79537276e362d38aebeaa3a66a9a7a1bfd6b4e8c489d38a6d490150d85ad3b962b981b1b1dd7d5474e27934f437fafae,
  0x5b5d3a7142de692cc5d70c3744e91859b665b2832a79b9fa179db2eba5263d9ceed29b39432e9d38a1160949662ebbaec6d3a04faf13167261663d9b3169c577,
  0xb3028a8ee94dfde653ce425b754ad38932152f80afb4a476363cb7f7994f39096caa315a7111a61525980f5c3b1ba2773908144ddb760b208d38437274a6ce42,
  0x1360b42f3d4e40fb33877994f39094cc4dd98bed9c9242dd28ee9fef7f7994f39094cc4dd98bed9c9242dd28ed23fef7f79c5930b05b9484b6dd9620ccdc8293,
  0xdc3be30da748c0be7db838e3546764c1ab3289c959aaaa369d966a5ddb76ce49046d4b13b2cd4bbb6ed9c9208a9acb13bb17109a411b5452adb99cca6f70bb71,
  0x958becf264ad9e5b87741bdfd2b9f329b177992b66e512a8defebdb2346409f08f80dec1dbcdbc2ecff659029b4d215cd7d4a09b4aafdcb21019cc8593256cf2,
  0xe0af66951dc3e8508defeb4ee854327d23cd2385241de8fe813ebc4c59c9c3c5dce559f24bbb67249d5451dd289d9567c92eed9c92755147741b4ef09f659084,
  0xb3479a76a715c479a5980f5c3e857ff7bfbcbc5e0266d769d6313b538ae23cd238526e1e9d8defe9fa470a489c34fef329b14fd238524221e70f2dfde346538a,
  0x495fd4e2b82bc25259e5b87d0dffb4eb1957b80f34e2b82bd9a59e5b87d0dffbdfd63d94c4ed4e2b88f34b301eb87d0affef7f64ca986cda74a6e236f9d4dac7,
  0x77221f49ff87bfa59efc0d9e6658b75662990e3851fa4ffc3dfde7fef67b1e6658b75662990ecf74a3e923f87bfac63d99253f3142e724909147d53fda758c2a,
  0x990ecf74a3ea9f87bfbc22991e691c292272bbfb0ceacceed9c921c2b52acaefeb18f7b3d8f332c5bab314c8767ba51f54fc3dfd6339899e6658b75662990ecf,
  0x2a612577ab33bb672487e5954ef566776ce490454d6553bd599ddb3924382a6b2a9d6d69c5363809340d3bd599ddb39243856a5595dfd6326d78de6658b75662,
  0x56a9bad9fe62fa699210b84923b48ffbdfdcc067058590b264a54fd89246e1bdfde3997f31f0a05990b2643834ee9069b4ef566776ce492e32a9dd893b31bfc3,
  0xca673b0e18c894f9a6e95ce9d3caf5b05cf857fb76ce490e0a9fb6d3b4720339b615fe42c9904ea37bbbdb69dcaf51a6ecf33fcc5f4d324201eb87691ff7bfb9,
  0xa537b33848b20bd227137bfb5927e4af7c9db4ef566776ce493bf275b54f371a27a74f2bc0cbf999ddb39241153596274e9e578197f333bb672487054d6589d4,
  0x8df98f69bb2d1cefc9a4da088f7437ae988ee63d45e716798ac7705a3a482ad02e8b4d37bfbd74c0404bb59c1c7a63f482ad328925bdfdac45939266aed3b588,
  0xe54d03dfdc9b349b462291d0490ea07e1a737a48bea790f9ee262ce490e0a9ac4da77716b24fc94fdbf847cf3158ee0b4749069ee8b4d37bfb2692d44e555ddb,
  0x4d03dfdfe67ab1854ed1dd0cb8f3f6b88fa44900e80fc308969a07bfbcf53a5e71b2291d04900e80fc34e6f483dfd9344d82737432e3cc72dc47d224807407e1,
  0x24382afcd12c40f7f4a6d31fa4e52270d3fbcbb593f253f6db0dc1c6c7705784a482af4844b4d03dfde60c137179c584adb47743046ab1dc15ecd21587e1844b,
  0xb7c1858286b57978a173924382a6b103dfdc9b9535d890bfc7b479d60275d7eb57978a173924387c6896207bfad5e5e285ce490e0aaf225881efeb57978a1739,
  0x641b49b92e965aa1f3dc4c59c921c1535954ea32c563bbda8e920d3b969a069de1a9b158eef6a3a4834f2a68bebbc35362b1dded4741ab3d953525f5d4ec8c54,
  0xcecc2ecd19cd55a6e4ec6b770ec0731a32d55a69b4ebccce5b392411b52a9d7999cb6724822a6b2a9de76ce76f838f366d9acd66f7f7b417096da5b37999d05b,
  0xe17690b372479df4aac40d97e9e61baee8e44ba46040b7071c6a8ce85e7a9c8256455f575e6672d9c925c6553bc46c9e78c4cecc2ecd19f969b93bc46c9e78c4,
  0x8d321c3a80374a727492fcb9f0b5fb363ce490e0a9fb6d3a59e79f485735f002826d2abf42f3b631c8256b6eaed65c173e179cf2990e1d40a0965a6e97becac,
  0x9c9277e4eeed96ce490fcb2c4eeed96ce490454d6589d4f347c2a6ce490e0a9acb13b71e9b2d973e16150e2ad52990e1d401bb911c9d4ca3216db2e7c2a29c51,
  0x92b069dcb2b43795350b2560ab4b965686cd9e62d38b668e419a772d37276b358fee3410c5821bc732c5a716cd1c920d3ca9a2d69df6dd0d9b4d890abdebc4c5,
  0xc41644a7953727766105d9a3c7cb4dc9d9b3dc4c41645569e54dc9d9b3dc4c41645569dcb4dc9db62334dc6fcc7bcd76a949ffe4c837502972e803aa1bca9a85,
  0xcf925ddb39245554fdb69dcab54c24ac5f67932560d3bbdb7bfa59cbc5e704ca91ed3a8bcca6c5de64ac3e345edbdfd5aa6033990b264ac1a7749d769d9b3dc4,
  0x5cf832497e641953f6da772ad4b299c079f4f30dd40a06afdac4e638194f224832ad2175da76b13cc260b292fb61ef4f69d0267c2bfdbb67248aaa9b4d3b9619,
  0x4ea79cb98190b05478fbad369d023cb1151c151e3e69a74099f0bc079ce491555369a77339c6dc3b353536133bec4cdb08f433a691cfcc92ce8f56da7aa753ce,
  0xac671dbece73cb169c405eea4807494892562a95c3fb59685c4c572287f7d99d65aba998de84f348754a539a6e90fdebc4c59c8e269d0267c2f01e73924c7cd3,
  0xf4844b4d56c3fb8229ab3367596782fa15337ed36637fa43e7326b30feb189189cf28ecb10dbbe79f487054d69aad8dbc68c7999ddb3924382a6b7a5b1b7f99e,
  0x69dcb4d56c3fbec298a6e7161d6e1751fde2133d0cfb5cfea716cd1d241568112d355b0fef109b8c4e6cc736a4875df185f26ab636c33ed73fa9c5705a3a482a,
  0x1f2556f56c3fb99257999ddb3924382af2ab7ab61fda56658bed9c921c15795589b0feec5cc2669a650c9f43ed4cc68c8126b31b53380a6898b74e9c5b347490,
  0x69e9d87f7ab33bb6724822a6b63d4b33bb67248706d440c6d5af014e439778ee1b7ab33bb672487054d621dbd599ddb3924382a6b11efb9a6409e66776ce490e,
  0x42c27546d3fb95fedf84c47f11815c7e9674e913a68f7d632bf84c47f11813fd2ce9f3be1547be87cfe63d9a3a4834ee5a6a5b1b4b37c462318109490ad494a5,
  0x7bee54fb02f84cb22226231cda92ce9d2274a7ec3fbc7b5e2bb6928a483a107f696cc0b9bd997f84cb2222699f77c5a4b3a748add29fb0fe94dcd264a441da7f,
  0x3debc4c59c9209f255623df780d419e516ce490455e55626c3fa53698fd2729077a3fbc06a0cf28b6724822afcd12c4d87f58cdf84c47f11813fd2ce9f3be154,
  0xf2a6a4187f5ab73190cf33c7821a1f721e429606d5340c6debc4c59c9208a9ac43b7af1316724822a6b11efbc7328cb158e6d490ebbe35cb4d56c3fb2792c245,
  0x8a9ad8f66d4a997f71310590e0d3ca9a061fd8474c8dc8a5b8b331c3aa529cd3548befb131ecd5fcb45a3f73dec252476e9953c556d9b52a65fdc4c41643834,
  0xcf85a56670b6e438750f253d6a5b1b611d37b6fe0b9f0b4a1ef3ec59dc870ea074a53edb1b617329ee35e16100f79f67f7dc870ea00ddd22d3c73debc4c59c92,
  0xf85024c9676293856144a7db636a65190b6c27cf8545ac99108d321c2b0ff74a93b4099f0b4acce16dc870ea1e4a7ad3636e92fb39ea7216617487f4e9e57f05,
  0xa794ce59399f9cd2f16cd1c920d3b969a9527ef5e262ce4918cdebc4c59c921fb35debc4c59c9208a9e6ba04cf85a5f686db149c2b3c94f5a6c6de3167ab3e5c,
  0x87f51696e3990b2560aa3772c4dcbfd4f299cb7de67e72fed9a39241a772d352a4fd7f0958b4e2d9a39241a772d34d8da551912b169c5b34724834ee5a69b0fe,
  0xe54d3248750f2734d030fee4dc4c4164ac1a772d34d8db275048833b31a533563cc92a313812ebf84bc4c4164ac1a772d34d8dab523fbe3410592b069dcb4d2b,
  0x753b9534c9219aa569a061fde3169373e8418891b36798b4e2bb354a6490ea1e4a569a0636d2ed6273b11fb8aecd5299243a87939a68187f51562720cdf1fb8a,
  0x4fcfbd8246c99530d833de39f167397e4cd94a7ebbe49b1f99908a1497c057ddded9ffb367b89882c95834ee5a6e1b5abc73ebb354a6490cd52b4d030feb54b3,
  0x90f94dcb4d37bfbd7898b393878bbd7898b3923ce6bbd7898b391a6a9e6bb97054b73d36a0bbcd56587014f573b9230dfe29f66cf7131059155a772d370da9e6,
  0x24827c9558998fdddb76ce490454d626d3b4e2a5f612923aeb969a71d3b74e9c5b2f09419a772d34defedd3a716cbc25241a772d34defe9d98c431538ae0af66,
  0xddb39241153588f7d93a82ddb3924387c95589b97fbc096f6091bcfb5e5373b652cd32ab38793fd29b3314fd2729b87899ffbbb6ed9c9208a9ac4cc7eeedbb67,
  0x4aadea0b97fbca2d9c9208a9ac4cc7e91e6066490454d626f7f53c87c46231810949069dcb4d37bfb588a536988f34841d227137bfbbb6ed9c9208a9ac43b776,
  0x467e5a69b4ef28b6724822a6b10ed8d6ee1d94b7cc858d5589b4ec875e3cce1dacfc07963a5f6cd23b74ca9a6e97bca2d9c9208a9ac47bef30672a6b9c921c3e,
  0x1c1535881efed672b67126b4364dbf672487054d62074bd936fd9c921c1535881d0fd9c79e506d47eca538a6d4906d53458fdfde516ce490fcb10edd93b30bb3,
  0xcc736a4836a9a061fd85c8f1f014e4396daa695b64dbf672487054d62069d936fd9c921c1535881efef3d18c777b51d241b54d17d764fcf8b050de24b6ed9c92,
  0x3834ee5a68187f61b427b6a925b60b21c1a772de9072ff48f339a1d0ca653ceec1643834f2a68187f48c08ad1b9f92a55cbfded6c1643834f2bd20e5fefa79a6,
  0xc59eacf973e14093259d8a4e159e4a7d801b7945b39241153f6da7513a5ddb76ce49046d4b13bca2d9c921f96c7bca2d9c9208a9ad8f7890508af1c97854c164,
  0x854d9c922aaa6d34e859155a772d372744f5b286f28b672487ecd76e3d365b2e7c2c2a1c55aa5321c3a8deee45984ef28b672487ef63b7945b39241153f63b78,
  0x86d459b709f70718592b069dcb4dc36a2cda195ac6b766a94c921d43d72d340c3fa164ac1a772d34d8dbec12342c95834ee5a69b0feeec164ac1a772d34d87f7,
  0xda89bdfd8666a53715d97b4b3c596312c82a6b100dfd4ecc6ff7c5ccaef28b672479cd77945b3923cb4d3bca2d9c8d354f35d79ccdb84fb838c2c8aad3b969b,
  0xdc8798da77854d72614c0652c4659f4a603366b6ec9f9d2980c639484f9cc89ee7234db51369da5a4d2088cb8d3b9c8581b51369d93d26930936c983c85ce42c,
  0x31fa4e52272b5fef125b05ecf5538aebae5a5349679a9ea9f8743f7391a7366d3b98c77431aab142ce14a4939ee43cc6d3a8833804ee67349a962859c2949273,
  0x3df7391b5cc93df7392439ce61331fb9c8e269dce469c794ee724824794e9d3298ffb6f221dce469b6a577f7390b036a577f4e994c94f344deadbc06a1514a6d,
  0x3c5d63e7164d54b8db9c85e64dce4bfef9d3a6531ff0890c773910d5efbc4c5c42692e3add21fdce4c2c23df4e994c94f354d236e7249b39847bee7248739cc2,
  0x446923ac8a952fb34ef3e70defebf88ce9f5695be69f77d89bfafe2312ea74ea1e4fbbfe2dfd027d640ce819bcef9f19de73cf38ec4646251ecdd1546d3b9c9c,
  0x9de505edb4ee62542dbdfdcc4b78c4defe94c066cd6eb2cf05f73f9a5e3137bfa53019b3bcd2d2fdafc4602bc55ce50fb32b3c9fcee0e14fb26d19276a7b27d0,
  0xfbc3b18f673ad213e4aac4defec9a4172b67b6d3bc3b33f6d9ceb484f92ab137bfbc3b18e1679d691d9e655626f7f4a6d35367e5c95589bdfdeafb6d3a8833b6,
  0xbb629bc896ce13f92a3c4defef225b3adc5f255626f7f7912d9d6909f255626f7f4a6e176f9ddc55626f7f77c579cf3add59670c1fb980c0279d6f8f32ab137b,
  0xd92ab55defee7c642e26f7f522608e9ac4da77384fe617137bfac7b156466f9a17063de7a9e16e7167a94d0a0cd64b35f4f37a17f8f7838c09ec485fe3d93e36,
  0x3e226defeb1ec547e0651761804f6467a4aba2769d93bc5ec53d4cdc7b4e8e1d4d1773e32165defee7c6151cbbdfdceb4a132ab55defee7f3b25472ef7f73ad2,
  0xecf3942dd6613f1e1fdccb33066aca16eb37befc787f79cc43799f2256611efac6f5626ae459603356aa172c4d87f732356af573acde59d70fec6a31227771b7,
  0x55623df7992da64a2d366f9acbedb0fe965e4a2d3356b3650fe8d99d69095a8aac47be9f9eb84a90a8b4d509d539a7b61fdc10d99fc89f255623df43118d28a8,
  0x3bec3fb1adcf7c79a429df61fdc2c7e5fbed8da366709fc95588f7d0a366709fc95588f7d1b33f913e4aac47bea20cecc68d99d6909f255623df428d99fc89f2,
  0x6054a04e4cdf257db61fd23a2c854570d60f609086d8d4e84fe4acaed87f73cec23df73d25588f7d4cad5626c6dce13f92ab11efbc9265fbed8db1adcb5cd220,
  0xe0e3b9b5239657f6b1cd82ad7cb752e9d9b131eac0ab57aab6f553753efd9afbf5a0d3b9f1131db9c27361da367c44db4ee7c44cf7dcf8cac7bef0a08b06d0a4,
  0x51061686c9e532c634a2cae650b3cdfad4befec300ca3d96020bdd4a9a9e4e38b4a694c0624e91aa750439aff6d816cf351f92ab2bbfbc3b3e42a778d35cb9b3
]
def gemBitBlock2 : Array Nat := #[
  0xaff785c52a92a0650b3f2256773dbf27dd96301528ac747b9ff82f7beb4ef0b8ac6540ca3d96020bdeff5d05b3cd47e4aacaefe9631a7aa027e44f93a8b73f7f,
  0x234f2aad6dce1354d6577f5b5639b1f962069d1b3384d53595dfd1b3384fe4aacaefe9631a7aa33f913e4ea2e876feec9548b8d8d239fcf79e7f18149b9741ba,
  0xd154a87f7384d5369efee709fc9569efe9642a2ac8ccd363956de73cb1ec55919be53cef60f7f4b2f2515646669ecd6dcfe44f9a5669efee6476d96b34596028,
  0x59747f6b70c86f5291a42d1f5149ba5953fef3c4eec1560bed6726cc1f72a0b84f8b12379e65fdc68218b0436bf670989554a87f79cbf2a8818da8a3667f227c,
  0xdcf3b31ea66e3ada996a895b7384c1b7dce1354fd3fb991db65acd16580ccd3caab5b58f62ac8ccd3e8a187f7384c4b59747f73f9104b59747f64e8333f9104b,
  0x9626f7f7ae99aab1369de478fd81613103c9cca9ade96f7f788db884d58244e99afb3a0691f437fef7f78126e716a55ec99d4e4d466a76d969dd72557ee7cf13,
  0xb137bfa362644b59626f7f767986a58990a99cd52b7a5bdfde1e2dcd5ba95cef2f1429dda7251c2cf8be622659cf344b4ec6d3ac6d2acdd77b6d3a8a362644b5,
  0xf755a2731fae6e3a5a3104a1a5623df7984c15c950fa9e78469e501e6b0fec9e26730cd9a79e3834ee5d13b97fbc8962cb9866cd3d9834f280f3587f53225ac,
  0xb4149da9ea28d9462096b2de93df69532f56f3272f22bbaa267f3980f7acbe32761fd932e2815652997b4d4cd165a8f6b5e2bf707f6974dbcb4d32b6773df398,
  0x8931152779dc7660527df74ec5790fd45973cd5366787f50b097319c29227a3fa8a362644b596f49efbec77398a17ce85e3da91d355e4fb666655f92bedb0fe8,
  0xfec6b766becd2209f61fd4512d2a644b59623df46c4c896b2de93df68f643b931152779dd080a4fac3d3b15c3fa1e09152779dd080a4fac3ce15e5feb568f67,
  0x46ca33834fd6588f7d632a0651ecb0105ef7fae9c1aaf3d4e4d867878af667c8954acbdfa6c3fa1f0160b79cd2cf34fac3d29fb0fec32dae5a6d2729f587a69b,
  0x13225acb11efb366ecd5acb4d715c6d451b13225acb11efa1472a44af08aad3b96f56c3fa98912d1d60d3dd1626c6d451b28c412d6588f7de03cf01a8d959751,
  0x1dbcea9597e5f31f7f41b5c8beccc91dbceb36eefbfbc68ce64d683244069d93c18475c7b5acf9a56147f44b74f32a6135f3a9912d6588f7d4ca6e937de9fd1b,
  0xcbf2dd4bd7fbc5791576d0b09d1569d7fa88e9fb0515117075fe8d89912aabdd77f529e316f9de754acbf2f98fbfbc62dcf53b999782ef3981181393529e3169,
  0xe0ebfda586517adcf0970b661512fbdff0e87ea2f84c8c4ad34ce5a9ed2c181936cd23aac39dfda56a889555ecf7f6ea74f399012aabd9d7fbca7d0a92cf754a,
  0xb05454fede0baaa6a831b4e9c9b92fb3c9c7c751fca6944917d1b13225552bbfa3656012aa95dfd1b28ce025552bbfa771bb395b18d55354b5a778a4c0515101,
  0xe1fdb8d289cda9cc4dbdd56d3b50c448d29a8a6a7ac4a6e11953fed6789e496c39cd52ad27858f0fef3ed4e63557a878d36db91f062246f05344c4cf79db24f8,
  0x9e1349da9e896968ce02555729fb0a9615538a49c3addc3ce82a5c3fbc68c4cd2c23b8a4d243addc3ce82a5c3fba6cb9e7753fb96908ee00a6921d6e4e74142b,
  0x1619fc85889acbeaa387f79ea7766b0828941619c8e0b113597d5470fe854547e18aede79902bb1f051282c33e212aa9590fd12d2a644aab47f66d363d52e36c,
  0x4dd958f6ada96eb719c2257de1d4c895568fe8d89912aad1fdf0b62569a66ecd5acbfd685ed84c8c4ad3f995ab2e37aab68d89912aabcabf79ea7734d3082894,
  0x68c8eae68b4d37b1de741519c04b2a2c4da764cbb6d168f64b18e97ae63b3094dcb1369de1a9d2d467012ca8b1369de03cfb6696d375cb1369dc9b80f3ed9a5b,
  0x462569f38edad58671c95328f2c474bd7356cc24ea2eb3fbd8eb5799e34ca37f248e97ae6ad9849d45d67f7b1d1b28c412d6589b4ed19c04b2a2c4da7788da8c,
  0xa8491d75cba0ae3c86b19503297db348ebae5bd5c790de03cfb6696d376512b8dac7360d150e3da87b2e8d89912d6589b4ec98e3e0e3e7fe550eb61ea7a63a98,
  0x59e15371a0b8767cc21a98f6fd84a4b69bb2bd52e368d89912aa954e8d946209554aa746c4c8955443b64f499a6474a2514c20c6ba48fc70c779e7d0c03297da,
  0xa6131f4e3a31731ee3e9c675c2e63de3da91d659cb544cdf257d9efbc7b523acb396adc70c1fa9912aab1e9d985d93a6b10ed0731f1ed5626d3a362644aaac7b,
  0xdfd4644a165f23d9cfb6d3a9d98f532dab1ef1ed48eb2ce5aa266f92bec8bea65b510ed4cb6a26d3bc2e2855adcd522decc798bb2b1eb1e674c09a67e3ba8c74,
  0x2b0096b7b6f7f46cac0d3f5bdb7bfa985df88c4ad363a61646746c0a5804b5bdb7bfbcbb55aaed3a8a36560eb77adedbdfde626936ecf6da75e4960eb7253edb,
  0xf7d85f21a7eb7b3df42c27457db3ff4e9a76f685f23db7b3b90fd58af1ad614274b2757be9d9f17b717b3df532a9fb6f7f53225adedbdfd1b13225adedbdfd1b,
  0x3a9954fd9efa9912d6f67bea65a7eb7b3df7304b4672f532c3fa34c9954fd849f617134fd6f67bea65a7eb7b663f6b034fd6f67be85f91a3cc87ee65069fadec,
  0xbc2ec76f1460952e1de74109785d8ed85c46d4cc4b74d62953ee4de2bceecfea090da69a99b8ced4caa7ec76a6553f6da76559baef6da779533164f9bae5aaed,
  0x9fd12d1b57790fe8968dabf1f50fee98e9fa7f4e9b4f7f68cfcd3dfd2346557384a9c33ed19fafbaefee98e9b4f7f74c74ef957ee99fe3bd3fb360d3519fbd3f,
  0x26764d09b37b28975fd99462757a7648c4bb9688d317b225de74111e74c7a15db4226d124da3d35d1c3b68da9e885fb5678bbc46db46c66f3b60ed1a761d3a7e,
  0x92573ec91aac6547ef2c65fd4cebaabd4a7749c8d96cd8f6f49b0db8dfb8ccd8e9772db262f644bbec02764f8dbd804e813e1a9db498299f82763593519c04cf,
  0x933b3497e4e19e81663c2712ae612ef78e3d254419c33da5ba964da0be4e19ead72d11ddbb7c75bc07644eee36f4c4fea66d8cbde3da9257371b558ca8fde3da,
  0x50631cda35e3c6d4f371fc8a6fb25153cdb420b79ed2cc33d93371cdbd94062c53f5de3134a638dafe2adae5a4e562ecfcef41624bc29ae92a20ce19e82cfea5,
  0x4f492b9b8c1919edc87e9257371b54a8cf6e43f52459cdc60cfb6c3fbcc9a91f38416a76c82a379a7baa3f5bece37e08939afb3fb3b35fb36318bb685b7bf5de,
  0x8833867a495cdc74b5c30fd4f371a2a5340b31e1389298977b6c98bd95f5779cc4d5f8d232f5192bd57b7c69b71a79b8d16ded93c4c9e78c4d8bbfd74509a4ed,
  0xc76f189f7e3f7b6c6de313efcd5adedb4ee163f7b6c6d24ae6e3cca98cf6c3fbece792f2cf88f3a63dba5940dcffcf49bec93719d254419c33d05bd926e33a4a,
  0xd453ab2dcf504360bde36c1e262e32c7ed9f9ddc52a59d99b0c82f4e5afc9d1ac926f2cf9161013c0ce16de76c11a8cdecedc6fda8a7167d87157bc627df8fde,
  0xc68b5fdecbb61e5cc1763b1b9f5bc04dc62773d95e3b30c156ee2952ceccd8465ebfbd976c3dbd982ec76373eb78dfa4cf1534143cd8f6e76b2b5b934d5cc7ea,
  0xcb9ceea3fbc6fdc666c74ba1c2e5daa287f46e6932320cf5d3ab270c434b6b88270b32a472dd2657d453b644b59b28916f16c5c6d95b2cec9cd5ad5a7564ed99,
  0xead0825cd5ee36f3d4fae6dfb8efa4d4538ad2d13246be25e87dec497f38b31ebfb3047a9eeaf0a594604bbc04dc62773d95e3a8f05d7ba4a8833867bc0796af,
  0xf9f9128f42e6ead232e7516a8141c59e9b247ec36f38b6c5f173ce947edf05ca06e7fea22d2cef3c28269e79a4d4538b3822b2097514ee3992b22fabb2682699,
  0xe5fed8e36c9b131250e2d69cb5f93a350d169cff57e15cb4b622fcdab0ab4e7f86292e5a8a773ccce3917b27f19b610aaf33dab7809b9899e634ec625ed49e53,
  0xdd4ef0fdfc0967f5042abde10607cf666e156f224c9e635e3c6d63b8d671585b7b8f1b72db09463656b5728beacba6d3fb369385db963348cb9de24b7329dc69,
  0xb07d7b2712c9554855ea5295ae53ab05fbcc35464a967644a05afebd4a52b5cd27560bf6105ca2f8e03330bf776e73166f4d317b8f9298130d7a0cc20f847f53,
  0x26e8ca3b60faf7d32328e1702d9d8cbdb6128ee98d5a94a48e8462882fd4a52474cdc8a20bf762843a9861fb8f955fd6cf2f753728b1c32c479ab03adf8a751d,
  0x29c65367c733f5aae7ad56036fbc6d9c6bcecd1a62faf78db38db2e3d9a3acadd8a10c7990fd85b14211043f72f585d8f3dc2cf632f640cd67deca42d7557bf3,
  0xde7b627f0df0b5cefb1af542f7975a7ce7985e961fd85c06b9a85e2db685c06ad3196bbce3606616c508553f6d87f71f70f17ec46da30271a8a6db094738e55b,
  0x79e669b22d09ea71b7954dc6d9593abf49bcd26e31362eff5d93725d8a10aa7ec161fd8678c3b584955c7d9b354fb6c3fa8c95eabd4e36f105dc5efde9636ec8,
  0xafd26f2f148f95e317bdb6e58ca48fe4cbdef2b609705582fa72d7e4e189726a29da64cde4b358ee35db42dbdc78da3c52622db4c5f1bcb3ebc67564fdbb60eb,
  0x3217a93ef329eed0c099b4ab6538d8ce399fac6dd5f6d453b9e678c0d7bc46d2647ded99fb7992d6c3d3be5e94d9e6859a7f79aedcf2513316c63de2c7c7564e,
  0xc87edbbcdb85b142ea8a5aef0fdbc68a77104e4be45b593cf071f1be344bd44858fc47d75ab71950b50f372153f91e617a1c2e5dab1c9f7375680c0dcee5a352,
  0xb033919eb2688d4e7b3b52df1966f0718821217f8f79aedca29e098f3b673b477ce7d33f675d7727d5dc7b31a9cc66ca656f9555e8cd6b366f87aec9e53e1a9f,
  0x1acc164a72c2ceeadcccce994dc5765edb72c65247f2693446a73194b7c6bf6de18cf2a9b2db5b6ea195bf264cf5ba71894ea575dc9f71f3fc7267d3eb268cff,
  0x5fdd7bc62c1f49c3c88e64de313e1a9f11349bdab1edb26671cbaf619cc96841bcf6d11c285cbb54cfbcf33c7330c4dd0b9c5a9570b6b30c6aa2be922dd9e0e3,
  0x18717aa9cf8cbdd8ae7a9377da2dd44aee387e95a2c7b28e96e995b65ed1e695d55b25617a93ea5295a91ac43bea5295a91af70bea5295ae6e56c7f53ca32155,
  0x4cd3cea29c597b8764b72d275d9b0d9197ab659d93a9b35ab73227ce79cc1fa94a56a47582fd85c65fb9ff98f784f9294ad48eb05fbce790b2f527de399e24b0,
  0xb984da8b26753d22d26535df27a4dbc52658b7aab55d2f37c59ab5cb0c6aa2be55da3b6d9b49a4b6a29c5979308cde77649b99de192c999f6ea953cec9fdae58,
  0x68bb59e03b71135cf07b59ae50671135d977d03ce96610d5821eca3f6d396bf27662d7e74eac9d94423379d79ac9c7e44e4d3ab2765a5a5bcebcd64eafd296bf,
  0x8b3b14865aaebfc7650b4841d6dea29d4a58f73cce9c597b8764b7ab2bedbfe5ad5219b6a936ba47082f1b607c66a79630ea3729ad931c7d5922ed6780ed859a,
  0x465ee32c7273128fead3a86c3b2c6bb476bbe9de92ad7df56c9f2fc1c9d3e6d779935cdbe3169d593b2a66f3aff1d942a458eb6f46eafb6a29c59796244b55d3,
  0xe314c1b49b9f6659a3c6d838762a8545de13e2c93c4d20e69aff1c99184b5d6dee3ecd416d2f2d345a5e7dbe74bcfc7269d3cb4bed21bdb78e4bd781e3e3016d,
  0x2cd7fe779ff8ace3cccd9afe5de7fe01671d28d4672516f3ff00b38f2a64ef976b3c27c72d7d3cccd9cb2ec9b3cf1b670d4c2e659a116ded1e36c1c1c61732cd,
  0xf6cde4a76c5704fede78984a776956f3af3f17e6ecf889b787622dd2ef32989786328bbf98b8e4b9ac2ef3ff159c736cd61779ff8ace3cccd9ac2eef8c4f80f3,
  0xce5aa1958a543dbcf6d7e0573a3f6cff54a76ddce09fdb6dcd26e678e16e977267815ce8fdb3fd529db773827f6f13fb04f65aa1958b470b7bc725c99e0573a3,
  0xf3db26af3824a61fb8763cf6c324f2986f3dba99b52a9cac52b252e9648ee6d705b113f3a20a7c4f1ef171ccd62ffa7a96393672d50cac52a18b9ed6306c4a66,
  0x379e643ee54170ec78b12364fa0bd8cee6b983ee541709f16246f157c9ad8ed9ade09ab1ad347b73f8b7a0b4d9b1132adbc1c630c4dd0b9c5a944ba94c3f2790,
  0x3b711b56d4cf2d4eb01b556d1ac1f7c06b49660d75bcaa654f323030f748d93f53e2622c48d18a6c0c3dd23478c4c628f37cf6f2a0b8763c5891a04e4fcf8b12,
  0x38dbc627765b3654425adcb6c21559fab42e6ead7329ef3d1996d842ab3f56f04cd3b86b0fd5a8592ff56e22a8c9639de31d8e9c80625372995ae9b05a9945c4,
  0xcbd58558bafe3a653715d97bec1f2f2fb0fdd8ab22dbe56e5cec9f1dbd8cefbc5eac6267bcfb54552a6fcfb07dc459bca2df9c584adb274fa6c99865318f9c6c,
  0xa6bfe4f23d778cf8ce98f5d1b297fd0dbae89737c75fbaeadfc55aa2091ecdd9acb7b36e3064d5714d907b629b265256af57314df8f358a5fb26535f5b3514e2,
  0xde34d64e1e517b6637838f295ba1962863bca829b385351b53c6271ab9cb6d6a92ba8b098c4781918aa66c9a78f87622f6cc6eed271e38677627f35771783b6e,
  0x6574dbcc2ddd4dcc3f2532ba6de616eea6f733ec675aaaaf508e36960a1bc5c135a0d9d70c6fb66e37622c9b595aac5968ff189c27a94de592f38da1846459b5,
  0x3b7157a18ad93379c537b9ff82eee3695d8a188a496c9a4d462c7dc64ab6f1a0bb99b651153ac1fde5717317c57ba71b64cd4c6c2c48d29b3cc8c2c4ffb99c62,
  0x2336d59d778cba9db6d14ed05b8dd9b225022a77bcb313fdb22505b4bd6d64e72250228dbde51f1d722d6dad5939c89408a36f78d79d912811457ade98b35de0,
  0x302da3b6cf78505b34605a4651db67b468a76d1a28ebbf3c7c4f1ef2ed68d14edc82a3453b7947d468a76cb947d468a76f19c06b985b75de51f665a29da7170b,
  0x56b5c8532a55e2ae53eb71f64e1e73053bd53cdcc7b09d159156bfd453b4d5855175764f0622afaeef3c926455f5de3daa7945358916b6a5312db75da302dd9a,
  0x95b78f94f9e3a6205c2de3138d72918c61ecf7bcf724a45ffffd93626e2694a57b13724a458ffea66959850cbc8af7be102d6e3ea669593bac327ef7c205be1f,
  0x775d934f1f0ec44d3a1bca9ae54a7ecc7709bcf724a45ffffde37e860115e26248168d90ce64b242ae16a32e58c28a53a0e666cc58e40eb6b215b5a66bbcdb25,
  0x8bf2b6a99ad76e9752f748bea661985718c7ef7d4341eeb2203ef29f7329881c2d0284f372a4bec259df98feccd38611a531054eebbf31fd99a699588d29882a,
  0xf1c9d766515c2da715e77b2582099f2c1f5cf1cfa6dc719cd75ca67994e6dc629efc96936d9a994ae58c2b6b41cccc90202aea40eb6f1f29f3c74c2ae16ece09,
  0x52a1a0fd7d85718c7ef7d4341eeb2203ee6acc2865cf2644f4d85adc7d8d513dd56d54f90f25e4aee97d756bc1357b32af15729f5b8faa9f21e4bc855ee97d76,
  0x33c5de61894a57b13724a458ffec9d6c0b38ab56894e605492f2e522c7ff790f25e4aee97d7697041e697ca3580623f4f7423d6a5ee9727d18a15c633da6a112,
  0x2b79c5b2b91d9559f87de43c979455f5d065cb1856d46c733366202aea40eb635182ae16f189c2865ecf644d8fbb87adc7db82f31decc771c28426e948bfc7d9,
  0x1684c7a992299b5cb46557597c3ee586c54532db3663969ce8f30a0348873e8bf1f7281876b7189d9bac3291a448ba2fbd139ffab3e4d3abeb9c8ffc34a47916,
  0x99a441f53b508ce9d6cf0eb0fa65f7d5bcca6273ff39ccf744eafae3923ff0d291e45ff5b5eccd99c4f1f012cea644e1d92eb74f36e9401fbead933a9f071fb2,
  0xa278fa131ef329ddf4d4237399e15d1d40b71c91ff86948f22ff1f7994eefa6a11b9ccf0ae8eaa0b71c91ff86948f22ff1f795c511394570b7bf43396b677d56,
  0xb16a536e8abdcb2997d6f5bec63e56caa54f2ca65f7d5bcca6273ff5dbcc722757d71c91ff8770f22ffad0bc2a6855998fd964457677faee94a083ec9abcf071,
  0x7d740ce32942a52959d4ba57d5bc651e620baba47f64e45f3bdac5a94d9b9ef72ca65f5bd6a79a139ffaede63bdb3abeb8e48fe9b87917fd6c9f998d461370b6,
  0xa4f51fbc33ec17cc9adb21dcd26b6f08fb8c4d294ce46bde5dfdf66add0baba766f623a5a1cb92b0fbde32962932a6cc082778c5848a7bc23b49cffcc7a5e515,
  0xe58eea6dc7ed9d67955f0c6def0bb02c26048bee417cd12f8618db09eed9a294803fbdcd6fa21df6cdcec8f955f0c3fbd7ae4a556974afab477349ea3f7d83b9,
  0xec9a78f876222c48dcce31318b79489bba9b26a30e9855c2d6aec4765ccea2a19558d9aebc78fad52984ea3cb71c556132b71f7984c8b0a970b5dc6dc2c7ea5d,
  0x37b3370ab64ebb12d3acfabbf18d9e2fcc7d21fde653e3132b4a9e1c94ba65f7c3efe79c82ee6b868bebfdd6192b4a9e1c89a65f7c3ef7e864aecefaad334883,
  0xdc3144882fb6f329881c2d9378c83b5c16f214dce670ef38d957fb53a43fb99ce3655fed4e77ddb6bc85363f768368d557fcfa7bb6b1b50ab85b1a8c5616c9b1
]
def gemBitBlock3 : Array Nat := #[
  0xf5a7ce5b0ccec1f3f858e5bc27d4759363851302c72de27f8ecb4accef7714e9e5a56d64bd6319787671908514924725eb1b9e1d927f08914524db2f53b53847,
  0xdee3991bcb7b1d3bce298a1d32cdec71b4e2f2c678df86de714c52b1aa3c5bd8e36f2d4cb204ab96597cb63555e2aa565bcf15caae7d69f396f28a7ceec72ab9,
  0x1a0c28c82072d93135a5934143cd8f79f5ddda4fb61167933b829c61f076d8d76459cfb6d3bcc4c1ef63a7796a6590269c92b8796f08ed0da4925bd8a6f2c958,
  0x4312d6f915ef0b8a9ad594ff1bc461b4c5619db12de33cd649f92b5769deaf29f65e453d5adc60b5626b5653fc6f118d06146410396d64a6acc4d6aca7f8de23,
  0xbcb53ac06d55b6bf072b5cf6991e20c4a8b3ae25bca29e098f3b673bc491b16a28c694c20e9dc8617aeb195f839f6794272581c9957d64d896e6efdb14273f20,
  0x2bb896ece632bdd59a14c8d648618ca1a51002bdd9cc657bab342991ac91a0c650d288015ee6a30b26767199b18813bc7335e3513b34a7635923418ca1a7e457,
  0xd88d06e434fc8af416e24131cd8e0fb8d3785356aa2eb14df1e9dc9b6991721aaf54477e25b275257b2c04170b5eac45ea8bc9bd8e9dafc1cad73da64788312a,
  0x3b3f8b36f9d0a66fb623418ca181d1062bdcec85b2c479d31eec425d8a1253be211a0dcc9488315e966b3ee027b6251f108d063287bff22bd11c27df717699be,
  0xcf8636b9afd597826ab341aae6882cb58cb913a2bb8643ea27c625b9baaa9cd34eec508553f6da76bf0ba132bb864355ebf1896e5c7db020a21aaf59028968b6,
  0x943df92bae5bc06a7169c6d9064d571c6ddc5cd1e431dafd59b9348ac61f5de6b9045cb762842a9fb6c3fbb8b6c8a9cd3f0c6df4d3b8ad5accf061fde1762ab9,
  0xa2065572dafc1f67b4c8d61418943df92bae5aaaf508e36d7ecb8fb736906abd43136b96fb389fe7162a36f7ecbcca771fb2b2e37b638db5f83ecf6991ac2418,
  0xcb66d8f969add2764ac958643ea20dc425ab1228643ea27c6b96d7e58914321f513e35cb7af0c94a8db268db864a5836f29f508f4321f513d396a27989b8643e,
  0xe4f2d025563fc31f2d1b9c6caac7fa2fb470c87d44f8c4b447a190fa89f1896916d88fde17eb93ef3b155ea1e34d932a66aaabd43c69b2717ed728a190fa89e9,
  0x43ea27a72d63e1a98956b96e92bf869572d02554c1e23555cd3d2c3fa45b62b6e2f753d2c3fb5470c87d44f4e5a9dc58494fdb636c9fa9cd98faf96c9fa9cd88,
  0x3d0d7f0d16096c9abcfc74b097d396f0c94b13adae6751a4dc25aaac79baa2bf834d0312dccea349a6c4b41cc7ce2c26d3b20c9aae3a76804d57ad6b972da386,
  0x6525b0c8625f8d72d9320cde409556be5b0c86abd7d396c321aaf50f34b6190d57afc625adab1f1ed562069dd4d0c86abd7e312da5d4d0c86abd7e312dacb7b6,
  0x91f3ff6572aa9ba979fade3a332c995ad287587a750fdb764e1cfabbece7da9c37cec2d6f5bcc35465fe7215576e512c3ade74d58fd75d864312fa72d8643129,
  0xeab9fb7eb5efe8936937a63b30dc9a30eb51718b4332eab9f50d7e97bfb0cda3327d35ce12286ab9f50d7b5efe8e36e278f7986bc2a67215576e512c3ade0d6b,
  0xb2eab9fb74a748f9c6c8a98fbc3f736e16c50baa296bbc3f78c59fc165d573f6fc34ef08ecd51fab5840355cd557fa21de3167f059755cfdbf5ad3bc62cfe0b2,
  0x96d9a8c3029f7c6fb1efc598163ade5a9cd9ca20c6d2a46d5bc6e42963180d75a531790a1aab1f4aeb4493e9aa469523e1a9850d558fe7c7eb1f4863bc62cfe0,
  0x436db9876be734ae6e0f50448121a617c6c2ca2b85bc33e948e121b7c17a42b9b929e9108939cb690be35214414af82bc25b253d23727396d217c6e92c9b0af0,
  0x57850571823900dd9387747bcb53b8c7f97a40378c59fc165d573f6f76c79ac9b1c3ed520ff6cc6f326af150902c75bc1350a14b2b38fde3167f050d573f6f42,
  0x8f7e5345f62268abfcfe94ec6aab9a0443bc07993f3e788f994d1539a045f46788f994d1539a045f785d8aae6817d7762cc707dd153302c75a1f2fd866216fb5,
  0x8de64b05550bacade3167f059755cfd84de3167f050eb0cfdbdf6f3062ab9a5c3bc27c7e91ea0e7c70c49f6b4d71bb1662ca764ab17781e37f0e6935ed3094b9,
  0x27593b285a3577a765a3635f5def18b3f82875979fb2aeb945d693bd33e37d11bdcc18355119df78f19fe9d31d6ec598b35855175764d13511a43fb2667caa89,
  0x67ebffad542c74c2fdfa1c16b2e19107b87f64fcc854e6061c3b03dc3fb36ac9b1c3ed520f2c48ddb6a9e4fc2677682d0b9cf376677d3b5ac9d942d041281ae,
  0x22275dfebb59a997baadbc6bcdd392521c3b1b74cb1ee3c6d5b54b1ee3c6de3167f059755cd8bb1e530668a9a50eb0cda691bf9e64f0eda17efd18c260b86586,
  0x1a55b788dbb3ceb1b7b36e73ebbcbb523efef9f9d6678dd9472937954c2257e5269fb37a907462e2e11f5639155587d7788273605bdfaef1b656f60d3bc42611,
  0x64729c74a354eb78767c9c76f0c97867c25d934e8c64d5a0b0166083abf41602cc10710fb97d840d3d7b890420ed3fb26419bcb4e86b32858fd475b781e3bb79,
  0x929db15c13fb4b092c6ae405bcf6f325e21da55d7397cef2c969190aaafead1f229a8b2612d9e629bcebcad7e4ecca11a2deff32d50f6c537812dbefeead3d02,
  0xc62c18f6db9a4d266a7b133d553b5cb6d587eade64b76c5378827c319ccb3415ceea52d33884abb88a9cc7baa0eae45bd3fee653d371bf31ed7e1b55ce8fdb37,
  0x49176aa620bab945245dbf8b675b7b6ed8a6f1947597094beaef0c64acdb94584bb462e69bc595bc6fc76bba5de0a7d5dd2ea29335345d9363b04d65dcedca2d,
  0x65b6aca3d95ad4ed48ca64277dbca2dd5ca94aeedcf314d93096cf314dcc565c8b7a234d177302504b916f794593ce604cd77ce87c2edd5ca94aeede516eae51,
  0xce6335629185a6ced7bd38b980c8e38ca7a7a529003def30d77684c70718545de506728b7572a522eda46428d47f56f28b7a7d4663977dda863d9387945de553,
  0xebba07324861eaebfd1cef1a6b48b251e449cd24861eaebfb1efa65929b3a0b24f15dfe65fde73ced8a9df022b409848bad67d5ebabef5dde3028d70b6c32d52,
  0x8f829f0c6732bb5599aade362ee975cf0ea6983b29cd62fe824b785d8e791e345d73559b9216c2da86a46d54d22c99eda61cc93c55d451e94b50d726dfa45904,
  0xaccadd2bd547253dd7d6c2fde71b6639accf56c4af55b7a7a5942fde592b914dcc86274dc62d478535e5596f0c65e5596894412537b8b419e18cb9152d951cb6,
  0xf578c08fd22269b6ba2098dbe580a977944d3eb485bc4e45343ecc9a5ac065134fad1e14de2bce5ab2b32af51d567bad1afee5ab32b74af551c94f75f985fb96,
  0x6fbaea074d65fd02455ad4922bb2abfb596aca4579c8d5257dd7503a6b2fed65ab2b32af391aa4afbaea293597f53b70cc4e45350d5e728ab26ef4270a5fd636,
  0x852fef3ff6655e7235564d7549c297f79ffb32c79c8d55935d5270a5fd7f60b32af391aab26baa4e14bfb98e6b309b12a2fcff5f752a502fdcb5656655e72355,
  0x53daae51062beeba80557f79609ad530ee17e6ebbf058bfa2731352ecad228a7b55ca20c57d8fd4665fd120cf86ba458622ab54d1e96f3ff22bce46aac9aea93,
  0xa96c9e1ad134e1ed2332d1ab945c55d68d7f48c85e9c6ae5171575a35fde789a2c9e9b2e5171575b8e5fd7f0d48b27a6cb9455935d6eda57f617083297656914,
  0xd81b319c096d85f172bfdbcdf720b63267cd2ec7cbc7a66f6595b267649d3efcffd43b69e2adb8cecced58ae535b26e3289a7d68d7f409fc5ca132d027f15c8,
  0xea8ec472cadd8828d463f9ada72910b3f4ec91fb0da9cd72d11f0ec5d6fc9fa470784a5c2de38cfb2b26cbdededccaf2d99a94c1b9bfedd8b95b28c2d77b2b5a,
  0x2f7f3a2f5aa5336b968cb3f35a5f79c6dc5d55f1bf3188db9ec2c9bf29e73cc3a7cfdf9e3991007f3f53b7329f2c94243a0721bec9a78f84f8b12379cf34b0df,
  0x14bf3d7bf8a7bc4bf72c9730e9d46fbc4bf72c94243a751bec9e530defd77041f7b34f3cce93e7c4697a71257b041f7b34f3cce5efe7c65e92579fc18c4d3ce1,
  0xd6a3660b9a8431f735a3cf8ccd4327de7dafcf1a68c5983331821769859cd985906baf462cc1998c10bbad92ce6cc2c835d7aaa9adf1daf735af349ab176d4b4,
  0x1df3d9a6852b482163f788263c6263134f309136f0a6f21e618579ea782d231b2bc559b152855602e60081374300b1fac603619372c4029d575c687d855923f4,
  0xe355a03ee76c58ab0816aabd0229b3dc5584dcb4d00a242f635d7bc164a6ea94cfd9f1a4bd5b924b1fa03ea563162ac205aaaf7897e95041ecbde1d94aaa1db3,
  0xb98ca81ef7f40c7131d955fb031f7715a79bd98ca920c3f780f3c1c7824a657e2ccd8c3cf682cd2c2253235e6f67c6a83d5b9042c7ead4b2c6c9b969900ce8ba,
  0x7cb18cc6825f7e3bbabcf53734d6aa4ef4f3adec97229c7a687dca03e653a50f79d04d549de9e75bd92e5eeba187dacf01e58f9c59354a681ce94daca50f7964,
  0xb16292541b63423a7735ae66338b6996c766036efaa5c56f3a08b3f8b63b1d2a6137a875055fadab1f1ed7da5d3bc896e73c879e6cad563a1bea25f554ebebb3,
  0x2d63060b4b5d6db5bd4078db9bbf5c27a79b18d9b75a8bad8f15d63e80fb9db16214c9eadaaaf7377e4f557479b1ef2abb5d6c789758fbcb25cc3a22dfd0fb9d,
  0xe2d823a54c26f50ea0abf7307cc4c05ab5cddf923b117479b1ef21e7b5d6c7a7ac7dcc1c35310bb4c2ce6cc45df75eb183054ed6db5bd4078dac6716d3b5b52a,
  0x4810cd993bd93a9d12d7edb859ab596546de7daa2a71b618b852dca0b52fa5a1f3d99ba3de592e61d3e7ead7377e48ec45d1e6c7bc879ec6d8f4f58fbce822cf,
  0x693826ab724a41bfb0be65ba974eaaa6a846d7bcd26add693f8dac7c725df1e36f1a6b365567d96c59b365567d8f016ede24a90219b3256a33a1cb5fb6ec0c45,
  0x2d95c85393aaf79cf31a819d0b2845df75ee6739e61b504a22eb0f5ef08fb8c4d295ab9eabde5dfd45031ee1d9ef8b373728ed97d87ea5a75b855a7fd9862ae7,
  0xae6adb2794f99f6d677969f1a6abde171768b2b9aa1513443b9a8c2c99d9a998c409d7f752ca21dcb7c5972f663b64a8859bca3b65f61fb59cf134e6ddb5b56d,
  0x90743ee5dac9a8ce7fee2394edd5f30c67faaf7622789285bce9ad392abde35e69cbdd57bce9ab9cfd6da23efc97f5d5f3933f5b79cbf56f60d3bc454c09ea58,
  0xe089f55ec9e4d48b73ff711ca77e3cc3bab6f2f164fcf9296a8387cbdd57a94b5452aedbdd57a94b5452aedbdd47ef2f179830b3954c94d010ef22ee97ae69b,
  0x1d8d17f9247972def2b65184a2ecd6a476345fe45ef3eb96f785c5e6328bf30eeadae73e8877f6ccd78c53f9877755ee6bc629ff40eeeabd2bcbc593f3e4a5aa,
  0x73afec9a94bb63b30cafa45b9ffb897069df8f9899296a83ae13a2fb82a3dd0c8bed1f2cfb9459202ef68bf3e25f5da3e59f728b2405ded17e723cbebb27e7c9,
  0x318f8c185580432ded13235dc2ac020f7bc27d40af226f56e111f50a8bbd18956998489b7b8d378c4c6269e61226eea6d65fd1aee1561657bdf4fe51363cce2c,
  0x3e32971c1775f7b45d6ef5bc3a9ef3654425ade64b35515f486ad18b8dfa862852db4f8ca27882eebef689a7f8fd86dc6fdc6667ed5bf8adc6247b3766b2ded1,
  0x5ed666d599bcc7eade76ca3a3d9cdb5e7fe2ca2de69324445383c8b2390d398b49cb5dfb2b7947dc89309d9911fa9fd9bd933a996c867b6618cda911168deccd,
  0x1277533c883102740150a7a5cf2fe1c813b447cfb5a734a6c778d35853634f30e57b79ed3a62e39b52ad68874e99669435c83b8f9fe38b34b2483bce82f99567,
  0x90ac54d379cd99583ad23e51f1fa977963ba9bca0c4888a70791647234938eea3d276cec7e59f5b9b7f64e44f7a89d7c99abbce95d6b7829f10ef201de36ce27,
  0xad379cc5910eb56acc916739aec9bda9fb89886269e799585bc07618ac2db8eb215b5a6f39b32b075ac7cd26acd2db7cf2bdbccc79d3d5b0ce64b2440e16dc75,
  0xbcdec0eb6a4c14ee1114e0f07d4938e5a453f319ef89b1fec15a1bafef7941891114e0f22c8e469271dd46876cec7f6d5bd6c99530c4d3cc24abdd69d85590ad,
  0xb6f3dbd5189a79e626de7b79e678e648f893742e7166385b0db80d44ee2bce4d54d3cf3cb429fae8c4d3cf32af71a68925065319969e7989e9e7b6b215b5a66b,
  0xea135b1fd048757ac75ec99533f88ee9ee1564337b2794f817eac85db90969ec7ccabdd7fd6ad4484b1de25255874729d65ab75071281efd0ef3c946269e79fb,
  0x722d1e634e1942ad3cfd3894f7197bc43ab0efa0c7561d0e82b91d1bd99a7c652e379b5d86dc27c7715e726aa69e79f12853f5d93fb511168decc25cdb34909,
  0x15de8e82f603388577bc833da19ecf4b2d3e896c42d36fee2bbdf8c4a5fa7096c42d6d4bfdc577bc4a51da2622e6cd0ab0083def0833882663bfdf528ef01d84,
  0x9e79cb19b7312b1792fbe7e96757db78cf3fdd47bc679fee2bbdab8e4d95ad6a3f953c4556542df71fb27832b88dbac5c41badbde44984ed3436de96ce33cff7,
  0xc4a3de449b8cf3c4a3de33cf1066de7014e91b7978bce029d23691f2f179c053a46de5e2b9a7a587f78cf3c40f6d3a47c23e17399df698bc33ecf3e20b865ef1,
  0x7e88542d032bf7e88542d4ed96bbd3bbf4429e7b42fe8851ea664d485b294d7383d4185e9fa95a79e7dcbcf6818c511176c52a8babb99c626315d32b75378cf3,
  0x36f94d2dbb89416b6ee2010b5bc496bb88042d6ec577380ac356c9826e70a7b6f39750b7fbea3de64b66ca886f6adfd10a3dafdfa2147b2ba9b22151bd49f6bf,
  0x90f79c9f90f79a4c273935b3d12db50779c99560f7b994952fb239ceb3d1739d53ef39329241ec2ce1338a8dea4fbc4a3de215dec9826e251edf7128f78950b7,
  0x44b6dd7697a607b4bd316bdba9d2f4c5af5cd3d2c6da5fb341ec9a62a5fb341ef149a6cf9b2af5e2c48dcd2e91b697ec8e1e8835ca9fe12465af6db6b50f7b9f,
  0xf6eaead5a6f5f0dfa311ea3f79632b505af86fd188f51fb9a94c0b2165ef2b65184c335a4623796bfb8ca7ccb190dfdea47ce027bd4edc28269eea8fd6897a67,
  0x6ded70b70dfda30c75fe7ac31907da3094b4f66b68f7d6322fa94fecc2eb186afa94c1d7180210485eb9088df8fd11cef28a13e4775c8446e3ec2ee616fc8f7e,
  0x1eca3cb42c85ba7ddd57dc7eb94524b7620a583e5a7bc2dc37f51739b119144d335cd4bfadbcc267f67f6335ede45f53be2924967de704f2d2b3217b9695134c,
  0xafac5ef3c4eb3d6b3f7ec8dfde37604f8f35a04d32af676101612aa6bd02277c795dec3e84a5a777b56a762d90c8fe5b35bc71c9b5e779833799670a8ba8fdd9,
  0x6019dcd2290fdf6019dc8192643f72d2fa7582f66cf9b2af7abfe6b4fbd5ffab4a7d6acd88c8c795ef2c66d86ba95cec9d6ceafcc90fd0582886d69d2a79525e,
  0x9061a1dcc4fb4aa7290c343bf669f78525ee648a43f6e9327c59ad5dcc8990fd23f71fcf96fcd4a7de61dbb993d21fbc719b6ee644c87ecdb3561f2dee4ea7df,
  0x648477b9eabcf47a22ea88778c53efe45249bdefe452949bdf9ee6b67a70fb4aa7208dbdf9ee64e88758d57f0a2be1d6df9ee6b01b7e785193c36a2e627da553,
  0x385ea32568ec759ead78bf0b2cf75b47f166c8a4ebd451bac747d90368fb2175a3e6900da3b1c80da4630f968f9aa4175b859191e93f898e861def735b3d4c5a,
  0xbc95ae69fafae8b9cfd6d1fc2ee5e4ad4cec7f85d6887d865eccabdf88697d6e3eb9a0fd6de64b05f9a739f93af7ece7a3ece7b5f87d9cf470bd464ebdba9dc6,
  0xdd8fe173cc7d1fc2d3e63e9651955587d7785cfc95b239cfd6de72fdd33a99b734bbffc2a443ea66dcd2effee46443eef8a49259f64c8ed4bbe3777cf1f785dc,
  0x166e42d3d66f5197ab659d93a9b35ab78e64a9648c0946aef726e1a9fcb4f7fe1772e76e5a3635872de8fe173ceb56abea5366e7bdc78a997d6fd7b21dce7ce,
  0x69697e819b35b764fcef0a9aee23603296232cfa06616f6d6a967319ab148c2d3676bdef1899dcf25d4cf104e122a72aab577a1fdc2a6d93746333ad52ce63d8,
  0x5ba1962863bc413859952396e932bef1b671b656cb3b27356b568928716b786a7f21fb6c9e53f9f9128f788dbe7536ad7912d731925d36cfdef84d91f40cd9de,
  0x2c104cf960fa998661432f22bdef840b5b8fa99864eeb0c9fbdf0816f87d4cf214ca9578ab94fadc7de2af4315b266f7336ca22a7583fb2693586119166d7729,
  0x7677d5699a441f56a5366e7bdcb2997d6f5ab529b7455ee594cbeb7ad8672d6cefaad334883e8c50a1973c9913d3616b71f7984cf6655e2ae53eb71f79f6bbd9,
  0xbca3ecb468a1ac77b5fc2138fdfc2d3e63ef17557c6fcc6236cd98faf96cd88e4f2da11e8643ea27a72d7b3370ab52d3acfabbd6192b4a9e1c89a65f7c3ec325,
  0xb7d6bc7ef0b9e75bf85cf3ade1761d968d17aef416e24151e631ff84275ead56a750dcad8e7f09fc5e8b2ef5bf85cf31f68fe2db5607d7bf85ade63ec8e7348d
]
def gemBitBlock4 : Array Nat := #[
  0xe2e9b850eead8647f2d9ad0fbe2e9b850f74adace192d53ff90f74ffe9250209fd44de47dcedbb67bff9193c36f1bf1fb7c2f156916dfcc5f1b48c85557f56e5,
  0x97fa3ceb40babf6157f31f790f28cdb1d461d6f3af30c8fbba4ceb47b1e75a25027c62dd33b27cc4f0f63ceb45c94e7f8b29de778c4f8e674db1e97def87d0fb,
  0xade33cfb6ebab0318b9638a8ab75dec79d6818c51139ab2e1917574ac209e307a8b041f7992d6c17595a25e14978569ec9976763ceb4e2e164666d7dd766ce14,
  0x3fef35bffb7b56f1467feded5bc6fde9f2a9b8e640fc645c4378df9578761611d2ed300fd127886f19f1d2d5baeffededd7bc519ffb7b75efed926d79db60bac,
  0xa76b93d4075b2e474adf9e7ed5b275ad6f14675ad6ce32f3d6b5a7eb828f60150b39d2150b582f796a647ce027bddf5ad69fb7d6b5ae27593b2d1b577bfef35a,
  0xa99d969599ded656bf32b696f6b2765a5a5b36acc9cfb05ef4cef73d5dfd33a7318b5b610eea2ccabd233a677e6f6deb5ade47256f73d695bc482e0354415298,
  0x55b6cc3dc2aac5675f53309e1cc7aa7d49f7e65668eb1ea634f57abd987b85a581709a284c22a5a6bc9f5cb4c164509dd4b4d793ec26475996b2321c113cffdb,
  0xed74c2aceebbc4bf433ca82ba74eab3baee58aac3b623a2a173fd73fc3147ff61b69b855cfd4abee6d91cdb4ddccabd00fd0be9ebaead4b02ae7e861b99aa0b0,
  0x63d50eb3e2424584fe37fa215ccf069108e9bdb4c3aadf120180d39ffa3085733d5845ae6074df12a51398de59f074b232e77967c9d984e8381ba8a7d0dfef10,
  0xbcb3e48321ee06449f527de59f24190f703224fa1bfde799ac1ea8759f0348b4f1c6ff79a4db1ea8759f0348b4fff8dfedd4f3545dfc5cfda864fa0ca4423a6f,
  0xc45451f3449f437fa76b5599b39f6dec80415e0592d5bb2953be7d44e5d0d23bb3a3d2228cd96eca55efd211522a1a90643dc0c893ea4fbc292dc6fece4016f5,
  0x336c398f54faebb09fc5e21110c56411253c796f66d5990f9be5fded6680dedebaec6bf1c269d615455baee9b81bdbd75d8669655cfdbd49f6b35995b4b7b6de,
  0xace1a6c8e6316b6c21ddc161d437867c59cc07672df182d74379632595af7b392460b5d7fb59939f6decdab32737cbfbdacc9ca24ef63cd64daef6e2553fe635,
  0x7754503305d51ae4dd0b64c74b65ac8c870911d7fbc4828f237902232c1249f35af8ff66cc68ca67e5fd58765a6f6d3e2e24938cd7c7fbcc96e5417cc2774c2a,
  0xaace905ef545c10897a15b6eb2ecd6c9c1c6ab26ed960a15567482f69772a089d6d95397ab68380dd7a69c0de2099c06193a69c0db8e3c9c06193a69c0d4f399,
  0xad79703bc311168c8f6d30f65ea1f83c5976f6e30248af865c0eaad16254f3cc2aace905ef2c9557864b9e615567482f46269e79855bdfaef2c95564ddb2c142,
  0xadbc23b012fa93ea52b1837fab334df012231c6a52b1837fab334df012b841c6f1b6055c2de37604a7e52f2c2d688eaaf630d22c858085280c893b97e366c157,
  0x720ef08ec04bb93eecd7e4ec39d0509257735e33c812ee4fa9dd0d9dab027f10089d38dca37548b26b34ade0259807c6c6a459255797dab075a2e78db2db6113,
  0x13e3bbe42af5f41d6bd1a81a4eb421d6bc0cbc0693ad0875af032f01a4ebd621d6f0c95e065e0349d687aef03c7980e037b6d743796a7404f01a4eb4232f4097,
  0x6812d0f5d025a10eb50b5c772ee0a35d5a3aabdf5d2f204b421d6916dec8875af46a04b421d68554af7d74fde82ae7b0eb5e8d42af5a10eb6919cc1b79ade399,
  0xf5da025df5dcb155876c474a1734cb3fc49e5e74ffed01bdb7d778c4c62ba6205bcf6c9d8cd01bdb7d747cc9beba04bebae8f9a7aebae7324016fd7a3e69e839,
  0x399c3bcbc5ea89174aa37fbf3ced9d4e08aab05cbfdea893896b0fef1c97aa24e25ac3fbcbc5181c1152aae8695e3c67a9c1152aae86c79e7a98cc53c5bd025d,
  0x8c363c94c8b999457977b417e776f0bb28e73e187f42fcce1da0bf3787e81a455ebbc69a89174aa30d48b9cdeff7ab9d502b4feca9ce6f0de5356d610512edd4,
  0xc95e5fc6f01a81262f657d5de7928f6386ff7e2f38da9ce6d8f3c1c6f66792bcbeb7679e4a110c70dfeb573728b55397917de7928cd572ff788269ce11c11679,
  0xd9b03865cf19b00693880fd90de7af466bd7466b20e8cd461bc2e28cd46ff492ac55419ac9f785c519aaebfdfcf25e6d861bc4f1a58a364e9f226c5e1760a543,
  0x8c1818c6c0692b56d931c61545cf5ec98e30aa3957d7a578f6a07cb9e23bc7b503e5e9388ec9b4636a33d2b71dc607cb903a1545cf1fa1545e938fd18b3b609,
  0x6b6d8911afaf42afb0ebde11d82afb0ebde626cd2d3bbdab7af313669f94bcb0b5b26d1974c277947d57575ef2f48ccd957a1bdce36a63ef2f42a8b9ebddc262,
  0x692f73f9acd8821c2db41fcd646a1ddeea12ec79e2931c00d20d5748ef79ea7b3aea1aaf406d7b8af3dcd573be8552cebdf0a7591b3b5641c2ea44992f53b6f2,
  0x4644b07c7988fd4644b0166f311fbec7f8b07c6f0fde3c644b07c6f0fde626e13e7956b3620857a65fd0abd55ef3c942af557a94effce54d3fae4662912e855f,
  0x78d05b12d728c466edf8a16575459d7ad5aad728c466edf84f2ca2cbbd6f547c6897bc627d51f1a25ec9d6cea70f92a3f44b02a6bd12c1f1bcbde7992c1f2d3d,
  0x5948558595ef64f8ec1ef6aac54e5e292460184a00fdcb1c509fbf94ecd69562a44fc50782963c069328afbd50a9af78e7dd50a9af78a33aa1535e819d50a9af,
  0x8cb5fd48c38a1146f3d7b26762760de559213cbc3d58e2c9097a1bcaac5cd5499099ae030947e3f48b02d6c2663f568cb5fd48c38a1147c79f5ef0bb0acbfa18,
  0x96db0daed67523388986f3d7a040ea533112227bc3e6dfe04822f6ad1050b2ca168d59d48ce2261bcf5e8d59d48ce2261f2e7af682aa7db46105080b4b282d2e,
  0xd5aa289055ef5eded5bc6119c44c18a3af51344c8ce2866798f9e95c9d7a89a26467152c3e68693af780d4084fcabdbf9eb186f5bd48ce2261bcf5ea53173c6d,
  0xf6f6ebdd9b6a0b43bfcc9e07b7b71fa593a94cc4a0201fbdff2a37ffe3dbd87db610aaf33dab78c23388986f3d7bc6119c44c3d82f5ef1846711302c13af780,
  0x1585a911168c8f6d30dc9cf51e1336de2cbbd6a52feba9e5eca8fdcd4b21e08e124d2f5e813e236a12235f5e919c44c3dbdbaf7d363e2261ededd7be9b1b1b5f,
  0x27be6d23388982a6bda12454ba467113096cf5ea52feba9e588f0fd233889848e73d7b26df8b2e5247b3fe1aa3aecd70f60bd7afecca3104af4ecc337bb2594b,
  0x994e8d306d15c711c9de0349e9e9bde653cd77260d8c90f2f23ea2806933cebef329e6bbab363243cbc8fa8a01a409cebe9652c5616a27ca3e739d67bbe0e3a1,
  0x32d0a9af46f3d7bc093054d7bc44c1535efa7360a9af794fa41779102fa7bb71f1ce4663b3a25a2c9c1535e836f4e6c18b25edf7b5b26ee05b753dc50bf3acf7,
  0x3cae46692a3a2d6dfe06937757d85cca655b58d5cb905409986c01a4ddd5f79a4dc282f615f6150e77d3e592db018183b7c6ecf5a3d9c88b3ef126a3e73bb46f,
  0x19c9aaa976e13e2856e15f63cd6652a54e10cefc485f05fb1e78e323e73a6f6171ed4160ee3cae46692a3a2d6dfe1577757de0350210aaf33dab6171ed4160ee,
  0xbb4e2e16466d9324ade14947ce74dea4162c62a72dc183a8a8d9ac9e242faeafbc06ae4a81015defd0c8bd87db93cb25b83128a8198384f034805d5f64fc9732,
  0x782cdd6fbcc1996f9059bbed733670375e59f79d8b5a298ae582afe1e1bef3a6a3b9a4d6de049bb9aa15b53ce7996a1fb13ff63cf7bcc4c12546629e2f5a3e73,
  0xd27e299fd4bfd5b8805104cd94b04ade678d6b45315cb055fc500df7333ce133a8b4a6474544fc27f17aea595fffb1ab32474b82e0690795fbb2d56648e97315,
  0xcd29dc8a766b33dea4530af1948558041ef7d8b5cc02aa587b0ddf6f08fb8f9a0bf52b5cca3173909de617165deb6f933960273b20693f017edf2672c04e7640,
  0x58b5ba615442dce961ed0b78cf3c7b75747ce6d1f30be88f9cdbc7cd05fbc7cf017ea33c7cf017ef28a6abc2aac6efb519e06ebc05fb980457760aa06efb5fc0,
  0xb72c60d8c2bc27f17aea8b3afc6f19e786d779e265786d773334c955a5323a2a27e13f8bd752cafffd06cdae5cf8e67ebf8b2bf05510b73334e69a7f82fda572,
  0x7ffde3daed27220d75b47f16d8ecc1aeb6498421af8dacc88c65f1b9697d390c368a6175858fbe4939106bad0daef0daef1ed0b785512e91f0aa25d2bc2aafab,
  0x2dc715587b37adc7d4ec29231e3e88e5e383c8bf1df3faedb1af740aba925eb63cf071e6055e5dee76da73078aca40eb769a30eb45346163e8d2c8243f453461,
  0xe9ffd487d942b6bb4c5dd9ee894d2ce0c7d9362d474d108c41dc95ee9727301fff6b34b6df29d4de663cc41f79c7645a3a6884620ee4af74b93980fffa1d0aef,
  0xe8c14c0fef1bb05306d1491ac7d14918f1f64da6ac68929ae8ea1c0b5084a52330fffb0ae318fdefa84242874ffecd91e63cfb0845cc6c2b8c6d92c128426ea0,
  0x4c299fb9811a57e9df51ec8855e09b8e5ffc6e986da9f7852514cfde14946da4fba6173b906ff7986bf1e99337f7986bf1e99aa3f7924cf165177ebe8a607f78,
  0xdb6f8d102dd30816dd4ce020b5deea6e45f8fdbb6eba2989de38ccd8fdbb609dd30d2fb6e410a62772086d969d4888a90c3c8b2390d399d4e5aeedafab4533f7,
  0x4e573492a9d49b6792f01eb7ebde176454f1054d3958c4750ea940544dc04ebde176454f1054d2fe9750ea8702d44dc17af7e2db6eb2b63cfc5b6dd656fc5b6d,
  0x85e52f0a0c57e23ac7c853bc7c5948ce58cb4ea8e79a6e0275ec990634ce4cac65aa69e79951957b99c482ad9b1f5cce58ce0b76605129901eb7ade429d6cd53,
  0x5231c5561e485adf8fdf8c8c48550c57ebd5e5a3f9e4dd20c6f8fd132d02a5295dc9ba57c3e9794850c57e23a5e5375062bf11d4bfa489bcfe4bcb1efbaf78dd,
  0xf8fdea97f2219779949449deafb8fde209f54bf91390586b0816fb8fdf8b589cc37d7bf16b139857ebde5416ce0921ddcea4f115587937556fc7eecad6b7a5f9,
  0xb12bf97f5f7b662c0999cef5cb11894fca698eb657decb502016dd0ccce24c63f6757922415582f529a530e2f293b61af7c7e833fd894c386196718a24ef520f,
  0xe1f73d31584f978a8ab3bc49ab9cf8636c8bca42c9be3651e61242c9be36b2cba50b7257726baca5e4ad84d6b9a4e0d217eca3cc24d5c186badf8b589a3df5ef,
  0x1d406e5933992d4b4b4fb9045cc9495072c7df6663fc8b545779e5a1995581f86257cc6f5aff704d6a597338ae7b5558a4951d10f1f4fc469b8caecf44f272fb,
  0x3cabf986bad2b6d415e19602fd104365b242c9be379e4ab5eb99c894542d6798792f01e4afffdcb267225bae6ccad8382d67bebb93703963e9ff1d37892bc14,
  0xb01a6831ff30d75b964c126a4cf0452abd80f2afe61aeb51973458130b1ece402edeb56b019cc1b0ed774b767b01a6831ff30d75b963b306af12fcf045daaaf6,
  0x7bade7998d78e673333c02ff52adf1b590b99a7b3948d2988818392353ce6718985e5162b0b48b0647bcedb32d441f4411160d347be35ab580ce60d876a8b767,
  0x18c36d64b4bc816979acad54cbcd6569794c5d69792a22eb645e4a88badcc54318e96bd3cf29c1dd984884a6962b61d6979b6dd6f24991467a594ef3bf16b134,
  0xa1fead6478ab90a1a4ed9a05bb3f544bcb1e4a1fea2f08fa8f652b55ac751d19d593bae70558cd3fef104db50ab85bc626315d30ab79ede026c2c8a18dbc2929,
  0x43baecf744dcbf227fdd984e88cb3ec79ba9d2a2ac4bfde2bcfa726cd2eb6e57c93b669575d9bc1370f250ff517847c164d9a5d6dfb24ed9a55d766f04bcb1e4,
  0x52545581b7852545580fe8948fac07f7947d4a8ab12ff78f19cc9a4ae16fa78f9fc1899a68f35c140ada7fdce97cf488a336dc86945e725e5d489ff68c50272e,
  0x3e4dd1397c940680278ad2aa2bfa9b39ef612f2c79280dcf9f6ab5a6d8c273e1fadbd10b2f15a5545a30b4727793744e5f2501bc09322ae83bc292f3b66c0b78,
  0x2ff7668f6696b6d4fd5f1fcc0a25e03ae84081a9df01ae7b2fef4de14ca2297b0206819d55b4f89045891bcb2573b3973cc1e0a071bd0ff4b2f15a0faa2bfa9b,
  0x6a9cc45a15383783b8aaf742a3af743fd4ca2d2dbab55940a075ee87fa495cb90eebb30289ba5227fd0cad2e6eb0b036ed53d9a5ef293f55f1df3dec26e1d7b1,
  0xebdd0ff4aaa61308e4548a5a721dc774ac0a272f5ee87fa55b54ca2b910e452ab028140ebdd0ff635a3d9eedb3cc1e0a071bd0ff78cf25699a2955dc141d406b,
  0x4ea2ac0da59a50d606d0214ab55d5d286b03689515606d735208be95a5cdd61606d23d979298cdba5cda75ce4bcb393fe9554c2611c8a914b4e43b8ef98144e5,
  0x22af3de449930af55e7b9865e7b9865d3ee3e44f3589c8e6ba7db82b945cb02d25c90b582f6e0b4aa8b96ba79d25e11a555e965cd0868be8951579ea32d5ddb0,
  0x11cb3d455e7b1aa2af3d8d4ae6bcf799e34cf3fe1acb559520a075ddf7628d51579ef1a082a2af3d0f2d85b875a49cbfe7ef2b6082eb59fbc292a2af3de35e61,
  0xa7752fa9e73235cb0aa6ae6ba95a169dab1b5b53ef2f158f74fb1a8747566474a7503af397de5e2951b74fbcfb5a63dd3ee6886dd3ec6a1d2c546dd3eeedb3d9,
  0xd605ac7f2157d5db6cf4a9d9ed2c54ecf7e4a9d9ea2fc953b3db6a7d63dd3ef2a0a463f59e951b74fbf1bcb52bd3065a951b79ed0aa774fa1f50aa774fa1f50a,
  0x17168e6837bfdba6944eb4279e02ad472140fde37ee3333f6f1466689d7d93ad8b5def2cc5f2b5de919c319f95aef4afcef5657e77bbcd02ae4bb5a7495f5765,
  0x74f3938abeb5785da19e678f04379d3572147fad57f3f8246c4d6d39b79d1e9028ff7f6c1b19df8d236268ecdbce8f49570ff7e348d89a3b36f3a3d252523fde,
  0xb5ed30cc4263d4a7c69bc8bf6f18a7a05a5616ad77ab5afbf2460512ef3cf96b5f77ce9aad6be95e6535896b5f58f3afae7dabee689ef73938b7b9c9c55f5e2b,
  0x9b59a5b6a2d8f79933b0eb7e63cdd22cd66567016dee34d1c69ad2df1ad557ac6495769e026a5193eec9626412e2cfb2715d8abcd5a3d19885fe3d5a09ef399f,
  0x6988aeb58ccf8ccde8446dd351eeb8ccde864d06785c5e24d46a2d8a6f1af34ce97c4bd02cd7f2a6be9fb6f329f189e996a90abd2334dc6fc04baccaee3dbdc6,
  0x642c8bbc426cadac32946538bf18dbc6d9d5bece97e7798983bb8dbbb3c98573679ef2ef29f7b26c1ef2e967307c46c8b26e5e56c7b2a33f18da0ccd99956c70,
  0xaa1c9ba6e035bab328e932dd6eeaf3cbde96409b5c16dcd522d2d9b2f34de45d2d9b2f34dea3ad7fb896d3cd57e758c2b9bfb37929e62730914cbcb45d6393c9,
  0x48ffb28e5bb7f1d329a6c7f6f28b75728ceb07b9c3335a50bbce09fda7267e35d6de8d81f0a9aeca59b9d6dede0e32c787aaf7b2698bdab1e4ca08c1c9a9a344,
  0x34b5cd6533248ac292fea6109515156fbb83992fef18b65a396e6bc319ca132de43ca7ab91a5a86bc78ce5a396fb7664410fce5a3ad6336c5a3ad8f2208571e7,
  0x61738b390f529b98f566542a0c2fd0d3c3b18ae532db8d10689c294b68f8935ee4462fcb99278ae0e652de21355666ab78d8a8bbc49af7223176f3992430f5c3,
  0x1fdeafa57346f3d4e5a726dc803672fe8454a6f329f01d913ba9b4b559966c69f5dd2edd4ae5cefd379164a2b76d74bfb58e5ceda61bc8b2515bb6ba5fdcdc45,
  0xb6ba5fdd8db63a7299e0373b1a80459ca2ed2b973b179ea39164a2b76d74bfadadd4a691c6bb22d82d14ae68de7a9cb4e4aee76374a5fddb9aac0249b49bceb5,
  0x1a6d3ebba74d4b6898548caccc5020f7a9e1d8c5ace952d4d1dd0c62dd4a96b56ab16a0b34faee9752d58631777c34b434f0ec62d1cb6ea572e76899c8b2515b,
  0xb8c4c05bc29b2acdce44ba99ce79722a5a9db6553b92abf53c3b18bb9031a5a9e1d8c5ba952da1bc87a6c1dd5d774e9a96b9aac024cd9818deeab502fda1bcc3,
  0xd8c5722a5a8ca4ad6ca69659db5f67d40ca9fa9e1d95fa8f0a6a3292b5b2938e9676d7d9f5032a7ef2d4fe3d371bf31ea78763177f352d48c5c627b5bc29a918,
  0x976b2dc2ec94d34fb1bea7876316154b53c3b18ae454b785dbd5652de369f5d955fd4bfdd562b9152d73c7321a27b2b2df902fed27f5069f9f500aafea5aa9e1,
  0x881b55607a6c18deeba81b0bf53c3b18bb2c96f214ca6d9168424dbdb0a19a50fb636d8e819e1606ded4bfd098b472df599446722b4faef2c97f6ab00bd362ee,
  0x39d879ed1d26f86baff49b760131ea4ad66571cf2e69a30eeaeb4200de7f68eab06c39b061eaea06c2fde516e3160c7a92b5b2ba19f1334d1861eaebb006f3fa,
  0x957eaadff253bb79fdc9833a62a9b9cfea78763168e5a0404150694d75d955fdaacd8369293520d7d85fa92a05c73cb98a3a0d29aebb1bda57f79e7c9ba1738b,
  0xdcea94de226b831a5ad3e236e94a56116f113679a65bcb53b834cb78a328e5bc51946bfaabce2ce4696f1465db1a5aabcb3ea35fd93b312a776c696e3e5aa53b
]
def gemBitBlock5 : Array Nat := #[
  0xad06dc732da880200ad6f29f07739e7165165dbdb6e11f116d91dd5d5fb999a2d566fdaebb627b7a5bb7bc4f1d18822aefe3994a69a7dc9ac5a396f2d4dcae52,
  0x1909f54cda430bd40fd5fac6ded59ba95ced2894fe5b2ede72328a0ea54126d6be3edb39172d37d4121d5b4a226752dbb84cd9d0d25f2d75f6e31b066bea090e,
  0x190b1e6b29edbcde34c909607acb936190b1e68cafb7b6722c266d21813afe3d645b0c858f3594f644e978d3242581eb2e4d8f2573566e4ce181dd55a8e74e98,
  0xa19b865d1740f7b1e5fd59b928363d819f150cb036f2f7b0c858f3594f6de6f1a64a503d65c9b7dec7f566eb06c7b0330efaba81bbb7ae6ab37d5cdb13536f6,
  0x2de34e16d86708fb7b2282a23b325a632f7ba75fb0ce11f6f6450519b54b4c65ef74ebf618c675d979485bc69c2db594f6de4e2c94a2975b45b587fc271d213f,
  0xebec32965add4bbd914143d9c200137dbaebbdd1637d9b03377ceca69d5990137ce774bbc3c5acdd76f6e766ce533771827566404df39dd2ec318c5544f36ca4,
  0xda20b937bc3c3b3355ed105c9a1dd4e26c545dd373a88c63e2aeaf6eede1d8d3ea22aee583ba88cf650f4bdbcc7d45ca7158b9d008b6946d696d9fb3a1a4be5a,
  0xaa3a3caf399257ba4dc066fa8cd6aa3d944f3944b02beeedd7027d454658bb95008b7371826665ce844936940f26481674a45b937f1cc8aa797726f3b87666ab,
  0x7740768b5a69cb7182212fc5dd7027de2bb1542dcf32d5ccaed6ab8ef80f8f3ac5775f889f58c934d9813597519ad547b289e728960526edd7027db60bec8cd6,
  0xf64cc67e44acdeb84fb1e7337b0c44813177b0bf55671e66de134cb5107dace514ce2ce0b352ef441717a759723b4fcfd454658b9d008b7d539c2ba5317099b1,
  0x5977e4e29a4b93788ff98bba03e48b6964f2923ceb3092921edd7e3efbeec599c95db94bdc26974af87de02989a645ad499120899f58ae75974b309d66f53d09,
  0xdef2f12fd62ee52e2116f306660f3395d8113e2fb9f18b7a6054cc363f4225974e2fb0562e659bca7cc5ce8045a458ee209c97c8b6f1c2745772a13ef18980bf,
  0xad5c3e12fb5db2f745774a27ee7ecbab551d653f295eebeee0337dceb29ad546144af22af74902fb9fb2ead547594fca57bafbb871cdf73aca6b55185de5157b,
  0xb17397108b780a79ef4d9935a9fcd302ad96de6535fc9d98add94e1cfae7750ef8d06f77a645f93b350e78653873ea13750ef8d06f553c13558bbe25c6edcca3,
  0xcf1bf7cde3d42d4b5e3f9f9dd2edd4ef1bfdbcb26e991966691655bcfe3cb775b865bcf2f7bc5d57354b9d3ce5e45acf2a87458df6bf316e0116f29f316e0116,
  0xb2a0e8b1be9ccc8a797a691b2ed677bdfb3c91de5dad0c38e2b16e0116e4dc1c61f6f32a5bcbba68668ccd22cab699c4bbadc32dea2d7bd1c27c03de5d5544d,
  0xb8045bc47fd9e63c04f0d207458df784fa857eb2eb4effaf84a576536f58d8e2b16e0116c7938e2b16e0116e9adb2693c9f22ce47da7d775c65de23fecf31e02,
  0xe48b8dfa71fb6f398ab18db0b1da6accd7506f7d9cb53cb0131e87dbce15c9ca1e4d3d2003f5b7bb14223a15a78560716f58b7008b7f1b05059318b765d38ac5,
  0xd99c5ccecc9cde9c9e02fb6a95b7b3139a41b996d2341bd738245cd5693ba913247eeeb47a5b48d06f731ce086fab9c9165393247eeeae65520d06f7302ebb84,
  0x269e90ceb57da5cc12ea74c0f269e900356afbc496e2932aa48ee1282c2de9c04c6b907bd44f98306fa44a45b96b3c57d76d16ef4c1769ad4fe698156b6f6daf,
  0x786ce3ab2d050bda7d73ce5be18d057df65c6e4e3a9782d4bd73ce5be18d06f6e3ebbf4d793663a978b344b5fb6d60d99b0b1da6accd7506f553a5cc23a74c0f,
  0xe363a79a18f55d9817167248622b7dcca63642dce63a5b35d41bdb8ef1dd999682b969f5ceedf5afe7ef2bb2eda767565aa5385adfbbad3e72df0c682befb2e3,
  0xc25aa30bd5dd33dd0e7c5704f0f6f78dfa86fa534a45a5923ace0b6252ba8e87d71d0df4a695d7ef627a60b59f60df4a40626c991f096cf233c5be2470ff7dbc,
  0x56bd33dd0e7d69de584fe2f6f4ea52cc166a5ded669cd56e7504a5de853a115098523ab3ca06ad5f4b0053a8a9db0b501d6773deb57df5c5cdb38b04a5dee9a6,
  0xe42bad3dc24e345d7d69853a8a9db0b501d6773deb57dc7d3612a285eaee99e72157d5ee7aedeb1416e2098134674eca215651ba2ca083a8bdbdd3013568e3bb,
  0x79ceb2e81567cb705af1f612331abad3dd9fe2f57d8f3c29c99e1276724f5a0ee198bd5f40ab3e5b82d78f448cc6aeb4f701bf17abee3e9b34fe5b82d78f448c,
  0x113e9d5bd874be8573ea0aee5f8bd5f4e2ce08ac9c5bd9369af1135c168b72d658b76d16c9c5fb2a669b3d736dcef6b3db52fcf0ab9a2e2bb3fc77d7edf719c5,
  0x4c890402928ae6044fa711c330b2d0b35c9adb1360717abef09f739e73d9fa599cd6428156cb6f09f739e73de980ab37480ab15dd2ede355acbec049a362eebf,
  0x5b623dc60ebe8c521f9cb9de714cad711ee21875f7e3e5494aec438430ebeb16eda2de26982c214d5f6a7a0a56526c4dd7e2f57de592f5736ca6de89a60a756a,
  0xf2515cc754fde346422bd5ef9d6c4d81fa8e3e8e13e01dd4d1b20841674573393f553d305a5a7fbd054df562bba1d457d6324d3660495de716004f6239ccaec9,
  0x4f3ac53662b5b626f7c60ebef39e562455856eb07f0d03cb4c8ad9bdb4f515f610dc5b69a48c5eafcf0734de346422bd5ef9d6c4deff51c7dd3053ab53f9a699,
  0x57dadb11ee3075f5fd5b623dc60ebee982c21447bd8657d5332b5b626e5ff515f4b3599320891c3107dcdbb63a4e2deec45052d66515f52ef27ed18872d5778c,
  0x64569ef4e76f42128a449c66f009ea9fbc096ac55ee3075f61938a2753b323ceb26edcbf5c969fb9f025ab157b8c1d7d29b35f514765dfaf8ebd67509bb7bfd4,
  0xd785dbe2e60430f7b58abdc60ebeb5451ca2ac9bb72fd725a7ec9e535aeea6d1d645e8eca9b6fc2e10e7d415deff515f448ad3de9cec5210945224e0aed3d53f,
  0x74de792fa798144cfd386556f2b6518cd8bba5d55ce8e43a1d550a24916a2550ae7a8ed62af7183dec6ac67e3f50e10c3de9db62dc8b7bc27c7e064e11907bd8,
  0xc2bb378fe7e40a5d3b66f9abf3f3ba0958def309b9c55e184cfd34a535d5683638e2af427d5be73ba095d3409df036ac0a7158bba5d42d94ed984fabf3f3b4a5,
  0x3ebba2bb826ad1e5487dbd85fb4a9ac5416b67eae3ab758efaeebbc9fb4b559bba6d3adbd8cbd82cfbc4c40da9b15e36337898929aa962790a7f378f529ef3b4,
  0x33cdd47d7e8c4716b6f63c5247a07bd033397a7b90ce9b98f56f6c7bd8d207757d4a653094aed8de05abed1e66ac2ad408b5a8761d6ebd162bef104ce28cd68b,
  0x64f7663a8afa16b2a50e1f9d485ad5a99ac7e764d09a3563e626a1c2187bdac55c87bd457b95d9724e10c3afb5805721ef76c5b916f7532d43ac33a390ebee5e,
  0xd736c0cef9cee84dea262e7987bd55f6721ef648bd9c87bdbe1f6e143de8969fd25d455dd22628489bdccca579d9eebe7bdeedcbfea2bea16ccca57d05dd0e7d,
  0x41ef63cbfab1cc930661dd5d40db9de1827084fdf2307d600441ef4e2fb6c3a0bacc3def1463d99ca89fafb30faf61107bd4d605eb9a877b6fa85d1c37b59bad,
  0xdb7d3a5f67ab3cc3de9c5f6d875bacc3deb4d537f56664c0121dd5d40db9de75e6e9bdedb0fac0b83def2c66b02b176004e6a3c0a22def3af374def6d87d6004,
  0xdae79f2a854a7ddf64f5dab9e7d58054d3397d93d76ae79f56015291ce5f58ae516f325b7f29967b252348b58a24916b1535916b15c87bd62e7987bd0bb8ad5d,
  0x6117bcdf79e7c76aaa176d3fb2778b24417625df9e31324bc627b5bcf6aa85104d550b7089bd132a85b844d550a969ef1cf9542a6826facb70bb06aa1534e77,
  0x6fbb1125550a47f78767b4303eb4f2f7b73bd5e6bb6db5c15dd77957bd3b5550bb69fd495db1efd0d27157d93ad8abfe76216b32987ebc7f3f20515de2363b59,
  0xd550a47f5c4d54291fd713550bbcdf78e7caa22f79be8180d95445ef37d55107814bbc73ebee22f79bef1cfa40f88bde6fbc73e0c6f85f59bed00c06d26f85de,
  0x49d54758aef6e75122addcd08d8bede314f78f9156ee6e17da460c5ec4558aee82fb7762f3ec4558aee82fb5b5ca546e873f6f76c30f6f79dd8c5ca70eaa8545,
  0x4335e8295adbf757f576f77a602a866bd05df96759376f776f79dd8c5b841deab94559376f605f6dd2acdbaf4fddb73eb5122ac56846c5f6f04d77a602ac128b,
  0x2bd5ad965b17534629b361e14ddf4ce202acdd202ac5774ba731e7989767d73ce5b0de1bdcc4bae55a3c1fbeadde996a1d4335e84056b6fe724d5dbdde996a1d,
  0xc59cb7b0a3bed9852bc59cb7b0a3bc576dede33cdc477667aedef7bceec62918eef4c8b5aa6d2dd11e759376f6e777ee302cb9b640ba8ca2bde51bddfb8c0a35,
  0xf939de2bcef4c4782091bce805d46596fc9cebfb8e679dd803df336be9c80db9de2bcefdc647821067402ea32cb7da7bbf7191dd59ce81abd415df69ec99e759,
  0x88ab15dedea69c562a5a7b9d6715dbd851dceb38b396f614773ceb38b396f614774973ceb38b396f61474a6cd8c22d7167bf75722bdf10e779dd9b4c6af52abd,
  0x62ef2d37bdaf5798faac5d8ba9a195f0b7bceb6c4dfc8de87c3a9e5e2fac5231d62dc20ef28ecc54b4f58af7b0ef15dbd851d44c5a1d8551ddad7880a19ea750,
  0xa3c29bc053ca067a6c5dd166e74b07546d50288b5b7eeafc2ef796a79b70cdb9defb2ae72f9df67aae906f73aca6b551dd2de514731bcbc4bf7bdaf57939e6d3,
  0xb7494d62dd20debc08ee904786be1f4e63a59c8af77c06f7ececc8a296dd46de96f8837bd7ececc8a296dd46de96f8837b71c79d9d9ae63b6ea557b17536966c,
  0x1f3b82f72f2ad47e1676635751bf7085bda7f7546d5774897ba2a216f785d8a89bb6b83d8776d12f749b80a5d8d7aa20ca005dd0e5def3a01ab71f58b7220f58,
  0x39c94540a7ce967165002ee873f6f76e426f7809a19d25f90f5de96f3dbc33e62a52226dcbcab5db18d4c5df4fcee0b994d37244ddb65002ad7a1ceb7ae1edfa,
  0x5d91316ef9de19f316e11371f3188a17aa0533cc6a5eebd7b9ebb7b38f714ac9d14f780d58f994d37244d881697d34df39d885bcd264ed224ad3dbb6ca361894,
  0x25b42a5e2e2bb74f9de33e34cafc5e7781e3e02662eeabe7780a6269916b526434d337eb773995de078f80998bbebaf9d636f8e4634e16793461dc1edec7cef1,
  0xfaebe7784fabf315ee2d9b7c7ebf31774f9d9b7c7ebf3177c6f9de13eafdc57c8bbc04cd3eb77cedc366a6f8c4854bc5c470ee9f3b59ca299c5929a977a76ac7,
  0x2ee88f392addb9773b2794d6b79ed5afc9d1ac9269c5acb17755f3a716b2c5df5d7ceb3275658bbaaf9d664eacb177c57cea65993ab2c5dd57cea67e311fe62e,
  0x1839331774bac5bbe76ee1d8c5bbe76e2c81316ef9de59f1c8c88f5deb16e1136e3b8b20558addf3a1c2e73ca67d9b7b6d8c8d3391c2722f7bc04cc5bbe75e0f,
  0x5d3fe62a2e9ff31774ba32c4c5dd2eb4fd8c5dd2ef0d4e194a7bf9bb354e13db7b7b13bb35cac545de32131774bb9d6535aa8c2ef28abdd7de5a3fbc06bec460,
  0xcd568baaa536f0b66abaf8f554a6d8d9766abaf8f554a6d8c32ecd575f1ef06b8faef63975f1eb17625d5898bb12ed62c45dd327355ec4bad3ea8bb993766ab4,
  0x6e100bbcef64eb8eadbdeaf327876d62a2eb16be3d5af225ae6324ba629bd374fd51f7355a2ef5645a2edf316be3d2b9aad176166ab45de34131517554a6de16,
  0xa9e7f8c5ed0a5981923ef1b60134a70a13cc39774bbabd0ad5f64d130c4d3a45b3860ebe91f3cf929f2b09e770e5da6eae9ad5f73e065ca9896606cfe8a2d5ab,
  0xdf3f613a16119093757735f7ac223235dd2ec274ba7b2302db9ded5719e6977aff31d6acc02f56e2b9769babb9afbc49ac26985d5cf30e5da6eaf42b57de36cb,
  0x75b60bbc8126eaf9bef3ff75b60bbc8126eaee6bef3ff7cb9a017ab76c4849babdc1d7d84f2db23b6ebba5d84c8faa0b424dd5dcd7d4ed6de4e5ede516f67ba9,
  0x5ed798ac6d49386dd7d9b243145bd7b2c9cd75abedf1658f3ceb63f7b1b75f58bc60858e77bdac81277d22575fa0b70ea70bee4d3f7cd64084ae4a645cbef3ff,
  0xfd6f02fdc04cb49dc3df1f7817ee56ceaa4e4ef8fbc5c6797b2c9bb79fdcd4ed52e775f73522cb4b9cfee67014de4c2ccce5e7b7817e629164b9dd7d3b5cd52e,
  0x292979ac5ee36ebef33c7428d8e960658ef7c6dd7d4d652335b1fde05fb8e32973bafbc78cf3c4e8c79b90bdee6b5a396f02fdc71949c9df1f64e24d4634adce,
  0x6de8d56bef87de6bb010142863cf2e929dd9ef7981b7c7de6bb73259e0a94f35d95ed79ea52ccce5e7b492ef96779a3defdf569dc4135ed7f3def735e678e800,
  0x5cbb235ef3cb47b74ba6f75f8dbe3ec99416e97bde9ef6e7d6f2cf8afc7cae2e79bdbc853ac94a6701ae66c7cdedb8f0416922d40cccb55962f71b75f55671e6,
  0xde0260973bafb71e082e5decef6568f6e974deebf1b7c7d934f18d66229d996beb71f704172efa65ede6a3defd6e3ef149ab3bcf2d05d4ba6f6040dbe3ef3130,
  0x3585775e99fdcd39a6ae3dec2fdcbd7307dbdb9d4e9aee90fb2d3a73a1585763fa67f53a6ba81f65a74e742b0a803fa67f799e32a460d8e169559a9bdcbd37c7,
  0x4eb37aedee5f64c1aad72c89d6cf0eb0fa65f7d5bc3b03eae0344052fe7ee415191fcee97583de21370b8a2500d8e62ef3cd35bc7194b9dd7dd3659173f912cd,
  0x9fdcfd9576732cd0798ef7c77b97df8f7f695e5cf3cd7d66f6c0e3b48fbcf3e4a6738b39d879ede5a9fc7c4bf31eb1a538576709d66f537bcfef146253a3cf38,
  0x59e94c12b24656ed8f9bda94f80d4aed8deebb735f78a304a037de6bb6cfc6e42ebed6397b790f2e73fbc7194b9cfef1c653bbb3fbc44ce761eb33987c9def8d,
  0xe3eaa759a3d9db6be99d3e6b52deebd02f8fb59aeabfd98a674ed3481ebbaf4df1f795b28c2d77b2b5b6c04f676c903d6beeeafb6cc6082cca0f37b64ebb1799,
  0xbdeee1faa3e8c9b6cceb34e63a66e978fb9dc22335736b4f4e4aaebb0f01bd93a822c4d51d289bddf01c7d2cfc6e42f8faa9d668f676dafa674eb63a96f3f40b,
  0xbbdf8c19f8ce4ef8fa994552331a1d5fb9b37f54d81554ea05047751d6fc60cfc752277c7d54f37f07db2135b14cc77b7bdd3638b9e3ee6cdfc1f05553a8141d,
  0x54e63c5ba99ceebefc6e77c7d9c6abf1b9dd7df644c4f8dceebefb22ca27c6e775f7d3d9f8f3cf75f64cb75397c67f419f8dcef8fb4bf34bbd1f25a7f479a66a,
  0xa1aea071f7964af756b28f61e155af5b4284c7960f08bf5997af907850fb59cbd78cf0aadcdfc1f05ad59ecf6c7f75d471735f72f548d5ab7986a94dee2d9372,
  0xf38d83cfaeebec8e767a9c367f737f07c98914cf6072a9a96f6e78fbc1c79f5038fb9bfaa6cb63a81411845b2b5a90176042dfa93dc5c7de0e3a0fa81c7de0e3,
  0x3eb185775d77c7d0b9b30b461f522a4d2dea75a9d5d7c86f617eb42e6cc2d187d489ea5bd9d199aebb1bd85ef726e53e79ea59b29bdbdb71e669b3631c8def2e,
  0x3e9d4653aa5ba96f691f737f07d6c750283b7bd84438951f66ca15ef6f6c9e26b816ba74a4b695f5dfad93c4d0cba7b5d3ae7d77eb7838f3ebbe3eb18573ebbe,
  0xf8fa47736b82d889f9dcfaef8fbbcfaef8fbba0faef8fb9bf83e194ecc74fa66389f7ba96c72ce3ee6fe0f8653b31d3e998e27deea5b1c5cf1f737f432f070a9,
  0x22f8fbc55f26b67f56e0ae73be3e8d267addf84fae4a5c8fbec4759c16e17cec99d9274fbc33b257691917adc157573be3ef1af382aeae77c7de35e7055d7776,
  0xdf6f8fa771bf0af72cf7bde7c66ae73be3ef3e33576eedf1f720841665079bdba6b9fd9a97a73a1585763fa67f72f3e33576efb7c7de28c7206fbc6bc87964dd,
  0xeb2ad93576ccdbd1aad7df0fb99b793379a3defdf0fa5e72ecdce77c7d02e592a27462817e6830326b7924cab739df1f64dbb2800292979ac5ee36ebef3bb2ed,
  0xedef8c13f78905cbb52b4a9f7d4ba5f5a5f6ee5537489f726f2b8b2be739fd73bafae77c7de3997b288e53722e3edce77c7de7765ce77c7d4ce5537558d68f69,
  0x9fd027f2d99e72d3a5dcf75d04fd027f2d99e72d3a5ddbdf1827edb05f60ae7e4570b0880a1ff3f671d71132ee39759fd0ee323bb630c13f78dd938e8f771d2e,
  0x3f6d9312f3969f0b387f1bff3f6d9302b9f915c2c220287fcfd027ee5ae6ac81f912b3fab5cb22754a9e1d61f4cbefab5299ce2ce400f3da04d146126ed87c77,
  0xf7d82e4a7f19fde17690b93987b40b994c7e44acfefb96b9ab207e44acfef1bf71f612b3fbc6fc3d856acfec9b99132d9d67f1f9033acfebc96af15701a2013f,
  0x19f670abafde6538595ca2dca9a73bef29f654d39df4e9f572a523c22d8595cae9bca7d9534fb1be9d3eae54d3ec6fae73fbc518e73fb0d932e73fa591ca2567,
  0xbbd43ea2b80988553a8c66739e5adde6b39e60a67b0213d2dbd771f7986b9e60a67b0216f72783a07c7de11f2652d3d4ca43f6de03cc92306356e513ec6fad5e
]
def gemBitBlock6 : Array Nat := #[
  0x43e85cd993b6899c04577d7dea1f48b045d3b38bb1784aa55c3e5a7865eebbd43e91608a9b38bb179e965cca7ba815de4fd22c11738e2ec68ea957085f3197ea,
  0x1c7dacd4d94693a81450a8440565ade6935e339140aa8178ad77b977a87de880ca0f4cf638f63a6f33871f78e4a91831ab6b289cefa173664eda26701154afbd,
  0x90d5b944e77de15352a23a8d3cf37782d37711028cbdede1c7dcb63edb1e6393ba34f3d85f9456cd3638cbdeeeafbc2a6a544751a79e6ef05a6ee220519606de,
  0x387fb0ebaeebbc38fa0cfb32dc36f3db489b4d75dcbbc2bed701e643f74a52bbb68ff829c1a62825116eb2d6c9b3c89245bc6ec1c413d888ab65b124356a461,
  0x3e7ba5887575dcbbc2beb19d59a769fbc1c6328817a5295d38fac633acfd0c9fb980b5dc626b35e9def63fca7575dd77871f7892db37537c66f634948cd3bdec,
  0x3b4fd58b2d376f6e24990c3834f8bd9c2a1a3aab4af101701a8cc39a0cea6d1ff3c93834f8fb85055ee8ea1f6b353651a4ea05e220ae1ddea8ea1f78db2b2d2d,
  0xa0651c7dcf30583e2cd33d810bec0f501cf1f4fd4bbcc2ddd4de0e3cdfc1f5b712cc3fb7701953f72e69da7ecd95c7258437bb1243569c502748cdb3fab4eacd,
  0xd7de7da81b36c6fbbde650ed7e8450daebee16d90f6e9e845506fb26e3204f74a5f434abe575f7307c46c8b26e5cbb4fdcf30585c7c653ab63a7e7b005dbfbae,
  0x2d63dd775c65de2bb65b81df6809a2793980d3e2207aef54387dacd4d95f3b49d40bc41c1ebbf1596b68ffb758e0d314ccdd51d5b596968f6d221d434d88a1b5,
  0xd2750281b2b76eb2d6e5ba41bed2e54a557ed2e54a5157dd8bd9ecb5ae55ae6972a528abeb1d2e5b9157dcb94efbce2ca9dc95ec6fb96e077d0c4d35d4b52d4b,
  0x8cd2e58437de789ee13a3acb54f6f72a13ef0c65cd2e54d33afbc33e5d2e58437d024b9fed98a97adede5d7da69ecd1f0fbc1a7fdb315d7c82de1beef8ca9b28,
  0xf2eff57ef214cad2ef285b71e5dfeafd59dc57679552e42732bbdd2955b2609b782cbbfd5fa5b1fd1e699966e5b957e9d223fafe3a447f72c21bed2e58437de1,
  0xa27ef08f84a034438a7db6b18c859a8dee86144fda5cccb0a98c43cb4ee9401fbe1f7291fdca9eafdb969eafdcbbfd5fb9db3c1f08f534dfdb03d40a5d93b04,
  0xa2aecaea64d8a782d9b12157b0c299ecb0105eea54dac1f7ebb96ffb73390f3a85b9e4ba59cc4ece79ea782dd9e5a9ead416dace0a9b4a689fb59cc4d9ad3743,
  0x3933310131eff3257aaf529bcf5393ad8f529bb2c602a5fe7b9ff82f7beb4eb195299ecb0105ef7faea6aa5c6d2cbfc467718b08c5a7396a7ebb2698840c6d2c,
  0xf09b4e8d27db019eba57aaf538dbca82e314d8cdea25850cc9fa9eafa936745ec9e53e54973a2f79cc571a27b27aec36565d38e2d29bcc96957bed26e32256da,
  0x61e38d78f1b785d8bb685b7bf5d93e7962eff5d93c4d26763177faef3ed6e345b7b5298e36c9914e35e3c6de53ed91684f538db363d52e36c9c4b424855e8e79,
  0xd4d508daf7884c2504ebbfd76b25ba974ea6b7c76bde38dea1e34df64f104eda105bcf687dec4978df98f409c6a29b71fc8a696619ec99b8f989a80c58a7ebb2,
  0x3bca2dc6fc256dc2c7e5951b53c627c62796dad52575b57f0d26e12deb49fc6de54149a8c1b77c78da255ae5af508e36aded8f4370b3dc78dbc6bceed290e1d8,
  0x3dd0d0ea2beaac9bafd2abf7838ced91fdace0a9b4889fb5972afdf6713e37e2a36f326b59365ef6f6a2a71b5154a9bf3c69a7169c6d93c35f60d3bcbb5f60d,
  0x62ac9bdf4c89fab5d8940f2ac4f05fb97d804e2d894e2046239a1a1d457d5896a5698d8c47343470afa94d19122339ef798ea2bef01a8cb661ee8687515f68f3,
  0xefdd401fbe1f70526d29913f76f66142b72f623c1fbe1f76f02c142b97623c1fbe1f70526f7d3227ef189a452d18817b1ffea2bea53465e7f51e7bdd38ea2bee,
  0xb9cda9bdeffcfdac3baa7ed666db4889fb72c5be22a04577be344fdeb16db5cce7b91c687f54fde24b7a221c697f3f7f7e231cf7238d2fe7e87dbd874742a1e5,
  0x26c67e1a6e9bdeff515f4ffa13633f0d3637bdeff515f40c8f2752a52b3a974afab68ffa133f227d5cef7fa8afbc325020841f398f6da3cad3dd0a7a8afac686,
  0x88ee59d4783f7c3ef11311fdd4dbdfdf54fd84d8f39b537bdfea2bef0c96960bf203e3ad35ed366bb775361363cc09569bdeff515f78cf3a60a1a20287b69ff4,
  0x787667592b420afd29a45808e15b5f0fa8c85ceb2542c15fa8c855cd8e8fd116f37dacac5b69fd441a2eed30beed2227eb578e33752bafdd4db4889fb99972ee,
  0x915fb2764a8b79bed656223fb59ccf4c8fed6733d3a12fdacb1a7d3a12fdc1531a7d323fa4656b3113123fb0a135888fef01a9c990aba1cdf780d58fe32bbcdf,
  0xccd0edd1d6d3fc7eda57d46ade76c45b1286ade45fa93ca7c8b6e572adebc725b831ab7e735ae916d243e4ca2d9c32e4d23fbc62991fde314f79be833249b7ea,
  0x22b2716f530fd986b2ac4e43de8188ae4353a8c6ca2d95adefc3e65b19901eeb9cb62b8ab7bf0f996cbc6573ea3ca16f214cac2e2b85bcc19b1286ade45fa871,
  0x1876a17ba069adafd982a7ac9eb78c3b50bdd03155bbd35c0425cc3d370ac2bba5dbc7c44ce77bdbc686b484bdeec4a1ab5578aecf756b12e40cb55aab9e6ad8,
  0x250cbbcc7aef777ade209e67f6241da89d9871385d76f637bf5bc05323e59f9ac8b09c176388cc537701ba6fd6bcccc8eb85cc7a59ee39b71952b932f75dd2ef,
  0x6b78c3b50b729ade7762f72cd35be9f185e57b9754d6a27f8ccd7ad5cc7b5bdbf5a3e6b1cc5de3335eb575d76d6f6fd6f1876a17bb935a222d1919186e735292,
  0x8f56cd9218fcef1466f3ea9ad0f8a31cbdbcb04f8a3379ad29ade114f35e28cde6b4a6b78b761b2db60e19a47aeee4d6db0573b1ad2f36c173cf7eb78a302dca,
  0xcf71f1bf15059eebb0f0a6d2d4defe6ab58f6963797be2deb91ab56272356ac5bb86ad7a869b1ab4fc8b770d5a1f608070a4d11eade28c0dcbdbc5260d2d3dd8,
  0x7d85a15568971646668e88802b5b263ddb71444f7b26e2d110e271db9ef4d71da4b4196e15297e720b01cfadcf7a6b892d2a57264aa2ea762c82d215dedeaad2,
  0x50bd9d6a28512d5c756a66e5e75bc053a3ade1414a8eb780a797ad6b1899a3adc2d475ad3c2d475bc33ec2d475bc413de50e55bc62dd72f5adf4e6d9435ef786,
  0x5ad12d65ceb64fb636bd4b34236756b938a77a7b2b5b27db06ca3a221c428ad3bd3da2ceb5fe12d6deceb696cd542299d6e4dca7c9a491eed5b14ceb46224a35,
  0x45b2ce4fdde1b07b42f23bf588df91c6d8490abdad8a6d6c74ea5e01d4b7952596c9f14f7826de876dee33bd466a2ed1d6d51d6d65ceb788da4fb60d94744401,
  0xde18ce0a166a564187f735e035727eef0d83da1791dfac46d7e2cb9f770d7416236bf677189c35d6c46f5680c5f574ff939dc6270e524b4ff93978c13872925a,
  0x28c734b02c25a0897975fac46fc524b9e3ea52ca3386f31f4f491f4243444afa21df90eb217d96255b78a31cfafc544b47be7495d7eb11a22682f573eea03090,
  0x3ffae5a3660b3cc0a95137270de6bce92ba0b1ff7d8b15b36bbcbb505a9699ed2f07c2c46f172d4d227b1d9d7d87c4bfde28c86db8a2253437eb969f919eb2de,
  0xc7e74958eb02373ced50ae128dbd9f7878eb03fe979bb31d72d86c5e6ecc75cb73e3c6d8673e3c6d93ad893b8db0d8bcdd9ffd72dbc726e32546d734b02d0cbb,
  0x98832fc91df05025a912e6b74ce9e778ce026d2f07c096cd81aa674d152e78f514734958e13b0d8bca539f1a96c362c4ef8946def9d243eb02361b16252251bc,
  0xd7e25bc44db15288692c8da2f9d7daebf12d4a7ca7d38ce4e759d257d17de7761794a73fea5bd5ad94a444af3017f7864b8f84cefad8e020bcf2e805fde59f3d,
  0x8753a258e02fec362f294e62a5bcebcd2e6be9d15449e1bf12d3f5c62596f3af34b7d97d31b44f57daebf12d6afc89707a92bf5b7889b62a51ac591b45f3afb5,
  0xd8bcdd98a96e7ce09e7262bd9f44b1c05fde799db99427f6270dee02fed390261bc95fd85bcf3de5272e841bfbc3b3e348968753c92b1c05fd4a7c3b3e34896,
  0x7a98b46374ba822fec93ec4a4e5c2aff50d75326655b79e27cbb52b245f5cb15c8c2e8422fe88599aee38657a9218e046899e7f20416f714fde51da13ac922fb,
  0x1ffc7a5ef11b0a0a67e807fee84747ccafe65b4fb5ec49694ed3ed7b1296f7f4529e9b125f0d3a294f4d892f87434fc7e6396ea67a9ee125f0e86979bb3152da,
  0x2220954b8111d3f3156a91f70938e25ab3f5000247d3d00f630fd0f70f17a8a53d362552f4bd1c5264eeeea3896ddce09ee94f4d8954bd0fd78711b014a7a7a0,
  0x7a524bfc75afed1d1a69305244cbc758ffa294f4d81b88e36e514a7a6c497c31b79dd9735405a1cbe8bef02fd7257c30fed29e9b129751fa5e730e25a7e62ad5,
  0x55fa57a94a62674cb5dfaafd2bdcebbf5d338bf32d2f39854b6e362ad69ee1d475afe8a53d3624b03ad7f41b3dba35529102f1eb5fdc983d31fb646d9357614a,
  0x9a26d617a5cb58bbfd7635ba6dac2fc2e5bc7250678a5a9945ba79ae616bf0b15e94dcc4c1eebfcf5328b74d135e616bf0b15ef3ff75a5df58aea1ddb87742f,
  0x5ba6dae6a5cb5fe0daa89e08b1cec9f6c4542f6c6b74c16de6a5cb515e4cd4dbf543f3d2bc6fdf1b1bd2f5ff1eb0fe8d9555b79ea659b10ecf875ff1eb0fec6b,
  0xb09677826a267b1877e7826bee03571bec6a5e42d0f5ae5b47ba0fca4d93413721618fea7a5077d622b96c993e4a6b1233248572d936ec067aec9b7eaa1fd763,
  0xa1a5cb73332774efd99ede9497f63584f760b434b96c6b09fb5b05a1a5cb6e9392f34cebec43fb9b337276898cb9fa1543e9f5143ef6067dc06af2968cdeced4,
  0x30ccd7d8e5db5c1471c497f53c853ac97aafc64d2a98640bd5ed985d18a7bd80ae95fd48182f5226213a7bdbf15fd3eec5a6452d84ee6a80b4d8821fd8d4bc85,
  0x972de035b843cb58255028996b4e71a2a76badd7e388db1a979cd4b96c6a5e42ee972d4502617fb66174629178ae911fbcca617fb660468c53c582ba57f43eb9,
  0x963585bcc7f5d9566e5ad0d936fd54349deabd42f6f126b96fb5ed23fc877f42e763b5a5dff0217f73cd19f68672fcafef01dbabb7bf5d44f976ac6237d2f39a,
  0xfa14f417f6b716ca65bdfd065354265157533aff7bfbc49ae75df90d4287b0c57b27db116ff5d937253bd83e435f0b8e3211fb9d8bce64cb73b179cc95fd4a64,
  0x225b0b74e5949cb7237f72e74c70c45b2d3bae78682fe979cdc396a287df19fbdd55f8f194b5140be7d819f767c78ca5a5e6174cb6f197985d32d1a8d3227151,
  0x1b30d7f79d059b93ba27b29b9cae80ff7bf9f1b30d7f671ac59bf10bfb8f82748b42e5dad2a2fa5e73265a8b9b79435f4dd3f1fc44b515e85f1f107de9bcf8fe,
  0x76fedb71b63d49eaa044b6db878a1ea4f550225a3d8f72cad46f531c800f7a7ebaa7585fd01f0137ab32a17e218a1ebdfde346679b93ba27b29b9cae80fdef9f,
  0x8c07ef7cfdf00c7fdf5c492a5611668efb3ad473b6dcb19acc044b6db963349ca044b6db8db1ea4e50225bc8cee04d375b7defee5d39ac2fec284d27e55daf74,
  0x29bab49a7cdd953c6ff5de24b3df3e9ee4ee3154d2a69b72218afb03e7ef806bfbc8964ca14b0c8d46269f2a6b0cec9f410914f40b992d4cf3727744d34a9b9c,
  0xacdc652db6e58cd42fc652db68f2fea85f8ca5b9352fcf7d57a8a9e624fc75ad7f6db9458542fc652de71629bab49a7cdd953c6ff5dcc7fb05366f7bfd753062,
  0xfab9b37c8d8627def7f3d78fd4a57b7ed4f504bbcd341bfc56bfab15295edf55ea09444d050fe2b5fde24b0739b93a9475bdf56934129d9d07fd616bfb6dcb19,
  0x35405a7bee39fdcd78e96cfc9effc97f78c5b81349cbe1eebfa7dcdc575f52c95ede1c6fb6dcb19acc252dba71ac49cbf8ad7f4fd6cf664b33bcd3448f25fdb8,
  0xbb708d5557864d41920ea92fef1259534dc6f51b984eebb7bdf93ec3685b2f2a65532b57309ee973c27de43cc33992d82d93a9ae6bc74b7a796604a5bc5c62d7,
  0x894b63ca72cada1796e844a5a8b8876e236adbc6279f2b432aa70b7ba925b75c7e9d23cd064f113c97f7e3bae3969b1f272f192fe80a90fb62f31d033c2c0dfe,
  0xfb094d33f25fd4c2e6bb517476f6252d4c2e6bb5175496f6252d78565a42b4a9de7d064f901bfe4bfaf0acb49b55a54aa74193e4050ff25fd8f29caa9c2f2dd0,
  0x25fdce88ab379af927e382f3dafee74451ae79882adb5fde09ad661296f04d68e784a5bcd767a8e784a5b9af1957f2f3ddde4bfb998b7d4b7daf695d7934efec,
  0xa5eaddb24eac705fda4e5fe4bfad38494d194e5fe4bfad385cbb5b9e45f7954d49cbfc97f4e867d84a699f92fe85451ae4d4df1bd792fe8544fe63c9a9be37af,
  0xb59b449860f000de5a08bfb49104497f7892dcf137b37b70c0f03bbdbe1afe83f7b5f25efe9db39cf89381ebdfdaac7c15359006c0c9e3b382fee7548ab00554,
  0x7f735ade82131ee639acc2650891654e3f1feea54a05fb5984a5b38f976b0b6237dde78dd9e9e54e04a5b85b2df6bf2a7e2077f78476129f630ed272892febca,
  0xceb712fde198a108eb5fde74105454b931d0a1083f5afef3c4f4c91fc2a3fa2839d566538087d3fdd2f6bf54f75afee6679d661329db35b8fc7fba5f4faa7b8,
  0xbbffad7f79e279d8ae6755afed5c6b166e3d6bfb473984e9abc7ad7f4fc0595375c5473fe1526b2feef3c6fd59a96bfa04c4acb84abee3d6bfae6ab16a0b0a4,
  0xf78af338fd87505d241f0b5fd121715ddc6d934bf1ff708333d44fdbd994167fd6bfa89fb7b32855dffd6bfbcad949eb9bfeb5fdcb7131650bd56bfa3276a4f5,
  0x71fb0ea0b0bc2d7f7898a9465f97f4b3fff5cb6da71fb0ea0b383e16bfbd5b66d69427354e1793dc2c46f3a6a38da8b6c462569a60bda612124ee368821217f8,
  0x7c01f642fd8f21472af72c231a65200e2e30823f4628f2145ceb9aac024cd6c37c1654117f5cd5601266cc0c6f3ad40bf78dfab352d7f7864a546d4dc1d4b6da,
  0x759d1c2ad7f56513da65b09b2cacf62271fb59628151888b9ed7775ef2b611bde48656d7b04c992042e30823f789355a465bee584c99200e2e30823f79c59329,
  0xec0f7fc800fa98c75b64799cbc91b37782c2faf400fb54349defd964f4c1b7ec99a187defdb23ca9ddc146dfb7b9616bfcc7d4cf23c7b2578cc34fbe1f4b66ce,
  0xfbcb530af6c881eff9001f7826bcfb5e2bb5034ecd9b4fb7ae9e2a6f39b6209b0181f796a79b7973f66f6f1f11315a65cca869e1c83e9c59f61c55ef2d4e859,
  0xaf3b6048d22fed54b6bd14a7a01417fa8fde514c529981425d47ee65424ec8cbe80557e3d7ea6650b64add5407afde10649e26bea069d05b84f82bdec0f7fc80,
  0xf3c55bcad816133f0fd1b33f4b6786742aaa72e80523f1f4b677ecc645f66dc4ccaecaef79f19cdb3ad8b06de8829cb33f6e4114df2307b1aec5e4cc12322fb1,
  0xc17efb25fc02605fac6ded59ac73bb166577756dcdb3a59b56b6afd0ad60bf5a65696b4b5b6cbf34de7af726d254a66b3a308a4ade43cd665770ab7967c4694e,
  0xd491f7b70e1fea3f696f191967c94691a41f4b6265aa9cc01f796a79b95ad6007f2003edd4cb294d36405a6c7afc3dfd4cc98352b55b5803f97938fd4817a15a,
  0xad57947e3eaeb0e4ce6ddb1d59720fc7d93ad88b9dc161527a8e320fc7de5dae6d964b2b6f7eda5339804512b3c3fadefdb4a673008a256a48feb4ed9ea4659a,
  0xbdac06301fac7d7333a54c8651cb586305e8d99fb8f3a1555cc31b120fc7d635a5fd4b98e8651cb5d60bde73cf2cf80930cdfdcb7d96b9ecc743284f65e96c4c,
  0xf3d7bf172c990469dec4f9a186fc7ecd98f8e64a967d9484387c603f48def21dbcd6e76484cacce9388611f4b6265ab9401f4b6265ab947e3ef10ec94e70b646,
  0x1e5ab9401f753721e5ab9401f5fe69bfcf51a4a9c1ed8da687e3ec9abcf16f26b663a49d7bc4262ca622bc16894ade4ec6691b4d0fc7d7f6607404996d6d4909,
  0xac4c0f97951247eecac5439e7b36c894cc49060bdca00fbb7801f4a8588ea11bc8a4a4803e87d47486c5699b1fe2ff353d220c75c86fc7ee92a40b32bc48bef2,
  0x7b285bd953ba6bad5508f5f785d82565db5eeab811bfb946fe85ca37f53f359be22bd1465e360501fe411fb58409fd57a0627e53439eccf6537c4295d01fa9f9,
  0x8a06e1ed9c5cce924e3c508dc7ec27c627a67f53aaf78aedce2c009edfd4adb4b6481701ae6103aaeabdbbe470287ebfbc06a3142dc27c1c2792b8fafb2f55d5,
  0x5f43eacf361563450a14838143f1f780d4626384f8820a143d7d666194597791c0a007d6acd81f756ef91c0a007d6acd8e5b5eaddf2381400fb47248ded5ad5f,
  0xb54345e894fb1876d8a8ec3a143ef766b29adb0724a8c113dd2ec7ca112f7b0d7bcc964d62a92a3062a2e595cbdee4dc82105581d5755efcd64318b77c8e050f,
  0x87f7714eac9ddfa4325eece9856325eeccd97296fceccd9726d65b666cb956f28a7b20cc9a8cbdc658e4d2d0ea51ab78c5be2db35457d7bc2a63bdd55f8ac43f
]
def gemBitBlock7 : Array Nat := #[
  0x636a54d2d75b1b174a4df5ebfd2ea29fdd50f65785612917e3437e3f5fe956a3b35b3ddca40d3f12917e35271fb7d50b74fc5621fd1bc74158c97a77baabf158,
  0x1c87ea267012688e959ca2fc68390fdcd5339d033b9361c8465f655b2e5b6afc72bb5ec0db12917e341af8fd1956a3b2a766b74e5224b1fd5009f8f0bdf1fa25,
  0xf1a0e43f5133ab24655ca2fc68390fd44cec151195728bf1a0e43f58b98b2e52f51dfdcbf2e2b158fbc5b4f116a3313edea4c292258fa899c049a232ae517e34,
  0xb591989c2d2ab4b8408e37e3f466270b4c89aab87f1a0ffe3f428190cea81d3b13ed320948bf1eb1bf1fa06cdb0c7efccb132aaa0b97bd8c87ea26ff1195728b,
  0x6759eeb55483f7abbcde9ecca869bb8fb9307c8860c65d7bbe316a5920a64cdae3ebdcc4e16955a5c20471bf1fa98d5d91f112e7e6919e44292055684b8c871f,
  0x1aea7a93d2aa1bf1fa9df854327da37f1c334f7d788e38638fd69fb857fd630fde33cdd46327dcb393a6c232ebdac25b857ffa8fdc98b37c8a4aabd3a604257f,
  0x55a6c6903af42bafb9dbaaab2ae03a1fbc6d8ab21f85ac71fae4e9b08cbaf4417a6ab21f85ac71fbd5e2aa58623f50b55755e9640b986bb73548b69c639f457f,
  0xbea715701d0fde43cef86a7f37dd7478c5b4c34972ac87e03a1fac61ddc802a84022a4fcb5d7303f6e067b910692e5590fff5c80fd094b4c4aa93af762ee775b,
  0xf52bb8115d7d4c9b7156984ceee04575f7aaab2aa0e87ef555655c0743f464a62bfeb187ef555643f01d0fd1baaab21f80e87ee98692e5590fc0743f64ec946,
  0xbabc43f01d0fd4c29aab69a7372612eea0ebea64d956b2ef6530974ae17203f780f34620d21df887ffae407ec334c8b4dd2d287a95dc08aebec334c8b4dd15a5,
  0xbb81190fbca3ebae4c92aaeabde236128137fa96a069d10d99ae1630fd63723d2d74bde56c713e1a9b1d52d74bdeaf1550743f7abc55c0743f7abc43f01d0fd1,
  0x68992de8cccd7fc3a1fa2523cc9eaf4a46a111bee3ee7feb8af55d5755ef57678110c7e9d75df9c2b03ff58c3f52983b2ddd5ef0cba1190fbdfa19d7333cc173,
  0x9e5b86a808c9f7e2e65299d2b858c3f5623f3c77b37e93eb7be20a279d203c2e5f8fda5a99fc7ba421a01907ef18edf18539e73d39d480f0b97e3f5c4dfeca1,
  0x23c9c7eeec7654a6554361e97e35271fa9e61954b5d2f46666b80e87ec99d4e3c882899fdb35ec571d47eac47e78e095aeeeadef88289e7480f0b97e3f762a67,
  0x4c605305aa5887f7954d9b8588db38c57fc390fd666a83a5ef09f7071f1575ad74bdae16ba11d86552d74bd10b5c2c611d666a83a1fb968ceca948ff4a7ef080,
  0x5cfd996a5770b10feb6b752eacc771faa575483fbc609b3bc809034ab63637b7e23c440fd8494caeedbd2ea4eb521afac61dcb230cc8c2a7d299d70b1103f613,
  0x57fc8a9859e5a1154301fa304ca2140bb15c751fb082e5033903330bf737c52a88502ec571d47e8dd5e21ffeb48fd6d6e855a8fdd9816a55d6a41fd026d6e2cf,
  0xb10fef2ed48cb35aabaaf72ac7a0e4bdacedce54a7541c97a751b1ed24778c56325ea7aac7a0e4bd7f86292e5ba6158c97a37578ab85a47e8dd5e21f85a47eac,
  0xaaf5c2483f1a0e43f73b3335c2d23f5c8f41c97b44d6aa0e4bd666bfeb48fdba149c979a575fb10fef189aa70b85887f6e2cf54c4cf4bbec43fb4ba4e4bcd2ef,
  0xfd84eb202d36f4843facc832e57b1541c87ee5b6b65afd9bade7765dec49cba55751faccd70b48fdf61dd224891e750e1f8f01af8fd3999ae1691fa74f70cd5c,
  0xfd06517725c22f74d8c3f599aa5a47ef3bb1195ca436f3989195ac5169163a1b7a7d51cf7abc554b48fd5ec50e1c87ec9abc89726b663a06bebdafcbd8a1c390,
  0x965c7822a18ac46deaf155755ef28b7578aabaaf599aaea3f599ae3a8fdc82f4bb81110fea5315c751fbd5e2aaea3f7abc55c751fbd5e21f8ea3f7abf207e3a8,
  0x43f7887e16243f64f2983294fccf70397ba01148fdcce21f85890fde1d9c73254676d50801ba53ee5ee817407ef10fff0e43f78633c43ffc390fd666abaaf4e9,
  0x90fd3fe7fb3166b0083deaa87f1e6b9a1b5187c50721fbc5541c87ef1552c487ecd9a6ca912ea6e8990703f51fb7fc0490be9bdd2c2f2ade2ae0390fde21f80e,
  0xe5a7b5c25cb3b7fbc1f5fe2b158fb461f1c0721fa058f8eac9c04b55ef45701c87e8ae16243f68f63aeba8fdcb0e385890fd552a88502d08ae3a8fd844638e03,
  0xe3feb48fde18caa655294d4abf5d50f1dfdf91c0a017f6a8390fdaa5890fd22c726779804a28954bdf5ed701c87ef39e42cba43fbc70b121fbb3c701c87ef01a,
  0x54ede591695efaf8ffc7e8153dc4f50ae5ec6992b8ffd7ae27c73230af638ffad23f4a6a5c232f7c78143d7dd9f609425363b15ec703ad23f4ff919cd10852d8,
  0x92b88ad933c5917b1ffffae80fd5a952bd8ce8522d2bdf5f11c7edb53dd4a91e5234c95c475e8c2bd8ffffd691fbb2ff0c4e69583adf6457fd75f8fdf622bdd2,
  0x1ef30a95eeb88e3f779807b3728bac95bcc9ac2906f8ffffe23c77f645ec7fffeb48fde789e5e2917b1c7fd691fbcf13e70e291695efaf881f56af75c165ec69,
  0x8affad23f79c6cbd8affaf623f516c0fff5a47ecd8fe172279d6e22b7617603d9b546f5a72648c0788d10d52c0ad9b2e52d45b1ffffad23f76726cc5295b9312,
  0x9915ec0fff5a47ea67b115ea153bd6622f7d75f88f1ff8fdd8b53567640857b15ff5a47ef172b2df1a1437f762d4d59d9fdaa2bd8affad23f762e026b69c62bd,
  0x44d695faebe207dac54cae52b97746fe5ec57fd7407e967ef254a919d484bdf5d7e23c7fe3f64ca0b6169766d51bd68af607ffad23f64ca0b747766e517592b5,
  0xae45271ff5d7e3f4e066e2390c354b09dd81ffeb48fd86226283ffd7407ed1c29c691abafdacec8108d8affad23f57b03ffd691fbcc3b2f607ffad23f7867c70,
  0x5ea6d149c52ebf1faff1d5969696d4e7221ba887faf79e27978910d5b8a779e2738f324907fffeb48fd3a74ebd5bbf3afa864907fc75d01fba6bfe7afbab9a37,
  0xa8a4904ee9a4eb2d03ffd691faa981972a72a714ec9201ffeb48fd2a1cdc054237914949038fd9241ffffad23f4ecb5c61b569c44527fe9691fa99285997242a,
  0xde67ab3fb917b15c2ebf1fbc3b16b360cc8a752440f253eb35ec570ba03f787671cce602a4857929f72e84570ba03f72d3a89475b34c8bd8ae24e3f4ff919a52,
  0x23703c687ef84f2f13bc2b4af31bfb4a02a2f4f38615a46e1637d0b940df05e855695ef637d5d5482bd03f0b48fd0a9ca857c53b2d81f85a47ef329810b894e2,
  0xc15edec349ce4a9c30ac07ff1e4e3f42efe513c17b0d48b44ea2227cca796a8c31ea4ebd0b942e453224af7b1beb569b1b1857b11bf11e238fdbe85f2f7fbdc9,
  0x91fa8b824558dd5ceba4aee40574ff8ebdf1fbe13cbc4385695eeb8efed295daae79b6b6c594112577203063d49c7ef28fab03aaeabd464615d07ffad23f44d4,
  0x2cce5af13d3637f88c80fd0b2f4237dae16188fd1f85a47e8de465b5f115b2a0fff5a47e8d2a0fff5a47e8c2ba0fff5a47e8c2ba7fffeb48fd3b518574ffffd6,
  0xfb952f74daffe3f47fff51fbc412cd81f04e65730eaa4ebdf944f05ec350f5d4cd897096bee1f4df1dfe23203f763fffa8fde026d8fffea3f55385c088df5306,
  0xffc7eb1877722b07a2bff03513f72a5ee9b5ffc7e863f1d47ec3031f8ea3f77bb6612ea6c40c3aa58c3f5108fc751fb0a71a46a193eb1877722b07a2bff0abc3,
  0x1d47ed2f0f65ceb7748456bfc7525312328ca544aa0ffebd38b2f561562ef2b62e83f1d47ec9f996d78db2d98e9275eb18777236523d151c0d44fdca97ba0115,
  0x4ae1691fb22e95c2d23f56a561319dcac8b4af7d7c471fb0b8a8177c77f888a1fb7d22e95c2d23f41b5f48ba570b48fdcb74a6e15ef8f02b8d0fdae17b11fa3f,
  0x4570b48fdc991689b857be3c003c687ea67ac3337324c97c2c6fbc55c2d23f5152b85a47e8c2199e648dc2c6fa5b37479d019ab2956f30d5cf54ec993637d1a5,
  0xaf7889857b15ff5a47e8362a2bd8affad23f72645a1515ef8fe200f1a1fac545cb9533db291a57e40788e3f7889857422bfeb48fd551b38b6f3cf31db66f52e8,
  0xf8fd54d6a572ed8fbd484bdf1bf11e238fdea985612f62bfeb48fd8598244a62a6bd8affad23f50d753662cd6012e4d15d2b85a47e8ae95ff5a47eec5d5606ba,
  0x37e3f7ae9a12e95ff5a47eaf62bfeb48fd025ec57fd691fbcad8bd8affad23f617151ef8eff11143f6719584bd8affad23f56a8cfcc9b031c32c87097b00475e,
  0x3aa53622ce39691022b881f612e95ff5a47e83684ba57fd691fb9e98fcc621d9e5ab97bf54cf82b4b974023aebf1fb9e996aaa8b99b7b2d019b951d37061fe34,
  0x95ff5a47eae95c2d23f795b174ae1691fb257e5d2b85a47ede339feca15335b753660bd619e8556992e9637dcc0365bd0aad2baaebf574affad23f5551013a36,
  0x4388fac333f54f4897d7c2c31fbce2c705ca06cb67ba39ae161af695c2d23f6b25945cc40815f115bc3c5a57fd691fb2a57fd691fab2c844f3eabe22b7ae9a96,
  0x658dd7ffa8fd13332fa6c6ff11187ef04d7ae59617d2ee04643ee6dfd9398bb5c2d23f514eacb4dbd982ee916f97faf79e275ff5a47e8dcf335ff5a47eec9d31,
  0xeec2ef6f15ea1fd9df8fb5ffea3f79e275ffea3f79c58ed5fea5a8b5a7795b1157ffa8fddc52a8abffd47ee66c8afff51fab16ebffd47ed2d3d973addd2115b3,
  0x80fd1a52dae3a8fde789d71d47efc5e789d71d47ef0f1695c751fbcb53cdbac85fbd9306bb0bbda6b2b9fbe1c87f1f6ea950c9f64c1aec2ef69acb707f7d17e3,
  0x115a76b2221e9691fbb274c564e2f1bdd2f12f78e64e9a7912fdd2955687eec9d30d5f9cc21de9b11695e51fa76b2221c75a47ec8ba0e3ad23f6e31857b143ae,
  0x7aea3f7755d47eec7aea3f43dd5751fa1ec7aea3f6a9691fa8aa9691fa89a2aa5a47ef1130a2aa5a47e8f4b48fdca92cb97b6366491e22b64eb677e841447a5f,
  0xfc478803bc85302746d512d91483623c7fad58ab89057b541c97a3d0725eec7a0e4bd1fac392f7976bb3b1e8392f6aba8fd1eba8fd4555d47ea21eba8fd2a88,
  0xc755ea649b0ebffd57bcc269331afff55ec8887e3aaf64443fffaaf78af3c6820bc407e23c401d1ae2415eec7e3aaf6fb63f1d57b7db1fffd57b26d04fe0bf20,
  0xaf46dd71d57bc2ed994a4614b3875b6aa415ed7120af47aeabde21ebaaf441156a88f42441f11e8478803bb1ebaaf6fb63d755e8fc755eee10511e97c456f10f,
  0x6b15ef3b65f565dee9fc856bfb2e7792f6abaaf6a9632f53b73ff260007ad7c401dae3aaf6b2569b788c7721a1d6056ad6b8eabdccad5c755ef1571d57bbae3a,
  0x1724edaf79f19eaf1bdd28dfa1a45fe03000fd103cb1afcc50af4b220bec0ff42bd84eb3b9276c7ee79a165fcc6c7ed39105f31423f7876539105f31423f7ec0,
  0x57bb12102bd97d8950af73e3b5ecbec2fd0af79c132c9c95e604088dfd97d81fe857b0ca313aae46c5fcc50af78e33943f9e368a37e861ebf80fffc0fd667e6e,
  0xfdd89057bb0230af535877daf7407f1109de4935db232fa96fac0fe321b7924d7084f2fa96f863f8c86dd81142bdcbd6171b4efaf0c42c7afb98f25efd890,
  0xcdaea72366ccf98ae3f5b57f2272a23f98ae3f5b52b991354fe62b8fda5c2df31b5ec9e4b6ed0984ed287b6c53a445f3000fd2cc2759b9e76c7ed5db629545f3,
  0x63f4609d93fd50d8fd865121889984fee8575e892e76d7b27e679ffb7cedaf63cafe636bd5adc9acb9bbf75ec3283ad67f3a36d44e3f68e892c09dd195f6cfd6,
  0xe7b2d13247c417a76b705eb4e653fd7aaa76b96db8c4eb447fb7feff1000fd11334bbff7f88007e89462d2effdfe2001fa2518a565bff7f88007efb37feff101,
  0xde46949d7a92a243324fdf007e3f7f03f11b1fa9d83fc57115c7efaa6175d39495a14099e6035b09c7ea764acbd3ddfe07e2363f671b55c8d96cf35084fea3f6,
  0xb1fa54429befac571fa59f65d344bd2a243324fdf581f8fde07e2363f4690c1ece3ccdd18e96d4f9a9153f1fa246a3f7f88d8fd4951219927ef815c7ea668215,
  0x180fd0bed9ed15d4ee7af589483ef0008daf4ed6e7b2d1192cebd3a659a62cb9e372aebde13e6395d973674e2e993af787670008daf440c4f1afdd0aebde0011,
  0x166a94ccd4373d42e79731b1fb9aa5324841b944f3cd2147ee6422b2df1dfeb1c0fda51dd4ee65be3bfc603f42cafb3cb753b9ebc39483ed0445753b996f8eff,
  0x980fd2be7cb881bf1fba62b2a0004003f58e17905d4e93baf0c40dc7dd31596d6001000fdb66324d33fb31b5eb1926996a90abd4c95cdf1a539d0f51dd0007e8,
  0x6e3e9554e5d63275ee616980fe64881f8c07e81857790fca4ebdcc2d301fcdbe3f8fc603f53945a603f9b7c7f1f8c07e88ba7ad991f14f1bf1fa4942df712ea9,
  0x51d78ff5c40fc7ec9bc64445766e7af1fbe37e3f6199e648800658fda3ccb2bf1b9c0ee18845f69613a5a0004003f4414b05991a648bec9b8ccb30b4bb3234c8,
  0xc75999a60b6f88d881f8fdcd465e5275eecd2f16fd2f4c2cccaa77c457103f1fbb34bc5bf4bd33352a25be22b881f8fd2d8144b991a648be916dece0a8d6b9a9,
  0xd042aa9fb75ee58611b115c7ef15e6db8a32f852c773a12284f103f1fbce2da6cc21de9ba264a12ea3f7947d581e636bdbb37321839495b4a4650002363f4417,
  0x1bd6e6a35d96da42e68b2f21bf5eaa6019f5d2169d165e437ebd54ce23eadd596e9ca4ebd0a59fb7aea77288390deb7994c002363f4a899e6036648cf71fa17a,
  0xa57a80008007ef09f15450dcd3b9ebe5e437e3f51422bd78eff58e07e888aecdcf5e29e37e3f7994c00236bd3a635d96da42e68b2f21bf5eac5f6f5d4ee51072,
  0xe4371f6b0004003f56b936ca2eee3455b7809914e2f5111b115c7ef50001000fd59dc2ec69e6bd788d881f8fde10622b4c7373d788d8df8fd2bd40004003f58,
  0xcdca20e437ad0008d8fde1416647c3922fa001000fdddb79e236207e3f78db297323e1c917d93926dd8345e236207e3f64dc66f82d2ecc8f8721b8fa8ae0311f,
  0xe8622a752c975bc319ccbdd295ea91021d7d0008daf4b2d9a759ea2236b03af735cd7945b34511b9388ee92f09f221de61ae6b9af28b668b2f21bf11de0267ae,
  0x9ff8e28dc400064207ec26b86767ae5801b192f8fde7c658a546e291021d7dcd21646000032103f73494bb1060910321fc7e96389e662ec4f910321e3e954ed5,
  0x514b4190febd93304c4bd5c8c000064207eb4f989929c2036045721fa04b4cafcaeccff386c088c3f79f1990072546091022b1fc7ef15d8e28dc400064207eaf,
  0x6fd9a67751b023203f5a7c23ea51b02230fd2a9dabd0c454ea510faf4b17c5262ca51b02230fd12f573d7f004b881fae270b86731c83000019081fbcb3e39271,
  0x1910bab9ea00032103f7d3e141500837573d5220643f8fde026ac106cc40c97c7ef16a6c15646bab6897ab9ebf802400fde3997f88c1504618cbf5e850773c4c,
  0x2122043fc7ef224d9a8000032103f78b8988092980064207ef1713151a7add310321fc7ef573d7f004801fbc5c04d0cf5d46c088c3f7ab9ebf8025c40fdf4f9f,
  0x9003f78b912654f8025c40fd12f523fc012007ef3e3225ea47f802400fde02612f523fc012007ef17013097a91fe009003f513de7f004b881fbe9e6a5b3668b,
  0x8a79a2f004b881fbd48ff004801fa57050b3af474fe41c56a4be3f7817eea47f802400fdf4f8662de7f004b881fbe9f0bb13d58a1220643f8fde2e114fa91fe0,
  0xb4bb3b648dc7df4f35cec9976746280810ff1fbc732ff1182a08c30ff5ef17398be48ff004801fb75b57e12698e45e76d7bc5cf13a31b373d7fd815fe07ef170,
  0xb218dd7a59ce621b3cce2043fc7ef3af247f802400fd6afa232bdc85a879b90a9f4ba9985ec310d449a639179db5efa6362ae60cd2f7846f990cbd7d936ec480,
  0x66f4f9ee10e3bddf4bf7bf03f64e8b7e0097103f78b8525fc012007ef3cfbe3973bd2f78b9e2747bcf51b023203f78b8525fc012e207e91fe009003f409c362b,
  0xf8a8b25019890f77b6f0d13b114bcfd7190f1f79662451a55b6d93374c6ebdfc012d8fdfc012007ef38a74e5440c83f409f3b67cd430ff5ec9d16fc012007ed0,
  0x7ef189c8a966a1008a93f2d75a1901fa8bc012f21fb090b5df1426501b2120e234fdfd8ff4bcf8fc643f8fdf8b594066243ddedbc34dfd8ff4bcf8fc643f8fd,
  0x500a244fdfb9625fd70bfc0fde241394ce50b5fd3115f79d13f74bfc0fde799056d8eadf0a244fdfb9625fd70bfc0fde3992b6c756f85030a7efdcb12feb85fe,
  0xf5178025b1fbcca7b464ea50913f7f2803fd7e2bf43f78e64ae50a9aadb912253ee5ddc0af81fb98e72b900fdceaa05644fdfb9625f7c2ff03f6b395c807ee75,
  0xdcbceb815f03f7e3973bd2f78025e43f492ddf1426501b2120e7b672787f63fd2f3e3f190fe3f7e2d6500990f77b61407f63fa73e3f190fe3f4ed5fd4f984a43,
  0xedb31820ab033bc97bcfb5e2932c4772a887a1d2df581fc6435f614e3df0c40f5fbc73e848851ef863f8c83fbd5cd4040c83f78025b1fbc73257313554a244a7
]
def gemBitBlock8 : Array Nat := #[
  0x1f15d9908dd7bca0c2a2968321fd7bf346b00097103f7e68d63f025c40fdcb584a1c86fd7b461141c886818febdf93af963f025c40fde7317c9d7cb1f812e207,
  0x346b0009003f79cc5f346b0009003f66c93229af40025c40fde2554cd913d24e1f3c5d46c08607e918004b881fb75480f5fb4638fe00c840fd2ac74190febde5,
  0x7ef38ed4be17504cca93b2a7d7fb901a43ebf11fc40fde34166f2a919f2a48e9ba7dac487d703fc87e95d99087faf6718004801fbc282a3de7af1d811901fbf,
  0xa7cf3ca227ef9c2b48f4affff8fd4c73c8c0a989fba7dac487d52ff03f4012e207ec2ea874cd235483f764012e207ed656e859acdd24112e4035d6d187f812e2,
  0x474af7a09d3227ef9c8877f8aff03f71f665c60054c7bd32a644fdf385691f5f8aff03f71f665c60054c7bd32a644fdf3856243ebf15fe07ee163a636ab9a5e,
  0xb1f3a2f7945bab987df90c87e9673989cfa7f23d090c87eec3e176f6acd425d47e8025b5e802402f704b1422375ee6bce62852ada0096c7e802400fdc7d981b0,
  0x48815f1fad31d3669495900ff774b7ff48d07ee5f94a58e4d9cc2e5eabddcc83e745e8c51e57f3a2f72fca52c726ce6172f55eee641f3e95e95e24a6729f674a,
  0xbafff8034207efa636389dc77da575d7ffc01d81fa25469099841b9ea33de670f9d07edd3554c12894959dea8375ffa440af8fdba6aa1f7de74959deba46ebff,
  0x67cb9ea00034207ef2833e4e1ba8000d081fb74d542815dfe7e98dd78622423f8fd0f85dbab9a84ba8fd2d847be1cab6d1ee97245f47e28a48643f79418abce1,
  0xd081fbcbb5232cfccab6fa7f200034207ef28b7a7f200034207e9c2eba6b190afaf6718dff2190fde7898bb7615d6f28b4e309f2190fdf973d40006840fde50,
  0x7bccb691fe43ff1fb74cb651fcd506ea28207fe3f46972d2fdfde5a1abfff691ba8a0eff1fb74cb651ef32d84f90ffc7e8000d081fbca0c2bb3290afaf671800,
  0x548c859915242ec748f901fbca0cde65b007e1f03f79419f270dd40007607ebc59495b8242f12f54885edd6d2bdf5fe9bfc7edc04eb4b6dd1c0b7ebdf4f85054,
  0xfeaad47e9ecf7cffd235c0fd6aa47cc26aa26c799d583fe941fbc627a619d2a42af7947de9fc800751fbd5cc37fc831fb5be13e1b79ade5067a63750001d81fa,
  0x7607edd4b108beb1b69286afcbdb4ee891b3da7e47a03e407eb57e730877a6e8990748f187efa7f200fc7607ee5cc9cc6c7ad840bba3ab07fd13d7b6c94b9a06,
  0x4bfd7a859624e60aa64a5d7b38c0007607ec9e260feddd406cfc36b5ffd7ac7c673490ffd7ab5f4e3594a4d4ce6ae339a487febde26b6d75f5252ebdf4fe4000,
  0xf72dc158c6a3db320374f4a7d8fc31fbc732335629185a6cec477b1a8e9b34a68540feba47d56fbe2057c7ec6a298599a5342a07f5c50eeb7df102be3f4ab1d2,
  0x7e87cc194f9b6321fbc7336cb0b98a485bab87fef72a7ae3f1103f7640034207ef19e61273aaca0d8add2ef4ae9952e9f7c408fe3f42cbec43fbd767f0078103,
  0x5c77f5aa05ca7d9d287f3a2f6136b978a7673a7d84efd28e07fb1bdca9e9543f40034207ef1cc91d161d5402dd54f4356f5c711103f4003c081fbc579000f020,
  0xf521339777c8ba8fb1bcc4f9d50fdaca6016d7c3662125e4fdffbd8ae9eb8fc781fb088ce29d9ce9f613bf4a381fec6f724ff4aa1fbcc357325b0513bc2b4af7,
  0xcc529b4bc9fbfe87628bd71c4781fb7dc4126eee9de59574fa1dd6dd75f03f6fb2893777dfde593a7ef72bb6bf5f70b7cf8cbdd9fc01f407e8d89978f3337f0d,
  0xbc732546c2f1529b4dd5c3fe8775b7c01e07edf65126eefbfba5e37dee5753d7dd9000ec0fdd9fc01d81fb78cadd734c3ee688bf9c8b3cc47d7daca6019b6146,
  0xde799054e2c3a9215342beffde5feb81e3c0fd69a60ed57d942e057e55eb54a6da1639ef9a782740fc390fd000cb1fa001d81fb78cae9b37aa917f17916677af,
  0x55e81f8c17a00ea3f789e3f9ac843fd7a07fd47e81fac61fbb207eb48fdb6494cf698e45ef0a5edf5603fea3f774607eb48fddd1fe3f5a47e9dca7db42cfe0ab,
  0xfebd7ebe3f7992d36a1822ec2e74f44ff5f7d7c7e8dff2e207ec9835457a8334fa015c57c31e3e91fd93ab1dc42f58f6064217a00eabde278d8d232975e81ff,
  0x4a7a52c6e2521fa3058a9e895d71290fd4f2994d0cf4249dd75ba7f5d7febf5faf8fd4f2994d0cf424bc3c7f1b1bfeeffafd7ebe3f7bf6593435b0597ad8dfa5,
  0x7359d3ed74f5e87af8fdba9f61a6b815c87ea2dd4fb0d35c0ae43f42ee28a5b853da124eebadd3fa45fafd7ebe3f5571f0a5cb5821deab622d23ff5ebe3f5399,
  0xf397e3f4baaf77fcb881fa1771452dc29ed092775e74fe917ebfbebe3f72d50cf424dc3f80e9fddff5fafd7c7ecda86b6d85e03a7a27faf5faf8fde2369b31e5,
  0x49d57fe7e81397cc7a5efc5b6d99755ebd71d13ba679d661df7190dc7de1928a5793b0bbab83bef5b8faf5c64604decca4adb852d01dec55adeb7e2f17cc7a5e,
  0xfda56262dc869ffae87e07ef5f6757e5557bc46c0421fb339a7a023d0fdcc3ade808fc0fdcc3145e808fc0fde14131ec755ef1cce6cc3145e808fc0fd1ac1667,
  0x40cd02af1d212d6b1fa023f03f6b1316e6b7fd743f03f7331fa023f03f788270915395558eb6f74d94aec2ec0db7be1f63ce985f15cdbab6f7c3ee7ede808fc0,
  0xa2ffae8003f4b13b25557db58f6047e07ee4c9f4b93b2995abee9a867985431ec08f43f5fe23b8fa73ba940abd9b81871c7ee5e3998627a73b93bccc74bc7eac,
  0xb3cc9fea86c7e85ea99a7ccadbde1760f86cb67993fd50d8fde278c2f57ab132b6f4622a8bfeba1f81fb9a836defb8fdd85d81b6f7c3ee66f301b2b6b139a9dc,
  0x53ce1228321875b5347ebf1000fd5548548fafd6381fb26f196a818a8921bd6aaa6e9247d7eb1c0fdced9b996f8721bd6a28632adbc46dff5d0fff1fad572365,
  0x71c557b849f98e38fda3f5f88007e85a7afc4003f462e176eae6a023a8fd22dc2ed7d40a9581ffa8fd09859998c0db116243e808007e8d9eee9247d7e301fbc3,
  0xef0ec4cad4a9cdcf5e74ce97fd70235c7eb945fd7f2007ef50c655b7dc37f888c3f4fd210ff5eeff1000fdcce264745e7b55ac20fb97cbf11e87ef071b6a9a67,
  0x72fe80ac01fbce2da6cc21d9ee8e72af7ae64ff5fc801fbcffc04e94aafd299e7410f8fd4f234d9539bc30f1fc6c2897f5c2f8e3f79e7c1462abf96eebc0863,
  0xe87fff8fd1b373248fafc603f523bfc457c0fde23686757f666348d421d6ff5fc801fa9febf9003f7327fafe400fd03153b88810ff1fa5569febf5f007e81b62,
  0x3f79126114765fb02363f735af1cce76388dcc245e82b8fddff2007efafe400fd6d465f1102181fb9a9ebf9003f76169ebf9003f68130b361737a1bdd02523fa,
  0x84193430f5f1b7929ffaf8fc57c7eecb21703055aeb74cbfec7e2be3f619492ff5eeff96c7eec8a3bd0048fe320feeff11b1fbc2ed7d40bbe18ffd47efdfe236,
  0x155d074cbfec7e2be3f452e5a323a93863993ff5f1f8af8fd4cd36610ef4dd13d7fa507eb1e5a0cf424d0c3c7f1b7929ffaf8fc57c7eaa7a9ae4c11b58f2d067,
  0xf588df53fd7e3e80fdcd7637fac703f517f5f8d703f53fd7e34207e8a5cb46475270c4a9ffaf8fc57c7eb1e5a0cf08326a4ebe037929ffaf8fc57c7eecb21703,
  0x1d81fb9780a7d54d2269dc2f418de79d6c4471fbc63b0a3cd3b4d751ff8e6cfafd088e3f72f014faa9a44d3b0b2f5b1bcf3ad888e3f671a47f588df79cc58f87,
  0xebe388ffc7ea6b5723de770bfa4890d4df107f5d711ff8fd48fafd7407ed1e6b95396e95281295f9388e3f5b548fafc390fd231152228361295ef6321fa9febf,
  0x177852f735d8dffd47eca9ebfea3f69bfc390fddfe32c7eeff1d81fb4dfe3b03f69ebf1d81faccc24a52ba913ee92f62207d4d6ae34dbded39ff49121aef448f,
  0xdd5011a7dcb973da729dd7577f4bdec4408ec7da5b79a58e5b129baa0234fb4b7acd3b2569baa03d7ef2a984488145bbffa8fda6ffea3f69ebfea3f43299ed30,
  0x665516c08d8fda6c4bc87ed2ffab0ad369908c9f69b0bfe43f7353617fc87eb18896390177a6d220469f7295ded2f7ab9617fa581b110235c7da5b79a7676ab4,
  0xb0c2ab0bf6bda4408863ea466d95ddf0a2fe41f1c7ed3617f63f5ecd208decf6aa8bfeb5c7ef189aa772440f5fa063c05705beac25214bda6c08d8fd0c1916c3,
  0xee76cd17ec0721fbd517ec2c487e9dd517ec2c487eef3b7545fb0b121fbb12d8fdd811b1fbfc948ed8eac7710bda6c4b63f492f0bb2f9db5eae9b12d8fde716c,
  0xc7f7b9a9b0b48fd54d2c79a2fd8ea3f4e4cd39dd2f49cd31f7bb01c87ef2cfb60390fdd85ae43f7864bb2a3c2e67085863ef071a2140bbe188ea3f517ec2c487,
  0xbb488587c7ee6dd18c77c7f7bb3b1d47ee6a6c751fb4b258ccf36f75d4ef977c3101ffc7e9d594ad7cbebee9798fbf9a5e110b5ffc7ec9b7e39334e774bd277,
  0x133a9bcfe54e85f31ffebd2b9a8deda17cc7e17bce9aec4805ef3af35b62402f50d4bcd6d8900bdd80e4bd0bb01c97b0ca063faf763a8fda6c751fb5b7ba8ff4,
  0x2b0c6becb606e5c40fd15ec0dcb881fbed1afb052999d2ea3f7aa22c04cba8fdf9a8ac64217a28a5bb1d57bb0305eec4805efc7f049fe92959d4100c3ffd7a15,
  0x207ee6bec986532a58fd3744c83a65e43f6d87a77cbd93a928d4600d888103f4494949710bdd81b97103f58f69ca70d9a8d20fadcdb0372e207eedce51b36f86,
  0x524b0bd12b244310bdfb5ed2bf210fef28edf6bda57e421fda4b885e8dcb885e81b9710bd5af1cc8dcb885ed25c40fdad497103f7d0a8690bf46e5c40fd0372e,
  0x4207e874dc9edefaa0679b2963cbf5bc2edcfb54a65aa898a5ea72a8fe9d23f64f826f6d39a6a9472deda2eb4b0c78fbc626d3bae4afc86fa275140c40fda26b,
  0x3f6d9317b2bf9d17bd1b3563cd564521ffd8fa03f4e92403634207ebfc1d0abdd50766ca5977ade176e7daa532d5cd52143a39547ff63e80fde078ce9240363,
  0xf513e73ce60fd3f42a57a953bb8031d213fd8ec0fde51679303bb813cf6f6fdd5cbdc6c7d05e8d9c3c57a15d5e94447566956d64e385d74e5215f5ec9201b1a1,
  0x4207edb60932985805f3a2f46c310bd0361885e8a10c42f40d86207e81b1a103f780a67e854af52a777a5903bfd8ec0fde0299fa152bd4a9ddce3a40eff63b03,
  0xfe385d74e5215f5ed6a06207ef2c948cb22511b6b278d081fbc5be799e46abd532908ef6da8da69973958bb55ebfa4683f40ab503103f64f82639846d02ac9e3,
  0xfb11b1fa16e1f4320ff62001fbc547be1c917de53ecb753ee9b15ef8721bf1fa17db3cb753b996fac4a41f453e699e6dd1c5977e3f681885e810827fabf08ef5,
  0x51fee400fde43cac4938b32ac04c83ff8fd4d2867608e1fb585fffee400fda5c2dcedaf457cedaf7d751fec4003f52306362005e8fa1907fb1000fda09d2061f,
  0x1fb586e402f7a81b900bde75e68c723077cc86f5a9ac372017a3750372007e8dd47fb9003f7a815e400fd9750372007efaea0579003f47d751fee400fd387d7,
  0x2c0dc805e81b9003f64e3c7ca9aa62d328b1daf56f2c7fb9003f47ed53175f187497a5e9cbd86b1fee400fd85ca3e19d18676d7b46b0362001fbcf3346b03620,
  0x36ba03f42a40b3f76d7b4afa2fa4946581b5d01fbe977dc83efc831fa372017a06e402f7992c04bcbf206d7fd08ee5a323b9797e77e4b0388eac0dc805ef306,
  0x7cb036ba03f640d606d7407ec87e73957a8bd8f56a6f61e2ff6ba03f66dc5f206d7407e8cb036301fbc44dce2c0413f9eeba35c95f45f6b32d6dd40d8c07e8cb,
  0xe71606469b311dd4fb907037f43f5fecc495c88c1bdfd2f4e4ce6dd2d0e1be47de8d8c17a06c60bd036301fbf206c603f5606c603f64e3c7ca9aa62d328b197b,
  0x49c7e83217e5a2f803f5e72d5ceefb5a44072d8fd7bad2e6a7b6f5abedb3185f968be00fdd36663cf744af7c39751fa34d9524776d7f635517c01fb5a8be00fd,
  0x9884a503660c86f5a70c1d17c05ed2400fdd9a4801fb46f5246f30c072d8fd952400fd7135afa74b54834ef0bb517c01fa0ca6517c01fb2794d0d5cf1ccb92c9,
  0x6a90477489a3c1fbe1f72d4180fdad45c82f68ba03f6ea2e80fdac1a6ccc7e9ba7daf699751fb5a8ba03f72d5a8ba03f692017b45f017a99d5d8cba88ef19e78,
  0xececfcca8513d0ac2c7af5c01fb0b8a8f7c311c69f5ed9d94a7dc02dc3e857beb03ff1a03f58ce1bfb2294f4df0c7fe291fb4eabda0c17b4180fdd9a0c07ef2a,
  0x1fd6aeef96339cb0e7981e241fd4d1d7a74625c6bafead53ee10aa69e857ba03ff1a03f4a8cdcbdb2f67479694732392f73634faa74c4d3d0af691ff8d01fa0c,
  0x23f57d56bfb6da6a5f9f1c47e9794dc9ddb6c7722248d7d4dd8210baad7f4bca6ec104ac4487f4ed5cac649d961f52a7af5f63f5b56ab958c93b2c3ea5981e24,
  0xea3f968e5fa96fac0ffc6bf1faff52a513a3a5c57aa1fad18805b87d0af7d607fe35f8fde1d9983cad52b7d40f7bb9b65a51816fd7a29c711fbc6d85b040def4,
  0xfd0b74c053847d0ac2c7af5c01fa1464c014e11f42b0b1ebd7007eecdd32a9d88f1d12ebfe3407eb180b44fa15ec7e3d7007eb180b44fa15858fc7ae00fd7f83,
  0xd13ea5b1f8f5c01fb90420ab033bc97a02d13e857b1f8f5c01faff436ca39cbf52df581ff8d01fbcf3eca3a76bf52df581ff8d01fb74ff0b70fa15858fc7ae00,
  0x63f8fd5abdd4a91e5cb5b7d60471df5e85a27d4b63f1eb803f7644a0d930b960df12485dc6b8fa98548ccc2c27c67e9f1aafbb22506c8a5837de927af1aafa02,
  0xcfb282505a7ab77ebb1fc7ef11b4d8fc8abf4d8fc6f803f52716ece8d3771f52716ecca869bb8fbc46dec7b041157e9beb0238d7e3f765ce7f7582d1c884ee7b,
  0xd7007ee76c98b138ba8dd6e7c46c387535d0b3a8cd2d286f2f915bd0b44fa6c7e3d7007eaa8dc0edf0d57e838b3d363f1be00fd3a8250ebed54df0c4790fe3f5,
  0xf803f42d13ee1f8f5c01fbc6fc573cfd7da6f93de58fe9c01fbce2d1ac2e37be2f53ddd625b1fc7efd93a521dc42f42d297ee1f8f5c01fa7e020f5db5fb87e3,
  0xf4ef4dfa1b15efac5f0fd0b4a5fb87e03e00fd2cfb199acbd0b4a5fa96c7e03e00fd0f24e5ec57b1f80f803f7986a0ce50b4a93d962b7bbea9cc614e9057b1f8,
  0x9428dd495bf1be00fda5d9a3be5ca146ea4953f1be00fd4cbb2e50a37520ae9fd3803f6194a25cb95e186f77c18a7007e85a27dc3faae00fda3a1bea3d07c7e3,
  0xdc6ffb0629c01fa7e859a6a8326ee3ed2ecd1df2e50a37459fd3803f532ecb94e0c6e8b3fa7007ee605a5d995a3f5a99765ca706375d574fe9c01fb4bb3477cb,
  0x5757dfd57007e8d59adb5fe94aebfe291fa0498b138ba8dd685a2441fd57007e9f93f3ae2322fcfad066ecde11220fb75b0106ea95bfa7007eb9e37eacd8f603,
  0x7ecd9b38b4a191437bd75ef3ff16ca3a496fac08e35bd107f55c01fa2083faae00fd39620feab803f6910feab803f780d641ca3ddc396e43f7796a91ef86348b,
  0x3fa7007edb083fa7007edb7b87f4e00fd16dee1fd3803f5620fe9c01fa8ab107f4e00fddce3a51e78e1d86f71faf5157f720fe9c01fab10951453c1528bfa700,
  0x7ea2afe5fe9c01fa8abf55bfa7007ea2afd0a2fe9c01fb0ca75619629d222ebc6abeac4254516c945fd3803f50b22af628bfa7007eaae7990b1c37be4f1ade88,
  0x3f4b3fa7007ea2967f4e00fd4642dd59cb54e92495a78d57de37602bb2187faf42ff4e00fd585fe9c01fb6c17fa7007ef1bf26775832d7fd3803f515617fa700,
  0xf8fd735993c4b5cb8d7e3f444ccd54f6e258dc77c7eb9acc99112d72e35f8fd796a55cd5394c8883971afc7eb4fe4d6c995d6ff4e00fdcb7f4e00fdaba7fd380,
  0x1fa8a5829c01fbf178bbdf6bdcb6c98b13d31bad5ad64cac1fd7354e5320c95cb8d7e3f514fd44d6f2fd8a11a4050dc6b8fb26935ed54e6272a7378ea48b843,
  0xfd14e00fd634a46b3deb8fd2c14e00fd92b0a7007ee5853803f6156e80d546b58721fc7edcc63156e80d54618721fc7ed65614e00fdac44229c01fb47444229c,
  0x294861de96619911496b19ef09f23229b5fa96faf88ffc6bf1fbcffc1a32f6d7ea5bebe23ff1afc7e83397326415a57c65c6bf1fb554720c1fcf803f4b1ee388,
  0x971afc7e9d3e56c7320af7d60471aafab523d8de403f5be00fdaa39060fe7c01fa7167047488ba8cf5194e64c929049c7ebd2ad5cd28b20ad2be32e35f8fd2ca,
  0x5bf5e00fd4a616138607f42c261779fa9f8b9b372327d6fc7ec8306f7007ece39112c465c6b8fb8284e12258a21afb20c1fcf803f471c66fab462cc9905695f1,
  0xe871df1faf7c7726e4e5105edd7b5fb3228861febd92b3dc01fbb17928e95bd6bfa4acf7007ef2c948cb358ee217a8a716619ac896b19eec5995d95f5a161385,
  0xb219bd12f29f6d2d99c482930538676b499d9b547d430fe7c01fb547d430feeb803f79c13cb595f50bd2cbfab6d7f7d57c47fe3be3f79e656b724ae56d76be22,
  0xa1a8b838c16de31db643963a3a58aa66c9b7e2f3a86bcc96d924c9f6829a35e5d8fdbfff66e7416fb7189b6bb27f6a9e39f6f1ed63519bd9db262ce832f6de7a
]
def gemBitBlock9 : Array Nat := #[
  0xda7492b9b8f37c57b61fd24ae6e3a59edc87ef1a3399351122034e8d833d1b369dfe8c3f6c9a4172ed769df93b31bf21686fc9db4ef0a0bdf6c6d6d769d091bb,
  0xf09c585b7a0276ea62246f189f7e464ed2adae5a4e562ecfcef7328c4eaf4ec91897635398ca5be35fb6c6a73d9da96f8cb378f6b1a8cdecedc6fdbcc4d26453,
  0xcd9b4ead72d11dc45ab6b3c1e78767cc21a994dd26e9fd5adc9a6ae63f56fb2ed8797305d8ec6e7d6e92fc9c33d9566ed9da742c274feaff42c275599ffa0598,
  0xad4c45cd9a1560107bdc9a94bb63b30cafb09d11aad7fb98b35855175768eb26c70a26058e5ad32af676101612aa6bd14353b8b088cd8dbb14219b361fdd8a10,
  0x39b31177dd7a15b5a66bbcdec0eb5318f8c185580432def7e0adad379cc5910eb6f195b8c48f66ecd65bde2360adad379cd99583adbb2d9b2a212d6e6ca886f6,
  0x8da314790f748de35e776ac70ec6dc726cad6b51fca9e22ab2a16fb8fde32942a52959d4ba57d5b9a4d5e753318813be1e619d29b3cc8b27fd5af0d4c42ed30b,
  0xd934f1f0ec05a86c9a78f87642691ad5e314c2fdfa1c16b2e19107b87f635d9165aed3b269e3e106246e16c13d96a86562d1c2dee16b8ca8dba99ef91027693f,
  0x7faa291cb2b684674eb6787587d32fbead9333eba6378d3593879f4f31b2641804e86c99a99ff246eca46c98260d3bc78c869d93f53e59f246c9a78f8767a798,
  0xec79ac9b1c3ed520b9cc6f214e8f6736d79ff8b28b7bf11fa6b51b305cd4218fb95c8ecaacfc3eb898ecaafd818fb98b29d92ac5d84f372a4bec259de73cd2c3,
  0x6d92cade0358d770ab0b2bdeff324774f70ab219bd4c8d770ab0083decdab33798fd5a98459b5cb46557597c3eb5515f486adde6ca884b5b1a819d0b2845df75,
  0x8bd87dcce4aedca5ee134ba57c3e81262f657d5d5a9d4372b639fc27f17a2cbbd6f1a6b4b7c6b555efa7cb25b64641dbe3462e582758e455561f5d0adad335de,
  0xc266d6194a329c5f8c6db96306c615e13f8bd16675f8da5b6f94ea6f331e620fac51139ab2e191757419a53b914ecd667bde56c7b2a33f18dae4a81015defd0c,
  0xd6f0bb0e0358616521561657bdcca3104af4ecc337a98548caccc5020f7ad514482af7af6f6ad0210aaf33dab5feadc40288266ca58256ee2b172c715156ebbc,
  0xfb6d642e669ece5234a62541c91a067556d3e31d9236e0a3d80542ce748542d60bde3416c4b5ca3119bb7e28594599d7ad11168c8f6d30dc9cf51e1336de2cbb,
  0x33dba613bf1c269d615455baed2db516c7bcc99d875a222a430f22c8e434e675396bbb6bead0213f2af6fe7ac61bd6ad7328c5ce4277985c5977adcd7f2a6be9,
  0x5b7d7aaf88ffc6bf1fb47d430fe7c01fb9ad6350573b64c59ddfc586564ae871cf7978af7ca6730aabeb7e3f63c9d4a94acea5d2bead9b332ad8e0d3115d6b6a,
  0xb695b8d7c65c6bafe963dc01fb9d326f6e25887c6b8fa172695dc4b10f8ec7d2cf9f007eaa87f3e00fdfbb8fc33abecd15c875a6a31aa8fdea187f3e00fd4c9d,
  0x3f5be00fde7898580fd6f803f79c6c0627e5272d729d9447b306b7bbbc6059f10ecbd2a544cdc8ad2be2341d7d3f25fdd43f6de209c2454e5ba75b7bbefeea1f,
  0x8a8f7c355fbec72479b9db337a7b8dd2e431d47ebdb8f2dc92a0c8de8f7d7c4471df1fab5b9257305cc2aafadf8fdcd6bb115ced93012f42c07eb7c01fb6c160,
  0x6de86f7007e861bdc01fa5681bdc01fac7b2ab96d962883fa1fcf803f6166f679868bd6861fcf803f56b0fe7c01fbc3b04b1aad43d4722f97ab01fadf007ebfb,
  0x76c7528875a300c3ffc9c788fdcccf32b37ed75db1033bd5f07dee217a5b08f7c31a1eba76bb4539332fa9575e0561fd973b6bd7b803f6b3dc01fa1f09e4a3a5,
  0x7efa34ddf7bcd569b185743d75432afa33c5681615efcb88e2b1fc7edc61fa31df7557be35087c7ebc56afb60e15ef86238ac7f1fb9826655d4a0ea864fb27e2,
  0x3069dc1ac7fc53c7f1faa9dc91a193ed67a666e01569706b1dee3f8fd9348272767d5c8ad23ff938fe3f46727560ae878ffe4e3f8fd19c9d582ba1e3ff14f1fc,
  0x3ffc9c40fde2bb5c62c4f5e1b8ac07ff93881fa317c6e4ecf3722b0b1ff938fe3f6804e74f4364632f5ba99aab0b1ff14f1fc7ed6a6a3b8358ff8a78fe3f6b5,
  0xe948f0f1fd7a30580fff27103f780a7988cc7cf5f26802c0d77b881fbc73e7271c24695ff2e2b1fc7eb1d042aa98c8baf43ea5da448f7d7f88e2b1fc7e8dc56,
  0x79c59ab365c1ea39ad8cbd63a2729d7d9860d63faf75351a7ec358ff8a78fe3f79662386588c2ec264bd6f3060c9b301c273af8aad7fcb8ac7f1fb2684c705f4,
  0xebd3b791580ffe29e207ee4dc06b94adc9d8699c2b0b1c0a78fe3f4ecc9cfa861c8788fd5f51ffc9c40fd18061ffe4e207edb1d2948ee217af0c030fff27103f,
  0x65f8fd0c3ffc8388fd0c3ffc9c40fd580fff27103f704b01ffe4e207e952c91ed21d210ca92f5a05416944d7beb0238ac7f1fb0c1580fff27103f73057643197,
  0x6d5580ffe29007ef3cfb3cc0c55695fe3432fc7ee7582b01ffc5200fd73c06a556bb03669b96163814803f73cf3722ba5aff1a197e3f68f083669385743d6068,
  0xfd0c3ffc800fd6aac65ff2e2bff8fd7f518bb8be516c56fa6e9f72501a1187eac07ff9001fb82580fff2003f736aac07ff9001fa34d988eedad2bdf5896e87ee,
  0x63e5c6407ee78258f11c57c0fdcf2db2c7862b103f6e3e99999e5483910c1ac7f1fb99f878d0ac40fd9c61690860c65bdcc156aa730b463a92c7f5ed1ac31975,
  0xe609981697508c3f7994ee0d225c563c47efcfc7961720687aee66e9f3294f4bb815c87ec33bd9b3d8fa90e355c0ac6be8618f2003f68ed963e5c6407ee796d9,
  0xc6aa8655f78f199c691a1187e82b78f33d256be94a95d43203f5190aaafeebde653b83489719711fa0ca68266bb6bcebfe2bdfd6ab955b9332fa5075c0c9f4e2,
  0x88f5c1a785897e3f70b64c46b01ecc7edb5dec18f5d0670494eff1f736aa2ff8a7881fb772b7d40b9d702b90fdcdab20ff8a7881fa494a66ad285df7b369dcb1,
  0xebb54f25ea21e4007ed191a47cb8c80fde11db2d1a2872dedc699f33313e6e680358fe3f428864788e3203f48d618cb88fd45ff9001fb8245ff9001fbc626999,
  0x994e76d6c064e6f6ade51f560677a5ee6667040a819213952baa197e3f696942280f85cc1febdcdc6d8b5cd3c79257543203f7838c30fbdff11fbbf8a0ca46a1,
  0x2e0c3f437ff8fdc1061fe1200fde209e619f10633e38fdce8ee0c3fc2401fa1671d1dcb01fa4fe07ea667477061fe1200fdb82f5a5b01917e7f5eac5cc183379,
  0xf81fb20cbafea2ff3007eeec338d108c3f428234a78afd7da6ea13cb9bfe2bdfd1217cb9f4dd3fe2bdfd05720bbc15cfa27d4b3aa1901fb820c3ff3007ee6176,
  0x811633cbe94620715fafa18633007e9d37f65fb19865f15ffc7e861809007ef30d58a472087d7b9e5cf32c40e2be07ee797d332c40e2be07e879e5f4ccb1038a,
  0x3f5153bc35508c3f4a6a3db1f128618c82f48f4df3e5a886600fd480a7eac20715f03f795b28c3d9c32b61032b5ac99edf58c35a8875a028cf2fa51881c57ebe,
  0x9007efcb972c67566cbb0de1fc2f43013c40fd0ffcc01fbbbb3ab86634865bd0ff09007ed03fc2401fa1ff9f103f43099cfad2b642019a56ed8f2ee4b034320,
  0x430fd27881fbe996711a1187ee64510c65faf7ac8619711fa33007e96cd9cac5b93faf78c4cb622fc15c9f5a0319c3bb93eb4319803f4eb822d18ec31e217a18,
  0x4de855695d50c9f4410c3ef003f64e2585ce666749d57d74327d7f939e619832fd7bc7254655572196f4430f69e207e8861fa4f103f77d779bee234230fdb638,
  0x2d1a64b7a3c601a1187e88619c00fd10c3ef003f4e9f18b6727f2f512622e6cdc1c632de91db1c8baefef64ef175366749d57d74327d4c58a9b3f6699197ebdd,
  0x6e4afd5dd295d0e218fb99b63487be53b8ff97f3abac710c7dce94423dd1de99d0e327de2369b7329ed2be23432fc7ef11b4d8ae6cd9d3d12baa10f8fd7137fb,
  0xcc401695f5d0c80fde36c03110d9850b4afae86407e9f88c9b3f9e1b3de602d2beba1901fbc6d806221b34bc1695f5d0c80fd0c3da7881fa187e93c40fdce969,
  0x5ea696206e9f9dd7c654e3f73b4b79b7c391da187b4803f58f3b935b39947a965faf430fd2401fa030fd2401fa8ce626c32fd7b0980187e9200fd3f11936b8c6,
  0x9c00fd4fcf1a6cd472ad4fb0d63feb5c7ea7e6b4d9a8e55a9f61ac7fd7af8fd2d9b69ef8723b53f35a6cd4721b74fb0d63febd7c7ea61666a515bdd330b1def2,
  0xfd2401fb583f49007ec25a8ce411e7b0b9d6c61fa116b07de007ef544d8d54230fd2c0cefc0fd0fbdc40fd0a9ec6e2343203f5798618f5da7dec6aa1187e861,
  0x27881fa117a4f103f78df61a7ae85721fb5828bd27881fbe92388fd106ce2342188fd0ce007ef283033801fbca29d033801fa19dc40fd0fbc00fd0fd2401fa59,
  0xf7b999769ce8caaeb2f87d495cd462b0ac715f03f419ad85cc04158e2be07ee6ddb1c59bfbdda7881fbec5558d0c9f729f8446856207efa4803f7d27881fa8bd,
  0x58f10204778e33b0f744b0b1e20781de38cec6c3f7c163c40f03bb17092c816cf51e2bd3801fa77103f4ef5b6b1418ae32a71fbb4803f790f3b867659ea18617,
  0x74e4be23bcbb5add03f7c25c40811de17607fd3f10bda2cadd2d8dd6f025a81ff4fc42f78766cdd9ec4eb43861afd23c7ebd22d739a7a0fdf278d6f7812c72ff,
  0x3bf84f10bde61dbfa7e217bc096a27f971020475fdd72c18eec549979cd503bbabc39085eb1b518bb1f2eb7812dc64ff2e20408ebfd59d9a6e9dc8c207eb696b,
  0xd39c1fea8cbf5ef249aeff218c808e8cbac7467c42f401b885e801fe217af15f5a5b1badb800ff10bd3a5c57c40811da3dd1482f881e077f998599ded21290f0,
  0xf025aeff3017bc4c4771717f980bd3a685ae4ec739150b13e5ff5e952c85791730128ee22c4f97fd7a74c36328e45469cbcbfebd2d9f6e73abbf5465faf48b52,
  0x771ade9669bd81f551971afd7a70e2bd784715edcf71c57a33017b7c33017b7c02405e8d601202f6eff3017afee2006017bc23ecb56006017bfccbfb8801805e,
  0xdcf7017b596adce7aa8aff1a023bc096b9ee02f726c983d991573967b80bde04b7acf7017bc096e8a432e35f88ef249aee8a432e35f88e8328b4b092d5ba8f66,
  0x10bdacf7e217bec69f147ecd6244badb8e017ad3b8e017b6d260f37fd74c8e8e65b15b76d202f6edfd80bdb8ee217b36a6416511a197e23beb1c02f7d63b885e,
  0x8f41f10e5f8dfafc7ea27cbb52310fed08f96f15de99f92bdd00e21fd3805ec8700bd3b885ebdf885ef7f26eb96751e120c6eb7c2eae62c4f91d46eb795c57bf,
  0xe38103f529e5e4a6b874a3dba07c697adfafc7ec99a9a726eaed2287e18db9007021f10e5f8dfafc7efca260735a7afa5f8afe9f64cd4d25356ded29ae18db9d,
  0x243f6130bbcfd713ac9cdbe3886bfc0e38103f6d82a72ebdbc6e6b2617df1c435fe071c081fb78dcd64c2f43c710d7f81c70207e836bc6e6b2617a1e3886bfc0,
  0xf1be91fa3c329b66a88febd466953374ae1d53db71a5ff4fafc7eb89d645dd710d7f81c70207e854e6064b984e88ff1be91fbcc263b54fa66919613a0a8bf1be,
  0x10e5f8dfafc7ef0c67352aa88febdf94ec239ac995fa8fff87c081fbca92e745e963fc9cf335447f5ef3bb12715d990442f69766e47308fad0a93864b984e88f,
  0x6427ec10feb89e3ee34b81c70207eb89f195c697038e040fd93f33cffdbf572f51669178d557fd3a47e8572b1a8efb62dc322fe9e80fd4a797929ae1d1cee81f,
  0x349cb4fadf48fde60c734cf35ef356ed8557d4cd06ce856eacd229ebfd3d7e3f64f827c4188db8fb8d2e071c081fa99985737dba570ea9715e34bfff7ebf1fa4,
  0x57bc135a679af75c59c24c8557d5a84cbd4b5c315f2e691ae21aff02bd7e3f64c4d79e677bbab8636e40a07c4397cfd7e3f61507b6c52a8bd6fd01fbcaeccf81,
  0x306071c081fbb55acde7e63ad7987eab9d88e116f8fc643f71f71a5c0ae040fd7f08146e4abeacfec3e21affdd7afc7eddb92b8bd1ee32ffcfd01faf179dfa4a,
  0x92a6d9e4fa5335eebae74fbf9141fa03f5e1b1cf55a454fca9018abedfdf486f71cfd7e3f6b3578c1815c081fb59abc60c0e38103f7e2db35457d7a86bbacd5e,
  0xed3981f1a5c50e040fd54f5360846dccab360dc0473c5762207ee3ef580ae040fd066ece8d3771f71f718302b8103f6bf561c9e9cd217bbab74f4bc6fd01faf6,
  0xbd4a0895bf407e96cf8c3bb34db52459d20881faf71978e889a72d0afe3062870207ea5abc697038e040fde39971397adf4af7826a294244cd3ba7b6c46beb89,
  0x40fd44f6639166a72d3eb7d2bdc7c1134952c0f8c18a1c081fad5e3060570207ec9b14fd8bd6af183038e040fd4b578c181c70207ec9f72166b65e148b67654,
  0x1f1831438103f78633d5da520b07c60c50e040fd0272f5be95e96cf8fd34a7e3a34e41103f5ea05a2b98f571b93c74a4b2e0c2e8287afc7ef30d5321f183038e,
  0x207ed0cc386c7706110e3c70207efac0570207ef18302b8103f78c181c70207efb38c181c70207ebd9ad2a6daee34bfa70217a990f8c181c70207ef5769482c,
  0xfdf47c3495b830186071c081fa59cf3bb3716fa45e2b4f41d25f8fbafc7e85737c72443e97e1291fb36491f0d257740c061d7e38103f77e8f8692b706110e3c7,
  0xce911f7bf09a103f7869cc0c06181c70207eb186d5975eb1f0d256e0c06181c70207ef214f94fa49b2670d20417497dc7fff8881faa9ef3479e7b3933ca8440,
  0xc78a103f72810194e64cf8dd28eaa2542a77fbe2840fda3e1a7303a06071c081fb78f343510fef38274bcc38796965ee1c78e040fde3dac983cb544cdc413987,
  0xe040fd0d3981d03038e040fde1a7303a06071c081fb82129cc8f02b98eaa2542a77fbe2840fd7f50b3ed74bb97a03f15f1fb973243b954c2869470f34d2c841,
  0x8f9f4af698f8273cd412fd88fe3f43f6503038e040fd2d9f1fcb94ac2ec6da720881fb42cfb5d2ee5e80fc57c7e8696ad03038e040fde236631044ce1e6590c5,
  0x86e7ec47f1fa272a5736e8650717ec47f1fa4694e60740c0e38103f529cc0e818e3c70207e91a53981d031c78e040fd9b12907715f0638f1c081fb6c9e7dad60,
  0xfd4e60740c0e38103f529cc0e8181c70207ee746bca8972f49df5ed18e99e60b91c58271fadae5dfaaca66a487edb6746bca8972f49df5ee6ba7b4fef1c03e9d,
  0xfd4a643a06071c081fa4694c8740c0e38103f4eedad1303b96f4bd7e38103f69f952c58a817aad64af61ad7e9f7c7ea5ab40c0e38103f44cb7de67314309e040,
  0x439cc3af5f8c87edf3fbd2efb5ee82eb887f58b7d4b7daf695d711b7d97015c081fbeca060570207efb28181c70207ebfdf799cc50c278103f5321d03038e040,
  0xbdf6718302b810bdead6f7594eef160adee6bc67c7bddb277f3215bdcedecb80ae042f6942d1247d3f798fd5ba4a9f7669384a23c0edc0570207ef3cfb7f324,
  0xc7e23db1f421c869638103f68f30f621fd4c45b05ba2e3ac70207ee60a2d82dd171d638103f6916b6c16e8b8eb1c081fb7015c085efb2e02b810bdf650302b81,
  0x36365950721e00e040fdafc2667b319fae2b659162434070207ed7e1333ddef27ae2655ec390f0070207eb578c18eb1c081fbb05b8c18eb1c081fb5f84cc3bc9,
  0x7e87cfb5ac11f3e95ed6cc0c2c4b8eb1c081fb1ad6c59785c5a5230af1c1ecce0fb1fe3f7d61438103f78c18a1c081fad5e3062870207ebfd70814378ef27ae,
  0xc3b3e7e3cb0c25ec46dafd08e93dde139cbcabd872e2870207ed6cc0f625c758e040fd937b5cb47be21aa4bfe9e040fde2bc8aca23d968f01b9d479ea08f9f02,
  0x3f696e3b6f93b3e3f397947ec311ffeb1c081fb4b71a6137bbc27397957b0c47fd3c081fa059818ebc758e040fdcc0f625c758e040fd667303a4b8eb1c081fb,
  0x64c5a2cbd6fefaf7303a063ac70207ed49d71785d8ef4dd132505ec643f7303a4b8eb1c081fa991388686e5ff4f0207ee60603971d638103f730301cbffd6381,
  0x6124af0fb671c39d2662421f6d93162717cfefaf6818a1c081fa1d031438103f5aa948f39797abd7c71103f7303a062870207e8d66194cc25d75128b8df48fdb,
  0xbdcdfe38e1cef610edc80e9d3aa2d14309e0408ef38a7545e5be0c50e0408ef0f15aa9a5cbcb7d2e287020474e9d3c98297c085e89726b66a8aeb6e1438103f,
  0x3c3674bfcd2bd6aa697287c69703d0103f4e9bc1ebba73cf7471671c2c47f1fa74e9444e6265186fb8ffc78881fa74de0f5dd39e7ba38b3f1e1623f8fdb82781,
  0x74deb84b85df28c897ebf1e2207ef151a64d887f46086acb83dfef724af7c70c7eb1733f58af8fd6aa696171a5c550103f5aa9a5ca1f1a5c550103f74d984ce8,
  0xb62b65be97df02040fde51f564bbc95ef183154040fdacf183154040fd0f3bbeeb6c2c43fad5d985c60c550103f5fe4e7996ab11fd7a9b6d9ca1f4422a8081fa,
  0xeb57661503154040fd6aecc2a07fd50103f72658b4d984cc2d0e58fbae325eb57661525c550103f44de76252efd3b02802cbfcf7c7ef1499c4e5e9295ebd98e7
]
def gemBitBlock10 : Array Nat := #[
  0x1fb70aa0217a2653999afc788811ddc524a18ea7339797ab5f8f11023a0d852ecce184a23eb6e154040fd3be42d367f58881fb59a062a8081fbb30a818aa0207,
  0xb1f42b0b1ba1afc7ee56366afe201d69fd3d0d20b1ba1afc7ef3a758e68959db0bba7cb94501fa34d953bdd5d774ec56163743407ee9b30975dd3b15858f5429,
  0x623c7dcb274fa9c8147227ab623f8fdcbc23e7816cc051c59cefc7edc28042f6f9337c366972a775fe5a09fb1f42bd80286bf1fb7c99be1b34b97ef75fe5a09f,
  0x7c1e796fbc42870207efa6c45a64d8c87e85cbf75980d6c271fae78850e040fd12e5e38ca57b11b72f38dae63cc140a38355e77e3f6139e21438103f6ecf303b,
  0x89e151e1ad5be0408e8aa0207e8a1c081fbb39d674676c478fa3062870207edcc7410e0f74146faefc7e82c143ced82fdbecdfd4611441a5d238103f46c6ab9c,
  0x8443fa28042f556d86156151a5eb7e82f6719644f99d72517adfdf5ec994d612d4fd0c84700bba6c3adc27d7e3f78c7684715ddc1c92e3faf5f8fd154042f63c,
  0x5f022207ef0f169098af4cc3a3861beebe04440fde2bb53dc95ec643f7878af165057a661d1c30df75fa1103f4b67c7e9a73cfad52459d2a1103f53595111dde,
  0x8881fbbea17d6142840fd4354f4e79cb6722a0a14207ef0f16909a73cc3a386144285081fa72d6406fd2a4993d063f64dbf56f8cbde1e2d213159e61d1c30df7,
  0x674e6b75445985d088fe3f5690b70a14207ec9ffedd9742321fae569383b850a103f73a0fad088835f022207edd20ca19dc50a103f7850549aaceafb60ef95d0,
  0x9936321fbc2ecbb7ba383f5850a103f671e64fc61e64d135ba3830ba0a14207ead8b4bb3387d221bd088f1f64e4bcd33af4221fdafd5bcce916993623f8fdf9a,
  0xca922ce950881fbc879d9198eed91f4cc2e8447f1fa90b70a14207ec9de2ae84643f5ce617d6142840fd7399c1fac285081fbc2ec7399c1fac285081fa1e6556,
  0xbe04440fd1b0b6676732a48b397c08881fae776444695d7a110feb90cee285081fb98512540ffcaf811103f51358ae739db4a81859cbe04440fd2d9f1fa69cdc,
  0xb2f564337b7fda64d3e6b1b622e93c7fa1103f4b64d89a7dd2c6ae22ce5fa1103f416ca888eef4221fd7f939e6d99047f5eb90ee142840fde789f18e65419106,
  0x625cf3170d57055f022207ed18c176f75f022207eb55ceecdadde8443fb463050b7baf811103f6ae4c491df3ce4358febde5a9d18c142dee3f811103f7945338,
  0xad0b70a14207ea1a8934c33d9cf8cbde1e285b850a103f44845736d3947573247ec47f1fb46305cbd7c08881fa53253c5f2356ad12e798b86ab82af811103f5a,
  0xcbd15fab97bcffc17eae5e9d942ad36d3581111fc7e9d968f63ca8881111fc7ed3dc95ec643f6e142840fdf7247d0887f79633ee48ec443fbc579ca356f91a54,
  0xa31054a7ee44f0df4bf0f01fbeb0a4881fbf1cbd5cbdd251752d7e54d0a802ba47d02c50d8af8fdd25cb54f4c289462ba47d02c50d8af8fdb6e44b1cf2acbd5,
  0xeb194b672dc9f79e678098506ce813eb30fbfb1dcb7404097e3f462f96bfad94d33a0eb303f6e149103f619b491df3ce642223faf68f9f6a7e73b20712103f44,
  0x2b96faee928d366dec094dec47ed7be3e9e5f8fdd366bbdd4ded7f6bdf1f4f2fc7ef0130a0d9d027d70b43efec7d0af691025f8fd4fdd5c94fa1b15ee80ee407,
  0xb826840fde0260265e057ae16870fec7d0af691025f8fde0260265e057acc13f63b950a4772fc7eac1b0d9a5ce8295c0943efec7d0af6375e5f8fde19f731349,
  0x308af8fdb83c207eb9cfafe2e1fa24bd5cbd84c15cd6ab337853613b0057d88fa96ffaf432fc7e82ac6d9bc2efd3bdffbf423ea49fc7a197e3f7ab99234230fd,
  0xc0e8f74cd91d74ed29ff74117ebf5c57c7ee64519047f5e87842f58eecc2223f88ee6cc02223f88eec8c223f88ee6d918447f11dcdb2ba111fc4743c207eddec,
  0x5248a7cfd25f7e8081fb99e6345a1d4b563fba92474fcfd25f7e8081fb85af93b4cb9cf74d37aedfa0207eecd63df7c5948f69f5be9fd3fd0312715f1fbc733e,
  0x2a7eda79ac010fefaf6ea58e040fd3f67b2c7fd1ee9923dd2ce4fcf845fc87e2be3f7d3e557b190fdacdd43c70207ea1a8934cfecfa57b99e6363143a96ac7f7,
  0x20d2ff8efd01fa958b9238103f521845f638103f521f145f638103f6ea0f8103f535ab32d7365ce4bce9fd483f10fef8fdb935ab351b9def23eb8e25b0fd93a9,
  0xbd53bd6fb1c081fa56b5609ecc5431f5c6d8f7b190fd859b91cc23eb555277145f638103f43ccaf5936321fb2712c54697fc77e80fdd8b32a1a7d6e3ec9c4b1d,
  0x2470207eb905ae48e040fdea9d77d8e040fdd3654d7126b0d8a45c01c081fbc46d36cb5949dba7d8e040fde2369b65aca4e0ba7d8e040fd9b232e692fe9c081f,
  0x771d998c4bd6fef8fdbbd38103f422f4e040fdb935ab3518323c7e379f4a7887edc91c081fbde5afcc196c43fb77d8e040fd08bec70207eb9a4bfa70207e82d7,
  0xd7fa70207ed7e5872ff88dc57c7edd9f0207ec9ffe933532d62c02e1e3a872f37aa41c477c2f8fd93ffd26ce562b9129ee38aaf74f549f81dfdf1fb97847c9a6,
  0x190643f735e3467a6aabd848bd38103f4b611a64d88daf6c472fa8fe37e2be3f58d6911479295ef6321fb27db1eccaec89568bf10ff15f1fb0baff4e040fd2a3,
  0x27a55905887f475fc2e8081fbc496e5412ab9122fee8081fb9f0207ee667c081fa58e7abcf53ea2b1f48c3cf8103f7d38103f762ce8d3eb71f6dbd38103f4ef9,
  0x8881fbce29db70be5fac440fd1d7fcc081fa3affba0207eb91d7fdd0103f7302357f58881faaa93875ff74040fdf4bbeeb570b10fe8d99d256f20b10fed62704,
  0x7eb6bbceee93c8f05b8b3eef9607158fb77cc081fb71a2a4a954db07fd1efaf888e3be3f56af752a47948f7d60471df5eddf74040fd7377dd0103f730a0ee1f5,
  0x4e7da16fe68b8a3c275fe0446beac472648e968f72c4ef5e0207e8821f1e2207e9c5e7fecc0a32fd62207e8ac21f1e2207e951065f8f1103f7e6040fd45f3020,
  0x785cf303b0c7d3b9f8e075755e6f3c35c461971faaa71dcfc70972c28783e230c87dbbec5081fa117d8a103f78a2fb14207eb908bec5081fae78a2fb14207e9d,
  0xd2840fdad59862a5892eb6f549c7d2840fd6363bdb711c369aea3ff4bc757110057f8fde1a9f3ff3c0b6cf63df0d35f58f6f751fe9b3b740761f1fbc5763b654,
  0x20ac7d6d7ab71b5405a3c320ac7d6d643ab2f712e2cb83e2308ac7d6d643b9f8e12e2cb83e2308ac7dcc8a25df350ead9f905edd9d081fb6dc288ae84440fdbb,
  0x7aa0c6ad8830fc04881fb5b9c207ef21e5fd463d67af91f4221fdeaa1f111103f5564188db595ffc44440fdf99b7eb1103f73a103f7d2840fd6d790f22eaa3c3,
  0xf8ea24eebce82861fff1f4232e3f469b7b39ef475374fb187e3d0cbf1fbca3e39e5597ab97b77da440fd23ba44d1e5ffc4ee3f44bc27c89e7b11b6b5033bd9cf,
  0xdde6b2470217bf9e53905f3a2f7d88fec9c8bd3c17b98e0a474b43917adfa0bdeab2e388811db840fd197e222207edf087c44440fde7081fb773840fde3133b9,
  0xfdf5ec99d4cb6433db393fab97a25d72ad1e5f02775e8796a96f9d17b27d047658277d294a556814643cbaf534042f72cc67ed37c8cb15d6a470217b5923810b,
  0xbd666404447f11d66446111fc474b0acb623c0ed6b842f55446111fc475e0217b9f0217b267539c7995b92c6b3a952003bfbebd933a9cd856e4b1acea549f81d,
  0x416f580e3607ea79f8f74a593d0d0fde36c454b905bf51be37f8fd93bc5f9a51a2027c8df1bfc7ee709e513863fd0efebdf34cf3667165df8fdd90c2f8af6e10,
  0xc3f5bf1c6c0fdcecf27366e6fbe6bfc7ee5a00f84abfd7b93242b9104b2ebdb98e8139b7470d7d77e3f78db38c4fd6038d81fbc6d8b5acfac071b03f78db16ae,
  0x186eba8b828644e179e5917be3fd0d81fa8b82867df7de79453271fd3b03f78c4fd6038d81fbc627eb7e38d81fa47d465e2063fd0d0fde18c82b582bfd7ba6f4,
  0x1f73657221650ffd7be987eb7e38d81fa0cefab4cf36672aeeefc7ef189fac286c0fd45c122c26252f3ca185ec7f43607ec99761182bb230aff5ef10edc353f9,
  0xb03f7d6038d81fbeb7e38d81fb25f39acd8c28bf4ec0fd906c85b187a8fe9d81fbcf33b4cb3ac1067e86443fa6871fa0b7adf8e3607e833bea85d9c1ee98f777,
  0xbb2c74a059f55dd0ffd7a9824be687febdd9cd285b4ca78b287febdac286c0fdc2c1f24fd7c3415fe3f7826bbcb1ef050ca167593ee6cc28df7a0aff1fbeb0a1,
  0x5f4bf0f01fab54bd9aad361f15eeabfeb1f5f7892d584d91e670a6b5702237dac286c2f5a7c0c5a89ede857f88eb6ad3862c432ad50aff11dc2dbe035a0943eb,
  0x50d5ed3017ba97a1f55e3ff58ffc7e87efbf1ffac7fe3f53c87efbf1ffac7fe3f7860981a1187ec9a26cb11e6a34c78115fe3f7d6154e23f440a31054a7ee447,
  0x93d0d0fd97ace97a1fac07a01fa0aad4457faf7d30fd6fc7a01fbeb0eba01fa1fac3ae807e8d9a5cd98cb59fd8fdaf63feba7e3f6b069b366529e9ba0bf4343f,
  0xfbeb0380fd182196a25d4fb5d3d507f8fdf5827607e84cd3e40ab34c8ba7e9dfe3f50d5ed33fb3aa5ed61540bdac2a807efac2a807e87eb0aa01fbc62c050089,
  0xfd4c8777e38d81fa98990eefc71b03f6daae4d65a045a7f67ebdac0e0bd633ec65a7a0f7e258cbf5e925ac12b257bfd7a496b2ef592bdfebd6313888ed60701,
  0x6c0fdf65c071b03f56bd5cf300fa5e100c2b03f58c8fa6fa99e6a7b6122ff1fa99ecb80e3607ead6e4d65a045a7f67ebd0ee143607e87701c6c0fd4c87701c6c,
  0x7703d00fd09d81fa286c0fdbb79af7c35ec31fa2e12f56853ad3fbc1679e5456dfd0f03f5a7f782ceb79515b0a1e07edc13b03f44cce297b0bdb850d81fb701c,
  0x1430be2bd0705eb9cd28aecc22b023a13b0bdb827617b70a1b0bdb6b850d85ef3a6b9056dec13b0bd0701fb70380fd9320c38bb4edc2a807ea622b9cc845617a,
  0xf910fae379dc95ec31fb275c54810a14f5908ff4343f4b347b7b372290afd0ffc7e9642e6cdcdf7eabfc7ebc331e6a7b6f5abeec012a8743fd6b9bbd648d81fa,
  0xadbd6fc7efadbe3607efc8fc7c5211fe87fe3f617a6f676f86bdaff1fa17e50595447fa1ff8fd0a143cdcdf7eabfc7edb7adbe3607e85ea99cf32b6f4ad6acdd,
  0xdf1d553908ff43ff1fa9d88fe44adef8eaa9c847fa1ff8fdf8f3cdba533df0c7fa1ff8fdcc0b0b32b47eb42ef6f79332b7ad0bb0305ca23e857f8fd0ac617301,
  0xb11a2f4dfe3f6b073b67006c2a55687e85630bb0a17598bdcbf1fb7246c0fdbb7c6c0fd0a18182e511f42bfc7eb1850a181adbd6fc7edb5dbe3607ea762c895b,
  0x88ee5b28afd0ffc476bf0857ee89a0956b47b2afd4bf11d0bceac551950ffc474eacf91fe87fe23a7ecb2ac877f7bc23b660c1907567cca87febdbb3d81fbc23,
  0xf7967c9198517b15d7d0328c4bf2b143c0fd0b412fcac50f03f6b67b03f7366146fbf5581fa3111e595457b1581fb767b0bd727562290ca87fe23b96ca32a1ff,
  0xfb67ef6f42b023b9ec0fdf8c8e4eb12defee7a62b098c4f52d6d9d52f42967301adbd6fc7ed1ee972defeeeb607ed1e72f4237dee7deab607ec9f9f036f55b03,
  0x5e9df7981fa77f5981fbeb0807ee587390743fd6f9220fac7fe3f64d2fc20b69de576528b1e5ff1fbd5465d63ff1fbc1354558b79f11fb9ec2f6b67b0bd69f0,
  0x77de617b0c4fb3aaac797023ba9b36558eb1e0474403f7d8ff5b67082eeb7239ebe0465c7ee6435de6f49ebcf68b2ddc7db8403f6ef701fb76f303f762a5f4eb,
  0xe8117a1345e87a4bd09a92f58c022f71f0799545988c3f58c09a2f58c0f497a985c595167290fd0f32a1b90feb1813525e8817b70817a74963ac7811d3b8817a,
  0x15150dc64bdb8b2aa1613acd7e977e3887f5b5e493227d64b0388dbcc26ebf3e24bde029f309bafcf892f78c9b512bcde190fd97adf125ef014f984c8a86e325,
  0x7f21fbd7bdfc87eaa72ace586d44e491044cfb5ed23ff101fd9b3af7bf90fdd9ddb39c72ba838d3ee0a8f30d21fdcea4bdccccb0f5167c497b3622cf892f64cf,
  0x4b99285b308af02b0fef7e9b390a366f973702b58fb7484773133328c3d44f090fd44f7f21fbb15375c67d8636bff880feefe2a2a27279088e3b1f795d8186f,
  0x922e39547588fd84f2d2f11d6bfa157af055ea20a3f511db1fac6716eb29d90e52053ff2dfd459d07ed6caac2fdaf691fe840fa3b2abf94448ff4207dba4bd63,
  0xf5c8c495883feb11fa5419cb4bc475afeb922c9eb41ff588fd63115328473f9575b28fd7245befad07fd623f5c916fbeb4e3ff588fd8671895883feb11fb3629,
  0xac47eb1b6772562b01d623f785d93ec3feb11fbceec1c6d9b31b245c72a8eb11fa9be9711d623f7838fad07fd623f40c29b3cbd61ec4e5afef0bb27ad07fd623,
  0x9a7ac6bc97faf8fdcdd99fd7a59ff588fdf61ff588fdcca869f7cbfa9f61ff588fd42dc6fcf538dbcffcda9585e598cf64c14ca816ca4e2c263d636cee4ac403,
  0x40fd6ae75f9a6474a984ff5ef34f58d792ff5f1fb75058950fc7fe207e82bb3293af7d64e4e79852aafadebba70162543f1ffc87eb5739b426991d2a44a37e37,
  0xb44ae5d21fdb6bb35ebda1d687e3ff90fda30ff08d6f19e52886e238db403950fc7ff21fa9e79c8b384206fc7eefec9d2f4f682c4a87e3ff90fda0b12a1f8ffc,
  0x11f6ecc7ce82fbc3d23f8fda3cbcebd12b387a47f1fbc853a3cbcebd3951e91fc7ef1bb05179c32b64c25b357e13db628bcea9bcf5ea6f87e3ff90fd1a6ea235,
  0xda7f007f1fae6ef4e8898a5289b2bf603e02f8fd02d9a5de616e16b4f678898411185edd98f9d093c3d2be3f42aabfbaf51384dfecb932f78af376602c9e1e91,
  0x748fe3f5c817b1cecafce84b69fc05f1fb4e40bd8e7602c2de6008d6b902aca39d89b14f9ed3f8023c7eb902f639d89bf9d2769fc01fc7eb902f639d89bf9f09,
  0xfac7d63133386cb75108019fe1fda3cb9305dbd49cc47f5fe3f8fdcc8a3293af537c38ffc87e8173ccbd42598fc7ebe3f6e481f3a4ec6e91fc7edc903e7c2763,
  0xd7c7eb18999c3032b8400cff0fed2d661210cf56ca460174a975f1c64bfd63efdac04af861fdd94aaec549e42be1ac7da5acc24219ead9a58c02e952ebe38c97,
  0xea12cc47fdaf8fdcc3dc096623fed7c7ea79cf2a46e9c52823fed7c7eaf3bb817c23d2be3f79830165e77719447a643f53f3f8ffe43f68f2f3ccbd425988febf,
  0x2f8fd72051a957b812cd7f803f8fdcf8c58ae76e3165edce40931304d9c13c615fe00fe3f794fb838d3484c2f30b96b05eb9024c16c26cea7e34bf017c7ee61,
  0x67af48ee6d705baf91f9d02e7997a84b35fe3f5f1fb1aef3a0942df75eb9028d4abdc0966bfc05f1fa1c81565b157bed7fc8bfc05f1fae40ab2d84d9d4fc697e,
  0xf8fda3f9a64f0f1017c7ef11334c51690148ff1fb94a8e223af8fd18b3ff21fb4e40a3501616eb6008d687980b2a1c1fd4fcf1ff90fdb82e7598e183e37b7597,
  0xfa93bd893923d3c9fc526939869fc7ed7b130bc2f44955811c7f1fbfd893923c2cd34f6c6437e3f6f857fe43f69c8146a1e4c2cf6008d6f01e6ecc7cd32b8763,
  0x84530fbaa2ee979edb151fc857c7ee6cf37f211fc7ed3c2fb190fd631296fcd7fe43f7323d9186147b34badbf50374b97a0ca9c7eece080a859ce5ef8ca16b01,
  0xee598ae040fdca5401fc643f73ae248af8fdcb49cc01fc643f72d273007f1103f6b253115e0b15785bdd2e9f78453c9b35dd2f3dac94c45782c43f85bdd2e9f7,
  0x2939795efbf9e7964b46557e94f4f4f0fdf1fb9955a447f1fb7c2b890fd7fabf0ae5a9be15c487efddf0ae243f4a84888f1fa99662b8103f5fe4e799aa23faf7,
  0x4e239edc27bed7f3585f158fa94ce0353842f2dd2f3d4fcd70207ed0f9ae040fde571694f4f278683f7f3cfc549decfb3a9f8558a27812cc6f5f8fde5daa42ef,
  0xb1f44be9a2be4e5ce9c473db7b967dcb3581fc43fb7fdcad940421fd12d6f9457c9cb9d388e7b709efb5fcd617c563efc77dcc9a872158fa25adf3d7df2539e7,
  0xde314fd836168912bb1ff8fe3f4e2f2d4edb665256fcd7121fa9f9ae243f7ed7e59f1021fd12879978e9c473db7bd693ee59aebf10feb6b3601385f6b78440e2,
  0xab2e84d617a59ff90fde5a991e5cc08342deb577987a972cc65b1fc7ea401139ad171fb94aad63ff5f1fb96b288ac35f1fb6c8a3293af6f93ff90fdbe4ffc40f,
  0x8fd5a897e321fa00c111adca544bf1103f69c0f1dd09c910bdb266a6d5f8a16e3dd179510d069fbad2393c4dc43b50f85cbcb248d221fbade56c05553d9639a1,
  0x243f72e697e321fbc4c48cbf831cc7affcf4eabe4ec850c411cd3c219d38f50c687f5febd4651528a276d540cca663a9d12d7d57eb4b369972919b895964e23f,
  0xca9e9d8fa15fa4ffc47f1afa7fd4a04c34d6099ba763e857e93ff11fc6beb54416f8767a5d2a9788249fef634bf186c7f1afbcad8c7765bd0af691fc641fd2ce,
  0xc697e30d8fe35f58c2b2117fac47ed2dbf4491d04daf740234fa593bd8709f5b0d2d633b997be5feb11fa047019ec7e392b14cd79f187fc390fd3fe24a1a6b04
]
def gemBitBlock11 : Array Nat := #[
  0x2e241fd29b319c92a661623f7838e4f0dfac47ef071f12ff588fde0e3908bfd623f4ff892869acbbe6e36c7d0afd27fe23f8d7d6a882df0ecf4ba552f13371de,
  0x2ff103f78898e1f69ba6065c7d6bf80bee191ba59dc67202bf410046bf1fbd99fd7bdcf10321fc7efcd6421febdeafeb11fbc1c7d5fd623f7838e417f588fd0b,
  0x21fbe9f855290fdfbbe1bfc40fd8f29bee3c47e207e9554c46314abbd85e948efe642bf1fb0c4a52b4df05cfaeb4aaa62318a55dec2f4a47723a42bf1fbf77c0,
  0x95854363dcc8e1893928bba149de7e9ea74fdd0beadf8fdfbf90bfc40fde24b6cb1c2021b2cf59685dd6be13257e3f7976a4659551032e3bdf4eb05efddf0dff,
  0xeedac2e87023f87f7288f6d394eeb0bfd49b11fc442c7dfbf9dfe207ee646054a9d9adf7a8f36d37c2b11f881fb9994eadf109372f69a55f06363ef35d8e4899,
  0xd687d69f451b65272c6bbfa9363c08feb1f5a7f2df0db2939635dfd49b1e047f58fb99c4c8def4015654107d44077594a58dcefe97b4ffc47f58fa880eeb0eeb,
  0x23fac7d69fcb7c36ca441afbfa9363c08feb1f5101dd6421bb6b0ba1c08fe1fdcd731a7e153d8ad0ee36e4fea4d8f023fac7dd25be230a774e694a569dd294f,
  0x10b5b51656520fb3692faf7efe77fc87efdaa8eff90fd5a952a94c235efac08e3be3f735cc69fde5a7b15a1deb49fd49b5811fd63eb4fa28db29106befea4d8f,
  0xa243faf8fde43ca72d1895c00cbd341854bfc7f1fbb8b9434c3c91f88985f8fda3dd2c7970fe88664235ab5e321fd7c7ed0f4ba9be70a7fb386f6e35f6ff80b6,
  0xfe2b190fd5a8a1e2be3f64cec2c58ad7f7abfc87edb51e623d62be1fdd951cd721df1fa3151c9e2bb3f470f94443fd7c7e87c8a55ced2f7ce9de1588600f1f56,
  0xf6bdd058ff85fd0b98166dafd505d7e17f7967cf081e57fb34b42e647711afd501bf0bfbd5121fab5121e2be3f7e76243f732b7cbe16321fbdcac0ac643f7b95,
  0x9ddc2c3be11c0af40ce56c0a04957fc2fe9c5a95364eb63d52a694cf658082f752a6d6acd97e44b6deffe17f785dbeeb6c7f423f785db815b63fa11fa1730285,
  0x4881ebf4b3fa11fbc20c452ff896a7e6bfa11fbcd76e14d761720b74229bc079a53c2aff811fbcfb5480b207208e17f785d93f35fd08fde176fbf9afe847e94d,
  0xad55fec7e9c5939db3317988e77271fbc63b2ad6035f858fdcc0d86788ceb9557f62b7f81f7d0aaf7d6248be8d0c10b3ec56ffdfda5667f5ef57d08fdf4bbee4,
  0x31798832ee4e3f4281078d7fc71fa0ce5a0cbd57a8fc8effef6b53fd8fde76c63cf311e44b971c7eaa89c7ee666bd7b5b35ebd15aabfd8fd1042b53fd8fd8640,
  0x208effe38fd01546bfd8fd7f1ce46136b23dbdff03e850208aff8e3f6134ca31d64c5effe38fd54c5e7b30e16dd08a6db118317313508a6b4e816915711fe3f7,
  0xdb32186b7e6bfd8fd55588938fd1f35fec7e81f35fec7ec2e514c5f0eff007ec2e514c75a1dfe00fde60c0597985da2ac17aa98bcf272882dd08ae3f7924d4ac,
  0x1fb99148f617b955110fffff1fa74f8e646c453b2bc9491d2b9182fff7a54494bfe38fd0a0494bfe38fd0a0458cbfe38fd0a041e32ff8e3f7d32a21f23bf15b6,
  0x56f4fb1fa3e77f63f79e7cbcc4020ac08dc7e8be1bfb1fa15477f63f5202883c40c871fa2b56fec7ef2a097e4ccbbaf58b52a68ac077f63f73118949c7e967fb,
  0x8fad0bdbca8262d6f448fd1580ed23f7abb11fbc496a52b7054d363b15ef8dc0f1f5f7abf63f7350a30f5fa3abf63f45f53ec7ef3065c9feb3aa75158af8e3f4,
  0x9c7fae207de7532ca120972aefedc79dab2e6b9d25656a5b5f5f03c40fbc579f8c4e1c9d7bc42615bf4a47e954c15cbaf6e3d99b2e55b4a2595388ebde2130ce,
  0xc91fa2fb8ed23f456cd23f456f448fdcde9d22e3f456ada47ef109856ada47ef3c96b0ad5b48fd667331df551a430b5d57d7c0f103e85e5535cf36b76facad4a,
  0x2a8c91fa1547691fa2fa891fa9e78cb6e52ebd02f86d23f43e638d44832a501fa33a396eab6c2dd36444d38eb2a501fbcb3ea2d2041977271fb59306949a2fb8,
  0xc65639cea4108bef3a082ac963d6bfbd548fd1d548fd0a04114f11c7ea60872587a9020a0c23c487fe3f4165a405104392ff1fa99d48eb21ce5784cc4392c2f4,
  0xc9f6b13463d4e1fb5ee80fe23d0fd12977f8f78e65191e21e4ad947ea72df6ba1a03f8f14fdac197d287863fae4fbc2ecde6105bdfaea6bd9f6ba1a03fa2faaa,
  0x103f5ede6250f56d8d5a63f61ae87fe5e43f40b8e64fc724348e6bcf8c3fe1c87ed675a971b794f856129508fdac4d1a2387ed7ba03fcb811fb5976fd3740408,
  0x932a11fa8c8b4c7ee4aafc641fa8c8f150fdc9540641fa994ef79c9ea6c61585d0e163fd7df4657ef79aad3630ae87aea8655f5334c56109775b87ed7ba1ff97,
  0xc5c83111f45f7908e207e8bee2047103f6b311a5635c7ef01e6b3118a58d75ee6fbc887d7bc079a3f048f5f5ef29f0e29047efba9fac64bfb584cfca4de53e15,
  0x37b9003f45f6e5c40fd4e795236bba974b1e3c7da1e34d17de52d8fdcb973daeea5c8465c7de313491ae4308fa2fbc84003f449bf21000fd17de52f21fa0c954,
  0x15ea5fe417c0f5f03f449b006840fdacc46958cb8fdcc46958aff1fa0aa62c57faf45f79751fa27cb9ed7752e4b15d7d17db96c7e8bedc801fa0aad465faf409,
  0x42ded8ec0fd17db1a103f53b6f96615b525083975e8937b1d81fb6dc3a9dd41ee4d126c01d81fbb8ae4b000b5eb61ec6e0c7fe3f64ec942f7b007607ea764cd1,
  0xeb7727d68e29003f448f4801fb99d512f864320fd1c42001fb99d5124d8cba8fd1a6588fd7bd563ca3f4714823f45f6fa8fd17db180fd126f6301fa2fb63b03f,
  0xbed2d8018d6d6b1f7867c8b6bef0635e961fd4edcf13cca675cb37bb201df7c0fffd7f92989903bef81fffb9b76c716240d7aae4ac2ae80193c0fffd93b3115c,
  0xbef81fffa01df7c0fffdcc75f675965c78fad0c7d5cd6e35e11a74d9d4381fffbc48278469d36750e07ffee6d817a63bde2413c234e9e8674381fffa76b9edee,
  0x933db45dba1fffa2edf03fff6e69d6eea71a0efba1fffb751d1e5495d9a5075e961fd4cf09f21abda67f5538db59739eb1f8d4df674e7ac7e341519d28cbd683,
  0x9a1fffa999ae548334b1a81fda3382890ded5b95396eb4b5d50c9f42f57ab132b6f439e07ffea66cf31ef36616a41ec31f5ab4795396eb4185fa56133892f188,
  0x9e5476223c7dcc7abe6bec28ad87554a70b14e2be3e8170a0ae3d90d7bde7fe7930b048417bdfebb2794f8d35e59f7b2d86bedc174d65a03847aa105bde5eb43,
  0xef2f172c7eca9a7f4b6757a587f4e8549af9da72a77d6105bdc655b98f75fcef32761d553a85bdc57c7de2267bafab0ba77d6a94e162ab888f1f7945be2a537c,
  0x7dfffedf5246d57888f1f6fa922baaf111e3e86354e5c6e0a860727effff5ea34cbea18243aae223c7de516f8bf69be231d888f1f5ea34ceb5430a01d57111e3,
  0x87f6fa9236aa2223c7d4edcf1302cebcb6f6f7e53cc9726873f7fffa284fbfffd1470fbfffd54e6cf1d49add28f2d0cbf215f1f66d45b1ef36cf5d875a0c8a38,
  0x513e61abfa8c5c164f430ae97fd07fedb722596bc57eab31b26a4de10eb0ffd0e523fd0e53fffb6dc896cd7de5eab31bc353e6136d6bc57eb2ea27cd76f0b815,
  0x933db372ea455957d69eca269ca5827b7a1158fa0cbdb849de6cb7ad6987c9a38b04f6f422b1f57bbeeb0ffd44c1b34e1b51fa1dc923ae5ffde14166cebcb797,
  0xfd088f1f46cdc2632a2720ee45ec4563ebc9858b50b7bf5dcb0c830d888d7d6ad1e5495d9a575f4237dd9d6c320c362be3e8322ea2209de6171656e5eb671a27,
  0x265c3ad195e4c8846245a65c655a34c9dbf87b0632adca2963fde2a7f11f7f7c8ec4563efa7ca8ec443fbc0535ec7ad7111afabae3d6b888d7db8d3596d84832,
  0xec7fa0cd007caa7669683ebe91afa0cbc1f0153b34b9d675f6350e1242df1dd401907b58d7d8d43849ca37c72d20061ed635f5cd2c7fb5944e852d96826c0d79,
  0xfa59582b7bf5d7291feefd64fe3798993320ad218f90d4af371f5b0c7ae23198e6ee3eb53d4247fbb1ea123fde2369b536a722d958d42b58fb582bbb8dbb1ea3,
  0x42aa23b1158fac79864197b111e3ecb281bbf05ad88df79935cde8446d4c88c2b48a58ff416847ece95fe632105bcf6f0ec632b26c4c57bdfeba7ebb8875cbf,
  0xb110fea7767b2a6b4d41d7a1158fbc2ec255862ba5ec4478fac65c25f61f422b1f6e3a3a63634d6e172a9a0fafd088f1f44615a452c7fa9e678c57bdf193462e,
  0xac87f5158fbc549e31610f8cbd888f1f4fd4958bb9a73210f960fb36cdb0def4221fdcb3963057af5d888f1f51963057a8cbd888f1f6415a452c7fbc3b18bec3,
  0x63fd713ac91d75f422368c8b4ff4b1fedb715240c739a421f2c1f7826b994bf3d82d727d6f55d2c52c7fb5d574b14b1fef1d574b14b1fe87c7425aa60acbbaa3,
  0x4b4e83eb92fd088f1f7d89978ad361a7afd088f1f7f994b4ee93ad6c83d7fa58ff641197fd2c7fa241197fd2c7faff3579c5a96108eb2ef55a452c7fbd569fe9,
  0x923c7deb9997604557b23492b1f44615d4bd2c7fbcaeca0a9b014af7f6a7e75715fa58ff7324196acaecf72505fa0ffd4c552cadefd77af514b1fea76ad9f64c,
  0x4e6ab245af8581b6ce72a79a3d9654821f0e963fd84f7225ab03aaf41b20aea5e963fde17611d22d88da573502b98f882315d2c47111e3edc368a9d9558230fc,
  0x72a695cf5d28c34b62b1f4645d074b1feac390304b753ec3e3c70f80ffdcd0d84b9d67b0fac6ff01ffb20d6a58ff780a7208c03115d6c8234bd2c7fb6cb569ac,
  0xef1260136310c478ebf4223c7de24c42d4a308f1d7c7111e3ef107c92a9830ae97c7111e3e8dd91528c23c75f1c443fa04c57bdf1937ad6a58ff7a8c1d2c7fb9,
  0xdb65e6310c47d2fd088fffe8cfe9c755c08887f5e5afcc15fd887f7d83266eaa1c308f1d7c7111e3eeec8a94611e3af8e221fde792e76026310c47d2fd088fff,
  0x13a269bc8d25f5ffc2c7fb36e7119989ccabe8692f88fc2c7fbc0bf42f4221fd9b74ec8c79172a641bbcbae23f0b1fe8c498f5566e6ad6ea86fbc30af4ff64f8,
  0x5145d051815d2f8e223c7d18465ff4b1fec8475ab81110febcb54c15fd8ac7d1843ebff858ff6b0ac86eaeeeca9ad2baf4221fdbfea0805c692faffe163fd9b1,
  0x3fd86658465ffc2c7fbb5a95cc5681b548dfd2c7fb0a8eb9c208c574be3888f1f686c3b2c6bb0a8f63a882315d2f8e223c7d79397a8d1187d7e84478fa9ddb31,
  0x5ecce68dca7e7d3419c97c6ba7ffb74c563ac70b1feeed74c563ac70b1fee6e0e394ae1110a73ff4465ff4b1fef2c66d86ac73bc27c232ffa58ff72c232ffe16,
  0xeb1c2c7fac798533266a8f694d3fa5811ebeb1d3ffd634e514cc59a3da534fe9617d7c3e9ffe95b6911d60bf58d394533165ca7d6fa69fe6bebe35d3ffd2b7d9,
  0xa30431faea7d8623c50f27fbcc4ce68731355d4ef08f038f27fbc06bf1d73b605a77856071e4ff798996bde5d10fac70b1fecd9e384dd00a865f90af8fb74c43,
  0x2d9533e4aa7f418ac711ea5ffde7167aab3648e9b9286ffcc5638d53ffa232c52c7fa21f58a58ff7976a0cd75a1ebb9803bb54e398faf310311e3ac75cbffa9c,
  0xa0859bf1557afe7fae87d7fd2c7faf1187c65fa1158fa1ab21ba8aeb64230def4221fd1183a58ff529f129fa9365d0c320ac7df8b0808aaf64696c563ecdb883,
  0xd7b971f4057be5450c56911e3ee5450c57f62b1f53f65aa30cb0c447fff563ac52c7fb1ae4c98467718238097af3d8741f1e3af6321f635dac5b23d9474b74ce,
  0x9631943566158158af4223fffaf08d598560562bd088f1f562b15fd2c7fb999e54d3fc17eb1ac562bfa58ff776c74be52068c1d2c7fbc06bc3b1e72f15ca3ad7,
  0xd088fffef2ed64aa082b02b15e84478fa918562bfa58ff76918562bfa58ff78d35cb6cd0d54070ac0ac57a111fffd1059909e5a1aa80e158158af4223c7de792,
  0x18562bfa58ff5ab3609f14522f951015a7fa97ff7994f76860030575b27c6d4ccf5506c6158158af4223fffbbb4846b02b15e8443fbcf25e18cbd5410560562b,
  0xa2b15fd2c7fa8a2b15fd2c7fafe85bcc3358d8ca0569f42be3ecd9fcf4954ab02b15e84563ef3c4e8e44d60562bd088f1f46158afe963fd386158afe963fd78e,
  0xe562ba0d2c0d1ebfd2c7fa21d7f4b1fe8c21d7f4b1feb4f8f6b475d7d2c3fbbcca96bafe963fd58875fd2c7fbce2cf511896b35ba0df78615c07fe8ad3fd2c7f,
  0xc72e64203aa9ed8ec692c574fff456914b1feb9a3910722ba48447d68c2b142963fd054b217e644a6e90158a1f63fdbc60c8b82f09de61722a0eb72e3ebd4acc,
  0x458dbebac69ca364084196b3fb1f42b0beb4f4fff7976a0cd2c6df5d634e51b204203aab3fb1f42b0beb4f4fff58d3946c81080eaacfec7d0d258ae9ffee665c,
  0x2b14f2e3ee6518dd02f02b7985c59771f796a74748b621fd1361baa0bc0cdcd0ba40c5629e5c7d1ea2963fd93a9ad3282cb90311f5a308742963fddd84c9ae1a,
  0x637e963fd185637e963fd0531514bddc99160478dfa97ff78e4b4235fb341ea7a015803d07fe87cf2635f9f5683d4ef0ac01e83ff44d86ea82f033a09cc5d206,
  0x8ef72c9637e963fdcd0d84b767b0fac6ff01ffb22c6fd2c7fa748b1bf4b1fe9fab0e97ca40d1ad4b1fedd31ad4b1fe8af3a58ff78f19735983915d24223eb45,
  0x6f42d3282c88311f5b22c26963fdafc042651785396ef9471e9091fea2f4b1fe9545e963fd3a445e963fd0c3f4b1feac6fd2c7fa97f11ae83dec43fb9ec58b75,
  0xc983b5d3a08721d7e8457ffdcc24b79744a092de5dd850f82b9df110e43ca84478fa310573be2218dd7e84563ef109b309d77faed6a58ff7826a8a9d9ca38d5f,
  0xb30e43afd088fffeeed239cd6242bd0887f64d8ed7097d87d08afffbc71d04390f2a111fffde4faa821c8795088fffef27d5410e43afd088fffece348fa110fe,
  0x8447fff6e302171cf088c23c7d9368205b30e42bd088fffec9b412ab9cc390af4223fffb26d04aa25661c857a111fffd7f88c2ad18c47d088d7de792f0c65e12,
  0x215fd2c7fac634857f4b1febfc4604d8231857eb79e4bce09f63d91f4223fffbc55b188fc34b7bc474e85827c8fa1158fbc0963a558452c7fb26d040b661c86e,
  0xffd104acc390a1a111e3e952b940483af808d088f1f79e26b165112bd887f73b77f7c8aaec857f4b1fe9256afe13fae0b8fb271e30f2731541a49f4223fffb99,
  0xeec8d209a58ff6f18320e1739ef7ec2e5dd40772e3ef398a9bbb3f4a1ea417c56e55f6437e963fd1113f911f4b1fece30676bda57b10fee4dbc91614af695fa0,
  0x9cd3492e54a111fffd86751190563e84d2c7fb209a58ff6b24134b1feb33d72111fc6efdb30e43afc84478fab151aa776c47c846fbc2ec136b107dac2f8ad863,
  0x7a62a5923070d8da25cb6997ad9508f4b1fe956329b7c719dfebb93674b52334b43b8c972da65eb6b259d2c7fa22b1a58ff64eb8a91709201d088fffec9b413c,
  0x6f202223c7dce963fda0e963fda7a58ff46a0e963fd9674b1fed2dd6e721624223c7da5badce40889088f1f696eb75110589088f1f654f4b1fecb63d2c7fb936,
  0xee7348b25c6c92f4b1fe8de5e963fdac3afbcbd2c7fbcf25e5a9e61c97e54223fffbc6d9c499cad8b4afca8443fbc5c6fd410e4bf2a111e3e9fb88fdb2f318d,
  0x2d6badd088f1f728904dc8bebb02223c7d186dfa58ff5aae57f2707c201110fe91854afcf33aaf7b11fffd2a8bbcf55ef621fd230a95f9db0f55ef623fffa0cd,
  0x343a58ff4aad48d7be1cb3ff788da6db2bf2b9aa55ef8d4218fbe963fd97a58ff7826b36ef6c16b93eb6b7a58ff6d8e90dd52068dbf4b1fead72b5728904af2,
  0x22ca31bce522ee2a92fbcba7fff4e5aefefb918655f736a6e1fc9392395defec0559078f1f6963fd4cec9d2df5fb7dcd37d9a40c47d68c326963fdcd6a34834b,
  0xfffef014f319a5bce97eedaf8158d7de0e30b98cd2de74bf76d7c0ac6bee615ee9c6dcbb2ca563948bb8aa4bef2e9fffdcda9b87f24e48e577bf40ab20f1e3ec,
  0xb8158f1f5fe3b282a33065eb6b2e437feffff6f1b55237722618ac7aa1e3c7da585df224a4b3878fadacb90f2e9fffd78e45c14a576e4bef2e91fed565c87974,
  0xfbced944d0e7484da65521e2be9fffd199168fd1eca6b28aee784aa43be9fffd5c86fa7fff6b2e437d3fffb26d79f9f942fbad5c0ac78fb2609933f3f285f75a,
  0x55d07e490fea2d624acbfb755d07e491e3e9545154c69dec5eb42f57b62adbde29350e7484a92541e2be9fffd198cac9cf55d075d21fd1db195939eaba0eba43,
  0x3fffa59b8d8d720f7a86b2235d075c0ac3fa9e2adfb92fe12446ba0c0f02b1e3eecd2ac8797fbfffd0f8e95d3adbd8d72d547484aad41e2be9fffde318cac9cf,
  0x5ce83aa10c7da3d902f946cc2d2c6c71eb1f68ef8092054cea42707f4a8822358158f2a1e3c7d0da95911ae83f2a5ac7da5836a56446307e4958fbb34ab21e5d,
  0xaf815ac7da345a3f47b2f6515dcf269637feffff695643cba7fff798984b599a6e5a453f4f01f5d08f58fac6716e15656cae6b41f5f02b58fbdf88ef84cccf30
]
def gemBitBlock12 : Array Nat := #[
  0x9813ba1496f21ddc7d4cccac9cf55d07b48f1f53024ac88d741ed23c7d38adb04ef62f5bd54c092b2235d0672c7d5590f2e9fffdcc2be771b78f19ff1ff4ba0f,
  0x662b4c8478fe3696446ba0eb81587f4b34ac633cc569908f1fc6e5b3f4999e6f34eb5077f87fffb1af542eea6aac86ffdfffee59eada2e798a34eb5077d3fffa,
  0xfff492aac86fa7fff76144be98ef7aff1aec889d8e99564aff4d03ff87fffbcf25bfe393b1d32acc72ea3f8d031caac86fa7fff4b2446ba0eb81587f4b34ac67,
  0xb1878f1f78c769b2194a32a16f61b7e5b6cb5910c4696f798308d339ecb256fa1497c5630f1e3ef306424e67a962a175f4292e8461e3c7d90df4fffeaac86fa7,
  0x78fffec33b02adf23bd0303110e5bdcf6ff75a392f8ad743c78fb46c6128a9fc0fbfd68679c9d465c7da585dbcc960640478f1f43ee60c4673dd2952b7d46be2,
  0xdc9b94f9ee13edd38db77cebf67d40638f1e3ef3be746e58d270c16ba1e3eb73d964ab4f3ac22ba58f1f7983212733d97659aa3afa12211a5c7de313231580e8,
  0x8e6d960f5040207d2c6d8d726d9a2cd1b97f57aacf89c5f654e9fffdbbe746e58d270c03023c78fb9c6ad3ceb08ac0ac78fbcc190939996e3a3afa12210c65c7,
  0x7d2c3fa8bfd8bce49fc6f10f2e9fffd5f1a5f863fd7f6e8ef0b81587f788797fbfffd2358e1ed21fd9b08d63a2487f77f2dd3adbd63866b2f63c57d3fffb96f,
  0xdbcc4a3348dbc0a4bb93f8de21bff7fffa3745031e634d27371ba7121e42174b1afb9e799597b10be9fffd45cf3ccacbd885f4fffed669648d3654cba9f61802,
  0xbb02192751fc6f306424e67a8eb67211614a4b1927fff46fa7fff7886fa7fff44ccaba941d50c9f5cb1b95f45f87fffb82854abe8bf0ffff5324dd26702b0feb,
  0x43cd99cf15db92bc0ac78fbcc190939b7b1366da16672eb3fbfffde60c849ccf51d6ce4551c2916324fffeae9d3fffbcc18464657e605dee14292c0df7fffbb0,
  0x41b14dba2af65d80e9c6e1a7f1b4e9fffdafc256566da5c894cc197ada974fffea2a6d21db662bb72945202b1e3ea2a6d21db1cf15db94a290158f1f72a21bda,
  0xffd457b8e4b21a5feffff6b2c6dffbfffde58c9d41c325f9f907bf02214529fc6b553258724fe36b2c6f2ff7fffb9db8f1b61894ce24b71e36a530aec833098f,
  0x7effff7989b2b4de5fb56aa8de5feffff4ff962a3a5c890fef1cfb3558cb11e32a7ff785d8474b91236ed6aaa3797fbfffdd25ddcd3ac911e3248ff6b2eb7fbf,
  0xf7838e4dd3324781587f4e9f18b672b648db5bfdfffef3ff22bcf0190c14ac57d3fffa14a957bb16b5dc7d55adfeffff5546dffbfffd11e4ce5cca09592ab25a,
  0xc7dc1010f8afa7fff788da8f65ab5c2ac51815af8ac0ac78fb820bb34b90aff0c7fa55c96654b90c923fdacb1bcba7fff762f673bb11a7776d7fe6371fff5d7f,
  0x50cbd6a658c63cd98b1340a85a6f7d135a57c4011e3c7d452c91fa7b3b1b738d2350cb8fbc9f15bb351f15d2d7c6158f1f64dbf2c59d65defe3a30ba5aea8563,
  0x8f623d75bb5aaa8de5d3fffae5546e23a7fff533c7b5e209e6235815af88023c78fa99589cb19cf3f9340a85a6f7d135a57c4011e3c7d588b205bebb2765923,
  0x23c3fbcc9ae6e05636967045652e2def149a94f1ce6522ff0ffff5546f2e9fffd5aaa8de5d3fffad572ab742bea3a0eb8193ee6ce8467013cb0e1cbc9b9ce5ca,
  0xc574b5d50ac78fbc72573b14f1c24aa45fe1fffed658dbe9fffdb6067aad122dcce6b2c6df4fffec3202ec5414b91be5d0ffa7fff533c135a593255ba155a7f0,
  0x4857246b48dc0ac78fbb1941611551f5bb0ae64186df4fffea678a4cf556268556b753ed6043037c3fa4747c574b5d702b1e3ebd4a26dfab21f5bc9f15cd7d47,
  0xfe833d568856b1f788da6d4da9c8b6568856b1f7339551b7d3fffa3668f8ae96bae0563c7dd8572aa36fa7fff5622ccdb6542b9235a46e0563c7d452cad4aeee,
  0xb272ff0ffff788d8adc9dbd4a057b10d6065fffa57838dca77b5ad65fe1fffe95e0e3729def7b3597f87fffbc725729cac72acbfc3fffdcc275a71b5546df4ff,
  0x75dffbfffd975dffbfffdadd3fffbcb31099623cc32f50c0ac78fa578e3321baf0ffff46df4fffef2cf9313bc8fb56a5a691bdab66c36fa7fff788d8adc9def7,
  0x1d720158fffea4ae658a3a5ca40563c7dff7fffa89ffbfffd7a6c56ecdc5592be1fd8ff557a7fff648ba7fff557fdfffec917fbfffd452ff7fffbd77feffff6b,
  0xe35cc2a592e458ac78fb591069fffd551e07e34504b922f4a87e34504b92224950fc6ef2aa3c0fc6a292f8f1deef32443c0fc6aa8c30db21a4be3c77bd3fffab,
  0x78ef7e53fffa597ab0acbd3d7829c91a458cbd6b1a77d5588f1f5a46248691632f5b9ad149623c78fb5be53fffbcfb58666152ab2cf87fffb4b00c624a4bce87,
  0x775e7b5ff4b488f0e9ffdcb7c7c2ec77ad409a588fbeadc9b95c51217f8f735c83fbfffd69f1483fbfffde62695db5d2d6911e32a7ff52daae41fdfffeaac97c,
  0xa41ec31f4bcbd5b2cec9cd5ad5b269b4c3fbfffd1ca7d295dbeaba0a73ff449b5183fbfffd907f7fffbc1359b7ca8a97661a7d6f1483fbfffde7dac32e6b13b2,
  0x7f7fffa99978cc1c9f2eb7ae5bc234b8fb9d64ee371cb798e4971f5a61fdfffef3ed76515cbc23dd2211d67b5ff4ba0a73ff66ce5168f3015028b9d63a35e616,
  0xef93f7fffbd7effff78bafdfffeb6bc6d96db3d575aaa3f5fbfffde316f9e1d99aefb5d487112455f462d309423bb6b4af7c444b3ff705402d8d2a5ad634abe8,
  0xa3ddb5dbce96badf5d15d2c35ac563fffbf7fffaa9b195cb5f30b9563358cb1f7d3fbfffd90b3effff5a72167dfffed1ee972cffd1ea9c5435f2fac5206c9c8d,
  0xa028947ae5d0f5f1f423d63ef5cccbb5897b232f618fbce299c704ed8d23d39deae11e8f6e83eb1c65c7d58724fffe8102c375ac563f8d11474b5f15ac563c7d,
  0x6bdd50f27fb25f70d3fffbc5d53fffb474b58c962b58fbc4b4a7fff6444b4a7fff53274fa2bfb3503572d1eea17d3aeb7897c34fffee6ce8e6101363cc3c2a02,
  0x2855bd9470fae865c7d45f6ae1a7fff7826b36f97795d075c7d6b9eaf1927fff780edb2a9adbdcea4ef8ff9a7fcc5758e32e3e8c271927fff4e98329108eedcb,
  0x9d6155c78fb2609bdc720c3bdf4d3fffa25927fff7dbd34fffec97c94fffed18636678d92f8493fffa546cefd45518493fffad30d3fffbd5e1a7fff780ed94aa,
  0xe665cf7d79c9f6b27fff5329d949f84392e43c7d9249fffd908ad62b1afa208885ad623c7fff56222b58ac6bede30a54abd9832c3dc78fabea9fffde09acd96b,
  0xdc1697b11eb1f649fffdc9b9e4bd5aa20192c478f1f7826b365ae7d426b8f1f73092bb8dbd53fffab151a563258ac78fab4a7fff57c34fffef5f0d3fffb38d8f,
  0x58cc78f5fde4934332fa950d01e0561fd4558a71e3d7f7aa47fa55aa32f11171eb5fd1979cbac3d6bfa32dcb5d38f5afea7fff72693c192dd38dbda338aec88a,
  0xbfc3284a46e056b1f7afa7fab4fa7fab12cffd5f5cffd5f5f4ff56b4fa7fab58967fea47fa063c242f92b4bb8907f470a0315ad7f6e72f71e3d7f7aac7afe845,
  0xf519c10f50f72c1fde952103fe7fe85916c7520f618fb97655617fa5d0d711f4b58fbce09edea323b96e7bc1f11f418fbedd621efb71e21ef5cffdb6efc912d1,
  0x2eae9dfdfe38887f799e34f54d05e86b7184af7e87d7110fef5ffd3fdc7cba11197de37fea33825c81ea32043220f7863382cc0b4387fcffdcb07f7a54844b3f,
  0x2fc7ee7fee6261fa40f731332dd43dfeb7feb1825e31311942697bfc08f58fa3fe7fee6262d5a61efa7fb961961effe9feeec3f1e6b4a7d0887f535c4254542c,
  0xbe81a6861ff63c7dfc78f5fd85c45a7f1eb5fdcb7ff8f1e3e9f917ebd797ffe3c78fa71f917ebdea8548dd321fb94a8bc3f858d7dca545e1fc2c78fa15cd61f5,
  0x776111a5881fbc482489c06a39ac3ebbff1c6be8177ecb08efc7e35f68f31e0e82a7353e62fa46bea335980b50bd6f2d4c8f2e62142defff8f1afb27f6b462ee,
  0xfecbfe3c3fb9360913a633af50abf5e423fed63ef083326c116cceb3abd417ebaf88ffb58fb45d090488ffb58fb9373d4d6af055f0b5ed21fdfc71afbff1e35f,
  0xc78fa1fe3c6bef5f1e3f8fd5f5f1e3f8fdcbcf32553995d9485ba997396e5f8fde0e32af1626b0de5588ac65f1fbf8e1fd2b09fcb662d76206b0992cc7dff8f0,
  0x12588f88d92477397234afe5bd381911fd7bd5d9fb190fd5d088fe3f77615d08881fbc70fe816e1b05ab847e3bdfc787f7f1e35f79505c3b08f3a27f097b720e,
  0xf65fd0d7dfd61fdfd635f43fd635f7feb0feffd635f7884d5834affaef3099b586099873bfb277c63695a390a028def3037ebe4654971f41911fd7b2ffac6bef,
  0x71f53c665e358478e071f4676ad95a3f5ba4a9e332f1ac23c7038faf660e6b447bae13f5323caf7be34d7f2a88fa97e3f7d07f732af2e418aeb4018221eff435,
  0xfaf416fedff038fa2a5b358083597c7038fb766395787d4bf1fb2fc0e3ead72d5654ce7ecfd7a99f6125553f75e7ed8517e3f5565f81c7d3962fd7bbcaaaffe0,
  0xafb7cbff815f409cb75c74eec5980b2a7add7f4e73ff02befe071f7fe071f5ce5905c1578e071f66c46e4ad0ba9d78e071f79ffa9779557f75efb7fc0e3eac5,
  0x4bee5ab32dd79db5cb1fbf815f7fe057da3a15b6c8dc0ebfa9cee4ec9544ebed1d088eb646e075fdaff815f6b57fc0afa5366045cb8c208fd15abfe057d5ffc,
  0xfc7ee6044f45e52fc7ed65690044dd297e3f42d202e53bf1fb77e3f7f09fa9e04becbfe13f686771d2f5ae04bef2bb17d6b8fc3d5cb7e5f444f025f64fcc8c9e,
  0x7d93926a712b7186e91f7b938aa68d6bdfe3ef09fbc5261e3896c2b877f8fa226e1dfe3ef3c9444dc3bfc7de792889ce43bfc7dcc089f5a52fc7e85a40112775,
  0xdd7d85f75f5c8fbafa9387dd7dca1fdd7dea252dff7c7d9112fef8fbb30cf96e2cddce722d7f7c7dcd8f8c2b5fdd7d2bfef8fb4902fef8fb2767cf72b4937f7c,
  0xe95d275ade2131648eb23d8556b90c36f4f1f4316e245d7a57a78fa578971f4af0b1e3e95f438fa57811c7dcb9430bfc7d2bc0f1e3ee59703c78fbf3fa27cfef,
  0xa25c7d937b5b82e080a85909ecc22a1aae217b093c7d8425c7dcb5958ca5bdd30ac563faf51958ae436b9025c7d1885615f10bf5f5c80b1e3ef1a338c4e6a33a,
  0x9f4e9db710efee403c47d49f7d98cc16e17cebdf6b1efbb0fed66c3fb41f46c7de031f4af018fb274fa5c063ee74ab782c0fb956b9f0b58fb9b1e7c2d63ea78f,
  0xfe23c47d2c7fff6e0bfad1616286fc478ad23fffae7abdbfde5af88f1c78fffeb9eaf6ffa196be23c71e3c7daddc59bfe861e23c47d2c78fbf3c579dfb8487d4,
  0xb1209f25f11e38f1fffd033310c9496b1f5b6c3d3eabadeb490be0e5f11e38f1fffdeb490bff9cbe23c71e3fffb47a19457b872aa0161e023eb7ffef5782fff9,
  0xd63c7dfb1209f25f5f1d63fffb6c04bf3c6fd85f09f211ebf4223fffa5695299134ba57c3ebc464223d90c6e8981bf62413e4be23c758fffef117c47d08ac7df,
  0xd37bb8614017750fac3fd1bf70c1e0be1e03c47d2c7fff4a6eae6dddd56b5abef10efe51e23e96bffea522925f5f1d63fffa9484f92faf8eb1fffd855845f5f1,
  0x1af738da9f2885fbbe2921c478e3c7fff77faa8f11f4b0fef3c964e8b6fe51e23e961fde71d8b02ffe70e23c71e3fffbce3b1605ffc751c478e3c7fff5168f79,
  0x23eaac0c0390e3f8eb1fffd9050c6a4a87f1d63fffa9df141b88f1d63fffa9958ab21855ae65b504fd89529f638887f786a67729f52c250b0aec9a78f8767cc2,
  0x1f4b1fffdd89e189202ef69a0aa017fdc23c47d4bfff465831eb1fc6bfc9cf36cc96223eb465831e3c7d6a77c506ebe3ac7fff4a91f55606a4871fc758fffe95,
  0x2fe51e23e963fffbb13cfedb1a405afb105500bfc41e23ea5fffa169444fadc7d4890397d7c71e3fffa91203aafaf8e3c7fff762e1d890177b4d05500be208f1,
  0x321d61fd19cc871e1fd4a409d7c758fffec6a325229cee152c0c2b7adfffbde4f11f4223c7d4a409d7c71e3fffa94815baf8e3c7fff762b8f6c69016bec41540,
  0x3fffb99f218f58fadbbe431e3d75a157af8eb1e3ef0abd7c7110fef1f223e8443fa157af8e3d63ee55f1d63fffa04ebe3ac7fff705958cc16dcf0c78f1b58c67,
  0xf36ad5ade5b9c3ed423c7192ab8e3e5fec9820d51bd9bb7f9c18cf8589d60761fff7867d0b677e167f7bebd607727d631569572906bad1bf70103e961fd5f1d6,
  0x2b8e3c7fff6b277c095c71e3fffae6ab2d82eff19d6dfa1fb0c505a47fff6b277c506ae38f1fffde20be283571c78fffef1389cdb9dedc08f0035d571c7afffa,
  0xeb8e3c7fff7838c41480dc2a05fb7c059cd9ec008fdaf3ae38f1fffdcc4666308e7d27cae00452bceb8e3c7fff5b5d8b37cd64b97ad12f02571c78fffef16f81,
  0xb1c443fa1cf1c78fffeec4219292d63eb7812b8e3c7fff77c095c71e3fffa34dd2211814017e95bae38f97fa3169bdd4230f00bcf3a71e36df1fa6cf6143f6bc,
  0xf44bc51171d63fffb38eb16ae7f141fb6e5c0630fc7115fff78c53f469bdc43187e38887f4051e3ac7fff780a3c758fffea673c1507cf505ae65b501b1b5fa67,
  0xdec3e8447fff6ee2e38f58fae78eb1fffd1a61e3c7d6873c758fffef0e78eb1fffde37666e0b4847d6f16f873c758fffed5665ca177f8ceb6fd2fd06f7a115ff,
  0xaaefe51ebae3ffffee549c15798dfdac06355c7ffffda654a28fcc6fd2a4355c687d4c8f2b7b8d3795353dc040fa5efef1d63c7d44eb606949d7bc758fffeb1d,
  0x3e435a584a1667fae8f0ea77247727d1b826a1f3cd5abb698f6ee017f720f4e238fbc135ac86156b996d42e12b87a714fd2a25f947af8e23fff61b654ed359af,
  0xe3ffffe9f9396e9d6def16f8f7dd7c711fffbc5be38d6ebe388fffde20be38d6ebe388fffdcdaabb805fa10d63d71c47ffed1d3d33c109e8461aae388afa99e1,
  0xedd2550300c3fd75c7ffffd8f3be992ab63aeb5c687defc9972faa8ea187faeb8fffffb823a7c62d9c83fb6ff93294892ab91975c6ab5e4c782ee017f61ac7aa,
  0x128be9b2b1878756b00c2eb8fffffbc7337d36099ccc75d6b8d56f16f813af8e23fff78b7c0add7c711fffbc417c0add7c711fffae27964dcb0bf6ba0eb8e343,
  0x88c355c711fffa992f9017e84358f5c711fffa25e3390d71c47ffef413f4fe5103e97bfa25e04ebe388fffdefcaa135a96db18784afa8b3f5d71fffff68fd8aa,
  0xff68f4c2fecd4cfec61aae38d0fa063dec787c80bfb0d63d571fffff7882f8e218d5c711fffa3882f8e218d5c711fffa3882f8e21aeab8e23fff6169ab3425e3,
  0x2a55efe9e5bb8fbd55f02571c47ffef1a6a20b26a5a1ce6b71bd04e97df79febbc417c506ae388fffde20be0063571c47ffe85f63cfeb82ad05fd86b1eb8e23f,
  0xdcc128fdb4a7f02308721f55c7ffffda58aca57dc69bce82104c6700690d71c471f6e9c9194d2a65c8abad711bde1411593803075c711c7d12f02571c47ffe85,
  0xbe006b1e9c7ffffdcd34698bd9bee34d0afe0c4fb186baf8e238fa9e0c8ff97d2869c71a1f720bed74355c714fdc987fcbe943c31f418fa17c710c6ae388fff,
  0xac36f705d3595e384788d6f711eb7300cc7a6ceaefb9b76d9b4eb69d342c9870fb739ac86f5a17c00c6ae388fffd0be006baae388fffd0fbf5739945439a52b0,
  0x95c711fffa7ecca672a5dc7d5f02571c47ffeaf815ab8e23fff79cf20ca4aec2ddfd0d24956beaf8a0d5c711fffbce29f03621d571fffff5136d7dc14e28973,
  0x503616b3a7594ab88fffd15b1d66e5ee29fb71e5cc652ae3ffffed2db908d20ffe3452cfef2908d21bd68971e5cc652ae3ffffed2890b7b6ac83295711fffbc,
  0xc11d310aee9c51ec6057feb9ee83ebae238fb2647d935b0f4eb71a22d45b0929561e355a04971c47ffe85dfa6ac831a5271b9844daa2669a2e52ae23fff5cd1d,
  0xbdc96d87a75b8d7fb28978e5bdc173ff166e23a5037beaae3ffffee0b2c049acbb2fbb301d00ff183f55c7ffffdc165809359705e76624e03fe403f55c7ffffd,
  0x982132d5cecc56908adeab8fffffbbcc2bd4a05449494a83ebae238fb423ae16849494a86aab88e3e873c711fffab90955c7ffffd93413a50b44a2d37998c4b5,
  0xb9366e58b599eaa441f9388e3ec9f994c5832f71a685cc4bd969ba52ee3ec96e6b8fffffb0ca7a441e38aac7a7d6b88e3e8982f639abb315a422b7aae3ffffe8,
  0x24a06520eab8ffc7d949e1ab8e23fff7334d7cc7c6d71a6ba4bcca6c75ab71b2950c3571c47ffec9a4b2269f67a967c476bf5f652a92c6ae388fffd73c711fff,
  0x4aca83adcabec9a4b0cc7ecf4dd01daf7f46bb0b13b2558bad318a1248e8f53303b5ffffd93d760fb60552a0f88ed7f8fb26827984940720eab8ffc7d93413cc,
  0x322a3db5d075c71e3ffb2786ebe388fffd19bd9dab2aac7edac67383ebe388fffde51d96e76ba0faf8e3c7ff64d0ec3122624a4ad24a0640eab8fffffb4cd8f6,
  0x51ab8e23fff4319ef7365380399d9b30c6ee1865d711c7df9e3a723ac7232a0eab88afa23986054cafb8d56c9e1ab8e23fff5247b30b9c355c711fffac55a95d
]
def gemBitBlock13 : Array Nat := #[
  0x672d374a5dc7df8f8e23fff64cbb56d8c6d78ab7d9cc188ce7bcc4b8f2f50e55c47ffef071a76adfa6f312a13f9e194ab88e3ef56b8e23fff5621ebe388fffd5,
  0x1dc9f79c76a654e6547e74f4a90d571a1f70b232374f4c2d0863eb78e23fff7967c177e9fc18d2938de60c0673cf75fb34c88ab88e3ef0ea6717313114ee2ad4,
  0x7fff796a74b439cca4e36db85ebebe3c6bec8506aae3c7fff6f1db3917719c7aeb69406c77cbadca25d394b7bce62cb5990d6de74d642835571e3fffbc0bf5c9,
  0x79f1f4378db1ab087f0b4a1aaae35ffde74d6404ebae23fff780d6b6547fcbe9ba03b0c7dc9a1276465f4a1eb03b93ef56ab8f1fffd905aae3c7fff6404aae3c,
  0xffffb2141aab88fffde399ca572d280d21d063538fffffbcb53a5a6cca4e37abd75c47ffec9826158d6de74d6417aeb88fffde74d64f0dd75c47ffef28fb32a8,
  0xb88fffd4e6060c8baaf88fffd19cd711fffba6ae3c7fff43158d6daae23fff789635b7ab55c47ffec82d5711fffb20255711fffb59ecadfe389414bef002076b,
  0x3a3a14aafd4648cee22813d343d7c6b0fbc2ec23a14cab68a53d379f1e3c6dae238fb09ec0d293af6b88fffda246a1963256b9ae23fff58d34ba86588df8df8e,
  0xfff641ead8e23fff50d5aae58e80d45d6c71fffff78e648d6bb070e1398a7a0f8ac08d058f2e3e925128f5d5b1c78f1f79876acf15ae5f8d9013c8711fffbcb5,
  0x1eaa71e3fffa7e129f83cb0792214535b787666cc89771fc9c91f8fbe30dffe847d3d011d47fff56a7093809bf09fedf62145237ad14a7a50810abf6404d8e23,
  0xde04b060b7aa71e3fffbcffc5331b07d46c688465c6b8d72fe1d34fde1034e343e894e23fff4fdb23a5d4bb8fb2025388fffd907aa9c47ffec851754e23fff64,
  0x69d9ccf5abecd8ad2a532a0d84efaf8d61f736523ac2b25f71a69d82fb5d081e28abee6cb70977cce569ac3c47e369f6ba102157edd54e3c7fff5e5d538f1fff,
  0x5f1e3fffb4325f1e3c7da711fffa3229163c47e36eaa711fffb7571b88fffd7975c6e23fff4ad518ae8a9dd1e67adc7d7a6c569529114a7e9df5f1ac3ed1d022,
  0x8fffd11cd7c47ffed04735f11fffabdc97c47ffee4135777674b7057861b8d0fb9af8f1fffd002429d98a5f51e3ec9b41389d2d57ec999f118ad6b1ded2aaaf3,
  0xd849b02a352711c7d126c0e906a4e238fbca92ed192a30dc471f4adb2c78f1f5b9af88fffddf862295f6f1c6143e1a588c9fffaf00bbdc211e1963271f579af8,
  0xefb48b1e23f1ab9163c47e36bf7b48b1e23f1b22c78f1fc69dc47ffe9c7e0b58546963d78fbbb63a41a5a2afaf00bbdc2d95197d78fab3b88fffd5ec6e23fff6,
  0x34d1b8f58fb5b2a3fe5f4da47618fbc471f4ee238fb4bab6221cbf1fbb23d9b2f0a3ef7936205adf8fdf63b88e3efb6c6e238faaabd8dc471f4ee3c78fbc47ff,
  0x46ab50294f4da557ee0a93609c079a674da557ef326a22442faef1a1f73389919cf00fac86ce03ef1affe8dc6bffb45699a5291fde00277e423b0c7df8a249ee,
  0xec471fa4b15fe3785c544fa86bae235e5fffbb11d6ce64b15fad93135e293483b11d8affff7826ab50fa41c9b71b93ad9cc962bf5bedb11aeb1fffdaca6667a8,
  0x88d797ffef72538fd258aff1a8985d88d7971f53c853cc249efd761268b1232fa01148d793efb6c46bcbfff64ea4a3b11d8ac7fb2789ba86bd88d797ffec989a,
  0xfffbcf33c8fafd86362bd88d7d555ec56387ffdea1af62b1c3ffedd4b59df7994d8c72f39aca147def21fd500bfce03d17fffdea1af62b1d6bffeec46b87ffdd,
  0xee4fb4bd435a46bac7fff4aad48d7beb0abf523c797ffeec43e1fff5aa910aef7246f39172e1fff5aa9a5bbdc91ba0e45cb863ed2a76acb31920d7bdf6d8ac70,
  0x55691af2fffd1987270ec4615e5c7dbbac56223f8da5ea1ad235e5fffbf16db664b0eb5ea0b954477c7afcb8fbca82634884308ef8f5f971f4b398389ea41e18,
  0x53c87739fc27f57a844adec478fa4624ab08c2badf648d797ffec80b3e99ca54ef4e8911fe839001f5ffffdbc63105798c083e94291dcabed2fb246bcbfff695,
  0x8ffccae777cfada5ea1ad2b1e5fffa9e6b29aca0780695ae807d7ffff6efc24e2b258df797ada5ea1ad2b1d63fffbc2a67ae0d2b5a563ac7fff79935133f211b,
  0x47c04462b5cb7b4aaab4ac797ffed18e4627cca4bfc6d2aaad2b1d63fffb824511edbd99d27cc0c207987e9e5fffbce82435a584a1667fae91882208c2bad298,
  0xbfff535948cc31bf1975ffffdcdc892ad292ff1b43bcbdf111d63c7d4d66878cc31bf19758f1f7d921f97ffed24546432adf64ac797ffea532423912bd887f79,
  0xb197bca3e8d456b905ee666489917f8fda2385f3fec0ce5a86d46fa90f87ffd487e5fffa56104d1c81a441f734dd358ca55a21ad235e5fffa958f2fffd5a563c,
  0xfffbced9b15663862679550761d4803f4223ffb9306594b2679675b58a900f5ed63ffa497884d59d687f5d24bcf3edd675a1fd7521f0c7d48c2bfc7efc503056,
  0x51a410d74e3cbfff4e04629184311a71e5fffb74f976a9970c30c9eb8af7a73d5b3b8560469c797ffef0c64e85f34808d0e078afd6b9cfbdfe46906401fa11f,
  0xb3f1aeb6f6b3ece1d890a1396ea7a11840ef6bafb2acbd99c35bd8df6b3ece1d940aefe5ba9e86403bdaebebc14690435d38f2fffd9709f04ca50327ae326bcf,
  0x5a4961b07cf660943e5eb5e0a375929c797ffebc146ea1ae9c797ffef2ed4190327ae32695b6ad93ada9f6b0234e3cbfff6f8adb56c9d088c08d0e078afd6966,
  0xea2e965432eab8f2fffdbc7a63a152c808d0e078afd6bc2f6f22b0234e3cbfff7d64e4db31aafe364d1b665939aae6455fc6e6593f31aeb7e37d64e4db0a555f,
  0xf6fa6db2742230234381e2bf5a372643bd00c9eb863ebcf52ca8b5d571e5fffbfaf0137e13c64d7a11100d6d7ffff442abca896326f8cab732c9ce4ab1aafe35,
  0x742a04a6b0603f423ffff44cb7c62e3788de149e9100d7eb15ef732cec956355fc6bd4b279755c797ffec99d8556bc553d480863d715d7d79ea593cbaae3cbff,
  0x234e3ac7ff6e4acaa56326f8cab4aae9f2188d38eb1ffd9b537985dcbc2355c70c7de399be9b3fb3318193d71956bd4bed4e3cbfff65592a70d6f637de03548e,
  0x8117b72ba243a900ef63ffff73009a6991656a40122ad430d3d0c87d0274bd435d38eb1ffd459c759d561755c758ffea2ce3ac96d61755c758ffe8cf755f4b90,
  0x2fa811e2bfc6d64520d60681538f2fffd6aae9c797ffeec59ec595e6a8e77c83a55a87cbd6e7c8c1d258ca5be2bfc6d2fb538f2fffda5eb2538f2fffd4edbac4,
  0xbbd918dad32e343eb0ff7826a04e5ba1fd753d53980829cf05f5ef8daffa5fe3f88f5ee5fffaf43257abc99571b58a71fc47d6fffdd9f95811a75f58f1f696b,
  0x55797ffea4fdba78aaf6770d6f52fee4e23d7b5ffffdd88499b777152d2887a2e3fd0a3750d74aeb1fffd0a3750d7555d63fffa201ba86baaaeb1fffd728b47b,
  0x7157a4b70fba6597b2a2bffb11003e2046b6b1fffda5ea188d55758fffef7e85989202355d7d63fffa8a18f58fe372c18f58fe3428dd435d2bcbfff428dd435d,
  0xa65c6872ffabf4ce798bf74863df84e5e2847f02bfc7f11adac7fff57e99cf317ee99693f09a0afc508801f10235b58fffee9be3b82728d8af72e2046b61fff7,
  0x989202355d7e5fffb4bd435f5d5797ffed2c821afaeabcbfff697a86ba5758fffef29f52787626d93092d3cfa811f2f5b4b2086baaaeb1fffd728b47988de1b5,
  0x4aaaba5797ffef29f709f3548c28bb7d408f111f5b4bd7720811e2bfc6e68a22e4188fada5ea1ae95e5fffb4bd435d55797ffef189fca4b1721588ffc6a33b85,
  0xa6a9028eead9f7840fbe1f5c4c11dcd378777c3ea3346c689e0b43c46b727dcc45fd8602e4188fffe81ae1c5f40a455906b035aaba5797ffed288bdafafcb8fb,
  0x418018311fffd9b399b6583c36145cebf9202a627ac9b92fcbfff72f2ce00d215fffee697bee5c05c835fffee622fec301720d7fffae27991dcd3786b87256f2,
  0x39607a21ffd6d78a329ee03e5b158fb0ce62cd6151bad0feba054af2fffda5f6a5797ffed2f59295e5fffa711f04d6194094c8300306bfffd388f826b0ca04a6,
  0xdd8adaebef9ad24b981c3200c684478fb9f01ab1ad61cbf1a146ea1acef2fffd0a3750d798f2fffda7daf606d887f42851ba86bcc797ffe9601808d3c395500b,
  0xa9062bded2aaacef2fffdccab9907ac78afd6d2f50d67797ffed2f50d798f2fffd7b208aec04feb55f85ee5413bfffef16f26b66acab78e66d842ab45eb43c3a,
  0xe09a2ed7e843007cb6bfffd6aacef2fffdcc0d67797ffef29f3dbaccc754e65477e5fffbcc967bf5235d2f8f1e2bfc6e7b16579aa39df2e510d0f97e37890425,
  0x87fe9f83cb07923ee03bd887f42a6410c00c6857fffb97fccb801862bfffd23f4973b5fd8600f96d7fffbcf3247d176bf421803e5b5fffe896a4b58af7aab4bc,
  0xfffb2754d42418610c7ae2bafa25df350e10c43e3eb8aebe811de5fffb942cb801862bfffd0a9ea1801862bfffd0a9ea18018d0affff41f88cceb623f61803bd,
  0x8563886b4fe388f1feddb5d0f93635fea3346c689e0a04687e388df44bbe6a1c2188a7f1c575f435ed7c797ffefc86b3bcbfff7e435e63cbfff5547c87d7f1e5,
  0xb0df506552a1d5feaaa601946c689eba404687af2afbed0baf58f15fe3435d38f2fffde789f3ff08c21ad3f8e23c7fbcf13e7fe10c46187ae23c7fb9db67994e,
  0xc7fa94ca5db96d742077b1dfdacfb38a4d492ee7087c40ef6bafa1acef2fffdbc79d561d457dc63202b0ba1eb88f1feaae66ec273298c327af2afae6ab03c0ad,
  0xc4f0547430bea6b55646a308191d0d24ba6c824cb6ca38d246dec9f1db67ec7d487103757d929c797ffee759cf13baeeb9a94320600ef63c7fbb342910c01b63,
  0x9bdc6907a47fe3f4359dd63c7dc15f5dc7e9de5fffb27632308d2def88f1fea766e48c326f8aebec999f52f5eb1e3ec87797ffeec5c29ae67ab420c018358ff5,
  0xfa190fbc7462cee1fff6fa6d59bcdf2e7ba7a111ffd113b87ffddd9535ed3f8e221fd3bcb8fa0477971f73040beb1fc7ee64877971f730359de5c7d93f5323cd,
  0x8a57f8d0bc223fda7daea436c43fb2638f841845bad0feba30ad6223f8d3b863eacee18fa22770c7d3b87ffd59dc3ffee5b69e035905623e95a654a64bba5325,
  0xcce583d40a270db5875afffb27cc5d7ad7ffd55111adcc0eb0eb1fffdcc0e490eb1fffd7b2ce3dd2bd945052ff1a1fd447fff6d843ac3ac7fff72ef294fb18d8,
  0xd62b1e5fffac736112f1fe9b5f7835af8e1fff7ad63e8eb58fb21d6b1f7ad7ffdcb75ea3215d68cb1588af8d0e4188ef475afffbec3ad7ffdbe90eb5fff462ca,
  0x21f63cc82b1e5fffa46427ec1aff696d4385ea73a417c7971f5323cafe7faed2e6aa70bd4e7482f8f2e3e86b158f2fffdefd9b3136bf4d8ff30d6be387ffd550,
  0xa4b96c47ff6490f2fffd551e76ce2b029bad41b635fea79eac80a6e5946d8d7fb22f8f2fffd1a490f2fffd90563cbfff4b330927bf5d1ed4ca948bd9fba4bf43,
  0x2e5423ffff4ee7daeca2b9ac48233b8ff4a07a4b96c47ff686c3a962cd158f2fffd8d6b226ca2b9ac48233b8ff4a07a4b96c47ff635c9b670598f0233bafd1e7,
  0x2e7e98e26e552df1e5fffb41baac797ffec2f6de6565a4437a11beec541baac797ffec8307258f2fffd9c720c1c963cbfff643cbfff7e5026049cb406ee11716,
  0xfec9abc9daaaef3fd76b3b109b24aec2ddf6349255afb58797ffe8d58797ffec83561e5fffb74fa60fa0193f1e5c7deab1e5fffb6c99f8a32ad1baac797ffed3,
  0xff619ddb6759156d93fb5480a8bb1527558db1ffffb26e4a26c92bb0b773a492ad7d7b32c9d96946e255f5ab17b235393299b663d8a5f9ad58f2fffd12ac797f,
  0x15ac65d7bc3ffe85ac3baf5190ffc6afa88f111c68721949a32fa88f111c6c9d7179e6465f511e32e347ff0cb158cb8dbe1587a3cbfff79d90ab881f0b1b63ff,
  0xfbb14994d7838ef8afebb15d2c6bef93e894b471dffa0455e3bff635022af14fde18fa3863ec2e0395088e3f73e0e3187171fb5870c7d9243863e8c8a5c31f46,
  0x5fe3ef1755d0f1fffd1b14994d7838efb6762ba587f5153aae878fffef1715e762257c31b4529e9b125a43fa760bed60478e3271afa94ff0c658f7eedf1963ff,
  0xd2ba1e3fffbee48fa587f616c5752e3e9d988e4232f5ac6b90cb7bc5d57423fff78a415d08fffde211857423fff78c5ae1bf7247727d93e3b3f8529fbc2162ba,
  0xc0d5e87cbfd9047d0f1fffdefd9c31fce6b72a66242bd0f5fff5695d08fffdcae4266e0bc0cc3dba0948fdac088e24fffff7b7e9c691f4bdfdcc4721197adef2,
  0xfec82ba11fffa2569a2ed53143530158ad8faff7bf670c7ad9c8f98dfa045e878ffee70ca2ed9c8fb900a2b4ec78e3461588cbf1bd47d0f1fffdefc9a5ace54c,
  0xfff428aeb0d7ffff79531fa4232fc684ae963fffaf04ae963fffa56b2153d61cbfff4fd21158fadeaba11fffa17aae847ffeb96d72a736c5090d81203d763fff,
  0x66cb37f72a03d7ea43fd5d08fffd112462edfa5de975fef780623e963ffbdfa6c76cc2e76fd2ef4b1ffdcd74b1fffd485881c188fa5ac7d095d4bfff5e095d4b,
  0xdecf7d5bae9418c123c7fff462d36d54ecfac2d7e963fffa766ce9465eb462d36d55ef9f585afd2c7fff6b276bcfd6dca0cd219b557bee5407afd4bfff43ef48,
  0xac7d6a83f4b7202a80add3edfec3241197e35e5d3d0f1fffdef2e9e878fffefd86ba7a1e3fffb59e9f55734118fc82835d048f1fffddfd86ba7a1e3fffbb3bc9,
  0x463246d09e77f84ec0aafc08fa186037c7fff58f6553bf430c32538d7d93b194590cb7abdca878fffe8a588cee22ab6bff35d711bebffee64774a934cc46b8d3,
  0xa753d0f1fffda7b807e961fde53ede6028c32c5a21fc6d494f43c7fff732405a31d00ea401fa58fffed49b5fa1e3fffb4a936bf43c7fff579d0f1fffde316ce5,
  0xfffdfbdae9ea4fbc8532a1154bac0d7a5ffffde4299508aa5c31ebf4bffffb4f700f727dce878fffe9d9d0f1fffd3840e432fc6ff418d8f1a1e23fda7a1e3fff,
  0x70c4af311b58a9758e026bfd2c231b1636e55f4a8f25ff4eb007fa5d7fbb23d94759ceb6236b14eb1438743533c27c86af65b62424d556de429953b3eb01fa5f,
  0x4e71ece54adea0752f21e12be3fde0e373715037fd3af881fe97ffff7379578ca73e9e798d701d4baf8fe398ffead6f1faccb935847fb152ebe3f884ffffd29b,
  0xbc8532a29fd3af63fd2ffffef214ca8a7fd3d7b1fe97ffff5ab598d8f954ab1e6f55759790fe3f6b1ffd734b9fa738d8e85c9bea48a975f1fc52bffffae6973f,
  0xa889e58febf4bfc7de4299514fe9d69fe97ffff790a65453fe9eb4ff4bffffa254ccae765e5c9232f5bc1c76c5400bfe9d7c47fe97ffff66c393365e5c9232f5,
  0x32059b3b2d525474f09eb15fd2ffffe9d3e316ce599eadbc06b2cde1b967d62bed75fef214cabdfd3ad3fd2ffffef08fb90a65449ff4f5d3d2ffffec9e131c2f,
  0xfff6dbfcf885afd4b8faf2e9e847ffef214cad168b87c7daffffe955b18ded5a568b5d3c878fb5ffffdef2e9e847ffed3bcba7a11fffa337b3b56456f155f575,
  0xa547a27d0dc69c075f7fa0f8ed7ea5c7de53eadfe2fc685fe83e3b5fa971f52fe85f7253727d7f6e8ef753727d3b3e007e97ffff7e7c407ea5fffbfd3880fd4b,
  0x788f443ffa1e9134a5f0b5f443ffb753d08fffdf0a6f711bf4bffffb260f221533e359affffea67024d0a99f1af22ffffef7b8d3d4bfff7fcf8d3d4bfff4b34,
  0xbc27d9815c6e54fd7c6826bfde576660533a703c6fabfd385244e16ab5fe95a2ffa75f0f8d2ffffebcb9090cbd695a2ffa975f5f1e34bffffbc27c33f5b3f4be,
  0xff512e432def1a072fffdcf8d0397ffea43fd430ed61cb8fbc8532a767d69e34bffffa54abdfd3adc60e5c7de42995a4b3eb4f1a5ffffd2b49793af87c697c7f,
  0xdab1f08cbd6ec597e43335b5278328ea5d3654cee697dfaa57ffff7d8cc36b679634865eb74d9533b9a5f7907f6bffffba6ca99dcd03a7907f6bffffb767423f,
  0x96b952c6bee7423fff7d84756c9f6197e37c29a2e372ffffec3685c2ec04133e372ffffec3685c2ec04133e3b917ffff6a4f0651d4ba6ca99dcc2fd52bffffb0,
  0xab4af4aeb52e3e86b58a2de42995a4b3eb1852ffffef214cad25e9d630a5ffffd24a3609ba4a9f8c3fa5ffffd784652a971f5ead43c7fff513e72c6a58fffefb,
  0x1bfc32fe90ba7a1eb1f6847ffee6a11fffb0cec0ab22ada77a71d697ffff7e7c7ad2ffffeb9cf8872a971f56be981660cb7b9a878fffed6a11fffaf56a11fffa,
  0x532b0b8a2a0d7f6b50f97fb2f652d6bfaaa3d6bfb435ffdce86bffbdf9225a37f42194243de96b1f579d0d7ff61b429b536b9ddf6f7a7e21d7a0c7db6efc912d,
  0x824db7541299f56bc57eaab6df484447f1beea7a110fecd84447f1aff1f91311defbaabf15887f6877fe81313332e7bace4fa9d9197d00aaf4b0fed6a1dffbc8,
  0x66dc41969b675b5fdcbcbf0361ffa99722b74a96fc9b10fefcd75ba58fffec9f35d6e963fffbca3ecd7de5eaba8daca6667a8658aad40aaa70bbd8df704b1095
]
def gemBitBlock14 : Array Nat := #[
  0xa06bb3d8df55479db02f3adcb6bfd691b1aff56bc57baadbf6bda57b1aff6f96222bfc6fba9e846faf2f3a5afffaf2f3a58fffebcbadd2c7fff7817ebb3d887f,
  0xfb599b5db96d62400d8d7fbbe9a15efc9b1aff492dc6f6e2c91760277774fa1585d6f63ffff7fcd75ba97ffe8dfe6badd4bfff55479db02f3adcb6b0b48d8d7f,
  0x2a9b95cb22cd72cc457ffd4ad17a5afffbc5762b964495ae5988afffac7d555971ba6111971a46698443ad7979d07ffd7979d4bfff7bcbcea5fffbde5d6ea5ff,
  0xa74871fe97c7fbcbb53a618d2110eb64cf152b45e83ffe9f809eacf9cdeb671c32ce5bfe83ffe9f809e5afb52d6cebafa5bfe83ffea2f4b5fff7345e96bffef,
  0x187d2c7ff73917e83ffeb89bfc059832dec998261e722fd07ffd2f39c8bf41fff76188fa58ffea568bd07ffd4ae45fa0fffa1a5722fd07ffd9b60b6512733b95,
  0x4bfff4ecea5fffa76e552fffdad41fff696b6ceb22949b9a2f41fff43cd17a0fffa04239784f99d4d8fe9a58de857c7d2f398f5f41fff780a7c926784cd7493b,
  0x2f6bd88fffda4b80faf623b5ffffdf9af6bd8f1fffde065ed7b1e3fffb552e36cb8197b5ec78fffec33ee0b5ee55f686ff683ffefa0fffabf41fff73a0fffb9d,
  0x5a0eb98cf7ffffbf35d363c7fff45df653c7ea91dac78fb59afd4f9d027bcb4fd8f58fa9d9197d3691dc9f6d83165d7c6fcd7b5ec47ffef032f6bd88fffd9703,
  0xe3fffa9ef0dafc963c7d4c84c65d7c6ae9b11fffb9ae9b11fffbf35d3623fff7e6b48ec47ffef1cca6d917c962079cb9de86bd44e77513ebaa47727de7fef59a,
  0x7f7f637fbc46d3663cae682fdaf7c6d863eb1c261cb8d58c86b69b11fffa753623fff79d4d88fffd784cc27aeb4d8fffffbf31b5ed7ffff48d8e13ebc6f3a9b1,
  0xc6dc9f735ed7b0fffb59942fb929b93ef11b4d98d39c2ff2fa50f1b618fb965ed7b58ffee6bdaf6b5fff58c841eeab68e73cf5975ed7b5afffb4b3faedafee5d,
  0x1111ebe369b0fffa75361fff53fe629e422b1f735d361fff6835d361fff769dd215c30af7c6dac7ff79e262edd8471b9ae9b5afffa1e6ba6d6bffea48e17daf7,
  0x4a063d20c7fdd2fb62b903ffea60c5c46d70f8bb9996b0af55e70a43d7b0c7de03b518fae6bea32ae3444443e34a888887c6a66656432f5bd7344222235c6951,
  0xe21afc96b1f73f91affec9b160fb6578ce9e55963ffb9c920d7ff4ad674f2948b1ffdcfe47afffbce2c536f9187a99d2d7543d7739241ebffecb752e36cd8191,
  0x7ff68c7afffbce79e0e392e1983dc9f689cca53d2a41ee4fa1641ebffed2d9cb727d3b9f6bb28ae68ee392b37840f727d8d726d9c151dc7256628207b93edf39,
  0x831f4a86321f4a862be3e95f418fb0a8687d2a188e3e95f4343eec2b89918cde0ab2f20701f53b232fa6feffa1e1fdf52e3e8dfe87ffda30fffb4635ffda483c,
  0x71049ff12ebae2bd8fffdaeb4cc47eebffbca3e12170defb1b594ccc20cb155a8141bf75055fa99e13e4357b4c252f92771b64fa18fa543971f7618fb418fb0a,
  0x15ec7ffee6a0597264d27fe25d75c57be3c7df8e80b3518875134f71975d71938f1f69e83581f2007ffee92f01a9c22c6418fe35a74f41ac0f9003fff40a19e7,
  0xb2f56b3946555c517ffee6a055959b5a5efea5d75c47ec7ffef0f16b2999b262ab5b86fee4a0abf789340597aa04f6519557145fffb9a8165efc3a7fe25d63f,
  0x38b9430a91b9a8165c992f7fd72ebae23f63fff58c4728a709448821f1bf51fffb9a8173ccbdff12eb1f88fd8fffdf8e80b2f56b3bd8a9758fc47ec7ffef1268,
  0x744954d5d2eb1f88a47ffeb188e6b626e89cb49a3865d638148fffd3f2764e97a7b9a8173ccbdfd4bac7e23f63fff7e3a02ca5b37b152eb1f88fd8fffd02cbd5,
  0x7fae801fefc5b639cc835d6ece6148f33c0358fd7407ffec2d894604dd28154d1c32eb1f88a47ffe95d9a5de6131e8173ccbdfd4bac7e23f63fff58c4735b13,
  0xfd0273575504a39a784baeb88a47ffefc7b11ce76d984a15041f6809cd6cad12553574bac7e2291fffbe835d75f007ffee651d29093b399eb57d238642ac7223,
  0x998f3a787d12f1bb02d5cca4ad93f252c818701e2ba7ffec9f9296766d8458c831fc6d3dc042d21fda0d75d7c01fffa1406995735508478eaace97fac7e320ff,
  0x3f63fff40b2f7ebb8aebae23f63fff409e4f392f1c57ac2a75e7c7d6311e4f392f1c57ac2a75e7c7d6312eaf98452ab495f4a787deb756c64775d6d2db7cd8f7,
  0xe81658559aceaba7af3fffdb8439ce6f3d54daff1407d3fff735ed7c01fffb6d9d2174c73c67e8ba11907ffe9f93b39517b6e6baebe00fffd02e799bb8aebae2,
  0xdf72e2b8ae9fffb97bf567c6e2b8ae9fffa9dabd53d4382e673771a9eb71f40b9e66b3e9e2b88fa7ffe8165ead65efb9715c574fffd02cbdfab3e9e2b88fa7ff,
  0xa67b7d6914fea5c43f2d8fffdd9a4ed8a533dbeb48a7f52e21fea3fff72df16517f54e631d22813f887bafb1a76d7c01fffa05cf3359d38ae23e9fffa0594b63,
  0x9235a43d4e21f11fb1fffbcca7c41312d16765cdd988c32971fc6815c2565692bc6e9effef3ed7e5be13fa754ac1216fad229fd4b887d7f63fff79f6bb347314,
  0x41fffbf6bdf0d690fef21e4a954fcabfc468483fff733f248c497ccbaf8d0abe00fffde7dafcad30fc8595423a5235a43d4a711fb1fffbcfb5f95a61f90b2a95,
  0x92ceb3e3ee651d28e4277998f3acf8fb99f930e12ad2975f1b0d8efc4311ad803fff61b3dff10c46b600fffd86d9fff886235b007ffead6da44fe8bf19711022,
  0x87ac561f40bd8e72f5e77d8f5d05ec7ffea6ed9d9ec550af5a7b63b5ddc7de39f65ebce48f11a0bd8fffdfc435d57007ffefcec40a9ce652e3f8da3a39a04efd,
  0x3e77d8f5d05ec7ffef01aeab803fff68e8c79ecaad8f3a787d7270998eebcea5faeb03f63fff5c9c26619f5e727ed60523fff72f5e752ff11a1271e3ee569d2e,
  0x209597af19f03ed60683c7d93f3ee262b6ac4746d5debd438410aad257ed74f0fb4cbd79d55c6494b8fe3730eca47c67fcbd00e7fffa1e601b9ff82fd02f639a,
  0xaf09473409b8e4472730291fffa0ce569a470f74fffd02f639a3e77e1f1407ec7ffee67ea566384871a0bd8fffd026aa4b3cefb1a0907ffefa2eab803fff5c9c,
  0xd4cc082661840fd2b3e3ee5ebcea5f03417b1fffa05ec2cfb865ea80fd8fffdce1b7b86543417b1fffa593f5c88085d3fff7b7e72c6770fd857ff7bd55c01fff,
  0xc1dfd66a7b635208b8fa05ec7347cee903203f63fff409fea3e77f2e06407ec7ffe8e7997b6f0a7daf85af7b1fffa05ec7347cefb1032120fffd3aab803fff43,
  0x720fffdcd32f24aa79c994a92ebe372d7007ffea678827096af65acb4bff7be3c7d02f639a3e774d480fd8fffd727246c5286e17074bd480e7fffa982aed9d9e,
  0x173d8393ceeb0a8690deb68f9dd2064b5ec7ffef149a947ce12e064b5ec7ffe8cc19a3e77dc84694b8fe37d8e68f9dd354b5ec7ffee6e6b66f27e79a78cde11d,
  0x52d8ac7d9c691fb10fe95e00fffde58276d9ec833727d52d6958fb266a7983347cee1d06b5ec7ffee70db9dc3a1a5af63fff40bd8e68f9dd345af63fff53055c,
  0x99e13b78247ed7c07bdaffff48d74b5ef621fd4cde46925ffd054e732908fadccf5a8241fb5fffed653333d432c556a0529c2ef621fde73cd64ad2a77e5414ba,
  0xb7391e37fffb770a3c6ffff463f11afac3ae0087f530b110f017fffb367ad9cd52afac3ae00ac7dbba5e1fb5fffe9c9cc8bcb1e1fb11e3eddd2241fb5fffe8e7,
  0xf7fd206b88daffff7e37bfe9035c46d7fffb0b8afd556d2b725329e03e236bfffd2ab5235f0181b10febdffd880f88daffff4aad48c3485fa772b8a242e1bc91,
  0x40bfffd19fca9aeb3e007fef0a6b4633bd8255fad1892d01554ff557890420dfd4ab8e2372ffe955ae6e56993621fd3939914a8d3f55f1f5effa407c46d7fffa,
  0x874b1bec563ebdff0faf1002ffff5eff86203e236bfffd7bfeb5880f88daffff462cbc4c41ea0517846d798ffa901e388d88f1f7d6ee78dfffef0a6b44e674f7,
  0x825f88daffff7e2db1d9a42badf58af1bfffdcb46ae685d43debf1a158b9b640e36ffff42c6bff0d237d8ac7dff87c0c3fed7fffbff5af858e23623c7de653ff,
  0x3ed2f0e96bdec43fa73c3607d951505481787fab10166702a2ab3488901a92b6ee275f1bfffde19f5c552f09eea011f88daffff4efc4ebe37fffbca92dc963ba,
  0xbfffd7347cefb10181b5fffedd97af8dfffe9c16b2aee1fdafcb623c7d0b94e0a751d081fdafcb6be3e9d08e0a702a2ab2c9f8ec2f8fa2654d567c612fc46c56,
  0x6416050478fbb2e6950b9c9e16b1fed7fffbb2e53ea17393c2d63fdaffff5c8573bb2223a5aebec43fbb39d257d5de704fb5534b5ef6bfffde704fbf974b5ef6,
  0x6bfffdf12db232a7d42e3302be1600d88f1f5326c593cecbd9dcf6e9438bd254be1600d88f1f53270a6b16cbd98eca0b292a5d486d88f1f58c8c0a3348fc7cd9,
  0xdaffff7e68b4be1600d88f1f5abc3a5af7b158fa7e780a15679a79dc31125495ad57347cee9018ff6bfffdd9729f50b9c9e1600daffff765ca7d42e752f85803,
  0x4b2ff709f75ac95132f091d5377dcbffae68f9df623740bfffd2b4b44c5823029bfffd0a576767b4d0a8754f6c76bbb8fad57347cea00c7fb5fffef6af0f80c0,
  0x5f598e02b4aebed7fffa597fb84f84126817d66380ad237daffff4fd4bbcc263d2cbfdc27c209347e8e78e02b48df6bfffde714ebadc69146331c2577d88f1f,
  0x4b1c9a39a85ce4fdaebed7fffa597fb892c726817d42e727ed75f6bfffda1c20855692bf6ba787d2cbfdc49639340bea17384bed75f6bfffd2cbfdc62cda9c9a,
  0xc6770e5705fffeddc4ae37fffb260d68f27d015015417fffbc325a02aa9fef2eca262f640a05fffec9835a3c9e052a02a82ffff79c76633bd8255fad2ce584e2,
  0x7a6cd8c85bdd56d73cea00d636bfffd3f3c0599c1ecc5719f0c44aaa4ad73cee901ac6d7fffa9d87359a444aaa42badbb2d71bfffda1c209992207f6ba787d72,
  0xe61648f321273b8e0f662ab3e18a69ee3ee67014de4cde616fd556d3aecc0548ded5b99c3b1ed9ca153d179dc458017fffb9859e392d07b34d66914d5495bcca,
  0xf4efec3f72ffe855a9df30c0fdaffff4e4d2c31fb11e3e9c9a5ac0fd88f1f4efba5ac0fd88f1f443a7c5c483f6bfffd4ca41fb5fffef1561fb10fedc578dfffe,
  0x793b4acefa04594b55efb5f03f63cefa578df1f48c0d36c0e3eb91f4fc7efca22bcf8fdabe1159df4af1bfffde2aa0f025ffd4d61fb5fffe89c6274120fdafff,
  0xeb95aeec8851d2d75f621fd723c27ffa05cf33753311f41ffef01355285dee94e37ac3ffd9320ca0fedf6f65aac2a228f277b15e63ec99063dfad3ede2a47994,
  0x4414bf76e6db805b79b3a7a675f62b1f78e8c1bfa9571c46e5ffdea7e197d1237d887f7dadbac9eea5f03b1ff72ffec99a9c9d92a468149c53fa5f03e846c563,
  0x9330b6e84534af09ffea2a1a1b6ea1dc27ffb75335f09ffeedcdb700b6f305f4cebec563ef0f14ac302ca9d57fdccac62a7767f86c53d3d7a1ff62b1f4ab5452,
  0x4f3a9fe78fc6e622db3c55ecc71c3efd1206953f5907ffedc91796b1c7fff64f8a7362309dbfc30fad02d36f30b67246812c4465473948081a57848fb99c0537,
  0x3c0f90c83fff788d8e1297f7d6e4fe23e4320fffd63623ba718cbadb84bec31e1f1fffd848b6cf152b71d49e3ef34f1b952f81e1c83fff7a2bfb379ecc765154,
  0x3b1eb1c7fff64bc76c1354462493b1a1c7fff70494d08d0e3fffb727ec31e1f1fffda524a05baca682050eab34fdc85618fffdce95fcda813d0c4e6a4a43aacd,
  0xffde59f71bf6e847ac4bffb751e1a4fff6972df11ac642badba9988d27ffb7063c397ff76250bafb348188fadba423c397ff562307b751e1a1c7fff426846249,
  0x7d790bdfffbc05310ca2d277fa8e9fd3c0f90bdfffbcc4d944328b49dfea3a7fa01ebe2f7ffef38274a94b4de1f20e4ad723491f43a11eb48fa3faf1fb478693,
  0x5efffd58917314ec47ea9617c683e69e078e2f7ffef01aa53b22d179470a1638bdc7d0c5cd2c469dfea2828078e277ff74dbd9b67bd189b4d29355f7be1d0f9a,
  0x412817bda47da53aeb7fffab122e60b43130bd242ff51f34f03c717bfff56245cc16862617a485fea3e74be078e2f7ffeac48b997923f54b0bfd47ce97c0f1c,
  0x6603d87fc9fffa2e1ee02103dba4fff63f89703d61efffd4e51b204207b7491f63e83aeb0f7ffeb6a3ee804202b41b92697d435d6d335d6ffff532153b16f64b,
  0xe537e13b037ffd8ff4e23c07bfff75316c45f9d605ee86f5ac51b0e7be7973382f75256bc05f62a9ffcf31b19890bdbdfffec9835d342de6cd6b2db0707b315c,
  0x9d01d2e06fd6ffff492bd263acd7de6ecdf33ab8cd3c2f7fc9fffb4efc059b351d6b7391f84ed35ffdca97c0f01efffd24bc1354c01257722c71abb8fb9afb28,
  0x255b4ad247da1d491f6ea5c1aff1fb7533906bfc7e9523016b4782c50fb43a93ffda1d5bfffd019d5bfffdfe6419cbc283b30a5a02ab7fffa89bd94a9c1ee3e7,
  0xabec75cb87f8af63fff699abad1e5eebffb491f64f909fa75247dba43921ffb20e236ba9f3a01b0ffd90711b5d4f9d501b0ffde2148df64ca287d91e0c50fb21,
  0x5803fff7ab2aa0b007ffecb315803fff654e2b007ffea272a715803fff4b32a715803fff7291ca9c5600fffdcb9b72a715803fff73e236a5a09425c8bb3aeda6,
  0x4598e575283f20fffd95505803fff4eac9c9cc2ef665271bb95505803fff7629c086282c0affeee5d741600fffda1975d05803fff6865d7d61600fffddcbac08,
  0xca54068ac61ad79600fffdcc05989d8563a7927075f8d02e1d9559d56623d7fff61533f9447afffecaeaa78461fffb279600fffd02e799ace941f1187ffefb39,
  0x8173ccdc057de110ebffb5f8e0d54a400e6b9c057eb86b0c7ffe8170ec95d4bef08875ffdeccd70ecace97f315863fff7976af662e87ee4e3c7d02a0f88f2879,
  0x9ffee5143ebc18a1f613c18a1f613c18eb1f7310c50fbc49ae6765ca359ac57f8f5bc49ae6765ca359ac57ff1f5ae4473e3f5e0c57ff40b9e66ea5f78443affe,
  0xf069ffeac4311dedd5279613ffd380aa88ee5ffd3aba8623b97ff4e03d4311dcbffac61b54575a7e45111847d6ff993cb09ffeef3fe64f2c27ffb231ff993cb0,
  0x7ffa8a22b90aeb7e64f2c27ffb4738cfc239452c89c1d38dbfffd84f069ffec279613ffde58f2c27ffa46996c0fd985938403756ffe36ffff42c9e0d3ffdbaa4,
  0x8fe655c6c6ffff6fb3018e6837e065988dcbffadaf28ec3d4563ebc1a47da3ccadc2b192fd688223215f5ebc1a7ffa58f069ffe888c857c6c9e584fff6a4f2c2,
  0x5fffee62cb94d0713f4efca5b158fac637f4bf988dcbffaaa32b86ffff46255195c37fffa152ff3dcffc17ba17b553be5cb63637fffa9908fe655e837fffa990,
  0x65c37fffbf32b86ffff5efe97c2e846d7fffadaf3bb3e3ea2b1f462f995c37fffbc579cc705ddc22521d3dff5cb7211b5fffef35d93215cc2cb49fb5f023211b,
  0xb1c76bfffd93579eb16511ecc73dc7de69f4952f80c0daffff533c27c86af6984849aaadac79c86ffff763c86ffff4ebb75fd5dc6dca5b5fffe965c37fffa311,
  0x7485fffed02c7a1bfffde39f5df350e9085ee85ed63e774858fc6d7fffb52dc837fffad57347cea96d638ed7fffa0e104a5f54707b5d0ec478fa1f51f3aa416,
  0xb908fad4f5acc7ae423f8d95c37fffb36e20cb4db3aa7dcb600d87feb92a0099680dfa93ac9b97ff6a570dfffe94c278415221624dfffed363d0dfffed1fd766,
  0xf0c96b90afaf572587b977fffa225ee21affff7e2db2648575bc1c630cbaff1b70dfffef01d8b362b853dc65fffec6a475417ba1bf1a476d9b4e526fb067598c,
  0xfff5fdf2589ffea24fff6e449ffefc6893ffd143ea731bd90a2b193af766e0d637e3eecdd290c07dca91f48c0cd08afe3edc2963ee7214b1f68232e42bebdd93,
  0x37d8fffd557a1923ef6ce178ea1d23fff6b54b618fd8fffd18219328bddc22f858df63fff671a478907f523ea7ffa589ffed1627ffaa9a7ffafe54d3ffdf92c4,
  0x5af7be1fdad52d8df63fff56a579c8b9930a9eb71f6b5482c6fb1fffb580cb637d8fffd18ab0196c6fb1fffa0600cc2a05fa31560320b1bec7ffe8c4bea06416,
  0x66f63f7c78fb5aa43afd8fffdad52120fd8fffdac0465a7ec7ffeaafc8f120fefccb637d8fffdf0b3b42108d770cb11def87f77098f120fef859da10846b3846,
  0x7df991df63fff4b004fd8fffd9b7391732616c7ea38fa722a2e50f7c7f51c7d236d6948b9930a9eb71f43ccccb0eccb5f5b8fa722d1ca153df0fb27aec722ec9,
  0xfb9f01dbe57c2d606f7fe96735d99548d2587be34b0efb1fffbf29907a563e966c6fb1fffb43b4d5943dafd6afa4604ab7c3bde53ea4ac3a971fc6fce618f4ac,
  0x976c7ffecd847afffefccaed8fffd3b5e64b155af391730dfcaf7f6bdf1e3ed6a905a4775ffda5b3ac893a7c93b75a97c0fdaf75ffd2cdc9b1fffbf32dc9b1ff,
  0xf6964ae5b48dd9630e6b398eeba0bd4be16b1d35ffd06414d9a92fd78bd4be16234f7ff43ecb74c6a5c77afee653cbc7e7d3b0c49fffa94545f2ba5863fa8fa5
]
def gemBitBlock15 : Array Nat := #[
  0xdf990f91fffbd62cb8239ea3bac6d79d2c790ddfffb367336cb07a8145ced1dd10bd9f10220fbf3212483fff4b377c3fff7aa32e36fccb77c3fff7e64177c3ff,
  0xca51a5edb9805b3f1863d2b1f5a6bbe1fffad3586ba7ffefc8cb0d62435f7e465863c486be96391fffa58328fffd938bf561c14ecc28f63f51c7d3f52ea6ddd4,
  0x1bdffada8fffdcc454ef66135a478fb999b1ef66131e958fad3f91fffbcc4dbf2486fc6dc7f21f9162435f7e43f20f121afbf1df0fffdcc453b67e30d74fffda,
  0xe37838c574b908df1afa7150472192f8d6d40ccc1504720d75b6d77b4846ade313cb25cab6f5b5affefb6fb1d1a699805a6fc97458fad3f9affef01dbe574b58,
  0xd74fffdf832f9690d7baffec961af63fff733f26092956975f1a34b75ffd1a5b1fffa46b1d1243fb9b791ba8fffd3f566590dedab94b63fff61b22ccb158618f,
  0x5ad8be7fe46c426a4377ffe96408c295ec7ffefc19e9af75ffd948bd8fffdea1ec669948b48f1f561af63fff46586bd8fffd62e55a435a563ea53db1838574b0,
  0xe4ddedb950630a01fee60cb19c992facbaf8d917baffec8bd8fffd7a45ec7ffe965e917b1fffa59a1a45ec7ffed1798ba1fb5ef8f1f4b2046917b1fffb70d03a,
  0x3fff5e5c9b1fffa597916c7ffee7c3b0e4afd6975f1a5979726c7ffe965e5af7b1fffa061c541d22c640c7f1af73b67568c42fd1cde5af7b1fffafeccaccb596,
  0x6e7e916218dae58c27f4d2c358cb1f652495ffd45baffea2d8fffde53e93d7c3bdaa7dae9623243fb245b1fffb9b35f73ff7e13e40571f63f3a0359fffebc8b6,
  0xfe13c61b1d3e9c2c43cffff72df1f11b07a99d2c45cee64364473cb19031fc6fc51f7c3fff73e1d8334ca4a971fc6c9257ff79c5831cd2663d8235886be37947,
  0xa6b2f63fff79aedbcd479641321afc6b14e72b4ac7d2cdc1af63fff4b29d88720fffd48c1af75ffdf9affefc8fffd6319a4790d27ffeaef87ffeb90645c614ed,
  0xf4e12ee8bc53897dc891e3e9c2088a754bec6e91e3e9c47dee2e3348ec4648f1f6bad1c8fffd5ec7ffeb95ec7ffeec4a1d7c8b20fd68f95ec7ffe8ea95ec7ffe,
  0xb98ed94d65e04ab7ffe964229363fff687269f1b92be157dacd58f7d939230c81aeb74cf5b092186f975a711f7b8b8ce9b11923c7d3b3d8857ad529f621f48f1,
  0x209985663074bb8fa594aaec7ffed05b1c252482bebe34e62a55763fff6f1bf8ecf621d45a6a99ee9be3c7da063d9c25f22bebe36e9363fff4b3749b1fffab52,
  0x8fffd63442b2cbec3c3fff4e12fbbce78cc4bfae36f8f1f4e628e2d8fffd3ab151c5b1fffa711f785e15c6625fd537c78fa70820cde15474bfaa6f8f1f416d9c,
  0xaf0177c5ee3c7d384bb955a795df17b8f1f611c2085569854107d0e8c2fb038aad6b77ad9b118364d363fff4b238b63fff58c3c7151989048691e3ed29517dbd,
  0xbb1fffbc2e2f3ccd2841297d32a431be3c7de17179e66942094be8749218df1e3eaaec7ffec2d8fffd2cc2d8fffde1e29d44889aebd780bb01ef8f1f4e12ee57,
  0x874787ffee9a8052ec6e8160c975a9ca1d0483fff515f0fffd441c83fff6134edb15b1d4a356ecebbef3cc9cc60e9771f5e63d9c25f22bebe3788987ffeeebff,
  0x9eaa1d3d6fffdeaa180fd6fffd9065c916e5ae933196b1fed7ff47ffeb91fffa251fffb42bb630f7f0922330883dc78fb7c887ffedf2e41fffa98b6aac3dea72,
  0x413e579fff7d3f993943a6e9fffbb2f71c301814fffdccc777480ff14fffd3ab504f95e7ffdd9ca1e75bfff7dbd2ad6fffdb6450c5623eb7327aa879d6fffdcc,
  0xe85235d7eece50eea7ffeece50e9ba7ffed28d9437974fffde392bd58565ec1ef6953943a6e9fffbe9d2a72874dd3fff6dae69ac575a203b30a138743878fb4b,
  0xe6f80a7ffef58d7d2ee1621fdd9d30ac47d6a2f5206053fff720bd283ae1621fd155bed85ac7fb59e3df790588d7d155903d85887f48b7ff7672870bfff617da,
  0x8ff5543587b0b11afa1c2fffdcccf2a764ad37c6aebf7300db17a6d235d7ee51eecc4f13fe13ba142363f815f034a0f1f7e78a9fffbe9861621fdf9bedd3fff7,
  0x9ba7ffea2beea1ef3ffe8c57c901ee9fffa4799a61d7a7ffea27fffb947ba972fde7ff09dd506c7f02beb1a5078fbc54fffdbedd3fff640f74fffdeaa1c9b0b5,
  0xd0af18b956f329b1880e2a1d668869771f7994d8c4071558acd10d2ee3ef0f1774fffde22696e9fffbe9ee9fffbe9d7a7ffea16f4f74fffd69875e9fffa858b2,
  0xc632fa04f5f5ac43fad30eefffd38ea4eff57a471aeb787d0fb2a72a77c5ecfa687c96f0fbc43b252d34d0f907256d3fff774fffdaf4fffda57a7ffe9d46c7b4,
  0x58efa0b3dfefc723dfe82c29fe8fbc7dda68e3afaecb21af5b5b8fbd471f7af1e3eca9c7da7fc7d15d38fb248f1f7ffbfffbcaa2cc11588fadf4eefffdcc035,
  0x987b63904bf1aff1658d2b122f10ec390901bc44dbc292ef30edb26662d9b3553dfa3f5eff77bff7a2120fec9bdffab937bff40dffbf3f66c34b66c387f6f1fd,
  0xfc6e7966ac20c6425f8dcec98898f55d6f3d4c6ae37ed8ca4163f8dce92bf6ad4f2304545752def3d4c6ae7161d8ca4163f8da580ab2ef877bcb3109b7f7a515,
  0xaf08d5ab46cf2cb507755ca4163f8d9327c3701a8f4faaf8d1b3cb2c5d63203c7f1a3674b46b50722eb0c0f1fc6e5aad81d29240b1fc6f1a31e3f516a24925d6,
  0xec7f1b20ff1e3f8dba772ad2e9074e3533d358cbadff8f10378c53fc78fe364f0ece53e88933f1e3f8df9a5a3ab60756902c7f1bc09645f8f1fc6952cd28b830,
  0x1a41c78fe36521c78fe3514838f1fc6fe3c40dfc78fe36db35a08a331f3212fc6f30d6db353f34e5bd931eedbbc5890343fc78fe37afe3c7f1a8aa9a28888358,
  0x1dc423c78fad4554f91839106b10c7d6f3827211e3c7d6fb71e3f8d1c78fe36b238f1fc6e699cd6a25692fad63f8dcf8760929252587c6c871e3f8d9071e3f8d,
  0x7f1a8bece51477ba88720d75a05460db287495d01fc6eca2a306dc40f31180fe35540e3f8d02633ad651a4ae82f8d92a81c7f1aabf2bf5b78f10378f1fc69ff,
  0xcb901fc6b4c08b2f3d6db2b10d7c68151aa7bcd753315cabf1bcc4c38fe365ec38fe340e3f8d02a3233af2b495d05f1a05460db963cba03f8d02a306d9437974,
  0x663784f963c56206c26b58ac77abe07881a062f81e2068af81e206c26b02b1ded65fe2b10358e8e88d3968f3065bde255032de8e2068e3f8d02a36988c7c1c1b,
  0xaf8de14d64c14cb67cfd1889aebebe355781e2069573f207881ae6f9607881ae510607881a3e7e40f103416e07881aa99ff0c546b88f5f1b203c40d435d4c999,
  0x81e206ef207881bd431035c40de03b518fd3035d7c6f03c40da5b81e2069d36703c40dcdc0f5d02133e07881b09f03c40d4c84f81e206c9829e76aa160f4ebaf,
  0xfe359954f53266a5c6d44b90d01a722e37631a2d1e206f24997b22223c77b43c40d5f115881a0b50f10340f10348c03c40d62e603c40df611807881bc43b7071,
  0xbbe3f8d9b37c7f1ac585be3f8d730bd877f57a536886bf1bce6262c2df1fc69c54288222c2ddc3d6b6aabbe3f8d62a5577c7f1abdf1fc6966caf8c87f1a0b6f8,
  0x5c232c40fe34fc71672c9cf2c64190fe3780d73e3f8d2bd78fe37048840cb8db271fc6c2938fe3788d9337c984b5881fc6951588c86ddf1fc6d73062ac95b52a,
  0x6f584b007e37881bc7f1bced9c7f1a8bc7f1a715b62cc200ee3f1b96fb8fe36922a2b92eb6e5df71fc6f3989178fe373cd7c9f9800529cf0a2190fade30b3d87,
  0x609d401f8d72c6e4318303f1b7184515490db90f11eb4674b672c632c847721e23d68cf87603a5211a43c47adac34ab6f45cd21887d7fe3452c1aa99088721bd,
  0xa694a334ca490f11eb4fcbb63932903e355b5939ea63ca307d7fe343ed93a43757612c01f8d18410b05dff1632a2348788f5b20a0e2c020f4ce92fb88f5a94c2,
  0xbb1f8d129f35a83f1b9aaec7e358d13fc61f8de42995e597097fc6af63f1ab007e34e2a716013673a4df01f8d02167691ba57358303f1b59380b3e245bd0b46a,
  0xe28888358dff1b09c83f1b5a41f8dac181f8dceb0607e36436c303f1b26f6a1f3c57348d275ade2acb0c01bb1f8da5d8fc6f214cac2f21286a53d9ef2255a1aa,
  0x2ff8d124348b97fc6f214caf2cb972ff8de31611254a8e721a86c83f1a181f8de181f8d45b0c0fc681393c3d0de21d9141608a0ef992e5eb5b563a30d637fc6e,
  0x1197ad22d9b989baa32de808a18e42232f5b260d5fe2cf2bb9172ff8d9368c4c4547292e5ff1b9b4d6c222ea232f5bc8532a546e5cbfe36b0e975686f723b917,
  0x90a6bae9afd6df95a47f1b09afc847d6afec7f1b9ad65d088fade58c89f32d8fe36d8495696c7f1bc04c722ebb10353c86ac26ba96f401a3f1a253dc611441ae,
  0xc6a2fc6ac642bdeae9f8de078d7eb6c33e574fc681426beb96f7a8fe37e7a8fe37924d09ac6b6cb63f8df996c7f1b09ae4223bd5a47f1aff2762e45b3290af8d,
  0xcf344e7e53f8dfc6d889143fbfc6cd9d3f8de2e9fc6ef3c5d3f8d484512432569fc6fc5b6ac115d6a27eccca88589fc6bf8229c24367f7f8db60a98aeb416e9f,
  0x7f1bd516c8eb111f5bc491fc6f1cfaef9a874877ea8683556491fc6c367f5df350e90ef81a1a0dcb052cf13351ef7d76f41648fe37a7f1b7fd9e689313f8dbfe,
  0x86ff1b2a7e355654fc6b1eedbbdf1f036131e4238d8673228977cd43be687f5d48fe366c91fc6d66491fc6cd891fc6f183247f1a153c5261734e817ba14d6d2c,
  0x12f2a4a26673cb3eff1b4fc6bd4ada6f88c71e23fd6c9b92bd4aae9bea590e3c57eb64dc95ea5574df39ea38f15fade09ab978eaa5f24eea38f15fade2a7e378,
  0x63f56de32a350fe3563f8deb1fc689f2047888fad1bac7f1bb1fc69592c44477be87f1a1fa1fc6fb1d2092142dd712e34b363f8df50425d4c8b1aece059f7f8d,
  0xf8deaeff1b96eaeff1b2697e3fea1a3f8d3b8845623eb687f1bd5a1fc6c9a6218e190aeb44655a1fc6d7ead0fe36e3a099b6248441dfe346a1fc6d2db53ab4de,
  0xf5b742cc6de0ea5eb7ade6bb662872d3d6f5bff1e3eb7984cdad1de3baee0b28f7eaf1e3bde44983fc78fad72dabfd9b9de77d5de0e9c649f5a06fe377f8d1b7,
  0x6e18af5ac660b75f23f3bd565f8e3eb516621675bd6aab9d9454b48ad3dc3cc30077bc3c579aaab2fc71f5bf2f3329727318d38dae73eaa2ca99b8ae50f30c01,
  0x8d4ad3dc31001de8739f5514d9e0572879ec01f5a2846311fd75241dd35e803e37d8af5a9998e3da870fade1e2e63ddc37ba8fad5597e38fad1280a352a2087c,
  0x9d7ade57148b5c061ee4bc301f5b2fc71f5b965f8e3eb55338b9d1b91f5b4a4754ad9d3367ecf5bc62de9d0e2e6044d06887d6f17e38fadfc5f8e3eb555ceca2,
  0xba57c8df2f4ef624ecf894e2b3e9ceb7adfc78fad0ff1e3eb72c97c78fadfc71f5a57f1c7d6f06ae4354295cf3a6cafacbc64803eb78d0527ea77528179d0f4b,
  0x1e3eb78e3eb6fb8e3eb7e4fc94c04f5fa6d25977ad93e78c4c04f5fa6d20b7ad0f8e3eb6e0c4636ae6e465a1414f20637d7a594b11d179ee832fbeebde76ce37,
  0xa98252979d6d9dfaeb461c7d6c9a4b0a597ba2af01cffdd29c6f5bd6fa92dd5598ac47f1eb40b0559d65473933d038fad901c7d6f1e3eb46e3c7d68e3c7d6c87,
  0x7c4af41e7b8dc60f7b5936676383d995ba458cbd6fc72dd571b65c0f1f5a38fadd97b655304a50ceb6cefd75bc5d765edd2d84fdef4a5e75b7b92ff5d6ecbdb2,
  0x6d8cc875c7d68f1f5b43c7d681e3eb799e3acde46d354e33adc6e77ade078fad9078fad950f1f5a181e3eb68f65eacaca23ee7853a438d75f1ded1ecbd595944,
  0x8fad19571f5b20cab8fade76c0af5c47c4dd0106cc430fd6b1e74ca54ea5cbf2115eb77a6a23b93de5aeebececf894ff6f650d3eb7d71f5b4f5c7d6cbd71f5bc,
  0xac7d6f1f5bbe3eb6b6f8fadebc7d6d11c2e60ca094028b65be3eb56458e4c91967aa35bd784d94ac6b218469cf31b020f1a15f5d6d71f5b7d5c7d6cab8fad0eb,
  0xbfa1f5ba64ec28ecc8bbad91d73a01a438d7f5eb73d36ce09ce645ccabc3ae74034871afebd6e7a6d9c139cc705ccabc3ae74034871afebd696564b75fe7b2ff,
  0xdd8fad85b1f5b943d8fadfb1f5a57ec7d6e597d8fad158fad02b1f5be87d6ff43eb6d9176b4596ebfdd6cbd0fad5ff43eb7f58fadffac7d687e87d687fac7d6c,
  0x1a32aab0faef06b0cd567aaaffe07ad1f5ac63eb72a21f5a91f5a287d6a64d979e63dede8666ce8041f7d5a5450fad170cd30e855eea83b3652cbbd6bfd248fa,
  0x19c589f5b26c4f8e7d95efc6129ff1c75ee597a1eb72cbf03d6bdb97e07ada12d2ef37a7b1be6b81eb76f6e5f81eb78e6695edcbf03d6f06b0ccdbaacbf03d6b,
  0xc0f5b4af67f81eb695ea7fc0f5bb2bf81eb78c5b84fb6694ebca889f5b4a9d6d84cba75c0f5ae7657f03d6f18b73ccfb1cbfbaf78e6695ea7fc0f5b999689175,
  0x66c20d774fad9b083675d3eb66dbcc43a70d3eb66d5f310e9c34fad2323a7843a70d3eb4afa1eb4afe07ada5ae4447e995ace75b30b4fad1e3673ff03d6d295f,
  0x2ce77add951e1fad9341363453f5664b196f61703d6f0136f3661f0f3da7d6bdca825d6edbddd7bb85c0f5bbca1f03d6813967c74efed9f8853eb7d0f5bf81eb,
  0xf5a99ad983234a87607ade59f6faa8ec0f5b38ca6e3483b03d691ee8bcd2f7bee18deb687ad2ca1eb431287ade07ad2ce07ad8543d6f014cae92a53da7ae9f69,
  0xd6e6227d6007ad4a782e2d86f074af5a1e748937003d687b867cf533d8954bd2f77f8801eb7978a8b49917a9e9696f7f8f5bf88711eb7aacb63d6f0a0baa8ec0,
  0x26f120aeddd2415803d68c458b5f23bf4ef0830a8e23d6d295d8f5b5f98f3aa06157c43f5b4a56847ada2385c06a594a3145b4a5401eb69695801eb6953eb003,
  0xd6a810157bd7b7b569648eb382d894a45b991dcab4783f7d5afeea59adb4a94aad2e95f569fb37aebb4470b98301666da23851ade3b6bb7897ecdb0d88f780ec,
  0xb4f41efc4b197ebde4935dfe431905ee5b28ca87febd112bf5b78cf3c4c4d503660c86f5ba4bc27d5b732b214b3875b78b5370718d756d129f726d12bd892d29,
  0x7fd32ae68c70baeff1eb7cd975283e53175eb786a7b2be37addd249003d6d62312d52b0c5d77f8f5a32f2d42d727639c8a8589f2ffaf58e96cfaaee87febd48c,
  0x7ad9362772223f4caac57dd7607ad385111fa6546293ec0f5bc62dc73ea05e74feebd9341323f4caac57d20ec0f5b59e55316425fadbb2a00f5bba56007adacc,
  0x2bf5b4aec7adbb864b942f3b6e77adda729d7db2065eb688e139e13e48950c516ecaec7addd2b6c7addd2496c7adcc8b65b75ba1515f11baf774925423d69500,
  0xad6d78db2db665256f3d4e8ba01f11eb728c07adcdb518a8bdd6e832fbeebdca320f5bb1eb401eb6400f5b47b1eb68c01eb7994e400f5a59cc08371bd6f5b5f2,
  0xaceb790e77adb62b211196f428c23d6e603d6cdb05c6f7473957b45503d685e6144e77ad0a181eb69d4303d6f3d4e9d4303d6f68cf6ccfda143e23d6d3a87c47,
  0x7ad5503d68d403d68c0303d6f180dc7ade23d6aaf11eb7829a26153b9b2e79e6e5ce74783e371aada31eb786a658308d5b97a8f5a1641eb69447ad86565e31ce,
  0x5eb40cacf9197f2f5b98b358543f9fd77bf560d98cbf97ada0dc3fe5eb6b30b39712f5b41b8cbf97ade4298ce97c9efd778e7d9457c4bd68f5bec3d6fc88f5a0,
  0xffcbd6c836fd68dc6dfad1bc86fd6f0a084f257ad906f2f5a371bcbd6d06e3797ad0f81b054a52b3a99c8343c3adaccbae5eb735192c57bd84d7d62bde8dc3fe,
  0xe2130ce8faeff5dd8f2f5a36c797ad1b7ff97ad1b7eb635cd6ac79856792bd68de5eb78de5eb78c5ad8e396b55eaeded2753bd7deb7ad4f975cbd6f0ff97adf2,
  0x836c6fd6d3cbd6954578f2b1bd72f29673bd6ce35ad1e101650ebe4d6d0a1c4f36edaf93f69f5a353cbd6aea9e5eb5fea65ab88e6a9f3e30c287cb7a327f97ad,
  0x4f9fbecc7ded11c2e03cd1135cbd68b6d9eb97ad1bd6f5b21eb7ada0deb7adac86b97ad4a7d6f4fad0d3eb72869f5b965d3eb77eb69bf5b5f39cbaf683537eb6,
  0xef7bfcb7b0bf96f5ceca28d4ea42de62b7ab152bf6f40b9e64448838deeedd5fe5bda85fcb7b457ff2defad4fadbbd6fadeb7c92f5a35deb46dd3d6b185f77cd,
  0x9374668e29ef65fb44c97461e748cdfe8cd1eecdf419b2de11db779d0fb7f99de6136c9ebb6b1764c8edb27dd9b27cc5bbddef4aef69655def736f7be5bd4ef7,
  0xafb57c78da367189fe34d1b062befc69ab55df71d3bc6730d6fbf1e9d45cc3554efbf1a6c81fe3d3b09f1ed78f1b64db66fad9a3525dedd9a3af3bc78ce8a3ed,
  0x3bd77e74ed741b6f28edb2747da768f5def6f14dd945cf330841e9bedb30a17574ae79a3382f9d02e7992a220f4dffaef18a7ff5dbfeeb1b464de313fc69bb7f,
  0x668e62de36cde2df8bbcc35de209eea6de3466f3cfb78419be9eeceaaedf6a53de5066f28b6f3bb379453dc9b790f3b26cf3af6c9a29bc0f18a6f3e32aa29ab7,
  0x1bbc7b5d4cef1a0b780d771f6f0c13de592e89746dbfed93a7da2dd9a03c7b267
]
def gemBits : Array Nat := gemBitBlock0 ++ gemBitBlock1 ++ gemBitBlock2 ++ gemBitBlock3 ++ gemBitBlock4 ++ gemBitBlock5 ++ gemBitBlock6 ++ gemBitBlock7 ++ gemBitBlock8 ++ gemBitBlock9 ++ gemBitBlock10 ++ gemBitBlock11 ++ gemBitBlock12 ++ gemBitBlock13 ++ gemBitBlock14 ++ gemBitBlock15
def gemSteps : Array (Array Int) := unpackLearnt (147540) gemTree gemBits

def makeRowGroups (xs : Array (Array Int)) : List (List (List Int)) :=
  (List.range ((xs.size+31)/32)).map (fun i => ((xs.extract (32*i) (32*i+32)).toList.map Array.toList))

def clauseMask (c : Array Int) : ℕ :=
  c.foldl (fun m l => m ||| (2 ^ litIndex l)) 0

def annotatedHints (db : Array ℕ) (ids : Array ℕ) (target : ℕ) : ℕ := Id.run do
  let mut s := target
  let mut words := #[]
  for i in ids do
    let c := db[i]!
    let live := c ^^^ (c &&& s)
    if live = 0 then
      words := words.push i
      break
    let k := live.log2
    words := words.push (i+65536*(k+1))
    s := s ||| 2^(otherAtom k)
  return words.foldr (fun w tail => w+4294967296*tail) 0

def maskRows (input learned : Array (Array Int)) : Array ℕ :=
  #[0] ++ (input ++ learned).map clauseMask

def makeHintRows (nv : ℕ) (input learned : Array (Array Int)) : Array ℕ := Id.run do
  let masks := maskRows input learned
  let mut db : Array (Array Int) := #[#[]]
  let mut wa := Array.replicate (2*nv+2) #[]
  let mut units := #[]
  for c in input do
    let id := db.size
    db := db.push c
    wa := setWatches wa c id
    if c.size ≤ 1 then units := units.push id
  let mut out := Array.replicate db.size 0
  for c in learned do
    let (newDb,newW,hints) := watchedHints nv db wa units c
    let id := db.size
    out := out.push (annotatedHints masks hints (clauseMask c))
    db := newDb.push c
    wa := setWatches newW c id
    if c.size ≤ 1 then units := units.push id
  return out


def namedNumber (keys : ℕ → Key) (l : Int) : Lit :=
  (keys (l.natAbs-1), !(decide (l < 0)))

def namedRows (keys : ℕ → Key) (rows : List (List Int)) : List Cl :=
  rows.map (List.map (namedNumber keys))

def bitMaskList : List Int → ℕ
  | [] => 0
  | l :: c => 2^(litIndex l) ||| bitMaskList c

theorem mask_mem {l : Int} {c : List Int} (h : l ∈ c) :
    (bitMaskList c).testBit (litIndex l) = true := by
  induction c with
  | nil => simp at h
  | cons j c ih =>
    rw [bitMaskList,Nat.testBit_lor,Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | hc
    · left; simp [Nat.testBit_two_pow]
    · exact Or.inr (ih hc)

theorem atom_named (keys : ℕ → Key) (v : Key → Bool) (l : Int) :
    atomValue (fun i => v (keys (i-1))) (litIndex l) =
      valueLit v (namedNumber keys l) := by
  by_cases hn : l < 0
  · have he : (2*l.natAbs+1)/2 = l.natAbs := by omega
    simp [litIndex,atomValue,namedNumber,valueLit,hn, Nat.add_mod,he]
  · simp [litIndex,atomValue,namedNumber,valueLit,hn]

theorem numeric_row_holds (keys : ℕ → Key) (v : Key → Bool) (c : List Int)
    (h : satCl v (c.map (namedNumber keys))) :
    HoldsBits (fun i => v (keys (i-1))) (bitMaskList c) := by
  obtain ⟨val,hv,he⟩ := List.any_eq_true.1 h
  obtain ⟨l,hl,rfl⟩ := List.mem_map.1 hv
  exact ⟨litIndex l,mask_mem hl,(atom_named keys v l).trans he⟩

def checkSources (db : ℕ → ℕ) : ℕ → List (List Int) → Bool
  | _, [] => true
  | i, c :: cs => db i == bitMaskList c && checkSources db (i+1) cs

theorem source_models {a db} (rows : List (List Int)) :
    ∀ start, checkSources db start rows = true → (∀ c ∈ rows, HoldsBits a (bitMaskList c)) →
      ∀ i, start ≤ i → i < start + rows.length → HoldsBits a (db i) := by
  induction rows with
  | nil => intro start hc hm i hi he; simp at he; omega
  | cons c rows ih =>
    intro start hc hm i hi he
    rw [checkSources,Bool.and_eq_true] at hc
    rcases Nat.eq_or_lt_of_le hi with rfl | hh
    · rw [beq_iff_eq.mp hc.1]
      exact hm _ (by simp)
    · apply ih (start+1) hc.2 (fun t ht => hm _ (by simp [ht])) i (by omega)
      simp only [List.length_cons] at he
      omega

theorem bits_exclude {n k start last : ℕ} {yes no : List ℕ} (keys : ℕ → Key)
    (rows : List (List Int)) (db : ℕ → ℕ)
    (hnamed : namedRows keys rows = sampleCs n k yes no)
    (hmasks : checkSources db 1 rows = true) (hlen : rows.length+1 = start)
    (hprop : ∀ a, HasPrefix a db start → HasPrefix a db (last+1))
    (hempty : db last = 0) (hlast : 0 < last) : sampleDoesNotMatch n k yes no := by
  intro u hd h0 s o hpos hneg
  let v := keyVal k u s o
  let a := fun i => v (keys (i-1))
  have horig : ∀ c ∈ rows, HoldsBits a (bitMaskList c) := by
    intro c hc
    apply numeric_row_holds keys v c
    have hh : c.map (namedNumber keys) ∈ namedRows keys rows := List.mem_map.2 ⟨c,hc,rfl⟩
    rw [hnamed] at hh
    exact sampleCs_satisfied u hd h0 s o hpos hneg _ hh
  have hm : HasPrefix a db start := by
    intro i hi he
    exact source_models rows 1 hmasks horig i (by omega) (by omega)
  obtain ⟨i,hi,_⟩ := hprop a hm last hlast (by omega)
  rw [hempty] at hi
  simp at hi


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def delInput : Array (Array Int) := sampleNumbers 6 3 deleteYes deleteNo
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delKeyTable : Table Key := eval% makeTable (originalKeys 6 3 (deleteYes ++ deleteNo)).toArray
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delKeys (i : ℕ) : Key := tableLookup delKeyTable i (0,0,0,0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delRowBlocks : List (List (List Int)) := eval% makeRowGroups delInput
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delRows : List (List Int) := delRowBlocks.flatten
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delMasks : Rom := eval% makeRom (maskRows delInput delSteps)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delDb : ℕ → ℕ := romLookup delMasks
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delNamed : namedRows delKeys delRows = sampleCs 6 3 deleteYes deleteNo := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delMasksAgree : checkSources delDb 1 delRows = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delLength : delRows.length+1 = 1987 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delEmpty : delDb 8585 = 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delHintRom : Rom := eval% makeRom (makeHintRows 598 delInput delSteps)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def delHints : ℕ → ℕ := romLookup delHintRom
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart1 : checkSpan delDb delHints 1987 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart2 : checkSpan delDb delHints 2147 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart3 : checkSpan delDb delHints 2307 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart4 : checkSpan delDb delHints 2467 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart5 : checkSpan delDb delHints 2627 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart6 : checkSpan delDb delHints 2787 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart7 : checkSpan delDb delHints 2947 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart8 : checkSpan delDb delHints 3107 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart9 : checkSpan delDb delHints 3267 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart10 : checkSpan delDb delHints 3427 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart11 : checkSpan delDb delHints 3587 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart12 : checkSpan delDb delHints 3747 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart13 : checkSpan delDb delHints 3907 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart14 : checkSpan delDb delHints 4067 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart15 : checkSpan delDb delHints 4227 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart16 : checkSpan delDb delHints 4387 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart17 : checkSpan delDb delHints 4547 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart18 : checkSpan delDb delHints 4707 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart19 : checkSpan delDb delHints 4867 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart20 : checkSpan delDb delHints 5027 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart21 : checkSpan delDb delHints 5187 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart22 : checkSpan delDb delHints 5347 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart23 : checkSpan delDb delHints 5507 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart24 : checkSpan delDb delHints 5667 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart25 : checkSpan delDb delHints 5827 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart26 : checkSpan delDb delHints 5987 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart27 : checkSpan delDb delHints 6147 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart28 : checkSpan delDb delHints 6307 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart29 : checkSpan delDb delHints 6467 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart30 : checkSpan delDb delHints 6627 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart31 : checkSpan delDb delHints 6787 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart32 : checkSpan delDb delHints 6947 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart33 : checkSpan delDb delHints 7107 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart34 : checkSpan delDb delHints 7267 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart35 : checkSpan delDb delHints 7427 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart36 : checkSpan delDb delHints 7587 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart37 : checkSpan delDb delHints 7747 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart38 : checkSpan delDb delHints 7907 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart39 : checkSpan delDb delHints 8067 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart40 : checkSpan delDb delHints 8227 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart41 : checkSpan delDb delHints 8387 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delPart42 : checkSpan delDb delHints 8547 39 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delAll (a : ℕ → Bool) (h0 : HasPrefix a delDb 1987) : HasPrefix a delDb 8586 := by
  have h1 : HasPrefix a delDb 2147 := span_sound 160 1987 h0 delPart1
  have h2 : HasPrefix a delDb 2307 := span_sound 160 2147 h1 delPart2
  have h3 : HasPrefix a delDb 2467 := span_sound 160 2307 h2 delPart3
  have h4 : HasPrefix a delDb 2627 := span_sound 160 2467 h3 delPart4
  have h5 : HasPrefix a delDb 2787 := span_sound 160 2627 h4 delPart5
  have h6 : HasPrefix a delDb 2947 := span_sound 160 2787 h5 delPart6
  have h7 : HasPrefix a delDb 3107 := span_sound 160 2947 h6 delPart7
  have h8 : HasPrefix a delDb 3267 := span_sound 160 3107 h7 delPart8
  have h9 : HasPrefix a delDb 3427 := span_sound 160 3267 h8 delPart9
  have h10 : HasPrefix a delDb 3587 := span_sound 160 3427 h9 delPart10
  have h11 : HasPrefix a delDb 3747 := span_sound 160 3587 h10 delPart11
  have h12 : HasPrefix a delDb 3907 := span_sound 160 3747 h11 delPart12
  have h13 : HasPrefix a delDb 4067 := span_sound 160 3907 h12 delPart13
  have h14 : HasPrefix a delDb 4227 := span_sound 160 4067 h13 delPart14
  have h15 : HasPrefix a delDb 4387 := span_sound 160 4227 h14 delPart15
  have h16 : HasPrefix a delDb 4547 := span_sound 160 4387 h15 delPart16
  have h17 : HasPrefix a delDb 4707 := span_sound 160 4547 h16 delPart17
  have h18 : HasPrefix a delDb 4867 := span_sound 160 4707 h17 delPart18
  have h19 : HasPrefix a delDb 5027 := span_sound 160 4867 h18 delPart19
  have h20 : HasPrefix a delDb 5187 := span_sound 160 5027 h19 delPart20
  have h21 : HasPrefix a delDb 5347 := span_sound 160 5187 h20 delPart21
  have h22 : HasPrefix a delDb 5507 := span_sound 160 5347 h21 delPart22
  have h23 : HasPrefix a delDb 5667 := span_sound 160 5507 h22 delPart23
  have h24 : HasPrefix a delDb 5827 := span_sound 160 5667 h23 delPart24
  have h25 : HasPrefix a delDb 5987 := span_sound 160 5827 h24 delPart25
  have h26 : HasPrefix a delDb 6147 := span_sound 160 5987 h25 delPart26
  have h27 : HasPrefix a delDb 6307 := span_sound 160 6147 h26 delPart27
  have h28 : HasPrefix a delDb 6467 := span_sound 160 6307 h27 delPart28
  have h29 : HasPrefix a delDb 6627 := span_sound 160 6467 h28 delPart29
  have h30 : HasPrefix a delDb 6787 := span_sound 160 6627 h29 delPart30
  have h31 : HasPrefix a delDb 6947 := span_sound 160 6787 h30 delPart31
  have h32 : HasPrefix a delDb 7107 := span_sound 160 6947 h31 delPart32
  have h33 : HasPrefix a delDb 7267 := span_sound 160 7107 h32 delPart33
  have h34 : HasPrefix a delDb 7427 := span_sound 160 7267 h33 delPart34
  have h35 : HasPrefix a delDb 7587 := span_sound 160 7427 h34 delPart35
  have h36 : HasPrefix a delDb 7747 := span_sound 160 7587 h35 delPart36
  have h37 : HasPrefix a delDb 7907 := span_sound 160 7747 h36 delPart37
  have h38 : HasPrefix a delDb 8067 := span_sound 160 7907 h37 delPart38
  have h39 : HasPrefix a delDb 8227 := span_sound 160 8067 h38 delPart39
  have h40 : HasPrefix a delDb 8387 := span_sound 160 8227 h39 delPart40
  have h41 : HasPrefix a delDb 8547 := span_sound 160 8387 h40 delPart41
  have h42 : HasPrefix a delDb 8586 := span_sound 39 8547 h41 delPart42
  exact h42

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delImpossible : sampleDoesNotMatch 6 3 deleteYes deleteNo :=
  bits_exclude delKeys delRows delDb delNamed delMasksAgree delLength delAll delEmpty (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gemInput : Array (Array Int) := sampleNumbers 5 4 gemYes gemNo
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemKeyTable : Table Key := eval% makeTable (originalKeys 5 4 (gemYes ++ gemNo)).toArray
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemKeys (i : ℕ) : Key := tableLookup gemKeyTable i (0,0,0,0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemRowBlocks : List (List (List Int)) := eval% makeRowGroups gemInput
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemRows : List (List Int) := gemRowBlocks.flatten
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemMasks : Rom := eval% makeRom (maskRows gemInput gemSteps)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemDb : ℕ → ℕ := romLookup gemMasks
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemNamed : namedRows gemKeys gemRows = sampleCs 5 4 gemYes gemNo := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemMasksAgree : checkSources gemDb 1 gemRows = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemLength : gemRows.length+1 = 1776 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemEmpty : gemDb 13268 = 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemHintRom : Rom := eval% makeRom (makeHintRows 538 gemInput gemSteps)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def gemHints : ℕ → ℕ := romLookup gemHintRom
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart1 : checkSpan gemDb gemHints 1776 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart2 : checkSpan gemDb gemHints 1936 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart3 : checkSpan gemDb gemHints 2096 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart4 : checkSpan gemDb gemHints 2256 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart5 : checkSpan gemDb gemHints 2416 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart6 : checkSpan gemDb gemHints 2576 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart7 : checkSpan gemDb gemHints 2736 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart8 : checkSpan gemDb gemHints 2896 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart9 : checkSpan gemDb gemHints 3056 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart10 : checkSpan gemDb gemHints 3216 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart11 : checkSpan gemDb gemHints 3376 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart12 : checkSpan gemDb gemHints 3536 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart13 : checkSpan gemDb gemHints 3696 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart14 : checkSpan gemDb gemHints 3856 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart15 : checkSpan gemDb gemHints 4016 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart16 : checkSpan gemDb gemHints 4176 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart17 : checkSpan gemDb gemHints 4336 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart18 : checkSpan gemDb gemHints 4496 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart19 : checkSpan gemDb gemHints 4656 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart20 : checkSpan gemDb gemHints 4816 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart21 : checkSpan gemDb gemHints 4976 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart22 : checkSpan gemDb gemHints 5136 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart23 : checkSpan gemDb gemHints 5296 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart24 : checkSpan gemDb gemHints 5456 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart25 : checkSpan gemDb gemHints 5616 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart26 : checkSpan gemDb gemHints 5776 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart27 : checkSpan gemDb gemHints 5936 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart28 : checkSpan gemDb gemHints 6096 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart29 : checkSpan gemDb gemHints 6256 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart30 : checkSpan gemDb gemHints 6416 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart31 : checkSpan gemDb gemHints 6576 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart32 : checkSpan gemDb gemHints 6736 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart33 : checkSpan gemDb gemHints 6896 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart34 : checkSpan gemDb gemHints 7056 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart35 : checkSpan gemDb gemHints 7216 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart36 : checkSpan gemDb gemHints 7376 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart37 : checkSpan gemDb gemHints 7536 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart38 : checkSpan gemDb gemHints 7696 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart39 : checkSpan gemDb gemHints 7856 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart40 : checkSpan gemDb gemHints 8016 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart41 : checkSpan gemDb gemHints 8176 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart42 : checkSpan gemDb gemHints 8336 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart43 : checkSpan gemDb gemHints 8496 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart44 : checkSpan gemDb gemHints 8656 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart45 : checkSpan gemDb gemHints 8816 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart46 : checkSpan gemDb gemHints 8976 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart47 : checkSpan gemDb gemHints 9136 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart48 : checkSpan gemDb gemHints 9296 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart49 : checkSpan gemDb gemHints 9456 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart50 : checkSpan gemDb gemHints 9616 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart51 : checkSpan gemDb gemHints 9776 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart52 : checkSpan gemDb gemHints 9936 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart53 : checkSpan gemDb gemHints 10096 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart54 : checkSpan gemDb gemHints 10256 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart55 : checkSpan gemDb gemHints 10416 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart56 : checkSpan gemDb gemHints 10576 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart57 : checkSpan gemDb gemHints 10736 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart58 : checkSpan gemDb gemHints 10896 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart59 : checkSpan gemDb gemHints 11056 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart60 : checkSpan gemDb gemHints 11216 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart61 : checkSpan gemDb gemHints 11376 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart62 : checkSpan gemDb gemHints 11536 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart63 : checkSpan gemDb gemHints 11696 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart64 : checkSpan gemDb gemHints 11856 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart65 : checkSpan gemDb gemHints 12016 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart66 : checkSpan gemDb gemHints 12176 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart67 : checkSpan gemDb gemHints 12336 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart68 : checkSpan gemDb gemHints 12496 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart69 : checkSpan gemDb gemHints 12656 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart70 : checkSpan gemDb gemHints 12816 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart71 : checkSpan gemDb gemHints 12976 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemPart72 : checkSpan gemDb gemHints 13136 133 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemAll (a : ℕ → Bool) (h0 : HasPrefix a gemDb 1776) : HasPrefix a gemDb 13269 := by
  have h1 : HasPrefix a gemDb 1936 := span_sound 160 1776 h0 gemPart1
  have h2 : HasPrefix a gemDb 2096 := span_sound 160 1936 h1 gemPart2
  have h3 : HasPrefix a gemDb 2256 := span_sound 160 2096 h2 gemPart3
  have h4 : HasPrefix a gemDb 2416 := span_sound 160 2256 h3 gemPart4
  have h5 : HasPrefix a gemDb 2576 := span_sound 160 2416 h4 gemPart5
  have h6 : HasPrefix a gemDb 2736 := span_sound 160 2576 h5 gemPart6
  have h7 : HasPrefix a gemDb 2896 := span_sound 160 2736 h6 gemPart7
  have h8 : HasPrefix a gemDb 3056 := span_sound 160 2896 h7 gemPart8
  have h9 : HasPrefix a gemDb 3216 := span_sound 160 3056 h8 gemPart9
  have h10 : HasPrefix a gemDb 3376 := span_sound 160 3216 h9 gemPart10
  have h11 : HasPrefix a gemDb 3536 := span_sound 160 3376 h10 gemPart11
  have h12 : HasPrefix a gemDb 3696 := span_sound 160 3536 h11 gemPart12
  have h13 : HasPrefix a gemDb 3856 := span_sound 160 3696 h12 gemPart13
  have h14 : HasPrefix a gemDb 4016 := span_sound 160 3856 h13 gemPart14
  have h15 : HasPrefix a gemDb 4176 := span_sound 160 4016 h14 gemPart15
  have h16 : HasPrefix a gemDb 4336 := span_sound 160 4176 h15 gemPart16
  have h17 : HasPrefix a gemDb 4496 := span_sound 160 4336 h16 gemPart17
  have h18 : HasPrefix a gemDb 4656 := span_sound 160 4496 h17 gemPart18
  have h19 : HasPrefix a gemDb 4816 := span_sound 160 4656 h18 gemPart19
  have h20 : HasPrefix a gemDb 4976 := span_sound 160 4816 h19 gemPart20
  have h21 : HasPrefix a gemDb 5136 := span_sound 160 4976 h20 gemPart21
  have h22 : HasPrefix a gemDb 5296 := span_sound 160 5136 h21 gemPart22
  have h23 : HasPrefix a gemDb 5456 := span_sound 160 5296 h22 gemPart23
  have h24 : HasPrefix a gemDb 5616 := span_sound 160 5456 h23 gemPart24
  have h25 : HasPrefix a gemDb 5776 := span_sound 160 5616 h24 gemPart25
  have h26 : HasPrefix a gemDb 5936 := span_sound 160 5776 h25 gemPart26
  have h27 : HasPrefix a gemDb 6096 := span_sound 160 5936 h26 gemPart27
  have h28 : HasPrefix a gemDb 6256 := span_sound 160 6096 h27 gemPart28
  have h29 : HasPrefix a gemDb 6416 := span_sound 160 6256 h28 gemPart29
  have h30 : HasPrefix a gemDb 6576 := span_sound 160 6416 h29 gemPart30
  have h31 : HasPrefix a gemDb 6736 := span_sound 160 6576 h30 gemPart31
  have h32 : HasPrefix a gemDb 6896 := span_sound 160 6736 h31 gemPart32
  have h33 : HasPrefix a gemDb 7056 := span_sound 160 6896 h32 gemPart33
  have h34 : HasPrefix a gemDb 7216 := span_sound 160 7056 h33 gemPart34
  have h35 : HasPrefix a gemDb 7376 := span_sound 160 7216 h34 gemPart35
  have h36 : HasPrefix a gemDb 7536 := span_sound 160 7376 h35 gemPart36
  have h37 : HasPrefix a gemDb 7696 := span_sound 160 7536 h36 gemPart37
  have h38 : HasPrefix a gemDb 7856 := span_sound 160 7696 h37 gemPart38
  have h39 : HasPrefix a gemDb 8016 := span_sound 160 7856 h38 gemPart39
  have h40 : HasPrefix a gemDb 8176 := span_sound 160 8016 h39 gemPart40
  have h41 : HasPrefix a gemDb 8336 := span_sound 160 8176 h40 gemPart41
  have h42 : HasPrefix a gemDb 8496 := span_sound 160 8336 h41 gemPart42
  have h43 : HasPrefix a gemDb 8656 := span_sound 160 8496 h42 gemPart43
  have h44 : HasPrefix a gemDb 8816 := span_sound 160 8656 h43 gemPart44
  have h45 : HasPrefix a gemDb 8976 := span_sound 160 8816 h44 gemPart45
  have h46 : HasPrefix a gemDb 9136 := span_sound 160 8976 h45 gemPart46
  have h47 : HasPrefix a gemDb 9296 := span_sound 160 9136 h46 gemPart47
  have h48 : HasPrefix a gemDb 9456 := span_sound 160 9296 h47 gemPart48
  have h49 : HasPrefix a gemDb 9616 := span_sound 160 9456 h48 gemPart49
  have h50 : HasPrefix a gemDb 9776 := span_sound 160 9616 h49 gemPart50
  have h51 : HasPrefix a gemDb 9936 := span_sound 160 9776 h50 gemPart51
  have h52 : HasPrefix a gemDb 10096 := span_sound 160 9936 h51 gemPart52
  have h53 : HasPrefix a gemDb 10256 := span_sound 160 10096 h52 gemPart53
  have h54 : HasPrefix a gemDb 10416 := span_sound 160 10256 h53 gemPart54
  have h55 : HasPrefix a gemDb 10576 := span_sound 160 10416 h54 gemPart55
  have h56 : HasPrefix a gemDb 10736 := span_sound 160 10576 h55 gemPart56
  have h57 : HasPrefix a gemDb 10896 := span_sound 160 10736 h56 gemPart57
  have h58 : HasPrefix a gemDb 11056 := span_sound 160 10896 h57 gemPart58
  have h59 : HasPrefix a gemDb 11216 := span_sound 160 11056 h58 gemPart59
  have h60 : HasPrefix a gemDb 11376 := span_sound 160 11216 h59 gemPart60
  have h61 : HasPrefix a gemDb 11536 := span_sound 160 11376 h60 gemPart61
  have h62 : HasPrefix a gemDb 11696 := span_sound 160 11536 h61 gemPart62
  have h63 : HasPrefix a gemDb 11856 := span_sound 160 11696 h62 gemPart63
  have h64 : HasPrefix a gemDb 12016 := span_sound 160 11856 h63 gemPart64
  have h65 : HasPrefix a gemDb 12176 := span_sound 160 12016 h64 gemPart65
  have h66 : HasPrefix a gemDb 12336 := span_sound 160 12176 h65 gemPart66
  have h67 : HasPrefix a gemDb 12496 := span_sound 160 12336 h66 gemPart67
  have h68 : HasPrefix a gemDb 12656 := span_sound 160 12496 h67 gemPart68
  have h69 : HasPrefix a gemDb 12816 := span_sound 160 12656 h68 gemPart69
  have h70 : HasPrefix a gemDb 12976 := span_sound 160 12816 h69 gemPart70
  have h71 : HasPrefix a gemDb 13136 := span_sound 160 12976 h70 gemPart71
  have h72 : HasPrefix a gemDb 13269 := span_sound 133 13136 h71 gemPart72
  exact h72

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemImpossible : sampleDoesNotMatch 5 4 gemYes gemNo :=
  bits_exclude gemKeys gemRows gemDb gemNamed gemMasksAgree gemLength gemAll gemEmpty (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem delFiniteLower :
    lowerFor delete0Target 4 := by
  apply sample_implies_lower (hbad := delImpossible)
  · decide +kernel
  · intro r h; simp only [deleteYes,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · intro r h; simp only [deleteNo,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gemFiniteLower :
    lowerFor dualGemTarget 5 := by
  apply sample_implies_lower (hbad := gemImpossible)
  · decide +kernel
  · intro r h; simp only [gemYes,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> decide +kernel
  · intro r h; simp only [gemNo,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_11058

theorem PEqualNP.Outside.L_meta_11058 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact Classical.byContradiction (PEqualNP.Outside.L_meta_11058.reduced_cases_imply_exact_negation PEqualNP.Outside.L_meta_11058.delFiniteLower PEqualNP.Outside.L_meta_11058.gemFiniteLower)
