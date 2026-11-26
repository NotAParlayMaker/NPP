import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18191

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def stepSM (R : List (Option ℕ)) (g : Gate) : List (Option ℕ) :=
  let ins := g.inputs.map fun i => R.getD i none
  R ++ [match g.op with
    | GateOp.or => ins.foldl (fun acc o => match acc, o with
        | none, o => o
        | some a, none => some a
        | some a, some b => some (min a b)) none
    | GateOp.and => ins.foldl (fun acc o => match acc, o with
        | some a, some b => some (a + b)
        | _, _ => none) (some 0)
    | _ => none]

theorem foldl_getD_lt (gs : List Gate) (R : List (Option ℕ)) (i : ℕ) (hi : i < R.length) :
    (gs.foldl stepSM R).getD i none = R.getD i none := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepSM R g) (by simp [stepSM]; omega)]
    simp [stepSM, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_getD_gate (gs : List Gate) (R : List (Option ℕ)) (k : ℕ) (g : Gate)
    (hk : gs[k]? = some g) (a b : ℕ) (hab : g.inputs = [a, b])
    (ha : a < R.length + k) (hb : b < R.length + k) :
    let m := fun i => (gs.foldl stepSM R).getD i none
    (g.op = GateOp.and → m (R.length + k) = (m a).bind fun x => Option.map (fun y => x + y) (m b)) ∧
    (g.op = GateOp.or → m (R.length + k) = (Option.map (fun x => min x ((m b).getD x)) (m a)).orElse fun _ => m b) := by
  induction gs generalizing R k with
  | nil => simp at hk
  | cons g0 gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst g0
      simp only [Nat.add_zero] at ha hb ⊢
      have hlen : R.length < (stepSM R g).length := by simp [stepSM]
      have hout : (gs.foldl stepSM (stepSM R g)).getD R.length none = (stepSM R g).getD R.length none :=
        foldl_getD_lt gs (stepSM R g) R.length hlen
      have ha' : (gs.foldl stepSM (stepSM R g)).getD a none = R.getD a none := by
        rw [foldl_getD_lt gs (stepSM R g) a (by simp [stepSM]; omega)]
        simp [stepSM, List.getD_eq_getElem?_getD, List.getElem?_append_left ha]
      have hb' : (gs.foldl stepSM (stepSM R g)).getD b none = R.getD b none := by
        rw [foldl_getD_lt gs (stepSM R g) b (by simp [stepSM]; omega)]
        simp [stepSM, List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
      rw [List.foldl_cons, hout, ha', hb']
      constructor
      · intro hop
        simp only [stepSM, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases R[a]?.getD none <;> cases R[b]?.getD none <;> simp
      · intro hop
        simp only [stepSM, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases R[a]?.getD none <;> cases R[b]?.getD none <;> simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have hlen : (stepSM R g0).length = R.length + 1 := by simp [stepSM]
      have key := ih (stepSM R g0) k hk (by omega) (by omega)
      dsimp only at key ⊢
      rw [List.foldl_cons, show R.length + (k + 1) = (stepSM R g0).length + k by omega]
      exact key

theorem main_proof :
    ∀ (n : ℕ) (C : Circuit) (S : List ℕ) (v : ℕ),
      let m : ℕ → Option ℕ := fun i => (scalarMults C n S v).getD i none
      (∀ i : Fin n, m i.val = if i.val = v then some 1 else if i.val ∈ S then some 0 else none) ∧
      ∀ (k : ℕ) (g : Gate) (a b : ℕ),
        C.gates[k]? = some g → g.inputs = [a, b] → a < n + k → b < n + k →
        (g.op = GateOp.and → m (n + k) = (m a).bind fun x => Option.map (fun y => x + y) (m b)) ∧
        (g.op = GateOp.or → m (n + k) = (Option.map (fun x => min x ((m b).getD x)) (m a)).orElse fun _ => m b) := by
  intro n C S v
  let init : List (Option ℕ) :=
    (List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none
  have hlen : init.length = n := by simp [init]
  have hsm : scalarMults C n S v = C.gates.foldl stepSM init := rfl
  dsimp only
  rw [hsm]
  constructor
  · intro i
    rw [foldl_getD_lt C.gates init i.val (by omega)]
    simp [init, List.getD_eq_getElem?_getD, i.isLt]
  · intro k g a b hk hab ha hb
    have key := foldl_getD_gate C.gates init k g hk a b hab (by omega) (by omega)
    simpa only [hlen] using key


def cost (s : Option ℕ) : ℕ := min 2 (s.getD 2)

theorem boundAND (a b : Option ℕ) :
    cost (a.bind fun x => (b.map fun y => x+y)) ≤ cost a + cost b := by
  cases a <;> cases b <;> simp [cost] <;> omega

theorem boundOR (a b : Option ℕ) :
    cost ((a.map fun x => min x (b.getD x)).orElse fun _ => b) ≤ min (cost a) (cost b) := by
  cases a <;> cases b <;> simp [cost] <;> omega

theorem solveCase (C : Circuit)
    (hG : ∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
        ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 25+j ∧ b < 25+j)
    (hO : ∀ v ∈ [0,7], 2 ≤ ((scalarMults C 25 [0,7] v).getD C.output none).getD 2)
    (z v : ℕ) (hz : z < 25) (hv : v < 25) (hzv : z ≠ v)
    (hzS : z ∈ [0,7]) (hvS : v ∈ [0,7]) :
    ∃ f : ℕ → ℕ, f z = 0 ∧ f v ≤ 1 ∧
      (∀ i < 25, i ≠ 0 → i ≠ 7 → f i = 2) ∧ 2 ≤ f C.output ∧
      ∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → f (25+j) ≤ f a + f b) ∧
        (g.op = .or → f (25+j) ≤ min (f a) (f b)) := by
  let m := fun i => (scalarMults C 25 [0,7] v).getD i none
  obtain ⟨hi,hg⟩ := main_proof 25 C [0,7] v
  change (∀ i : Fin 25, m i.val = _) at hi
  change (∀ j g a b, _ → _ → _ → _ → (_ → m (25+j) = _) ∧ (_ → m (25+j) = _)) at hg
  refine ⟨fun i => cost (m i), ?_, ?_, ?_, ?_, ?_⟩
  · have hh := hi ⟨z,hz⟩
    change m z = _ at hh
    change cost (m z) = 0
    rw [hh]
    simp [cost,hzv,hzS]
  · have hh := hi ⟨v,hv⟩
    change m v = _ at hh
    change cost (m v) ≤ 1
    rw [hh]
    simp [cost]
  · intro i h hb hn
    have hnot : i ∉ [0,7] := by simp [hb,hn]
    have hnV : i ≠ v := fun eq => hnot (eq.symm ▸ hvS)
    have hh := hi ⟨i,h⟩
    change m i = _ at hh
    change cost (m i) = 2
    rw [hh]
    simp [cost,hnV,hnot]
  · exact le_min (by decide) (hO v hvS)
  · intro j g a b hj hin
    obtain ⟨s,t,hst,_,hs,ht⟩ := (hG _ _ hj).2
    obtain ⟨rfl,rfl⟩ : s = a ∧ t = b := by simpa using hst.symm.trans hin
    obtain ⟨hand,hor⟩ := hg j g _ _ hj hin hs ht
    exact ⟨fun e => by dsimp only; rw [hand e]; apply boundAND,
           fun e => by dsimp only; rw [hor e]; apply boundOR⟩

end PEqualNP.Outside.L_meta_18191

open PEqualNP.Outside.L_meta_18191 in
theorem PEqualNP.Outside.L_meta_18191 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) → (∀ x3 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] x3).getD x1.output Option.none).getD (2 : ℕ)) → ∀ (x4 : Bool), ∃ (x5 : ℕ → ℕ), x5 (if x4 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x5 (if x4 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x6 < (25 : ℕ), x6 ≠ (0 : ℕ) → x6 ≠ (7 : ℕ) → x5 x6 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x5 x1.output ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((25 : ℕ) + x6) ≤ x5 x8 + x5 x9) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((25 : ℕ) + x6) ≤ Min.min (x5 x8) (x5 x9)) := by
  intro C hG hO b
  cases b
  · exact solveCase C hG hO 7 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact solveCase C hG hO 0 7 (by decide) (by decide) (by decide) (by decide) (by decide)
