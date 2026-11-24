import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2826

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

def step1 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def step3 (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def isGoodOp (op : Bool → Bool → Bool) : Prop :=
  ∃ p q : Bool, op = fun a b => (a == p) && (b == q)

def lookup (env : List (ℕ × Bool)) (k : ℕ) : ℕ × Bool :=
  env.getD k (10, false)

def compileGate (bgLen : ℕ) (env : List (ℕ × Bool)) (g : Gate) :
    List BinaryGate × (ℕ × Bool) :=
  match g.op, g.inputs with
  | GateOp.and, [] => ([], (10, true))
  | GateOp.and, [a] => ([], lookup env a)
  | GateOp.and, [a, b] =>
    let pa := lookup env a
    let pb := lookup env b
    ([{ op := fun u v => (u == !pa.2) && (v == !pb.2), left := pa.1, right := pb.1 }],
     (11 + bgLen, false))
  | GateOp.or, [] => ([], (10, false))
  | GateOp.or, [a] => ([], lookup env a)
  | GateOp.or, [a, b] =>
    let pa := lookup env a
    let pb := lookup env b
    ([{ op := fun u v => (u == pa.2) && (v == pb.2), left := pa.1, right := pb.1 }],
     (11 + bgLen, true))
  | GateOp.not, [] => ([], (10, true))
  | GateOp.not, a :: _ =>
    let pa := lookup env a
    ([], (pa.1, !pa.2))
  | _, _ => ([], (10, false))

lemma bool_and_xor (x y p q : Bool) :
    (((x == !p) && (y == !q)) != false) = ((x != p) && (y != q)) := by
  cases x <;> cases y <;> cases p <;> cases q <;> rfl

lemma bool_or_xor (x y p q : Bool) :
    (((x == p) && (y == q)) != true) = ((x != p) || (y != q)) := by
  cases x <;> cases y <;> cases p <;> cases q <;> rfl

lemma bool_not_xor (x p : Bool) :
    (x != !p) = !(x != p) := by
  cases x <;> cases p <;> rfl

def notVal : GateOp → ℕ
  | GateOp.not => 1
  | _ => 0

lemma notCount_nil : notCount ⟨[], 0⟩ = 0 := rfl

lemma notCount_cons (g : Gate) (rest : List Gate) :
    notCount ⟨g :: rest, 0⟩ = notVal g.op + notCount ⟨rest, 0⟩ := by
  unfold notCount
  cases h : g.op <;> simp [h, notVal, Nat.add_comm]

def compile (gs : List Gate) (bg : List BinaryGate) (env : List (ℕ × Bool)) :
    List BinaryGate × List (ℕ × Bool) :=
  match gs with
  | [] => (bg, env)
  | g :: rest =>
    let r := compileGate bg.length env g
    compile rest (bg ++ r.1) (env ++ [r.2])

def Inv (bg : List BinaryGate) (env : List (ℕ × Bool)) (w1 w3 : List Bool) : Prop :=
  env.length = w1.length ∧
  w3.length = 11 + bg.length ∧
  w3.getD 10 false = false ∧
  (∀ k, (lookup env k).1 < w3.length) ∧
  (∀ k, (w3.getD (lookup env k).1 false != (lookup env k).2) = w1.getD k false)

lemma compileGate_props (bg : List BinaryGate) (env : List (ℕ × Bool)) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    let r := compileGate bg.length env g
    (∀ b ∈ r.1, isGoodOp b.op) ∧
    r.1.length + notVal g.op ≤ 1 ∧
    (∀ (w1 w3 : List Bool), Inv bg env w1 w3 →
      Inv (bg ++ r.1) (env ++ [r.2]) (step1 w1 g) (r.1.foldl step3 w3)) := by
  have hop := hg.1
  have hlen := hg.2
  have hstep_inv : ∀ (newBg : List BinaryGate) (entry : ℕ × Bool),
      entry.1 < 11 + (bg ++ newBg).length →
      (∀ w1 w3, Inv bg env w1 w3 →
        let w3' := newBg.foldl step3 w3
        w3'.length = 11 + (bg ++ newBg).length ∧
        (∀ j < w3.length, w3'.getD j false = w3.getD j false) ∧
        (w3'.getD entry.1 false != entry.2) = g.op.eval (g.inputs.map fun i => w1.getD i false)) →
      ∀ w1 w3, Inv bg env w1 w3 →
        Inv (bg ++ newBg) (env ++ [entry]) (step1 w1 g) (newBg.foldl step3 w3) := by
    intro newBg entry hent hnew w1 w3 hinv
    obtain ⟨hl1, hl3, h10, hlt, hev⟩ := hinv
    obtain ⟨hl3', hpres, hval⟩ := hnew w1 w3 ⟨hl1, hl3, h10, hlt, hev⟩
    refine ⟨by simp [step1, hl1], hl3', ?_, ?_, ?_⟩
    · rw [hpres 10 (by omega), h10]
    · intro k
      by_cases hk : k < env.length
      · have hlk : lookup (env ++ [entry]) k = lookup env k := by
          unfold lookup; exact List.getD_append _ _ _ _ hk
        rw [hlk]; have := hlt k; simp at hl3'; omega
      · by_cases hk2 : k = env.length
        · subst hk2
          have hlk : lookup (env ++ [entry]) env.length = entry := by
            unfold lookup; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
          rw [hlk]; omega
        · have hlk : lookup (env ++ [entry]) k = (10, false) := by
            unfold lookup; exact List.getD_eq_default _ _ (by simp; omega)
          rw [hlk]; simp at hl3'; omega
    · intro k
      by_cases hk : k < env.length
      · have hlk : lookup (env ++ [entry]) k = lookup env k := by
          unfold lookup; exact List.getD_append _ _ _ _ hk
        rw [hlk, hpres _ (hlt k), hev k]
        unfold step1; rw [List.getD_append _ _ _ _ (by omega)]
      · by_cases hk2 : k = env.length
        · subst hk2
          have hlk : lookup (env ++ [entry]) env.length = entry := by
            unfold lookup; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
          rw [hlk, hval]
          unfold step1; rw [hl1, List.getD_append_right _ _ _ _ (le_refl _)]; simp
        · have hlk : lookup (env ++ [entry]) k = (10, false) := by
            unfold lookup; exact List.getD_eq_default _ _ (by simp; omega)
          rw [hlk, hpres 10 (by omega), h10]
          unfold step1; rw [List.getD_eq_default _ _ (by simp; omega)]; rfl
  rcases hop with hop | hop | hop
  · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨by simp, by simp, ?_⟩
      apply hstep_inv [] (10, true) (by simp; omega)
      intro w1 w3 ⟨_, hl3, h10, _, _⟩
      refine ⟨by simpa using hl3, fun _ _ => rfl, ?_⟩
      simp only [List.foldl_nil, h10, hop, hgi, GateOp.eval, List.map_nil, List.all_nil]; rfl
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨by simp, by simp, ?_⟩
      intro w1 w3 hinv
      exact hstep_inv [] (lookup env a) (by have := hinv.2.2.2.1 a; have := hinv.2.1; simp; omega)
        (fun w1' w3' hi => ⟨by simpa using hi.2.1, fun _ _ => rfl, by
          simp only [List.foldl_nil, hop, hgi, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true]
          exact hi.2.2.2.2 a⟩) w1 w3 hinv
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨?_, by simp, ?_⟩
      · intro g0 hg0; simp at hg0; subst hg0; exact ⟨!(lookup env a).2, !(lookup env b).2, rfl⟩
      · apply hstep_inv _ (11 + bg.length, false) (by simp)
        intro w1 w3 ⟨hl1, hl3, h10, hlt, hev⟩
        refine ⟨by simp [step3, hl3]; omega, fun j hj => by simp [step3]; exact List.getD_append _ _ _ _ hj, ?_⟩
        simp only [List.foldl_cons, List.foldl_nil, step3]
        rw [show 11 + bg.length = w3.length by omega, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero, hop, hgi, GateOp.eval, List.map_cons,
          List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [bool_and_xor, hev a, hev b]
    · simp [hgi] at hlen
  · rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨by simp, by simp, ?_⟩
      apply hstep_inv [] (10, false) (by simp; omega)
      intro w1 w3 ⟨_, hl3, h10, _, _⟩
      refine ⟨by simpa using hl3, fun _ _ => rfl, ?_⟩
      simp only [List.foldl_nil, h10, hop, hgi, GateOp.eval, List.map_nil, List.any_nil]; rfl
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨by simp, by simp, ?_⟩
      intro w1 w3 hinv
      exact hstep_inv [] (lookup env a) (by have := hinv.2.2.2.1 a; have := hinv.2.1; simp; omega)
        (fun w1' w3' hi => ⟨by simpa using hi.2.1, fun _ _ => rfl, by
          simp only [List.foldl_nil, hop, hgi, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
          exact hi.2.2.2.2 a⟩) w1 w3 hinv
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨?_, by simp, ?_⟩
      · intro g0 hg0; simp at hg0; subst hg0; exact ⟨(lookup env a).2, (lookup env b).2, rfl⟩
      · apply hstep_inv _ (11 + bg.length, true) (by simp)
        intro w1 w3 ⟨hl1, hl3, h10, hlt, hev⟩
        refine ⟨by simp [step3, hl3]; omega, fun j hj => by simp [step3]; exact List.getD_append _ _ _ _ hj, ?_⟩
        simp only [List.foldl_cons, List.foldl_nil, step3]
        rw [show 11 + bg.length = w3.length by omega, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero, hop, hgi, GateOp.eval, List.map_cons,
          List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [bool_or_xor, hev a, hev b]
    · simp [hgi] at hlen
  · rcases hgi : g.inputs with _ | ⟨a, rest⟩
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨by simp, by simp, ?_⟩
      apply hstep_inv [] (10, true) (by simp; omega)
      intro w1 w3 ⟨_, hl3, h10, _, _⟩
      refine ⟨by simpa using hl3, fun _ _ => rfl, ?_⟩
      simp only [List.foldl_nil, h10, hop, hgi, GateOp.eval, List.map_nil, List.headD_nil]; rfl
    · simp only [compileGate, hop, hgi, notVal]
      refine ⟨by simp, by simp, ?_⟩
      intro w1 w3 hinv
      exact hstep_inv [] ((lookup env a).1, !(lookup env a).2)
        (by have := hinv.2.2.2.1 a; have := hinv.2.1; simp; omega)
        (fun w1' w3' hi => ⟨by simpa using hi.2.1, fun _ _ => rfl, by
          simp only [List.foldl_nil, hop, hgi, GateOp.eval, List.map_cons, List.headD_cons]
          rw [bool_not_xor, hi.2.2.2.2 a]⟩) w1 w3 hinv

lemma compile_props (gs : List Gate) :
    ∀ (bg : List BinaryGate) (env : List (ℕ × Bool)),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ b ∈ bg, isGoodOp b.op) →
      let res := compile gs bg env
      (∀ b ∈ res.1, isGoodOp b.op) ∧
      res.1.length + notCount ⟨gs, 0⟩ ≤ bg.length + gs.length ∧
      ∀ (x0 w1 : List Bool), Inv bg env w1 (bg.foldl step3 (x0 ++ [false])) →
        Inv res.1 res.2 (gs.foldl step1 w1) (res.1.foldl step3 (x0 ++ [false])) := by
  induction gs with
  | nil =>
    intro bg env _ hbg
    exact ⟨hbg, by simp [compile, notCount_nil], fun x0 w1 hinv => hinv⟩
  | cons g rest ih =>
    intro bg env hgs hbg
    have hg := hgs g (by simp)
    have hrest : ∀ g' ∈ rest, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (by simp [hg'])
    obtain ⟨hr_good, hr_len, hr_inv⟩ := compileGate_props bg env g hg
    let r := compileGate bg.length env g
    have hbg' : ∀ b ∈ bg ++ r.1, isGoodOp b.op := by
      intro b hb; simp only [List.mem_append] at hb
      rcases hb with hb | hb
      · exact hbg b hb
      · exact hr_good b hb
    obtain ⟨h1, h2, h3⟩ := ih (bg ++ r.1) (env ++ [r.2]) hrest hbg'
    refine ⟨h1, ?_, ?_⟩
    · change (compile rest (bg ++ r.1) (env ++ [r.2])).1.length + notCount ⟨g :: rest, 0⟩ ≤
        bg.length + (g :: rest).length
      rw [notCount_cons]
      have hr_len' : r.1.length + notVal g.op ≤ 1 := hr_len
      simp only [List.length_append, List.length_cons] at h2 ⊢
      omega
    · intro x0 w1 hinv
      simp only [compile, List.foldl_cons]
      apply h3 x0 (step1 w1 g)
      rw [List.foldl_append]
      exact hr_inv w1 (bg.foldl step3 (x0 ++ [false])) hinv

def initEnv : List (ℕ × Bool) :=
  List.ofFn fun i : Fin 10 => (i.val, false)

lemma init_inv (x5 : List Bool) (hx : x5.length = 10) :
    Inv [] initEnv x5 (([] : List BinaryGate).foldl step3 (x5 ++ [false])) := by
  refine ⟨by simp [initEnv, hx], by simp [hx], ?_, ?_, ?_⟩
  · simp only [List.foldl_nil]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hx]
  · intro k
    simp only [List.foldl_nil, List.length_append, List.length_cons, List.length_nil, hx]
    by_cases hk : k < 10
    · have : lookup initEnv k = (k, false) := by
        unfold lookup initEnv
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [hk]
      rw [this]; omega
    · have : lookup initEnv k = (10, false) := by
        unfold lookup initEnv
        exact List.getD_eq_default _ _ (by simp; omega)
      rw [this]; omega
  · intro k
    simp only [List.foldl_nil]
    by_cases hk : k < 10
    · have : lookup initEnv k = (k, false) := by
        unfold lookup initEnv
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [hk]
      rw [this, List.getD_append _ _ _ _ (by omega)]
      simp
    · have : lookup initEnv k = (10, false) := by
        unfold lookup initEnv
        exact List.getD_eq_default _ _ (by simp; omega)
      rw [this]
      have hL : (x5 ++ [false]).getD 10 false = false := by
        rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hx]
      have hR : x5.getD k false = false := List.getD_eq_default _ _ (by omega)
      rw [hL, hR]; rfl

end PEqualNP.Outside.L_meta_2826

theorem PEqualNP.Outside.L_meta_2826 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Bool), (∀ x5 ∈ x3.gates, ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → (x3.eval (x5 ++ [Bool.false]) != x4) = x1.eval x5 := by
  intro x1 hfan
  let res := PEqualNP.Outside.L_meta_2826.compile x1.gates [] PEqualNP.Outside.L_meta_2826.initEnv
  obtain ⟨hgood, hsz, hinv⟩ :=
    PEqualNP.Outside.L_meta_2826.compile_props x1.gates [] PEqualNP.Outside.L_meta_2826.initEnv hfan (by simp)
  let outPair := PEqualNP.Outside.L_meta_2826.lookup res.2 x1.output
  refine ⟨⟨res.1, outPair.1⟩, outPair.2, hgood, ?_, ?_⟩
  · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size, PEqualNP.CircuitLowerBounds.Circuit.size,
      PEqualNP.NotBracket.notCount] using hsz
  · intro x5 hx5
    have h := hinv x5 x5 (PEqualNP.Outside.L_meta_2826.init_inv x5 hx5)
    exact h.2.2.2.2 x1.output
