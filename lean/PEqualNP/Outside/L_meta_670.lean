import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670_aux.Helpers
open PEqualNP.CircuitLowerBounds

def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0

def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]

def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0

def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, hM]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

def cands (M : ℕ) (S : List ℕ) : List ℕ :=
  M :: 0 :: ((0 :: S).map (fun a => M ^^^ a) ++ (0 :: S) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a &&& b) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a ||| b))

def nub : List ℕ → List ℕ
  | l => l.nodup

def next (M : ℕ) (S : List ℕ) : List ℕ :=
  (cands M S |>.nub |>.filter fun t => t ∉ S)

def reach (M : ℕ) (good : ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, S => (0 :: S).any good
  | k + 1, S => (0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])

theorem cands_mono (M : ℕ) (S S' : List ℕ) (h : ∀ x, x ∈ S → x ∈ S') (t : ℕ)
    (ht : t ∈ cands M S) : t ∈ cands M S' := by
  have h0 : ∀ x, x ∈ (0 :: S) → x ∈ (0 :: S') := by
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · simp [hx]
    · exact List.mem_cons_of_mem _ (h x hx)
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at ht
  rcases ht with ht | ht | ((⟨a, ha, e⟩ | ht) | ⟨a, ha, b, hb, e⟩) | ⟨a, ha, b, hb, e⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨a, ?_, e⟩))))
    have := h0 a (by simpa using ha); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ?_))))
    have := h0 t (by simpa using ht); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inr ⟨a, ?_, b, ?_, e⟩)))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this
  · refine Or.inr (Or.inr (Or.inr ⟨a, ?_, b, ?_, e⟩))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this

theorem mem_next (M : ℕ) (S : List ℕ) (t : ℕ) : t ∈ next M S ↔ t ∈ cands M S ∧ t ∉ S := by
  simp [next, mem_nub]

theorem any_congr_mem (l l' : List ℕ) (f f' : ℕ → Bool) (hl : ∀ x, x ∈ l ↔ x ∈ l')
    (hf : ∀ x, f x = f' x) : l.any f = l'.any f' := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).1 hx, by rw [← hf]; exact e⟩
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).2 hx, by rw [← hf]; exact e⟩

theorem reach_congr (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S S' : List ℕ),
    (∀ x, x ∈ S ↔ x ∈ S') → reach M good k S = reach M good k S' := by
  intro k
  induction k with
  | zero =>
    intro S S' h
    simp only [reach]
    exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
  | succ k ih =>
    intro S S' h
    simp only [reach]
    congr 1
    · exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
    · apply any_congr_mem
      · intro t
        rw [mem_next, mem_next]
        exact ⟨fun ⟨a, b⟩ => ⟨cands_mono M S S' (fun y => (h y).1) x a, by rwa [← h]⟩,
          fun ⟨a, b⟩ => ⟨cands_mono M S' S (fun y => (h y).2) x a, by rwa [← h]⟩⟩
      · intro t
        exact ih _ _ (by intro x; simp [h])
        exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)

theorem reach_mono (M : ℕ) (good : ℕ → Bool) (k : ℕ) (S S' : List ℕ)
    (h : ∀ x, x ∈ S → x ∈ S') (ht : reach M good k S = true) :
    reach M good k S' = true := by
  induction k with
  | zero =>
    rw [reach] at ht ⊢
    obtain ⟨a, ha, hgood⟩ := List.any_eq_true.1 ht
    by_cases ha0 : a = 0
    · subst a; simp [ha0] at ha; simp [List.mem_nil] at ha
    · simp [List.mem_cons] at ha
      exact List.any_eq_true.2 ⟨a, (h a ha.2 ▸ ha), hgood⟩
  | succ k ih =>
    rw [reach] at ht ⊢
    obtain hgood | hnext := List.any_eq_true.1 ht
    · exact Or.inl ⟨a, ha, hgood⟩
    · obtain ⟨t, ht, hnext⟩ := List.any_eq_true.1 hnext
      have := reach_mono M good k (S ++ [t]) (fun x hx => List.mem_append.2 hx) hnext
      exact Or.inr ⟨t, (mem_next M S' t).2 ⟨?_, by rwa [← mem_next]⟩, ?_⟩
      · exact cands_mono M S S' h t ht.1
      · exact this

theorem reach_sound (M : ℕ) (good : ℕ → Bool) (gs : List Gate) (k : ℕ) (T0 : List ℕ)
    (o : ℕ) (hk : k < T0.length + gs.length) (hok : ∀ g ∈ gs, GOk g)
    (hgood : good ((tabs M T0 gs).getD o 0) = true) :
    reach M good k T0 = true := by
  induction gs with
  | nil =>
    intro T0 o hk _ hgood
    rw [tabs] at hgood
    have : o < T0.length := by omega
    simp only [List.foldl_nil] at hgood
    have : o < T0.length := by omega
    exact List.any_eq_true.2 ⟨o, (List.mem_range.1 this), hgood⟩
  | cons g gs ih =>
    intro T0 o hk hok hgood
    have hok' := ih _ _ _ (fun g' hg' => hok g' (by simp [List.mem_append, List.mem_cons_of_mem] at hg'; simpa using hg'))
    have hg := hok g (by simp)
    have hlen := hg.2
    simp only [tabs, tstep, List.foldl_cons] at hgood
    have hnext : o ≤ T0.length + gs.length := by omega
    have hnext' : o < T0.length + gs.length + 1 := by omega
    by_cases ho : o < T0.length
    · have hgood' : good (T0.getD o 0) = true := by
        have hM : M.testBit o = true := by simp
        have := hgood
        simp only [List.getD_append] at this
        exact this
      exact List.any_eq_true.2 ⟨o, (List.mem_range.1 ho), hgood'⟩
    · have ho' : T0.length ≤ o := by omega
      have hlen' : o < T0.length + gs.length + 1 := by omega
      obtain ⟨o', rfl⟩ : ∃ o', o = T0.length + o' := ⟨o - T0.length, by omega⟩
      have ho' : o' < gs.length + 1 := by omega
      by_cases ho' : o' < gs.length
      · have ih' := ih (T0 ++ [gt M g.op (g.inputs.map fun i => T0.getD i 0)]) o' _ hok'
          have hg' : good ((tabs M (T0 ++ [gt M g.op (g.inputs.map fun i => T0.getD i 0)]) gs).getD o' 0) = true := by
            simp only [tabs, tstep, List.foldl_cons]
            exact hgood
          have := ih' (by omega) hok' hg'
          simp only [reach] at this
          obtain hgood | hnext := List.any_eq_true.1 this
          · exact Or.inl ⟨o, (List.mem_range.1 (by omega)), hgood⟩
          · obtain ⟨t, ht, hnext⟩ := List.any_eq_true.1 hnext
            have ht' := ht
            have hnext' : reach M good (gs.length - 1) ((T0 ++ [gt M g.op (g.inputs.map fun i => T0.getD i 0)]) ++ [t]) = true := by
              simpa [reach] using hnext
            exact Or.inr ⟨t, (mem_next M (T0 ++ [gt M g.op (g.inputs.map fun i => T0.getD i 0)]) t).2 ⟨?_, by rwa [← mem_next]⟩, ?_⟩
            · exact cands_mono M (T0 ++ [gt M g.op (g.inputs.map fun i => T0.getD i 0)]) (T0 ++ [gt M g.op (g.inputs.map fun i => T0.getD i 0)]) (by simp) t (by simp)
            · exact hnext'
      · have ho' : gs.length ≤ o' := by omega
        have hgood' : good (gt M g.op (g.inputs.map fun i => (T0 ++ [gt M g.op (g.inputs.map fun i => T0.getD i 0))).getD i 0)) = true := by
          simp only [show o = T0.length + gs.length from by omega]
          exact hgood
        exact Or.inl ⟨o, (List.mem_range.1 (by omega)), hgood'⟩

theorem mod_eq_of_testBit (B t tgt : ℕ) (htgt : tgt < 2 ^ B)
    (h : ∀ p, p < B → t.testBit p = tgt.testBit p) : t % 2 ^ B = tgt := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < B
  · simp [hi, h i hi]
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem lower_of_search (n B : ℕ) (f : (Fin n → Bool) → Bool) (T0 : List ℕ) (tgt k : ℕ)
    (htgt : tgt < 2 ^ B)
    (hpt : ∀ p, p < B → ∃ x : Fin n → Bool, List.ofFn x = T0.map (fun t => t.testBit p) ∧
      f x = tgt.testBit p)
    (hsearch : reach (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) k T0 = false) :
    ¬ HasCircuitSize n f k := by
  rintro ⟨C, hC, hsize, hev⟩
  have hok : ∀ g ∈ C.gates, GOk g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    refine ⟨?_, h2⟩
    simpa [Set.mem_insert_iff] using h1
  have hgood : (fun t => t % 2 ^ B == tgt) ((tabs (2 ^ B - 1) T0 C.gates).getD C.output 0)
      = true := by
    simp only [beq_iff_eq]
    apply mod_eq_of_testBit B _ tgt htgt
    intro p hp
    obtain ⟨x, hx, hfx⟩ := hpt p hp
    have hM : (2 ^ B - 1).testBit p = true := by
      rw [Nat.testBit_two_pow_sub_one]; simpa using hp
    have := hev x
    rw [hfx] at this
    rw [← this, Circuit.eval, Circuit.wires, hx, wires_tabs _ p hM _ _ hok,
      getD_map_testBit]
  have := reach_sound (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) C.gates k T0 C.output hsize hok hgood
  rw [hsearch] at this
  exact absurd this (by decide)

end PEqualNP.Outside.L_meta_670_aux.Helpers

namespace PEqualNP.Outside.L_meta_670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_670_aux.Helpers.TableSearch

def f : (Fin 9 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def T0 : List ℕ :=
  [8938538619961731399716016665470564084986243880394928918482374295814509353382364651201249532111268951793354572124324033902502588541297713297622432670722730,
   10726246343954077679659219998564676901983492656473914702178849154977411224058837581441499438533522742152025486549188840683003106249557255957146919204867276,
   12619113345828326681952023527723149296451167831145782002563351947032248498892750095813528751215909108414147631234339812568238948528890889361349316711608560,
   13355637471071225126423931515722554897411352724014212858744092333045803858750303603351283347590378511628981150567083381395178964979993470452478654262869760,
   13407603346151304507647333602124270744930157291580986197148043437687863763597662002711256755796972443613438635551055889478487182262900810351549134401372160,
   13407807926820848549984871490950625460264621687587329935306297008442977448960781863686381587396241115434734742314166555940848600484775015044616064818216960,
   13407807929942597098847186273910239236969444018900783322580063136098668673514857287274768220802268387129003177701362428774192761570871467260109520434626560,
   13407807929942597099574024998205846127439963814395998898511282403621620416268583029620646167694378705270794824322841769944638336182637648515027502377205760,
   13407807929942597099574024998205846127479365820592393377723561443721764030073431184712636981971479856705023170278632780869088242247907112362425735876444160]

def tgt : ℕ :=
  13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080

theorem key : ∀ p, p < 512 → (List.ofFn fun i : Fin 9 => p.testBit i.val)
    = T0.map (fun t => t.testBit p) ∧
    f (fun i => p.testBit i.val) = Nat.testBit tgt p := by decide

theorem petersen_minus_vertex_no_15 : ¬ HasCircuitSize 9 f 15 := by
  apply lower_of_search 9 512 _ T0 tgt 15 (by norm_num) _ (by decide +kernel)
  intro p hp
  obtain ⟨hx, hf⟩ := key p hp
  exact ⟨fun i => p.testBit i.val, hx, hf⟩

end PEqualNP.Outside.L_meta_670

theorem PEqualNP.Outside.L_meta_670 :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  have : PEqualNP.Outside.L_meta_670.f =
      (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    simp [PEqualNP.Outside.L_meta_670.f]
  rw [this]
  exact PEqualNP.Outside.L_meta_670.petersen_minus_vertex_no_15
