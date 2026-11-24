import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3268

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 516

def raw : List Word := [0x843f80211fc01f807e0f80441f80f810821108fc3f0f020882108488a1f8f83c0007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07,
  0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038,
  0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0,
  0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000,
  0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000,
  0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000,
  0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000,
  0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000,
  0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000]

def row (i : Nat) (j : Fin 9) : Bool := (raw.getD j.val 0).getLsbD i

def target (x : Fin 9 → Bool) : Bool :=
  [1,12,23,34,40,5,16,27,38,57,68,85].any fun e : Nat =>
    x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

set_option maxRecDepth 4096 in
theorem targets : ∀ i : Fin 258, target (row i.val) = false ∧ target (row (i.val+258)) = true := by
  decide +kernel

def Covers (s : Finset Word) : Prop :=
  ∀ i : Fin 258, ∃ w ∈ s, w.getLsbD i.val ≠ w.getLsbD (i.val+258)

def mix (op : Bool) (a b : Word) : Word := if op then a ||| b else a &&& b

def Can : Nat → Finset Word → Prop
  | 0, s => Covers s ∧ s.card ≤ 6
  | k+1, s => Can k s ∨
      (Covers s ∧ ∃ a ∈ s, ∃ b ∈ s, ∃ op : Bool, ∃ t : Finset Word,
        a ≠ b ∧ mix op a b ≠ a ∧ mix op a b ≠ b ∧ mix op a b ∉ s ∧ t ⊆ s ∧ s ⊆ insert a (insert b t) ∧
        Can k (insert (mix op a b) t))

theorem can_covers {k s} (h : Can k s) : Covers s := by
  induction k with
  | zero => exact h.1
  | succ k ih => exact h.elim ih And.left

theorem can_size {k s} (h : Can k s) : s.card ≤ 6+k := by
  induction k generalizing s with
  | zero => exact h.2
  | succ k ih =>
    rcases h with h | ⟨_, a, _, b, _, op, t, _, hwa, hwb, hfresh, hts, hst, hc⟩
    · exact Nat.le_trans (ih h) (by omega)
    · have h1 := ih hc
      have hm : mix op a b ∉ t := fun h => hfresh (hts h)
      rw [Finset.card_insert_of_notMem hm] at h1
      have h2 := Finset.card_le_card hst
      have h3 := Finset.card_insert_le a (insert b t)
      have h4 := Finset.card_insert_le b t
      omega

def delta (w : Word) : Word := w ^^^ (w >>> 258)

def unionBits : List Word → Word
  | [] => 0
  | w :: ws => delta w ||| unionBits ws

def mask : Word := 2^258-1

theorem mask_bits : ∀ i : Fin 516, mask.getLsbD i = decide (i.val < 258) := by decide +kernel

theorem covered_bits (ws : List Word) (h : Covers ws.toFinset) :
    unionBits ws &&& mask = mask := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, mask_bits ⟨i,hi⟩]
  by_cases hn : i < 258
  · simp only [hn, decide_true, Bool.and_true]
    obtain ⟨w,hw,d⟩ := h ⟨i,hn⟩
    have hz : (delta w).getLsbD i = true := by
      simp only [delta, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
      change w.getLsbD i ≠ w.getLsbD (i+258) at d
      rw [Nat.add_comm 258 i]
      revert d
      cases w.getLsbD i <;> cases w.getLsbD (i+258) <;> decide
    have hm := List.mem_toFinset.mp hw
    clear h hw d
    induction ws with
    | nil => simp at hm
    | cons v vs ih =>
      rw [unionBits, BitVec.getLsbD_or, Bool.or_eq_true]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl hz
      · exact Or.inr (ih hm)
  · simp [hn]

def ones : Word := BitVec.allOnes 516

def obs (i : Nat) (ws : List Word) := ws.map fun w => w.getLsbD i

def wordOp (op : GateOp) (xs : List Word) : Word :=
  match op with
  | .and => xs.foldr (· &&& ·) ones
  | _ => xs.foldr (· ||| ·) 0

def nextWord (ws : List Word) (g : Gate) :=
  wordOp g.op (g.inputs.map fun i => ws.getD i 0)

def extend (ws : List Word) (g : Gate) := ws ++ [nextWord ws g]

def goodGate (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

theorem read_obs (ws : List Word) (i j : Nat) :
    (obs i ws).getD j false = (ws.getD j 0).getLsbD i := by
  induction ws generalizing j with
  | nil => simp [obs]
  | cons a as ih => cases j with
    | zero => rfl
    | succ j => exact ih j

theorem ones_bit (i : Nat) (hi : i < 516) : ones.getLsbD i = true := by
  rw [ones, BitVec.getLsbD_allOnes, decide_eq_true hi]

theorem bit_wordOp (o : GateOp) (ho : o = .and ∨ o = .or) (xs : List Word)
    (i : Nat) (hi : i < 516) :
    (wordOp o xs).getLsbD i = o.eval (obs i xs) := by
  rcases ho with rfl | rfl
  · induction xs with
    | nil => exact ones_bit i hi
    | cons a as ih =>
      simp [wordOp, GateOp.eval, obs] at ih ⊢
      rw [ih]
  · induction xs with
    | nil => change (0 : Word).getLsbD i = false; simp
    | cons a as ih =>
      simp [wordOp, GateOp.eval, obs] at ih ⊢
      rw [ih]

theorem eval_obs (gs : List Gate) (leg : ∀ g ∈ gs, goodGate g) (ws : List Word)
    (i : Nat) (hi : i < 516) :
    obs i (gs.foldl extend ws) = (Circuit.mk gs 0).wires (obs i ws) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change obs i (gs.foldl extend (extend ws g)) = (Circuit.mk gs 0).wires _
    rw [ih (fun u hu => leg u (List.mem_cons_of_mem _ hu))]
    congr 1
    change (ws ++ [nextWord ws g]).map _ = obs i ws ++ [_]
    rw [List.map_append]
    congr 1
    change [((nextWord ws g).getLsbD i)] = [_]
    simp only [nextWord, bit_wordOp _ (leg g List.mem_cons_self).1 _ _ hi, read_obs]
    simp [obs, List.map_map, Function.comp_def]

theorem proper_inputs (ws : List Word) (g : Gate) (hg : goodGate g)
    (hn : nextWord ws g ≠ 0) (ho : nextWord ws g ≠ ones) (fresh : nextWord ws g ∉ ws) :
    ∃ a ∈ ws, ∃ b ∈ ws, ∃ op : Bool,
      nextWord ws g = mix op a b ∧ a ≠ b ∧ a ≠ 0 ∧ a ≠ ones ∧ b ≠ 0 ∧ b ≠ ones := by
  rcases g with ⟨o,p⟩
  obtain ⟨hop,hlen⟩ := hg
  change p.length ≤ 2 at hlen
  change o = .and ∨ o = .or at hop
  have memRead (j : Nat) (h : ws.getD j 0 ≠ 0) : ws.getD j 0 ∈ ws := by
    by_cases hj : j < ws.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem _
    · exact False.elim (h (List.getD_eq_default _ _ (by omega)))
  cases p with
  | nil =>
    rcases hop with rfl | rfl
    · exact (ho rfl).elim
    · exact (hn rfl).elim
  | cons u us =>
    cases us with
    | nil =>
      have ev : nextWord ws ⟨o,[u]⟩ = ws.getD u 0 := by
        rcases hop with rfl | rfl
        · exact BitVec.and_allOnes
        · exact BitVec.or_zero
      rw [ev] at fresh hn
      exact (fresh (memRead u hn)).elim
    | cons v vs =>
      have : vs = [] := by simpa using hlen
      subst vs
      let a := ws.getD u 0
      let b := ws.getD v 0
      have M (op : Bool) (eqw : nextWord ws ⟨o,[u,v]⟩ = mix op a b) :
          ∃ a ∈ ws, ∃ b ∈ ws, ∃ op : Bool, nextWord ws ⟨o,[u,v]⟩ = mix op a b ∧
            a ≠ b ∧ a ≠ 0 ∧ a ≠ ones ∧ b ≠ 0 ∧ b ≠ ones := by
        rw [eqw] at hn ho fresh
        have na : mix op a b ≠ a := by
          intro e
          rw [e] at fresh hn
          exact fresh (memRead u hn)
        have nb : mix op a b ≠ b := by
          intro e
          rw [e] at fresh hn
          exact fresh (memRead v hn)
        have A : a ≠ 0 ∧ a ≠ ones ∧ b ≠ 0 ∧ b ≠ ones := by
          cases op
          · change a &&& b ≠ 0 at hn
            change a &&& b ≠ a at na
            change a &&& b ≠ b at nb
            exact ⟨fun e => hn (e.symm ▸ BitVec.zero_and), fun e => nb (e.symm ▸ BitVec.allOnes_and),
              fun e => hn (e.symm ▸ BitVec.and_zero), fun e => na (e.symm ▸ BitVec.and_allOnes)⟩
          · change a ||| b ≠ ones at ho
            change a ||| b ≠ a at na
            change a ||| b ≠ b at nb
            exact ⟨fun e => nb (e.symm ▸ BitVec.zero_or), fun e => ho (e.symm ▸ BitVec.allOnes_or),
              fun e => na (e.symm ▸ BitVec.or_zero), fun e => ho (e.symm ▸ BitVec.or_allOnes)⟩
        refine ⟨a,memRead u A.1,b,memRead v A.2.2.1,op,eqw,?_,A⟩
        intro he
        cases op <;> simp [mix, he] at na
      rcases hop with rfl | rfl
      · apply M false
        change a &&& (b &&& BitVec.allOnes _) = a &&& b
        rw [BitVec.and_allOnes]
      · apply M true
        simp [nextWord, wordOp, mix, a, b]

def liveIn (s : Finset Word) (ws : List Word) : Prop :=
  ∀ w ∈ s, w ∈ ws ∧ w ≠ 0 ∧ w ≠ ones

theorem backStep {k : Nat} (g : Gate) (hg : goodGate g) (ws : List Word)
    (s : Finset Word) (hl : liveIn s (extend ws g)) (hc : Can k s) :
    ∃ u, liveIn u ws ∧ Can (k+1) u := by
  let w := nextWord ws g
  have old (z : Word) (hz : z ∈ s) (hne : z ≠ w) : z ∈ ws := by
    have := (hl z hz).1
    simpa [extend, hne, w] using this
  by_cases hw : w ∉ s ∨ w ∈ ws
  · refine ⟨s, fun z hz => ⟨?_, (hl z hz).2⟩, Or.inl hc⟩
    by_cases he : z = w
    · subst z
      exact hw.resolve_left (not_not.mpr hz)
    · exact old z hz he
  push Not at hw
  obtain ⟨a,ha,b,hb,op,e,ab,na,oa,nb,ob⟩ :=
    proper_inputs ws g hg (hl w hw.1).2.1 (hl w hw.1).2.2 hw.2
  change w = mix op a b at e
  let t := s.erase w
  let u := insert a (insert b t)
  have tl : liveIn t ws := by
    intro z hz
    have hh := Finset.mem_erase.mp hz
    exact ⟨old _ hh.2 hh.1,(hl z hh.2).2⟩
  have ul : liveIn u ws := by
    intro z hz
    simp only [u,Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact ⟨ha,na,oa⟩
    · exact ⟨hb,nb,ob⟩
    · exact tl _ hz
  have ut : t ⊆ u := fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  have au : a ∈ u := by simp [u]
  have bu : b ∈ u := by simp [u]
  have wf : mix op a b ∉ u := fun h => hw.2 ((ul _ (e ▸ h)).1)
  have cv : Covers u := by
    intro i
    obtain ⟨z,hz,hd⟩ := can_covers hc i
    by_cases he : z = w
    · subst z
      by_contra! hh
      have ea := hh a au
      have eb := hh b bu
      rw [e] at hd
      cases op <;> simp [mix,ea,eb] at hd
    · exact ⟨z,ut (Finset.mem_erase.mpr ⟨he,hz⟩),hd⟩
  refine ⟨u,ul,Or.inr ⟨cv,a,au,b,bu,op,t,ab,fun e => wf (by rw [e]; exact au),
    fun e => wf (by rw [e]; exact bu),wf,ut,Finset.Subset.rfl,?_⟩⟩
  rwa [← e, Finset.insert_erase hw.1]

theorem backward (gs : List Gate) (leg : ∀ g ∈ gs, goodGate g) (ws : List Word)
    (s : Finset Word) (hl : liveIn s (gs.foldl extend ws)) (hc : Can 0 s) :
    ∃ u, liveIn u ws ∧ Can gs.length u := by
  induction gs generalizing ws with
  | nil => exact ⟨s,hl,hc⟩
  | cons g gs ih =>
    obtain ⟨u,hu,h⟩ := ih (fun a ha => leg a (List.mem_cons_of_mem _ ha)) (extend ws g) hl
    exact backStep g (leg g List.mem_cons_self) ws u hu h

def seed : Word := raw.getD 0 0 ||| raw.getD 2 0

theorem raw_obs (i : Nat) : obs i raw = List.ofFn (row i) := by
  apply List.ext_getElem
  · simp only [obs, List.length_map, List.length_ofFn]
    rfl
  · intro j h h'
    have hj : j < raw.length := by simpa [obs] using h
    simp only [obs,List.getElem_map,List.getElem_ofFn,row,List.getD_eq_getElem _ _ hj]

theorem same_on_pairs (ws : List Word) (gates : List Gate) (out : Nat) (S : Finset Nat)
    (len : S.card ≤ 6)
    (ag : ∀ i : Fin 258, obs i ws = (Circuit.mk gates out).wires (List.ofFn (row i)))
    (bg : ∀ i : Fin 258, obs (i.val+258) ws = (Circuit.mk gates out).wires (List.ofFn (row (i.val+258))))
    (hn : ¬ ∃ x y : Fin 9 → Bool, (∀ j ∈ S,
      ((Circuit.mk gates out).wires (List.ofFn x)).getD j false =
      ((Circuit.mk gates out).wires (List.ofFn y)).getD j false) ∧ target x ≠ target y) :
    ∃ s, liveIn s ws ∧ Can 0 s := by
  let t := S.image (fun j => ws.getD j 0)
  let s := (t.erase 0).erase ones
  have hm {w} (h : w ∈ s) : w ∈ t ∧ w ≠ 0 ∧ w ≠ ones := by
    simpa [s,and_assoc,and_comm,and_left_comm] using h
  refine ⟨s,?_,?_,?_⟩
  · intro w hw
    obtain ⟨mem,nz,no⟩ := hm hw
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp mem
    refine ⟨?_,nz,no⟩
    by_cases hj : j < ws.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem _
    · exact (nz (List.getD_eq_default _ _ (by omega))).elim
  · intro i
    by_contra! hall
    apply hn
    refine ⟨row i, row (i.val+258),?_,by rw [(targets i).1,(targets i).2]; decide⟩
    intro j hj
    rw [← ag i,← bg i, read_obs,read_obs]
    let w := ws.getD j 0
    change w.getLsbD _ = w.getLsbD _
    by_cases hz : w = 0
    · simp [hz]
    by_cases ho : w = ones
    · rw [ho,ones_bit _ (by omega),ones_bit _ (by omega)]
    exact hall w (Finset.mem_erase.mpr ⟨ho,Finset.mem_erase.mpr ⟨hz,Finset.mem_image_of_mem _ hj⟩⟩)
  · exact (Finset.card_le_card (show s ⊆ t from fun _ h => (hm h).1)).trans
      (Finset.card_image_le.trans len)

theorem fold_keep (gs : List Gate) (ws : List Word) (j : Nat) (hj : j < ws.length) :
    (gs.foldl extend ws).getD j 0 = ws.getD j 0 := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl extend (extend ws g)).getD j 0 = _
    rw [ih _ (by simp [extend]; omega)]
    exact List.getD_append _ _ _ _ hj

theorem mix_comm (op : Bool) (a b : Word) : mix op a b = mix op b a := by
  cases op <;> simp [mix, BitVec.or_comm, BitVec.and_comm]

theorem reduction
    (root : ∀ ws ∈ (raw ++ [seed]).sublists, ws.Nodup →
      unionBits ws &&& mask = mask → ¬ Can 7 ws.toFinset)
    (c : Circuit) (mono : Monotone2 c) (sz : c.size = 8)
    (firstGate : ∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (S : Finset Nat) (hS : S.card ≤ 6) :
    ∃ x y : Fin 9 → Bool, (∀ j ∈ S, (c.wires (List.ofFn x)).getD j false =
      (c.wires (List.ofFn y)).getD j false) ∧ target x ≠ target y := by
  classical
  by_contra hn
  rcases c with ⟨gs,o⟩
  change gs.length = 8 at sz
  cases gs with
  | nil => simp at sz
  | cons g gs =>
    let allW := (g :: gs).foldl extend raw
    have good : ∀ v ∈ g :: gs, goodGate v := fun v hv =>
      ⟨by simpa using (mono v hv).1,(mono v hv).2⟩
    have ev (i : Nat) (hi : i < 516) :
        obs i allW = (Circuit.mk (g::gs) o).wires (List.ofFn (row i)) := by
      rw [← raw_obs]
      exact eval_obs _ good _ i hi
    obtain ⟨s,hl,hc⟩ := same_on_pairs allW (g::gs) o S hS (fun i => ev i (by omega))
      (fun i => ev _ (by omega)) hn
    have firstEq : nextWord raw g = seed := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have h := firstGate (row i)
      rw [← ev i hi, read_obs] at h
      have hk : allW.getD 9 0 = nextWord raw g := by
        change (gs.foldl extend (extend raw g)).getD 9 0 = _
        rw [fold_keep _ _ _ (by simp only [extend,List.length_append,List.length_singleton]; decide)]
        rfl
      rw [hk] at h
      exact h.trans (BitVec.getLsbD_or ..).symm
    obtain ⟨u,hu,can⟩ := backward gs (fun v hv => good v (List.mem_cons_of_mem _ hv))
      (extend raw g) s hl hc
    have er : extend raw g = raw ++ [seed] := by rw [extend,firstEq]
    rw [er] at hu
    let ws := (raw ++ [seed]).filter (· ∈ u)
    have he : ws.toFinset = u := by
      ext w
      simp only [ws,List.mem_toFinset,List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun h => ⟨(hu w h).1,h⟩⟩
    have nd : (raw ++ [seed]).Nodup := by decide +kernel
    have cc : Can 7 ws.toFinset := by
      have hs : gs.length = 7 := by simpa using sz
      simpa [he,hs] using can
    have nw : ws.Nodup := nd.filter _
    exact root ws (List.mem_sublists.mpr (List.filter_sublist ..)) nw (covered_bits _ (can_covers cc)) cc

theorem onlyRoots : (raw ++ [seed]).sublists.all (fun ws =>
    unionBits ws &&& mask != mask || ws == raw || ws == raw ++ [seed]) = true := by
  decide +kernel



def p258N : Nat → Nat
  | 0 => 0x203007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200
  | 1 => 0x10a8342219046c351acda693a9cce87639168ac582b96cb2542914caae774391cae67192890492591c482211885b0d96a359aad76934d9ed0688c05c2f188b41a090582818080301d7cbd5fb0580bc5c2dd72bb5d2cd64b45b2d55cad57ac560aa54ab156803f1fd027d3319cd0653c9ecf07a3e1dcc26031190c65d2e178be70379c4dc4e27944a04c26bfa02ff803f54aa85329d489b4f2713e9d4d3d1eef57b3cd1c9047a35f2fc7d3edf0a15128d40964aa5d329848a492893773c9daf077bc5d2ec753ad148945a310e886fb89c0e16f108884521918821e1007c3a381d0ec723c1b85c32180d05996ce663359429150ac58280201406dd6db71b43f1f1007a1c0d8cc6a341b0c8241109854280e0784192c563b1990c46130c4c27128000202
  | 2 => 0x172b85dae96eb459ad96ab24ba5932984aa71369e4fa75349248a51267b3d1e4f8773c188c26431980bc5d2f97076391c0e878371a8d066361904c24150a04430170c8682c0f070417ebe60b0178bd7fbfa03007ebe9f2fc7dbe14ca55429d48a250a8d40af572c560ad552b156a977bc1dcf278bb5eaf47bbd9e6ea74bb1d68b45231128e4823d1a87442110a864120cd66c369a4d4e57439dcce372124944b23920462410888fe80409f4fc6734194cce06fb89c2de6db75b8da219148444231047c3f200f43e1e10074381b3a1d4ec723995cb4582d964ac532a154a4d56cb59b0d76a341a6d268b3c5e30188b45c0a0682c1809038200c70389b8de4f289409c4d263198ec96431598cb6733594c26230c5629150b05026138940202000100a03
  | 3 => 0x10a824321106803ea04fe7e2511c96492411482442310c843f1e9007c7a3d9dcf8793c1d4e4763a1cce06e389bc723b1b8e878381a0d46436198c05a31178b85628150b052261289d80bc60afd7cbd803f602ff7f3edf0fc7d3e54ea4542994aa350289426c349b4d66a329a0ce66733a1c6e772b91c2de71381bedc6d375b6241088c441d1007c3c1b0e2e972bb5c2dd60af58ab95af1783c9deee76a612e994b255188b452256ab45b2cd64ab562a952f679bddeaf475bb1d4e94ea71349e4fa6d26924a2451e8d48239108731988c86130164b05a2d95cac50279449cd76b365b0d56a3218ec96331428130a848220c05834140901004005e2f974b8542a94ca44d26345a6d26833d9aca6733196c36230830160c8682e0f0803810070300c0a04
  | 4 => 0x202ff803f5fcfc7d3edf0f971381c2de6fb9dcae87338dc8dd6db71b4f0793bde2ed773ddeaf679bd1d8ea75ba5acd86ab65aed463b258cc862b3998cd6532da4d069b459ec46130d82bf602f17abe432110a8241a04fe803e9f8da6b361a4d46833994cca85329d48a55128d40a12311086452090896492511c90401f0fc7a200f8743c2312084441c0daed72ba5bae16cb45aac9667c3d1ecee783c990c46330184be5e2e17562af582b55cac55aa554763a1d4e473389c0dc6f2d960ae5a2c958a24f28138aa532a1489a4c4ca5d30954b27d389e4ea6936944924d223c1c8e876371c0d86835190cc2a130a044241a0c0642c170803c1c8b46225149047a351c88438b0542b140a4622f180b45c2713094160a068301201010000a030201c1006
  | 5 => 0x172b75d2ed70af56ac162ae31180c66430960ac5a2c96cae4f27140a2f2783b5e2ef7725d2a984ca59168946229b0d66a365aed564b1d8ac86304c22140a84816090683014010000978bd603057ebe4120d0a86421f4fc80409fcd26a361b4d665331a0ceb4592d56cb354aad58aa3b9e8f07b3e1e4e4733a9d8e86e379c0e25e2e17cba522a154a64c26bf603007fbf948a853a994a41221148c4321379c4e17037c3a200f879f0fc7dbe9f2a051a8942472412896491e8fc803e71b9dc8e873395b4dd6e36c42221208c361c79bddecf57a2693c9c4ea7d368d4823d1c371d0e4763c1c0a0542b160a594ce66b3196160c86034170181408ec75ba9d29249a512288438c868351b0cc5a2e180c45e251309da4cf69b45a0c461b081e10070181007
  | 6 => 0x10a864120d0880409f4fc7f3a9d8e4733a1ecf87a3b9e0f270389b8de44229188242219289647241247e401e8f8743b1e0e46e38150ac5828148c0622d170bc6a361a0c866261389580c15e2f57cbf5d2ed72b75c2c162af56ab96ab65a2c966ab562a5546c369a4d46b34194cc672c968b6582b15cc66431180c2502893c9c542a948a65f2f170ba4d2640202fd7f3fdf6fc7c3e5f4f1793c1daee77bd9eef37a3d5d6ec74ba94ea8522954ca35028544984ca5d2a964622d128a4ea793e9c4d26d1e9046a39269449245108770b89bcdf70399cee871b91cadc6eb69b6d76c365acd46ab2192c762b199ace6532d98d16934d9ed061b1184200e8783e2410888461b0e0301a0b04828281509844240200800321a0c0582e05018101006038401e0e
  | 7 => 0x202fe7ec01fea852a914ea67bbd1e6f67aa79369c4d2753e90472351e4522108824621b89bede70b80401e0e87c763a1c0e46e3c158a852281633996ca66b3032170c05834050200d7abe5e30182bf5bae172ba5dab55caf582c564b35a2d56ca9552ad58fc7cbe1f6fa50a8146a276bc9dcf078bbd2a964ba6132894522d18ec74badd4914924d28874420d0a8243210d46c349b4d6562d160b25b2b9ccea723b1d0a4542a94cfc803ea04fe66329a0ce6030988c6642713ca0513c1ecf27a3b9f0de70371c4b85d2f17c984d241288e4b24b91d0e771b99ca221208446d46cb61acd76a8241a0b060285c30168c45ecf69b49a2d0030200e3f1e9007cdd6d371b61b0e31592c7643182212098502a00008086a331a0c86c261289d88c3610381e10
  | 8 => 0x172bb5c2dd74b45b2cd64b531190c260319e8f87b3c9e0ee5e2f974b89e4e27d369a4ea5d32964aa61249448a4c74391e0ec70370c86034170b04c2a120885068361a8cc640f080397ec15f2f578c0422190a83411acda6c351a4fe81401f8fa6734198caaf58ab95ab0562a952ab2b960b65a2b164e8763a9cce4532a950a44f28938a071381bcdc4d263fe02fe7ec01f4fc7cbe1f6e573ba1c8e373381c4df6f385b6dd6d3714ca852a914ea250a814649259289047118904421219108c45211043e200f0747c401f8f4381b7abdde8f37b3bde4f0773b5e2ea763a5d6d56c359b2d46bb41a4d367b4598ce65b299ac664b1d8ac8613118690472351e8b45225188744028160d048305e31180b85a0704018542c158a450050200c02000109c4c25
  | 9 => 0x202fd7f3fe00a8522954ca771379bee07091082452110c8c200e8783e9c4f269369f4ebdde6f47abd9208d4723c723a1b8ec703c0c0642c170d33994cb663345428158a45805018117abc5f2fd82c041a090a84431a8d26c359b4fc7d401fd02663299cd0fc7c3e5f4fb5028544a37239dc6e872b9890472512496221089046dd6d36db83d1f8f8801b0e2dd72b85dae95aaf572c560562c168ae5b2c980c4613218c9c4f2894164b459ad96aa9552b15673391d4e87629150a6553c1e8ee7b3c9f0b85e2e97cde6e381c4984d4aa5d2c994c3b5e0f2773bde28945a2918d46b361b2d56b824160d0503022130905428c563b258cc800004049248a5126ec74ba9d6874433da4d3683445c2d180bc62060401c68321a8cc6c0f0704188c2618944c27
  | 10 => 0x172ba5bae176af582b55cb14ba612a964cbc1e2f276bb9de8b46225145a2c164ac572d988c660309909e5027145b2d66bb61a8d50682c18090504c2811090558ec864b158c010100178c05eaf97ec17ec0202fe7fa914ea852a99f0fb7e3e5f4a051a8544b45aac966b655aa554ac4d2713a9e4da7de6f67bbd1ea8d47a411c9249a4528eb763a5d48843a090a8342218fa803f1fd02412291084432311c94482492c7a3f1f100d26c351acda653319cd0de70b89bee00e8803c1f71ba1cce77239442241108db4dc6eb6c361c391d4e6743b1dcf67a3c1e4f86e381bce2371d8e474381e0a0562a148b05a30170bc62321a8d06636128984e542914caa5e2e174be4c2685830190b86994cd6732d980302811a6d16933da0080301c1e0e0830d88c2
  | 11 => 0x10a8441a090c6c359a8d26d25124904725ba1cae77238dcc241188842582d15cac592d9d4e873391d8a85329155acd96ab61a8d7058341409060c05e2e168c5a6d06933da208038197cbf5eaf180c17f3fe02fd802954ca85229df2fa7e3e1f6a15128146803f9f8fa8133998ca6821114864420919bee071379c21e0f8803a3f1f0f480db6eb69b81c0dae172b75d2ed66b4592d56c9b4e279349d4fa592e954c265229249a515caf56ac162aa54aad58f47abdde6f6472411a8f773c1def276bc5148b44a31d2ea763ad0e8830988c063321e4f47b3c1dcf85d2f170be381c8ec74371e05c30190b0682413088502a331a0d464360703c204f27140a270379b8e24c268a4562a140b196cc673299a040280d8ec664b159001000084c2513b0988c3
  | _ => 0
def p258At (a i : Nat) : Nat := (p258N a >>> (i * 9)) &&& 511

def inv258N : Nat → Nat
  | 0 => 0x203007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200
  | 1 => 0x10a8342219046c351acda693a9cce87639168ac582b96cb2542914caae774391cae67192890492591c482211885b0d96a359aad76934d9ed0688c05c2f188b41a090582818080301d7cbd5fb0580bc5c2dd72bb5d2cd64b45b2d55cad57ac560aa54ab156803f1fd027d3319cd0653c9ecf07a3e1dcc26031190c65d2e178be70379c4dc4e27944a04c26bfa02ff803f54aa85329d489b4f2713e9d4d3d1eef57b3cd1c9047a35f2fc7d3edf0a15128d40964aa5d329848a492893773c9daf077bc5d2ec753ad148945a310e886fb89c0e16f108884521918821e1007c3a381d0ec723c1b85c32180d05996ce663359429150ac58280201406dd6db71b43f1f1007a1c0d8cc6a341b0c8241109854280e0784192c563b1990c46130c4c27128000202
  | 2 => 0x172b85dae96eb459ad96ab24ba5932984aa71369e4fa75349248a51267b3d1e4f8773c188c26431980bc5d2f97076391c0e878371a8d066361904c24150a04430170c8682c0f070417ebe60b0178bd7fbfa03007ebe9f2fc7dbe14ca55429d48a250a8d40af572c560ad552b156a977bc1dcf278bb5eaf47bbd9e6ea74bb1d68b45231128e4823d1a87442110a864120cd66c369a4d4e57439dcce372124944b23920462410888fe80409f4fc6734194cce06fb89c2de6db75b8da219148444231047c3f200f43e1e10074381b3a1d4ec723995cb4582d964ac532a154a4d56cb59b0d76a341a6d268b3c5e30188b45c0a0682c1809038200c70389b8de4f289409c4d263198ec96431598cb6733594c26230c5629150b05026138940202000100a03
  | 3 => 0x172bb5c2dd74b45b2cd64b531190c260319e8f87b3c9e0ee5e2f974b89e4e27d369a4ea5d32964aa61249448a4c74391e0ec70370c86034170b04c2a120885068361a8cc640f080397ec15f2f578c0422190a83411acda6c351a4fe81401f8fa6734198caaf58ab95ab0562a952ab2b960b65a2b164e8763a9cce4532a950a44f28938a071381bcdc4d263fe02fe7ec01f4fc7cbe1f6e573ba1c8e373381c4df6f385b6dd6d3714ca852a914ea250a814649259289047118904421219108c45211043e200f0747c401f8f4381b7abdde8f37b3bde4f0773b5e2ea763a5d6d56c359b2d46bb41a4d367b4598ce65b299ac664b1d8ac8613118690472351e8b45225188744028160d048305e31180b85a0704018542c158a450050200c02000109c4c25
  | 4 => 0x202ff803f5fcfc7d3edf0f971381c2de6fb9dcae87338dc8dd6db71b4f0793bde2ed773ddeaf679bd1d8ea75ba5acd86ab65aed463b258cc862b3998cd6532da4d069b459ec46130d82bf602f17abe432110a8241a04fe803e9f8da6b361a4d46833994cca85329d48a55128d40a12311086452090896492511c90401f0fc7a200f8743c2312084441c0daed72ba5bae16cb45aac9667c3d1ecee783c990c46330184be5e2e17562af582b55cac55aa554763a1d4e473389c0dc6f2d960ae5a2c958a24f28138aa532a1489a4c4ca5d30954b27d389e4ea6936944924d223c1c8e876371c0d86835190cc2a130a044241a0c0642c170803c1c8b46225149047a351c88438b0542b140a4622f180b45c2713094160a068301201010000a030201c1006
  | 5 => 0x10a8441a090c6c359a8d26d25124904725ba1cae77238dcc241188842582d15cac592d9d4e873391d8a85329155acd96ab61a8d7058341409060c05e2e168c5a6d06933da208038197cbf5eaf180c17f3fe02fd802954ca85229df2fa7e3e1f6a15128146803f9f8fa8133998ca6821114864420919bee071379c21e0f8803a3f1f0f480db6eb69b81c0dae172b75d2ed66b4592d56c9b4e279349d4fa592e954c265229249a515caf56ac162aa54aad58f47abdde6f6472411a8f773c1def276bc5148b44a31d2ea763ad0e8830988c063321e4f47b3c1dcf85d2f170be381c8ec74371e05c30190b0682413088502a331a0d464360703c204f27140a270379b8e24c268a4562a140b196cc673299a040280d8ec664b159001000084c2513b0988c3
  | 6 => 0x10a864120d0880409f4fc7f3a9d8e4733a1ecf87a3b9e0f270389b8de44229188242219289647241247e401e8f8743b1e0e46e38150ac5828148c0622d170bc6a361a0c866261389580c15e2f57cbf5d2ed72b75c2c162af56ab96ab65a2c966ab562a5546c369a4d46b34194cc672c968b6582b15cc66431180c2502893c9c542a948a65f2f170ba4d2640202fd7f3fdf6fc7c3e5f4f1793c1daee77bd9eef37a3d5d6ec74ba94ea8522954ca35028544984ca5d2a964622d128a4ea793e9c4d26d1e9046a39269449245108770b89bcdf70399cee871b91cadc6eb69b6d76c365acd46ab2192c762b199ace6532d98d16934d9ed061b1184200e8783e2410888461b0e0301a0b04828281509844240200800321a0c0582e05018101006038401e0e
  | 7 => 0x202fe7ec01fea852a914ea67bbd1e6f67aa79369c4d2753e90472351e4522108824621b89bede70b80401e0e87c763a1c0e46e3c158a852281633996ca66b3032170c05834050200d7abe5e30182bf5bae172ba5dab55caf582c564b35a2d56ca9552ad58fc7cbe1f6fa50a8146a276bc9dcf078bbd2a964ba6132894522d18ec74badd4914924d28874420d0a8243210d46c349b4d6562d160b25b2b9ccea723b1d0a4542a94cfc803ea04fe66329a0ce6030988c6642713ca0513c1ecf27a3b9f0de70371c4b85d2f17c984d241288e4b24b91d0e771b99ca221208446d46cb61acd76a8241a0b060285c30168c45ecf69b49a2d0030200e3f1e9007cdd6d371b61b0e31592c7643182212098502a00008086a331a0c86c261289d88c3610381e10
  | 8 => 0x10a824321106803ea04fe7e2511c96492411482442310c843f1e9007c7a3d9dcf8793c1d4e4763a1cce06e389bc723b1b8e878381a0d46436198c05a31178b85628150b052261289d80bc60afd7cbd803f602ff7f3edf0fc7d3e54ea4542994aa350289426c349b4d66a329a0ce66733a1c6e772b91c2de71381bedc6d375b6241088c441d1007c3c1b0e2e972bb5c2dd60af58ab95af1783c9deee76a612e994b255188b452256ab45b2cd64ab562a952f679bddeaf475bb1d4e94ea71349e4fa6d26924a2451e8d48239108731988c86130164b05a2d95cac50279449cd76b365b0d56a3218ec96331428130a848220c05834140901004005e2f974b8542a94ca44d26345a6d26833d9aca6733196c36230830160c8682e0f0803810070300c0a04
  | 9 => 0x202fd7f3fe00a8522954ca771379bee07091082452110c8c200e8783e9c4f269369f4ebdde6f47abd9208d4723c723a1b8ec703c0c0642c170d33994cb663345428158a45805018117abc5f2fd82c041a090a84431a8d26c359b4fc7d401fd02663299cd0fc7c3e5f4fb5028544a37239dc6e872b9890472512496221089046dd6d36db83d1f8f8801b0e2dd72b85dae95aaf572c560562c168ae5b2c980c4613218c9c4f2894164b459ad96aa9552b15673391d4e87629150a6553c1e8ee7b3c9f0b85e2e97cde6e381c4984d4aa5d2c994c3b5e0f2773bde28945a2918d46b361b2d56b824160d0503022130905428c563b258cc800004049248a5126ec74ba9d6874433da4d3683445c2d180bc62060401c68321a8cc6c0f0704188c2618944c27
  | 10 => 0x172ba5bae176af582b55cb14ba612a964cbc1e2f276bb9de8b46225145a2c164ac572d988c660309909e5027145b2d66bb61a8d50682c18090504c2811090558ec864b158c010100178c05eaf97ec17ec0202fe7fa914ea852a99f0fb7e3e5f4a051a8544b45aac966b655aa554ac4d2713a9e4da7de6f67bbd1ea8d47a411c9249a4528eb763a5d48843a090a8342218fa803f1fd02412291084432311c94482492c7a3f1f100d26c351acda653319cd0de70b89bee00e8803c1f71ba1cce77239442241108db4dc6eb6c361c391d4e6743b1dcf67a3c1e4f86e381bce2371d8e474381e0a0562a148b05a30170bc62321a8d06636128984e542914caa5e2e174be4c2685830190b86994cd6732d980302811a6d16933da0080301c1e0e0830d88c2
  | 11 => 0x172b75d2ed70af56ac162ae31180c66430960ac5a2c96cae4f27140a2f2783b5e2ef7725d2a984ca59168946229b0d66a365aed564b1d8ac86304c22140a84816090683014010000978bd603057ebe4120d0a86421f4fc80409fcd26a361b4d665331a0ceb4592d56cb354aad58aa3b9e8f07b3e1e4e4733a9d8e86e379c0e25e2e17cba522a154a64c26bf603007fbf948a853a994a41221148c4321379c4e17037c3a200f879f0fc7dbe9f2a051a8942472412896491e8fc803e71b9dc8e873395b4dd6e36c42221208c361c79bddecf57a2693c9c4ea7d368d4823d1c371d0e4763c1c0a0542b160a594ce66b3196160c86034170181408ec75ba9d29249a512288438c868351b0cc5a2e180c45e251309da4cf69b45a0c461b081e10070181007
  | _ => 0
def inv258At (a i : Nat) : Nat := (inv258N a >>> (i * 9)) &&& 511

def autoV : Nat → Nat → Nat
  | 0,0 => 0
  | 0,1 => 1
  | 0,2 => 2
  | 0,3 => 3
  | 0,4 => 4
  | 0,5 => 5
  | 0,6 => 6
  | 0,7 => 7
  | 0,8 => 8
  | 1,0 => 0
  | 1,1 => 5
  | 1,2 => 8
  | 1,3 => 3
  | 1,4 => 4
  | 1,5 => 1
  | 1,6 => 7
  | 1,7 => 6
  | 1,8 => 2
  | 2,0 => 1
  | 2,1 => 0
  | 2,2 => 5
  | 2,3 => 8
  | 2,4 => 6
  | 2,5 => 2
  | 2,6 => 4
  | 2,7 => 7
  | 2,8 => 3
  | 3,0 => 5
  | 3,1 => 0
  | 3,2 => 1
  | 3,3 => 2
  | 3,4 => 7
  | 3,5 => 8
  | 3,6 => 4
  | 3,7 => 6
  | 3,8 => 3
  | 4,0 => 2
  | 4,1 => 1
  | 4,2 => 0
  | 4,3 => 5
  | 4,4 => 7
  | 4,5 => 3
  | 4,6 => 6
  | 4,7 => 4
  | 4,8 => 8
  | 5,0 => 8
  | 5,1 => 5
  | 5,2 => 0
  | 5,3 => 1
  | 5,4 => 6
  | 5,5 => 3
  | 5,6 => 7
  | 5,7 => 4
  | 5,8 => 2
  | 6,0 => 3
  | 6,1 => 2
  | 6,2 => 1
  | 6,3 => 0
  | 6,4 => 4
  | 6,5 => 8
  | 6,6 => 7
  | 6,7 => 6
  | 6,8 => 5
  | 7,0 => 3
  | 7,1 => 8
  | 7,2 => 5
  | 7,3 => 0
  | 7,4 => 4
  | 7,5 => 2
  | 7,6 => 6
  | 7,7 => 7
  | 7,8 => 1
  | 8,0 => 1
  | 8,1 => 2
  | 8,2 => 3
  | 8,3 => 8
  | 8,4 => 6
  | 8,5 => 0
  | 8,6 => 7
  | 8,7 => 4
  | 8,8 => 5
  | 9,0 => 5
  | 9,1 => 8
  | 9,2 => 3
  | 9,3 => 2
  | 9,4 => 7
  | 9,5 => 0
  | 9,6 => 6
  | 9,7 => 4
  | 9,8 => 1
  | 10,0 => 8
  | 10,1 => 3
  | 10,2 => 2
  | 10,3 => 1
  | 10,4 => 6
  | 10,5 => 5
  | 10,6 => 4
  | 10,7 => 7
  | 10,8 => 0
  | 11,0 => 2
  | 11,1 => 3
  | 11,2 => 8
  | 11,3 => 5
  | 11,4 => 7
  | 11,5 => 1
  | 11,6 => 4
  | 11,7 => 6
  | 11,8 => 0
  | _,_ => 0


def buildBits (f : Nat → Bool) : Nat → Word
  | 0 => 0
  | n + 1 =>
    let rest := buildBits f n
    if f n then rest ||| (1#516 <<< n) else rest

theorem buildBits_getLsbD (f : Nat → Bool) :
    ∀ n i, i < 516 → (buildBits f n).getLsbD i = (decide (i < n) && f i) := by
  intro n
  induction n with
  | zero => intro i _; simp [buildBits]
  | succ n ih =>
    intro i hi
    simp only [buildBits]
    by_cases hfn : f n = true
    · simp only [hfn, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, ih i hi]
      by_cases hlt : i < n
      · have hlt1 : i < n + 1 := by omega
        simp [hlt, hlt1]
      · by_cases heq : i = n
        · subst heq; simp [hi, hfn]
        · have hsub : i - n ≠ 0 := by omega
          have h1 : (1#516).getLsbD (i - n) = false := by
            rw [BitVec.getLsbD_one]; simp [hsub]
          have hlt1 : ¬(i < n + 1) := by omega
          simp [hlt, hlt1, h1]
    · have hfn' : f n = false := Bool.eq_false_iff.mpr hfn
      simp only [hfn', Bool.false_eq_true, ite_false, ih i hi]
      by_cases heq : i = n
      · subst heq; simp [hfn']
      · have hiff : (i < n) ↔ (i < n + 1) := by omega
        simp [hiff]

def rotW (a : Nat) (w : Word) : Word :=
  buildBits (fun i =>
    if i < 258 then w.getLsbD (p258At a i)
    else w.getLsbD (p258At a (i - 258) + 258)) 516

def rotWInv (a : Nat) (w : Word) : Word :=
  buildBits (fun i =>
    if i < 258 then w.getLsbD (inv258At a i)
    else w.getLsbD (inv258At a (i - 258) + 258)) 516

theorem p258_ok :
    (List.range 12).all (fun a =>
      (List.range 258).all (fun i =>
        let j := p258At a i
        let k := inv258At a i
        decide (j < 258) && decide (k < 258) &&
        (inv258At a j == i) && (p258At a k == i))) = true := by
  decide +kernel

theorem rotW_bit_lo (a : Nat) (w : Word) (i : Nat) (hi : i < 258) :
    (rotW a w).getLsbD i = w.getLsbD (p258At a i) := by
  have hi516 : i < 516 := by omega
  rw [rotW, buildBits_getLsbD _ 516 i hi516]; simp [hi516, hi]

theorem rotW_bit_hi (a : Nat) (w : Word) (i : Nat) (hi : i < 258) :
    (rotW a w).getLsbD (i + 258) = w.getLsbD (p258At a i + 258) := by
  have hi516 : i + 258 < 516 := by omega
  have hge : ¬ (i + 258 < 258) := by omega
  rw [rotW, buildBits_getLsbD _ 516 (i + 258) hi516]; simp [hi516, hge]

theorem p258At_lt {a i : Nat} (ha : a < 12) (hi : i < 258) : p258At a i < 258 := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp p258_ok a (List.mem_range.mpr ha)) i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  exact hh.1.1.1

theorem rotW_inv_left {a : Nat} (ha : a < 12) (w : Word) : rotWInv a (rotW a w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < 258
  · have hh := List.all_eq_true.mp (List.all_eq_true.mp p258_ok a (List.mem_range.mpr ha)) i (List.mem_range.mpr hlt)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
    rw [rotWInv, buildBits_getLsbD _ 516 i hi]
    simp only [hi, hlt, decide_true, Bool.true_and, ite_true]
    rw [rotW_bit_lo a w _ hh.1.1.2, hh.2]
  · have hlt2 : i - 258 < 258 := by omega
    have hh := List.all_eq_true.mp (List.all_eq_true.mp p258_ok a (List.mem_range.mpr ha)) (i - 258) (List.mem_range.mpr hlt2)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
    rw [rotWInv, buildBits_getLsbD _ 516 i hi]
    simp only [hi, hlt, decide_true, Bool.true_and, ite_false]
    rw [rotW_bit_hi a w _ hh.1.1.2, hh.2]
    have : i - 258 + 258 = i := by omega
    rw [this]

theorem rotW_inj {a : Nat} (ha : a < 12) : Function.Injective (rotW a) :=
  fun _ _ h => by have := congrArg (rotWInv a) h; rwa [rotW_inv_left ha, rotW_inv_left ha] at this

theorem rotW_mix (a : Nat) (op : Bool) (x y : Word) :
    rotW a (mix op x y) = mix op (rotW a x) (rotW a y) := by
  cases op <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [rotW, mix, Bool.false_eq_true, ite_true, ite_false, BitVec.getLsbD_and, BitVec.getLsbD_or, buildBits_getLsbD, hi, decide_true, Bool.true_and] <;>
    split_ifs <;> simp

theorem rotW_covers {a : Nat} (ha : a < 12) {S : Finset Word} (h : Covers S) :
    Covers (S.image (rotW a)) := by
  intro ⟨i, hi⟩
  obtain ⟨w, hw, hd⟩ := h ⟨p258At a i, p258At_lt ha hi⟩
  refine ⟨rotW a w, Finset.mem_image_of_mem _ hw, ?_⟩
  rw [rotW_bit_lo a w i hi, rotW_bit_hi a w i hi]
  exact hd

theorem can_auto {a : Nat} (ha : a < 12) {k : Nat} {S : Finset Word} (h : Can k S) :
    Can k (S.image (rotW a)) := by
  induction k generalizing S with
  | zero =>
    exact ⟨rotW_covers ha h.1, (Finset.card_image_le).trans h.2⟩
  | succ k ih =>
    rcases h with h | ⟨hcov, x, hx, y, hy, op, t, hxy, hwx, hwy, hfr, hts, hst, hc⟩
    · exact Or.inl (ih h)
    · refine Or.inr ⟨rotW_covers ha hcov, rotW a x, Finset.mem_image_of_mem _ hx,
        rotW a y, Finset.mem_image_of_mem _ hy, op, t.image (rotW a),
        fun e => hxy (rotW_inj ha e),
        fun e => hwx (rotW_inj ha ((rotW_mix a op x y).trans e)),
        fun e => hwy (rotW_inj ha ((rotW_mix a op x y).trans e)),
        fun hm => by
          obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
          exact hfr (rotW_inj ha (he.trans (rotW_mix a op x y).symm) ▸ hu),
        Finset.image_subset_image hts,
        by
          intro v hv
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
          have := hst hu
          simp only [Finset.mem_insert] at this ⊢
          rcases this with rfl | rfl | ht'
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ ht')),
        ?_⟩
      have himg : insert (mix op (rotW a x) (rotW a y)) (t.image (rotW a)) =
          (insert (mix op x y) t).image (rotW a) := by
        rw [Finset.image_insert, rotW_mix]
      rw [himg]
      exact ih hc

theorem can_mono {a b : Nat} {s : Finset Word} (hab : a ≤ b) (h : Can a s) : Can b s := by
  induction hab with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def allN : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

theorem allN_eq : allN = (BitVec.allOnes 258).toNat := by decide +kernel

theorem allN_testBit (m : Nat) : allN.testBit m = decide (m < 258) := by
  rw [allN_eq]
  change (BitVec.allOnes 258).getLsbD m = decide (m < 258)
  exact BitVec.getLsbD_allOnes

def deltaN (w : Word) : Nat := (w.toNat &&& allN) ^^^ (w.toNat >>> 258)

theorem deltaN_testBit_lt (w : Word) {m : Nat} (hm : m < 258) :
    (deltaN w).testBit m = (w.getLsbD m != w.getLsbD (m + 258)) := by
  simp only [deltaN, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, allN_testBit,
    hm, decide_true, Bool.and_true, Nat.add_comm 258 m]
  change Bool.xor (w.getLsbD m) (w.getLsbD (m + 258)) = (w.getLsbD m != w.getLsbD (m + 258))
  cases w.getLsbD m <;> cases w.getLsbD (m + 258) <;> rfl

theorem deltaN_testBit_ge (w : Word) {m : Nat} (hm : 258 ≤ m) :
    (deltaN w).testBit m = false := by
  simp only [deltaN, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, allN_testBit]
  have h1 : ¬(m < 258) := by omega
  have hlt : w.toNat < 2 ^ (258 + m) :=
    lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : w.toNat.testBit (258 + m) = false := Nat.testBit_lt_two_pow hlt
  simp [h1, h2]

def compAuto (a b : Nat) : Nat := (0x5127390a864b4036281b975a680a4b271539791b5a36042832450189ba6723541098ab76046382b179a5157293a068b486a0b472519397b1a5634082ab8967452301ba9876543210 >>> ((a * 12 + b) * 4)) &&& 15
def invAuto (a : Nat) : Nat := (0x5a9376b48210 >>> (a * 4)) &&& 15

theorem p258_zero_ok : (List.range 258).all (fun i => p258At 0 i == i) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem p258_comp_ok :
    (List.range 12).all (fun a =>
      (List.range 12).all (fun b =>
        let c := compAuto a b
        decide (c < 12) &&
        (List.range 258).all (fun i =>
          p258At b (p258At a i) == p258At c i))) = true := by
  decide +kernel

theorem compAuto_assoc_ok :
    (List.range 12).all (fun a =>
      (List.range 12).all (fun b =>
        (List.range 12).all (fun c =>
          compAuto (compAuto a b) c == compAuto a (compAuto b c)))) = true := by
  decide +kernel

theorem invAuto_ok :
    (List.range 12).all (fun a =>
      decide (invAuto a < 12) && (compAuto (invAuto a) a == 0)) = true := by
  decide +kernel

theorem compAuto_lt {a b : Nat} (ha : a < 12) (hb : b < 12) : compAuto a b < 12 := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp p258_comp_ok a (List.mem_range.mpr ha)) b (List.mem_range.mpr hb)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  exact hh.1

theorem compAuto_assoc {a b c : Nat} (ha : a < 12) (hb : b < 12) (hc : c < 12) :
    compAuto (compAuto a b) c = compAuto a (compAuto b c) := by
  have h1 := List.all_eq_true.mp compAuto_assoc_ok a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  exact beq_iff_eq.mp h3

theorem invAuto_lt {a : Nat} (ha : a < 12) : invAuto a < 12 := by
  have hh := List.all_eq_true.mp invAuto_ok a (List.mem_range.mpr ha)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  exact hh.1

theorem compAuto_inv_left {a : Nat} (ha : a < 12) : compAuto (invAuto a) a = 0 := by
  have hh := List.all_eq_true.mp invAuto_ok a (List.mem_range.mpr ha)
  simp only [Bool.and_eq_true, beq_iff_eq] at hh
  exact hh.2

theorem p258At_comp {a b i : Nat} (ha : a < 12) (hb : b < 12) (hi : i < 258) :
    p258At b (p258At a i) = p258At (compAuto a b) i := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp p258_comp_ok a (List.mem_range.mpr ha)) b (List.mem_range.mpr hb)
  simp only [Bool.and_eq_true] at hh
  exact beq_iff_eq.mp (List.all_eq_true.mp hh.2 i (List.mem_range.mpr hi))

theorem rotW_comp {a b : Nat} (ha : a < 12) (hb : b < 12) (w : Word) :
    rotW a (rotW b w) = rotW (compAuto a b) w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < 258
  · rw [rotW_bit_lo a _ i hlt, rotW_bit_lo b w _ (p258At_lt ha hlt),
      rotW_bit_lo (compAuto a b) w i hlt, p258At_comp ha hb hlt]
  · have h2 : i - 258 < 258 := by omega
    have heq : i - 258 + 258 = i := by omega
    rw [← heq, rotW_bit_hi a _ (i - 258) h2, rotW_bit_hi b w _ (p258At_lt ha h2),
      rotW_bit_hi (compAuto a b) w (i - 258) h2, p258At_comp ha hb h2]

theorem rotW_zero (w : Word) : rotW 0 w = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < 258
  · have h0 := beq_iff_eq.mp (List.all_eq_true.mp p258_zero_ok i (List.mem_range.mpr hlt))
    rw [rotW_bit_lo 0 w i hlt, h0]
  · have h2 : i - 258 < 258 := by omega
    have heq : i - 258 + 258 = i := by omega
    have h0 := beq_iff_eq.mp (List.all_eq_true.mp p258_zero_ok (i - 258) (List.mem_range.mpr h2))
    rw [← heq, rotW_bit_hi 0 w (i - 258) h2, h0]

def rw0 : Word := 0x843f80211fc01f807e0f80441f80f810821108fc3f0f020882108488a1f8f83c0007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07
def rw1 : Word := 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
def rw2 : Word := 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
def rw3 : Word := 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
def rw4 : Word := 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
def rw5 : Word := 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
def rw6 : Word := 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
def rw7 : Word := 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
def rw8 : Word := 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000

def rawRot : Nat → List Word
  | 0 => [rw0,rw1,rw2,rw3,rw4,rw5,rw6,rw7,rw8]
  | 1 => [rw0,rw5,rw8,rw3,rw4,rw1,rw7,rw6,rw2]
  | 2 => [rw1,rw0,rw5,rw8,rw6,rw2,rw4,rw7,rw3]
  | 3 => [rw5,rw0,rw1,rw2,rw7,rw8,rw4,rw6,rw3]
  | 4 => [rw2,rw1,rw0,rw5,rw7,rw3,rw6,rw4,rw8]
  | 5 => [rw8,rw5,rw0,rw1,rw6,rw3,rw7,rw4,rw2]
  | 6 => [rw3,rw2,rw1,rw0,rw4,rw8,rw7,rw6,rw5]
  | 7 => [rw3,rw8,rw5,rw0,rw4,rw2,rw6,rw7,rw1]
  | 8 => [rw1,rw2,rw3,rw8,rw6,rw0,rw7,rw4,rw5]
  | 9 => [rw5,rw8,rw3,rw2,rw7,rw0,rw6,rw4,rw1]
  | 10 => [rw8,rw3,rw2,rw1,rw6,rw5,rw4,rw7,rw0]
  | 11 => [rw2,rw3,rw8,rw5,rw7,rw1,rw4,rw6,rw0]
  | _ => []

def starting (z : Bool) : List Word := if z then raw ++ [seed] else raw

def startRot (z : Bool) (a : Nat) : List Word :=
  match z, a with
  | false, 0 => [rw0,rw1,rw2,rw3,rw4,rw5,rw6,rw7,rw8]
  | false, 1 => [rw0,rw5,rw8,rw3,rw4,rw1,rw7,rw6,rw2]
  | false, 2 => [rw1,rw0,rw5,rw8,rw6,rw2,rw4,rw7,rw3]
  | false, 3 => [rw5,rw0,rw1,rw2,rw7,rw8,rw4,rw6,rw3]
  | false, 4 => [rw2,rw1,rw0,rw5,rw7,rw3,rw6,rw4,rw8]
  | false, 5 => [rw8,rw5,rw0,rw1,rw6,rw3,rw7,rw4,rw2]
  | false, 6 => [rw3,rw2,rw1,rw0,rw4,rw8,rw7,rw6,rw5]
  | false, 7 => [rw3,rw8,rw5,rw0,rw4,rw2,rw6,rw7,rw1]
  | false, 8 => [rw1,rw2,rw3,rw8,rw6,rw0,rw7,rw4,rw5]
  | false, 9 => [rw5,rw8,rw3,rw2,rw7,rw0,rw6,rw4,rw1]
  | false, 10 => [rw8,rw3,rw2,rw1,rw6,rw5,rw4,rw7,rw0]
  | false, 11 => [rw2,rw3,rw8,rw5,rw7,rw1,rw4,rw6,rw0]
  | true, 0 => [rw0,rw1,rw2,rw3,rw4,rw5,rw6,rw7,rw8, rw0 ||| rw2]
  | true, 1 => [rw0,rw5,rw8,rw3,rw4,rw1,rw7,rw6,rw2, rw0 ||| rw8]
  | true, 2 => [rw1,rw0,rw5,rw8,rw6,rw2,rw4,rw7,rw3, rw1 ||| rw5]
  | true, 3 => [rw5,rw0,rw1,rw2,rw7,rw8,rw4,rw6,rw3, rw5 ||| rw1]
  | true, 4 => [rw2,rw1,rw0,rw5,rw7,rw3,rw6,rw4,rw8, rw2 ||| rw0]
  | true, 5 => [rw8,rw5,rw0,rw1,rw6,rw3,rw7,rw4,rw2, rw8 ||| rw0]
  | true, 6 => [rw3,rw2,rw1,rw0,rw4,rw8,rw7,rw6,rw5, rw3 ||| rw1]
  | true, 7 => [rw3,rw8,rw5,rw0,rw4,rw2,rw6,rw7,rw1, rw3 ||| rw5]
  | true, 8 => [rw1,rw2,rw3,rw8,rw6,rw0,rw7,rw4,rw5, rw1 ||| rw3]
  | true, 9 => [rw5,rw8,rw3,rw2,rw7,rw0,rw6,rw4,rw1, rw5 ||| rw3]
  | true, 10 => [rw8,rw3,rw2,rw1,rw6,rw5,rw4,rw7,rw0, rw8 ||| rw2]
  | true, 11 => [rw2,rw3,rw8,rw5,rw7,rw1,rw4,rw6,rw0, rw2 ||| rw8]
  | _, _ => []
set_option maxHeartbeats 0 in
theorem rotW_raw_ok :
    (List.range 12).all (fun a =>
      (List.range 9).all (fun u => rotW a (raw.getD u 0) == raw.getD (autoV a u) 0)) = true := by
  decide +kernel

theorem rotW_raw_get {a u : Nat} (ha : a < 12) (hu : u < 9) :
    rotW a (raw.getD u 0) = raw.getD (autoV a u) 0 :=
  beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp rotW_raw_ok a (List.mem_range.mpr ha)) u (List.mem_range.mpr hu))

theorem rawRot_spec {a : Nat} (ha : a < 12) :
    rawRot a = [raw.getD (autoV a 0) 0, raw.getD (autoV a 1) 0, raw.getD (autoV a 2) 0,
      raw.getD (autoV a 3) 0, raw.getD (autoV a 4) 0, raw.getD (autoV a 5) 0,
      raw.getD (autoV a 6) 0, raw.getD (autoV a 7) 0, raw.getD (autoV a 8) 0] := by
  interval_cases a <;> rfl

theorem startRot_spec (z : Bool) {a : Nat} (ha : a < 12) :
    startRot z a = if z then rawRot a ++ [mix true (raw.getD (autoV a 0) 0) (raw.getD (autoV a 2) 0)] else rawRot a := by
  cases z <;> interval_cases a <;> rfl

theorem map_rotW_raw {a : Nat} (ha : a < 12) : raw.map (rotW a) = rawRot a := by
  have hr : raw = [raw.getD 0 0, raw.getD 1 0, raw.getD 2 0, raw.getD 3 0,
      raw.getD 4 0, raw.getD 5 0, raw.getD 6 0, raw.getD 7 0, raw.getD 8 0] := rfl
  conv_lhs => rw [hr]
  rw [rawRot_spec ha]
  simp only [List.map_cons, List.map_nil,
    rotW_raw_get ha (by decide : 0 < 9), rotW_raw_get ha (by decide : 1 < 9),
    rotW_raw_get ha (by decide : 2 < 9), rotW_raw_get ha (by decide : 3 < 9),
    rotW_raw_get ha (by decide : 4 < 9), rotW_raw_get ha (by decide : 5 < 9),
    rotW_raw_get ha (by decide : 6 < 9), rotW_raw_get ha (by decide : 7 < 9),
    rotW_raw_get ha (by decide : 8 < 9)]

theorem map_rotW_starting (z : Bool) {a : Nat} (ha : a < 12) :
    (starting z).map (rotW a) = startRot z a := by
  rw [startRot_spec z ha]
  cases z
  · exact map_rotW_raw ha
  · simp only [starting, ite_true, List.map_append, List.map_cons, List.map_nil, map_rotW_raw ha]
    have hsd : rotW a seed = mix true (raw.getD (autoV a 0) 0) (raw.getD (autoV a 2) 0) := by
      change rotW a (mix true (raw.getD 0 0) (raw.getD 2 0)) = _
      rw [rotW_mix, rotW_raw_get ha (by decide), rotW_raw_get ha (by decide)]
    rw [hsd]

def keepGo (t i j : Nat) (ka kb : Bool) : List Word → List Word
  | [] => []
  | w :: ws =>
    if (t == i && !ka) || (t == j && !kb) then keepGo (t + 1) i j ka kb ws
    else w :: keepGo (t + 1) i j ka kb ws

def childFrom (ws : List Word) (i j : Nat) (op ka kb : Bool) : List Word :=
  mix op (ws.getD i 0) (ws.getD j 0) :: keepGo 0 i j ka kb ws

def childFromW (ws : List Word) (i j : Nat) (ka kb : Bool) (w : Word) : List Word :=
  w :: keepGo 0 i j ka kb ws

theorem keepGo_sublist (t i j : Nat) (ka kb : Bool) (ws : List Word) :
    (keepGo t i j ka kb ws).Sublist ws := by
  induction ws generalizing t with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    simp only [keepGo]
    split_ifs
    · exact List.Sublist.cons w (ih (t + 1))
    · exact List.Sublist.cons_cons w (ih (t + 1))

theorem map_rotW_keepGo (t i j : Nat) (ka kb : Bool) (a : Nat) (ws : List Word) :
    (keepGo t i j ka kb ws).map (rotW a) = keepGo t i j ka kb (ws.map (rotW a)) := by
  induction ws generalizing t with
  | nil => rfl
  | cons w ws ih =>
    simp only [keepGo, List.map_cons]
    split_ifs
    · exact ih (t + 1)
    · simp only [List.map_cons, ih (t + 1)]

theorem map_rotW_childFrom (ws : List Word) (i j : Nat) (hi : i < ws.length) (hj : j < ws.length)
    (op ka kb : Bool) (a : Nat) :
    (childFrom ws i j op ka kb).map (rotW a) = childFrom (ws.map (rotW a)) i j op ka kb := by
  have hget (t : Nat) (ht : t < ws.length) : (ws.map (rotW a)).getD t 0 = rotW a (ws.getD t 0) := by
    rw [List.getD_eq_getElem _ _ (by simp [ht]), List.getElem_map, List.getD_eq_getElem _ _ ht]
  simp only [childFrom, List.map_cons, rotW_mix, hget i hi, hget j hj, map_rotW_keepGo]

theorem keepGo_mem (t i j : Nat) (ka kb : Bool) (ws : List Word) (v : Word) :
    v ∈ keepGo t i j ka kb ws ↔
      ∃ (u : Nat) (hu : u < ws.length), ws[u] = v ∧ !((t + u == i && !ka) || (t + u == j && !kb)) = true := by
  induction ws generalizing t with
  | nil => simp [keepGo]
  | cons w ws ih =>
    simp only [keepGo]
    split_ifs with hdrop
    · rw [ih (t + 1)]
      constructor
      · rintro ⟨u, hu, heq, hkeep⟩
        refine ⟨u + 1, by simp; omega, heq, ?_⟩
        have : t + (u + 1) = t + 1 + u := by omega
        rwa [this]
      · rintro ⟨u, hu, heq, hkeep⟩
        cases u with
        | zero => simp [hdrop] at hkeep
        | succ u =>
          refine ⟨u, by simp at hu; omega, heq, ?_⟩
          have : t + 1 + u = t + (u + 1) := by omega
          rwa [this]
    · simp only [List.mem_cons, ih (t + 1)]
      constructor
      · rintro (rfl | ⟨u, hu, heq, hkeep⟩)
        · refine ⟨0, by simp, rfl, ?_⟩
          have hf : ((t + 0 == i && !ka) || (t + 0 == j && !kb)) = false := by
            simpa using Bool.eq_false_iff.mpr hdrop
          rw [hf]; rfl
        · refine ⟨u + 1, by simp; omega, heq, ?_⟩
          have : t + (u + 1) = t + 1 + u := by omega
          rwa [this]
      · rintro ⟨u, hu, heq, hkeep⟩
        cases u with
        | zero => left; exact heq.symm
        | succ u =>
          right
          refine ⟨u, by simp at hu; omega, heq, ?_⟩
          have : t + 1 + u = t + (u + 1) := by omega
          rwa [this]

theorem keepGo_length_add (t i j : Nat) (ka kb : Bool) (ws : List Word) (hij : i < j) :
    (keepGo t i j ka kb ws).length +
      (if !ka && decide (t ≤ i) && decide (i < t + ws.length) then 1 else 0) +
      (if !kb && decide (t ≤ j) && decide (j < t + ws.length) then 1 else 0) = ws.length := by
  induction ws generalizing t with
  | nil =>
    have h1 : ¬(t ≤ i ∧ i < t + 0) := by omega
    have h2 : ¬(t ≤ j ∧ j < t + 0) := by omega
    cases ka <;> cases kb <;> simp [keepGo] <;> omega
  | cons w ws ih =>
    simp only [keepGo, List.length_cons]
    have hih := ih (t + 1)
    have hadd : t + 1 + ws.length = t + (ws.length + 1) := by omega
    rw [hadd] at hih
    by_cases hdrop : ((t == i && !ka) || (t == j && !kb)) = true
    · rw [if_pos hdrop]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hdrop
      rcases hdrop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hti0 : (!false && decide (t + 1 ≤ t) && decide (t < t + (ws.length + 1))) = false := by
          have : ¬(t + 1 ≤ t) := by omega
          simp [this]
        have hti1 : (!false && decide (t ≤ t) && decide (t < t + (ws.length + 1))) = true := by
          have : t < t + (ws.length + 1) := by omega
          simp [this]
        have htj : (!kb && decide (t + 1 ≤ j) && decide (j < t + (ws.length + 1))) =
            (!kb && decide (t ≤ j) && decide (j < t + (ws.length + 1))) := by
          have : (t + 1 ≤ j) ↔ (t ≤ j) := by omega
          cases kb <;> simp [this]
        rw [hti0, htj] at hih
        simp only [hti1, Bool.false_eq_true, ite_false, ite_true] at hih ⊢; omega
      · have htj0 : (!false && decide (t + 1 ≤ t) && decide (t < t + (ws.length + 1))) = false := by
          have : ¬(t + 1 ≤ t) := by omega
          simp [this]
        have htj1 : (!false && decide (t ≤ t) && decide (t < t + (ws.length + 1))) = true := by
          have : t < t + (ws.length + 1) := by omega
          simp [this]
        have hti0 : (!ka && decide (t + 1 ≤ i) && decide (i < t + (ws.length + 1))) = false := by
          have : ¬(t + 1 ≤ i) := by omega
          cases ka <;> simp [this]
        have hti1 : (!ka && decide (t ≤ i) && decide (i < t + (ws.length + 1))) = false := by
          have : ¬(t ≤ i) := by omega
          cases ka <;> simp [this]
        rw [hti0, htj0] at hih
        simp only [hti1, htj1, Bool.false_eq_true, ite_false, ite_true] at hih ⊢; omega
    · rw [if_neg hdrop]
      simp only [List.length_cons]
      have hf : ((t == i && !ka) || (t == j && !kb)) = false := Bool.eq_false_iff.mpr hdrop
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, Bool.not_eq_false'] at hf
      have hti : (!ka && decide (t + 1 ≤ i)) = (!ka && decide (t ≤ i)) := by
        cases hka : ka
        · have hne : t ≠ i := hf.1.resolve_right (by simp [hka])
          have : (t + 1 ≤ i) ↔ (t ≤ i) := by omega
          simp [this]
        · simp
      have htj : (!kb && decide (t + 1 ≤ j)) = (!kb && decide (t ≤ j)) := by
        cases hkb : kb
        · have hne : t ≠ j := hf.2.resolve_right (by simp [hkb])
          have : (t + 1 ≤ j) ↔ (t ≤ j) := by omega
          simp [this]
        · simp
      rw [hti, htj] at hih
      omega

theorem keepGo_length (ws : List Word) {i j : Nat} (hij : i < j) (hj : j < ws.length) (ka kb : Bool) :
    (keepGo 0 i j ka kb ws).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have h := keepGo_length_add 0 i j ka kb ws hij
  have hi : i < ws.length := by omega
  cases ka <;> cases kb <;> simp [hi, hj] at h ⊢ <;> omega

theorem keepGo_toFinset {ws : List Word} (nd : ws.Nodup) {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (ka kb : Bool) :
    (keepGo 0 i j ka kb ws).toFinset =
      (ws.filter (fun x => (ka || x != ws[i]) && (kb || x != ws[j]))).toFinset := by
  ext v
  simp only [List.mem_toFinset, keepGo_mem, Nat.zero_add, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨u, hu, hvu, hkeep⟩
    subst hvu
    cases ka <;> cases kb
    · simp [beq_iff_eq] at hkeep ⊢
      exact ⟨fun e => hkeep.1 ((List.Nodup.getElem_inj_iff nd).mp e),
        fun e => hkeep.2 ((List.Nodup.getElem_inj_iff nd).mp e)⟩
    · simp [beq_iff_eq] at hkeep ⊢
      exact fun e => hkeep ((List.Nodup.getElem_inj_iff nd).mp e)
    · simp [beq_iff_eq] at hkeep ⊢
      exact fun e => hkeep ((List.Nodup.getElem_inj_iff nd).mp e)
    · simp [List.getElem_mem hu]
  · rintro ⟨hv, h1, h2⟩
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hv
    refine ⟨u, hu, rfl, ?_⟩
    cases ka <;> cases kb
    · simp [beq_iff_eq] at h1 h2 ⊢
      exact ⟨fun e => h1 (by subst e; rfl), fun e => h2 (by subst e; rfl)⟩
    · simp [beq_iff_eq] at h1 ⊢
      exact fun e => h1 (by subst e; rfl)
    · simp [beq_iff_eq] at h2 ⊢
      exact fun e => h2 (by subst e; rfl)
    · simp

def sameWordSet (xs ys : List Word) : Bool :=
  xs.length == ys.length && xs.all (fun x => ys.contains x)

theorem sameWordSet_eq {xs ys : List Word} (nd : xs.Nodup) (h : sameWordSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameWordSet, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  have hsub : xs.toFinset ⊆ ys.toFinset := fun v hv =>
    List.mem_toFinset.mpr (h.2 v (List.mem_toFinset.mp hv))
  have hcard : ys.toFinset.card ≤ xs.toFinset.card := by
    calc ys.toFinset.card ≤ ys.length := List.toFinset_card_le ys
      _ = xs.length := h.1.symm
      _ = xs.toFinset.card := (List.toFinset_card_of_nodup nd).symm
  exact Finset.eq_of_subset_of_card_le hsub hcard


def rec6C (c : Nat) : Nat := (if c < 2 then (if c < 1 then 0x810780f080d580b623702330037003370272023001f001b30170013700f600b6 else 0x8470843683f483d583b68370833782f482b48270823081f081d581b481378119) else (if c < 3 then 0x9af09ab09a709a378cf08ce08cb28ca28c708c368b708b328a708a3a89f089b1 else (if c < 4 then 0xa470a432a3f0a3b0a370a3309cf09ce09cb99ca99c709c339bf49bb19b709b30 else 0xc4f0c4e2c4bac4aab4f0b4e0b4b7b4a7b470b43aa4f0a4e8a4b0a4a0)))
def rec6 (i : Nat) : Nat := (rec6C (i / 16) >>> ((i % 16) * 16)) &&& 65535
def rec5C (c : Nat) : Nat := (if c < 78 then (if c < 39 then (if c < 19 then (if c < 9 then (if c < 4 then (if c < 2 then (if c < 1 then 0xb54002c4000adc002970009c0002690009400024a0008cc002130007c0001e900074c001c90006d000194 else 0x2ae400a700028e4009f00026c400970002540009400011c000460001140004450010c000410000bc0002e9) else (if c < 3 then 0x6eec01b70006cc001af0006ae801a700068c000cf90032c000c790030c000bf9002ec400b79002ccc00af0 else 0xb0c002bf000aec0024f00092c0024700090dc023f9008ed8022f0008ac001cf00072d401c700070c001bf0)) else (if c < 6 then (if c < 5 then 0x2114008430021040082f0020b54082b0020a400827002094008239020864081f002074c081b302064c02c70 else 0x233e408cb00231e408c30022fe408bd8022ec408b73022bc008ab70229c008a390227d8089d20226c408470) else (if c < 7 then 0x290dc0a3f9028ed80a2f0028ac009cf80272d409c700270cc09bf0026eec09b73026cd409af0026ae809a70 else (if c < 8 then 0x40bc0102d8040ae81029a0409c0102500408ec101700405441013a02b1c00ac3002afc00abb00293c00a470 else 0x42ec010af0042ac010a700428d0109f0042750109c00413c0104d20412c010490040fc0103d0040ec010390)))) else (if c < 14 then (if c < 11 then (if c < 10 then 0x48cc0122f0048ac0114f00452c0113f0044ec0112f0044ac0112700448c010cf00432c010c740430c010bf0 else 0x605c01813206044813cf004f2c012cf004b2c012c7004b0c012bf004aec0124740490c0123f0048ed012370) else (if c < 12 then 0x628d0184f0061348184ba061268183f0060f40183b7060e5c182f0060b60182b0060a40182700608e418219 else (if c < 13 then 0x652d8193f0064ec8192f0064ae8192700633c018c7406315418c36062fc018bb7062bc018ab00629c018a55 else 0x6f3c01bcba06b3c01acb206b1c01ac3006afc01abb00691d01a431068fc01a3b0068dc01a2f0068adc194f0))) else (if c < 16 then (if c < 15 then 0x829c020a50082900203f2080f80203d2080f10203b2080e48202f0080b44202b0080a402017008054020132 else 0x8f1c023c3008afc822bb20853c0214b00851c021437084fc8213b0084bc0212b6082fc820bb5082bc020ab2) else (if c < 17 then 0xa2bc028ad50a2ac0283f00a0f40283b40a0e50282f00a0b40282b00a0a80282900a0a00281760a04ec2811b else (if c < 18 then 0xc0558301470c04c42bc700af0c02abf00aaec0294f10a51d82943b0a4fc0293b30a4bd8292ba0a2fc028bb7 else 0xc0f40303c80c0ec0303900c09c0302600c0958302420c08d0301f00c0784301d00c0704301b20c05c430160))))) else (if c < 29 then (if c < 24 then (if c < 21 then (if c < 20 then 0xc6b8031ab80c51c43143b0c4fc0313b10c4bc4312ba0c2fc030bb70c2bc030ae00c2b4030ac00c0fc0303e1 else 0xe04c0381100cf1c033c300cafc032bb00c8fc0323b00c8bc0322b00c8a8031c700c70c031bf00c6ee431af0) else (if c < 22 then 0xe4bc0392e10e4adc38bf20e2ee8383f00e0f48383ba0e0e68382700e08e83821a0e07d0381b80e066038170 else (if c < 23 then 0x1004ec3bc700ef0c43abf00eaec03a3fa0e8ec83a2f00e71d039bf80e6ed439af90e6ad0394710e50d8393f0 else 0x1010c040410100dc040354100cc0402f0100b68402b71009c0402501008d0401f0100764401b01005c040153))) else (if c < 26 then (if c < 25 then 0x106ac0414701050cc412f0104ac040c701030c040bf0102f8040bd0102f00404f010134c404b41011c040456 else 0x10cfc0433b010b3c042cb010b1c042c3010afc042bb010adc0424701090c0423f0108ec041bf0106ec041af0) else (if c < 27 then 0x120c50482f0120ac8482921209c048234120850481f01206e4481991205c04813312044c444f010f1c043c30 else (if c < 28 then 0x128fc04a3e1126fc049af01251cc492f01231c0484f01212ec4849b1211c0484541210cc48413120dc048334 else 0x140750501b81403c0500d01402c04bc7012f0d04b3f012cf844acf012b1c04ac3112afc04abe112aec04a470)))) else (if c < 34 then (if c < 31 then (if c < 30 then 0x1607c0581b4160650580f01602c05809014b1c852c3214afc052bd014af005047014114450430141040501f0 else 0x180b58602c3180a5c602691809406024318084c601e918074c601c91806505ac721611c0584501610c458411) else (if c < 32 then 0x181364604c31812686046018114c60446181040603e0180f58603c6180e5060360180d6860346180c58602e0 else (if c < 33 then 0x18958062520186d6461ad9185580615201847a460c50182940609a1182644609811825a460950182500604e0 else 0x1a06d4681701a04c4681211a04446810119358064d291915806452018f58063d2118d5a46352918b58062d20))) else (if c < 36 then (if c < 35 then 0x1a25a0684b41a1290684701a10c8683f01a0f40683b21a0dc0683341a0bc0682b71a09c0682371a07c0681d0 else 0x1a322468c741a30c068bf01a2ed468b741a2ce468af91a2b4068ab01a29e468a561a28d0689f81a26d468974) else (if c < 37 then 0x1a50e4693f01a4ec0693741a4cd8692f01a4b60692b41a49c0692581a48dc691f61a46d868cb91a32a468c99 else (if c < 38 then 0x1a8cd06a2f71a8ac069cf01a72d869c781a70e069bf01a6ee869b741a6cec69af61a6ac469a701a68c869470 else 0x1acec06acf01ab2cc6ac701ab0c06abf01aaedc6ab741aacc46a4f01a92dc6a4741a90e46a3f01a8ec06a374)))))) else (if c < 58 then (if c < 48 then (if c < 43 then (if c < 41 then (if c < 40 then 0x1c086c701a41c0650701841b13c06c4b41af3c06bcb01af1c06bc381ad3c06b4e41ad2d86b4741ad0d06b3f0 else 0x1c284c709a71c2664709871c1480704d01c1258704541c1058703d01c0e50703541c0c60702d01c0a4070250) else (if c < 42 then 0x1c6b6c715231c544c715031c4b4070cda1c324c70c551c305870bd51c2e5c70b551c2c5c70ad51c2a4070a55 else 0x1e03c0780da1e02e874d661d34ac745661d149073d661cf49c7356b1cd49c72d661cb480725661c94a471b5b)) else (if c < 45 then (if c < 44 then 0x1e2fc078bb01e2bc078ab01e27c0789b01e25c0789301e0fc0783b01e0bc0782b01e07c0781ba1e05c07813b else 0x1e6bc079ab01e51c0794341e4fc0793b01e4dd0793301e4bc0792b41e49c0792301e47c0791b01e31c078c30) else (if c < 46 then 0x2006e8800f0200344800bb1ef1c07bc301eb1c07ac301eafc07abb01e71c079c301e6fc079bb01e6dc079b30 else (if c < 47 then 0x2028c0809f02026d0804702010c0803f0200f58803ba200dc080330200bc0802bb2009c08023b2007d0801d4 else 0x204840811f0204740811b020464080cf02032c080c702030c080bf0202ec080b70202cc080af0202ad880a70)))) else (if c < 53 then (if c < 50 then (if c < 49 then 0x205044813f0204f40813b0204e4081370204d4081330204c40812f0204b40812b4204a508127020495081230 else 0x208ac081cf02072c081c702070d081bf0206ed081b70206cc081af0206ac081a702068d08147020514081431) else (if c < 51 then 0x20b2d082c7020b0c082bf020aec082b7020acd0824f02092c0824702090c0823f0208ec082370208cc0822f0 else (if c < 52 then 0x2209408821b22055c844f02112c083cf020f2c083c7020f0c0834f020d2c08347020d0c0833f020cec082cf0 else 0x22315088c10222f5088b90222d5088b10222b5088a9022295088a1422134888490220f5c88390220b5c8829a))) else (if c < 55 then (if c < 54 then 0x240b5090290240740901522335808cd2022f5808bd2022b5808ad202295808a5242255808952022335088c90 else 0x24315c90a6024295c90a40241368904972411809045024111090412240f80903d0240f0090390240d5c9031a) else (if c < 56 then 0x25358894d2a2515889452024f58093d2724d5809352024b58892d2024958092527246d6891ada24558091522 else (if c < 57 then 0x260f40983b8260dc098336260bc0982b12609c098230260880981702604d898126260458981062603c0980b5 else 0x262ed498b74262ce498af7262ac098a792628d0989f8262790989b52612d0984a4261250984702610e0983f0))))) else (if c < 68 then (if c < 63 then (if c < 60 then (if c < 59 then 0x264fc0993b0264dd099336264bc0992d82649c0992582648dc991f62646d898cf02632e498c742630c098bf0 else 0x26725899c862671e099c38266fc099bba266dd099b3b266bd899ad0266ac499a7026695c99a332651c099437) else (if c < 61 then 0x26aedc9ab7426acc49a4f02693809a4b72691d09a439268fc09a3b0268dd09a334268bdc9a2b02672d899ca6 else (if c < 62 then 0x2712d09bcf026f2c09bc7026f0e09b4f026d2d89b47426d0d09b3f026cec09acf026b2cc9ac7026b0c09abf0 else 0x281150a0413280f40a0394280d40a0314280b40a02a0280a40a02802806a4a0199280624a011b2713c09c4e0))) else (if c < 65 then (if c < 64 then 0x285580a1523283354a0c93283154a0c16282f54a0b97282d54a0b17282b54a0a90281480a0510281340a0493 else 0x2a0500a4d662934aca4566291490a3d6028f49ca356028d49ca2d6028b480a2529289464a2509288b50a1ad1) else (if c < 66 then 0x2a0f80a83d02a0f00a83902a0d80a83542a0d00a83102a0980a82502a0910a81e12a0740a81c12a0580a8150 else (if c < 67 then 0x2a5580a95232a3340a8c502a2c50a8ae02a2b40a8ac02a1380a84d12a1300a84982a1180a84542a1100a8411 else 0x2b1480abd602af49cab5602ad49caad602ab540aad402ab480aacd02a9580aa5292a8a80a9ae02a6b44a9ac1)))) else (if c < 73 then (if c < 70 then (if c < 69 then 0x2c1340b049b2c1140b04142c0f40b03902c0d40b03182c085cb01a42c0650b01842c0448acd602b3484ac560 else 0x2cf49cb35642cd49cb2d202cb440b2d002cad50b25602c94a4b1ad12c5580b15222c4b90b0c552c1480b0510) else (if c < 71 then 0x2e0e40b82e02e0b50b82c02e0980b82592e0900b81e92e0580b81532e0500b4d622d34acb45682d1490b3d60 else (if c < 72 then 0x2e5480b8c592e2d80b8b592e2d00b84e02e1368b84c02e125cb84602e1140b84442e105cb83e02e0f40b83c0 else 0x300664c018930044cbcd202f1580bc5202ef580bbd292ed580bb5292eb5a4bad202e9580ba5202e6b64b9560))) else (if c < 75 then (if c < 74 then 0x309580c2527306b64c156030548cc0c51301490c04d0301268c0450301040c03d0300e40c0290300840c01a9 else 0x320d50c82d7320940c81d9320564c4d2a311580c452030f580c3d2930d4a4c351930d424c2d6930b490c2b64) else (if c < 76 then 0x32d480cad6032b480ca560329480c9ad0325580c9520323140c8be0322f40c8bc032134cc8494321164c8410 else (if c < 77 then 0x341150d0410340c50d0290340850d01a9340664d018934044cccd60333480cc560331480cbd6032f480cb560 else 0x34cf80d2d6034b480d2be0349580d2529348f80d1adb345580d1523344f80d0cda343154d0520341340d049b))))))) else (if c < 117 then (if c < 97 then (if c < 87 then (if c < 82 then (if c < 80 then (if c < 79 then 0x361240d83d6360d4cd82d6360940d8154353580d4d2b351580d452434f49cd3d1734f41cd3c9b34d590d3527 else 0x371480dbd6036f480db56036d480dad6036b480da560369480d9ad0365580d9520363180d8c50363100d84d9) else (if c < 81 then 0x380cd0e02f0380ad8e02703808dce01f03806d4e01703804c4e0121380444e01013803c0e00b5373480dc560 else 0x382fc0e0be4382ed4e0b74382ce4e0af7382ac0e0a793828d0e09f83826d4e04b0381280e04703810e0e0370)) else (if c < 84 then (if c < 83 then 0x386f90e1bba386dd0e1b3b386bd8e1ab13869c0e1a333851c0e14373849c0e12583833c0e0cb93831d0e0c30 else 0x3893c0e24b73891d0e2439388fc0e23e4388ec0e2374388cd0e22f7388ac0e1cf03872d8e1c783870e0e1bf0) else (if c < 85 then 0x38d3c0e34b638d1d0e343438cfc0e33b038b3c0e2ce038b2cce2c7038b0c0e2bf038af90e2bb738add0e2b31 else (if c < 86 then 0x3a0e40e83173a0a50e821a3a0680e81903a0600e811a3913c0e44b438f2c0e3ca038f240e3c8038f1c0e3c38 else 0x3ad580eb5293ad190ead653ab490eac643a9590ea5273a9190e95653a5488e94643a3248e85203a1340e8492)))) else (if c < 92 then (if c < 89 then (if c < 88 then 0x3c9480f15603c5490f04533c0f58f03533c0b58f02503c074cf01543b34a8ec5203b1440ec5003af594ebd27 else 0x3e0a44f82133e0690f81943e0610f81163d3490f45603d1480f3d643cf480f35603cd480f2d603cb480f2560) else (if c < 90 then 0x401041003d1400e6d00353400c45002d1400a69001e0400745001c0400391000d0400328f84163e0e6cf8319 else (if c < 91 then 0x40d49102d6040b481025604094810156440549100560401545005414014ad0051b40142d004d44012690045b else 0x420f4108393420d4108319420b4108296420651080e342026d04d604134910456041148103d6440f49103560))) else (if c < 94 then (if c < 93 then 0x440d6510253440781101d444072d100e0440369100c442154108540421441085004213410849142115108411 else 0x445481112e0444b41112c04415811055a44152910529441465105094413411049944115510410440f6910397) else (if c < 95 then 0x4607851819846024514d604534811456045148113d6044f4811356044d48112d6044b4811256044948111560 else (if c < 96 then 0x465589195224615891855046152118520461441185004613411849846114118414460f4118390460c5518216 else 0x4734a91c5624714911bd6246f49d1b56446d49d1ad6246b5511ad4346b4811acd446af511a5604694a51a2a7))))) else (if c < 107 then (if c < 102 then (if c < 99 then (if c < 98 then 0x48144920502481381204d248130920494480b85202d2480b212026048094520248480381200d24803251cd62 else 0x48b58122d2048958522525488f852156048548121510485401213e0484f41213c04815812055248150920522) else (if c < 100 then 0x4a1581285504a1501285204a1441285004a13412849a4a0a41282164a024124d6049348123d6048f49523c90 else (if c < 101 then 0x4c0389300d74c03092cd624b34a92bd604af5412bd464af49d2ad604ab4812a5604a94a5295604a5489294d0 else 0x4c5581315204c5381314d24c5301305604c154d305434c1481305104c1401303d34c0b81302d64c0b0d30250))) else (if c < 104 then (if c < 103 then 0x4e1481385104e1401383a04e0e41383804e0a61382114e025934d224cf58133d214cb5a932d2a4c958132520 else 0x4f35413cd2a4ef5893bd274ef3813ad624eb4813a5634e94a5395624e5489395124e5409385624e154138542) else (if c < 105 then 0x500f49403c4500ec9402f0500b85402d0500b05402b45009c54026050096d402445008e1400f150038140096 else (if c < 106 then 0x5092c5424715090cd423f1508ec942370508cc9422f1508ac5404f0501381404d0501309404b4500fc1403e0 else 0x520b85482d2520b214826052096d4824852038143cf050f2c142cf050b2c142c7050b0c142bf050aec1424f1)))) else (if c < 112 then (if c < 109 then (if c < 108 then 0x5334814bd6052f4954ad6052b4814a5615294954956052554149540521381484d2521309483e0520f49483c2 else 0x548cc1522f0548ad9504f05412e95049a540fc1503b0540e41502f0540ae1502985409c1502365408594cd60) else (if c < 110 then 0x56085953cf054f2e952cfa54b2c952c7054b0d952bf054aec1524f35492cd524765490c5523f7548ec152377 else (if c < 111 then 0x58054560147580381600d75803215cd605734a95bd6056f49d5ad6056b4815a5605694a55849a560e4158290 else 0x5811816045958111d60411580f81603d7580f1d60390580d8560350580d1d60312580785601d758071960160))) else (if c < 114 then (if c < 113 then 0x58ad4162560589491622e0588b41622c05815816055758151d6052458145160504581381604d758131d60491 else 0x5a0d41683195a0655681135a024164d215915856452058f58163d2058d5816352058b58162d2058b44162d00) else (if c < 115 then 0x5ab4816acd45a95816a5295a1595685505a1501685205a1441685005a13416849a5a1141684145a0f4168390 else (if c < 116 then 0x5c1269703d05c0e41702d05c0549700e45c0341700ca5b34a96c5655b14916bd605af49d6b5645ad49d6ad65 else 0x5e0449780945d348173d605cf48172d605cb481725605c9481705605c1541705405c1481705105c1401704d0)))))) else (if c < 137 then (if c < 127 then (if c < 122 then (if c < 119 then (if c < 118 then 0x60115180410600d65802d060075180153600381800d0600315785505e1501785105e1401783d05e0e4178297 else 0x60d48182d6060b48182560609481823e0608f41823c06015818055060150180529601465805096013418049b) else (if c < 120 then 0x621425884d062126d8845462104188314620a418819962044d880996134818456061148183d6060f48183560 else (if c < 121 then 0x62f5198bd2762f3418b56462d49d8ad6762b4818abe06295818a52962935188567621541885406214a588519 else 0x641425904d4641265903d1640d4d902d164074590159640381900d06403298cd2b63159d8c52462f59d8bd50))) else (if c < 124 then (if c < 123 then 0x64f58193d2064d5819352064b58192d20649581925206491819245064910190560641545905416414a590519 else 0x6614419850066134198492660e4198317660a51981a066064198180660469980e166024994d2065158194520) else (if c < 125 then 0x6715259c5206713519bd6866f49d9b56066d4a59ad6866b4919ac646695919a5276615a19855066152198520 else (if c < 126 then 0x680d21a02e0680b61a02c26807a5a01d3680725a0169680541a0148680381a00d968030d9cd2a6715a19c554 else 0x689365a24c0681581a0558681521a052a681469a050a681181a0452681121a03e0680f61a03c8680d81a035a)))) else (if c < 132 then (if c < 129 then (if c < 128 then 0x6a0a41a81956a0445a80936934a5a4560691481a3d6068f495a356968d4a5a2d6068b481a2560689481a24e0 else 0x6af49dab5616ad49daad636ab481aace06a958daa5296a158da85506a1491a85146a1411a84136a0e41a8319) else (if c < 130 then 0x6c0d41b03396c0bc1b02d66c0ac1b01f06c05c1b015a6c04ddb00f06c0381b00906b34adac5636b1491abd63 else (if c < 131 then 0x6cafc1b2bb06c13c1b04da6c12c1b04706c1181b04556c1111b043a6c0fc1b03e06c0f41b03c56c0ec1b0370 else 0x6e0f65b83c96e0d41b82d96e0569b80e06d13c1b44ba6cf3c1b3cb06cf1c1b3c306cb3c1b2cbb6cb1c1b2c30))) else (if c < 134 then (if c < 133 then 0x6f1581bc5206ef581bbd206ed581bb5206eb581bad206e9581ba5506e9501b84d76e1181b84576e1125b83e0 else 0x700fc1c03b9700e65c0370700cddc0317700bc1c02b0700a81c0290700a01c01707004cdc01136f3581bcd20) else (if c < 135 then 0x70f3c1c3cba70f1c1c3c3070b3c1c2cb270b1c1c2c3070afc1c2bb07013c1c04ba701269c04707010c1c0410 else (if c < 136 then 0x731491cbd6072f49dcb56072b581cad20721269c8410720e65c8317720a81c8290720a01c81137113c1c44b3 else 0x74145dd0507741341d049a741151d0410740d51d0250740785d01d4740705d0150740341ccd607334a9cc560))))) else (if c < 147 then (if c < 142 then (if c < 139 then (if c < 138 then 0x760241d4d627534a9d4562751491d3d6074f49dd2d6274b481d2be074af41d2bc0741581d0550741501d0527 else 0x76b481dacd4761581d8550761501d8520761441d8500761341d849a761141d8414760c65d8217760651d8112) else (if c < 140 then 0x781401e04d0781249e03d0780941e0150780395e00d0780315dcd627734a9dc566771491dbd6076f49ddad68 else (if c < 141 then 0x7a0e41e82167a0449e80917934a9e3d6678f49de2d6878b481e2c5478b101e0566781541e0546781481e0510 else 0x7c0719f01507c034decd2a7af581ebd277ab5a1ead207a1599e85507a1519e85207a1441e85007a1341e849a))) else (if c < 144 then (if c < 143 then 0x7cb481f2ce07cb341f2cc07c1581f05527c1511f05247c1451f05047c1161f03d27c0d51f02527c0781f01d9 else 0x7e1481f85107e1401f84147e0e41f83157e0859f81987e0455f80917d3481f45607d1481f3d607cf481f2d60) else (if c < 145 then 0x80054a001388003c2000907f34a9fc56a7f1491fbd6a7ef49dfad6a7eb481fad107eb401f856a7e1541f8542 else (if c < 146 then 0x8011c2004568010c2003f0800f42003b7800dc200354800cca00270800942002398007c2001e180066200170 else 0x82f49e0ad6082b5420ad4082134208454820f4208354820942081e182054203cf080f2ea004f080136a004b8)))) else (if c < 152 then (if c < 149 then (if c < 148 then 0x840eee1039b840dc210330840c42102708408ee1021b8405c2101348404520cd608334aa0c5608314820bd60 else 0x86f49e1849a86105218390860c621821786044a13cfb84f2e6104f08412e6104998411c21043a84106a103f0) else (if c < 150 then 0x880b86202da880b162026088096a2024588058220155880516200e0880346200c08735a21cd2a87159a1bd60 else (if c < 151 then 0x8a044a2809189348223d6088f54223d4088f48a23ce088f34223cc0881582205558815162052288144a20502 else 0x8c0942302348c05c2301578c04de300f08b34aa2bd608af49e285678a1542285208a1442285008a0a4228217))) else (if c < 154 then (if c < 153 then 0x8f35823cd208ef5823bd508ef502384d78e0b5e382508e055e304f08c1342304b08c0bc2302d58c0ac230270 else 0x92044a481029013c2404ba90126a402f0900aca402929009c240239900866401709004ca4012290044a40102) else (if c < 155 then 0x940b42502b99409c6502569408e25017094055a501339403c6500939335824cd2a92126a4829092086648122 else (if c < 156 then 0x980ac2602909805c2601309804425cd609735425cd40960f56582da96096a58155940fc2503d5940eca502f0 else 0x2683909a0a42682179a044a602f0))))))))
def rec5 (i : Nat) : Nat := (rec5C (i / 16) >>> ((i % 16) * 22)) &&& 4194303
def rec4C (c : Nat) : Nat := (if c < 316 then (if c < 158 then (if c < 79 then (if c < 39 then (if c < 19 then (if c < 9 then (if c < 4 then (if c < 2 then (if c < 1 then 0x82c700004e000004d600004c2000049000003e000003d500003c4000039000002e000002d100002c00000261000025500002410000210 else 0x1013700100f000100b500091c00008d400008cc10008c400008bc00008b400008ac10008a40000854400084c4000844400083c40008347) else (if c < 3 then 0x10970001095600109300010470001043300103f000103b90010370001033200102f000102b50010270001023300101f000101b50010170 else 0x11274001123100111f900111b00010c700010c390010bf40010bb90010b700010b380010af80010ab80010a740010a3400109f400109b0)) else (if c < 6 then (if c < 5 then 0x11bf90011bb40011b700011b350011af80011ab50011a740011a390011470001143400113f700113b00011370001133700112f600112b1 else 0x12c760012c360012bf00012bb30012b700012b3a0012474001243600123f400123b40012370001233000122f400122bb0011c740011c34) else (if c < 7 then 0x18350001831400182d60018296001825400182140018156001811200180d000180940013c700013c370013470001343000133f000133b0 else (if c < 8 then 0x19b970019b5a0019b130019ada0019a960019a5a0019a1700191a600189a9001895600184db00184960018458001841000183d00018397 else 0x20b600020b530020b400020ae00020ad40020ac00020a940020a600020a590020a400020a1a0019cda0019c930019c5a0019c100019bda)))) else (if c < 14 then (if c < 11 then (if c < 10 then 0x28ac300211e000211d900211c00020ce90020cd00020cc90020c930020c600020c500020c400020c100020be00020bd00020bc40020b97 else 0x303c5003039200303600030357003034200302e000302d300302c000301e000301d000301ca00291c00028d430028cc30028c430028b43) else (if c < 12 then 0x38ac0003854800384ca003844800383c8003834a003824a00304e000304da00304c00030460003045a0030444003041200303e000303d0 else (if c < 13 then 0x4033300402f000402b30040270004023a00401f000401b10040170004013800400f000400b800391c00038d400038cc00038c400038b40 else 0x40bba0040b740040b3b0040af60040ab60040a700040a3200409f600409b1004097800409380040470004043500403f000403b20040370))) else (if c < 16 then (if c < 15 then 0x41a300041474004143000413f000413b80041374004133400412f000412b90041274004123900411f000411b00040c780040c350040bf0 else 0x4243400423f000423b00042374004233400422f000422b70041c790041c300041bf00041bb70041b740041b310041af00041ab40041a77) else (if c < 17 then 0x4811900480d000480990043c700043c350043474004343900433f000433b00042c740042c340042bf00042bb00042b740042b360042479 else (if c < 18 then 0x4a2da004a2900049a6a0049a2600492290048a2900484d400484940048450004841700483d60048396004831600482d80048290004819b else 0x50be00050bd60050bc30050b970050ae00050ad60050ac60050a94004a4da004a497004a45a004a417004a3da004a396004a35a004a313))))) else (if c < 29 then (if c < 24 then (if c < 21 then (if c < 20 then 0x601da00601c000591c00058cc00058c400058b4000511e000511d000511c00050ce00050cd00050cc30050c600050c530050c460050c10 else 0x604d400604c1006046000604500060448006041000603e000603d100603c000603600060352006034700602600060257006024200601e0) else (if c < 22 then 0x701bb0070170007013100700f000700b900691c00068cc00068c400068b40006854700684c4006844700683c700682c4006824400604e0 else (if c < 23 then 0x709f200709ba0070977007096a00709370070470007043100703f000703b40070370007033800702f000702b30070270007023400701f0 else 0x712f100712b60071270007123700711fb00711bb0070c770070c300070bf90070bb40070b780070b350070af20070ab20070a740070a30))) else (if c < 26 then (if c < 25 then 0x71c760071c310071bf00071bb20071b720071b3a0071af20071ab80071a7a0071a3a0071470007143400713f000713b700713720071330 else 0x733f000733b00072c710072c310072bf70072bba0072b7a0072b320072470007243000723f400723b90072375007233800722fa00722b2) else (if c < 27 then 0x78490007845b007841b00783d000783920078319007821b00781940078150007811000780d000780930073c770073c30007347a0073437 else (if c < 28 then 0x80bc0007acd1007ac90007ac51007ac1b007abd1007ab92007ab51007ab19007a2e1007a2ab0079ae10079aa400792a70078aa3007896a else 0x90250009024a00901e900901d300901c900891c00088cc500811e000811d900811c00080c600080c500080c450080c100080be00080bd5)))) else (if c < 34 then (if c < 31 then (if c < 30 then 0xa02b300a027200a023300a01f000a01b800a00f200a00bb00991c00098cc0009834900982c9009824900902e900902d500902c40090269 else 0xa1a3200a0c7600a0c3b00a0bf200a0bba00a0b7a00a0b3a00a0af000a0ab200a0a7200a0a3800a09f200a09ba00a097600a093600a02f0) else (if c < 32 then 0xa2bb000a247100a243100a23fa00a23b200a22f700a22ba00a1c7700a1c3000a1bf800a1bb500a1b7400a1b3000a1af900a1ab400a1a72 else (if c < 33 then 0xc013000b91c000b11d000b11c000aac6500aac2a00aa46600aa42700a9c6500a9c2300a8c2000a829700a821700a819300a809000a2bf0 else 0xc13b000c137000c133b00c12f000c12b000c127000c123a00c11f000c11b000c03f000c03b000c027000c023000c01f000c01b900c0170))) else (if c < 36 then (if c < 35 then 0xc919a00c23f000c23b000c237000c233000c1c7000c1c3000c1bf000c1bb700c1b7900c1b3600c1a7000c1a3000c147000c143500c13f0 else 0xd924000d81c300d808a00c94d900c949000c945000c941900c93d900c939000c935900c931800c92d000c929800c925000c921900c91d0) else (if c < 37 then 0x1181c300f934000f854900f84c000f844900f83c900f82c000f824000f81c000f808400f030000e92c000e84c000e844900e81c000e808a else (if c < 38 then 0x1704800170085016a3c0016834901680c5016008a015a34001580c4015008301480c0013954001381c901294c001281c901280800119440 else 0x19a54001980c00190080018a4c00188540018844001883c0018834901882c901881c9018814001880c301801800180084017a44001780c9)))))) else (if c < 59 then (if c < 49 then (if c < 44 then (if c < 41 then (if c < 40 then 0x1c814701c80c401c008a01bac4001b80c001b008901aab4001a854001a84c001a844001a83c001a824901a81c901a814001a80c001a008a else 0x2082540208156020811602080d402080cb0208097020008901fb4c001f80c001f008001eb44001e80c501e008001d80c001d008901cacc0) else (if c < 42 then 0x2112400210a4002091e002089e002089d002089c002084db02084980208458020841202083d002083990208356020831002082d10208296 else (if c < 43 then 0x22839a022835202282d1022829402281d5022815702280d4022809002184d2021849a02183d0021839002182d6021829602182540218218 else 0x23841902383d60238390023831a02382d002382a00238290023828002381930230ac002292600228a6002284d00228450022841002283d8))) else (if c < 46 then (if c < 45 then 0x248390024835a024825002481d2024816102481500248141024811802480d00248096024030002392d102389d202384d002384970238450 else 0x25821b02581980251b410250b4002501c1024acd0024a2a00249ae002492e002492d102492c10248ae002484d90248450024841902483d6) else (if c < 47 then 0x2789d2027829a027821902781930270cc00268c6902682d5026825002681d002680d70258496025845b025841b02583d002583920258314 else (if c < 48 then 0x2a80c002a12c002a04c002a0449029818302980c00291b580291ad8029135002912d602911e802903d40290129029011902901090289240 else 0x2d011602d010602d00a002c944002b9b4b02b818502b80c502b134002b054702b04c402b044702b03c702b02c402b024402a830002a8189)))) else (if c < 54 then (if c < 51 then (if c < 50 then 0x3081c1030814703080c4030008002f818902f154002e818002e80c002e14c002d818702d3c9002d33e402d2be402d23e402d12d402d0126 else 0x3382ca03381c7033814103380c80330080032a440032814603280c903204800320080031a3c00318346031814703180c00310080030a340) else (if c < 52 then 0x35844003583c0035824903581c1035814803580c00350084034a540034814703480c60340080033a4c00338548033844803383c8033834a else (if c < 53 then 0x3980800393440039014803900c503880800380089037acc003780c40370080036ac40036814a03680c60360080035ab40035854003584c0 else 0x3b83d303b839003b82da03b829a03b825003b821903b124003b09c003b054503b044503b034503b02c503a808003a34c003a01c103a00c0))) else (if c < 56 then (if c < 55 then 0x3d009403c924003c8ac003c854a03c84c503c844a03c83c503c834a03c81ca03c124003b92d103b925103b89da03b89c403b84d803b8490 else 0x3d245a03d235a03d22da03d126a03d0a2903d09d003d049b03d045103d041b03d03d003d039703d035003d031903d02d803d029003d0113) else (if c < 57 then 0x3e045303e044003e03e003e03da03e03c403e039203e036003e035403e034b03e026003e025a03e024003e016003e015003e014a03d9240 else (if c < 58 then 0x3f011403f009b03e924003e8b4003e854a03e84ca03e844a03e83ca03e82c503e81ca03e1ae003e04e003e04d703e04c203e049a03e0460 else 0x3f2c5603f2b5603f22e603f1aa703f12e603f0aab03f09ea03f04d403f049903f045003f041203f03d303f039303f031403f021203f0191))))) else (if c < 69 then (if c < 64 then (if c < 61 then (if c < 60 then 0x4123e104113e10410ba004104d0041049204102900410217041011a041009004092400408c4004004d204002d80400250040015103f9240 else 0x433ca00432cea04314e50430ca30430390043029704302160430113043009a04292400428d4004202d5042015a04192400413c920412be5) else (if c < 62 then 0x4413300441270044123004411f004411b004404700440430044037004403300440270044023004401f004401b4044017004401300439240 else (if c < 63 then 0x44243004423f004423b0044237004423300441bf40441bb00441b700441b340441af00441ab00441a700441a30044147004414300441370 else 0x4584c4045844004582440449cd00449c910449c500449c100449bd00449b900449b500449b140449ad40449a90044347004434300442470))) else (if c < 66 then (if c < 65 then 0x4894c004882400479440047824004780800469340046854004684c0046844004683c004682c4046824004681c0046808a046030004592c0 else 0x4d9d4004d834404d80c604d008004c9c4004c854004c834404c82c404c814404c80c104c008a04b9b4004b80c804b008b04a80c00498080) else (if c < 67 then 0x50ac4005080c0050008004f80c004f008004eab4004e854004e84c004e844004e83c004e824004e81c004e814404e80c004e040004e008a else (if c < 68 then 0x5581c0055814405580c2055008a054b54005480c80540080053b4c005380c60530080052b44005280c0052008a051acc005180c00510084 else 0x56849405683e005683d205683c4056839205682e105682d005682c105682940568260056825b05682440560080055c540055834405582c4)))) else (if c < 74 then (if c < 71 then (if c < 70 then 0x58035005802d60580290058015a05800d905800c305709c005705420570442057034805702c805694d0056939005684e005684d005684c2 else 0x5892c00588ac005884c905884490580a600580a500580a4005804da058046005804550580444058041a05803e005803d005803c50580390) else (if c < 72 then 0x599ac10598ae005984da05984980598456059841005983d005983970598354059825005981e105981d005981c1059815205980d00590300 else (if c < 73 then 0x5a84d005a849905a845005a841a05a83d305a839b05a831005a821b05a811405a234105a0b4005a0241059acd0059a2a70599ae00599ad1 else 0x5c821905c812205c811205c810205c0c4005b8be005b84d005b849005b82d505b825005b815705b80d705aab5105a92e505a8aa305a8a57))) else (if c < 76 then (if c < 75 then 0x5e8a5705e829005e811005e0d4005d8ce105d83d505d82d005d825605d815605d80da05d018205cbc9a05ca3e605c93e605c849a05c8292 else 0x6101c006083000608209060235006022d70601b580601ad80601264060045006002a006001a60600196060018605f92c005f84c405f8440) else (if c < 77 then 0x638191063818106380a006314c0062820906280c00621440061820406180c806123410611340061054006104c0061044006103c006102c4 else (if c < 78 then 0x66814906680c206600800659b40065824b065814406580ca065008006480c20640200063b464063ac64063a4640639ad8063946406381a1 else 0x6883c7068824606881c7068814806880c7068040006800800679d400678343067814206780c306700800669c400668542066834806682c8))))))) else (if c < 118 then (if c < 98 then (if c < 88 then (if c < 83 then (if c < 81 then (if c < 80 then 0x6c00c006b820006b808006b2cc006b014a06b00c106a808906a2c4006a014506a00c006980800690080068ab40068854706884c70688447 else 0x6f034506f02c506f01c506f014006f00c506e808006e354006e024606e00c406d808006d34c006d014506d00c606c808006c344006c0241) else (if c < 82 then 0x70831b07082d10708290070819007012c00700cc00700c4007009c0070054007004c0070044a07003c20700340070024a06f808006f4540 else 0x718390071816a0718150071814a07112c00710cc00710c4007094da07092da0708a6007084d007084940708450070841707083d20708390)) else (if c < 85 then (if c < 84 then 0x7292e10728aa20728a570728a4007283d207283920728110072809207212c00720c400720b40072044007201ca07183e007183d207183c4 else 0x74813407480f707480bb07412c00740cc00740c4007404c0073846007384520738444073841007382d307381d0073815207312c00730c43) else (if c < 86 then 0x7493b907492f507492b80748bf70748bb00748afa0748ab70748a700748a3407483f007483b407482f007482b107481f007481bb0748177 else (if c < 87 then 0x7504120750294075019707501120750097074abf0074abb00749bf00749bb20749b720749b350749af20749aba0749474074943007493f4 else 0x7612c007592d007592c00758c600758c500758c410753c550753c120752be50752ba30751be80751ba707513e507513a20750ba90750450)))) else (if c < 93 then (if c < 90 then (if c < 89 then 0x76a3320769470076943007693f007693b707693720769330076927007692360768372076833207682700768230076822007681700768137 else 0x7900840781340078044a07802c0078024a07801c70780080077830007723da077239807722d2077229007702a0076b3f0076b3b0076a372) else (if c < 91 then 0x7c00c007b808007b1c4007b054207b04c207b03c007b034207b02c707b024707b014007b00c007a808207a1b4007a00c6079144007902c9 else (if c < 92 then 0x80039a080035308002d6080029408001d107f808007f44c007f00c007e808007e344007e00c407d840007d808407d00c007c808707c1cc0 else 0x818361081833008181760818167081813108180f008180e508180b00810b0008103000808b0008089c008004d00800450080041408003d5))) else (if c < 95 then (if c < 94 then 0x820156082014708200e508200d008200c5081b3f0081b3b0081947108193f608193bb081937008193330818b700818b370818a700818370 else 0x828b9408283e108281e708281650822bd00822b9008212e608212aa0820ae00820ad50820ac508203e108203d008203c108203900820167) else (if c < 96 then 0x848be00848455084841008482d408481d0084815808480d408383d00838390083811308313450830b40083044108301c708301450828bd0 else (if c < 97 then 0x87020208700a008693400868441086824108681c70860300085abe10858453085841308582a208582920858282085819908581130850c40 else 0x8a014608a00c408980800891b4008902c7089014008900c3088828408880c00881440087828608780c008722d008712e908702220870212))))) else (if c < 108 then (if c < 103 then (if c < 100 then (if c < 99 then 0x8cb44008c814a08c80c008c008008b808908b1cc008b02c608b00c408a808008a1c4008a054808a04c808a03c408a034408a02c108a0249 else 0x8e8c4008e8bc008e8ac008e8a4008e89c008e854108e84c108e844008e83c008e82c008e824008e008008dc4c008d814508d80c008d0080) else (if c < 101 then 0x8f047008f043508f03f008f03b308f037008f033708f02f008f02b208f01f008f01b308f017008f013508f00b608e934008e8d4008e8cc0 else (if c < 102 then 0x8f1a3008f1a2008f13f408f13b908f137908f133408f127008f126408f123508f0bf408f0bb108f0b7708f0b3008f0a7008f0a6408f0a37 else 0x8f2b7408f2b3908f247008f245408f243a08f23f008f23b008f237008f233008f22f008f22b808f1bf408f1bb608f1b7008f1b3708f1a70))) else (if c < 105 then (if c < 104 then 0x8f845008f841908f83d608f839908f831808f829008f821908f819a08f3c7408f3c3b08f347008f343308f33f408f33b408f2bf408f2bb4 else 0x900a440900a1909009e109009d009009c1090099208facd008fa2a008f9ae008f945108f941908f93d108f939408f929808f8ae008f849a) else (if c < 106 then 0x900cd10900cc00900c980900c600900c590900c470900c110900be00900bd00900bc00900b900900b600900b570900b400900a600900a57 else (if c < 107 then 0x9103c309102c209101c209093400908d470908cc70908c470908ac40908a470902cd009022a70901ae009012e009012d009012c00900ce0 else 0x9182f009182b809181f009181b30918170091813209180b109113400910d400910cc00910c400910ac00910a40091054209104c20910443)))) else (if c < 113 then (if c < 110 then (if c < 109 then 0x9193740919339091927009192350918bf00918bb70918b740918b360918a700918a300918470091843209183f009183b709183700918336 else 0x91a470091a438091a3f0091a3b0091a370091a330091a2f0091a2ba0919bf70919bb00919b740919b310919a700919a3709193f909193b4) else (if c < 111 then 0x9203d009203970920312092029009202190920118091bc74091bc39091b474091b434091b3f4091b3b4091abf0091abb3091ab74091ab3b else (if c < 112 then 0x928bd40928bc00928b910928a600928a570928a440928a1409282e00921c510921c140921bd10921b990921a98092049809204560920414 else 0x930c400930ac00930340092acd0092a2a009292e009292d009292c00928ce00928cd00928cc60928c600928c500928c400928c100928be0))) else (if c < 115 then (if c < 114 then 0x940a320940370094033209401f409401b50940170094013309400b209393400938c4a0938ac00938445093824509381c409313400930cc0 else 0x941bb90941b700941b350941a790941a690941a3409413f409413b609413700941330094127009412370940b700940b3a0940a700940a57) else (if c < 116 then 0x94a2a0094a290094a2800949ae10948ad209483d1094839609482900948280094819b094811709433f009433b0094237009423300941bf4 else (if c < 117 then 0x9601560960147095ab0009593400958c4609522e009512e009512d009512c00950be10950bd20950bc80950b9009502a0094a3d5094a396 else 0x9604db09604c0096046009604510960440096041009603600960359096034609602600960257096024209601e009601d409601c10960160)))))) else (if c < 138 then (if c < 128 then (if c < 123 then (if c < 120 then (if c < 119 then 0x9701f009701b10970170097013409700f009700b309693400968cc00968c40096854009684c009683c109682c0096824109681c009604e0 else 0x9712f409712b90970bf20970bba0970af00970ab20970470097043809703f009703b80970370097033609702f009702b409702700970233) else (if c < 121 then 0x972c580972c340972bf00972bb00972b700972b3709723fa09723b209722f709722ba0971bfa0971bb70971af70971ab009713f509713b8 else (if c < 122 then 0x978ba7097849b0978454097841b097831409782d0097829209782100978199097811209780900973c780973c3509733f209733b00972c79 else 0x980c500980c42097bcd8097bc9b097bc58097bc1b097b3e8097b3a4097acd0097aba2097a3e8097a3a00979be80979ba909793e809793a3))) else (if c < 125 then (if c < 124 then 0x99037009903300990270099023009901f009901b009901710990132098934009834d00982b2009823600981360098135009813400980c60 else 0x999ae00999aa809992e109992aa09933f009933b0099237009923300991bf00991bb40991b700991b3909913f109913bb09913700991333) else (if c < 126 then 0x9e1cc009e00c409d808009d00c409c1b4009c014b09b144009b034709b008709a13d009a139709a0290099abd0099ab90099a2e0099a2a6 else (if c < 127 then 0xa534400a501400a483000a480800a42c400a400c00a200800a180c00a100870a0a4400a083490a080c909f829009f234009f014309e8080 else 0xa712e00a712d00a712c00a704d00a704510a704160a703d20a703540a702d00a702c10a7025b0a701d40a680800a644c00a601400a600c0)))) else (if c < 133 then (if c < 130 then (if c < 129 then 0xaa03900aa02d20aa01d70aa01510a90a400a89ad00a884db0a884580a883d00a883970a883560a882d10a882540a881560a79b400a789c0 else 0xab845b0ab84140ab83540ab82da0ab82900ab82500ab81d90ab81570ab80d70aa8ac00aa84450aa22d00aa12e10aa03e10aa03d00aa03c1) else (if c < 131 then 0xae03020ae00c00ad94400aca3e60ac92e30ac849b0ac84520ac84160ac83190ac82170ac81940ac81120ac0c400ababe00ab8be00ab84d0 else (if c < 132 then 0xb380800b300800b2a4400b280c10b2010b0b1a3400b100800b09cc00b083400b080c60b000800af81030af01290af01190af01090ae9b40 else 0xb789c00b785450b784c50b783c50b783450b782c50b782450b700800b6c4c00b680c80b601020b5b4400b500800b4ac400b4814a0b480c0))) else (if c < 135 then (if c < 134 then 0xb914400b90a400b894400b812d80b80be00b80bd10b80bcb0b804990b804500b804100b803130b802d60b802990b802100b8019a0b79440 else 0xbb01940bb01130ba94400ba8ac70ba84c40ba14400b99b970b99ad50b9849b0b984100b983970b983190b982d60b982900b982170b98113) else (if c < 136 then 0xbc05470bc04c70bc03c70bc02c70bc02470bc01c70bb94400bb245a0bb23970bb0be00bb049b0bb04510bb04130bb03940bb03170bb0290 else (if c < 137 then 0xbcab9a0bcab550bc92e50bc8be00bc84d00bc84970bc84530bc841b0bc839a0bc83540bc83140bc821a0bc81980bc81100bc14400bc0b40 else 0xbe04100be03940be02900be02170be01940be011b0bd94400bd8bc90bd85400bd84c00bd83400bd82c00bd82400bd81c00bd14400bcacd5))))) else (if c < 148 then (if c < 143 then (if c < 140 then (if c < 139 then 0xc001140c000900bf94400bf8cc00bf82c00bf02d50bf02600bf02500bf02450bf01d90bf015b0be94400be33970be2b650be0be00be0490 else 0xc102440c101c40c094400c044d60c03c230c02c660c024660c014660c00c270c004d40c004990c003930c003130c002920c002140c0019b) else (if c < 141 then 0xc281300c214400c1ace50c18bd10c184170c183120c182940c182170c1819b0c181190c114400c10d400c104c40c103c40c103440c102c4 else (if c < 142 then 0xc293b30c292f00c292b20c284700c284300c283f00c283b00c283700c283300c282f00c282b00c282700c282300c281f00c281b00c28170 else 0xc323a00c31be00c31ba40c2bc700c2bc3b0c2ac700c2ac3a0c2abf00c2abb00c2ab700c2ab300c2a3f00c2a3b00c29af00c29ab50c293f0))) else (if c < 145 then (if c < 144 then 0xc800800c780c90c700800c680c40c600870c580c10c480800c394500c394110c33c500c33c100c333e00c333a00c32be00c32ba00c323e0 else 0xd181e00d181db0d181c70d100800d044c00d001400ce80800ce00c30cd80800cd34c00cd00c60cc34400cc01400cb80870cb00800ca80c0) else (if c < 146 then 0xd194500d184e00d184d70d184c80d184600d184500d184480d183600d183510d183400d182e00d182d10d182c00d182600d182500d18241 else (if c < 147 then 0xd304d30d3045a0d303d00d303500d302d60d302540d301510d209c00d205480d204c80d203c00d203480d202c10d202470d1b3e00d1a3e0 else 0xd52c400d50ac00d4a3e00d4a3d00d4a3c00d484d20d484580d483d00d483c50d483570d482db0d481d00d481520d401830d38a400d31bd0)))) else (if c < 153 then (if c < 150 then (if c < 149 then 0xd68b400d62cd00d62be00d62bd00d62bc00d61ae00d604d70d604530d604130d603d20d603c40d603540d6025a0d601d90d601500d58302 else 0xd901500d900d80d83c400d80bc00d7b3e00d7b3d00d7b3c00d784d30d7845a0d783d00d783c50d782d60d782590d781d00d781530d6b440) else (if c < 151 then 0xdb01d10db01570da14630da02930da02180da01900da01120d98cc00d93c600d90c600d904d70d903d80d903520d902db0d902540d901d2 else (if c < 152 then 0xe104950e101210e101110e101010e0b4400e000800de00800dd80800dd34460dd00800dc80c40db8d400db04500db03560db02d10db0257 else 0xe589400e585400e584c00e583c60e582c20e582410e581c70e501000e4c4c00e300800e280800e234c00e204400e200c10e181000e134d0))) else (if c < 155 then (if c < 154 then 0xe784120e783140e781160e780990e734400e70a400e703c50e6b4400e62be20e6049b0e604130e603140e602190e601990e601120e5b440 else 0xeb3c140ea83f00ea83b00ea82700ea82340ea81700ea81300ea34400e9ac220e982920e9819a0e980900e934400e90cc00e880d00e83440) else (if c < 156 then 0xf001d70f000d00ef0a400ee84520ee83560ee815b0ee80d40ed89400ed04db0ed04510ed03570ed02570ed01d00ed015b0ec00800eb3c50 else (if c < 157 then 0xf30bd60f309d60f309560f302d40f302540f301540f300a50f284c20f283c20f282c20f282420f200c00f100900f08cc00f02c600f002d2 else 0xf40a400f401000f389870f344e00f344a00f33ce00f33ca90f334e00f334a80f32ce00f32ca80f324e00f324a40f31ce00f31ca20f314e0)))))))) else (if c < 237 then (if c < 197 then (if c < 177 then (if c < 167 then (if c < 162 then (if c < 160 then (if c < 159 then 0xf504e60f504a40f500eb0f489800f484c00f484440f483c00f483440f482c00f481ca0f411c00f40cc90f40c400f40bc40f40b490f40ac0 else 0xf534e30f534a70f52ce00f52ca90f524e60f524a40f51ada0f51a5a0f514e60f514a30f511ea0f50bdb0f509a70f509970f509870f50953) else (if c < 161 then 0xf681c00f612020f611c00f60cca0f60c4a0f60bca0f60b450f60aca0f5a50b0f589810f585000f580c20f544e60f544ab0f53ce60f53ca0 else 0xf70a530f709a90f709970f709870f709640f709530f709470f704e20f704a40f701ea0f689800f684c10f684410f683c10f683410f6824b)) else (if c < 164 then (if c < 163 then 0xf785000f744e20f744aa0f73ce80f73ca00f734e00f734a70f72ce00f72ca90f724e40f724a70f71ada0f714e00f714a20f711ea0f70bd3 else 0xf884c00f884400f883c00f882c40f882440f881c10f812010f811c00f80cc30f80c460f80bc60f80b460f7ad000f79acb0f789870f78949) else (if c < 165 then 0xf91adb0f914e60f914a30f911eb0f90bda0f90a530f909a70f909970f909870f909600f909530f909450f904e60f904a00f901eb0f88980 else (if c < 166 then 0xfa0bc60f9b50b0f99b480f9898b0f989410f985030f944e60f944ab0f93ce60f93ca40f934e30f934a70f92ce60f92ca00f924e00f924a9 else 0xfb09990fb09870fb09550fb04e10fb04a00fa89800fa84c20fa84480fa83480fa82c20fa82420fa81c70fa12010fa11c00fa0cc60fa0c46)))) else (if c < 172 then (if c < 169 then (if c < 168 then 0xfb3ce60fb3ca40fb34e40fb34a70fb2ce80fb2ca00fb24e00fb24a90fb1b510fb1ad10fb14e80fb14a30fb11e10fb0bd50fb0a550fb09a7 else 0xfc89890fc84c30fc83c60fc83460fc82c30fc82430fc81c90fc12010fc11c00fc0cc60fc0c460fbbd070fb89870fb85000fb44e80fb44ab) else (if c < 170 then 0xfd2ca00fd24e00fd24a90fd1b5b0fd1adb0fd14e00fd14a20fd11eb0fd0a5a0fd09a70fd09990fd09870fd095a0fd04e20fd04a40fd00ea else (if c < 171 then 0xfe82460fe81c20fe12010fe11c00fe0cc60fdc5000fd89870fd85000fd80c10fd44e20fd44aa0fd3ce00fd3ca70fd34e40fd34a70fd2ce8 else 0xff14e00ff14a20ff11e80ff0c560ff0a560ff09a90ff09970ff09890ff09560ff04e00ff04a00fe89800fe84430fe83c30fe83430fe82c6))) else (if c < 174 then (if c < 173 then 0x10011c00ffcd000ff89880ff85000ff44e00ff44a00ff3ce00ff3ca90ff34e00ff34a90ff2ce40ff2ca40ff24e40ff24a70ff1b580ff1ad8 else 0x100c4a9100bce0100bca0100b4e0100b4a1100ace9100aca9100a4e0100a4a01009ce01009ca010092d9100925910084a010081201001201) else (if c < 175 then 0x1049d0910445001040180103a500103818010301c3102814110201601020151102014110200e01019188101150010111c91010180100c4e0 else (if c < 176 then 0x10904491090340107830010704c0107044010701c9106b50010681001062d001060100105054010504c0105044010503c0105034910502c9 else 0x10d03f010d03b810d037010d033210d02f010d02b910d027010d023010d01f010d01b610d017010d013210d00f010b01c910a81801098480))))) else (if c < 187 then (if c < 182 then (if c < 179 then (if c < 178 then 0x10d11f010d11b010d0c7010d0c3010d0bf010d0bb110d0b7010d0b3a10d0af010d0ab010d0a7010d0a3110d09f010d09bb10d097010d093a else 0x10d1b7010d1b3010d1af010d1ab010d1a7010d1a3110d147010d143710d13f010d13b210d137010d133510d12f010d12b410d127010d1230) else (if c < 180 then 0x10d2bf010d2bb010d2b7010d2b3010d247010d243910d23f010d23b110d237010d233010d22f010d22b010d1c7010d1c3010d1bf010d1bb3 else (if c < 181 then 0x10d929b10d925010d921610d91d010d919710d896010d83d110d81d710d3c7010d3c3010d347010d343010d33f010d33b210d2c7010d2c37 else 0x10e0ad010e0a9610e0a5010e0a1010e09d010e099a10e02d210e025210e015210d945010d941610d93d010d939010d935010d931710d92d0))) else (if c < 184 then (if c < 183 then 0x1100111110010110f950010f8d0010f8a4010f150910e950010e149010e12d010e125010e0c5010e0c1810e0bd010e0b9810e0b5010e0b10 else 0x1110ac011101c51110141110950911085041108289110818111012d911012581100a56110096911004a4110049411003d011002291100121) else (if c < 185 then 0x1128d041128504112818111215001120d001120b4011201c5112014711195091118d04111850011181811111ac5111150411112c11110d00 else (if c < 186 then 0x114849011481211148111114810111415001140d001140c4011395091138d041138500113818111315071130d001130bc011305401129509 else 0x1160d0411605041160384116018111595001158d001158cc011515091150d041150500115018111492d911492591148ad0114896911484a0)))) else (if c < 192 then (if c < 189 then (if c < 188 then 0x11905041189500118924011881c61181507117b4e011794a011794901179480117925511791d511692d811691e611683d011681271161509 else 0x11a245011a235011a1a2411a12d011a126011a125411a124011a04a011a049011a048011a02d011a0164119950011992c011981c71191500) else (if c < 190 then 0x11c150011c050411b92d611b92c211b925311b849611b848011b816611b150411b134011b01c911a9ac111a950011a850011a34e611a24d0 else (if c < 191 then 0x11e050011d950011d944011d81c611d3d4411d150711d050011c950011c93c011c84c411c844711c834111c82c011c824011c81c011c1b41 else 0x11f826011f823411f81f111f81e011f81b811f817011f816011f150711f050711f038011e950711e94c011e844411e82c011e81c911e1509))) else (if c < 194 then (if c < 193 then 0x11f923411f91f011f91b511f847011f846011f843411f83f011f83e011f83bb11f837011f836011f833811f82f011f82e111f82b211f8270 else 0x11f9bb311f9b7011f9b3211f9af011f9ab811f9a7011f9a3111f947011f943011f93f011f93b011f937011f933511f92f011f92b011f9270) else (if c < 195 then 0x11fac3011fabf011fabb011fab7011fab3811fa47011fa43011fa3f011fa3b011fa37011fa33011fa2f011fa2b911f9c7111f9c3111f9bf0 else (if c < 196 then 0x120036012002e112002d912002c912002601200255120024512001e0120016011fbc7011fbc3111fb47011fb43011fb3f011fb3b011fac70 else 0x12044e012044a01203ce01203ca012034e012034a51202ce01202caa12024e012024a01201ce01201ca512012d11201251120046012003e0)))))) else (if c < 217 then (if c < 207 then (if c < 202 then (if c < 199 then (if c < 198 then 0x12180c612104c4121044712103c9121034112102c0121024012084e0120846012083e012083d712083c9120836112082e0120826012081e0 else 0x1231a60123049012302d012300a0123009012300801229ac0122814712200801219a4012184c1121844312183c6121834a12182c61218146) else (if c < 200 then 0x124ac95124abd01249ae0124849012483a012480a0124809012480801241b4012403c412402c012401441238080123249012323d012322d0 else (if c < 201 then 0x12880c212800801279cc012700801269c4012684c712683c0126834812682c01268240126814012680c012600801259bc012504001250087 else 0x12b3d4412aa3c012a854512a80c5129a34012981c2129814112980c1128a2c0128854212884cb128844812883c2128834412881c4128814b))) else (if c < 204 then (if c < 203 then 0x12e008412da54012d844312d83c612ca4c012c854312c844612c83c312c834612c82c612c81c012c814312c80c312c018112ba44012b80ca else 0x13181c01318149130ac4013081c8130814613080c012fabc012f854012f81c612f814812f008012eab4012e81c912e814012e028012e0108) else (if c < 205 then 0x13483c713482c0134824413481c5134814713480c71343d44133b3c0133854b13381c2133814113301091330080132ad401328141131acc0 else (if c < 206 then 0x136b54013683c813682c51368148135b4c01358540135844413583c013582c0135824013581c9135814013580c0134b440134854913484c0 else 0x138bd40138bcc013885401388440138834013882c0138824013881c6138814413880c4137bc40137854413780c0137040013701091370080)))) else (if c < 212 then (if c < 209 then (if c < 208 then 0x13d810913d808013d4d4013c810813c808013c454013b44c013b00c313a810913a808013a012713a011713a010713a00a013a0090139bd40 else 0x13e0c5013e0c1213e0bd013e0b9813e0b5013e0b1913e0ad013e0a9013e0a5013e0a1013e09d013e099013e02da13e025513e009913e0087) else (if c < 210 then 0x1418b40141898114181c214109871410184140ad461409ac614092c01408ac8140898714081c114009871400280140018413f8a4013f8988 else (if c < 211 then 0x1450987145038014501841448cc0144898b144098714401801438c40143898b1430987143018414295021428bcb142898914209891420180 else 0x14883431488242148250614815091480280148018614801051479500147844614783c314695001461490146125014602d4146025b1451503))) else (if c < 214 then (if c < 213 then 0x14984c5149844214983c814982c5149824a1492d07149150914912c614901811490109148ad411489ac1148950314884c9148844a14883c5 else 0x14c950014c450014c150914c018114c010514b950014b3d0614b150914b018614b010814a950014a350314a150914a018314a01091499500) else (if c < 215 then 0x14e034914e02e014e02d514e02ca14e026114e01e014e011714e010414dad4914d9ac114d850014d810114d4d0014d150714d018414d0103 else (if c < 216 then 0x14fad0014f810514f808914f054414f04c414f044414f03c414f034714f02c714e834814e82c814e04e014e046014e03e014e036014e0352 else 0x1560184155018415401841530480153018615284411528343152018515181c71510300151018415084c51508445150350815001081500080))))) else (if c < 227 then (if c < 222 then (if c < 219 then (if c < 218 then 0x1568940156846015684551568445156841015683601568355156834515683101568261156825a156824515681e015681da15681c51568195 else 0x1570971157095a157093615704701570430157041015703f015703b415702f015702b015701f015701b41570171157013615689601568950) else (if c < 220 then 0x157133315712f115712b21571275157123215711f115711bb1570c301570c101570bf01570bb41570af01570ab015709f015709da15709b7 else (if c < 221 then 0x1572c351572bf01572bb61571c701571c301571bf01571bb01571b701571b301571af01571ab01571471157143515713f115713b11571371 else 0x1578a5a1578a1a15789d0157899b157849015784501578410157835015783101578250157821015781d015781901573c701573c361572c70))) else (if c < 224 then (if c < 223 then 0x15802e015802da15802c515802601580255158024a1580160158015a158014a1579490157925015791d01578c5a1578c1a1578b5a1578b10 else 0x158811015809e015809d015809c01580460158045a158044a158041515803e015803da15803c515803921580360158035a158034a1580312) else (if c < 225 then 0x1589a5415891e41588c501588ad01588a5015884941588450158841015883d415883901588350158831415882d0158829015882501588210 else (if c < 226 then 0x1590360159035a159034a159031215902e015902d515902ca15901e015901da15901c51590160159015a159014a1589c941589bd41589ad4 else 0x1598394159835015983101598294159819015981101590a601590a501590a401590460159045a159044a159041a15903e015903d515903ca)))) else (if c < 232 then (if c < 229 then (if c < 228 then 0x15a0b4015a045015a041a15a025015a01d015a0150159a490159a3d4159a2d41599a6415992641598bda15984901598450159841015983d0 else 0x15b01d015b015015ab49015ab41015aa36015a9b6015a936015a8c5a15a849015a845015a841015a821015a819415a811015a0b6015a0b50) else (if c < 230 then 0x15c00c015bc49015bb42015ba46015b9c6015b946015b849015b831015b821015b819015b811015b0c6015b0c5a15b0c4a15b035015b0250 else (if c < 231 then 0x15c11d015c11c015c04d015c049915c045015c041815c03d415c039615c035015c031915c02d415c029715c025015c021815c00e615c00d0 else 0x15c945015c925015c84d015c849415c845015c841415c83d415c839415c835015c831015c82d015c829415c825015c821015c809b15c11e6))) else (if c < 234 then (if c < 233 then 0x15d124015d04d015d049515d045015d041815d03d415d039015d035015d031015d02d015d01d015d00e215d00d015d00c515c9cd415c9b54 else 0x15da45415da35415d9a2015d84d015d849015d845015d841015d83d015d839415d835015d831015d829415d819015d809a15d126015d1250) else (if c < 235 then 0x15e04c015e049715e046015e045015e044015e041615e026415e025015e024415e01e415e01d015e01c415e00ea15e00d015e00ca15da4d4 else (if c < 236 then 0x15e945015e84d015e849015e845015e841015e821015e819015e809015e341015e1b6015e149015e136015e135015e134015e04e015e04d0 else 0x15f819015f809a15f146015f145015f144015f04d015f049115f035015f026415f025015f024415f01d015f00e115f00d015f00c115eb4d0))))))) else (if c < 276 then (if c < 256 then (if c < 246 then (if c < 241 then (if c < 239 then (if c < 238 then 0x16002641600250160024416001e416001d016001c416000ea15fc4d015fb46015f949015f84d015f849015f832015f831015f830015f8210 else 0x16100d016100c0160b4e0160841016083101608210160819016014e016014d016014c0160046016004501600440160036016003501600340) else (if c < 240 then 0x16103e016103d416103c01610390161036016103501610340161031016102e016102d016102c0161029216101601610150161014016100e0 else 0x161829416181101618090161249016122d01611a601611a501611a4016104e016104d016104c016104941610460161045016104401610411)) else (if c < 243 then (if c < 242 then 0x16203171620250162015016200e716200d016200c0161a45416184d016184901618450161841016183d016183941618350161831016182d0 else 0x16284d0162849016284501628410162835016283101628210162811016280901621ad41621ac016204d01620497162045016204121620350) else (if c < 244 then 0x163811016380941631b601631b501631b4016304d016304901630450163041216303d0163039016302d01630254163015416300d01629bd4 else (if c < 245 then 0x16402d41640250164015016400d0163b4d0163b450163a3601639c5416384d016384941638450163841016383d4163839016382901638210 else 0x1648490164845016484101648310164829016482141648110164809a1641be01641bd01641bc016404d0164049b164045016404161640350)))) else (if c < 251 then (if c < 248 then (if c < 247 then 0x16502e016502d416502c016502601650250165024416501601650154165014416500eb16500d016500c0164bcd4164bc54164a3e416484d0 else 0x16582101658110165809b1651c601651c501651c4016504e016504d016504c0165049416503e016503d416503c0165036016503501650340) else (if c < 249 then 0x166045016603e016603d016603c416603601660350166034016602d016602541660150165a46016584d01658494165839016583141658294 else (if c < 250 then 0x16701d0167015016700d0166c4e0166a4e0166841016683901668314166829016682201668210166820016681101661ce01661cd01661cc0 else 0x16783d01678394167829416781901678110167809016723601672350167234016704d016704901670450167041016703d4167039016702d4))) else (if c < 253 then (if c < 252 then 0x16823c016804d0168049016804501680410168035016801d0168015016800ea16800d016800ca167a45416784d0167849016784501678410 else 0x169049516903d4169035016902d416901d0169015016900d016884d0168849016884501688410168831016881901688110168809016823d4) else (if c < 254 then 0x16a02d416a01d016a0150169a49016984d0169849016983941698310169829416981901698110169809a16924601692450169244016904d0 else (if c < 255 then 0x16b014016b00e216b00d016b00ca16a841016a839416a831016a829416a819016a811016a24e016a24d016a24c016a045016a03d416a0350 else 0x16b34d016b346016b345016b344016b04e016b04d016b04c016b049016b026416b025016b024416b01e416b01d016b01c416b016016b0150))))) else (if c < 266 then (if c < 261 then (if c < 258 then (if c < 257 then 0x16c812016c811016c810016c34e016c34d016c34c016c045016c025016c01d016c015016b84d016b849016b821016b819016b811016b8090 else 0x16e024516d831016d821016d819016d811016d44e016d44d016d44c016d035016d025016d01d016d015016cc4e016c841016c821016c8194) else (if c < 259 then 0x16e91d516e919116e8c9416e8bd716e8ad716e8a5716e89d716e849016e83d716e81d916e094016e04c516e044516e03c516e034a16e02c5 else (if c < 260 then 0x16f84ca16f844a16f83ca16f834516f82ca16f814a16e945416e941416e93d516e939716e935416e931116e92d416e929416e925416e9210 else 0x17081841701c941701bd81701ad81701a58170145017012d0170125017011a41701194170118417009e8170049417003d8170012416f8a40))) else (if c < 263 then (if c < 262 then 0x172044517203c517202c5172024517201451719a8017181801711ac01710ac017104c5171044517103c5171034a171024517101451709a04 else 0x174849017481211740c4017404ca17403ca174034517402ca174024a174014a1739b8017381801730bc01729b0417281841720b4017204c5) else (if c < 264 then 0x17680c01761c8117601801758cc11751c001750180174bc90174abe4174a3e41749be417493a01749390174938017492d917492581748be4 else (if c < 265 then 0x179834417982c0179824017981c017980c11791b44179018017881c617880c01781ac0178018017792c017781c417780c6177018017681c4 else 0x17b94c017b844017b82c017b81c017b80c617b1c4417b018017a944017a81c017a80c517a1bc017a018017993c0179854017984c01798440)))) else (if c < 271 then (if c < 268 then (if c < 267 then 0x17d824017d821417d816017d815017d814017d80e017c954017c84c017c844017c83c017c834417c82c017c824017c1cc017c038017c0180 else 0x17d844017d841417d83e017d83d017d83c417d839717d836017d835017d834017d831017d82e017d82d017d82c417d829317d826017d8254) else (if c < 269 then 0x17e835017e831017e82d017e829417e825417e821017e811017e1a4017e04c017e044017e03c017e034417e02c017e014017d846017d8450 else (if c < 270 then 0x17f841117f83d017f839017f835017f831017f82d017f829317f81d017f815017e9c9017e9bd017e849017e845017e841017e83d017e8390 else 0x180a3d4180a2d41809a6418084901808450180841018083d418083941808350180831018082d01808294180819018081101801ac017f8450))) else (if c < 273 then (if c < 272 then 0x18203c418202c41818450181841018183d41818390181836018183501818340181831018182601818250181824418181d01818150180a490 else 0x182ac94182abd41829ae418284901828450182841018283d018283a018283901828380182835018283141828210182819018281101821b40) else (if c < 274 then 0x18483d0184839018482941848210184819018481101841bc01838450183841418383d0183839018382d0183825418381d418381501830400 else (if c < 275 then 0x185824018581e018581d018581c018581601858150185814018580e7184b490184b410184b3d0184ab601849b64184849018484501848410 else 0x1860140185bcd0185bc50185aba0185846018584501858440185841518583601858350185834018582e418582d018582c418582601858254)))))) else (if c < 296 then (if c < 286 then (if c < 281 then (if c < 278 then (if c < 277 then 0x186bc901869be4186849018684501868410186831018682901868214186819418681101861c4018604c018603c0186034418602c01860240 else 0x188c490188bc6018884901888390188831018882901888210188819418881101881cc018783d1187835118782d1187825b18781d1187815b) else (if c < 279 then 0x18ba3c018b81c018b80c018b018018a81c018a80c018a0180189a2c0189854418984c4189844418983c4189834018981c4189814418980c0 else (if c < 280 then 0x18e83c018e018018da4c018d854418d844418d83c418d834018d82c418d81c418d814418d80c018d018018ca44018c81c418c80c018c0180 else 0x192acc019281c01920180191ac4019181c019180c61910180190abc019081c01900180190008b18fab4018f81c018f028018ea54018e8440))) else (if c < 283 then (if c < 282 then 0x19680c01960180195b440195854019584c019583c019582c0195824019581c0195814019580c01950184194b3c019481c4193ad401930180 else 0x198bc4019881c019880c61980400197b54019783c419782c41970180196b4c01968540196844019683c019682c0196824019681c01968140) else (if c < 284 then 0x19bc4c019b81c019b80c619b010019abd4019a0180199bcc019985401998440199834419982c0199824019981c0199814019980c31990180 else (if c < 285 then 0x1a0014219fa50419f9a0419f8a0419f850419f04c219f044819f03c819f034819f02c219f014819e950219e850019dcd4019cc54019c0180 else 0x1a2cd001a28c861a285001a1bd071a18b871a185071a0ad001a09a881a08a801a085001a01ac01a004c21a004421a003c21a003421a00248)))) else (if c < 291 then (if c < 288 then (if c < 287 then 0x1a502c41a502441a501441a4ad001a42d401a41ac01a404c41a404441a403c41a403401a402441a401441a3a5001a382801a304401a303c0 else 0x1ae0a401ac81801aa83001aa04c41aa04401a905401a904401a903441a902c41a8cd001a7c5001a6bd001a5b5041a504c41a504441a503c4) else (if c < 289 then 0x1b004451b003ca1b002ca1b001c01b0014a1afad001af9acb1af8a481af85001af04c01af04441af03c01af03441af01ca1af01401ae1500 else (if c < 290 then 0x1b1a4e41b1a4a71b19b551b19ad51b194e81b194a21b18bd11b18a511b184e81b184a71b104441b0b5041b09b421b08a401b085041b004ca else 0x1b384a41b381a41b380ea1b303c21b292c01b28c401b23d071b205071b1c4e81b1c4aa1b1bce81b1bca01b1b4e01b1b4a91b1ace61b1aca4))) else (if c < 293 then (if c < 292 then 0x1b401801b3c4aa1b3bce01b3bca71b3b4e41b3b4a71b3ace81b3aca01b3a4e01b3a4a91b39b5b1b39adb1b394e01b394a21b38a5a1b384e7 else 0x1b614e01b614a21b604a01b602201b601a71b5cd001b585001b504491b503c71b503491b502c71b501c21b501471b492c01b445001b40500) else (if c < 294 then 0x1b7c5001b781871b6a5001b681801b644e21b644aa1b63ce21b63ca01b634e01b634a71b62ce01b62ca01b624e21b624a01b61ada1b61a5a else (if c < 295 then 0x1bc84801bc044a1bc03471ba83001ba04c01ba044a1b9b50a1b981081b92d001b901001b805421b804c21b804401b803c01b803401b802c2 else 0x1c100db1c100b71c0a5061c08a801c089861c085041c082891c081811c025001c012401c00d001c009821c009401c001c61be02c01bd8182))))) else (if c < 306 then (if c < 301 then (if c < 298 then (if c < 297 then 0x1c10a361c109f01c109b31c109701c109321c103f01c103b41c103701c1033a1c102f01c102b41c102701c102301c101f01c101b41c100f0 else 0x1c113381c112f01c112b91c112701c112391c111f01c111b01c10c701c10c301c10bf01c10bb01c10b701c10b321c10af01c10ab01c10a70) else (if c < 299 then 0x1c122b71c11c701c11c301c11bf01c11bbb1c11b701c11b301c11af01c11ab01c11a701c11a361c114701c114301c113f01c113ba1c11370 else (if c < 300 then 0x1c134301c133f01c133ba1c12c701c12c301c12bf01c12bb01c12b701c12b301c124701c124301c123f01c123b61c123701c123301c122f0 else 0x1c2015b1c194501c194111c193d01c193901c193501c193101c192d01c192501c192111c191d01c183d61c180d11c13c701c13c301c13470))) else (if c < 303 then (if c < 302 then 0x1c21a501c20c901c20c501c20c1a1c20bd01c20b901c20b501c20b101c20ad01c20a901c20a501c20a201c20a101c20a001c202d01c2025a else 0x1c38a911c384e01c384661c383e41c383601c382e81c382671c381e81c381661c325061c30d041c302801c2a5001c28a801c21c901c21ad0) else (if c < 304 then 0x1c403481c402471c401c81c401461c3c4e01c3a4a61c3a4961c3a4861c3a2d01c39ad81c392641c38ca41c38c941c38c841c38c501c38bd0 else (if c < 305 then 0x1c502411c501c31c4a5061c48d041c485001c481811c42d401c425061c422c71c41ac81c40d041c40ac01c405401c404c61c404441c403c0 else 0x1c6a5061c68d041c685001c682841c681861c625001c60d001c60bc01c5a5061c58d041c585041c582871c5818b1c525001c50d001c50b40)))) else (if c < 311 then (if c < 308 then (if c < 307 then 0x1c805001c802801c801811c7a3e41c79ad01c792d91c792591c784a01c784901c782201c781211c781111c781011c7250a1c70d001c70c40 else 0x1c992d61c992561c98ce01c98ca71c983d41c925061c90d041c905041c902841c901801c8a5001c88d001c88cc01c885431c825061c80d04) else (if c < 309 then 0x1cb82d91cb82591cb25001cb01c61ca22d91ca02d41ca02281c9c4a01c9bce01c9bca41c9b4e01c9b4a81c9ace01c9aca21c9a4e01c9a4a9 else (if c < 310 then 0x1cd80c01cd2d401cd25051cd1ac11cca5001cc92c01cc85401cc82401cc81c71cc80c41cc250a1cc05041cb94541cb92541cb84991cb8480 else 0x1cf25081cea5051ce93c01ce85471ce84c41ce84471ce83411ce82c01ce82471ce81c01ce80c91ce25011ce05001cda5041cd82401cd81c9))) else (if c < 313 then (if c < 312 then 0x1d125081d103801d0a5021d094c01d085401d084441d082c01d082401d081c91d080c01d025061cfa5001cf94401cf82411cf81c61cf80cb else 0x1d284431d283c61d283431d282c61d281461d225061d202021d1a5051d195401d184c41d184471d183c91d183411d182c01d182471d14d48) else (if c < 314 then 0x1d41c9a1d41ad11d41a601d41a511d41a411d404901d400a01d400901d400801d3a5001d39ac01d382491d325001d2a5001d29a401d284c0 else (if c < 315 then 0x1d61bc01d5a5061d584001d580861d51c9a1d51ad11d51ac01d51a511d500951d500851d4a5061d4a2c01d480801d424901d423d01d422d0 else 0x1d880801d825001d7a5061d780801d725061d71c401d704c61d703c01d703441d702c01d702401d701401d700c01d6a5081d680881d62500))))))))) else (if c < 474 then (if c < 395 then (if c < 355 then (if c < 335 then (if c < 325 then (if c < 320 then (if c < 318 then (if c < 317 then 0x1d9a4e71d9a4591d984a01d984901d984801d982d01d925041d922c01d904c41d904421d903c81d9034b1d901cb1d901441d8a5061d88203 else 0x1dd81811dd25001dd24401dca5081dc85081dc25001dc23c01dba5001db85001db04911db04811daa5041da81c31da25061da05001d9c4e0) else (if c < 319 then 0x1df02301df01f01df01701df01371dea50a1de85001de25001de24c01de04461de03c31de03461de02c61de01c01de01431dda5061dd8500 else 0x1df23701df23301df22f01df22b61df04701df04301df03f01df03e01df03ba1df03701df03601df03301df02f01df02b91df02701df0256)) else (if c < 322 then (if c < 321 then 0x1df3c701df3c3a1df34701df34301df33f01df33b01df2c701df2c361df2bf01df2bb01df2b701df2b371df24701df243b1df23f01df23b0 else 0x1e002d61dfc4e01dfc4a01dfbce01dfbca01dfb4e01dfb4a01dface01dfaca01dfa4e01dfa4a01df83e01df83601df82d01df82511df8153) else (if c < 323 then 0x1e300c01e22bc01e205401e202491e201c61e1ad401e180801e12b401e105401e102401e101c91e084431e083c61e004da1e004601e003e0 else (if c < 324 then 0x1e582231e582131e582031e580a01e580901e52d401e502401e485401e42cc01e405491e402491e401c01e32c401e305401e302471e301c8 else 0x1e881401e880c01e7b4401e785471e784c01e783c71e782c01e782471e781c41e781411e780c71e6b3c01e682411e681c31e602031e60080)))) else (if c < 330 then (if c < 327 then (if c < 326 then 0x1ea82471ea80c01ea04001ea02061ea00841e9b5401e983c81e982c51e982481e8b4c01e885401e884441e883c01e882c01e882401e881c9 else 0x1ed80c31ed02061ed01091ed00801ecbd401ebbcc01eb85401eb84401eb83401eb82c01eb82401eb81c61eb81441eb80c41eabc401ea8544) else (if c < 328 then 0x1f182d01f182581f181551f082031f080801f002221f002121f002021f000a01f000901efcd401ef02021ef00801eec5401edc4c01ed8543 else (if c < 329 then 0x1f302e01f302641f301e11f301601f300e51f28a801f18c501f18c1a1f18bd01f18b951f18b501f18b141f18ad01f18a941f18a501f18a10 else 0x1f33ca41f334e01f334a71f32ce01f32ca71f324a91f314e01f314a31f30c551f30bd51f30a971f304e01f304a01f304601f303e01f30360))) else (if c < 332 then (if c < 331 then 0x1f42d091f40d001f3ad401f3ad001f3a2c41f39ac11f38ac51f384c01f384401f383c01f383401f381c11f381401f344e61f344ab1f33ce6 else 0x1fa044a1fa03c51fa03431fa01491f882801f881851f782841f781801f70c401f682801f681891f60bc71f582801f581801f50b401f48184) else (if c < 333 then 0x1fb82011fb81831fb25091fb04c51fb04421fb03c81fb02c51fb01441faad071faa5061fa82031fa81811fa2d401fa25091fa1ac11fa04c9 else (if c < 334 then 0x1ff03441fe82081fe81801fe25041fdc5001fda5061fd82051fd81811fd25001fcbd061fca5061fc82011fc81861fc25001fbb5031fba506 else 0x201035020102d120101d120101122010100200850420081042002d0020022c4200010120000861ff82861ff05481ff04c81ff04441ff03c4))))) else (if c < 345 then (if c < 340 then (if c < 337 then (if c < 336 then 0x20784a0207816120702802060280205028920501832040480204028920384462038340203028720282c820204c42020445201046020103e0 else 0x207a4c9207a4a0207a4502079ce02079ca92079a272079260207925120792412078c592078bd92078a972078a602078a592078a4920784e7) else (if c < 338 then 0x20889c12082d462081ac620815032080ac22080500207c4e7207c4ab207bce9207bca4207b4e0207b4a7207ace4207aca7207a4e7207a4d0 else (if c < 339 then 0x2092ca620924e02091ce02091ca320914e020914a92090bd820900a1208ad402089ac120892c02088cc02088c402088bc02088b402088a44 else 0x20a84e620a84a420a2d4020a12c020a0cc620a0c4020a0bc020a0b4020a0a4420944e020944a42093ce02093ca720934e020934a62092ce0))) else (if c < 342 then (if c < 341 then 0x20ab4e320ab4a720aace020aaca920aa4e620aa4a420aa45020a9a6020a9a5a20a9a4a20a94e620a94a320a8c5320a8bd620a8a9020a8a56 else 0x20c014020bad4020ba2c120b92c020b8cc420b8c4420b8bc420b8b4020b250920b228720b1ac620b050020ac4e320ac4ab20abce620abca0) else (if c < 343 then 0x20c9ae020c9ad120c9ac120c94e620c94a320c8bda20c8ae020c84e620c84a020c81e120c80a020c04c020c044020c03c020c024420c01c1 else (if c < 344 then 0x20d1ac920d0b0020d050420cc4ab20cbce620cbca420cb4e320cb4a720cace620cacd020cacc320caca020cac5020ca4e020ca4a920ca2a6 else 0x20e84e820e84a020e04c020e044020e034020e024420e01c120e014020db54120da34120d934020d8cc020d8c4020d8bc020d350920d2d49)))) else (if c < 350 then (if c < 347 then (if c < 346 then 0x20ec4e820ec4ab20ebce620ebca420eb4e420eb4a720eace820eaca020eac5020ea4e020ea4a920e9ad120e94e820e94a320e8c5520e8bd5 else 0x21084e221084a421080ea21004c121003c12100341210024b21001c0210014120fb54120fa34120f934020f8cc020f8c4020f3d0720f0500) else (if c < 348 then 0x210c4aa210bce0210bca7210b4e4210b4a7210ace8210aca0210a4e0210a4a92109ae42109ad12109ac121094e021094a22108b172108ada else (if c < 349 then 0x21294a32128c5921284a0212044321203c32120343212024621201c22120143211b540211a34121193402118cc021145002111ac52110500 else 0x213a34121393402134d042130500212c4e4212c4a4212bce0212bca7212b4e4212b4a7212ace0212aca0212a4e0212a4a92129ad621294e0))) else (if c < 352 then (if c < 351 then 0x21444e021444a12143ce02143ca021434e021434a72142ce02142ca721424e021424a921414e021414a321404a0214045021401a0213b540 else 0x2169ac1216818021645002162d412161ac12160180215ad402159ac921584c4215844421582c421582442158144214ad002149ac12148180) else (if c < 353 then 0x21a04c921a044821a0349219854021984c021982412198140218ad0021824e02180121217054821704c8217044921703c9217034821702c8 else (if c < 354 then 0x223844722383c72220bd022202d5222015522192c0220834021f834021f018121e834721e048021d844621d834721c029021b054021a8300 else 0x22a034122a02c42298504229810522945002292d0722902872290181227ad00227818522681842260c41225818422481842242b40223ad00)))))) else (if c < 375 then (if c < 365 then (if c < 360 then (if c < 357 then (if c < 356 then 0x22d026122d01d022d011022d010022c850422c810422c030022b84cb22b844122b2d0022b010122a830822a054222a04c022a044422a03cb else 0x2328bd12328ae42328ad72328acb23284a02328165232030023103002300302230018222f048022f030022e844522e834422e010022d0354) else (if c < 358 then 0x23389c923315002330b412330504232c4aa232bce7232bca0232b4e0232b4a9232ace0232aca9232a4e9232a4a42329ce42329ca72329255 else (if c < 359 then 0x23494a32348bd12348ad623484a023413402340cc02340c462340bc62340ac32340a4a23393402338cc02338c402338bc02338ac02338a40 else 0x2358c402358bc02358ac023525042350504234c4ab234bce6234bca0234b4e3234b4a7234ace0234aca9234a4e6234a4a42349a5a23494e6))) else (if c < 362 then (if c < 361 then 0x23634e023634a72362ce02362ca923624e423624a723614e023614a22360bd62360ae423604e723604a423601ea23600a423593402358cc0 else 0x23784c0237844423782c0237824023781ca237814023713402370cc02370c402370bc0236ad002369acb236850023644aa2363ce82363ca0) else (if c < 363 then 0x238850923844aa2383ce82383ca023834e023834a92382ce62382ca423824e423824a72381ad523814e623814a32380bd123804e623804a9 else (if c < 364 then 0x23a14e023a14a223a0b5a23a04e023a04a423a00ea23984c723983c723982c7239824723981c2239814723913c02390cc02390c40238bd09 else 0x23b81c823b814723b13c023b0cc423ac50023a850023a44aa23a3ce023a3ca723a34e423a34a723a2ce823a2ca023a24e023a24a923a1ad1)))) else (if c < 370 then (if c < 367 then (if c < 366 then 0x23c34e023c34a923c2ce423c2ca423c24e423c24a723c1ad823c14e023c14a323c0c5623c0b5623c04a023b844923b83c723b82c723b8247 else 0x23dace923daca023da4e023da4a023d9ad923d94e023d94a023d84a023d81a923d13c023ccd0023c850023c44e023c44a023c3ce023c3ca9) else (if c < 368 then 0x240810023f854023f84c923f844023f83c023f834023f82c023f450023f018923e350023e018023dc4a023dbce023dbca023db4e023db4a9 else (if c < 369 then 0x2491ac924901c52470bd02470256247015324503c0244818024403c9243848024304402430349241830024104c9241044024103c0240ad00 else 0x24d854824d84ca24d844824d834824d82c824d450024d350324d030624d018124c018024b018024ac50024a8c4124a01892492d492492b44))) else (if c < 372 then (if c < 371 then 0x251826025181d1251038525083c625035432500500250010024f838924f830024f04c424f044724ead0024eab4624e810724e808024e0386 else 0x256a5042568bc0256850425595022558bc1255850025483872538389253818325284402528349252034725183e025183602518351251834b) else (if c < 373 then 0x25a01a0259cd0025985002590449259034925902c7259024725901c22590147258c50025885002580249257b50425785042572d002570500 else (if c < 374 then 0x25abd0025a818025a44e025a44a025a3ce025a3ca025a34e025a34a025a2ce025a2ca025a24e025a24a025a1ad025a14e025a14a025a04a0 else 0x260048025f844025f834025e030025d84c025d844025d2d0025d010025c054025c04c025c044025c03c025c034025c02c025bc50025b8180))))) else (if c < 385 then (if c < 380 then (if c < 377 then (if c < 376 then 0x26601c1265a3c02640c502640bd026402d026402582640152263950026393c026384c82638448263834826382c2263824226184402610180 else 0x26a4d0026a3d0826a038026a0184269c500269bd062698384269818126881842680cc026781802670c45266b3c02662d422662bc02661ac1) else (if c < 378 then 0x26d04c926d044526c850926c810926c2d0426c010526c008026b840026b054826b04c826b044926b03c026b034826b02c126a850026a8100 else (if c < 379 then 0x27103c5271034527102ca27101c5270848027084092700445270034726f850726f810726f040726e844826e050026e010026d840926d8300 else 0x2758c402758500275818b27515002750c40275050027484072738409272810027183d4271835527182d027181d5271811027181002710508))) else (if c < 382 then (if c < 381 then 0x27894e027894a027884a027881a02784d0027805002773d072770500276b5092768c4b27685042762d002761acb2760c4a2760500275a50b else 0x27a044027a03c027a034027a02c027945002790180278c4a0278bce0278bca0278b4e0278b4a0278ace0278aca0278a4e0278a4a02789ad0) else (if c < 383 then 0x28114402810d002810980281094028101c627f018027e048027d844027d834027c030027b84c027b844027b2d0027b010027a054027a04c0 else (if c < 384 then 0x28202b72820270282023328201f028201b62820170282013228200f028200d328200b8281c5002818d002818981281850028181812814500 else 0x2820c332820bf02820bb12820b702820b3a2820af02820ab32820a702820a3128209f028209bb2820970282093a28203f028203b828202f0)))) else (if c < 390 then (if c < 387 then (if c < 386 then 0x2821ab02821a702821a312821470282143728213f028213b22821370282133528212f028212b42821270282123028211f028211b92820c70 else 0x2822b302822470282243928223f028223b12822370282233728222f028222b02821c702821c302821bf02821bb32821b702821b302821af0) else (if c < 388 then 0x28294502829416282925028281d728280d62823c702823c302823470282343028233f028233b22822c702822c372822bf02822bbb2822b70 else (if c < 389 then 0x28323e02831be028313e02830c502830c122830b502830b102830ad02830a902830a502830a1028309d0283099a28302d328302532830153 else 0x2858d002858ac028581c428545002850d00285050028502802850181284c500284a4402848d002848a402844500283c5002833c902832be0))) else (if c < 392 then (if c < 391 then 0x2868d002868b40286854628684c128683c628682c1286824628681cb286814628645002860d0028605002860181285c500285ac402859ac4 else 0x288c5002888d002888cc028845002880d0028805002880181287c5042878d002878bc028745002870d0028705002870181286c500286b440) else (if c < 393 then 0x28b044628ac50028a844128a81c628a80cb289b464289ac64289a46428994642898420289835028945002890d00289050028903072890180 else (if c < 394 then 0x28d044928cc50028c854028c844428c81c928c80c028c450028c1ac128c050028c044728bc50028b92c028b844028b81c728b80c428b4500 else 0x28ec50028e944028e81c628e450428dc50028d93c028d854728d84c428d844728d834728d82c028d824728d81c028d80c928d450028d1441))))))) else (if c < 434 then (if c < 414 then (if c < 404 then (if c < 399 then (if c < 397 then (if c < 396 then 0x2910247290c5002908380290450029014c0290044429002c029001c929000c028fc50028f850028f34e028f04a028f049028f048028f0194 else 0x292249129223d029223c02921be12921a6029200902920080291c50029184002914500291154029104c4291044729103c9291034729102c0) else (if c < 398 then 0x294054829404c4294044229403c8294034229401ca294014429400c8293c500293840029380802934500292c500292ac4029284002928080 else 0x29623c02960545296044a29600c5295c500295a441295844329545002950541295044b29501c329500c1294c5002948444294450029422c0)) else (if c < 401 then (if c < 400 then 0x298814329880c3298450029805002980181297b4e029784a02978490297848029781a52978195297818529745002972440296c5042964500 else 0x29a450029a040029a0280299c500299a540299844329983c62994500298c500298a4c02988543298844629883c3298834629882c629881c1) else (if c < 402 then 0x29cac4029c81c929c450429bc50029babc029b844029b81c729b450029b2c4029b044929b008029ac50029aab4029a854029a844429a81c9 else (if c < 403 then 0x29f450029f2d4029f044929ec50029e450029e2cc029e044729e01c029dc50029d850029d34e029d04a029d049029d048029d019429cc500 else 0x2a134402a104c02a103c72a102c02a102472a101c42a101472a0c5042a045002a033c02a005412a0044b2a001c329fc50029f840029f8080)))) else (if c < 409 then (if c < 406 then (if c < 405 then 0x2a285402a284442a283c02a282c02a282402a281c92a281402a280c02a245002a205002a1b4e02a184a02a184902a184802a181942a14500 else 0x2a53c402a4c5002a484002a404202a404102a404002a400a02a400902a3c5002a3b5402a384422a383c82a382c52a345002a2c5002a2b4c0) else (if c < 407 then 0x2a745002a73d402a6c5042a645002a63cc02a605402a604402a603402a602c02a602402a601c72a601442a600c42a5c5002a585002a54500 else (if c < 408 then 0x2a903542a903332a902f02a902b72a902702a902382a901f02a901702a901322a8c5002a885002a845002a844c02a7c5002a784002a78109 else 0x2ac14402ab84002ab80802ab4d402aa03502a9c4e02a9c4a42a983542a982d42a982542a981542a904702a904322a903f02a903b62a90370))) else (if c < 411 then (if c < 410 then 0x2b083072b081802af45002af34402af04c72af03c72af02c72af02472af01472aead482aeac402ae24402ac8c122ac82d52ac82552ac8158 else 0x2b404c42b404482b385042b382042b381032b304872b285422b284c12b284492b283c92b283492b282cb2b205042b201062b1c5002b0c500) else (if c < 412 then 0x2b902d42b901d02b884892b881892b784802b704c72b704462b703462b685042b681012b604872b584c22b505002b501012b484802b48300 else (if c < 413 then 0x2be83402be82c02be45002be05002bdbd072bd85002bd35092bd05042bcad002bc85002bc250b2bc05002bb15002bb05002b903d02b90356 else 0x2c5815a2c504462c502c32c385402c301802c204802c184402c183442c003002bf85402bf84c02bf84402be85442be84c02be84442be83c4))))) else (if c < 424 then (if c < 419 then (if c < 416 then (if c < 415 then 0x2c9a4e02c99ca62c98ca92c984a02c981262c981162c981062c804492c803c72c802c72c802472c801472c704482c703c82c582d52c58255 else 0x2cb80892cb44e02cb34e42cb24e02cb1ca32cb14a92cb04a42cb00a32cb00932cb00832ca8d0a2ca89c72ca81842ca01832c9c4e02c9b4e0) else (if c < 417 then 0x2ce05072cd85402cd85002cd80c52cd2d4b2cd05482cd05002cc854b2cc84cb2cc844b2cc83cb2cc834b2cc81ca2cc80c02cc0d0b2cc0100 else (if c < 418 then 0x2cf85412cf85092cf81c02cf80ca2cf3d412cf05402cf05092ce85402ce84c02ce84442ce83442ce82c02ce81ca2ce80cb2ce35452ce0547 else 0x2d182d32d182c02d181e02d180e02d105472d105002d0854b2d0844b2d083cb2d0834b2d082c12d081ca2d080c02d045442d005482d00500))) else (if c < 421 then (if c < 420 then 0x2d203c02d203442d202c02d184e02d184da2d184c02d184602d1845a2d184442d183e02d183d02d183c52d183602d183572d183422d182e0 else 0x2d484442d483c02d483402d482c02d3049a2d304102d303992d303172d302902d285452d284ca2d284452d283ca2d2834a2d204c02d20444) else (if c < 422 then 0x2d901802d9008a2d880c82d804802d8008b2d784442d783402d780c82d700802d680c12d603002d584c02d584402d581c02d485442d484c0 else (if c < 423 then 0x2dd05002dd01c72dd00c22dc84c42dc84442dc83c02dc83442dc82c02dc0d042dc01822db84452db83c52db00802da80c02da00842d980c1 else 0x2dfbd462df85402df85002df05482df05022df00c32de85402de85002de05472de05092de01c82de00c32dd85402dd85002dd2d002dd0546)))) else (if c < 429 then (if c < 426 then (if c < 425 then 0x2e203d02e203c62e203542e202d82e200e62e185042e183802e105472e104412e102cb2e101c02e100ca2e085002e081802e005472e000ca else 0x2e40a692e40a562e40a462e404a42e401212e401112e401012e382802e303902e303182e302a82e302982e302882e284402e283c02e203e6) else (if c < 427 then 0x2e594a92e592642e584a02e580a12e580912e580812e512c02e50d092e509c72e501802e492c02e481842e434e42e424a72e41ce02e40ca9 else (if c < 428 then 0x2e802482e801c32e800c92e7b5452e785402e785002e725452e705462e705062e69ac02e68d092e681002e6008b2e5b4e42e5a4a02e59ce4 else 0x2ea01c22ea00c72e9c54b2e985482e985002e905452e905032e904c52e900c42e8bd452e885402e885002e805422e804c22e804422e80342))) else (if c < 431 then (if c < 430 then 0x2eb03d32eb03c02eb03602eb03502eb034a2eb02602eb025a2eb02402eb01e02eb00e02eacd4a2ea85492ea85002ea05432ea050a2ea0443 else 0x2ec04c92ec04492ec03c92ec02c92eb84c32eb84432eb83c32eb83432eb82462eb04e02eb04d92eb04c32eb04602eb04552eb04442eb03e0) else (if c < 432 then 0x2ee2ce02ee2ca02ee24e02ee24a02ee04e02ee04a02ee01e02ed9b402ec92e02ec849a2ec84162ec83902ec83182ec82162ec1b402ec0549 else (if c < 433 then 0x2ef85402ef84c02ef84402ef83c02ef83402ef82c02ef1d402ef1d002eead402eead002ee44e02ee44a02ee3ce02ee3ca02ee34e02ee34a0 else 0x2f500802f480c62f401802f400872f380ca2f304802f300842f284402f283402f280c92f181c02f103002f100842f084c02f084402f080c6)))))) else (if c < 454 then (if c < 444 then (if c < 439 then (if c < 436 then (if c < 435 then 0x2f885042f881ca2f805462f805062f801c72f800c22f78d002f781012f6ad402f684c12f684412f683c12f683412f6824b2f600892f580c0 else 0x2fb05402fb05002fb01c82fa85462fa85002fa05482fa05002fa01c52fa00c12f985402f985002f92bc02f905402f905072f901c12f88541) else (if c < 437 then 0x2fd821a2fd03432fcad402fc2cd02fc22a72fc04d22fc04562fc03d02fc03542fc02e02fc02502fc01e12fb85422fb85002fb83802fb2cc0 else (if c < 438 then 0x30080c3300054730004c930003c73000243300014a2ff83042ff05422ff04c02ff04402ff03cb2ff02c02fd84992fd841a2fd83932fd8310 else 0x3038183303029530301a13030191303018130300a030205423020181301854230181833010300301008030084cb300844b300834a30081c0))) else (if c < 441 then (if c < 440 then 0x307834630780c73070080306834230681c730680c630601803060080305834430580c530504803050080304844a304834430480ca3040180 else 0x308ab60308a4e4308a4a73089ce03089ca63089b603088ce43088ca93088c993088c893088b6030884a43088123308811330881033080080) else (if c < 442 then 0x3098b413098ac03098a4030989c0309818a30915033090187308c4e4308c4a4308bce4308bca0308b4e4308b4a6308b414308ace4308aca3 else (if c < 443 then 0x30a34e330a34a730a2ce030a2ca930a24e630a24a430a14e630a14a330a04e330a04a730a00eb309950030993c03098d083098cc43098c47 else 0x30b1d0030b1bc030b0d4430b0d0830b0cc830b0c4830b0b4230b0ac830aa54130aa50a30a854830a850a30a44e330a44ab30a3ce630a3ca0)))) else (if c < 449 then (if c < 446 then (if c < 445 then 0x30bc4e230bc4aa30bbce830bbca030bb4e030bb4a730bace030baca930ba4e430ba4a730ba36430b94e030b94a230b84e030b84a430b81ea else 0x30d84a030d83a030d054330d02c630d024630d00c730c9d0030c9bc030c8d4230c8d0230c8cc230c8c4230c2d4430c2d0030c054830c0500) else (if c < 447 then 0x30e150230e054230e050030dbce030dbca730dace030daca030da4e030da4a930da3e030d94e030d94a230d949230d948230d93d030d84e0 else (if c < 448 then 0x30f04d230f04c030f02e430f02d230f02c430f026430f025730f024230f00e430e9d0030e9c4030e8d4230e8d0230e4d4030e4d0a30e3c8a else 0x3111502310bc9a310a3e631093e6310849a3108298310821931081223101c403100542310034331002c230f84c030f82c430f824430f04e0))) else (if c < 451 then (if c < 450 then 0x31380e03131d403131d00312bd40312bd05312850031244e031244a03122ce03122ca031224e131224a531204e031204a03119c403118180 else 0x316044a31600ca31485403148440314834131482c031403c0313bc90313a3e131384e031383e031383d031383c031382e131382603138160) else (if c < 452 then 0x31b050331b00c231a040031a018031a008031980c031881ca31802c031801c03178180317808031700c031683013168180316808231604cb else (if c < 453 then 0x31d04d231d03e031d02d831d025031c854231c850031c3d4031c14c031c054631c050031c02c531c00c031b854031b850031b81c131b0546 else 0x322008032184c9321844532180c932104003208542320834832082c03203d40320038031e849a31e829231e821631e044631dbd4031d14d0))))) else (if c < 464 then (if c < 459 then (if c < 456 then (if c < 455 then 0x326811132681013260080325844332581c232580c53250182324818232401a43240194324018432400a03230080322844832280c03220300 else 0x328050032794c03278d073278c443278ac032789c83278180327018b326c4a4326b4e0326ace03269ce03268ca93268c6732684a03268121) else (if c < 457 then 0x328c4aa328bce8328bca0328b4e0328b4a7328ace0328aca9328a4e4328a4a732894e032894a232884e232884a432881ea328254a3280540 else (if c < 458 then 0x32a826a32a825032a824a32a80ea32a3d4632a14c032a054032a05003299cc03298d433298d003298c433292d433292d0032905483290500 else 0x32c029632c021832b9d4032b844032b834032b82ca32b03c332b02c332b024332a94d032a83e032a83d332a83c032a82e032a82da32a82c4))) else (if c < 461 then (if c < 460 then 0x32f02ca32e9d4032e9d0032e4d0032dbce032dbca132dacea32dacaa32da4e032da4a032d84e032d84a032d83a032d1d4032c14e032c0397 else 0x33401c433400ca33301c03328180332808033200c0331808033100c03308302330808433004c2330044033000c032f054032f044032f0340) else (if c < 462 then 0x33524a933514e233514a23351492335148233504e233504a733502e43350264335016033500ea3348540334850433481c233405413340507 else (if c < 463 then 0x3361d023360d423360d00335bd42335bd07335bcc033595023358540335850733582c4335824433580c533544aa3352ce23352ca033524e3 else 0x33982523398249339816033904003389502338838033803a2338039233803823380294338021b3374d4033684e033683d033682d23368253)))) else (if c < 469 then (if c < 466 then (if c < 465 then 0x33b81c033b80ca33b050633a844033a834133a82c033a4d4033a03c233a0248339bce033984e033983e033983d233983c233982e13398260 else 0x33e818033e808033e054733e01c033e00ca33d818233d018033d008033c854033c80c233c030633c018033c008033b854733b84c333b844a) else (if c < 467 then 0x3408b613408b543408b413408b123408ae03408ad03408ac03408a943408a603408a5b3408a443408a1834089e034089d434089c033f8182 else (if c < 468 then 0x3410c483410bc83410b483410ac83408ce03408cd03408cc43408c943408c603408c593408c473408c1b3408be03408bd73408bc93408b98 else 0x34200b83418d403418cc03418c403418bc03418b403418ac0341854234184c3341844234183c23418342341824234181433410d483410cc8))) else (if c < 471 then (if c < 470 then 0x34222f034222b73420470342043534203f034203b23420370342033334202f034202b33420270342023734201f034201b7342013534200f0 else 0x3423474342343934233f034233b03422c743422c343422bf03422bb03422b743422b363422479342243434223f034223b034223743422334) else (if c < 472 then 0x342a35a342a313342a2da342a29034284d434284943428450342841734283d634283963428353342831634282d834282903423c703423c35 else (if c < 473 then 0x3430bd03430bc43430b983430b603430b543430b463430ae03430ad03430ac03430a94342a4da342a497342a45a342a417342a3da342a396 else 0x34402c4344024534401443438d443438cc43438c443438b443430ce03430cd03430cc43430c943430c603430c543430c403430c1b3430be0)))))))) else (if c < 553 then (if c < 513 then (if c < 493 then (if c < 483 then (if c < 478 then (if c < 476 then (if c < 475 then 0x34482b33448270344823434481f034481bb344813134480f034480b93440d403440cc03440c403440b40344054434404c4344044434403c5 else 0x344ab32344a470344a430344a3f4344a3b9344a375344a338344a2fa344a2b23448470344843134483f034483b43448370344833834482f0) else (if c < 477 then 0x345041b34503d034503923450319345021b344bc77344bc30344b47a344b437344b3f0344b3b0344ac71344ac31344abf7344abba344ab7a else 0x3458bd23458bc03458b923452cd13452c903452c513452c1b3452bd13452b923452b513452b1934522e134522ab34504d034504903450454)) else (if c < 480 then (if c < 479 then 0x3468d403468c403468542346834334682c234681423460d423460c403458ce03458cd03458cc23458c943458c603458c503458c423458be0 else 0x34723fa34723b23472371347233334722f734722ba3470470347043834702f034702b4347027a34702333470134347012434700fa34700b3) else (if c < 481 then 0x347bc9a347abe8347aba2347a3e6347a3a034784d7347849a3478292347821034781223472c793472c343472bf03472bb034724723472432 else (if c < 482 then 0x3498231349813234980f034980b63490d403490444349034534902c434901443488d423480ce03480cd03480cc23480c9434801a0347bcd6 else 0x349ac30349abf0349abb0349a474349a431349a3f7349a3b0349a377349a330349a2f0349a2b734983f034983b734982f034982b23498270)))) else (if c < 488 then (if c < 485 then (if c < 484 then 0x34b844034b83c034b824034b81c034b814134b80c434a3ce234a3ca634a2ce234a2ca034a24e234a24a134a039034a029034a0213349ac70 else 0x34f80c034f020134f008934eacc034e814834e80c934e018034e008234dac4034d80c034d008234c80c034c008034bab4034b854034b84c1) else (if c < 486 then 0x3520080351b4c035180c035101803510080350b44035080c0350008434fad4034f84c134f844034f83c034f834034f824034f81c034f8141 else (if c < 487 then 0x3548b413548ac03548a4435489c035401803540080353c540353834135382c035381c0353814035380c03530084352b54035281c035280c0 else 0x35544e635544ab3553ce63553ca035534e335534a73552ce03552ca935524e635524a435514e635500eb35495403548cc43548c473548bc9))) else (if c < 490 then (if c < 489 then 0x356bca0356b4e0356b4a7356ace0356aca9356a4e4356a4a735694e035681ea3561d403560cc83560c483560bc83560b423560ac8355a50b else 0x35844e635844aa3582ce83582ca035824e035824a935814e635801223579d403578cc23578c423578bc23572d00356c4e2356c4aa356bce8) else (if c < 491 then 0x35c84cb35c844a35c81ca35b039035a9d4035a4d0a359bce0359bca7359ace0359aca0359a4e0359a4a935994e03591d403590cc2358bd07 else (if c < 492 then 0x36183083610ac036084d436084943608450360841936083d13608393360835b360831336082d8360829035f81c035e81ca35d81c035d0301 else 0x363a3e036384d2363849a36382d836382573628b403622cd036222aa36204d93620490362045a362041036203d336203943620350362025a))))) else (if c < 503 then (if c < 498 then (if c < 495 then (if c < 494 then 0x366ab40366854636684c6366844036683c0366824736681c1366814836680c036604003658d4036503d236502d036502563640c40363bc9a else 0x36a834236a824936a81ca36a814336a80c436a0080369acc036980c73690080368ac40368814a36880c0368008036781c736780c03670080) else (if c < 496 then 0x36e008036db54036d80c436d008036cb4c036c81c136c80c036c008036bb44036b824b36b80c036b008036aad4036a84c836a844436a83c4 else (if c < 497 then 0x37301823720300372018337184c937184453714d40370bd403702d4836fa54036f008036ec54036e834536e82c936e81c236e814036e80c6 else 0x375ace0375aca3375a4e0375a4a7375a497375a487375a2d73759ce03759ca63759a5737584a437581233758113375810337501823740182))) else (if c < 500 then (if c < 499 then 0x376a2c03768d043768cc43768c423768bc83768b4b37689cb376894437681803762d003760187375c4a4375bce0375bca0375b4e4375b4a6 else 0x37744ab3773ce93773ca437734e037734a73772ce43772ca737724e737724a03771ce03771ca937704e737704a0377016137700e9376ad00) else (if c < 501 then 0x3789ca33789a6437884a437880a3378809337880833782d0037822c03780d473780d043780cc73780c473780bc73780b4737809c03778500 else (if c < 502 then 0x379810b3792d003790089378c4a4378bce0378bca7378b4e0378b4a6378ace0378aca6378a4e0378a4a0378a490378a480378a2d43789ce0 else 0x37a84a737a81e137a054a37a04ca37a044a37a03ca37a01cb37a014a37a00c0379ad00379a2c03798d0b3798cc13798c403798bc73798b40)))) else (if c < 508 then (if c < 505 then (if c < 504 then 0x37b8c4637b8bc637b354137b350037b054737b050037ac4ab37abce637abca437ab4e337ab4a737aace637aaca037aa4e037aa4a937a84e6 else 0x37ca4a937c84e537c84a737c054737c050437c04c737c044737c034737c01c637c014737c00c837bb50037bab4037b8d4637b8d0b37b8cc6) else (if c < 506 then 0x37d8d4737d8d0437d8cc737d8c4737d3d4537d3d0737d054037d050737cc4ab37cbce637cbca437cb4e437cb4a737cace837caca037ca4e0 else (if c < 507 then 0x37eaca037eab5437ea4e037ea4a937e84ea37e84a437e80ea37e054637e04c637e03c637e034637e01c737e014637e00c237db50037dab40 else 0x38000c237fb50037fab4037f8d4737f8d0437f8cc737f454b37f450037f054837f050037ec4aa37ebce037ebca737eb4e437eb4a737eace8))) else (if c < 510 then (if c < 509 then 0x380ace0380aca0380ac90380ac80380ab54380a4e0380a4a9380a2e438084e038084a03800546380044638003c6380034638001c73800146 else 0x382015a382014038200e0381b500381ab403818d473818d043814d0b3812d003810500380c4e4380c4a4380bce0380bca7380b4e4380b4a7) else (if c < 511 then 0x3828349382814938204e038204da38204c938204603820455382044438203e038203d438203c538203603820350382034a38201e03820160 else (if c < 512 then 0x383ab50383849a38384103838397383831738382a038381133832b40383054438304c4383044538303c538301c438284c9382844938283c9 else 0x3862d043860500385ad40385ad0038544a13853ce13853ca038534e038534a03852ce03852ca038504e038504a0384ab4038483003842d00)))))) else (if c < 533 then (if c < 523 then (if c < 518 then (if c < 515 then (if c < 514 then 0x38902c038882c0388035038802e038802d038802c0388026138801d1388011038800e73878500387810038684c4386844538683443862d40 else 0x38d844038d83c038d00c438c830038c808038c00c738b830038b818138b808038b00c038a848038a830038a808038a044138a034038a00c0) else (if c < 516 then 0x3910548391050039100c1390854039085003900540390050738f854038f850038f808038f054738f050938f01c838e054838e01c938e00c3 else (if c < 517 then 0x394831939481133932cd039304d6393045639303d03930354393015039285003922cc03920542392050039201c1391854639185003918185 else 0x39a018339a008039980c0399048039900803988448398834439880c839802833970288396830039604c33960446394849a39484163948397))) else (if c < 520 then (if c < 519 then 0x39d09c239d018439c818939c3ce039c2ca239c24e039c1ca839c04a039c012839c011839c010839b834639b80c039b008039a82c639a80c4 else 0x39f854539f83c539f82c539f814539f80c039f3d4139f054039f050739e854039e850739e80ca39e2d4439e054839e050039d850239d0d00) else (if c < 521 then 0x3a102c43a101403a084e03a084d13a084c03a083e03a083d03a083c63a082e43a082d83a082c43a081603a081523a081473a080e43a00500 else (if c < 522 then 0x3a500803a480c03a403003a384c03a384403a383c03a2049a3a203973a202903a201123a185403a184403a183443a181c03a104c03a103c0 else 0x3a905073a9048a3a885403a885003a82d003a805473a805003a801c63a785423a780c93a704443a703c03a680c03a601803a600803a580c7)))) else (if c < 528 then (if c < 525 then (if c < 524 then 0x3ab81133ab81033ab02803aa83903aa82a03aa82903aa82803aa81123aa03c03a983e03a983d03a983c13a982d53a981503a93d413a90540 else 0x3ae05403ae05003ad80873ad05003aca3c03ac8d093ac81873ac01873abbce43abb4a63abaca33aba4e43ab9ca63ab9b603ab84a43ab8123) else (if c < 526 then 0x3b085043b0054a3b004453b003453b002ca3b001c03b0014a3b000c13afc5443af85483af85003af05403af05033af00c53ae85473ae8504 else (if c < 527 then 0x3b284143b283173b282903b281133b22c403b204c93b184493b104da3b104603b104553b104443b103503b102d33b1015a3b100e03b0a3c4 else 0x3b52d403b52d003b4bd403b4bd003b444a03b43ce03b43ca03b434e03b434a03b42ce03b42ca03b404e03b404a03b3ac403b2a3e03b2849b))) else (if c < 530 then (if c < 529 then 0x3bb80c33ba80c03ba00803b980c43b901803b882c03b804803b800843b784403b783403b780c43b700873b680c03b603003b584c03b58440 else 0x3be05403be05003be01803bd85403bd85093bd80c53bd05403bd05043bd01c53bcad003bcabc03bc85403bc85073bc81c13bb85483bb81c9) else (if c < 531 then 0x3bf83e03bf83503bf82d13bf81593bf05043bebd403bebcc03bea4c03be85453be85083be84453be83453be82ca3be81c03be81453be80c1 else (if c < 532 then 0x3c2018b3c182803c181033c1049a3c104133c103173c102aa3c1029a3c1028a3c101233c101133c101033c084453c03d403bf84d03bf8455 else 0x3c600893c584453c583403c580c03c502803c500803c484483c480c03c405463c402873c384093c383003c304c43c2bd463c283803c20302))))) else (if c < 543 then (if c < 538 then (if c < 535 then (if c < 534 then 0x3c904483c902c63c900c43c882843c8818b3c802893c801833c782ab3c7829b3c7828b3c781a43c781943c781843c780a03c682873c60480 else 0x3cb81803cb01833cabca03cab4e03caace03caa4e03ca9ca63ca9be43ca84a03ca81263ca81163ca81063ca04493ca02c33ca00c53c98080) else (if c < 536 then 0x3ce82c23ce81c93ce81483ce80c33ce3d413ce05403ce05093cd85473cd85073cd05403cd05003cca4443cc80893cc05003cba4403cb8d09 else (if c < 537 then 0x3d101133d0acc03d084493d003c23cf84d73cf83e03cf83d23cf83c43cf835a3cf82d33cf81503cf80e03cf05003ce85483ce83c83ce8348 else 0x3d2bce03d2bca03d2b4e03d2b4a03d2ace03d2aca03d284e03d284a03d282203d281603d22cc03d124603d1049a3d103993d103173d10290))) else (if c < 540 then (if c < 539 then 0x3d700c63d684803d680843d604403d603403d600c63d580873d500c13d483003d404c03d404403d3ad403d3ad003d345403d345003d2c4a0 else 0x3db02553db024a3db01603db01523db01493db00e03da854a3da81c43da80cb3da0d003da09813da01813d900c43d802c03d781803d78080) else (if c < 541 then 0x3db83c03db83443db82c03db81403db3ce03db3cd03db3cc03db3c503db34e03db1ce03db04603db03603db02e03db02d53db02c83db0260 else (if c < 542 then 0x3dd05043dd01c83dd00c63dcad003dcac403dc85483dc85003dc81c13dc80c53dc45403dc0d403dc03483dc02c83dc01c93dbc5403db84c0 else 0x3df04603df03d03df03503df02d63df01523df00e13de85003de81813de44c03de05443de05043de00c63dd85403dd85073dd80c13dd0547)))) else (if c < 548 then (if c < 545 then (if c < 544 then 0x3e284803e283003e204453e183023e102843e084993e0839b3e0831b3e082a23e082923e082823e081143e004c93dfc5403df44d03df04d2 else 0x3e584c43e582c13e580c53e504803e500803e484c03e484413e483413e482ca3e480c63e400803e384c23e382c83e380c63e305473e30286) else (if c < 546 then 0x3e984a03e981233e981133e981033e904c63e900c73e882803e802863e783943e782a13e782913e782813e780a03e682813e601843e60080 else (if c < 547 then 0x3ea8b403ea8ac63ea89c03ea894a3ea81853ea01863e9c4a43e9bce03e9bca03e9b4e03e9b4a63e9ace03e9aca33e9a4e03e9a4a73e99ca6 else 0x3eb34e03eb34a93eb2ce43eb2ca73eb24e73eb24a03eb1ce03eb1ca93eb04e93eb04a33eb01613eb00e53eaa4c03ea8d0a3ea8c463ea8bc3))) else (if c < 550 then (if c < 549 then 0x3ec84a43ec80a33ec80933ec80833ec24c03ec0d413ec0d033ec0c413ec0bc13ec0b413ec0ac13ec09c03eb85003eb44ab3eb3ce93eb3ca4 else 0x3ed8bc03ed8b493ed8ac43ed81033ed00863ecc4a43ecbce03ecbca73ecb4e03ecb4a63ecace03ecaca63eca4e03eca4a03ec9ca33ec9c66) else (if c < 551 then 0x3ee44aa3ee3ce83ee3ca03ee34e03ee34a73ee2ce03ee2ca93ee24e43ee24a73ee24603ee04ea3ee04a43ee01ea3eda4c03ed8d033ed8c40 else (if c < 552 then 0x3efa4e03efa4a93efa4543ef84e33ef84a73ef81e13ef2cc03ef0d483ef0d0a3ef0c483ef0bc83ef0b483eead4b3eead003ee85483ee8500 else 0x3f0acc03f08d483f08d0a3f08c483f08bc83f0354a3f035043f005403f005043efc4ab3efbce63efbca43efb4e33efb4a73eface63efaca0))))))) else (if c < 592 then (if c < 572 then (if c < 562 then (if c < 557 then (if c < 555 then (if c < 554 then 0x3f1bd463f1bd073f185403f185073f144ab3f13ce63f13ca43f134e43f134a73f12ce83f12ca03f124e03f124a93f124543f104e63f104a7 else 0x3f2c4aa3f2bce03f2bca73f2b4e43f2b4a73f2ace83f2aca03f2a4e03f2a4a93f284e73f284a43f280ea3f22cc03f20d483f20d0a3f20c48) else (if c < 556 then 0x3f4034a3f402e03f402d33f402c03f401e03f401603f4015a3f401403f400e03f3acc03f38d483f38d0a3f345493f345003f305483f30500 else 0x3f503ca3f5034a3f501c83f484493f483c93f483493f482c73f481493f404603f404553f404443f403e03f403d43f403c53f403603f40350)) else (if c < 559 then (if c < 558 then 0x3f73ca53f734e93f734a93f72ce03f72ca03f704e03f704a03f6ad403f584103f583993f583173f582903f581133f52d403f504ca3f50448 else 0x3fa84403fa83493fa80c63fa02803fa00803f980c83f903003f885403f884c03f884493f82d403f82d003f7cd003f744e03f744a03f73ce0) else (if c < 560 then 0x3ffacc03ff85473ff85003ff81c13fe854b3fe81c03fe80ca3fd82c03fd00803fc82c93fc80c83fc01803fc008a3fb80c03fb04803fb0083 else (if c < 561 then 0x40183d0401835040182db40181524010544401050040100c3400bd434008540400850940080c54000547400050440001c240000c63ffad00 else 0x4068446406834b40682ca40680c04060080405854040580c6405350040502864048506404830040404ca4040448403830040302804018452)))) else (if c < 567 then (if c < 564 then (if c < 563 then 0x40a8b5040a8b1740a8ad640a8a9040a89d740a895a40a8917409008040880c24080180408008040782ca40780c0407048040700894068547 else 0x40b83c740b834740b824740b814740b0cc940b0c4940a8cda40a8c9040a8c6040a8c5640a8c4340a8c1a40a8be040a8bd340a8bc640a8b90) else (if c < 565 then 0x40d814040d0cc740d0c4740c8cca40c8c4a40c049440c041740c039040c031b40c029040b8cc040b8c4040b89c040b854740b84c740b8447 else (if c < 566 then 0x40e049440e045240e041240e03db40e039340e031740e011940d8cc040d8c4040d8b4040d854040d84c040d844040d83c040d824040d81c0 else 0x40f829040f811b40f0cc040f0c4040f0bc040f054940f04c940f044940f034940f024940f01c940f014940e8cc640e8c4640e2cd540e04d4))) else (if c < 569 then (if c < 568 then 0x411023b41101f041101bb4110170411013441100f041100bb4108cc04108c4041084c041081404100cc04100c4040f849040f841040f8397 else 0x4118294411811a4113c794113c344112c784112c354112bf04112bb04110470411043941103f041103b44110370411033341102f041102b1) else (if c < 570 then 0x4120c904120c604120c554120c434120c1a411bcd5411bc92411bc55411bc1a411abe5411aba341184d041184924118450411841a4118317 else (if c < 571 then 0x4138370413833441382f041382b8413823141381f041381b94138170413813341380f041380bb4130cc0413044a413014a4128cc04120cda else 0x41404d44140494414039b414031b41402924140119413bc70413bc32413ac72413ac3a413abf0413abb04138470413843b41383f041383b4))))) else (if c < 582 then (if c < 577 then (if c < 574 then (if c < 573 then 0x4158d4041584c0415844041583c04158340415824041581c041581404148cda4148c9041444d141444944143c614143c2b4142c614142c22 else 0x41982804198080419354041900c1418808041834c041800c54178080417344041700c94162ce241604104160390416031a41602904160119) else (if c < 575 then 0x41c808a41c4d4041c00c441b808041b454041b04c041b03c041b034041b02c041b024041b01c041b014041b00ca41a808741a44c041a00c0 else (if c < 576 then 0x41fbd0941f44e641f44ab41f3ce641f3ca441f34e441f34a741f2ce841f2ca041f24e041eb50441e2d0041da54b41d254041d0c4341d0bc6 else 0x4224d0a421ad404214500420c4e7420c4aa420bce0420bca7420b4e4420b4a7420ace8420aca0420a4e042081a442080ea4202d404200c49))) else (if c < 579 then (if c < 578 then 0x42a03004298b0042989c042904d0429045042903d8429035b42902d142802c042702c0426818042602c0425848042402c0423830042282a0 else 0x42ab3b042a847042a843842a83f042a83b042a837042a833742a82f042a82ba42a827042a81f042a81e142a817042a813542a80f042a0b00) else (if c < 580 then 0x42b2bd042b2b9042b04da42b049842b045642b041042b03d042b039742b035742b01e142b015242abc7042abc3342ab47042ab43a42ab3f0 else (if c < 581 then 0x42d02d542d015a42c0b4042b8cd042b8c9a42b8c5042b8c1042b8bd042b8b9942b8b5042b8b1742b826142b2cd042b2c9242b2c5042b2c10 else 0x42f830042f818342f0c4042e84d042e849042e845542e841742e835042e82d442e815942e048042e030042d8bc042d04d842d045642d03d0)))) else (if c < 587 then (if c < 584 then (if c < 583 then 0x43283004320d40431845143183da431835743182d0431815643103004308cc043044d043004db430049643003d0430035943002d04300153 else 0x436014543600c043580804353540435024643500ca434808043434c043402c84340241434014543400c643380804333440433024143300c0) else (if c < 585 then 0x4384d40438014643800c44378080437454043704ca43703ca437034a43702c7437024143701ca437014043700ca436808043644c043602c8 else (if c < 586 then 0x43f018343d828743ccd4043c454043bbd4043b354043a2d40439c4e0439c4aa439bce0439bca4439b4e0439b4a7439ace043981e14388080 else 0x4438d0644381064430089442c4e0442bca7442b4a6442a4a044284a044280a644280964428086442050044181894410287440028643f0289))) else (if c < 589 then (if c < 588 then 0x4468500446054a446044a446034a446024544601c1446014a44600c0445854044585004450540445050044500c544485094440509443abc0 else 0x4488413448831744882194488112448344044803c1447834744704d24470451447036044703544470341447025044701e0447015a4468542) else (if c < 590 then 0x44d80c444d018244c834044b844244b354244b350044abd4044abd0744a44e244a44aa44a3ce244a3ca444a04e044a04a0449b440448849a else (if c < 591 then 0x45301c1452854645285004520548452050045200c1451854745181c8451054745100c8450054245001c345000c944f008044e80c044e008a else 0x455831945582174558122455811245581024542cd045404d24540456454035445402504540150453854245385004532cc045305424530500)))))) else (if c < 612 then (if c < 602 then (if c < 597 then (if c < 594 then (if c < 593 then 0x45b811145b810145b008045a834645a80c045a0080459844845980c445903024590182458040b457038445681824560102455849a4558416 else 0x45e80c745e3d4645e054045e050045d850045d050045cac4045c8d0745c89c845c818145c018445bbca045ba4a745ba3e445b84a045b8121) else (if c < 595 then 0x45f84da45f84c045f83e045f83d045f83c645f826445f825045f824845f816045f815245f814745f80e845f050045e854445e850445e8142 else (if c < 596 then 0x46284a046234c04610498461039146102104610114460b4c04608540460844646082c846081c746004c046003c04600244460014045f84e0 else 0x4678507467054646700c2466854246680c946580c04650184465008046480c146384c846345484634500462c4aa462bce6462bca746284e6))) else (if c < 599 then (if c < 598 then 0x46d818246d808046d00c146c848a46a849846a839146a821046a811446904d646903d0469025046901504688500468054346805004678540 else 0x4712cc44710500470acc04708d044708100470008b46fc4a046fb4e046fa4a446f84a446f80a546f809546f808546f050046e818b46e00c4) else (if c < 600 then 0x474821b474811447435404732cd0473045847303d34730350473025547301e04730154472c50047285484728500472054747205004718500 else (if c < 601 then 0x479008047880ca477854047735404773500476cd0047644e047644a04763ce04763ca047604e047604a0475b540474841a474839b4748310 else 0x47d01ca47cad0047c854647c844647c83c647c834647c81c747c814647c80c247b854b47b81ca47b80c047a834047a008047980c64790180)))) else (if c < 607 then (if c < 604 then (if c < 603 then 0x480021a480020a480011047e845647e83d047e835447e825047e815247e054847e050047e00c147dbd4747d854047d850747d81c147d0541 else 0x484030748401874840080483834448380ca483050048183d0481835448182d0481826148181d04810283480ad004808207480039a480022a) else (if c < 605 then 0x4878317487821b4870a4048709c0487054348704c3487044348703c348702c3487024248701404868a4148503094850080484854048480c6 else (if c < 606 then 0x48a01c948a01414890cd04890c924890c504890c174890bd44890b964890b504890b184890a504890a134880a414878494487841b4878392 else 0x48c021448c011148b8bc048b844248b824348a849a48a841048a839048a831048a811348a0ac048a054948a04c948a044948a03c948a0248))) else (if c < 609 then (if c < 608 then 0x48e824148e81c048e814848dbc9a48d84d748d849a48d841348d831048d821048d811248d0c4048d03c748d024648c049348c041048c0394 else 0x49083924908317490821349081194900d40490024248f049948f039b48f031a48f021048f011448e8cc048e854048e844048e83c048e82c0) else (if c < 610 then 0x4954500494bd074942d404932d40492ad404920080491c54049184ca49183ca491834a49182ca491824b49181ca491814949180c04908413 else (if c < 611 then 0x49c03d049c03c149c035049c015149c00e049b09c049a84d049a845149a83d249a835449a825b499834a498018249783474960297495cd0a else 0x49f015749e848249e0bc049d84d449d845249d83d149d825b49d815449c8ac049c84c549c844549c04db49c046049c045149c044049c03e0))))) else (if c < 622 then (if c < 617 then (if c < 614 then (if c < 613 then 0x4a203574a202564a201574a10cc04a084d94a083db4a083574a082504a081544a0018449f8c4049f04d049f049249f045b49f035449f0250 else 0x4a504474a503c74a400804a3c5404a384c94a383c34a383484a382c94a382414a381c24a381404a380c74a3028b4a28d404a204514a203d2) else (if c < 615 then 0x4ab09c64ab09444ab01824aa81884aa44a04aa34a84aa04a04aa01224aa01124aa01024a983004a803024a801824a74d404a6c5484a63d47 else (if c < 616 then 0x4abc4aa4abb4e04abb4d04abb4c04abb4a74abb4604ab84e74ab84a04ab80e14ab3d404ab3cc04ab0d084ab0c404ab0b404ab0ac04ab0a40 else 0x4ad34e34ad34d04ad34c64ad34a74ad34504ad04e34ad04a74ad00eb4acbd404acbcc04ac8d454ac8d024ac8ac54ac8a454ac3d424ac0500))) else (if c < 619 then (if c < 618 then 0x4aec4aa4aeb4e04aeb4a74ae84e74ae84a44ae81ea4ae3d404ae3cc04ae0d474ae0d084ae0c454ae0b454ae0ac54adbd434ad85094ad44ab else 0x4b002e44b002d24b002c44b002644b002504b0024a4b001604b0015a4b001404b000e44afbd404afbcc04af8d4a4af8d024af8c454af0500) else (if c < 620 then 0x4b445024b3cd004b304e04b304a04b2c5404b182934b182174b181124b145404b103434b102c24b101c24b0bd404b082c94b082494b08147 else (if c < 621 then 0x4b901504b885484b881c14b805474b800c84b785424b782c84b780c94b684404b601804b581804b501a04b501904b501804b485424b44540 else 0x4bf04c44bf01404be049a4be02924be02164bd89c04bd85474bd83494bd82c94bd81494bc050a4bc01824bb018a4ba81024b902d84b90250)))) else (if c < 627 then (if c < 624 then (if c < 623 then 0x4c201c04c201444c104994c1041a4c103104c1021b4c101144c08b404c083c04c082404bf84904bf84104bf83174bf82904bf811b4bf0ac0 else 0x4c801e04c801b84c800f14c800e04c704404c681804c581a04c54d0a4c43d404c3bd464c2829a4c282104c2811a4c20d404c203444c202c4) else (if c < 625 then 0x4c884d04c884c24c882e14c882d04c882c14c882604c882514c882404c880e04c804704c804604c804344c802704c802614c802304c801f1 else (if c < 626 then 0x4c989c04c985424c983484c982c04c90cd04c90c904c90ad04c90a904c90a514c90a154c904e04c903e04c902e14c902604c901604c884e0 else 0x4cd81564cd01824cc8b404cc04d74cc045b4cc03544cc02524cc01504cb830a4cb81834cb0ac04ca84da4ca84554ca83504ca82d34ca815a))) else (if c < 629 then (if c < 628 then 0x4d401484d284074d1cd404cf84c24cf82c84cf82484cf44e04cf44a04cf04604cf02614cf01e04cf00e04ce81824ce0d404cd82d04cd8256 else 0x4d601194d58ac04d584c34d584424d583c24d583424d582424d581c24d581434d483904d4829b4d482194d409c04d404484d403494d402c8) else (if c < 630 then 0x4d88c404d883434d882c24d881c24d881424d784134d783924d783144d782124d781144d70b404d702484d604104d6039a4d603154d60290 else (if c < 631 then 0x4df8b404df03da4df025a4df01504de84024de09c04de03414dd83d24dd82e14dd82d04dd82c14dd825b4da4d404d902934d902174d90112 else 0x4e104474e103c74e082c84e0028a))))))))))
def rec4 (i : Nat) : Nat := (rec4C (i / 16) >>> ((i % 16) * 28)) &&& 268435455
def hint7C (c : Nat) : Nat := (if c < 6 then (if c < 3 then (if c < 1 then 0x31028091086090087014004072060050048030027016006 else (if c < 2 then 0x1000005204109808507006203202b09208a038021013003 else 0x9708003702007b06603b02207806409408905404009b083)) else (if c < 4 then 0x7106309908409a0820b10a10b00a009308b011001096081 else (if c < 5 then 0x1241171071090f70e00db0c609508807706a0b80a8012002 else 0xe40d10c31f01e61d41cb1b61a019718417416015014013b))) else (if c < 9 then (if c < 7 then 0x2b02a029228227026623422525024221420b23022a210201 else (if c < 8 then 0x2d02c71f41e31641541a41991441311201d01c11b3180170 else 0x3b03a033032b3903803793693503483343213103002f02e0)) else (if c < 10 then 0x3773673543422d42c93143044304234104003f03e23d03c0 else (if c < 11 then 0x4344264144043f43e849048047746745044a3b43a4394384 else 0x4d04c24ba4aa))))
def hint7 (i : Nat) : Nat := (hint7C (i / 16) >>> ((i % 16) * 12)) &&& 4095
def hoff7C (_ : Nat) : Nat := 0x4800
def hoff7 (i : Nat) : Nat := (hoff7C (i / 16) >>> ((i % 16) * 8)) &&& 255
def hint6C (c : Nat) : Nat := (if c < 171 then (if c < 85 then (if c < 42 then (if c < 21 then (if c < 10 then (if c < 5 then (if c < 2 then (if c < 1 then 0xfb00e400d700c700b000a90090008a00780068005000490038002900140004 else 0x13001200119010000f600e700d400c400590040003a00200017000601100109) else (if c < 3 then 0x1c001b101a001990190018000b900a000990088007a006a017001600150014b else (if c < 4 then 0x28002790220021002890270026902500249023102290218020001f901e001d9 else 0x2e002d002c002ba02a0029001e901d002600259020901f001c901b302400233))) else (if c < 7 then (if c < 6 then 0x3c003b003a003970389037603490336036003500340033b03200310030002f5 else 0x40903f902a9029b0329031902c902b80380037b040003f003e003d0030902f2) else (if c < 8 then 0x4c004bb04a004900480047004690459044004380428041803a9039403690359 else (if c < 9 then 0x489047904600450050004f004e004d004c904b604a904990449043b042a041a else 0x5b905a3059105880228057005670550054905360522051101a0019901900180)))) else (if c < 15 then (if c < 12 then (if c < 11 then 0x5790564053b0525051305b005a1059305f005e90580022a05f905e005d905c0 else 0x6a3069b06800678066006550648063b0620061a060002a60559054005d005c9) else (if c < 13 then 0x75007400730072006690652071003c4070006f706e906d606a1069606c006b0 else (if c < 14 then 0x76a000a070906f406c906b907590749060b02ab0689067a0629061806e006db else 0x810080007b407a4079a006a07f007e307da07ca07b007a00795006507800771))) else (if c < 18 then (if c < 16 then 0x8a0089008940880051001b0087008620850084007f407e607d507c508300820 else (if c < 17 then 0x9600950051401b40940093009240910090008f005e0027008e008d008c008b4 else 0x8c408b00920091405e4027409c009b00984097409a009900964095409800970)) else (if c < 19 then 0x69003300a440a300a200a140a0009f009e009d00944093408e408d4090408f4 else (if c < 20 then 0xa640a540694033409e409d40a240a100aa00a900a800a700a600a500a400a34 else 0xb600b530b400b300b2004700b190b090af004300ae20ad20aa40a940ac00ab0))))) else (if c < 31 then (if c < 26 then (if c < 23 then (if c < 22 then 0xbe00bd20bca0bba0b640b560b440b340ba00b900b870b770b2404740b170b07 else 0xc500c4705f402840c300c200c100c0b0bf408a70897089908870530052b01c6) else (if c < 24 then 0xce00cd20ca4096b0cc00cba0ca009610534052101c30c9009460c840c7b0c66 else (if c < 25 then 0xc340c240c540c490c140c010bf00c800c710c6305f002800d000cf60cc40cb5 else 0xd900d800d700d6b06a003480d740d610d500d400d300a000d200d170c940943))) else (if c < 28 then (if c < 27 then 0xdd40dc80df00dea0d940d8406a403420d240d190d540d440dd00dc20db00da0 else 0xe2a0e1a0e0700670e600e510e400e300e220e120e0000600e200e100e020062) else (if c < 29 then 0xe270e170e0a006a0ec00eb20ea00e9b0e800e700ec20eb00ea20e940e820e72 else (if c < 30 then 0xf370f240f320f2b054201d20f100f020ef00ee20ee00ed00bf208ba054701d7 else 0xfb00fa00f900f870f720f600cf209b80f500f460bf008b7063002d60bf708b0)))) else (if c < 36 then (if c < 33 then (if c < 32 then 0xbfa08b20f120f000cf009b10f700f620f920f8a0fb20fa20f520f45054a01da else 0xf9a0f820f570f410fd00fc00fd20fc20f5a0f48054001d00f300f290f3a0f23) else (if c < 34 then 0x1019100910260476101510050f970f800f7a0f670ff00fe0063702d10f770f6a else (if c < 35 then 0x10c010b010a41094102704771014100410801070106010501040103010200470 else 0xee40ee80ed80c100c0b08c7055601e6102104711018100810c110b110a81098))) else (if c < 39 then (if c < 37 then 0x8c1064002e30c110c0a08c61111110611101107055701e710f010eb10d00ef8 else (if c < 38 then 0x11301123055001e011810fb111761165115011480d0209cb1136112a0c160c02 else 0x111711000c170c0308c010f610e210d60d0b09c2115611441170116911800fb0)) else (if c < 40 then 0x11511149117711641131112211a1119111a011901137112b055101e111161101 else (if c < 41 then 0x122207c21211120011f611e711d100c1117111681157114511c011b0064102e2 else 0x1210120111f711e611d000c012b012a01296128212740e381260125112401231)))))) else (if c < 63 then (if c < 52 then (if c < 47 then (if c < 44 then (if c < 43 then 0x12411230122307c31311130012f112e212d112c11310130112f012e312d012c0 else 0x13701367056001f4135013401330132010d00f040c2008d7056101f512611250) else (if c < 45 then 0x13d113c513b013a10cd0099b1391138a0d1109d1067003130c2108d613711366 else (if c < 46 then 0x14500de00ab2144014301420141911400f60140013f013e306b0035011410f61 else 0x14b114a114b014a01390138b06b1035114911481149014800d1009d014701460))) else (if c < 49 then (if c < 48 then 0x14e0142114181441143114d014c00671031213b113a013d013c4140113f113e2 else 0x157a150404b414f414e415601072155a154a15340b5415231513150004b014f0) else (if c < 50 then 0xf110c3208ea0575020515300b501526151615a415981585157515a01592158a else (if c < 51 then 0x68403240c3808e515c815b515c215ba057a020a135213421332132210f210e7 else 0x163406c2036211500f7416211616160013b00ce009a715f015e115d70d2509e8)))) else (if c < 57 then (if c < 54 then (if c < 53 then 0x169816aa16920d2a09e21680147a0df70ac0167414431663165b11540f701649 else 0x160813b4162b16131647163016c416b416c016b015f415eb15d906c8036816a5) else (if c < 55 then 0x17401739172008001710170816f500c5166616511670144616e016d106800320 else (if c < 56 then 0x1810180617f017e017d017c417b0012017a0179a178712c71770176017540e74 else 0x1860185005c0025015b0136011000f200c4008f00590023018401838182407c4))) else (if c < 60 then (if c < 58 then 0x15d013800cb0097218c018b00d600a36065002f00c60091118a0189018801870 else (if c < 59 then 0xdc00a9a165014101920191011600f80190018f006f0039011200f4018e018d8 else 0x19b019a019901980197018d006d0037019601950194019300d400a1916901480)) else (if c < 61 then 0x1a481a381a2018f5163013e01a101a00061002b0161013c019f019e019d019c0 else (if c < 62 then 0x1b041af41ae015901ad21ac21ab010b01aa41a941a800b901a791a691a5004b0 else 0xf340c50090705b505aa02451b800b571b751b651b501b441b381b281b1004f4))))) else (if c < 74 then (if c < 68 then (if c < 65 then (if c < 64 then 0x66303030c850c7a09281b9018a6188718771867185705d4026415c013701110 else 0x1a23070003a011350f511bb8197515f015e113980cc2098a1ba018ca0d780a45) else (if c < 66 then 0x1bf01be119400d570a2016a014970dda0aa2166014241bd0192911740f901bc0 else (if c < 67 then 0x1c801c7119f41c6019d21c501c411c301c211c101bb018eb06e803881c001961 else 0x12c21cd01cc01cb012c01bc519081640140513f51ca01c94062202c2162013d9))) else (if c < 71 then (if c < 69 then 0x1d101d021cf31ce417e41cd71cc71cb712c71d001cf41ce317e31cd21cc21cb2 else (if c < 70 then 0x3f716b214a011900fc40d800a57072603d61cda1cca1cba12ca1d401d311d20 else 0x14a20d820a5a1c12198a0da80a71074a03fa0da10a781c4019a61c1019870747)) else (if c < 72 then 0xa5216d214c41c901a0911b40fe01c9a1a03074003f011920fcb1c4219a516b0 else (if c < 73 then 0x1d621d601d501c921a0b072103d11c4719a11c1719800d870a5016ba14a70d8a else 0x19a816b714aa1d901d80074203f216d014c31c971a041c1a19821d921d821d70)))) else (if c < 79 then (if c < 76 then (if c < 75 then 0x15971db71da71df01b401de41dd41dc215921db21da21dc015901db01da01c4a else 0xa67073603e61dca159a1dba1daa1e301e201e111e011df21b421de31dd31dc7) else (if c < 77 then 0x75a040a0db10a881c5119b61c301c2119970757040716c214b011a00fd40d90 else (if c < 78 then 0x1a130750040011a20fdb1c5819b516c014b20d920a6a1c321c28199a0db80a81 else 0x1c371c2619900d970a6016ca14b70d9a0a6216e814d41ca41a1911c40ff01cab))) else (if c < 82 then (if c < 80 then 0x1a141c3a1c2519921e421d9b1d701d621d601d501ca31a1b073103e11c5619b1 else (if c < 81 then 0x1e981e891e781e691e541c5519b816c714ba1e401d940752040216e114d31ca9 else 0x1f901f801f761f661f541f401f3a1f261f161f001ef61ee81ed71ec91eb01ea8)) else (if c < 83 then 0x20992080207020612051204120392020201020001ff91fe81fda1fc01fb81fa6 else (if c < 84 then 0x219021892170216021502141213921292110210020f020e020d920c920b020a0 else 0x229022822270226422502247223022272210220021fb21e021d121c121b121a1))))))) else (if c < 128 then (if c < 106 then (if c < 95 then (if c < 90 then (if c < 87 then (if c < 86 then 0x2359234623342323231b230422f3209421e022e422d41e64002422c022b222a0 else 0x2446243621e024292419240923f923e423d023c023bb23a42399238923702360) else (if c < 88 then 0x2546253125202512250024f924e024d024c424b624a024932484247024632457 else (if c < 89 then 0x2644263926202610260425f425e725d025c025b625a325932580257a25642555 else 0x2744273627242714270026f026e026d826c026b026a026972684267126602657))) else (if c < 92 then (if c < 91 then 0x283328202810280027f50af027e427d427c427b027a427902780277027632750 else 0x20352026201604460af0043028b01e70003028a0289628842876286028542844) else (if c < 93 then 0x230529aa2998298b2976296b2957294b2937292b2910290b28f828e728d928c7 else (if c < 94 then 0x2a862a772a652a572a462a302a262a192a0529f5044629e829d829c8238029b0 else 0x2b252b502b402b142b0a2b302b2a2b102b052af02aea2ada2ac62ab52aa62a94)))) else (if c < 100 then (if c < 97 then (if c < 96 then 0x2c002bf02be02bb42ba42bd02bc02b942b842bb02ba02b902b802b702b602b34 else 0x2ce02c902c842cd02cc42cb02ca02c942c802c702c642c502c402c302c202c10) else (if c < 98 then 0x2ce42cd42cc02cb42ca42c342c242c742c602d502d402d302d202d102d002cf0 else (if c < 99 then 0x2e042dfa2de02dd12dc52db02da02d542d442d342d242d902d802d702d602cf4 else 0x28e028c0206020402ec02eb02ea02e962e8a2e702e602e502e452e302e252e14))) else (if c < 103 then (if c < 101 then 0x2fc02fb02fa02f902f802f702f602f502f402f302f202f162f002ef02ee02ed4 else (if c < 102 then 0x30c030b030a030903080307030603050304430343020301430002ff02fe02fd0 else 0x31c031b431a0319431803170316031503140313431203110310130f130e030d0)) else (if c < 104 then 0x32c032b032a0329432803270326032503240323032203210320031f031e031d0 else (if c < 105 then 0x33c033b033a0339033803370336033503340333033203310330032f432e032d0 else 0x28d4205034523440341934053437342033f433ea3417340a33f033e533d71e5a))))) else (if c < 117 then (if c < 111 then (if c < 108 then (if c < 107 then 0x3530352028d020543514350034f434e034d434c034b434a03494348034743464 else 0x3570356035503544351035043490348434d034c43470346034f034e434b034a4) else (if c < 109 then 0x3617360a35f435e035d033e235c21e9035b035a0357435643590358035543540 else (if c < 110 then 0x36d736c030473467303728f236ba36a736903680367436623650364036303620 else 0x37c037b037a7379037803772376037503747373a372a37103702248a36f736e0))) else (if c < 114 then (if c < 112 then 0x38b038a13890388038703860385638463836382638102200380b37f237ea37d2 else (if c < 113 then 0x396b2a04249920d43860395439443934008439203913390038f038e338d038c6 else 0x3a663a563a403a393a243a103a0039fb39e439d939c739b039a9399439833974)) else (if c < 115 then 0x3b513b403b373b283b103b073af03ae03ad43ac63ab03aa337343a903a833a77 else (if c < 116 then 0x3c443c373c2038603c163c063bf63be63bd33bc33bb03baa3b943b853b763b60 else 0x3d403d383d203d103d003cf73ce43cd13cc03cb03ca73c943c893c703c603c54)))) else (if c < 122 then (if c < 119 then (if c < 118 then 0x3e3928003e253e103e003df43de03dd03dc03db33da03d963d843d743d603d50 else 0x903f103f083ef43ee83ed03ec43eb03ea43e903e803e703e600b203e593e49) else (if c < 120 then 0x3f673f5b3f4036e436d936c4306734793057290b207610200b2004703f303f20 else (if c < 121 then 0x40293b7440143ab140013ff03fe8398424a13fdb3fc83fbb3fa63f9b3f873f7b else 0x410040f01ed140e640d540c640b440a040974080407740604050102040494039))) else (if c < 125 then (if c < 123 then 0x41e041d041c041b041a44190418041704160415435e441414130412134024110 else (if c < 124 then 0x429042803f4030c7348730b729104270426142504243423042244210420141f0 else 0x437043604350434943303ae143204311430142f042e824d142d042c042b442a0)) else (if c < 126 then 0x4464445444442820443244204411440043f043e043d743c043b743a043904380 else (if c < 127 then 0xb600b5345104500183044f044e544d044c444b044a0449044833e9044770b60 else 0x3af1456145504542453424e1452b42a0429042803f5b30e7349930d7292b1533)))))) else (if c < 149 then (if c < 138 then (if c < 133 then (if c < 130 then (if c < 129 then 0x1f144642463546234614460045f745e445d7153345c045b045a0459445804579 else 0x46f046e046d446c0418446b046a94690360a46893f20393a33e8467046684650) else (if c < 131 then 0x3f692fc934a92fb9293947a0479a478047774760475047444737472047104700 else (if c < 132 then 0x4870486948594840483048203a594819480047f0243947e947d047c947b042b0 else 0x449449203eb449100b20490948f948e9284048d8219948c048b048a048904889))) else (if c < 135 then (if c < 134 then 0x2fe934b72fd9294104800b200470499435d40e144980497a4960495049404930 else 0x4a144a0449f049e73a6949d949c049b82324244929a149a147d047c947b03f71) else (if c < 136 then 0x36294ac934204ab91f552ac94aaa4a904a804a704a6904804a594a494a394a29 else (if c < 137 then 0x4b504b403f80308034c0307029504b384b244b194b004af446f94ae741c74ad0 else 0x4c304c204c104c004bf04be04bd04bc04bb03ac04ba04b904b8024b04b704b60)))) else (if c < 143 then (if c < 140 then (if c < 139 then 0x4ce049444cd444b04cc03ed04cb40ba04ca94c994c8928604c784c604c504c40 else 0x4b574b473f9b30a734d93097296b1a800ba00b904d204ac017304d104d054cf4) else (if c < 141 then 0x4df04de04dd04dc04db04da94d903ad54d854d704d684d5024c54d4a4d3b4b67 else (if c < 142 then 0x3664450834044ea41f904e904e854e704e641a804e574e474e374e254e144e07 else 0x4f204f103fa0300134e12ff129704f094ef04ee64b014ed847354ec642074eb0))) else (if c < 146 then (if c < 144 then 0x50004ff04fe04fd04fc04fb04fa04f904f804f703a704f604f504f4024504f30 else (if c < 145 then 0x50d650c050b750a038f0509b5080507150615051504150302290502b4c605010 else 0x51745163515b29f4246920c45080514051304120123051205113510050f450e0)) else (if c < 147 then 0x52434f6749d64816523052295214520051f051e451db51c451b951a751905189 else (if c < 148 then 0x52c552b652a152905288527052674560431043004d844ba640003a8937245250 else 0x53c953b053a4539053845374536753505340533653235313530052f452ea52d4))))) else (if c < 160 then (if c < 154 then (if c < 151 then (if c < 150 then 0x54c454b054a0549054805478546054505440543454275414540153f053e753d4 else 0x55a055902880558a55705564508055505540553055205510550354f054e654d4) else (if c < 152 then 0xb53562041301240561056024cf055f0496055e744d455d43ef055ca0b6055b0 else (if c < 153 then 0x4f134d314b7949a147e9452142c43fb136f7302934f73017298120831b8b0b60 else 0x56b456a456945687567443203a9b525b566b56525644247b4d4156324f334f23))) else (if c < 157 then (if c < 155 then 0x5778344157641fda4e9b575a1b8b574057305720571b570756f056e956d456cb else (if c < 156 then 0x56343fc43100350130f0299457c84ef057b64b2557a847755796424a578036a5 else 0x586458505840583058205810580057f03b00526057e057d424f4312035143110)) else (if c < 158 then 0x4984590944f058f13f1058e80be058d458c458b428a058a635b0589458805870 else (if c < 159 then 0x42d03fdb31273519311729aa0be10be00bd2577157700860561459264d105915 else 0x58f052703f1158e93b115271498559083b1025013126351831164d4b4d4a29ab)))) else (if c < 165 then (if c < 162 then (if c < 161 then 0x59545940593a1e950be158c558d558b54d1159145615592728a158a7250044f1 else 0x5a455a355a245a1a5a0559f059e159d559c859b159a1599a5980597159601f15) else (if c < 163 then 0x5aa45a942ee42f202b902360515439642f102ed62b8623145a805a715a615a55 else (if c < 164 then 0x220b5b755b605b545b405b305b245b145b005af45ae05ad05ac05ab039b05190 else 0x5c505c405c305c215c145c015bf05be85bd05bc95bb05ba628405b945b882800))) else (if c < 168 then (if c < 166 then 0x2b9123882384237151683984398839732f272ee92b9723285c765c705c605c56 else (if c < 167 then 0x5bb65ba028065b8422025b79516439c651a6232428465b9839c051a02ee52f21 else 0x5cd05cc45cb51f995ca05c9a5c841ed55bd85bc55bf65be45c185c075c365c27)) else (if c < 169 then 0x5db05daa5d9a5d895d795d695d505d495d3b5d205d1a5d075cf959f45ce85994 else (if c < 170 then 0x5e205e1039f051d05e005df05de05dd05dc023b0517039902f522ef32ba22330 else 0x5ef1288022915ee328205ed15ec05eb05ea05e905e805e705e605e505e405e30)))))))) else (if c < 257 then (if c < 214 then (if c < 192 then (if c < 181 then (if c < 176 then (if c < 173 then (if c < 172 then 0x5fd25fc05fb35fa05f905f805f705f635f505f445f305f205c105f1b5bb05f06 else 0x5ff25fe25dea5dda5dca51a023c15182453439a22f672f092bb729b023522349) else (if c < 174 then 0x60b760a460976082607460686050604460346020601960073a01564451f151e5 else (if c < 175 then 0x6151614359d36131612361181f506130612261191f51610260fa60e260d460c2 else 0x61c261b261a46190618361725d0161616150614259d26191618261735d006160))) else (if c < 178 then (if c < 177 then 0x62506240239151b039d02f3a2f3b2bcb2390623062226212620261f261e261d0 else 0x630062d062ca62b062f062e062d162cb62b139d151b162a06290628062706260) else (if c < 179 then 0x5bf463635f3063705bf0636628646354286063506340633062f162e16320631b else (if c < 180 then 0x4d5039ea2f472f492bd723aa63f063e063d063c063b063a06390638a5f346374 else 0x643764606450644064394d5439e551c564206412640062626252624223a551ca)))) else (if c < 186 then (if c < 183 then (if c < 182 then 0x64e264d71fd064f264e764d21fda64c264ba6464645464a06490648664776444 else 0x6550653a652865165d40654861a0650a5a176530652665185d4a65005a1264f7) else (if c < 184 then 0x65e065d065c265b023d752023a122f712f752be123d265a06598658865706560 else (if c < 185 then 0x667637f066626630662066506641661a660a663a662a661066003a17520765f0 else 0x66d05f746696639066c066b066a05c34668b5f7066935c30668128a4667328a0))) else (if c < 189 then (if c < 187 then 0x640039c439c023e53b10521a3a2a2f872f892bf723ea67226710670266f066e0 else (if c < 188 then 0x6782677767a26790678867793b143a255215676267526742673265d665c165b6 else 0x6804682168100032002720a5680640e267f03e0067ea67a8679467d267c767b0)) else (if c < 190 then 0x68b168a0689168845d64687168606855684468335a33682068110033002620a4 else (if c < 191 then 0x689068855d656910690068f268e468d261e2687068616854684568325a3268c0 else 0xae0352b29e129c1241023f020a569606950694069326924655468c168b068a1))))) else (if c < 203 then (if c < 197 then (if c < 194 then (if c < 193 then 0x241129c023f120a4590157d156514f454d614b8a49b047f3454042e13fe13701 else 0x47f26750673065e45fe15df66410629062705b905a975fe05df75b915a9629e0) else (if c < 195 then 0x69b269a0699269816971590057d0454142e04d604b8b3fe0370056504f4449b1 else (if c < 196 then 0x697069c069b36a606a506a406a306a206a1069e069d96a0169f169e169d869c1 else 0x1e731e6601c46a901e721e6701c56a616a516a806a706a216a116a0069f06980))) else (if c < 200 then (if c < 198 then 0x6b126b0261f26ac16ab46aa25a426af16ae26ad35d746ac06ab56aa35a436a91 else (if c < 199 then 0x3a302f9a2f9b2c0b29d1242024006b506b426b3265646af06ae36ad25d756b20 else 0x6b9a6bc06bb06ba16b9b3a3152216b806b706b6067406280242129d024015220)) else (if c < 201 then 0x6c136c605fb36c536c436c305c606c266c166c006bf06bc16bb16be06bdb6ba0 else (if c < 202 then 0x20b66cc067026cba6caa6c645fb66c566c466c9063d06c806c706c345c646c23 else 0x20b3498557e656614f564d704b9749c44804455042f03ff037140af035370446)))) else (if c < 208 then (if c < 205 then (if c < 204 then 0x4f5349c04800676265f65ff85e05642062a228435aaa5ff25e0a28465aa50443 else 0x6d316d276d106d076cf06ce06cd6498a57e3455442f44d744b993ff43710566b) else (if c < 206 then 0x6d526ce46cd36d296d146dca6db26da06d966d806d706d436d3b6d686d586d46 else (if c < 207 then 0x6e0463e06e105c746df35fc06e005c706df66dc56db86de06dda6d846d746d62 else 0x6e393a4152316b826b726b6221e1523b3a4b2fa72fa92c1721eb67106e2a5fc4))) else (if c < 211 then (if c < 209 then 0x59936ed06ec76eb335e96ea06e9a6e646e546e806e776e446e376e606e506e40 else (if c < 210 then 0x6fc16fb06fa76f976f806f716f606f576f426f316f276f1647306f006ef16ee7 else 0x31302c20251170907087707770647054704470307027701770016ff06fe96fd7)) else (if c < 212 then 0x70f070e070d470c070b070a03cf154216cd1697560002691528043373b2032b0 else (if c < 213 then 0x5bb071c83e9071b0634071a17191718071707160715071407130712071107100 else 0x72bb72a072907280727072607250724a723072247210720071f071e9496071db)))))) else (if c < 235 then (if c < 224 then (if c < 219 then (if c < 216 then (if c < 215 then 0x70a73d0156d4544154356ce0698826a1529b40143b4b3b3332c731492c37252b else 0x360564c6737a736b73547340733773247317730b72f072e472d072c970c770b7) else (if c < 217 then 0x73fa73c46f4573e073d073c06f4a73a073947385360a73b259b073a47390738a else (if c < 218 then 0x6cf06990253052a43b54315731592c4725347460745074407430742074107400 else 0x74d074a4749474c074b07484747474a0749074807470316031642c503b5052a0))) else (if c < 221 then (if c < 220 then 0x75306d0069aa71f475097520751071f075073eb474e05bd074f23eb074e45b60 else 0x6d0769a2254752b93b743b793b6b316731692c57254975677560755075477540) else (if c < 222 then 0x74e7254071f7750052b03eb774e9254452b4316031642c503b703b773b6152b7 else (if c < 223 then 0x6f8775b446f075a859d475907580757b36245bd774fa71f97504752775173eb9 else 0x31792c6925507670766076507649763976297610760575f475e075d973d075c0)))) else (if c < 229 then (if c < 226 then (if c < 225 then 0x76f076e076d076c076b076a0769076803cd054006d1069b0267052c03b803299 else 0x77a472107790494077895bf077783ed077695ec0775077407730772077107700) else (if c < 227 then 0x3b9a32a731892c77256a7847783078207819780977f977e077d577c477b07520 else (if c < 228 then 0x78707869785476a0769076804df43ce554156d2769c862b85164268552da4d90 else 0x795a366961077945793779247917790078f678e778d078c478b778a778907880))) else (if c < 232 then (if c < 230 then 0x7a0979f979e479d979c175e179b86f4479a16fc779914185798959f079707960 else (if c < 231 then 0x7a503c2053506d3069d025d052e03ba031f631962c8625707a407a317a217a19 else 0x38f17b325ec07b207b107b007af07ae07ad07ac07ab07aa07a907a807a707a60)) else (if c < 233 then 0x7bd07bc277c07bb071f07ba772347b9444907b807b707b605c107b5a7b413ef0 else (if c < 234 then 0x69e225e35674530152f53bb1320931a72c9725817c337c207c137c007bf07be0 else 0x7c9970f77c837c747c647c547c477a7b7a6b7a5b52b045943c3353634a006d43))))) else (if c < 246 then (if c < 240 then (if c < 237 then (if c < 236 then 0x7d635a187d507d497d3836aa61037d2a7d137d047cf97ce07cd47cc37cb77ca0 else 0x7e2376077e107e0a7df373f67de07dd37dc270047db97da87d99477b7d897d70) else (if c < 238 then 0x32db31bb2cab25907ed07ec37eb37eaa7e9a7e8a7e707e627e5379d07e407e33 else (if c < 239 then 0x7f697f597f407f307f207f107f007ef97ee03d1954596d5069f026b953103bc0 else 0x6d00800972507ff049807feb5c307fd13f107fc821907fb97fa07f907f807f7b))) else (if c < 243 then (if c < 241 then 0x53283bd832e731c92cb725a88078806067068054804480347bd4802877e08010 else (if c < 242 then 0x80c880b080a0809880897f087ef17ee87854254425043d2154616d686a0826c1 else 0x81775a378160815000990088374081402ac8813581288114810880f780e180d7)) else (if c < 244 then 0x82107620820081f081e9741781d081c681b0704081a00e17486068008190818a else (if c < 245 then 0x2a1020eb82d082ca82b07e8082a08290828b8274826a79fa825082408230822b else 0x57fb56804f7b4da04bb449e0482745704340404040203c003be037400b103540)))) else (if c < 251 then (if c < 248 then (if c < 247 then 0x48606770660b60905e52643062c05c205af860105e185b705ab32a50212858e0 else 0x74e0747972c070d058a0583145d043b04e004bf04070378956e04fb14a504a30) else (if c < 249 then 0x78b076f7833083258310830082f082e07c907ac680807f1a7c407a83786076b9 else (if c < 250 then 0x83ba5a4783a03f2939380bf78390838a837083608350834080d07f5673107140 else 0x84477e908430842784197a0a840083f983e9763083d0742783c9705035d70289))) else (if c < 254 then (if c < 252 then 0x846084503d3054704a406e306b9026d0533040303c103bf032f031d02cc025b0 else (if c < 253 then 0x855085405c60853885288510850084f084e084d084c084b084a0849084808470 else 0x7c168610860085f0782085e985d985c0755085b785a785907290858085708560)) else (if c < 255 then 0x4bc749f4483445804350102037540b2035572a2620f686506706864a863a8620 else (if c < 256 then 0x644062d85c335b0b60205e2a280622025ac12a6a213a3f11580656904f864db0 else 0x584345e043c44e104c094084379056f054814fc3048048706788661660a05e65))))))) else (if c < 300 then (if c < 278 then (if c < 267 then (if c < 262 then (if c < 259 then (if c < 258 then 0x8680867086607ca07adb80987f287c507a91787076c03eb7748072d070e728ab else 0x87288710870886f086ea86d086c080eb7f6b7320715978c0770486b086a28690) else (if c < 260 then 0x31e92cd725cb8060879a7c248780783087797560876772a08750874087305c70 else (if c < 261 then 0x87c084b787b087a08479846984593d4154916e406ba85b8426e1534b386b3307 else 0x88806f878871886488514b0988405d02883041c08820881a880087f487e087d7))) else (if c < 264 then (if c < 263 then 0x331732192ce725fa893089208910890788f788e788d088ca88b488a0889475e4 else 0x86c4834789828970896089508940866082e93d5154a16d706a1226f1537a3c4a) else (if c < 265 then 0x77c08a3972108a274cf08a145f308a0244b089f089e289da89c289b489a08997 else (if c < 266 then 0x4dc03c5a332732292cf7260a8ad08ac08ab08aa08a908a808a708a6a8a508a44 else 0x8b038af08ae4896089508940867082f978803d6154b16d806a2260342701538a)))) else (if c < 272 then (if c < 269 then (if c < 268 then 0x8b71420b8ba05d2a8b9b8b808b7b42018b628b5a8b468b348b208b1786d48357 else 0x8c468c308c268c108c008bf08be08bd28bc088a08bb46fc38bb06fc68b918b84) else (if c < 270 then 0x8c608c648c50868083093c6153916d966a322611539b3c6b323732392d07261b else (if c < 271 then 0x44d48ccb5f508cd244d08cc189e68cba8c868c748ca68c97868483078c838c70 else 0x2d17262b8d768d608d568d408d308d208d108d0a8a508cf072348ce372308ce6))) else (if c < 275 then (if c < 273 then 0x869083197c603c7156a453b153a56da06a42262156a053bb53aa3c7b32473249 else (if c < 274 then 0x8dd842448b668dca8d968d848db08da7869483178d938d808c608c648c507c64 else 0x8e748e648e538bd08e4288c78e3479d08e2270058e108e098df64ef48de05d44)) else (if c < 276 then 0x83203db055006db06a50276053c03c80337a325b2d2a26308eb08ea28e948e84 else (if c < 277 then 0x44f08f614c608f508f408f308f208f10870083808f008ef08ee08ed08ec086a0 else 0x90028ff08fe08fd08d108fc48a708fb07bd08fab72508f9656108f835f708f7b))))) else (if c < 289 then (if c < 283 then (if c < 280 then (if c < 279 then 0x3dc155116dca6a6260442771527053da43603c9a338732692d37264a902a9010 else 0x907787148397906a9050904090308ee28ed28ec28ae47cd486b0833980a072e4) else (if c < 281 then 0x12314ff39113910090f290e35d6390d01830437090c04e9a90ba90aa9094908a else (if c < 282 then 0x8bf091c091b091a788e791909184917279f29160915091497049913091211240 else 0x45c045a04370405037640b4035672a3021069220921a92038e6391f091e691d0))) else (if c < 286 then (if c < 284 then 0x5be05b3b60505e3a5ba05ad12a90216358f0581656b04f964dd04bd74a104844 else (if c < 285 then 0x4c3940b037c057405720554155214ff34a8048a06790662360d05e95645062e2 else 0x80b07f387c707aa1789076d07500749072f07127710759105873461043f44e60)) else (if c < 287 then 0x89b081107f927350718979207734905090308ef28d808c708af089707ce07b0b else (if c < 288 then 0x7a02927070599261413041210c6392505d7345000c2090908f389240923a8b30 else 0x6bb2278153e345b03ca3339732792d47265392b08e7392a48c00929088f79284)))) else (if c < 294 then (if c < 291 then (if c < 290 then 0x930092f787f084e792e092d092c0904087a0848971173dd15730555155316e50 else 0x93d07c1093c093b093a072989395938593705fb0936493549340933a93209310) else (if c < 292 then 0xb6835752a4a211a946090009459944994308d50942a941a94008ab893f593e5 else (if c < 293 then 0x2aa0217044f2582a56c24faa4de84be54a254855153043a8438840683cb7377b else 0x50004a9848b867a4663060eb5ea3646862f45bf05b476084606b5e495bba5ae2))) else (if c < 297 then (if c < 295 then 0x7ab278a576e871f574a8730771354d175880462a44064e764c4140c037d41b87 else (if c < 296 then 0x736271907931774690698f048d908c808b0089847d107cf17b1780cb7f4b7c8a else 0x8ac094c07c2094b372a094a75fc0949290a38f4b948594798b4089cb81247fa4)) else (if c < 298 then 0x50816e606bc26074279153fb43903ccb33a732892d57266b901094ea8d6094d4 else (if c < 299 then 0x4b239533952a95169324950094f7880484f792e092d092c07d0487b084993de1 else 0x88c095c095ba95ab76019561955095414b229590958b957b61a8956095519540)))))) else (if c < 321 then (if c < 310 then (if c < 305 then (if c < 302 then (if c < 301 then 0x964b963b96229612960295f095eb95da88c195c195bb95aa760095f195ea95db else 0x83634e203d7154c16dd06a766306271154c04e213d70333233332d6227109650) else (if c < 303 then 0x442096d09471923196c096b096a0969296809670966086e183629470923086e0 else (if c < 304 then 0x973097208a74971477e497098a70971077e097074d1496eb639096f24d1096e1 else 0x3d8554d56de06a8267b0272554da3d8a334733492d77272a9767975090079740))) else (if c < 307 then (if c < 306 then 0x979a9489924497809777968a967a966a86f4837778d49487924086f0837978d0 else 0x97f097e4762497a417394c14911497d097c797b761e797a017374c1091104647) else (if c < 308 then 0x98509840960098349821981488e4980497f497e076209830982b981088e09800 else (if c < 309 then 0x57044fd14e504e304c104a60488045f043d0409037a40b8035802a7021409860 else 0x67c0664060b45e78647063105c045b1260b05e725c005b182a74214459205851)))) else (if c < 315 then (if c < 312 then (if c < 311 then 0x74b7733071605924585b45f443d44e544e344c14409437a057004fdb4a644884 else 0x771990708f1a8da08c908b1089907cb07ae380f07f707cb47ae678e077177510) else (if c < 313 then 0xc44987761f74ac70c4090748f15977096908b14899480f47f747334716478e4 else (if c < 314 then 0x3d94335033542d80273498a79610989988f498847630989788f0988076344ac9 else 0x98c098b087d484c094f092f087d084c44e443d9054e06e706bd0273054e44e40))) else (if c < 318 then (if c < 316 then 0x99829970782099699959994063d0993299229912990298f098e094f492f498d0 else (if c < 317 then 0x215699d0900799ca99ba99a48ab499989988997478249967995799a08ab09992 else 0x5615586857114fe61a804c274a744894460043e040a037b40ba035972a86274a)) else (if c < 319 then 0x67d2665660c85e8564a0648663225c125b2a60c25e8a5c185b252a8327452153 else (if c < 320 then 0x752774c073407177561a5862460443e41a844c2940a437b0571b4fe34a704890 else 0x7724908a8f228db08ca68b2089a07cc37afb81087f887cc67af1791778f67720))))) else (if c < 332 then (if c < 326 then (if c < 323 then (if c < 322 then 0x9a0299f299e290858f28978096ca96aa8b2489a481027f8273447179791978f3 else 0x3dab336733692d97275b97509a3a8ac49a2478349a178ac09a2078309a1963e0) else (if c < 324 then 0x96ba87e484d779049500930087e084d979003da154f16e806be26490275154fb else (if c < 325 then 0x9a679aa09a969a8865589a71086a58969a689a509a4a9504930498d798c798b7 else 0x96029ad09ac79ab27e829b009af09ae98e699ad19ac69ab37e839a7008645897))) else (if c < 329 then (if c < 327 then 0x48cb4631441540d137e10bc035a22ab121819b019af19ae88e689b309b2b9b12 else (if c < 328 then 0x5bc05b5060f05eb05bc15b512ab0218058c158b15896575150184e814c524aa1 else 0x463044144e804c5340d037e0575050194aa048ca67e0666460f15eb164b06336)) else (if c < 330 then 0x89d07d207b2481317fb57d217b257941775a74f074db737071a858c058b05897 else (if c < 331 then 0x8f56979096d08b5189d181307fb4737171a97940775b90b08f578dc08cb08b50 else 0x8e789b7b96129b5b7e929b6a8e799b5a7e93577b09499b4b6568577a094890b1)))) else (if c < 337 then (if c < 334 then (if c < 333 then 0x8810850358d03df155616e906bf627a158d155603df033b233b32da227a09b6b else 0x9bba9bd067009bc09bb09ba09b909b80952193319a4098e28811850295209330) else (if c < 335 then 0x9be19c0b900b9bfb9beb9bd467049bc49bb49c0090009bf09be09bda670a9bca else (if c < 336 then 0x4e924c6a2aca219a4640442240ea3e0737f10be235bb2ac521959c0190019bf1 else 0x61015ec664c063405bd05b6761005ec75bd15b682ac421940be835b14e984c65))) else (if c < 340 then (if c < 338 then 0xbe735b0464144234e934c6b40e43e0837f04e994c642acb219b40e03e0237f4 else (if c < 339 then 0x8b6489e48b6089e061045ec92ac1219161055ec8610a5ec25bdb5b6264ca634a else 0x67109c124e964c61464b44268b6189e12ac0219064c46344610b5ec34e974c60)) else (if c < 341 then 0x557b3e1b33c733c92db727bb90149c3497509c4080649c2990109c3080609c27 else (if c < 342 then 0x953693449a5098f78824851795339340882085193e1155716ea06c0267f027b1 else 0x9baa9b9a9b8a)))))))))
def hint6 (i : Nat) : Nat := (hint6C (i / 16) >>> ((i % 16) * 16)) &&& 65535
def hoff6C (c : Nat) : Nat := (if c < 2 then (if c < 1 then 0x17905a7150050b128443b0f383680bfc28808681b005100de01d0000 else 0x27509ac25b0902236c8a321ec846203c7db1e7475d1bcc6c81a4062b) else (if c < 3 then 0x36c4d7f3530d0b339cc873124bc92e3cb592c98ae52aa8a7828f8a0c else (if c < 4 then 0x453911e43a90b8421905640bcfcb3e68f283bd8eba39f8e4e385cde7 else 0x54f94db52c544750753b54e2d3214bc12af4a2122447d5185)))
def hoff6 (i : Nat) : Nat := (hoff6C (i / 16) >>> ((i % 16) * 14)) &&& 16383
def hint5C (c : Nat) : Nat := (if c < 765 then (if c < 382 then (if c < 191 then (if c < 95 then (if c < 47 then (if c < 23 then (if c < 11 then (if c < 5 then (if c < 2 then (if c < 1 then 0x280009b002100070000c0002a000400000001800051001000000000c4002b000440000 else 0x58401500051001340049001140041c00f70038000d60030800b0001840050001040000) else (if c < 3 then 0x980025b00900023800880021b0080001f70078001db0070001b0006840190006000170 else (if c < 4 then 0xd8c035300d0c033400c90031400c0002f000b9802d000b0002b800a80029900a000272 else 0x119004570110004300109c04160100403f400f8403d900f0003b000ea4039400e240370))) else (if c < 8 then (if c < 6 then 0x159005500150005340149405140141004f90139004d00132c04b3012ac0494012240470 else (if c < 7 then 0x199006500191c06300188006100180005f60179805d00172005b0016a80594016180574 else 0x1d98075501d18073301c80071001c1c06f001b9006d601b1806b401a90069601a080670)) else (if c < 9 then 0x21280838020a808100202807f701fa807d801f2807b601ea80797008280786007a80779 else (if c < 10 then 0x24c00920024500907023c008e80234001840230008b402280089402200087902180085a else 0x286008e80282009f80055009e00276409c0026e409a0026640988025c00960025400940)))) else (if c < 17 then (if c < 14 then (if c < 12 then 0x2b880ad002b1c0ab2002d00aa002a600a80000000a70029800a5a000000a40028e00a28 else (if c < 13 then 0x2f680bc302ecc0baa02e680b8002de80b60000000b5002d280b3402c880b1002c000afb else 0x32e80ca0032440c80031cc0c600314c0c40030c00c20030400980030000bf0021400be3)) else (if c < 15 then 0x36d80da0036480d86035c40d630354c0d40034ec0d20034480d00033e00ce0033600cc0 else (if c < 16 then 0x3acc0ea403a500e80039e40e64039640e40038c00e230386c0e00037e80de4037540dc6 else 0x3ed00fa003e5c0f8903dc00f6003d5c0f4403cc40f2003c500f0703bc00ee403b400ec0))) else (if c < 20 then (if c < 18 then 0x42ec10a4042641080041c01064041501040040c0102404058100903fd00fe003f400fc4 else (if c < 19 then 0x461011700459c1156045180751044d811230444006b6044140670043e410e00436410c0 else 0x499c125a0491c123a04898121a0482011fa0478011da047180c8a046e40c6a046a41194)) else (if c < 21 then 0x4b9812d804b1c09b0028e00990006d012b004a98129604a100880027e8086000598127a else (if c < 22 then 0x268013a002fe0087004e40138004dc0136004d401348030e0133004ca0131604c0012f0 else 0x518014520511c0070050c014270504800000500013fa04f80000004f40135004f0013b0))))) else (if c < 35 then (if c < 29 then (if c < 26 then (if c < 24 then 0x551c15370549015140540014f4053840ae00534014c0052cc14a0052401481051c00000 else (if c < 25 then 0x580015f50578015d10570015b90568012c005640158002400157004a0008900559c1554 else 0x5c0016f205ba816d705b2816b705a80169105a001674059801653059001638058801614)) else (if c < 27 then 0x600017f105f9817d005f1c17b505e94179705e00177905d90175305d2c173205c881714 else (if c < 28 then 0x640818f60638418d00630818b2062a818920620c187a061a818500611018300609c1812 else 0x681c19f00678019d10670419b7066a8199a06608197006580195406524193b0648c191a))) else (if c < 32 then (if c < 30 then 0x6b541ac006ac8071406aa4112706a5406d406a101a70069801a50069201a37068801a1a else (if c < 31 then 0x6e841b9206e041b7906d841b5506d041b34057841b27057041b1806c28115006bc01ae5 else 0x24e40a180245c019404ac013a904a580c0a023000a0a02280017706f841bd006f041bb5)) else (if c < 33 then 0x22dc1c80071e41c6004be413b004b680c18071401c40070ec1c20070401c0b06fc01587 else (if c < 34 then 0x529c1d09073c01cea02c901cd9073201cb9000001ca004b981c9b0702c0920055dc12ab else 0x75241d00073e41ce802c9c1d30074981d17052901cd0073281cb0000001d39074ac1d14)))) else (if c < 41 then (if c < 38 then (if c < 36 then 0x76581da2076541d8004c001d70070800940070a41309025241d50075801d40075a41d59 else (if c < 37 then 0x78e81e26078581de0077441e02077c41dc2076d01e00077e01de2077601dc0076cc1da0 else 0x7adc1ee507b581ea707a5c1ee607b541ec207ae81eaa07a681e80079c81e620794c1e42)) else (if c < 39 then 0x7dc01f6307d6c1f4407cc01f2907c501f0207bc81e60079501e82079c01e40078dc1ec0 else (if c < 40 then 0x7c4c1fc707ec0200007fc01f6407d641fe107f441fca07ec81f8a07dc81fa707e681f87 else 0x80a81ae00811c1170080dc0730080a01a74080641a77080401faa07e5c1f0007bc01f2b))) else (if c < 44 then (if c < 42 then 0x81a820bb082a820960821c207b081a01dab081641da6081401179080d01ae9081100739 else (if c < 43 then 0x726c1c360565c133904f00131b030a00979028a00959006ac209b0821020b6082a02076 else 0x836420d008300133004f241316030a81c50072581c3b056500970028a80950006981c59)) else (if c < 45 then 0x842420f90850021300848021190840020f0083801328075c01c40025801c4904ca80969 else (if c < 46 then 0x71c1ca0071a415a704f401379031200a400272401c4084a42110085802150085242139 else 0x86c021a0086682180085c013d904dc00c4a0838020c0076001ca90718015a40292409c0)))))) else (if c < 71 then (if c < 59 then (if c < 53 then (if c < 50 then (if c < 48 then 0x8a402280089dc2269089582229088582240088c022200886c2200087c021e00875421c0 else (if c < 49 then 0x8b642189085e42209087e421a90866022600896c22e008b4022c008ac021e90874822a0 else 0x4e4020d0072001b0305b0809e0071c0138902740076a00bac2289089d02249088e422e9)) else (if c < 51 then 0x35a402f908f2423b008e80239908e24237008da4235308d00233308c80231908c0022fa else (if c < 52 then 0x8d400e70078c017e00100016e4035d0077008fa0066708f680d600788016d000bc016d9 else 0xc002430090a4241004340240a08fc4236003a201e4605fd8041605be00d88007a423f0))) else (if c < 56 then (if c < 54 then 0x3b981e660615c047005c400c6a00c5c24500910023b003b681e5a06100046705c1c11a0 else (if c < 55 then 0x6010042406c500d9400c9024d90930024b9092a424900920024700691024640912423c0 else 0x1e28068408f5024e908e000ea607a2c181a010c015c4036a8033709380237003a6c1e7b)) else (if c < 57 then 0xd4c22fa08bc00e3007a6417a001e001720036c0034900d0c17aa07a4c172a036e80e3a else (if c < 58 then 0x6c8003e005d000dd000d8024f80699c246508bc02300039281ea305ee8020905ce80dca else 0x94a4201009440250308d000e6b07b2c15e400fdc175b037980370094002330039401eb0)))) else (if c < 65 then (if c < 62 then (if c < 60 then 0x3b281dab060d0045405dd00e0800e50253008e400eb0081401820011001760037c00380 else (if c < 61 then 0x388003b0095402310046c01ed005f0003c005e100e1400e802549043c0240a094e423a0 else 0x178019c007bc01050061a4079904700256000000255908c800c8a07b8017d400f401790)) else (if c < 63 then 0x675805f6061d411da01ea406b6095e02176085c0105607bd819c6017981865047180795 else (if c < 64 then 0x96a8259008640101007c401980016801b3003bc007b0096100000085d82180041981f06 else 0x3c6c07db0970025c9096ec00000966821a0040981f220664805b006d100f0201f2406da))) else (if c < 68 then (if c < 66 then 0x7d20189a01f80189803ca807e9097c006f8097ac25d0086c00f1607cec188b01f581886 else (if c < 67 then 0x1c6026240984021d003e401f5006dc00520062800f3001fc02609001e825d0087000f28 else 0x9a242679099a426500992000000985421e003ea01f6806e1c0534062e00f4b020242630)) else (if c < 69 then 0x3da8082901cc026d009b0021f0040e020680668805c8063200f520206026b009a802690 else (if c < 70 then 0x48101f700641004a0063800f74020c026e0002c026c0088001048081ec19b00174018d4 else 0x9c8027100000026fb08880121807e0c1912012cc18f303e0c084901d4c270a09bc02210))))) else (if c < 83 then (if c < 77 then (if c < 74 then (if c < 72 then 0x9ea42790088c0109107e441a00018801b5004780048009e00277009d80275009d242739 else (if c < 73 then 0x160019200488004c009ec00ae809e402240042981fa306848063006d9011fa0125c1123 else 0x9f2c22600400c1fc306f900597064cc123801340115b09f6827c0089400ff007ec01bd0)) else (if c < 75 then 0x496804f0045c028190a0002270042c020800688006400650012400138027f709f900b29 else (if c < 76 then 0x7f40196001400196901424126904980282000000280708a0010c8082581a30019401950 else 0x65dc0514065d0127a0145c11940a0c0229408a40126407f5019670141019640499c0507))) else (if c < 80 then (if c < 78 then 0xa180285008ac00fb607fec1b9b015001b9603eec05490a12c000008a5022a0049e01fe4 else (if c < 79 then 0x18001bb003f6805670a1c014a70a14022c003f18200b06e9c055006e900fcb015641acb else 0xa20022e00422020bb067dc061006f100fea015dc1ae00a264288008b401078082a819e7)) else (if c < 81 then 0xa5cc29620a54029490a4d829200a44429060a3d025720a39828d60074028c40a2d428a7 else (if c < 82 then 0xa8402a060a8d82a260a8502a030a7c020f30a78002050a74029c00a6c029a00a6542983 else 0xab442ac40aaec25770aa9c28a00aa502a800840029e80a9c82a6a0a8cc2a230a9402a40)))) else (if c < 89 then (if c < 86 then (if c < 84 then 0xae402b800a8402b78084402b600ad402b400acc028340ac802b100ac0c2afa0ab882980 else (if c < 85 then 0xb19821200ada42c500b1042c320b0802c170b0002bf90af982bd00a9d82bca0aec02ba0 else 0xabe82d200b4642d060b3c02cea0a50c2cd00ab1c2cc20a4282cb10b2802c910b20c2c70)) else (if c < 87 then 0xaed42df50a8d02de30b74421300b7002db10b6802d900b6002d700b5842d510b5002d39 else (if c < 88 then 0xb9c029640b9902c890b99c2c80085002dc00af802e560b9142e350b8802e120a9402e04 else 0xa8c02ec8085402eb00ba802ea90ba242b100ba582d100b9e429670ba6c2d190ba002b19))) else (if c < 92 then (if c < 90 then 0xbc002350085802eb00bbd42ef20b0242ed00b9242ee80a8e42eca0b9002eea0b0002ed9 else (if c < 91 then 0xbe0c2f700bd982f530bbc02c300a7c429b10a6842f440bce42f290bc6401e40081028b4 else 0xad2430100c0242ff00aa5c2fe008ec02fd00bf242f0708d9829c40bee02fa00a3002f93)) else (if c < 93 then 0x8e002d400c2ac309b0b1c0308008dd030770c19030570c11c30340c0902db60bfa423c0 else (if c < 94 then 0xc3d830e60c3402db00b24030c008cc02f5408c00230a0a75829d80bea028e00c2d43087 else 0xc59c309b0b28031500c51031340c49030b40bd9031140b1002dd00b5802d500bd003106))))))) else (if c < 143 then (if c < 119 then (if c < 107 then (if c < 101 then (if c < 98 then (if c < 96 then 0xc6e42ff00aa9031a008c40317908e802ea00c64031800b990317008e4030c308d002d70 else (if c < 97 then 0xb6002a3a0c84032000864031f10c79c31d40a4002186086002a100c70031a908c802b59 else 0x870c32700a84032600c94021b60c91432460c8e832370c88029240c82831450be1021a0)) else (if c < 99 then 0xcb4432c30a58832a5087802f430a96032b00ca8021d00ca5832890a51032580be6c2f92 else (if c < 100 then 0x884033770cd9829850cd2022000a8c033500cd0021f30cccc33230cc4c330a0cbe832e7 else 0x88c02d900d04034000cfc033e00cf6433c10cecc33a00ab1c3387088a02a760ce503380))) else (if c < 104 then (if c < 102 then 0xc49422600b6802beb0d1c0346008940345a0d1182af40d08022400aec034300d0803151 else (if c < 103 then 0xd34c34cb0b3c022a408a802c200d2c0349708a002c000d2a43490089c034840ac50346b else 0xb90035300d48022d00d44435000b46434e00c4d4313208b002e2b0d3c034e008ac034d1)) else (if c < 105 then 0xd6c035a901a4c066801a4006660d64035800d5ec355a0d5ac354a0d56c354b0d48022e0 else (if c < 106 then 0xd90423e30d8c0363a0d89023e90d84c36000d74035c00d7e035e00d6e835a30d76835ca else 0xdc2010e00dbd036e00db4036ca0daec36aa0da6c368a0d9e836600d62836550d9143651)))) else (if c < 113 then (if c < 110 then (if c < 108 then 0xdf2837b90de8033660de5437810ddd437600dd5c37400dce437230dc400694043d035b1 else (if c < 109 then 0xe1d40ae20e180385a0e10000000e0c038200e06800000e00036d50dfe837ea0df682547 else 0xe5a839500e50039370e488391a0e40038f80e38000000e34038ca0e2d038a20e2403884)) else (if c < 111 then 0xe89037200e8481a700e80435d70e7d01a570e79439d00e70039ba0e6a8399a0e628397b else (if c < 112 then 0xec0039ca0ebd83ae60eb583ac70ead83aa50ea683a840e9e43a600e9483a480e8e03787 else 0x69dc3b700ed803b500ed08391a0ecd838a90ec900b270eccc38a70ec800b290ec44007a))) else (if c < 116 then (if c < 114 then 0xef843bd00ef003bb20e9103ba40dd903b990e9003ba00dd803b97069e43b740d7dc3b8a else (if c < 115 then 0xf0d000b40f12c39100f0c000b00f0e800ba0f0803b500f0483c010efec3c0b0efc43bd4 else 0xea003ca70cd943c96019c03c740d8403c88019c43c7a0f1803c500f10439140f100391a)) else (if c < 117 then 0xf4003c500f3ac3cf00cdec3cea0cde83cc90f36c3cc80ea043ca60ef083cb00cd903c97 else (if c < 118 then 0xd8a8359a0f6803d900f5903d540f6003d700f5103d300f5803d500f5003d340f4803d10 else 0xf7403dc00f6c03d000f1803b040e7543c200ed8038040dba83b000e76838000db943660))))) else (if c < 131 then (if c < 125 then (if c < 122 then (if c < 120 then 0xfa403e800f9d03e600f9403e400f8c03e200f8403de40f7503e000f7c03dc40f6d03de0 else (if c < 121 then 0x9bd03e440f8d03e840f9c03f000fbc03ee00fb403ec00fac03ea00fa50338009bc03ea4 else 0xfd103f300c68025500bc0023f00ea5837a40d8c43f040fbd03f200fc403ec40fad03384)) else (if c < 123 then 0x100003f500dedc3ff40ff803fd40dbc0240a0ff003fb10fe803f900fe003f700fd803f54 else (if c < 124 then 0xfe8040a00fe403aa7102404080101c04060101504040100c039e7100a840040fd804010 else 0xe56840f00fcc03ac1103803a071009440d00fe0040d00fdc03bd0103003b70102c040a0))) else (if c < 128 then (if c < 126 then 0xd6c441250f6d83db01044000000fec03fc00fec03fb10f3043cc00f1d84100103d03f40 else (if c < 127 then 0x10584007a105003de00ead036500d76c415a105003dd0104cc00000f6d83dc00df283640 else 0x1075800ba106c03e000ef8435f71070041b00f7c041a0106404180106504184105c04174)) else (if c < 129 then 0x109804250109004234108800000107c03e200f35c42100d848420a107c03e101078041e4 else (if c < 130 then 0x10b403e570f94042c00000042a00f9003ad40df68372310ac042a00f8c0429010a004270 else 0x10c400ae910bd03e800efc4376010c1042f00f9c042e002c9c3e570f98037e50dfa83740)))) else (if c < 137 then (if c < 134 then (if c < 132 then 0xfb003c0b0e900436010d403eb010d0038a710c903ea00eb9037f50de2c433a10c803e90 else (if c < 133 then 0x10f2843b00fbc043a30e44043800fb803af00ebd03a6610e4043800fb404376000004350 else 0xfc403cf20f04844101100044141101043e010fc043e410f48391a10ec03f000f39c3a82)) else (if c < 135 then 0x1115444441048c01f10a30c28b60a35001f00a30828b70a35844200fc803bc0110c04420 else (if c < 136 then 0x112444480111d444e01134844c4112c844611115044451048844a1112404481111d04460 else 0x1154c01e60079c4540114c02f210bec02f110bec42f200bc404520114404502113d044a0))) else (if c < 140 then (if c < 138 then 0x1049c0c50116e445a80aa003d27116482f310f46c2f30116404582115884572115484563 else (if c < 139 then 0x9c004670119ac465411928463011880461b1180045f010b5c45e6117402aa70a34045ca else 0x11c402c600f51c46e911c0046f00f4c046e011b6446c90322031b011ac046a011a40468a)) else (if c < 141 then 0x11f6847c311ed847a011e40478711dd0464211d8045d911d44474011cc42c8311c884473 else (if c < 142 then 0xaf8048900aee048850a8c04874121843d57121404841120c0482712040480111fc447e0 else 0x1255c44b71251c2c800f59c4850124c4492b124604907123c048e91234048ca122e048a5)))))) else (if c < 167 then (if c < 155 then (if c < 149 then (if c < 146 then (if c < 144 then 0xf5c049b01269049a0126404980125c44784125904600125ec4780125804604125242c84 else (if c < 145 then 0xbd142f4a123dc4a1a122d04a080b01049f7122c04a020b00049f90a94049e21274849c2 else 0x11f244a8609c0c4a640a29c4a76113e04a6a0a2a03d87126dc4a52129284a33128d84a26)) else (if c < 147 then 0x12b802a7a12b682a7012b403d9212b004ab012ac44a9111f204aab126084a8709c084a90 else (if c < 148 then 0x12c803f5712c504b000f69c4aca12be04af212bdc48f112b8448fb12bac2a7412b5048f0 else 0x12e102f9912bc0490011bd846a611a584b7012d804b5612d184b360b0c00c640321045a4))) else (if c < 152 then (if c < 150 then 0x130804c1013010484112fc04b240fd9c46b912f804bd90bfc045b012f004bb712e8c4b93 else (if c < 151 then 0x132804940132403f70131403fa711f804c84131cc4710131844c500fe5c4910131004c30 else 0x11fc02c4012dc04d01133c44ce10bbc04cd0121004730133003f311325c3f871269c4cb9)) else (if c < 153 then 0x1330c3f47120404d60131cc4740135504d44134d04c6012e644d23134502f89121804800 else (if c < 154 then 0x1366844790f7042f7112e0c3dc70b0c82c3b0a8404d800ff183fc712ad44ab4135c84a60 else 0x137e04df91378844b2134544dca0f79c2f69124a02ef10a8cc4dd0137003dd2136d44da4)))) else (if c < 161 then (if c < 158 then (if c < 156 then 0x139884e58113c04e320f81c4a260a9404e40138c03dfb114c04e22138484e021384c4e03 else (if c < 157 then 0x13b5c4ec313adc45d413a183e2712bc0454213a802a7213a404e800f8444e76139e04e67 else 0xb0804f5013cdc4d5512ecc3e470aec04f4013cc03e30120804f2713c5c4f0713bdc4ee6)) else (if c < 159 then 0x13e84464913e003e87128d82c0013e644f800f9e44f7b13d8046090f9804bc112f2c3e67 else (if c < 160 then 0x140403eb7140044ff011e1c4fcb134d43ea7124e44fe012dc42be313f404fc00fa584fba else 0x141404d45135283ee7123585060141403ed714104504b140d847a0140403ec7122c05020))) else (if c < 164 then (if c < 162 then 0x143ac50c11436c50c0142ec4982142483f07120c048f21428050900fbe85086141d047c4 else (if c < 163 then 0x145c05160145685142144c0512a144283f27123dc5110144003f121290050fa143a850fb else 0x1484852001394451f51478451d0019c036f70c88051c001a5010d7146c051a0146405180)) else (if c < 165 then 0x52b014a80529014608528a139a8527a0ff64323a149802417149405244148c05227 else (if c < 166 then 0x14bc8532014c48530414bc052e014b6852c00000052e714b4852c70000052ea14b4052ca else 0x14d88536014d40533214d08534014cc0533714ce852e214b5c52c200000532214c40530b))))) else (if c < 179 then (if c < 173 then (if c < 170 then (if c < 168 then 0x14e5c53b814ea053b214e8851e414e501a5714e2851e914e6451e014e401a5014e085370 else (if c < 169 then 0x150880ae215040540115020535014fd853fb14fa853f314fc453e214f4053d714f0051e7 else 0x1530054b0152805490150a80aea152005472151905450150dc0b271512052f2150c00b20)) else (if c < 171 then 0x1540054f91558055541549c55181550055311538054d81548055151541c54f41539c54d5 else (if c < 172 then 0xc92825ca12c5c3ff01571c55b00bf602438156a8559715600557412c203fe50bf002420 else 0x15988565b15908563a0bf5424351589056101581055f9139e841e2157ac55d312c403ff7))) else (if c < 176 then (if c < 174 then 0x15a8056901592856320bf1c24271570055b712c143fe8156885590139c841ea15a005672 else (if c < 175 then 0x69e456b0148c056d71484056c2069d056b71582455f40c90825c215a1c567a1578c55db else 0x1538c571415d4c574715cec5722153ac57191485c56ca15c0056f2148dc56d014ed056e4)) else (if c < 177 then 0x14aa851a715020536014a8851a014a40519215ccc572a15e6c578215d6c574015dec5768 else (if c < 178 then 0x16048580a16040580715fc057b01528057e715f8057d014a5c519a15f0057b015e8454b0 else 0x14dc052b2146c052b0146c8581716000586016140586216148581a160085840160c05820)))) else (if c < 185 then (if c < 182 then (if c < 180 then 0x1620058760c94025d614adc51ba15fc057d21530057f215f4054c214ae851b71504053c1 else (if c < 181 then 0x1628058921630858ba1638858d21620858751638058d01630058b716288589013a0841f8 else 0xc95c25d11629c589a1632858b21621c58711640058f01640858f216228587813a0041f1)) else (if c < 183 then 0xbfa8244a12c8040071499c57ea15f8053d81498859301631c58b0162a85897164805910 else (if c < 184 then 0x1669c538416640558b1561059800bf802440165c05969165e8596312ca84002165485940 else 0x167d059e21654055a11569459e01650055941566c53e4166c059d01676859a21670059ba))) else (if c < 188 then (if c < 186 then 0x168c05870158c055d01689800001686459701571054eb168405960156c057101682456b4 else (if c < 187 then 0x16ac85aa016a485a87169dc5a60169400ae0168d858801590455e114fc0527a147845a42 else 0x162c05740157c05af002c9c5ad216280568415cec521016b805ad016240567115c805ac2)) else (if c < 189 then 0x16cd058d4163405658158505652158405b20000005b0716300575315800523016c5c5b00 else (if c < 190 then 0x14ed05b7016d8058f015a50576816d5052f21635058e014a08566115880528a16d005250 else 0x16e40592015e6c579415c005ba016e40591015e08578016e00545016d80590015a90577b)))))))) else (if c < 286 then (if c < 238 then (if c < 214 then (if c < 202 then (if c < 196 then (if c < 193 then (if c < 192 then 0x170805c141702c5bfa16fa0420416f585bc4031c045b9116a028a016ec425e70aa5028d0 else 0x172005814171c05c49171804b50160005c50171000c6812d004bd012cc03000170c05b30) else (if c < 194 then 0x173c45ce01735c5cc6172c05ca6172485c86173405cc1172dc5cd61731c5cb1172805c9b else (if c < 195 then 0x1749c30170915c5d10166204be01005c3016091585cd1173005cb6174045cf0173845d00 else 0x16d045d76175945d50175204ea21086c4be6100443270097cc4be1100585d31174985d30))) else (if c < 199 then (if c < 197 then 0x174845d37174804be7100404eab108485d56175105d70175a45d8016d003010091405d81 else (if c < 198 then 0xb1805d71175a05d57175145da0176403271097c85d51175245d77175903011091445d36 else 0x16f005dd2177185db20b1985e01177c05de116f1c5e07177d85de716f045ddb177005dbb)) else (if c < 200 then 0x172005e00177c45de016f185e40178c45e20178445e41178c05e21178405e06177dc5de6 else (if c < 201 then 0x17a845eb017a805e9717a2c5e76179885e52172185e9017a0c5e9617a285e70179ac5e5b else 0x171505c70171645c76171545ed017b805ee117b585ec217b445ed717b2c5e9117a085eb1)))) else (if c < 208 then (if c < 205 then (if c < 203 then 0x17c9c5f1b12d8c4b6212da85934164e0582812dac5c71171605f0117be05f0017bd05c77 else (if c < 204 then 0xaedc5f690aec05f640aed85f6817d485f5b160e05f4017c805f3017cc45f2617c485f21 else 0x17e642c8417ec05c1917e8c5bf017e502c89161205f400aec45f6517e045f7117e005f70)) else (if c < 206 then 0x180a42be0180605850180005ef017fdc5ff017eac5bf717fac5fd017edc5c1417f105e14 else (if c < 207 then 0x17c006090182044b7212de82be7180546078181a02c07180905f80181486042180c82c00 else 0x1240060e017c405db01834059441720060b01830060c1182985f12182c460a7161906004))) else (if c < 211 then (if c < 209 then 0x179c06156185005dc01849c4bb0184c0612912ed05f50179805e501241061121840860f2 else (if c < 210 then 0x186dc61a0186605bc51859c597417fd05d3018610617017e406160165805d20183405958 else 0x1882461f6187905bf21870c4b98184ac588417a402c411242c2bb01874061c0161c05e80)) else (if c < 212 then 0x18a586284170506268162905d500af8062701898058901750062531890c6234188906211 else (if c < 213 then 0x163804baa12e8858e4176005d840b08062c018aa458c4175c02c0018ae462a0162c05d60 else 0x18cac631017f6062f016410608117ac05f8018c0062f0163d05ea018b8862ea18b405e10))))) else (if c < 226 then (if c < 220 then (if c < 217 then (if c < 215 then 0x18ec063a118e44638018dc0636018d406330164a05da0181e0634018cc05918176406322 else (if c < 216 then 0x1920830d00b2c06470191a064501912c2db0190d8642019040640018fc063e018f4063c0 else 0xc10024a01948065141941c60a0166904bf7100c064f0193ac64d01932064b01929c6490)) else (if c < 218 then 0x1972465b9196906204169c0659019610657b0cf5027441305840611959065511951c6530 else (if c < 219 then 0x1998066530d058278619910663619880661713c8042971980065f01978050e31102c65d4 else 0x19d20673419c9032f3099cc671419c1066f419ba466d019b1066ba19a80669019a006670))) else (if c < 223 then (if c < 221 then 0x19fa467d619f244deb19ecc1a7b19e804eb019e6432ca19e2806900691c677419d946750 else (if c < 222 then 0x1a1046834137d441720c344682313b8442570cb8426631a0402db1091e461e91a02867f0 else 0x18f8069101a41c68f41a3a468d11a30068b11a28868901a2006870187c45a671a1846859)) else (if c < 224 then 0x1a8406a001a7c469e01a74c69c01a6e469a71a64469801a5c069601a54069401a4dc6920 else (if c < 225 then 0x1abe06ae21ab486ac01aadc6aa71aa5c69371aa106a7718ec06a601a95c6a401a8c06a20 else 0x1af206bb01ae8848401ae446b801adc06b601ad4069d01ad006b301a2806b221ac486b08)))) else (if c < 232 then (if c < 229 then (if c < 227 then 0x1b18060b0166d03024092106c501b1086c301b09c6c101b0186bf01af8c4cd011d406bd0 else (if c < 228 then 0x1b3a44e031062c6cd01b32c4ed7109004c401025c6cb01b29c6c941b2183076093586c70 else 0x1b62833e009d406d771b5806d541b5044ef6109846d301b49c623416a806d191b4106cf4)) else (if c < 230 then 0x1b9906e541b910333309acc6e301b8a06e141b8146df01b78c6dd01b7006db01b6806d90 else (if c < 231 then 0x1bc106ef01bb9c61e41bb481a7b1bb0033a01bae432c31ba8c06700e7806e941ba246e74 else 0x1bd906f511bd24621116a1c4cd11bccc33c109ce432d10994c48411011c50bb1bc8c6f16))) else (if c < 235 then (if c < 233 then 0x1a8006ab61a78064111bf006fb71be906f941a3406a771a2c063c01be0050c110f886f71 else (if c < 234 then 0x1c2c070a01c24070801c1c070601c1586b721c10070301c08070101c0006ff41bf806fd1 else 0x1c510714b1c4ac713b1c4906f811c44070601c40070f01a7c070e01acc868c01c34070c0)) else (if c < 236 then 0x1724071c41c6ec71a01c6605f101c60871701be4071601c5a868e21c5406f9a1a39c7134 else (if c < 237 then 0x1c81c71f21300c405b0c0d824961c70071b11c79071d81c78071d21c6907192183805dd0 else 0x1c9804e201069c72501c91c331409a504c061014472341c89472301c8a830330924c7210)))))) else (if c < 262 then (if c < 250 then (if c < 244 then (if c < 241 then (if c < 239 then 0x1435c43f01cc1072f91cb8072db189505ac01cb2472b91ca90625016b1072941ca187270 else (if c < 240 then 0x1ccc0331009a4072741c99072901ca0c72c71cadc72a01cc9073141cc8073101c9507249 else 0x1cd581a521728073801cdc033a61cd944eb01cd5c10e014e1872e41cb4473001cbdc7340)) else (if c < 242 then 0x1cf4073c10cee8272613b2c42391cec85f1b1672033a71cd9073a01ce5c73a11ce584eb1 else (if c < 243 then 0x1aa1468f418f4474201cf0033bb09c9c741a1d01c741b1d0184eca108e060eb1cfc073e0 else 0x1d14c74421d0c474611d14874431d0c069111aa1068f518f406fc11c3806fa51ad086910))) else (if c < 247 then (if c < 245 then 0x1d2d869061c5506fb61a41c5c801d28474a01d24074801d1c06fc01c3846fa41ad0c7460 else (if c < 246 then 0x1d58075571d50852f81d4c075241d44438a01d40074f61d39c00001d34074c01bedc74b7 else 0x1d90476301d88476101d80075f51d78000001d74075c11d6c075a01d64075891d5d814a0)) else (if c < 248 then 0x1dbc076e11db4076c41dac076a81da4070101da0076701a64074301bf4069501d9807650 else (if c < 249 then 0x1830859d3130a040750c16824ba1de4077831ddc077631dd4077461dcc077241dc407708 else 0x1384041971dfd077e913c6842820cc8026a0130c8408a1df4877ca0c19824c61dec077a2)))) else (if c < 256 then (if c < 253 then (if c < 251 then 0x1e1dc786a143dc44101e1687847189005ab41e0dc78200d02027781888c5a901e06c7803 else (if c < 252 then 0x9a1c79221e44079091e3cc78e41e34078c01e2c078a70cfc827621e268788213c144278 else 0x1e71467f71e6d079a01e64873a71e6006ef01e5e467d01e5881a701e54079431e4ec3307)) else (if c < 254 then 0x1ea4c7a841e9c077331e9887a531e9007a331e8a47a131e82076b31e7dc6f171e79479d4 else (if c < 255 then 0x1d18074b71d10871641c00070f11bf806b531a6046a971a58463f01eb4c7ac51eacc7aa5 else 0x1ed007b301ec807b101c10471001c0846b621ec007af01eb8876801a7006aa61a69c6401))) else (if c < 259 then (if c < 257 then 0x1ef407bc01eec07ba01ee447b821edc070301ebc076701a6e074521bfd469701ed807b50 else (if c < 258 then 0x1d1c071741c44070811ae086ac11a84064211eec47ba11efc47be11efc07be01ee407b83 else 0x10a84334009b0c71111c2006b831edc47b101da447b701ec4476901ab006a111908074c0)) else (if c < 260 then 0x1f1907c501f124626016b40342009e40626116b447c311f0947c101f0204e30106ec4f31 else (if c < 261 then 0x9b087c111f0247c301f090342109e447c911f2047c901f2004f3010a805100110887c70 else 0x1c2407b201ec846a211d20073bb1c82c70911a8807c511f1207c711f1947cb01f2803341))))) else (if c < 274 then (if c < 268 then (if c < 265 then (if c < 263 then 0x1f50049101f3c47ce21f4c47d211f4c07d201f3407ccb1f4407d061f3c07ce31f3447cca else (if c < 264 then 0x1314040a70c20424e51c2807b301ecc46a311a05c65181d24070a11a8c06816194644911 else 0x1dec877b31949872121b1c465271314440a61f5847d561f5807d570c20024e41834059e4)) else (if c < 266 then 0x1c8c86c95195007d901f5406ca01df0079f01954072201b20065301f61c79571f5dc6c70 else (if c < 267 then 0x1b60078a01df8066501c9006cc01a0807da519ea024651f65c7d601b2c077d01dacc6568 else 0x1b88067001a0c07dc4000007dbb1f3406d911e2cc77f31999c72531b34030d61f6c07cc0))) else (if c < 271 then (if c < 269 then 0x1a11c67d01f7407c001f0246e291e44c7a0919c2472631b3a468391c98479111b3807a00 else (if c < 270 then 0x1ea00780019b8072801b40068501f79014a41f0047c101b8c079201e84c67181c9c86cf5 else 0x1bb2040241f7d07c301b8547a931e06466f91ca486d191a19867f71f8007df01f0806e00)) else (if c < 272 then 0x1a9006876196244a401f8c049101f8807ce01b78078e01e08066b01ca806f30195c07e18 else (if c < 273 then 0x1965c31511318470c01ed807a711e3d07b411a984689719b2074a01cf1c72bb1be043952 else 0x1e88067601cb406f40196807e591f92438a91f88c7cf01b7c0790b1e0ec66d61cb2c4cd1)))) else (if c < 280 then (if c < 277 then (if c < 275 then 0x7e691f1406e941e5107a3319de072e21bd4465b41bbc07e771f9807c401ba007930 else (if c < 276 then 0x1f1906e641eb10784b19d1072fb1bd9065c41b98078411cbc47ac019d0065c01bd807e80 else 0x1cf405c861720073701f1807c701b9d07ad21e15867561cc0c6f71197646f161fa407c60)) else (if c < 278 then 0x1c2c46a571a21865e71a9406881197807b571ed5870b61a94468801978470b71d35873f0 else (if c < 279 then 0x1e1846d21197c46d201cf8073801666070b01ed407b511a95868871979874d01cfd873d6 else 0x1e1ec6606183886d311981c7d001f4186d271e19c7866197d873e61b49865f7197c07860))) else (if c < 283 then (if c < 281 then 0x1fb007eb01f2006d601e2007a40198c074001b50066101fa8052f81f4007d101b4c0787a else (if c < 282 then 0x1b68466771fb8079921f5c07eb01f2406d771e25c7a531992074121b55466271fb4073a7 else 0x1fbc07d301b74078d21dccc66a61cc886db119a1c7ef01f4806dc01e3087a6219a587312)) else (if c < 284 then 0x1b95467391e7507f301fc807ca01b9107aa41ea9467281ccc86e4519ca47f101fc0075a0 else (if c < 285 then 0x1fdc07f610b21c7f5510ae07f4409b502c750a3587f201f2c06e541eac87ab319ce07342 else 0x1ee008000057047ff01ff807fd00c2807fc016b907fb11fe987f921f7407f841071c15d0))))))) else (if c < 334 then (if c < 310 then (if c < 298 then (if c < 292 then (if c < 289 then (if c < 287 then 0x1fa4080702019c805616ba080410b218803409e9c802609b5847140a29c7b98200008010 else (if c < 288 then 0x9e9080c110ad87180177185db20aa207bb8202d87ba4202c080a0132008095110e08083 else 0x183c080d609e948120204448100203c48121204408101203c080c010adc80e20b18080d7)) else (if c < 290 then 0x205dc2c801ef48816a1ef18611020580815a2056c60e2204c08140204c47d46185406100 else (if c < 291 then 0x208808210208007e98207d481e4207507fa92072881b02068080f02066480642061c7dda else 0x20b1882b81234882a520a4882860b91c827917e008267122c082540b88082421ef9c8230))) else (if c < 295 then (if c < 293 then 0x20c6415e0057007f6020c007cc020b5c7d602085c82f220b80817020b407d501efc8823a else (if c < 294 then 0x20d2030901fdc04d5a1848430ba124c082b0204d04920200447ff11ff444a2220ce48329 else 0x20e1c7c390b910839020e007c2020dc083661fe807c101f0482e2020d4083071f3607fe0)) else (if c < 296 then 0x20f5c7c54122d083e020f407c4020f04806020e9c7cf52028483b5131dc804020e807ce0 else (if c < 297 then 0x210807c80210688400203dc7d1a1f44861302052881421850880e01f1d87c781234083f0 else 0x1f28c84632078084401f4c8822a2114882e22070084401f48884271f25c82c117e008430)))) else (if c < 304 then (if c < 301 then (if c < 299 then 0x214680690069ac8500213c084eb2136c84cb212ec84ab2126c84711f2c88290212008470 else (if c < 300 then 0x216848595093c06190216248570215801a5b19e804d96215608546214e44fa921480328a else 0x2188034872185c32802182006700ede485f02178085d0213d461a31f69c4da22170c85b0)) else (if c < 302 then 0x21780508b21a5c629b21a2c329b103245077219d483c3219801a702195c6287219248636 else (if c < 303 then 0x69c0872413d8087172100087000d21086f413e8486e80438056b421b4086c721ad086a0 else 0x21e9c879021b24345a21e28877713dec841a09fdc4fba21d805a090d118875521d048738))) else (if c < 307 then (if c < 305 then 0x22150840a221288634220cc8540220801a501e54888102200087f721f9c87d721f1c87b7 else (if c < 306 then 0x2248089102201c890b223e888eb2236c88c01f60888b02229c88982221479a0221e88864 else 0x227404f642271c6280226d04d95226940694080508990226248970225808950225008930)) else (if c < 308 then 0x52948a402262431fb228dc8a2b136e88a100949c31d0228008363227c01a70227908861 else (if c < 309 then 0x22b408ac022ac08a680e2a08a54052908aab1d6988a9022a008a7b151608a690e2a48a55 else 0x22d908b591e6a08b4820d808b38222408b2221d1c8b1420f1c8b05215d08af4069c08ae0))))) else (if c < 322 then (if c < 316 then (if c < 313 then (if c < 311 then 0x230d08c24230508c0422fd08be422f408ac022f188bb820dd88ba622e587e5522e188b77 else (if c < 312 then 0x69486ec00c7488ca2222d88c940d1108c87141c88c75186408c69019c03a04231408c40 else 0x235008d30234808d10234008cf0233808c441f84031eb2336c61bb103a48cc122d808cb7)) else (if c < 314 then 0x2205c879021b5086a0217c085d02164c8505237008db0236808d90236008d70235808d50 else (if c < 315 then 0x237e04dc0105088de0237484fc010c9832a0098408ce0231508bd022b408a40226408910 else 0x10be484201fac0509010ee883d01f98062a016c008e202386c34900a00061c0168c08e00))) else (if c < 319 then (if c < 317 then 0x23ad432000964083801f7c08ea023a688e80239c08e6023940346009f008e40238c04f80 else (if c < 318 then 0x1f8808f6023d408f4023cc08f2023c408f0023bc08ee023b5083001f6c08cc2216888ec0 else 0xc5c0253020b407d90185805a101324040d00c30025000e5508a14223288760216e083a0)) else (if c < 320 then 0x237408dd223e84000023dc08f8023dc08f7122dc48b7022b988f901330040f123e008f71 else (if c < 321 then 0xe29c8e58238008b80215e08fd0239408df023f1014a7237408de02235085c0215288fb7 else 0x23b408ee023b408ed421a5086902194040b023ac08e2021a18863b23fc08eb02386c8fe9)))) else (if c < 328 then (if c < 325 then (if c < 323 then 0x22e40878a21d049010238d88e3024000545823bdc8f0023bdc8ef021ddc877021c9059f4 else (if c < 324 then 0x241008f20241008f10223c09030221c07d77237c08e602288488e4221ac9027238d88e40 else 0x2241088ba242408e9023a68908800000906023a008ba0222589070241808e702415875a6)) else (if c < 326 then 0x23d408bb4242808b4423e408f3923d008f3923cc08a39228c089e0094408e9023a808cd7 else (if c < 327 then 0x243c090e52435c2621190c02ca70b25828d4238408ec022f008b682430090b023d8090b0 else 0x56c07f731fda42c60246009171245804153245409141244c08fb1244809110244044332))) else (if c < 331 then (if c < 329 then 0x20c80834020c404fe0098d431600c3c030e02478091d72470c5a45246c091a02464c9020 else (if c < 330 then 0x20cc08cfb0c4009280249cc9263057a492502490c92312489c30d61f8dc92102480091f0 else 0x24ba87e7024b402c8024b005b1424ad890c124a90281024a4426251252428a02341c9288)) else (if c < 332 then 0x1fb2493400a05c933210cc05f940aa008d2724c64932823450931024c004cb024be043c4 else (if c < 333 then 0x153ac93d024f0093b01860093a209f5c93932406c54d024e00937b0b210936710c009355 else 0x251108fd9250e87eca250a490c4250408fb0205c82c622351c93e42500893f0234e493e0)))))) else (if c < 358 then (if c < 346 then (if c < 340 then (if c < 337 then (if c < 335 then 0x1dad094e02534094c0252c07eda2528082f02525c90902522094781dc8094622515081b0 else (if c < 336 then 0xb200954623f44953910c00952016c649518105502e640a3408d67253c895002356894f0 else 0x2571095d0235e495c0076ac95b02568095900c6409588096a4957a1f81c1d9025580955b)) else (if c < 338 then 0x23fc09643206c096321f8289625251e496142406496021f9e895f02408095e30b2108d87 else (if c < 339 then 0x25aa82e4025a5c829825b20607025acc48b025a802e4a25a488d9b25a009670259809657 else 0x24258970709f4896f110f0c96e7169206b9011d0047310a29c8da725a2096d625b6048ba))) else (if c < 343 then (if c < 341 then 0x134008db325d0070d01334483b0135804cf013380973023fdc804b0b18097260968c9711 else (if c < 342 then 0x25dd88dea2379c311b20ae082b10b880976023e188f87259a0966925d5095e02371c9745 else 0x23b9c930924c1c4ca024b5c8ec32389c94a2122c097902399c8e0b25b4491f00b91c9780)) else (if c < 344 then 0x24fd493d524ed44a37248249204128c082c0124c093f824f6093b81539c54e024dc08ee9 else (if c < 345 then 0x239048e47181e097a023c008f0724f1093c9185c093840c4884d32134e8312a124dc82c7 else 0x2540c94d3252cc608025fec96d020b0082b025f8497d125f0477321dac8945225ec08f17)))) else (if c < 352 then (if c < 349 then (if c < 347 then 0x261409840239d8983026084947025ec08f2725308981020b80946026000977413528313a else (if c < 348 then 0x256d89596076881da0255408ea2260044d2323a9c94e22539c48d226180984123a1c8292 else 0xc51c4d1713468314a1248896d22575495b5256544a3224864921b25b404a301248095d6)) else (if c < 350 then 0x262849897261d08f67259e0988025d509640261c08f5923d108f472569095a70c6109564 else (if c < 351 then 0xd41c994406948799218b40993913fc099290d30099122640098f02638098d02631898b2 else 0x26680999b2660098f0265c8504a240dc7ee018ba834da140c89965260849958069c08877))) else (if c < 355 then (if c < 353 then 0x267208460267c81a7022d246310267901a7122d2035042675c3505267584ff42672499b0 else (if c < 354 then 0x1d6909a121d6889a101d6809a002668c500a1fc4090a718cac90a60d46c351a1402c4ff5 else 0x2691c846a269689829269249820269009a30268809a1a1d6a89a131d68c9a161d6989a14)) else (if c < 356 then 0x26880983b269e09a72260d89833260c498242691079a82698484622694879a0269889827 else (if c < 357 then 0x264009aaa26a689ae026b409ac226acc9aa726a5c9ac026ad09aa226a489aa026a409a80 else 0x10d5c34e60a158998a264289a80268c09a02266d099872641c9a00266cc9982264089980))))) else (if c < 370 then (if c < 364 then (if c < 361 then (if c < 359 then 0x24194501210d68505810e04352a0a228505110e2098402419835270a21c62f016d905010 else (if c < 360 then 0xa144984724184501710d40501a10d4884721fc90633416e4035200a20062f216dac9842 else 0x241009870242e484401fbc897b02411c9977265c0984a241a035220a20884701fc8c34e1)) else (if c < 362 then 0xa1989af026c009af026bd09a74269c09a6026c4084471fbe89b0026bd09877242d097b7 else (if c < 363 then 0x10e609b61241d876a02518094530b21c9b570a25081c20b1809b4716dd09b3010d9c9b25 else 0x26e94289626e50436926a809b8026a4097e026e00773325fc097d02604097c0211409b75))) else (if c < 367 then (if c < 365 then 0x26ac09bd026200988126e54436826f087f30259002c8726ed85ba8259042c8626e902897 else (if c < 366 then 0x2700481b826fc07f322700881b026f9c907026fdc7f3a26fa4907426f80907726b009bd4 else 0x20a449c3320a6c9c3620a609c3420a409c3220a489c3026b449c20270509c1026f909079)) else (if c < 368 then 0x272089c63271c89c53271889c5226c109b00270609c12271009c0026b809c2120a5c9c3a else (if c < 369 then 0x275009d34274809d122740001f7273d89ce6273589cc4272d09ca42726c29bb0a6ac3590 else 0x278c09e24278649e00277c09de02775c29c4277009db0276809d99276009d73275809d53)))) else (if c < 376 then (if c < 373 then (if c < 371 then 0x27cdc9f2727c5c9f0827bd89ee427b549ec027ac09ea427a409e84279c09e6a279409e49 else (if c < 372 then 0x280d8a02528058a00027fe09fe727f409fc927ed89fa427e689f8a27dd89f6827d689f45 else 0x283c0a0e228340a0ca282e8a0aa2826ca08a277c09efa281d49ed3281842ff628140a042)) else (if c < 374 then 0x287e0a1e92875ca1c7286d0a1a82865ca182285d0a16a28540a141284c4a12128444a105 else (if c < 375 then 0x272c4a2e228b68a2c328ac0a2a028a5ca280289e4a2642895ca24a288c0a22228868a208 else 0x28e84a39128e00a37828d98a35628d18a08827824a18828cc0a32528c5ca309131cca2f0))) else (if c < 379 then (if c < 377 then 0x292a0a4972921ca47729180a4582912ca43629080a41529000a3f028f80a3d028f10a3b4 else (if c < 378 then 0x27308a59629614a57629590a5582951ca53629480a51029424a4f529398a4d829314a4ba else 0x2991ca63129880a61629818a5f628d18a09627840a43a29794a5d329714a5b10bfd8a5a8)) else (if c < 380 then 0x29d20a73129caca71b29c1ca6f929b9ca6db29b04a6b029a80a69229a0ca67329988a652 else (if c < 381 then 0x2a0dc4ca02a080a8132a014a7f629f90a7d429f1ca7b329e80a79029e24a77129d84a753 else 0x2a3a0a8d62a318a8b82a2a0a8992a204a8702a198a856297d8a356282a09e2729b04a847))))))))) else (if c < 573 then (if c < 477 then (if c < 429 then (if c < 405 then (if c < 393 then (if c < 387 then (if c < 384 then (if c < 383 then 0x2a780a9d92a714a9b52a680a9922a614a97a2a59ca9592a51ca93a2a488a9142a428a8f9 else 0x278e4a9282aa80a9052aa5c4c732aa00aa712a988aa5a2a900aa372a890aa172a80ca9f0) else (if c < 385 then 0x2ad80ab502ad00ab382aca0ab182ac18aaf62ab88aad12ab00aab62a158a60628d98a0b8 else (if c < 386 then 0x2b1a4ac542b110ac342b09cac132b00cabf02af88abd32af18abb62aea4ab972ae24ab76 else 0x2aad8a86629858a378283209e402ada8ace02b34c4d722b300acb02b280ac902b224ac70))) else (if c < 390 then (if c < 388 then 0x2b3c0aac02a1c0a620296d4a44228e00a30528654a0d92796421002b480ad102b404acf0 else (if c < 389 then 0x1e00ae102b800adf92b780add02b700adb12b6a4ad992b600ad702b580ad502b524ad39 else 0x277a029a70d668ae43291aca1bb08400ae302b8a4ab7a2a4cca6d229150a1ab27c2c9cdb)) else (if c < 391 then 0x298c0a5c0291c0a40728e40a31028710a15628390a06027c509ec92ba00ae712b984ae50 else (if c < 392 then 0x27750359a2ba4429c72b400acd02ae00ab4b2ab40aa942a500a8f82a200a83029b80a6a5 else 0x2bac0ae402ae80a96029c00a490287809f342baa029b72ae50a95429bd0a480287509f24)))) else (if c < 399 then (if c < 396 then (if c < 394 then 0x29c88a4b32882c9f43273ec26502bb40aec02aee8a97329c48a4a4287ec9ed3273ac11c0 else (if c < 395 then 0x2bc2402d901e00aef92b880abd92a600a73429300a21027d4002d027780aee02af28a903 else 0x27de89d092bbc0ae302af90a99b29d10a4d4288909f6b007d0af502bd00af302bc80af19)) else (if c < 397 then 0x2b4c0ac092a6c0a764293c0a32027e0024802bd809cb408400abf82a698a75a29380a238 else (if c < 398 then 0x2bea411c02814024082be40ad402b064a9c029dd0a5d0289009f90038c0af8027310af70 else 0x29458a26627be89d292bf40aec02b540ac252a754a78529414a255281d49d152bf00afb0))) else (if c < 402 then (if c < 400 then 0x2bde4ad702b118a9f629e98a52628cd89fa6274dc248928bd824672b580ac362a798a796 else (if c < 401 then 0x289cc9fc32754caff92bf800e30296ac23d42b600ac562a828a7ba294c0a18427ee89d49 else 0x9194ada02b1e8aa2a29f68a43928a289fda27580b0002be40ad902b18caa1329f0ca5e3)) else (if c < 403 then 0x2a918a6c729550a2a827fec9d892c040adb02b200aa302a100a54028a509fe4275c0a827 else (if c < 404 then 0x276a4aee02b740aca82aaa0a7e8295a0a2b8280209d902c0a426502aa2025102b700ac98 else 0x2b380aa512a000a58028b40a021276c0acc009020ade02b2e0a92b29fc0a57028b00a01a))))) else (if c < 417 then (if c < 411 then (if c < 408 then (if c < 406 then 0x2c1c0b0662c140b0422c0c0362227794ae002ada0aa6b2a068a59028b90a03a27724adf0 else (if c < 407 then 0x2c5c0b1602c540b1412c4c0b1252c440b10a2c3c0b0e32c340b0c22c2c0b0a92c240b080 else 0x2c9c0b2622c940b24b2c8c0b2242c840b2002c7c0b1e02c740b1c02c6c0b1a12c640b18a)) else (if c < 409 then 0x2cdc0b3602cd40b3402ccc0b3202cc40b3082cbc0b2e02cb40b2c02cac0b2a12ca40b287 else (if c < 410 then 0x2d1c0b4602d140b4402d0c0b4222d040b4072cfc0b3e02cf40b3c02cec0b3a92ce40b381 else 0x2d558b5402d4c0b5202d45cb5002d3d4b4e02d358b4c02d2dcb4a027794b4912d21c3636))) else (if c < 414 then (if c < 412 then 0x2d940b6432d8c0b6232d840b6002d7c0b5e62d740b5c02d6c0b5aa2d648b5822d5c8b560 else (if c < 413 then 0x2db84b6d02db00b6b02d680b6a927410b1d12da4001d02c740b6802d9c0b6602c7409c90 else 0x2daecb5b12ded0b7a92de44b7892ddccb7662dd64b7442dcd044442dc80b7192dc04b6f1)) else (if c < 415 then 0x2e1e4b8642dfdcb5d12e140b8412e0ecb8242e044b8002dfc0b5c62dfacb7d12df24a434 else (if c < 416 then 0x2e480b60b2e440b9092e3d0b8a72d7c4b8e42e344b8c02d9c0b8b02e280b5e02e26cb887 else 0x2dc80b9e12e744b9c12e6c0b9a02e640b6202e624b9742e490b6112e580b9512e51cb930)))) else (if c < 423 then (if c < 420 then (if c < 418 then 0x2ea80ba902d900ba892e9d0b9922d8c4ba602e944ba492e8e4ba202e864ba002e7c09160 else (if c < 419 then 0x2db049d000076cbb2027290bb170bc9c2f172ec24baf42ea48b6512eb90bad42eb04bab0 else 0xa7ec2f372e20cbb432ecd8baf02eaa0ba702e6a0b9702e4c0b8f02e2e4b8602e024a430)) else (if c < 421 then 0x2ecc09cd000b80ba112dd44bb312734402e12dd40ba102d5c4b5700d880bb17274009c9b else (if c < 422 then 0x2c400bbc62eedcae2000bc0b4ab01da436392ee80bb902ee00bb702eda8bb5a2edacbb5b else 0x2df40bc302f08004402c480bc172f000bbd72ed6c04102c448bbf40b0e0bbe02ef400400))) else (if c < 426 then (if c < 424 then 0x2f3c0bce02f350bcc02f2c0bca42f240bb402e040b7602d99cbc802f1c0bc602f140bc44 else (if c < 425 then 0x2e200bd742f58003c42c500bd592f504bd302f09cbb6a01140b1332f480ba112f458bd00 else 0x2f140bd802f6d0bdd02f758bdc22f6e0b8862e880b6772d9c4bda02f698bd902f158bd86)) else (if c < 427 then 0x2c58cb9172f990be572f904be302f880be102f804bdf02f5a4bb5b00f50b1532f790b751 else (if c < 428 then 0x2fbc02ef02fb80bed000f80b1802fb18beb42fa9cbe77010c0b17b2fa40be802f9c00420 else 0x11c0b1bb2fddcbf602fd5cbf4001180b1a02fcd0bf202fc64bf092fb6cbb6600fc0b191)))))) else (if c < 453 then (if c < 441 then (if c < 435 then (if c < 432 then (if c < 430 then 0x30140c043300c0c02130048c0002ffc0bfe42ff44bfc02feccbfa02fe40aef42fe1cbf44 else (if c < 431 then 0x2e500b9002e310b8702e080b7c02db58b6a02da4cc0c0302c0c0a430240c080301d4c060 else 0x305c0c16030540c140304ecc12030440c100303d0c0e03036cbb002ead4ba802e6d4b980)) else (if c < 433 then 0x309c0c26030940c240308e4c22130844c200307e0c1e030748c1c0306ccc1a030644c180 else (if c < 434 then 0x30dc0c36030d44c34030cc0c32030c40c30030bc0c2e030b40c2c030accc2a030a40c280 else 0x3112cc43131084b6a02ec40b68331040c40030fc0c3e130f64c3c930ec0c3ab30e6cc380))) else (if c < 438 then (if c < 436 then 0x31480c51031400076400b80c4f031380c4d031300c4b0312acc49031228c47031180c450 else (if c < 437 then 0x2f7c0bd772f4c0bc372f004bbe62ee40bbb02edc0aef431600c57031580c55731524c531 else 0x2ee0001f02c70cc5e43175cc5c9316c4c5a0316409cd02fe00bf542fc00bee62fa80be80)) else (if c < 439 then 0x3039403502d31cc67031980c0d000d00b4b031944c648318d8c62a31858c606317d8b6a0 else (if c < 440 then 0x273c0ba312e0c0b77031b80c6d02e840c6c031ac0c6a031a40c0f000e00b4d031a1cc660 else 0x31d10c69730424bcb600e40b4e131cc0c72031c40c70031bc0c4202f6ecbd402f2acbc9a)))) else (if c < 447 then (if c < 444 then (if c < 442 then 0x27380ba412de04c7c031ec0c6d02dd40c7a031e40c78031dc0c11700c00b4f031d90c750 else (if c < 443 then 0x2d440c774304a4bdd000c40b50132040c80731fecc7e031f40c4302f800bdda2f710bcca else 0x3229cc8903220cc87032180c85032100c8233051c03702d4ac2f40320c0c820304c00360)) else (if c < 445 then 0xed0b56132380c8d0305c003a42d550c8b0305a403302d504c8c0322c0c15900c80b531 else (if c < 446 then 0x2c7c4c97030650bcd101700b1e832588c9553250cc93232490c91432414c8f232364c189 else 0x326dcc7da3071404b02c85cc9b0306c004a02c800c9a232644c981325c8c6f3306a405d4))) else (if c < 450 then (if c < 448 then 0x32840c1f001480b24032828c9f4327a8c1e7016c0b23b32780c1d001680b2203276cc9cb else (if c < 449 then 0x1780b26032aa0ca9632a20ca7632998ca5032920ca3832868c209014c0b25132884b720 else 0x32c40cb0332bd0cae0311009d502ca00cad832b18c5f632ac0c220017c0b27232ac0c210)) else (if c < 451 then 0x3091004f02cad8c6db2f144cb5032d00c23001380b2a032ce4cb2032b98c45927590b291 else (if c < 452 then 0x32ed8cba032e40c2672f38c06102cb6ccb903095c06002cb2ccb8032dd8cb6332d1cc70b else 0x33000c29001900b30032fc0cbe932f40c71330a2405702cbc4cbd0309e405602cb84cbc3))))) else (if c < 465 then (if c < 459 then (if c < 456 then (if c < 454 then 0x27690b33133124cc3033080c72b311909d902cc98c6eb33044cc0730a9cbcf301940b31b else (if c < 455 then 0x33250cc8b30b1cbdb001340b35b33200c2b001300b340331d4cc6233144cc27311e4bd06 else 0x31f8cc2e901240b37133480c2d401200b36633464cd00333dccce033350cccb332dccca7)) else (if c < 457 then 0x30c2405102ce44cdb030be405002ce00cda033650cd80335c0cd6033564cd40334c0cd27 else (if c < 458 then 0x2f6009d242cec4ce2033864ce00337c0c7f0312009d102ce80cde33376cc7c53370ccdb0 else 0x33a40ce86339d0ce6433940c32901550b3d133940c31901510b3c133910ce30337e0c499))) else (if c < 462 then (if c < 460 then 0x312809d702d000cee030d1c06302cfeccef033b80c33701880b3eb33b40cec033ac0cea0 else (if c < 461 then 0x33de4cf6033bc0cc94327d0beb42f150bd142ee98cf5733d1ccf3733c80cf1024340cf00 else 0x274c0b44132100cf9330da405902d0c4cf9030d4005802d080cf8833c18c4b927610b411)) else (if c < 463 then 0x27710b47133fe4cfe033f40c4e7276c0b46b33e80c4d927510b45133f0ccfb033e80c4c9 else (if c < 464 then 0x34200d07034180d0503410029f02b84cd03a340ac363327240ae5734064d00733f50c4f9 else 0x1ba837c52b44c29e00bc24ae5700794d0170a780d0f034388d0d03430cd0b0342a4d090)))) else (if c < 471 then (if c < 468 then (if c < 466 then 0x34600d1733459c4d9001c80d15112fc04dab3451c2a1011140d13034490d1103440c35bb else (if c < 467 then 0x11710d2002c540d1f03478435b601a98d1d200f5836473471c2a3325440d1b434698d196 else 0x349d44d9801b004db23499c2a501fe00d25434908d235348a44de001c244df1348642a10)) else (if c < 469 then 0x34c20d2f70a9c85be034b80d2d434b00d2b513960074013988d2a70a8cc917034a40d280 else (if c < 470 then 0x34ad0d2a4349d0d26034880d21034790d1c034580d14034400d32434c54b5752b4982fb8 else 0x34e0007d034108d37634da0ae4034d4007700f480ae5034d00bd6434cc03d2027740d2f0))) else (if c < 474 then (if c < 472 then 0x3502cd3f834f88c6e82df64d3d634f2407e43446cd05104750d3b034e98d39b0b0c037c0 else (if c < 473 then 0x35264d48602090d177341c431e0351c4d46913680d45135104d43802040d064350a4d41a else 0x342443234354a0d5190d900d50001e40d089353ecd4e23534cd4cb352e8c7c52e20cd4a7)) else (if c < 475 then 0x2010d234342c42f440ca40d5763558c4df03554007f034280d548354e4bb5001e90d1f7 else (if c < 476 then 0x34380d5e03576407c434a08d0d10cb40d5c1356ec2ef0136c0d5a001ec0d0c035658d589 else 0x34cdcd18035940d64112fc0d6303589c084034b20d0fb0cdc0d614358204e64357c00830))))))) else (if c < 525 then (if c < 501 then (if c < 489 then (if c < 483 then (if c < 480 then (if c < 478 then 0x35c80d71035c08d6f935b80d6db35b28d6b135a80bb112b8d0d69735a10d67935984d489 else (if c < 479 then 0x35690d5813556cd5313542cd491350c0d3c134e002f3134d68d30034900459035d00d730 else 0x35ed0d7a435e50d78735ddc02f700818d69434d2c459035d8cd75308d90d621357c0d5d1)) else (if c < 481 then 0x2f810ad4003900d81336000d7f035990d4442b4c0d1990c080d7eb35f64bbb02b8d0d7c4 else (if c < 482 then 0xc7ac31d201c80ad6036180d8540a84028f034f40ad5b3612cd83b0476006bb01b9cd823 else 0x2e38032320c89c06a9359d4d4572b600d1a03622c2a3a25600d7f53528cad760c094d877))) else (if c < 486 then (if c < 484 then 0x2b6c032930ca1c07002dd50ada036300d8b60a8605bb036080d5402b660d8a1362600e48 else (if c < 485 then 0xcd8007492b780d8e40a8c07f4035784add30cb4432c301b0cadc0363502a5824380d594 else 0x3642cd96136568d94b3642cd930364a8d91b3642cae00363d02a7411a00d6312b7c03371)) else (if c < 487 then 0x367c0d9e03676cd9cb366c0d9603656cd94a3642cd9a03666cd98b365c0d931364acd91a else (if c < 488 then 0x36ac0daa036a40da8436944da45369c0da60368c0da2736940da44368c4da2636840da00 else 0x36d50db2136c6cdb0636d00db3036bc0daeb36b5cdb2036c68db0736bc4daea36b58dac0)))) else (if c < 495 then (if c < 492 then (if c < 490 then 0x37104dc3b37084dc1137004dbf836f84dbd236f2cdbb236e84db9536b00db8036dc0db60 else (if c < 491 then 0x37080dc1036e80db9436f80dbd337300dcb037280dc9037200dc7037180dc5037000dbf9 else 0x37500dd3037480dd1637304dcb137284dc9137400dcfb37380dcd637184dc5137100dc3a)) else (if c < 493 then 0x37714da1a36828d9fa0f480ddb037680dd9037590dd5437600dd7037510dd3437580dd50 else (if c < 494 then 0x37980de5437910de5037900de3a378a8ddf537794de1a37800ddd437728ddfa377a8ddd0 else 0x37cc0df2a37c68df0237bc0deea37b6cd90b37b00debb37aa8d90b37a40de8a379e8d90b))) else (if c < 498 then (if c < 496 then 0x38040e00037500dff037f80dfd037f00ddc037ec0dfaa37e68df8b37dc0df6a37d6cdf42 else (if c < 497 then 0x38300e0b037f94dfd537f14ddd00f500e0a438240e080381d0e06038140e044380c0e020 else 0x38668df4238600e17a385acd90b38540e14a384e8d90b38490e11438410e0f438390e0d0)) else (if c < 499 then 0x389c0dde038980e25a38928e23a38880e21b38828d90b387c0e1ea38768e1c2386c0e1ab else (if c < 500 then 0xf580e33038c80e31038c00e2f438b80e2d0381c0e2c438040e2b037580e2a038a40e280 else 0x3871ce3b037c24e3a0365e8e39038e10e37438d90e35438d28e29a38a28e27a382c0ddfa))))) else (if c < 513 then (if c < 507 then (if c < 504 then (if c < 502 then 0x39100e050390d0dd8039080e41039000e3f037800e3e038f68e3c438724e3b437c1ce3c0 else (if c < 503 then 0x39280e49039228e41039000e3f0378683d80391c0e46039140e2e439110e054390c0e2e0 else 0x388d0e51038f68e4f437e10e500388c0e4f037e00e4e0366e8e4d039300e4b439290e4b0)) else (if c < 505 then 0x395d0e46039600e09439590e320395c0e09039580dda039540e540394e8e52a378a8e504 else (if c < 506 then 0x39710e5d0396d0e5c0396c0e5a039500e53a394a8e48a38350e0d0378e83da039640e324 else 0x39b24e6b039a8ce69439a18e670399a4e6543991ce6303988ce61639800e5f036400e5e0))) else (if c < 510 then (if c < 508 then 0x39e90e79439e10e77039d80e75039d10e73039c80dd4039c54e70639bc0e6e036b60e6d0 else (if c < 509 then 0x3a0acd9003a050e80439fc0e7e039c18e6f039b80e0e437900daf536b80e7d039f10e7b0 else 0x3a3c0db023a380e8db3a300e8b33a290e8903a200e8703a180e6833a140e6233a108e830)) else (if c < 511 then 0x3a700e9b03a680e9903a600e9743a580e95039e40e94439cc0e93037580e92a3a440e900 else (if c < 512 then 0x3a8e8ea203a868d97a3a810e9f43a790e9d03a440e9003a3c0e7e038d50de5036ca8db10 else 0x3aa40ea843a9c0e8743a980ea543a900e6673aa50ea803a9d0e8703a990ea503a910e669)))) else (if c < 519 then (if c < 516 then (if c < 514 then 0x3adc0eb643ad80eb503ad00eb303ac80db3a3ac40eb003abc0eae73ab40eac03aac0eaa6 else (if c < 515 then 0x39240db4a3af80ebd03af00ebb03a590eba439dd0eb943a580eba039dc0eb9037600eb80 else 0x39a98ec743b180ec543a2ccec4039a8cec313b080ec11366e8ec003afc0eb403acc0eb20)) else (if c < 517 then 0x3b3c0dda03b3a8ecd03b300ecb036d44eca03b244ec703b190ec503a2d8ec803aa98ec44 else (if c < 518 then 0x39fc0e5a036da8ed503b500e9a43b410ebc03b4c0ed203b440e7b43b3d0e9a03b400e7b0 else 0x3b710edb03b690e6c93b668ddb036aa8359a3b600ed703b580ecd03b300ecb03afc0e7f4))) else (if c < 522 then (if c < 520 then 0x3b7c0ede43b740e8d13b880ee103b800eae73b700edb43b680e6c73b7d0ede03b750e8db else (if c < 521 then 0x3a700eea039f40ee903ba00ee703b980ed603ad40de6036e28db7a3b940ee403b8c0ec91 else 0x3bbc0eee036400eed03ba00ee703b980daca3b540eec03a710eea43af80eeb039f50ee94)) else (if c < 523 then 0x3bf90efd03bf00efb03be80ef903be00ef703bd80ef503bd08ef303bc80ef103988cef00 else (if c < 524 then 0x3c300f0b03c280f0903c200e9d036e44f0703c180f0503c110f0303c080f0103c004eff0 else 0x383d0dba53c600f1703c580f1503c500f1343c480f1103c400f0f439cc0f0e038040f0d0)))))) else (if c < 549 then (if c < 537 then (if c < 531 then (if c < 528 then (if c < 526 then 0x3bd20f2003c7dcf1e03bd08f1d03991cf1c73c6c0f1a036400f1943c280f0903c200e364 else (if c < 527 then 0x3ca80f1003ca40e7503ca00e0303c9c0f2603c990f25036edcf2403c8dcf2203c848f1e4 else 0x3cc00c9b43cc10f2603c990f25038400e10436f00f2f03cb80f2d03cb00f1043ca50f2b0)) else (if c < 529 then 0x36f64f3a03ce40f3803cdc8f3603cd40f3403c7dcf3343be10f3243999cf31037c1cc9b0 else (if c < 530 then 0x3d190f4503d100f4343d080f2b03d040f1203d000e7703cfc0e0503cf90f3d03cf00f3b0 else 0x3d340e6863d300df493d2c0f4a03d240f4843cf50f3c43ced0eb603a010e4a036f94f470))) else (if c < 534 then (if c < 532 then 0x381c0f58a3d5c0f5603d540dbf63d500f5353d480f5163d400f3543d3d0ef483d380efc0 else (if c < 533 then 0x3cc00e37438440dc0a3d800f5f03d780f5d03d0c0f5c03c400f5b03c510f5a439e40f590 else 0x3c004f6903da10f67439a8cf6653d940f64037e00f6343d890f0b03d850f5743d590f554)) else (if c < 535 then 0x3dd90f7503dd10f7303d458f7203dc40f7003cde0f6f03db90f6d03c848f6c03dac0f6a4 else (if c < 536 then 0x3e050f2d03e010f1603dfc0e7b03df80e0903df54f7c03dec0f7a037054f7903de00f770 else 0x39b1ce0a00dba8f8503df00f7b03de80f484326d0e5b037094f8403e0d0f5e43e080f450)))) else (if c < 543 then (if c < 540 then (if c < 538 then 0x370c0f8f03dd80f8e03e340f8c43d4e8f8b03e280f8903ce40f8803c8dcf8743c100f860 else (if c < 539 then 0x3d810f9903d1c0f9843cbc0f9703c600f9603e540f94039f40f9303e480f9103e400e120 else 0x3cd40f9f03be00f9e03a1c0f9d03871cf9c03e6c0f9243e450f9043a050dc453e100f9a0)) else (if c < 541 then 0x3eb00e9603eac0e2e03ea80fa903ea00fa7037168fa603e940fa403e8c0fa243e840fa04 else (if c < 542 then 0x3ea40fa803e9c0f4903a790e4b0371a8fb303ec80fb103ec00faf03eb90f4303eb50f120 else 0x3ef40fbc03eec0fba03e840fb943bf10fb903bf00fb803a240fb7a3ed80fb5a36400fb44))) else (if c < 546 then (if c < 544 then 0x3f140faf03f100f1443f0d0f1403f0c0e9803f080e3003f040fc003f010fbf0371e8fbe0 else (if c < 545 then 0x3c004fca03a2ccfc90388c0fc003f010fbf03d850f61038e00e38437228fc803f1c0fc60 else 0x3f540e3203f528fd303f480fd1037268fd003f3ecfce43eec0fcd03e8c0fcc43d44cfcb0)) else (if c < 547 then 0x3e140f1943a7d0e5c0372a8fdb03f680fc603f650fb103f600f5e03f5d0f1603f580e9a0 else (if c < 548 then 0x3f800fa503f7d0f53a3f780f0443f740e8db38cc039da3f700fd303f480fd103ed10f624 else 0x3fa10f1803f9c0e9c03f980fe503f900fe303f700f0c038e40dcba3f880fcfb3f850fbd0))))) else (if c < 561 then (if c < 555 then (if c < 552 then (if c < 550 then 0x3fb28e3da3f940fe403f8c0f6343e6c0ea0437328fdb03fac0fc803fa90fb303fa40f600 else (if c < 551 then 0x3fc80f3723fdd0ff603fd50fa303fd10ff303fc90f3783fc40ff003fbc0eaa63fb88fed0 else 0x3ff40ffc03adc0e5d039300dcd23fec0ffa03fe40ff803fdc0ff643fd40fa343fd00ff34)) else (if c < 553 then 0x4014100403ec5100343d15100243ec4100303d14100203af0100103918100003ffc0ffe0 else (if c < 554 then 0x3ce4100803e94100703ce5100603ab9ce4700ed80ffe03ff40ffc03d290f4a03b5c0dcea else 0x3d1c101043af8100f04038100d04030100b040280e4d0373c100903fe0100843e9510074))) else (if c < 558 then (if c < 556 then 0x402c100a03ffc0f4b43d2c0eed03b000dd0a4014101203ecd101143d1d101003ecc10110 else (if c < 557 then 0x40590fcf1405c0ff8040550f76040580fcfb40540f76440500ec91396403c60404c100c0 else 0x40751005040780f84440710fdb040740f84040700ed50406c101a040641018039780dd12)) else (if c < 559 then 0x40941024b408ed022b40869020b407ed01a0406410180404c0f9c43e700ed80374a8fdb4 else (if c < 560 then 0x40b5102c740add02a740a5cb5742b9c0aea92b9810280409dd02692d5d0b0360a6d829a6 else 0x2ba0102550bc00ae5040e51038440ded036740d51034140cd1032440c51030040bed02e1)))) else (if c < 567 then (if c < 564 then (if c < 562 then 0x41151044334c8104344108d041412d104b3440989040040fe903ea40f6903cb40ee903aa else (if c < 563 then 0x414e9052b4146d05044101431a4413d104e44134d04c3412cd04a0412410480411d10464 else 0x41841060b417ed05eb4176d05cb416ed05a0415d43f44416410580415c1056b4156d054b)) else (if c < 565 then 0x41b4106ca41ae906ab41a69068a419e90660419003f80419410640418d106150fd810624 else (if c < 566 then 0x41e11077441d91075041d01073041ca5071341c10d31941bc1042041b844cf1133850270 else 0x42041026839c0108042902507f041f8507c10ff0107d041f0507b041b683fa041e810790))) else (if c < 570 then (if c < 568 then 0x421c108604210102a634a9108504210108342a3e108262ef40e7042f591044640a58d210 else (if c < 569 then 0x424410900423d108e04234108c029a9508b142290e6f640ad8d14042240e6f0422189ec5 else 0x34cc1070840b18d1c042641027642601097028559096b425410930349810940424c10920)) else (if c < 571 then 0x2774023f040a050a20427c10a1034bc10a00427c109e04274109c02ad2d09b6426910980 else (if c < 572 then 0x42ac0a40742a8104f012cc036ea42a410a9034d0102d542a010a70429810a54429010a30 else 0x42ed10ba742e410b8042dc10b6042d410b4042cd10b2842c410b0442bc10ae442b410ac0)))))))) else (if c < 669 then (if c < 621 then (if c < 597 then (if c < 585 then (if c < 579 then (if c < 576 then (if c < 574 then 0x431810c50431110c30430804b404140104604114102e0430410c0042fc10be442f410bc0 else (if c < 575 then 0x435010d30434810d10434010cf0433810cd0433110cb443280d210432410c80411c10c70 else 0x437010db0436810d98436010ae4435c0a8f84164039d5432010d6043540bbd040be83d44)) else (if c < 577 then 0x43a110e70439810e50439110cb0438c0d2a0438810e10416810301438010df1437810dd0 else (if c < 578 then 0xdba90e1043c010ef443b910ed442191071541629048040c683d6043b010eb043a810e94 else 0x43f010fb443e810f9043e010f7043d810f5043d010f34436490f2042c890f1027b1d0620))) else (if c < 582 then (if c < 580 then 0x441c11060441411044439511030433411020345011010440010ff443f91063040ca90fd0 else (if c < 581 then 0xed8110044440110f44439110d44229107254125103350f50110c0442c110a0442411080 else 0x44641066040d011180445d1116044541114043d911134436c1112442d81111029a950650)) else (if c < 583 then 0x4254103550f6011220448411200447c111e04414111d4439d111c0433c111b03498111a0 else (if c < 584 then 0x44b010ba744ac112a044a40a15644a1d07a01339c39da446411270449811250449011234 else 0x44e41138b44dc1136044d41115044d11133044c910fa444c41130444bc10dd044b8112d0)))) else (if c < 591 then (if c < 588 then (if c < 586 then 0x4510114304509114104500113f0133dd13e044f4113c041ec1074641cd9036644ec113a0 else (if c < 587 then 0xf58114d04530114b0447c114a044241149043a411484434411474347011460451410756 else 0x445d5153143f151525437c1151142f9515052ad2907d10f1851450453c114e442691037a)) else (if c < 589 then 0x4484115b0442c115a043ad11590434c1158434bc115704558107e040e11155144e291541 else (if c < 590 then 0x458c1162442b811614458011560457c115e0323510a204129103950f68115d04530115c0 else 0x4334116c03c99d16b042ca116a045a110ed0412d90cb445a411680459d11664459511644))) else (if c < 594 then (if c < 592 then 0x41099173045c910ba945c4116f0448d10cf045c0116f045b810b6045b40f2674435104c6 else (if c < 593 then 0x45f1117b445e91179045e11177442f81176445d411734453910d5041da104d6434411740 else 0x4366118104608118104358104e04600117f0435002550410c117d4323510d3045f8117d0)) else (if c < 595 then 0x462c10dd0462991880439d11890462011870436c1184043b810e54461811855461011830 else (if c < 596 then 0x464410f0443b103f30463c10eb44640118f0463810df1463010ef041de10e904634118c0 else 0x466c119a0466411980465c10fa4465811950464d11240441411944464c1192443d811910))))) else (if c < 609 then (if c < 603 then (if c < 600 then (if c < 598 then 0x469411a40468c11a20468410fc44680119f04674110e441e2110904678119d044f0119c0 else (if c < 599 then 0x46b81115046b591ab446b011ab0443c11aa446a5110c40fd411a70442c11a80469c11a60 else 0x46e41126046e011b7046d911b5046d011b30445d11b2046c611af04494111f046c011af0)) else (if c < 601 then 0x44f4114c0470011bf046f81138b46f591bb046f011bb0449c112200fdc11b90448411ba0 else (if c < 602 then 0xa7011c204708115f0457403fb14704113e04704114f041e5914d00fe4106f646fc115e0 else 0xdb811ca24724d1c83471cd1c624714d1c422ba4c36672ba582fa0470c09ca10a7109cab))) else (if c < 606 then (if c < 604 then 0xe7411d42474c91d22474491d03473c91ce4473511cc40e0002ff7472d04bd42810c2b54 else (if c < 605 then 0xf09c4ca04769c4cb9132dc3b60476411d83475c03b07131cd1d602a9c44c84135811d50 else 0x478010d400dba82b50477c11de7477983d02135c91dd012aec4aba0f1811dc7476e51db7)) else (if c < 607 then 0x47a511e84479d11e60479510ec00e7691e441359d1e30046c11e200f51104f0473011e10 else (if c < 608 then 0x47c911f1447c111ef447b9110c40dba91ed412f411ec0103803d64416411eb047a811d77 else 0x4535039d51321d1f40103003d80419411db0448903b60132c11f340ff403d40418911cd0)))) else (if c < 615 then (if c < 612 then (if c < 610 then 0x8f691f600f3003da041f411de5457503c6012add1f5047a811d5a101003d6041e811d81 else (if c < 611 then 0x472c0240a0f480d3500f440d354471291fa047e011f9047dc11f8447dd0077001dd11c37 else 0xf5411d971010040e44759c402a0f5011fd047cc11e300f4c11ce047f111fb00ff5011b0)) else (if c < 613 then 0x4774841000f6011fe047d011f440f5c11dc01030040c44768040b047ac03d6047d411ec4 else (if c < 614 then 0x4351c2b5748000c74947fc10f1a0be88a5a0272a03da047d811f640f6411df20f3003cc4 else 0x4836920c0482e920a048255208343edc4c73481c10fa7481812054481012034480a92010))) else (if c < 618 then (if c < 616 then 0x43ddcd361485cd216743d9d2154485112132484810f200bfdd211442c81210a483ed20ea else (if c < 617 then 0x489012230488a522164881121f44879d21db4872d21b348688c76b48645218143fe51e07 else 0x48bd122e448b690d9748b0922b043e5d22a0485cd229743e1c4ca048a1d2273489a92253)) else (if c < 619 then 0x48e9d239348e01237048da5235548d15233048c88c75548c690fe7478650f3734de92307 else (if c < 620 then 0x490810f5748a8123094904122d543d1c4c734900123f02a9c5227748fa923d048f1d23b4 else 0x47fc858104934124c0492dd24a043f484d72492410fc0492252477491a52457491092437)))))) else (if c < 645 then (if c < 633 then (if c < 627 then (if c < 624 then (if c < 622 then 0x4960125704959d255049501253249481251a4942924f049388c77a4908122b04849d2086 else (if c < 623 then 0x900925f048b61219616a0125e74401c58174974123184861811a04970125b2496a92592 else 0x486ccc11049380d38048c8521a048001265249909263049881261049808030701f40a5a0)) else (if c < 625 then 0x49a69251048d4121d4484c00ed049a0d2670494012340487112090166c12660493c12334 else (if c < 626 then 0x48e1122044829059ba481d05990160412374487d126c04974123604878126b049aa811a0 else 0x49bc126904950123a9488a5214949ba926d703b69211009029253048e552215499e92520))) else (if c < 630 then (if c < 628 then 0x49c405a874900059f2495c123d4485cd27024958123c448a412280167c1255048ec12230 else (if c < 629 then 0x496c1227b489d125a04928123e148981249009009259048c2d2254497dd2580490412240 else 0x49f9d27d627bd127c049ed9273b49e91279949e05277049d81275049d09273027b452726)) else (if c < 631 then 0x4a30128b24a28128944a201287a4a18128544a10128304a0812814410410aa04a00127f5 else (if c < 632 then 0x4a70129b94a68129904a60129704a58129504a50129324a48129104a40128f64a38128d8 else 0x4ab012ab54aa812a904aa012a704a9812a564a9012a304a8812a1a4a80129f34a78129d9)))) else (if c < 639 then (if c < 636 then (if c < 634 then 0x4af012bb04ae812b904ae012b704ad812b504ad012b364ac812b104ac012af74ab812ad0 else (if c < 635 then 0x49a012c704b1852c5042a80d8102be212c460de912c314b0812c104b0012bf04af812bda else 0x4b5412d404b4c12d2049ec127404b4412d0a4b3d52ce04b3452cc04b2c12ca04b2412c80)) else (if c < 637 then 0x4b8812a404b8412e004b7c127604a9012de04b7412dca4b6c12da04b6412d804b5c12d60 else (if c < 638 then 0x4b49927c04bb812ed64bb112eb04ba8d2e974ba0d2e764b9992e544a9192e404b8c00c70 else 0x4bec12fa64be592f864bdc12f634bd50c7b94bd112f344bc912f104bc012ef14b5192e26))) else (if c < 642 then (if c < 640 then 0x4c28530904c21930774c18d30544c1012d364c0c130264c05130004bfcd2fe74bf4d2fc6 else (if c < 641 then 0x4c55131474c4d531204b80131104c4012ef04b59d30f14c3a130d64c31130404b55930b0 else 0x4b6a931f64c79131864b65931d04c71131b64c68131904c6012d804c5d931644c4052d76)) else (if c < 643 then 0x4cb1132b04caa5329931b6532804c9c091004c98132514c90532312dc81322a4c8413200 else (if c < 644 then 0x4ce1133744cd8133504cd0133304b70133284cc5933044c80d2f004b6d932f04cb8132d1 else 0x4cfd933e64cf4133c731f1d33b4281112de312d0c4b33317d133a64ce5133334bc412dd6))))) else (if c < 657 then (if c < 651 then (if c < 648 then (if c < 646 then 0x4d24c46a311a4ca0442ad8134804d1c134644d14134434d0c134224d04134094b9400c53 else (if c < 647 then 0x4cc0132164c78131934c581311b4c3012f404c1412f204b9400c7327bc127514cc8134a4 else 0x4d34108a0035c128b04d31934934b9412f304b78c46f312d4d30f94d2e49ed94ce413346)) else (if c < 649 then 0x4d49d35344d490be072f810bdc027b652f5049d8d27614d44135194d40134f94d3a49ed0 else (if c < 650 then 0x3bc128d04d64135804d5dd35644d56908a72f76c0d804a32935440b0e134f04d3813537 else 0x4a3c136104d82535f04d78135db4d70535a74d4a40f004a3acb76b4d390ba414d6c135a0))) else (if c < 654 then (if c < 652 then 0x4da4536804d9dd36604d96536414d4ece7f703e0129014d8c134f02de2d362439fc00f74 else (if c < 653 then 0x3cc129304dc8537164dc1536f34db5c0f604a48d36eb4db400f504a46d36c74dad136a7 else 0x3c4129564dec137a44de4137804dde537604dd59373b2f3200f404a518b7204dd013730)) else (if c < 655 then 0x4e15d38494e0c538204e05c9ce02732538034dfcd37c44d4d00f204a58d37e04df4937c0 else (if c < 656 then 0x4e39938d84e31938b64e29938794cf5129864e248d1d04e22d3870310c133c04a5ed3864 else 0x4e5400e504b18139494e4c13910035812c501499c37a44e4813910035410aa04e40138f8)))) else (if c < 663 then (if c < 660 then (if c < 658 then 0x4e74139c14e6c535c04d48533e04ca4530602ddc139a04ca80ba404e64139804e5c13960 else (if c < 659 then 0x2de013a7a4e9ed3a6b4e9593a404e55c0e604b1d849004e8c13a204e8413a004e7e939e1 else 0x4eaed3a804eae93aa04ea853a904ea0535304d4c533f04ca852f602de0533f14bd8532a0)) else (if c < 661 then 0x4ebcc0ec04b28d3b134ec013af003ac12c904eb993aa4494500ee04b2193ad04eb193800 else (if c < 662 then 0x4ee800ea04b3193bc04eed93ba003a412cb64ee593b804edd13b604ed413b404ecc13b23 else 0x4f14d3c454f0d53c244f0590a2703a112ce612bc13c084efc13be0428800e704b3413bd6))) else (if c < 666 then (if c < 664 then 0x4d2c130704b7c53cd04f3013cb04f28134e04bf813c944f2000d904a65130334f1d13c62 else (if c < 665 then 0x4a6d13d384f4993c884e74c0da44a6993d104f4013cf74f3a53a844e91d39c44e6d0c7e4 else 0x4e7a4c7d94c3dd32b04b8052f704b8193d664f5853d514f29d34f74c3c13d44443400e10)) else (if c < 667 then 0x4f6400df04a7413d804435d3aaa0388129c04f5c134f031f513ca04e7913aa44eaa53a94 else (if c < 668 then 0x4f7680de04a8193e004f7c44b704f7813dd00374129f04f70d3d9a0380129e34f6cd3da0 else 0x4fa000dc04a8a93ea04fa413e80036c12a104cca13e764f9a13e564f9193e304f8a13e16))))))) else (if c < 717 then (if c < 693 then (if c < 681 then (if c < 675 then (if c < 672 then (if c < 670 then 0x4fe413f804fde93f604fd413f404fcc13f294fc413f064fbc13ee04e4813ed04fb1d3eba else (if c < 671 then 0x4cd6933104c88131f04c68131704c49d30d04c2012f804b9812e3049f4127724fec13fa0 else 0x49a653a504e58537f04df6d37504dd0936f04db8136404d8a135d04d6e0d8202be6133a0)) else (if c < 673 then 0x5011d4030500954010500013ff04ff813fd04ff193c104ef853bd04eec13b204ec013ae0 else (if c < 674 then 0x5050141305048141115042140f0503a940d05030140b0502814090502194070501814050 else 0x506c141a0506414180505c14160505413ab04e7c138a04e200c7f04b98134904be412e10))) else (if c < 678 then (if c < 676 then 0x4f5253d204f24139304e48135504d3492fa0508a942105080141f61499d41e05074141c0 else (if c < 677 then 0x4a94142705098142594b9800c504a8c14248508d93eb04fa693e104f78d3dc04f6a53d80 else 0x50b4142c950ad942a050a1d3fd14e7a53a0b040012a614f28132ab50a4142804ff000ff0)) else (if c < 679 then 0x50cc1400603ec12a9650c81431750c0d42f050b813ff303f812a8350b813fe303f412a73 else (if c < 680 then 0x3e812ac350e014370500800f904aac1436950d65434050cc140164e84c0fc04cb112aa6 else 0x50fe143e850f6143c050ec091c050e8141514e8ad34004ab4543904e6ad4377500cd3ce0)))) else (if c < 687 then (if c < 684 then (if c < 682 then 0x4abc14431510a143a75059934144ab9944185100142a74f2813cf04d7a534e44c2414380 else (if c < 683 then 0x4ac4544c7512c144a7512414487511d144615115d444b5014c10c04ac0d44405010010b0 else 0x515414544514c14520514414509513c144e05135d40764ea0c10a04ac9944d0501841090)) else (if c < 685 then 0x4eac134204ad5145935162d45734cfe9456050258c7d4041812b46515814080041412b30 else (if c < 686 then 0x5184140a6041d12b765181145f75178145a85061934344ad9945d05171945b4516814174 else 0x51a8140c3040c12b9351a414680519c14660519414646518d146245184140b6042112b86))) else (if c < 690 then (if c < 688 then 0x51be146b65069934544af1946e651b6546c051ac141904d1012bb051a8140d3041012ba3 else (if c < 689 then 0x51d09473051c8141b64d1812bf64ecc14713503d810204af9947105038010104af414708 else 0x4bec1438051e89479251e09477051d80450051d4141d34d2012c1351c8141c64d1d12c06)) else (if c < 691 then 0xd6ec110003628ce040df15475450798ab644b09947c851ec134f04f41d38034e01934f4 else (if c < 692 then 0x52041480012d4125c034e80aebb51fc147e351f6d2de0413c0d0143400128c04404cd390 else 0x492c05c40522803f64413c00c88340405c4052241488a521c1486b521414844520c14824))))) else (if c < 705 then (if c < 699 then (if c < 696 then (if c < 694 then 0x5255c4b6b4441d1e294419cd3bb5250149305248149105240148f05239148d15230148bb else (if c < 695 then 0x528994a155281949f45278149d75270149b7171c149a94eb45499052620c811525ed496b else 0x52b414ac052ad14aa152a6d107713ac0111052a014a70529814a50130114a41528c04ecb)) else (if c < 697 then 0x440a43740046000e20516e837e54425c2bb01fd414b0452be524c44421c5c7052b8148a9 else (if c < 698 then 0xb000953052d814b5952d1d104713d90116913dc50cd70b08045f052cc14b204a7014b10 else 0x5224110ab01d4c1134048610e570af8c911052e514b8052dc1103b13e8c114413ee11057))) else (if c < 702 then (if c < 700 then 0x52fe94beb52f612fe34e6a14bc9493514ae011ae510c712f6510b70a9d8299052ec14bab else (if c < 701 then 0x531dd4c66047d14a90520584900186c14c58531044ec0530c14c295304411e0520254c09 else 0x520d85284533c54ce80df914cd9049814950520814ccb532c94ca35326d30f34cfe94c84)) else (if c < 703 then 0x535994d56049514b46521586290535054d3613dc14d20049014840534614d06049d14b11 else (if c < 704 then 0x48014880536c14da6048d14b73525814876188414d9b536044b7013ec14d70048814860 else 0xc6407e601bd01107537514de6048514893525c1489612bc03cd05378d4dd0048414dc4)))) else (if c < 711 then (if c < 708 then (if c < 706 then 0x5395924f4526414e460a84029303048124e034f054980538cd4e23538514e04537d127a5 else (if c < 707 then 0x53b094eb0539e910e752ac14ea453a504c0053a014e745304125040b1014aa0182c14e61 else 0x5335d4c605308046f0478c0d3d02bb2d4af011b814f1053c014ef053b854ed14d24125d0)) else (if c < 709 then 0x4974149a053cd14f2b031a14ec0443c046e012c9d4de05372d4da0535ed4d50534914d00 else (if c < 710 then 0x46254c30494e14ad053d5c2bb0247414e81531cd252452b014f43182c461bb186401110 else 0x4955149c053e414f890b0805c304eb814d104952549b053dd94f604c5680ee614a085250))) else (if c < 714 then (if c < 712 then 0x527c06211187901143495d149e053ee54fa80b000952053591256452740629318a001160 else (if c < 713 then 0x53f402a70114414dd1496814a100f3443614044e52594528014fc00af807fc0536c52580 else 0x541a550595411d5030540a5501952f2513f74792512975401d4ff053f84b7d9496d14a20)) else (if c < 715 then 0x545415147544d151275445d5100543e550e05434150c0542e550a74ed055090542055071 else (if c < 716 then 0x5479951d65401d51c83214551b244a9cb7d90be8151a0321049cab5465d5185545e55164 else 0x4ecc0aa70321015281133c44ce1549c152615494112b75490152305488152105481151f1)))))) else (if c < 741 then (if c < 729 then (if c < 723 then (if c < 720 then (if c < 718 then 0x54d51534054cdd532054c59530054bd952e011d4152d054b2152b054aa552934e6a4c6e9 else (if c < 719 then 0x54f9148e04bf9953d054f0153b654e81539054e015374547c04c6044a050ec7135815360 else 0x4ede95480551e9546a5515954483222154385509954105501914274795d132734fa153f6)) else (if c < 721 then 0x44cdc2ff0555004be02812d55385549555165540154f85539d54d05532554b6552915490 else (if c < 722 then 0x557c155e05574555c044d2555b45569155945560153755481153f3555e55567555592fe3 else 0x55a414bd84501d1e6744b1cd3f855a19567055985565042e815640558c15620558515601))) else (if c < 726 then (if c < 724 then 0x55dd9576055d61574055cc1572055c65570655bc156e155b4556c655ae0c861541a156aa else (if c < 725 then 0x5606558094ed6d57f955f8112d90bfc157d44ecec4fe45465957c555ed957a455e615787 else 0x5630158b056291589156201587156185585044b9d5840560c15820556015381548415683)) else (if c < 727 then 0x4ee055941564cd592832245591b5642d4beb450dd1e7944d5cd40b563cd58e04455d58d0 else (if c < 728 then 0x563cd5a1744d9c4ca05680159f35679559d65671159b45669d5993566015970565815959 else 0x56b055ab156a855a9556a015a71569855a51569011377568c15a2056081559454e455220)))) else (if c < 735 then (if c < 732 then (if c < 730 then 0x56d055b3056c88c871564695b1756c294bfa4505d1e8944bdcd41a56bc95ae456b690dd6 else (if c < 731 then 0x131cd5c002a9c559f256fe95be056f5d5bc456edd5ba356e415b8056de53b6156d915b51 else 0x571e15c60571455c4044c5d5c305688158305569153a1548c15af8570815c1b56b551307)) else (if c < 733 then 0x573e0c8a6573a54c094511d1e9944e5cd42954d815cd044e015cc8572e15ca8572595c82 else (if c < 734 then 0x44e984d72577015db4576915d905761d5d745759d5d50575015d30574a53b97574595d00 else 0x1eec15e30578815e10578015df15778113b7570c15a305610155b454edd524054d855dd4))) else (if c < 738 then (if c < 736 then 0x57a1d5e70579a53ba1579415e48322c55de0571015a405614155c054f055250546c95019 else (if c < 737 then 0x124407bb057c815f1156c295403540a47e1057c015ef057b855ed057b015eb057a9d5e90 else 0x57e815f9057e255b1955f815410541255f7457d915f5457d115f3413f91145755a415030)) else (if c < 739 then 0x550c950690f3c15e2057f815fd057f055fb1573a55ada5642d56aa5508d5292541646f60 else (if c < 740 then 0x5810d6039580a560135800c03290204d51a3091a55fe1578855ff057fc5591a5646d5068 else 0x564cd56c65514d52b15401cc15057900d430573c15b215648156b05510552a0547016053))))) else (if c < 753 then (if c < 747 then (if c < 744 then (if c < 742 then 0x56d015a505618157f655b4155d05555d54645498151d7541c06f80581855e50574015b30 else (if c < 743 then 0x56d41594055b815474542006c6044a05607057fc15fb057e194c10351015df0571415c10 else 0x5429d60c0582c160a1582404be047a9d5b6455bc1548447549509012441608057c415d17)) else (if c < 745 then 0x574815b70565415710555c152c0542c160f95838d60d9047a555491664113c755c195567 else (if c < 746 then 0x5525150d0584415e20581c55e70574c15b8056581572054fcd52d1543016100579814c20 else 0x58481608157c815d4056e41598055d0154a011d4550e01b1847e1057fc113d7565c15730))) else (if c < 750 then (if c < 748 then 0x57e514c3047adcd451578015c605698558715601d57585578153d1549c151e6543e56110 else (if c < 749 then 0x3a5957d70919c7bb0575415ba35664d5776552cd52e15445d13e755d815100578855fc1 else 0x55a1954d454c055134585413bb057a015d6056ec159a05604154c054bc15120585196137)) else (if c < 751 then 0x585c55ea0576015bd05684157805539153105450161675681c7d7757a415d7456f1159b4 else (if c < 752 then 0x55e91550454cd95164586006f60570107d7157ac15d9056f8158f355e6154f254c855150 else 0xf3c15dc0100895ed0576d15af25675957b65544d5341545e55fd057b015da45709159c4)))) else (if c < 759 then (if c < 756 then (if c < 754 then 0x567cd5196554c953615465d611057f815ee0577515bfb5679157c4554ad5354546116190 else (if c < 755 then 0xea6d61bb4165cd0193401d61a0451a8d460136488ca005bcccfb8136a55ef054d8159f2 else 0x13adc8c64587dd61e713b0d5e14202c03fa94165cd017202c161d057c114c40351c161cb)) else (if c < 757 then 0x4529c4ff0232dd0d170af8c9330588916210451c44fa623214179651cc96200531411490 else (if c < 758 then 0x452cc5078231c10e97123589b705895162414521c5036232405041447dc48b026e416234 else 0x5890161d11bdc1629758a045040578c047e04535c4c84589c15e204531c48f224bc1626b))) else (if c < 762 then (if c < 760 then 0x58bc562e400ce0082701cd08ca04269cd4871248961a858b5162cb05bc162b058a9c8cd0 else (if c < 761 then 0x57c408cc01b1c163510ea415e5058d0c2a330b9ccc16157904d49058cc9632058c516305 else 0x5885963b458e901790579c163900aec02cd0579814c6058e156371047e01121231816360)) else (if c < 763 then 0x1314162a3531cd1ec93528d62705881c48505901163f158f815f2058f4163c04539c4937 else (if c < 764 then 0x591002be617e813bd057a01643b590900ea6148688c8058d855f201b1c56410453dc4850 else 0x2080162b157b106f711bc588c9057ac164725918848b0258015ea020f2c8cb057a516450)))))))))) else (if c < 1148 then (if c < 956 then (if c < 860 then (if c < 812 then (if c < 788 then (if c < 776 then (if c < 770 then (if c < 767 then (if c < 766 then 0x47b5d0ab92e3e564b0592acb88157bc96490123c0499057b903bc8231c15ed85920048d0 else 0x595e56560595656549594d165245945d38bb5942d64f15939164d7593155f345321d0c29) else (if c < 768 then 0x597e4b8fa59780c608597450aca2e2242fa259710c5f8272a4a599596e965a7596416580 else (if c < 769 then 0x4c3c566b059a81669659a196678599a965f042a81665042b656640598c16620598416600 else 0x59cd967244e369671a59c1966f8318a166e159b595f444311d1ee742cdcd4b84c5a166c0))) else (if c < 773 then (if c < 771 then 0x59801316a59f1130f342d002ff759ed0a043280e167a559e59678059de1676759d416749 else (if c < 772 then 0x532590c6947bdd0bb73531968575a111683a5a091681042d65680059fc167e059f416668 else 0x28b9d692a5a44d69005a3c168e75a34168c95a2d168a74e3e968905a208c64a5a1d96864)) else (if c < 774 then 0x42f6569805a5c1696059f41667a5984168595a541694557d410bc7131cd69304cec44fe0 else (if c < 775 then 0x5a8854ca1431651f0742de4d4d15a8596a0942da569f05a79169d05a70169ba5a6816990 else 0x5abe4aa665aba96ad35ab016ab05aaa56a965aa116a745a99d38eb5a96d6a465a8e0c63b)))) else (if c < 782 then (if c < 779 then (if c < 777 then 0x5addd6b675ad496b475acc10b995ac816b105a58167e059a2d66205a8596b0942e244ca0 else (if c < 778 then 0x5afc16be2318456bda57d814cba430dd1f1942bdcd4ea5af016bb45aea90ae05ae5d6b87 else 0x42c1c4c735b280aa712a0496c9a5b2016c775b1916c575b10d6c305b0816c194e3056c01)) else (if c < 780 then 0x5b49d6d175b41d6cf35b39d6cd042c656cc45ac41697059fc1669b598c16bc45b2c16ba5 else (if c < 781 then 0x5b64d6d805b5e0c6535b5996d5657dd14cc6431e51f2742fe4d4f6277016d4042f816d39 else 0x277296e504300c4d725b9016e305b8816e105b8256df05b7a56dd45b7116db45b69d3909))) else (if c < 785 then (if c < 783 then 0x5a04166b95994165d25931421205ba016e795b9810c195b3116b205a601680059aa56640 else (if c < 784 then 0x5bcc16f205bc416f095bbe56ee05bb416ec05bae56ea05ba40c6695b9816cd05acc16990 else 0x9cc16f794322568645939021295bd8139105b56d6bd259b6d64d4090416f502b8256f40)) else (if c < 786 then 0x5bf016fb05be816f9000d2407995970023d45be016d6b5ae896a235a1ed66e34cfa964f3 else (if c < 787 then 0x5a24167064cf68b8f9303656e90354256d785afa16a385a20966f84cf0965e85bf816fd9 else 0x5c0016eb057e016d915b0196a565a52167185941824d05bfc133b65ba816d805afd16a46))))) else (if c < 800 then (if c < 794 then (if c < 791 then (if c < 789 then 0x5c1016ec0533416da75b05d6a675a29d67c74d09d65175c0e570205c040126959ec0240a else (if c < 790 then 0x5aa11695459c91346b594d024d95a4d024645bb416db45b0916a745a2d131684d0e96524 else 0x5c1640d50090416ef057e656dd75b12d6a9b5a151673b4d1e165405c0256ee05b7116c34)) else (if c < 792 then 0x5aac168d059d412e5a5958170704e4816f605b7816c505aa8168c059d000c50595417060 else (if c < 793 then 0x5960170905bc016e005b1c16b005a39167644d10165705c2256af00944021205b7c16c60 else 0x5ab01690059e0134035964170a009ce56ca00919d6f105b8416c845a85968f059de1345a))) else (if c < 797 then (if c < 795 then 0x4d22965ba5b92823d65bcc16e305af116ad35a44d67964d06965a75be256f205b8816cb0 else (if c < 796 then 0x34040d0002c4410c9a3544035b314708041232bd836495bd016e5a5b2556aea5a4a967a5 else 0xdf956e700ad8031a041880d0140ad80d2c05c3416f5053380d5200de9170c65c2e10620)) else (if c < 798 then 0x5c4a50ce913d8052295c46571045c3e50d0913e8052041305170eb533c10cc70dd005240 else (if c < 799 then 0x1d6851f0021150cb70aec080c05c54171405c4c50ca913ac051d413b850cf90b0009364 else 0xb10052745c4c170d80cf0171865c5c44ee05ba1031b7434e42a760ab917160343c10d23)))) else (if c < 806 then (if c < 803 then (if c < 801 then 0xaac0c0e15ba4cd5305c7cd71ea5c74cb7b55c70d71b300d6807a701acc51c25c6817198 else (if c < 802 then 0x5340172645c95c12780465052475c90172365bac170f00c1c172275c8416ea05c8182a10 else 0xc1dc34441480172b85c8c50d575c40172a05ca404c105bb4172895c9c02c200acd16ec7)) else (if c < 804 then 0x5cc4573055cbc172e15bd80d69935a0172b55bbc171105cb6c2beb24e8172475bb9172c6 else (if c < 805 then 0x5cd81735903580d6904358046e05cd1c2329358017190534411f303550046e05ccc17320 else 0x5c6856f205c50033c10ce8051d45bc4173895cde02c0024d116f000d20052204e4c16f60))) else (if c < 809 then (if c < 807 then 0x132e573c25cec511190be8173a027284d6115bd2833750cda851f05bcc173970aec080d0 else (if c < 808 then 0x5d1257434444802ff75d09174104459c4c735d00173f45cf8111400bfdd73d42810d1227 else 0x4460c4d725d34111705d32574b95d29d74975d20974775d1811137131cd74502a9c50db0)) else (if c < 810 then 0x5d60175705d58175505d5013af05d4c175205d440c8205cf8173b32348175005d3c174e0 else (if c < 811 then 0x1fc173a90919576101bd017600446408d205d7c086905d78175d05d70175b05d6817590 else 0x5da4175301b20176805d480c1305d440d5505cf1576705d98176505d90176305d8800360)))))) else (if c < 836 then (if c < 824 then (if c < 818 then (if c < 815 then (if c < 813 then 0x5da4175605d05c6c805d01c7d775d54176c05d5014d205cfd176b05da8012405cf5059f4 else (if c < 814 then 0x23e408d205dc0175f021a4175905dbc13b005d60174305db8176d003ac17420094417570 else 0x5dcc9772233da44df85d74175c05d3a174d81009175b05d84175a05d1a577101bd017459)) else (if c < 816 then 0x5dec177a35de49065034050d0005de017770446acd5601378886005dd8d775305fcd7743 else (if c < 817 then 0x4475c4f642191c4b0013dc574f424c403f8441940d01024c4177d05df0175e4534c0d570 else 0x5e0c111b913d80861907b8146cb5e08978105e00511e713fc086601308177f15df814d40))) else (if c < 821 then (if c < 819 then 0x2024178745e1811203142ec8670143050e77122c09b305e141784b4471c4ff421880500b else (if c < 820 then 0x5e34178c41430178b05e29886805e10177c61bd4178945e20450005d41c49a74485c48f7 else 0xddc080601c4c86004255c4a265dde179105e40017f05e3c178e31421178615df4c3ce0)) else (if c < 822 then 0x5e6ad79905d49d79800a9402ce030501751b3560577805e5cd79635e56579405e4cd7921 else (if c < 823 then 0x5354179f95e7ac1258045e486404491c4a365df9179d95e7244b045e6d175335e0106c90 else 0x5d59d7a431b2548b602198112575e0417a305e8804c205d55d7a195e8002c000ba017544)))) else (if c < 830 then (if c < 827 then (if c < 825 then 0x5ea1c0ec8148dc8610448e44a335e0d17a775e99c1ee45d5dd78225e95c48b02594179b1 else (if c < 826 then 0x5ec411263129017b035ebed7aeb5eb697acb5d6657ab05eaa42c0017ed13b205d6017a9b else 0x449c049b01324178e45e2914d6447d10d594126c17b005ed917b5b5ed017b3b5d7c17b20)) else (if c < 828 then 0x5d70d7b030f3843a8b219c175b75ee2448b42064178b15d6a46f511bbc086245d7c17b70 else (if c < 829 then 0xbfd97be05ef54a0425ef00c6895eec10d7b0be897ba0272a175d75ee5c48f711f4178f1 else 0x5f2017c794e5297c65436242ff05f1517c405f0d57c2a4379c4c735f0417c055efc10da1))) else (if c < 833 then (if c < 831 then 0x5f18d7c235efc11d545eed08dc05f3417cc05f2c10e03135c97ca0437c17c974371c4ca0 else (if c < 832 then 0x5f68175d05f6417d805f5c17d605f5417d405f4c17d205f44139505f4017cf05f380c690 else 0x356817bc45f8417e005f7c17de05f7417dc000e0007b05ee902510438448dc05f6c06f30)) else (if c < 834 then 0x5f4414d705f0157e505f90012205ef8059f45f8c17d005f0e46ca05f8817cf0303c17ce0 else (if c < 835 then 0x5f5417c715fa017e70039417c56091957d405f8c17d305f1186ca05f0587d775f4817e60 else 0x5f6417cb95f2a440b0237017db01bcc17d805fa817d705f2457c8623e417d605fa413960))))) else (if c < 848 then (if c < 842 then (if c < 839 then (if c < 837 then 0x5fe017f785fd8d7f505fd017f315fb2d7f205fc457f005fbc17ee05fb417ec02a4057eb6 else (if c < 838 then 0x60181805560101803a60081801341b811280600017ff75ff817fd85ff017fb65fe817f92 else 0x6058181546050181306048181196040180f86038180d16030180ba602818098602018071)) else (if c < 840 then 0x6098182506090182386088182106080181f06078181d16070181b760681819260601817b else (if c < 841 then 0x60d81835260d01833760c81831560c0182f060b8182d960b0182b160a81829760a018270 else 0x5da1d4e604999583d05f89972205bfdcd7e02bd943a9160f1d83b660e81839060e018370))) else (if c < 845 then (if c < 843 then 0x611c18460611418440610e97f305fb696060610a184186102183f060f99635044a0179a0 else (if c < 844 then 0x581806b9060e004c61614418500613c184e061341838054a0184c0612c984a0612418480 else 0x616c1854b6110585a0616418581615c18560615418540610c122d1614c152e060e058520)) else (if c < 846 then 0x619d986606194185e7611858640618c58620618418604617c185e0611595ad96175185c0 else (if c < 847 then 0x61b99848161cc1872161c41870061bc186e0611dd86d661b056ba861ad986a161a598685 else 0x61fc187e061f4184b061f0187b061d9184a161e81879161e11877061d81849b61d418740)))) else (if c < 854 then (if c < 851 then (if c < 849 then 0x54b806b915fd017eeb62180480011fc188502a9c18840620c187d36130588206205d8800 else (if c < 850 then 0x1340588a46225188841be018874620c187e361ec1877461d0186f66194185f7616c1855b else 0x2f6e84e006010988f62dca188e03a0004180600c188d16231988b56218152e054a044860)) else (if c < 852 then 0x6260589471b4418063625c189672e8c58950625006d006014189306249d891462400e807 else (if c < 853 then 0x62804e7e713b4180862e88589f92ddd189e039f804240601c189d06271189b9626818990 else 0x602ad8ab062a806ce0602418a9762a118a776299d8a506291d8a30628a58a102dda5352b))) else (if c < 857 then (if c < 855 then 0x62cc18b2062c4189f06258188f062c10a90062bc18ae01b30180b062b598ac462a9c6cf0 else (if c < 856 then 0x62bacbca61b34180c162d402ef062d0135c76261d8a042f51cd6642f24988706136d7ef1 else 0x273c09cb962f818bb4188c180eb62f418bc062ec05aa0603418ba462e418b8962dc18b60)) else (if c < 858 then 0x6316552b0604058c70345418c6063140c42054a8180f0631118c37630a58c17630018bf7 else (if c < 859 then 0x633058cb062605898054a4186014ca44ba3154a4586004ca40ba30632858ca0632418c80 else 0x60f818d30634815fb05f41c6cb060f458d10634018cf0632c58cf1633858ce0633418cc0))))))) else (if c < 908 then (if c < 884 then (if c < 872 then (if c < 866 then (if c < 863 then (if c < 861 then 0x637498dc3636c98daa636518d83635c115e757fc04c4060fc58d60635418d40457804090 else (if c < 862 then 0x639c58e65639618e41638c18e08632cc6e30604858e24638418e001b8818110637cd8de4 else 0x605418eeb63b698ecb63ac18ea13cc1d39ea13bc132b16051d8e9863a00f300109818130)) else (if c < 864 then 0x63dad8f5b63d2d88f048b418f3063c806d80605c18f1463be86e10605ad8f0063bc06e00 else (if c < 865 then 0x63ec44b7063e818ea44e81d8cc75c8d0c707622018561613ad8f9063e018f7063a418e20 else 0x6418026b0606419058641199038640999016640058ff863fa18fd063ca86d90606058fc0))) else (if c < 869 then (if c < 867 then 0x6070590e06434170e06430190b054bc181b0642a190964ced99080641803330606899070 else (if c < 868 then 0x6332c6d706079991694ca6d91506450191301b58181d06448191146442590f0642d95300 else 0x1b7018211647a591d4646c06e506082d91c0646c06e40607ed91a06465d9180645c19137)) else (if c < 870 then 0x63358c7176224186194cb0184fb649019230648819160638819214625815ad06480191f0 else (if c < 871 then 0x64a806e80608c1929764a019270647c18ce31b7418221649819250645e53a17634918ce7 else 0x54d01826164c41930064bc192e0633d153306095992d954a5192c064a9c6e906092d92b0)))) else (if c < 878 then (if c < 875 then (if c < 873 then 0x64edd93a464e5d938464dac6d5060a2d937064d806d40609c1935164d15933864c8192e7 else (if c < 874 then 0x65101943065081916063a419414627c16ba06500193f01b481829161b5d93e064f5d93c0 else 0x65201947064fdd39c31b4c182a1651819450539c139d74e6d98cb731bdd88a061c0d850b)) else (if c < 876 then 0x4cfa995206540033e060b05951065400275060ac194f06539194d06530194b0652a59490 else (if c < 877 then 0x62d10b7646570195b0656819590656005de0655c195604e7c152c060b4195526550d953b else 0x60c0596106580195f01b68182f165781956854b4182e1657414a4065151925463e916070))) else (if c < 881 then (if c < 879 then 0x60cad96c065ac06e6060c4196a065a419680659c196606595d9644658d19620657c06db0 else (if c < 880 then 0x1b781835065c8196e654c81834165c4197095dfc196f065b81531060cc196d465ac06e70 else 0x65fa197d065f1d97b065e8d979058201978065dc9976065ccc6df060d85975065d019730)) else (if c < 882 then 0x61d41871661981862761701857b614c185215fd417f0b6610198326608198166600197f4 else (if c < 883 then 0x62f918bc062b018ab96285d89e06266589546240d88eb35fd0af746210187f361f018780 else 0x63c418f0563ad98e81638c18e18635c18d475e6c1769653a012674634c17e375c9197006))))) else (if c < 896 then (if c < 890 then (if c < 887 then (if c < 885 then 0x13181985465b4196c465481951064e01937164b1192b96474191c46461d91406420d9073 else (if c < 886 then 0x655e1932064bdd90f0643193a29633cd8c80631a4c729614c18860614459884661d19864 else 0x6501d9270648018fd063ce96360582018b6062bed98b02330198a066251972065bd995e0)) else (if c < 888 then 0x54d8183a16638198d066301989054d41839b614c0475060dc5976065d0d9620658019470 else (if c < 889 then 0x6646d990354a0107a734064d007663c10e22356c04d9a1baa41e4b330d04db56631198a0 else 0x25d017860664c84d005f68d78805d82571705bdc1628057e914d8049780d5c02bb4d992b))) else (if c < 893 then (if c < 891 then 0x130c193011412d9940536410e4313eac6ed712c6c4fb55f30c97400fd1d07a712104d017 else (if c < 892 then 0x1bad199b705f6599a76665d99875100d997713b999963665418d1158a4d0e87140d86f00 else 0x6678177d043aa850741bc9050865e2550e6713fc06ee71400599d0667017180438c04eb7)) else (if c < 894 then 0x4219c4922663d59a34668981e406684043e0664c17cd3120419a0043adc48f225bc199f7 else (if c < 895 then 0xa8dc2cc0304017ce4357459a9266a059a79669a59a5966914039901f1806d41ba90bcb7 else 0x5f46d4da066bd19ae3048e0115b1bb690ee7124dd994566b519ac466ae04b105f3dd9aa7)))) else (if c < 902 then (if c < 899 then (if c < 897 then 0x66d086cb12336c88b61bc018d2143bdd995066cc19b21130c17d2666c419b000af982d30 else (if c < 898 then 0x1bac13a4143b5d99c966dd19b6105f417d4757f01996266d5c48d2252418d315f4d962a3 else 0x21a18863b1bb817d6366ec02bb0177c13a505f545719066e9d9b9666e180e66149c851e6)) else (if c < 900 then 0x670419c0666fd070d066f8188615f6cd7b235ec4d7d8766f659bc9122d494205f5ed78a0 else (if c < 901 then 0x6684978b15d86571a15be2562b157f514db1497dc486147d5cd5e12bb8d9a006675c4850 else 0x454282fa2670809ca85e3057d990f3943a841bca57db3133457b7343c1c48501330d78d1))) else (if c < 905 then (if c < 903 then 0x454642ff0672119c704555c4c73671819c55454c42ff667100a0424575c4ab4670c104a0 else (if c < 904 then 0x6738003a4020c19c20090159cd04549c4c7367300aa71672dd1547132819ca0672650397 else 0x675819d50675001204671002405434c0c17045600d5f0670c19d34674819d14674119cf0)) else (if c < 906 then 0x676100e706721823da453018d40457019c76102419c66100a910b0675c115a0537019c55 else (if c < 907 then 0x6770043e46732040b043ac19db0456419cb167298402534bc19da04ef811570672459d90 else 0x4f0411571358004e580f2400e88677999dd833f9c4e6241f403cc04484115b0668519cd8)))))) else (if c < 932 then (if c < 920 then (if c < 914 then (if c < 911 then (if c < 909 then 0x41f5cd01712b011f625e3c578c1358c55fe453744d6116786d9e0b677e907d734064d007 else (if c < 910 then 0x6358115c6141c83cb01310598d05378115ab01d4c3c80678cd9e230486115f312b003fc9 else 0x306013c0035885158001d5c3c9400edd9e89679dd9e676795d47b36791c0846589c18d71)) else (if c < 912 then 0x67ad99ea667a589ca05e3911591141c03ca01420d9a005e34515b3142ec3ca314304d300 else (if c < 913 then 0x819f2867c419f0067bc19ee64d80d89b367b6504492f54d9ec028e800010622c0a040 else 0x67e509e640295135f0626809ca067e219f7867da0e0e067d699f470d5019f344221835b1))) else (if c < 917 then (if c < 915 then 0x36bd108090d6c00a6467fe59fe067f519fc067ee19fa940a4d02b636b8188c34d30cbbc3 else (if c < 916 then 0x6824189a139881a08500001a07568195a05568115a03a68080de40680559f490d9d1a000 else 0x68495a11b4d84ce6506841da0f74d7cce64068381a0d068305a0cb682d589c5398dda0a3)) else (if c < 918 then 0x687c5a1e968741a1ca686c4e67768681a19939981a18002b89a17068591a15468501a13a else (if c < 919 then 0x39a81a29500001a285689d5a26568945a24a688c1a22462354e6976884da200622c4e680 else 0x68c01a2f868b80000068b400a600296823d068b00002b00044240067c68e6b368adda2a0)))) else (if c < 926 then (if c < 923 then (if c < 921 then 0x68f01a3ba68e80000068e41a38a68dd1a1e268d81a35068d2c0ae268cc1a32768c49a0d0 else (if c < 922 then 0x67d41a46b69169a44b690e9a42a0d9e8354a39b01a41069011a3f068f91a3d0279a8a3a1 else 0x68ae1a4ba68859a4a068681a49968411a4876828da4700bfc02a060be802b7839c41a010)) else (if c < 924 then 0x67e9d9ed669451a500693d1a4e069341a4c000f0004000addc412a37500e6d7627450263 else (if c < 925 then 0x34501a5504224134d467ee19ee869501a530694800d740a81c41253484108102f5c0bbe0 else 0x69691a59003dc1a5836836ce730682d19fc067be9a0a2695c189e039c804240695840000))) else (if c < 929 then (if c < 927 then 0x686d19fd067c15a5f0686ada5ea39e01a5d302b9ce7b06845da5c068415a5b54d880e7a0 else (if c < 928 then 0x67c69a2b7698c0e74069880000039dc1a2216885da61439d8188e410611a601687a4e790 else 0x104003d42dcd4e8172f62da67411541a6624d54108936996da64b03628e75067c559fe0)) else (if c < 930 then 0x69c418a1639c85a70669bc1a6e713b59a6d22f000bdf04205da6c469ad1a6a069a51a680 else (if c < 931 then 0x69ea134f64d3cce75769e41a78039d01a77769da5a75369d2189f54d38ce73769cc1a720 else 0x6a0c1a8202dc84e7886a05da7b96a029a7f639ddda7e069f41890239dada7c369ec84e02))))) else (if c < 944 then (if c < 938 then (if c < 935 then (if c < 933 then 0x6a291a8904d900e7a86a21da7676a1c5a8656a1400f816a129a7f42f16588f539e5da7e3 else (if c < 934 then 0x6a30da6f06a2c044561110c10d91171006841172006826a2d844501112810d539edda798 else 0x4d50135464d40cbbf66a361a7666a401a8f66a381a7b86a419a8f06a399a7b46a351a760)) else (if c < 936 then 0x6a50da933699c0bda74d44ce7c96a481a91011550b73a4d8d8bbf04d8c0bde62f780bd91 else (if c < 937 then 0x6a6c5a9a16a6449ca039f5da98069e61a96a69f99a97669f81a97069e41a96369cc1a953 else 0x6a911aa346a89daa104dc4d8ad36a825a9f96a799a9d62fb0da9c42a2501cb4624413560))) else (if c < 941 then (if c < 939 then 0x4f8137002a9c09ca06ab05aab16aa85aa906aa25aa7722481aa606a9410977136401cc0 else (if c < 940 then 0x21301ab40420e04d9504fc1ab356ac91ab106ac11aaf96ab9189234d5ccbc136ab40a0f0 else 0x6af65abcb4dc8ce8656aec1aba04dc09ab9b4d60ce8516ae19ab764d589ab606ad65aa77)) else (if c < 942 then 0x6b261ac8b6b1d5ac746b1ace8876b141ac403a1e9ac3205281ac226b049ac026afcdabe8 else (if c < 943 then 0x6b525ad303a2ddad286b469ad086b3c9ace76b35589353a29dacc36b2c189113a249acab else 0x6b6e9a1e46b681ad9a6b60000006b5c013f704f8825106b5801cc8072e424626b568e8c2)))) else (if c < 950 then (if c < 947 then (if c < 945 then 0x283c8a8996b981ae596b921ad1a6b8c1ae2b6b851ac906b801adf86b78014a46b741adc0 else (if c < 946 then 0x6bc41ab506aa01af096bbe5aee96bb65aec92132489293a341aeb86baa1ae986ba21ae76 else 0x6bdc1359a6b50daf6a6b319af566b141af406aecdaf33131cc2a236ae01af260be804872)) else (if c < 948 then 0x6250135a04260908433a3c9af806bc65ab606aa41aa5a6a74dafb06be81af906be00e8e7 else (if c < 949 then 0x6c1c1b06062b80e9026a78db0506c101b0306c081b0106c001aff06bf81afd06bf013730 else 0x6c341b0c06c2c1b0a000f800440121dc44796c241b0802fb40e9122f081af7a6ab85a9f7))) else (if c < 953 then (if c < 951 then 0x6c4d1afc04d6c1b1206c4400ef06c41800006c241b0802fb80bc306abd9aa076c3c1b0e0 else (if c < 952 then 0x6879db07062bc1b0606ac55aa291b301b1500a8a444796bf41ab976ac05aa146c501ab8a else 0x6b169b1c76c001b1ba0529daff06af19b1a06aee5b1944dd01afe06c601b17003cc1b169)) else (if c < 954 then 0x6c801ad186c0c1acd06b321b1f06c08189501b401b1e66b261b0106b191ab216a8c1b1d0 else (if c < 955 then 0x58b01099635901b2616c945b2416c8c416f56c894b9f012fc5b0506b569ad496c865b040 else 0x3a4c5b2d66cb19b2b713b59b2a26be6cbc466ca4092506ca059a20421441e466c9c18b00)))))))) else (if c < 1052 then (if c < 1004 then (if c < 980 then (if c < 968 then (if c < 962 then (if c < 959 then (if c < 957 then 0x6ce2db3713a59db3606cd41b3403a55db3306cc9c4e146cc44e9466cc05b2f46cba98080 else (if c < 958 then 0x6d081b4106d000e9956cfc1b3e0139d9b3d362595896a3a61db3c66cec0e9776ce8db390 else 0x6d1804492112206ec06d141b2c06d104917024584201311c880682254401a413a69db432)) else (if c < 960 then 0x62d458b152fbc5897258b40d6502f488bc696d289b3e36d259b3946d201b3276d1d1b2fa else (if c < 961 then 0x6d3e98b356bea8bc896ca45b4e824945b4d062c94e9b72f1e445642e7c5b4c06d2dd9a30 else 0x6d555b4e16d50003f801141afb73a71db4346d4e5b3c06d4a9b3686d461a7e06d401a738))) else (if c < 965 then (if c < 963 then 0x6d2c1b5e76d765b5c76d6e1b5aa6c25db5940a8d047206c21cbf012f4c1b5826d5c1b560 else (if c < 964 then 0x6bf68b7746d941a7306d901afc84d741b6356d895b61a6d8000f056d7e1b2c93a740bcd0 else 0x6c1a86cd13a7dcbcf76d311b4066da49b681139c0e9e72f39db3446d9c9b668138418b45)) else (if c < 966 then 0x1158189fa4d784d67a69fc9b2796da41b6706dbadb6d16db05b6b16da81b4e0112018b61 else (if c < 967 then 0x6dd0137506bf89b73a6dc900f466dc69b2f26c1ddb7000a8d044903a81cbd076d351b6f8 else 0x1b461b7a66ce41b0172f465b6716de41b3626de01b0026ddd1b76b6cc81aff56dd41a7e6)))) else (if c < 974 then (if c < 971 then (if c < 969 then 0x27281b0576da45b4306e001b0406dfd9b7e76cfa5b0376cf11b7d06c09589986df09b7b7 else (if c < 970 then 0x628cdb8946e225b8796e1a5b8502f84c64946e110a644051118a204d941b8386e0a1b818 else 0x6e611b9746e591b9506e511b9366e491b9146e421b8f06e391b8d76e301b8b66e2813663)) else (if c < 972 then 0x6e8c064976e88dba146e81db9f16e781b9d06e70063706e6e9b9a84231c4de005141b997 else (if c < 973 then 0x6ead9baa44da618a6a6ea59ba882f9218a45423dd08d73a91cbe286e9e1ba676e955ba40 else 0x6e741bb716eda936763a96dbb536ed2936586ece1bb256ec59bb006ebe1bae76eb41bac9))) else (if c < 977 then (if c < 975 then 0x4239cea772f8e1bc206f051bc0a6efc1bbe03a9adbbd46ef0dbbb36ee8dbb926ee0db9f0 else (if c < 976 then 0x6f34dbcc06f2c1bca76f241bc896f1d1bc676f15136aa6f101bc322f9698a584da210909 else 0x6f589bd526f509bba36ee09ba076e785bd346f4818a753aa1dbd136f4018a216f3c9bcea)) else (if c < 978 then 0x6f801bdf06f780eaa26f76000006f721bdb86f719bdb66f689bda76f641bd803aa69bd72 else (if c < 979 then 0x6f9e5be604dad98a866f941be426f8c9be226f840be6662a0d36b34245d09193aadcbe63 else 0x6fc29bef23ab1dbee26fb404ea06fa91be946fb01beb76fa11be776f991bea06fa41be80))))) else (if c < 992 then (if c < 986 then (if c < 983 then (if c < 981 then 0x5140144a091a1bf606fd40eadb6fd09bf326f549bbb26f54dbbb36e855ba146fc81bf1a else (if c < 982 then 0x6fe65bf8802b89bfd46ff09bfb405289bfa46fe5dbf8202ba1bf7005150144509189bf74 else 0x700c1c02070041c02470050a64529929c0006ffc9bfe000001bfd06ff21bfb0052a1bfa0)) else (if c < 984 then 0x701c1bf306f581bbc06f591bbc46e881ba2470189c05270121c05870108637818dc8eae0 else (if c < 985 then 0x6fb89c0ba6f459c0a6132802a406ed51c0976f44dc0a36ed41c0990be81c0821274849c2 else 0x703c8eb0712949c0ea7034dc0d64db158a9570318b91562a6936ca4249d09293abdcb91a))) else (if c < 989 then (if c < 987 then 0x6f605bbe06e8c5ba30704c1c12070440eb1b6fd09bd726ef55bd736ef5064961925dc100 else (if c < 988 then 0x705c1c16070545c14b4db458aa162a8136d0424e9093b3acadc110701c9bf506f601bbe1 else 0x3ad2cbe7070311b8586e165c1c0706eceb3b6f849c1a070641c180705c5c16170541c14a)) else (if c < 990 then 0x70981c22070941c240708c1c21170885c21070805c200707c1c10012701c1e070740be71 else (if c < 991 then 0x70a01c270709c5bf606fbc1be206f641bbf16f645bbf06e905b9a06e185ba406e685b860 else 0x70ac1c2c070a85c2b170a8004210108049d0112c8eb5b703c1be306e1c5b87070a404a50)))) else (if c < 998 then (if c < 995 then (if c < 993 then 0x6ea55bc436ea51b8966e25dc1d02fa04be806f901bc306ea05bc316ea01b8816e201c2d0 else (if c < 994 then 0x6e2c1c30570be80f5570ba80aea709c0eb6b70351be636f14db8f96e2a1c1e06f949bc42 else 0x6f1cdbb716e45db8c870cc5c3206ed4dc3127050136e06f9c1bc806eb01bc606ed81b900)) else (if c < 996 then 0x62ac5c1606fa49bcc26ec09bd226ea89b9586e3506ce170d0014a070541be836f24dbad3 else (if c < 997 then 0x6e49dc38170e01c37013a89c1706fa89bcd46ec55bd336ead1b9666e39dc3606f451c350 else 0x706c1beb06f291bae46f281bae06e4d1b93070e682a47112ddc2803adedc0e66fc19b926))) else (if c < 1001 then (if c < 999 then 0x6ec99bce66ec9db9766e5ddc3a000001c1c06fb09bcb26ebc5bcb36ebc1b9466e51dc100 else (if c < 1000 then 0x5fc1c1906fc89bcf06ecc5bcf16ecc1b9866e61dc3d070f01bee070ec1c1806fc59bce7 else 0x71181c45a7116dc4411436dc4403ae9dc43071081c4113ae45c40670fe1c3e25e4010947)) else (if c < 1002 then 0x71081c4c070fd07f8406990495001a087f8006980ebc7712c9c4a071241c4803aec9c476 else (if c < 1003 then 0x71401c1a22fa5579102fa69c4f2711a9c4d671091c4e01134044c62195dc4c470fc1c4d3 else 0x712c9c55a6cd91c54869f91c5336cd81c54269f81c53670489c52671440ebd7115c17914)))))) else (if c < 1028 then (if c < 1016 then (if c < 1010 then (if c < 1007 then (if c < 1005 then 0x71649c52471605c593716000436010dd3d07715c0ebf771401c48a7158050d0704c8ebe7 else (if c < 1006 then 0x717c1c1404dbc1c5e97176c0f6871725c3f770789c5b00a940495070740bea12fa81c5a2 else 0x71901c52011301c1b0705c9b360718c18ac170589c6231b3d5c61071081c15871801a7e0)) else (if c < 1008 then 0x71a482a5011340ec0771441c682115c1c5782fadcbeb27124da7fa69fc1c67471991c654 else (if c < 1009 then 0x62dc1376071c05c6f171b849ca04f42dc190712c1c6d070619c6c871ac9c6ab71181c1c2 else 0x427184e5102b01c78571dd1c76071d41c7404ddcd8b8371ce5c7272fc4dc7102ab800ab0))) else (if c < 1013 then (if c < 1011 then 0x72109c834720a9c81a4de08ec4172001c7f04dd89c7e071f5dc7c471ec1c7a314501c790 else (if c < 1012 then 0x72301c8b772281c89972211c8774dea9c86072148bf3a62e453791427a509d73b15cbf21 else 0x725a1c95072521c7c971ec9c938724818ba53b19dc913724018b71489c9c8fa7238dc8d0)) else (if c < 1014 then 0x1c9c002b080ab709001c9ca02b1c0ab209029c9b672680ec8772641c980725c0ec75 else (if c < 1015 then 0x6b469ca5072921ca3000001c9f0727a9c9d000001ca2072869ca046b441c9fa72781c9da else 0x72ac1caaa1451c51423b241ca8672a61ca7672a21ca782ab9caae272981ca2a72841ca0b)))) else (if c < 1022 then (if c < 1019 then (if c < 1017 then 0x72019cae672459caf67200dcae30be804ad272b41c95a72541c7d071f69caba72b01caa0 else (if c < 1018 then 0x72d41cb4072cc1cb2072599c9683b29d37bb72c4137b1135c82a6a7244dcaf372641cb07 else 0x72dc1cb604df1d8bb762ec937c2427c509f53b2c5cb2072b41c97a726a1c97071f9dc7e2)) else (if c < 1020 then 0x2fd09cb1871c81c72a496c9cbc03b321ca6272e41cb8072ec1cba172de9cb6a72e69cb8a else (if c < 1021 then 0x71cd1c73b73081cc0a73041cbf073001cbfa0119c046212b5044f072f81cbd02fd1cecd1 else 0x4df41c895721d5cc52731000f12730c0000072f81c866721a1cbd02fd40bf5a7216dc854))) else (if c < 1025 then (if c < 1023 then 0x72e01c8d8724a05aa273201ad1a72dc1c8a672219c81a71d5dc742731c9c80073191cb60 else (if c < 1024 then 0x71d9dc76273301c998732c1cba0722c1c8b473280000072e41c8e0724edc910732418bc2 else 0x733a92ce0428040e8872f01c8f4723edc77b71dd1ccd00a99044f272ec1c8c6726c1c8c8)) else (if c < 1026 then 0x735c1cd84735d1cd5573581cd5a3b415cd40734d1cd224a400ecf673445cd07733d00f81 else (if c < 1027 then 0x62f55cde273749cdc2736c8bf6562f6937ea4285d0a193b45cbf6a73689cd976f781cd80 else 0x73991ce547390450d07392d4a22738e9ce2873851ce02737ddce2273841ce08737e537e5))))) else (if c < 1040 then (if c < 1034 then (if c < 1031 then (if c < 1029 then 0x73bc9cb363b4ddcee273b41cec273addcea073a49c5603b49dce80739dc4e2073981ce50 else (if c < 1030 then 0x734e1cf20739ddcf027340dcf12734c9cf08734185be4043cc4a7201a085be0043d92fb0 else 0x72d19ced051d80454273d00ed47116013bf42fde13bf02fdc9cf301144845000f1e9cf18)) else (if c < 1032 then 0x73f01cfb23b55dcfa06d0c5cf65712c1cf9273e09cf7269e41cf546d0c1cf6469e45cf55 else (if c < 1033 then 0x72991d01074101d03274089d00173fcdcfe874045d00073fc9cfe973f45cfd072d51cee0 else 0x74240ed6b73ec1cdc074209d072741cdd0604f0013c0173bc1ce90736c0d30034c05d050))) else (if c < 1037 then (if c < 1035 then 0x73781d0d60a9c04a7072f50bf812fe01cdd051d89d0b074301d0a1742c5d0a0011d80477 else (if c < 1036 then 0x73801d15674501a790744c1cb6b4dfc1cdf07449dd11874429d0f003ca1d0ea7342dcbe4 else 0x746884e2072e51ce2074641b430746018be572e0dce10745c0623574589cd3272dd0b788)) else (if c < 1038 then 0x715c9cec050e09d1f0712c1d1e072e81ceb07475dd1c0746e9ce7074188ed7773a814380 else (if c < 1039 then 0x116e445a80902802d00a32828b008f59d0923b61dcf4074808458072f11ce30729a1cbb4 else 0x25580955b0944016b91fdec7f640919c02d90a32028b908f5016b01fdd87f67091900d50)))) else (if c < 1046 then (if c < 1043 then (if c < 1041 then 0x7490dd23074891d21000b5cbb100bc802f1035a40d69935a000d59116c045aa090201e10 else (if c < 1042 then 0x74d15d33074c9dd31974c0dd2f174b91d2d174b09d2b074a81d29074a11d27074995d254 else 0x74f0dd22401e102fb073f41c20031404d6a02fe45d3b074e81d39474e11d37074da5d357)) else (if c < 1044 then 0x74b01d24075209d47875189d45275109d432750a0bfa02ec45d4137500dd3f374f8dd3d3 else (if c < 1045 then 0x75541d547754c1d5272dcc1d51b75401d4f330040bfb075381d4d075301d4b075281d490 else 0x5c6d96f9658b816008115591f7135dccaf0375741d5cb756c1d5a275641d588755c1d568))) else (if c < 1049 then (if c < 1047 then 0x6c30dc58470a91a6c0693a5b5446c2a4d79035bdcaf206794d9ceb669017dca5e4917625 else (if c < 1048 then 0x757c1d5e7679259d0058c0160275e51176415380126246699d7de074291cfe772fc1b550 else 0x75bd1d6e975b41d6c075ad1d6a475a41d680759d1d66675965d644758c1d62075851d604)) else (if c < 1050 then 0x75e41d78775dd9d76675d61d74675ccdd72001ad80682019c02b7401bc010d975c41d70b else (if c < 1051 then 0x76069d80675fe9d7e875f69d7c02dee96fb673fd8b73a69324d70649ea9260875ed1d7a4 else 0x76241d880761c1d86474bc1d3e374b40af24749c1d3c274950af0676169d847760e9d827))))))) else (if c < 1100 then (if c < 1076 then (if c < 1064 then (if c < 1058 then (if c < 1055 then (if c < 1053 then 0x76601d97076591d95476501d93476481d91576401d8f076391d8d376301d8b476299d4b2 else (if c < 1054 then 0x76711d9b476691d8b476651d49274b91d26474001c210314c0d71030080d6b031440bfc0 else 0x76981da5076441da4076181d34074a01da3476891da147682dd9f4767add9d4300c0bfd0)) else (if c < 1056 then 0x76cd1db2076c4ddb0076be1dae076b51dac076ad5b4e076a85da9076a24c0702ff81da70 else (if c < 1057 then 0x669657dd45e4cd763b5c7096fa2537d12610115891f8a35e1cd6ca2bc5ddb6076d45db40 else 0x5c7a96fda742c1cc046d5c1b0e771649c2b069a85a50669a01a4d735ed4af456799d9cf0))) else (if c < 1061 then (if c < 1059 then 0x76f81dbd076f11dbb976eaddb9376e29db72679d99d2158c8160425e589766a538892643 else (if c < 1060 then 0x69c0487001cd01a487729ddc9077229dc7777181dc5077105dc317709ddc1a77029dbf2 else 0x6c2dd62f158048d6da77481dd1077411dcf577381dcd275e51dcc975cdddcb501b502014)) else (if c < 1062 then 0x74f4dd2912bc5dddc1776c1dda177655dd81775c9dd6177565dd41774d59a815f811b4e1 else (if c < 1063 then 0x777c9dde077749d940766d5d9207534dd89176651d87175289d37075009d3572bd15d2b1 else 0x70880c57035cc4c08035b80c5212ffc5de7077981de5277911de3077881de1276991de00)))) else (if c < 1070 then (if c < 1067 then (if c < 1065 then 0x77ae1dec877ac9dea877a88c09130001de9277881de80764d5da4476201d36874a81d010 else (if c < 1066 then 0x77cd1df2477c69df0830100c04477bc1ddd077b81d8d077751d8d474c01d30477b49dec2 else 0x35ea8c5472bce9df9077e0ddf7a77daddf5077d19df7077d91df5a77d21df1077c19c520)) else (if c < 1068 then 0x693c8d7a031508af3067a099d1a669c97dfa5c7596fc658c41603253869263b115e11f91 else (if c < 1069 then 0x538412634669dd7df05c7616fc874311d02873041b56b6c34da6b0693ddb5646c365a6ba else 0x780c1e02077fc1dfe778049e00277fe9dfe277f45dfc877edddfaa67a1d9d1058c696037))) else (if c < 1073 then (if c < 1071 then 0x1c501a6406941e0621274849c201c401a607814de04b7805de00777ec9dfa078165e044 else (if c < 1072 then 0x70909c2323155579515d95cc55a7829de09a773a1e08875dd1e07477389e08275dc1e070 else 0x78441e106783e9e0e678361e0c3782d1e0e378349e0c6782c1795b5d965d03071499c2c2)) else (if c < 1074 then 0x77805de8077785da5476401d9a576391d4c374cc5d3f374c60af3474cc1d3f274c64af35 else (if c < 1075 then 0x30144d72131580c05078541e140784c9e12477801de8177781da5576405d9a476395d4c2 else 0x785d1c25030184c06078589ddf277b89d8f1777cdd8f074c99d327707c1d04031584d720))))) else (if c < 1088 then (if c < 1082 then (if c < 1079 then (if c < 1077 then 0x302a8c0a0786c1de4078481d95a77929d95074e29d38078651e1a47862de19b78611e17b else (if c < 1078 then 0x78891e21878901e23778811e1fb78881e21278801e1f178751e1c351d81e1e278741e1c6 else 0x35f0caf5366a517e165e5c176775c7d16fe458cc16050538c12654116011fa735f18af56)) else (if c < 1080 then 0x538d1265066a417e135c7c16fe06d611b0f571681c2d269a4da51b6d601b0fa69a59a511 else (if c < 1081 then 0x78b81e2d078b01e2bb78b11e2b178a9de29078a1de27078981e25758cd160545e5d17679 else 0x75ec5e31801d5c10f4043804ad001d5810f578b91e2d478991e25978aa5e29478c01e2f0))) else (if c < 1085 then (if c < 1083 then 0x78d49e34151ecd9d3451d89cc2451ec99d3577485e321782ade33075ec1e31977481e320 else (if c < 1084 then 0x7504dd3952bd51d3b075049d3942bd55d05078dcde36178e49e38678d4de34078dc9e360 else 0x78589e13277bc9d98176711d96575389de7177a49de53769d1d98076715d9647538dd3b1)) else (if c < 1086 then 0x765c1d3a174e80454070980c58135d00c0b135d04c580302c1de7077a4dde52769d5e150 else (if c < 1087 then 0x79005e3f078f81e3d078f01e3b178e90000074140c0c130301e1b477981e140765c5de61 else 0x126405d675cd9e43079080c2d030641e25b7706ddfa475a11dd3475f10048401711e410)))) else (if c < 1094 then (if c < 1091 then (if c < 1089 then 0x75f81db7475f9004a001291e44068341e42030b80c1a17898ddc2677ee1d69477501d7d5 else (if c < 1090 then 0x78a2ddb8a77f6dd7f576e2dd7f4012e804bb75d49e4523cb00c1b0306d1e27076dc1dfc0 else 0x791c0c2b030741e29076fc1e0b075981db907600004c001681e46002ba0f2c230704c1c0)) else (if c < 1092 then 0x687a5e473709c0c2c030785e2ab7702de0c4759c1dbab7605404d7016d9e49075dcde482 else (if c < 1093 then 0x79385d79479365e4c0308c0c1f078ac1dd5077f81d5e076ec1d820013800520792cde4a9 else 0x79481e51079405e4f000001e4c930900c20178b09dd6177fd1d5f476f11d835013d00538))) else (if c < 1097 then (if c < 1095 then 0x79611e57030bc0c21078d01dc3078025d6a076f41d8490142405e079585e55079501e530 else (if c < 1096 then 0x151806077964014a0795c0c30030881e35377101e01975ac1dbe0761540519017c1d7b0 else 0x77605d61001558061779701dce0796c1e5a030c44c25078b49dc5078341d6c5775c9d600)) else (if c < 1098 then 0x77651e02475895dd95758900568015a5e5d06b251e5a030c84c26078b89dc6078391d6d5 else (if c < 1099 then 0x30a04c28078c09dda0780d1d63577685d634015e0057977411e5f079780c271309c1e2f2 else 0x798d1e62030d40c29078d81dc9078101d700776c1d64001600064079841e6006b455e5e0)))))) else (if c < 1124 then (if c < 1112 then (if c < 1106 then (if c < 1103 then (if c < 1101 then 0x79981e65079900000079880c36130a81e3727729de05775c55ddc17595c05980195ddd20 else (if c < 1102 then 0x70a00c33130cc1e386771dde0f675b99dc7675b9c06260189de680799c5e681799c1e651 else 0x79a41d06030d04c34078e49dc8a78411d6f17722dd6f0018d8063779ac1e0ab79a81e690)) else (if c < 1104 then 0x3b69cc5982dd19a8b479d15e73030dc5e72479c5de70979bc5e6e079b51e6c02c70c2f30 else (if c < 1105 then 0x79e9de79079e25e77679d91383863069e756111a1d070316e0d76030f2d8bf54295d0a37 else 0x7a04de6f079b50b74a7a014c3d74e04cedb10bfd84d8027309e7f679f95e7d679f01e7b8))) else (if c < 1109 then (if c < 1107 then 0x4291cedd735d50c5a830e5db6a26d191e87a7a180c3e03b72cc3807a14de8437a0cde822 else (if c < 1108 then 0x7a469e9037a3c1e8e07a35de8c07a2e5e8a47a25d385a7a20044a2317698c084e0a10a79 else 0x7a589e9527a509e8437a049e71779b85b6a87a4c18c353b79cc3a9131cc4dd0272c5e922)) else (if c < 1110 then 0x11389d080317058c2b4e12d0a67429a4ee073172dc64671381e9827a5c0c4003b7e8c3b1 else (if c < 1111 then 0x132804e4012949e9f67a7a9e9d67a711e9b47a69de9d37a701e9b07a6a5384163085e996 else 0x73cc1ea2030fc4ee2b30fc1ea127a509e8327a50de83379c21e70971919ea0770a48ee17)))) else (if c < 1118 then (if c < 1115 then (if c < 1113 then 0x7a9c1ea607a941ea494e1998c467a8c04522317998c434e18d0a8742a24ee373178d4770 else (if c < 1114 then 0x7a149e9637a14de72579c9147707aaa8ee47135c84e907a9d1ea647aa41ea877a951ea47 else 0x7aac1e9707a881e8617a5c5e86079cc5e73073ec1eac07aac0c4113b96cc4107a589ea12)) else (if c < 1116 then 0x7a8c9e8827a651e7557a20de754274189d073b9ed3871631458c504e1c10a9a42a6cee6b else (if c < 1117 then 0x7a2c1e9a079e01e8907a0009d1027541eaf57aba9eada4cf144d8b1049cb6a13ba2cb6a0 else 0x111d0c49031145ea537a30de9b379e4de8a32dd149d2727599eb0131201388031101ea40))) else (if c < 1121 then (if c < 1119 then 0x275189da763184c4c131181ea627a3c9e9c279f09e93279d889d382765152a17ac404dd2 else (if c < 1120 then 0x79e91e8d079e809d74275c1eb2a1391c44b731344c4707a9c9e9047a751e7d56da85e774 else 0x312c4c4b07aa49e8e271911e7b17a38de7b0276189d87707c0c4a431281ea807a351ea00)) else (if c < 1122 then 0x277189dc773ec0c4e131381eaa67a45de9e679f99e91679f9c9db6276ddeb3013a4844f4 else (if c < 1123 then 0x7ad002ab60a35845c40a29c29360aa21d090313c4c4f051dc9e9207a7d1e7f57a485e7f4 else 0xb189ebe67afcdebe05c800d20053901ebd47af11ebb07aea5eb917ae21eb757ada1eb53))))) else (if c < 1136 then (if c < 1130 then (if c < 1127 then (if c < 1125 then 0x58d01ec797b181ec5a7b101ec387b091ec107aea5ec0a7ad282cc70b20047240b2242e70 else (if c < 1126 then 0x7b30dec227b2ddeb840b3902c89125402c620b3802c877b28deca07b241ec8a66a81b590 else 0xab9428a87b441ed107b429ecf47b3c17984716c179807b389ecda7b319ec287b2e5eb80)) else (if c < 1128 then 0x7434171617b4c5ec687b509ecd07b49debc77b4c1ec697b499ebc60ab9028a7129d82a88 else (if c < 1129 then 0x7b801edf07b201ede67b759edc07b6c1eda77b645ed837b5c1eb407b569ed607b5417160 else 0x7b3dda7e77b9c1ee607b969ee407ae10f2d769e5dee303cb41ee277b841eb607b7d9a730))) else (if c < 1133 then (if c < 1131 then 0x7bc8def147bc11eef27bba5eeda7bb21eeb47af01ee9769f81eea07ba41ee877ae91ee67 else (if c < 1132 then 0x7bf01efb07be85ef907b101ef706cd81ef807bdc1ef657bd41ec227bcc1a7907bd01ef30 else 0x7c12df0397c045f0227c041f0067b341efe77b265b4377bfc1efe07bf51ec647bed9b3c6)) else (if c < 1134 then 0x136406ec034545f0704e240ee910d6d810d534749f05a712c9f0607c141ed007c129f038 else (if c < 1135 then 0x4e281f0c97c2ed33d87c280eec21396c3c707c241eac23badc4de02195df083631c4eea7 else 0x3bb5df0907c4082a5013781f0837c3c82a33136418c8154ac5f0767c381f0d80a84035b0)))) else (if c < 1142 then (if c < 1139 then (if c < 1137 then 0x3332471a07c5516b54050518d80522c0a0407c521f1387c4a0c8f07c2a9f1120a9c84e50 else (if c < 1138 then 0x7c819f1f07c7a1f1d07c71df1b77c69df1977c601f1767c59d447364e8ded8478ee5b5a9 else 0x7ca55f28418d81f2707c9816090465dc4eb0050804be07c95dbf207c911f2307c881f214)) else (if c < 1140 then 0x4f0a5196745864ef177cd1df3307cc85f3197cc01f2f01c68df2e47cb51f2c27cacdf2a5 else (if c < 1141 then 0x323c9bb377cfd5f3e97cf51f3c07ceddf3a47ce5df3877cdc1f3607cd65446764e458d99 else 0x7d1ddf4647d15df4477d0ddf4277d041f2847b645e3c4332dcef2132415ed707d000cca7))) else (if c < 1145 then (if c < 1143 then 0x582813c393246464707d351202414b1144502a9c0cca07d321f4b87d2a1f4907d200ef30 else (if c < 1144 then 0x7d641f5867d5c1f5667d541f5407d4c1f5207d451f5007d3e1f4e47b681e3d96d6d18da3 else 0x7d881f6177d801f4117ca5071207d7d5f5e0458a44eb014b51f5d96e601f5c47d6c1f5a7)) else (if c < 1146 then 0x7dbddf6e13bd01f6da02b89f6ca7dae9f6aa7da55f68a7d9c1f6607d94064777d915f631 else (if c < 1147 then 0x7dd5df7467dcc1f7207dc6593b17b6d9e3e8333618dba4f1211987458dcef57324a1f706 else 0x7df99f6007d099f2a47df45f7c051218ef607deddf7a051159bb367de55f7867ddd1f768))))))))) else (if c < 1339 then (if c < 1243 then (if c < 1195 then (if c < 1171 then (if c < 1159 then (if c < 1153 then (if c < 1150 then (if c < 1149 then 0x3be01f8c77e2d1f8a77e25df8877e1d9f8677e14df8407e0c0ef717e099f8157e019f7f6 else 0x7e401f8f95128593d17b719e3f86d700ccf16372d3c5b4669d16493be5cc93b7e3adf8d7) else (if c < 1151 then 0x7d859f4377cacdf9bb7e69cefa77e641f9876f3d9f9757e599f9547e511f9377e48df910 else (if c < 1152 then 0x7ea1852f87e9d9fa667e959fa477e8d9fa227e841fa003bec1f9f77e791f9d77e71df7e7 else 0x7eb41fac95125993c67b741e402333993c6a4665d16593bf5cc94a7eae9faa47ea68efc1))) else (if c < 1156 then (if c < 1154 then 0x7ee55fb8063754efe77edcdfb6063605bcf77ed69fb407ecddfb247ec5dfb037ebc1fae4 else (if c < 1155 then 0x7f0d9fc267f05dfc067efc9fbe07ef40eff07ef1dfbb47ee9df9c77dfddf6217d11df2c2 else 0x79061b5d4334198de9582c13c79466dd16693c05cc9597f1c1fc603c001fc56001c1fc46)) else (if c < 1157 then 0x7f511fd307f49dfd147f41dfcf07f381fcd07f301fcb47f281fc997f21144b664f99ede0 else (if c < 1158 then 0x3c0c1fda77f651fba77e75df8077d8c1f4577cb51b9807f615fd703c09dbee67f581fd54 else 0x7f8a80ae47f84052d714b0824647f801fdfa7f78000007f74014290506059907f701fdb0)))) else (if c < 1165 then (if c < 1162 then (if c < 1160 then 0x7fba56b587fb41feca7fae400747fa81fe9b7fa1052f07f9c1fe647f96df8b07f901fe30 else (if c < 1161 then 0x7d901f4607cb81ff747fd91ff5b7fd2c712b7fcd063643c101ff297fc65ff097fbe52022 else 0x7ff1df7b07fedc4c737fe802b900ae002ff01221ded767fe61ff807f641fbb07e781f810)) else (if c < 1163 then 0x5130586d16d780cd15637ed60c04c0ed19c7459e4f057325adbee67ffa9fb767ff41f990 else (if c < 1164 then 0x80102003080080f0707f69dfbc77e7ddf827191d9f4771c68e001080000f06711c01fff0 else 0x79094cd216380119d045a00f080325c600207fe11fdb07ef41fa007e0c5f6517d201f2f0))) else (if c < 1168 then (if c < 1166 then 0x8038200d08030193f13c241f16b7064200b180286009080202007080182005051345edf1 else (if c < 1167 then 0x7dc41f4f07cd41f170804d2012b804500d941221045d08040200f44f200f0a07f225f4e8 else 0x80542014080401fca77eb5df9077dc9df5067cd9df1838004200f04f241fc907eb01f8f0)) else (if c < 1169 then 0x8074201c0806c201a0806460181805c20167800402b873c2c1fff77f2e5fae97d461f19b else (if c < 1170 then 0x7c6ee01e011c1dfdc07f5ddfcc77ef81fa107e105f6617d79df5267d241f3007c99df1ab else 0x65005fce77ebddf9177dcddf5467cdddf1cb807c06d210ae5c45d43c30200077f35df536))))) else (if c < 1183 then (if c < 1177 then (if c < 1174 then (if c < 1172 then 0x7ce41f1e080886021004246020002b8200d07f3ddfb0b7e4adf7417d559f3807c74e00c0 else (if c < 1173 then 0x7e525f7d17d5d9f3a97c7ce025080901f7b7808c2005050181fd007ec41f9307df01f560 else 0x80a05f997809c200707f481fb307e681f7507d601f3b07c81202607e2d200607f465fb29)) else (if c < 1175 then 0x7dde5f5a17cf65f2231b88202a714bd200807f4ddfb477e6cdf7657d659f3c77c84a0290 else (if c < 1176 then 0x80281fd587ee4df9607de01f5b77cf95f23280b01fb7080ac2009063841fd497ee25f959 else 0x650454e904679e02f080b804c04802c1fd897ed4df9797de65f5c97cfe5f24380b500070))) else (if c < 1180 then (if c < 1178 then 0x3c41e038080dc203603c3c2035780d26033366d81169605f44f0eb80c8de43080c660308 else (if c < 1179 then 0x3c51e042681042040b3c4de03f380f8203d13c49e03c080ec0f11780e82039763a553ca3 else 0x69ae0480790e07f5014e00f167712da047081180f1528114a04400646e0431645958e2a)) else (if c < 1181 then 0x53a813d1b4f2ce04c68112a04b680f9204a080e5e049480d0045eb1bb0047600436480c0 else (if c < 1182 then 0x8141e0380813e5a730813a20037651153cd3650d53cc33c5de04d08039d9b70651859425 else 0x6515605500aec04760803c13d20815220536036a200483c61dc4b6814aa04268145a03c0)))) else (if c < 1189 then (if c < 1186 then (if c < 1184 then 0x80d1e00d84f3c205780aed445e08031d94711b4c53ce53c65e04d4811960563064420107 else (if c < 1185 then 0x817e203c0817820070817420390801a605c080e1205b08014140708168e05940429a0583 else 0x8194cc984802e20646818c204408028a0422818820099638c606161b8c6060480f820087)) else (if c < 1187 then 0x67c4206c081aca06a081a4d04c94f4d98e563269e0680483000b6063910a044819ce0663 else (if c < 1188 then 0x32660f1db32665ee1281c48c98832624e10081c0206f20da4206e445adc374002dc206d9 else 0x81e84f20781e4207873c7c2077081d9e075581d6a074463994f1e781cce072063905ee2b))) else (if c < 1192 then (if c < 1190 then 0x2da8240567f80dbc03c89da2b782000f21081fec000081f6a07eb81f6e07b181f2e07b0 else (if c < 1191 then 0x8221a0767821d20863821500ae7820400b7402d94240a8210208328209da0d0820500b70 else 0x823c20900823d120c58238120ca8234208c1822c00000821c20866821400ae9822820890)) else (if c < 1193 then 0xbfc02c197b84209623c9c2070081c120950824c20940824d036908248036943c8c20910 else (if c < 1194 then 0xb06442d0380c0f247639c58e7b68ade099a81cda097481e4209870bfd02c1781cce0970 else 0x827c0f29063a004260827800ae74334209d045b013d4081ae606998270209b0826800e14)))))) else (if c < 1219 then (if c < 1207 then (if c < 1201 then (if c < 1198 then (if c < 1196 then 0x3ca020a3000000f2b081e860a2081e420a103ca820a0781d9cf10081d1206c581aaa0733 else (if c < 1197 then 0x63adcf29082a9e0a9013bde0a863ca2e0a727914a0a68829a53d8045b260a54829000e20 else 0x436445f4043420b207914045f0043520b113cade0b0082bde0aea3ca9e0ad082b020ab0)) else (if c < 1199 then 0x4f5d13d794f5520b277915e0b3182a520b6082d420b4182b0045f90435e0b3b82a4045f7 else (if c < 1200 then 0x82e520b0082f02038082ec20ba082e41a79082e093d604f590f2e782dc13d704f5dd3d50 else 0x5a6d01ce463b00a040830220bf882fa0c9c03cbde0bd482f41a79782e2a038482ed20ba4))) else (if c < 1204 then (if c < 1202 then 0x4649c4f60073c20c876b5520c748319a0c58831120c3683081442364ccdee54331a60c14 else (if c < 1203 then 0x3ccde0cf08338116e713d9054308335ccc593ccadee4383300c9c8832c20ca9225020c97 else 0x836060d7463b54f3678358e0d5063b04f359835020d38834ad44333cd020d17834119345)) else (if c < 1205 then 0x838401cf9073a059f083810f3896b5260df43cdc20dea02b820ddb8372e0dba836820d9a else (if c < 1206 then 0x83a6569b883a280ae2839c20e6b839520d3a839020760838e1f8b0150dc2510838a80aea else 0x83bd04ca00afe60d1483b9e0cf083b402ff0127e5ee4083b220eb0832820ea922524f390)))) else (if c < 1213 then (if c < 1210 then (if c < 1208 then 0x83c820eb9838120cb083d020f3083c80f3a983c419351331d58eeb3276dad4983c160d66 else (if c < 1209 then 0x83e820f9083e020f7083d820f505110193607b981e470332018ef0464e516f93cee4c9e0 else 0x840421000037c049f9118260ff083f813d903cf660f10830ae0fd083f00f3c96c1420fb0)) else (if c < 1211 then 0x84152076783d820c4a833c2104783d4193701b50210307e2e60ff0840820fe04f6820c39 else (if c < 1212 then 0x842c20fc0831a610a00afe4460983e02109083452108483dc140408315e10708418010b0 else 0x465004b0783ec210e002b960fa0835c20c7a8359a10d083e418f001b80210c4834e20fd0))) else (if c < 1216 then (if c < 1214 then 0x84502113713c0211215e981170007ba5e49060100f3fb8444de4821380a1109843e179c0 else (if c < 1215 then 0x84804f437847c211e084740f4278470211b9846acf419846421184845ee116084540f407 else 0x3d15db43784ad212a084a4212803d10e127b8498e125b063ee124b848e850ea84882121b)) else (if c < 1217 then 0x84bc046201186c865084b82118984b4611341259010d024d9c201084b25e487254e456b0 else (if c < 1218 then 0x69f82136884d62134883ce6133b84c80f46011b257a705e7413db084c42126484c2e11b0 else 0x8500a13f53d1de13e084f60b7226d0de13ca847d213b882c0213a780f02139a84e2a137a))))) else (if c < 1231 then (if c < 1225 then (if c < 1222 then (if c < 1220 then 0x83fc21459851002c001259e0fe94f702143484cec0e0885098f48784a2a1410143820f47 else (if c < 1221 then 0x851c614b080f1e14a083d4193818458214931b5561480844dcf4978454214768519c4f00 else 0x84a55b6968545c18f083e12150082c0214f983ddd4050853ae14d00432214c08461e0f67)) else (if c < 1223 then 0x84aa60b1069fc1b690851c21585855d61565855521544854d2152084cc0461083f1cf4a7 else (if c < 1224 then 0x8575211b783f5e15c4856d42c0711890f4b784ca615a98566046c0850a988fa3325cc9f2 else 0x8595a1646328020fbb858e616288586e126383e9e11f9858020f9463c4615f3857986e15))) else (if c < 1228 then (if c < 1226 then 0x85b4216c085ac216a085a5a16845094d9103792e4cb33859c1560005380aa70281021666 else (if c < 1227 then 0x15092173932ca4f4db7ba12172032822171085c2484a085bc1183613e8414f185ba1ad50 else 0x85f2217b13d41e17a085e6542633d3c2178785ddd91153d39e176085d42174445ca44fa0)) else (if c < 1229 then 0x687821840053cc14e8167c0f5236b51e18303d466182302c9e18138600e17f285fa617d3 else (if c < 1230 then 0x3d4c218c25582218b702c9e18a08624a1884834c2187a02baa186814bc854220918a1850 else 0x131d82bd085e82192985e12191785d8219000bfc048967ba1a18f88638217008636484a9)))) else (if c < 1237 then (if c < 1234 then (if c < 1232 then 0x328421950863a6174585c4219908660219708658219503d51e1940509c591216b522193a else (if c < 1233 then 0x6c1421a00867c219e08674219c0866c219a050a0191307ba41e4c032d01184645cd8f556 else 0x85a621a60869400dd01225c4649869021a304f740f57686506168b868821a1063c80f566)) else (if c < 1235 then 0x3fc21aa602ba219b085aaa176186a5e19a0645006d6086a0452f8869021a70868c13de0 else (if c < 1236 then 0x85b2a1b1085e861b00867821af6834e619d085aea1ae085e161ad4867013fc086b021ab0 else 0x461ac4b13461421a0086cd00b24868821a1063cc216da86c806d800af444649867c217b0))) else (if c < 1240 then (if c < 1238 then 0x86f421bc286ee61ba046148f59286e69e4d486e121b75865aa1b6086d44923086d059ab0 else (if c < 1239 then 0x793a19ac063ec18f404f7c0ca20871416820871021c30870ae1c13870021bfb86fa95650 else 0x45d1e1d0005e521cf0873921cd0130421cc04c9c61cb0872821c90872021c708051e1c60)) else (if c < 1241 then 0x876404f10876061d7b87582197b63d821d5086d421d43874ce1d298744163a05ca418f50 else (if c < 1242 then 0x87918f5c7878c21e278784581403d6c21e07877d04ef78778e1dd6877021db03d69e1da3 else 0x69021eb27936e1ea124440910115ac8f5e76d0ce1e9087a061e703d76a1e64879501f83))))))) else (if c < 1291 then (if c < 1267 then (if c < 1255 then (if c < 1249 then (if c < 1246 then (if c < 1244 then 0x4f8061f028794e1ef01198c46591bb021ee08789e1ed0877e61ec68765047740435c9330 else (if c < 1245 then 0x86d861f39248c61f2063e14f5f711b504fe04c9c61f108055d63b05ca819ad063f058f75 else 0x3d81e1fb46d0c21fa9847e21f9580e221f85810821f7287d8a1f5269f821f448662d8f95)) else (if c < 1247 then 0x880184f10869061c6487fc21fe00af984770868cd3e1087cd21fdb0379a1997875621fc2 else (if c < 1248 then 0x8804604208814219a16461a1dc08810a20331b5da20268764191763d85e1db04cb2a2017 else 0x8788219db63e9620c080e0220b0867193fd088282209188206207a040062066877c219b7))) else (if c < 1252 then (if c < 1250 then 0x3d89e1f14879e21c846da5e212107e0219f7871e22114847e221008678e20f48838620db else (if c < 1251 then 0x875a61d1987265a7f76da422174880422161885462141884c21f30119421a1b63f446d91 else 0x886da21a7879661a27872e221900af8046603d8de1f2487292218611b418e9a50a8572ba)) else (if c < 1253 then 0x5140d94a37bb01e5093354c0ce0887c16cf0003018fe02810221e88876221c8328c21a04 else (if c < 1254 then 0x4685807510034222a62ad82229488a0222708898222568890222388888222174ce422206 else 0x3d9e6237988da2235188d2e2330033a2232a88c5a230888bc222e688b4222ca0050222bb)))) else (if c < 1261 then (if c < 1258 then (if c < 1256 then 0x89066240488fc223e988f5223c788ede23a088e422389513c5949163fed3e2b4681d1769 else (if c < 1257 then 0x891c6246189146244088b21eeda79440cd493da28ca487bad22430334e4ca38280e62425 else 0x3296402c0893d1244402ad144e065200cd30893a224d88932224b03da5a24a1892622481)) else (if c < 1259 then 0x8969225908961e25708959a25508951a253089480baf08946225067bb81e5296400d3e39 else (if c < 1260 then 0x8988002c0898622600897c225e989752244088b640bb089721177601d540ac1896d89dc0 else 0x89a12267789981454a7bbc1e5323366990154f9151a5945e1cf6a732996265a89912263a))) else (if c < 1264 then (if c < 1262 then 0x88b9a273589c8194e53dade271389c0194812a05e26fa89b8e26d089b0226b789a822699 else (if c < 1263 then 0x4689d17973db5cca7a89f2227b789e8627903db2e278389dea276389d4e27438975e2453 else 0x8a19628568a11228388a09e28168a00227f089fa627d4652c5ef0679520cd61640a93e5a)) else (if c < 1265 then 0x8a38e28da8a30e28b389d0e25e08918e22f08a2aa28945144cf6e08a20228745138ca598 else (if c < 1266 then 0x8a491453165345ef1679560cd81640ed3e6b4691d17a93dc1cca8b8a45a29078a3c0f6fb else 0x88c2229f68a79cf7178a74229c728b9a29b58a69a29948a61229778a58e29508a5022939))))) else (if c < 1279 then (if c < 1273 then (if c < 1270 then (if c < 1268 then 0x468dd17b93dcdcca9a8a99e2a548a92a2a303dcae2a238a86a2a038a2ce2753897e62473 else (if c < 1269 then 0x2a99e2afa8ab822ad78ab122ab78aa8e2a908aa022a795148594c17bc81e562335c53e7a else 0x3dd6e2b538ad2a2a038a30e276389826248388c5a2b398ac8190453dd1e2b138ac018fe1)) else (if c < 1271 then 0x8af622bc0001d22bb002b1c0ab208f522ba08ae6a2b80000022b700034c00c8090022b60 else (if c < 1272 then 0x4910a2c895b3da2c708b1ae2c5402c8a2c408b0d22c2b02b8a2c108b0022bfa000022be0 else 0x89dc226108924223208b46a2d038b3ea2cea02ece2cd300528f7608b3262cb98b2a62c97))) else (if c < 1276 then (if c < 1274 then 0x8ac5a2d708a7422d698a2262d5789c4e2d400bfc04ad67bada2d388b4822b408a84228d0 else (if c < 1275 then 0x89e0c02c98928c0ce83de1d4551653c4cda16416d332b4699d17c93dddccaab135c82bca else 0x8b6022d2a8ad822a308a3c22790898a624b988cc22da08b6422d803de6e2b538a88e28e3)) else (if c < 1277 then 0x8b8022dfb8b7a62dd98b7022db0515a595097bcc1e570336e59060469ed17db3deaccab0 else (if c < 1278 then 0x36c04ad409c2a2e508b9013e803df2e26628942cae098b8c0f7b68a49627d58b8822e10 else 0x2ebe623934ce622e908b9013e908a9ea293a89faa267a8946a238a8882a2e808b9c22e69)))) else (if c < 1285 then (if c < 1282 then (if c < 1280 then 0x654662a938a54e280389c8e252988e8e221509d662ea3001d22e508aa0e294389fce2683 else (if c < 1281 then 0x8bba410508bb5800008b7022aa58a596281489cde253988eee22288bb0227158bac22db0 else 0x8954223d58892a2f108a2222f088b74140808aada29768a25a26968951a23c6888da2ef0)) else (if c < 1283 then 0x8bcea2df08ab4229e08a08226b48958223e4889522f2002ba22de08ab1629858a2a626a5 else (if c < 1284 then 0x8900a22788bda426b08bd4c0b278b8022ae38a7d2283089b0a257988fce22688bd0229d3 else 0x8acee29a48a15226e489666241a88a222b148bdc22e10641c22b228a64a284289b4a2584))) else (if c < 1288 then (if c < 1286 then 0x7961e2fa08be691a8b8b8c22afb8a6d2286489bd225a489092229b8be002bcb09c222e20 else (if c < 1287 then 0x8c0d004b78c08a30168c0022ff03dfde2fe78bf404f208bf04b56045f9803b53df9a2fb5 else 0xa65036f23e0ae30b48c28230988c22214143e06630708c1a450e48c16cb2103e0023047)) else (if c < 1289 then 0x11a083c7a8c40a30a28c3c230678c38230398c3562fd412a0810d70ab8006618c309e583 else (if c < 1290 then 0x8c5402a7412a022e4a4fac2314a8c4cc0dca8b68231203e11e31108b648f837323813ea2 else 0x8c6c231808b6e195218c00231a00cf8631968bf4231803e15e2ff08c5d84f208b9423166)))))) else (if c < 1315 then (if c < 1303 then (if c < 1297 then (if c < 1294 then (if c < 1292 then 0x8c1922de08c881a7988c8662dd65024232078c7da31e58c76810668c70230308b701c4b4 else (if c < 1293 then 0x6d0d232808b84990820ccca32728c28a2e008509630808c981b43b8c9422df08c92a3230 else 0x24dd059f2155c8938024dec59f00aa8024022038459900aa9c240a0aaa824078b8d22e20)) else (if c < 1295 then 0x8cb5a32c08cadc0d508caaa32974d24046a011a414ec253b014eb00aa882400155c09382 else (if c < 1296 then 0x8cea411a011ac172f08ce6a33808cdc233668cd62334a8ccc233288cc5a33008cbc232e7 else 0x1ad010d74fb0234508d10234308ca4234278d05e34078cfde33e78cf5e33c74d24233b9))) else (if c < 1300 then (if c < 1298 then 0x53b54afa77438234a46dc4234977170e34806a20a34756d7da3460019c02a040c8800682 else (if c < 1299 then 0x8d39e34d70904232b70c6c13ed08d32a34ba8d0de32aa5cb95d0fa6a169b60a694a4b8ea else 0x8d664112714e293ef08d60235708d58232c08d54235408d4c235208d44235008d3c13ee0)) else (if c < 1301 then 0x53b9d41f04fc0236048d7d235e28d74a35c58d6e220608d69c1a501222051e006981b5f4 else (if c < 1302 then 0x8da2636798d9a636598d9253f108d8da36268d58232d68d86e20a6804619ba16d84d60d5 else 0x8dbc006700b040525004365a8878db9411940435d3f208db4236c08dac232e48daa63699)))) else (if c < 1309 then (if c < 1306 then (if c < 1304 then 0x8dae632f08c76a207a826a5315a6a129701753bc231c08dc8205838dc4214c08dc1e2066 else (if c < 1305 then 0x8dfd637e08df5637c08ded237a08de553f408de0237708cc0237608dd413f308dd023730 else 0x5839d4f2049a9046c647ed4d8302bec238708e1a638508e11238308e0a238108e0061330)) else (if c < 1307 then 0x6c625a87a69689b62b6c44da650694dcd8aa2bfe99e37675019ae75f90172585c0a1637a else (if c < 1308 then 0x826da0532804819de2676696430585094f7249b8d9b925fa2973655c195d10473101b734 else 0x8e31231f28bbca05a7808aa38b38e2ae38908e202209a86b0a31378b99e1fd08695e0a45))) else (if c < 1312 then (if c < 1310 then 0x8e4ca39208e46a14c08e41e35c98e3d01a74127c0523708041c5c98e3a8117915ac238d9 else (if c < 1311 then 0x8e64a398b8e5ea14eb841de396b8e562133b840257a9b5db81c5db70be979eb5da923940 else 0x8e76e39c88e6ea37308db2636268d5c234d75c18234ba8d11e33308cea6331649aaa39ab)) else (if c < 1313 then 0x8e90239b08cd023a3a8e8a93f608e84237708cca1733053c0142004fd423a0a8e7c239e0 else (if c < 1314 then 0x8ec963b108ec123af08eb923ad08eb0e1f308eac63aa08ea663a808e9e23a608e9553f70 else 0x2bf899e266754579f75dac172605c0c1638a583dd4f3049ad046d747f00d8412bf063b30))))) else (if c < 1327 then (if c < 1321 then (if c < 1318 then (if c < 1316 then 0x66e0d7e7b5cd5d730a5c15dd1127314dc5e770c29a86a69649b63a6c489a64169518d892 else (if c < 1317 then 0x8822e1ab38c5162e75850c210178294209c78150a0130677499d8a5ea2576d453d9126d0 else 0x148501a486dc523ba90454056b48ee423b828c7aa2eea8535210698edca3b6a8ed423b40)) else (if c < 1319 then 0x584e1731a6dc85b17966bc57e508efd23be48e4963bd58161e3bc58d7823bb2069c04890 else (if c < 1320 then 0x8d15e33708cee6335849ac23c518f1123c318f0960591808563c118f00a1f318699d6421 else 0x53c4142104fe023c7a8f18239e08e84239c88de0237408db6636368d60234e75c16634ca))) else (if c < 1324 then (if c < 1322 then 0x8f3c23c608e7c233808f3823cd08f3023cb08f2823c908f2013f908e92a39db8cd997320 else (if c < 1323 then 0x8f502394a8f4c231ca8f4aa36068f440069012b504e58019a1d0e08f42407590dbc13fa0 else 0x3f623d697e2c13fb08f3c23c7a8e82a339a8c80a3d528ba00cfe2744899d64508823bf0)) else (if c < 1325 then 0x8f01a388b03eda3d9b14bc23d704ffc23b548e5ac0fe88d7263d808f5c13fe08ed123958 else (if c < 1326 then 0x8f74140208ed8238a003e423dc1001ea3da0500423c148e26c0fc68d7ae3db08f6814000 else 0x502823c208e5e810788f8020d3a8f75540308f55e3b788e2e2361203ea23df08d8223de0)))) else (if c < 1333 then (if c < 1330 then (if c < 1328 then 0x8fa423e808f9c23e608f9423e408f8e80ae28f84140b08f0d2398b0422239208f89e3e10 else (if c < 1329 then 0x40423ed402c9e3eb0503423b948e6ac10488e5023ec08fac140c08ee223992040e23ea0 else 0x8fc823f188fc1846f04a8c23eea503c23c548e34810268efea3efa8fb8140e08f10238c0)) else (if c < 1331 then 0xbfdc4f508fd0195555044cf877131cc4f408fcd5ead03372541063e1a82fa213610c5f8 else (if c < 1332 then 0x65505f0b67aba0cde16426d423b46a9d17f93e264cacb8549a12f98fd51457350480f880 else 0x8549a3ff93e2a44ca013e663fe68ff563fc68fed23fa48fe5e3f838fdc23f60118e54591))) else (if c < 1336 then (if c < 1334 then 0x7abc8cdd6509291a9746024f8c732b6a213787bd24034900aa4010504c0f8b0900263f06 else (if c < 1335 then 0x13f8133b19031e40ba9028240979021240779018e40509010046795161995365cd11f0c0 else 0x9040240fa3e3dc4d720ce4240e050500f8e0900263f18884e640d064294f8d7131cc4fd0)) else (if c < 1337 then 0x8fda52e5890440f910516819560337c190b046ac118103e400cae09038240108fcc63f20 else (if c < 1338 then 0x901863f814d06195705054240598fde63f494d006412054b004f49117412e603e4824049 else 0x8fe9d3438904c14174505c240748fe523f544d0923f90901c23f504d0804f5010b5d4160)))))))) else (if c < 1435 then (if c < 1387 then (if c < 1363 then (if c < 1351 then (if c < 1345 then (if c < 1342 then (if c < 1340 then 0x13f5c464a5068240a9854ad3458905414190902523ff04d102414013e404600506024087 else (if c < 1341 then 0x8ff493488905c0339709c0141c0884d23fcb4d1e190c0506c240d78fedd34669058152f0 else 0x6c4e1d5101115044450a29c5bb60a35828f40a35141e0903123feb2ada141d0903ca40b8)) else (if c < 1343 then 0x74501c3202dbc0d1202db80d8b03614241c07318241b06c66641a370c4a4195696ce4181 else (if c < 1344 then 0x9098200179094242415fa4e4230908ae42105840242009076241f02dc0241e090740b745 else 0x5c9d170441718126c411c011fd736198afd690b8242d390b0242b090a82429790a02427a))) else (if c < 1348 then (if c < 1346 then 0x6dd41b1a571801c3326a24da5cb344d9a55136328b00a52ec59d7666c017e665e80176c7 else (if c < 1347 then 0x85102102052cde09d034bad9da35914161545eac176f953e5126f00b141707074569cc7b else 0x90d02433890c82431a90c0242f08c8ae2f1b8170202598540210948c5622e9887f821a71)) else (if c < 1349 then 0x90eda43a090e42438790dde1ada11d802c6690d845df0177842c8390d49b13b0b3402c60 else (if c < 1350 then 0x90fc243e0883021aeb81542001766ec195b1656857e936d941b14a58e41610090f6a43c3 else 0x2dc6e44c0912ea44a0912424480911e644609115e4200907a24441910c24422910424400)))) else (if c < 1357 then (if c < 1354 then (if c < 1352 then 0x914021087913ee1ad2117c028a7170e42a80913a9a5b70acdc28d09134195c1913419591 else (if c < 1353 then 0x70c5c2e890b2124537911824550915024530911414b2053e0172809148e2f009145a0234 else 0x851417aa05e84245c0916c245ab9165e458084226457490e1049640b2245fb70b2024569)) else (if c < 1355 then 0x9184243a011dc02c8117e802c6491821b1910b4c02c86917664480917c245e8917424470 else (if c < 1356 then 0x919c244a091a024670912424660809261ff0591019b10919564646918c24594918a60239 else 0x91b46464891b2a45b391ade2f0291a8243c912a1828d616f9028a791a59cc660a65428a8))) else (if c < 1360 then (if c < 1358 then 0x90fc203c091cc2472090f82471191c02438791baa44c091bc246e0912c2316034b414ba0 else (if c < 1359 then 0x91eda47aa90f1247806495644108109a479091e02440091dce476191d6e474690e824720 else 0x920424300847d248209204242f09200e47fb91f82459491f0a4430712da47d091f024420)) else (if c < 1361 then 0x9191248ba90c81b4379230248b090c4248aa9226a488a921de48619216a4840920ea45b3 else (if c < 1362 then 0x3e4eccb000d6cc068011548ce0932bda48f89198243406d0da4900923c243309239a48d4 else 0x51745f0e07ac08ce216436d2e4b46b1d18293e51ccb1b7fe82016092445f0d069980ce10))))) else (if c < 1375 then (if c < 1369 then (if c < 1366 then (if c < 1364 then 0x8058195d13e55c4eb01bb014a4192602497a9258249549250249379248241370ae824119 else (if c < 1365 then 0x13e806ec45c3ae49b03e6004f692194249a051700f9700dd1c10d0516e241093e59e4990 else 0xdd00f9b79264249e70aec04eb065786016054b4649d03e688075a0f1c249c0643acf997)) else (if c < 1367 then 0x13e8190f1925415301926e649409282649f80b0004f60924c249a7924824924926a42c20 else (if c < 1368 then 0x338c51ae713fc08a60928e4f9c79276a49809289c2a7601d424970927024960928582be6 else 0x6464d42b932de64a8056240751051780aa70338c24a769299a4a563e79ccb697bd424a40))) else (if c < 1372 then (if c < 1370 then 0x92c664b0092bd898a092b99187713fd0752092b664ac092ade4aa691fc24a9091c41ef64 else (if c < 1371 then 0x92dc24b603e85e4b5092d024b3192cee4803517ccfa0791f824b29517ad42c33e7de4700 else 0x2299c7d773e91e4c0292fc0fa3292fa838a092f6a4bca92eee4ba192e6a4b8064694fa27)) else (if c < 1373 then 0x9320838a2931c64b47931824c54931060d3a930c1f8b49308075291d4588f949306814aa else (if c < 1374 then 0x1229e47e49339c4c731280a470093365ef509330a4cb092bc24ca126298fa509325d5896 else 0x934424cb792c064d30934824d103e99d46053391542da32e2a4c029342a4b74933e04ca0)))) else (if c < 1381 then (if c < 1378 then (if c < 1376 then 0x9354a4d44920523e1791c823d7951845ef7079688ce51646e942ea46bdd18893e9dccb9a else (if c < 1377 then 0x93681960192a464dc21b6844a0211e1e4db29368195f13ea5e4d909361cfa87935ca4d6a else 0x92dce4e0a9350191c592acc6e45937d24b40936424de2936024aa09374048a011e024db0)) else (if c < 1379 then 0x93949e5b01384e4e48938e57a2046c1c4c20935c24ac8930024e20935824e100e2824d50 else (if c < 1380 then 0x93ac24ea13eb424e978f8a64e8385180fac0939de3d8413c1e4e634625de5c06d980faba else 0x26e4079503ec5e4f4293cc24f203ec0a4f1293c0050fb93bc4faf793b9a4ed03eb9e4ec3))) else (if c < 1384 then (if c < 1382 then 0x93e4a4f0a93e1a4eb411e40865793dd23e20125cc6ec093d823d8926cc08ae493d41e5b2 else (if c < 1383 then 0x9406a4ee69401a11f093fe603c093f9db36093f4a4fc293eca4d203ec9e4fa0658457a30 else 0x125c24da0658846db13ed1e4fa493c965044143c24d30940c8fb379408a14766d9e24f42)) else (if c < 1385 then 0x942824d406474650931b956508493ac24d90941ca5062122c04790936024db49415448b8 else (if c < 1386 then 0x1d780aa7050bc25101943c650e132e824d7093d0250d09358250c6942c24f009356e4ee0 else 0x263825161462dc50361d7c25154945024760944de512491d4143096478ccbc9944415a80)))))) else (if c < 1411 then (if c < 1399 then (if c < 1393 then (if c < 1390 then (if c < 1388 then 0x50c4cfb9791d1a51b050bedefa732edcfb8732ee5ef9694680cba132eae51909461e5173 else (if c < 1389 then 0x1f5c64ac03ef1e4c06948c0fbbb948925214947da5202947de51e63ee9e51d0947024773 else 0x14bc252a494a42528314bd252461d7d075e11f5ee52709498a52576b25a52431d7c075eb)) else (if c < 1391 then 0x94c82532456a06531056a2e530094bea52e09485a52d094b0252b692d0252a094a525286 else (if c < 1392 then 0x94ec1ef9094e9253909461a518394e02537694d9a5363263865357263acfbd794d025330 else 0x94fc253e03ef9d432750c8a4c0094f4c4c701230251d894f06474a94ee84c7a1232a4740))) else (if c < 1396 then (if c < 1394 then 0x91e023da950cc5efb679788cbd150ced18c746324fbf732f6e53e694e4251919466e5406 else (if c < 1395 then 0x944ce54631b70448c311e8254539510191f13f01e512a935da543a9509a541791e123da7 else 0x130c654309528252189508251e09525251d8952025410951c64b47951425440648065141)) else (if c < 1397 then 0x9540254f788000fc319539a3db513c5a54d23f0ae54c2797c254b8952e5921066c8118d6 else (if c < 1398 then 0x1bb0255508f6e49b741e56e5540797c89b701e544fc6793d1a55303f14a552895440fc47 else 0x3f1dd9b3464985922566cc1926b648aa55769546847b61bb125560953de55548f6dc47b3)))) else (if c < 1405 then (if c < 1402 then (if c < 1400 then 0x880464f40956ce4ee095686042a9566a042095641b3c09561253f064915924a648d5923a else (if c < 1401 then 0x957ca4ee69578254109574654f09514255ca1234047b09510192711b74654003f21e2015 else 0x9592e563b79840fcaa32fa5efd495880cf8846f9850720ed025615950c25604954425426)) else (if c < 1403 then 0x95a96569095a0248e0959d247b064a19434632fda566457210392451bd0aa7433e12565b else (if c < 1404 then 0x3f30648d095c0146f295bd1435b3f2de47a795b8256d095b108bf095ac118e6141dc3930 else 0x95dc039370e48840b095d91ad1a0ed08402095d4192953f39e574395cc0fcd795c9e5710))) else (if c < 1408 then (if c < 1406 then 0x7bf4257e495f4256c022fd0fcf05720a57c095ece521095ea038a995e400b2995e2c007a else (if c < 1407 then 0x960c0fd0751c094367135c048e995d2a582a95c965815923425800131c04ae091e9657f5 else 0x51c41efe079880cf9064a81437046fe918fb3f468cc00960c257d495bce56d0961425840)) else (if c < 1409 then 0x9630258b065cc0fd3a5d74258a03f4aa57c4962425880961c25860923c23ee091f023dd0 else (if c < 1410 then 0x961c2568696402572a963c25860963a838a79630258b065d025678963406de012b8047c4 else 0x470184c41962825696964c048e711f12589095d1659209620192b095d4c6e809645a5214))))) else (if c < 1423 then (if c < 1417 then (if c < 1414 then (if c < 1412 then 0x9671a59b69669819189665e5986965c919016da00fd5896595e637139c6595a9650183f0 else (if c < 1413 then 0x143d25a1188480fd76968063ef907e0659fa967823df58c5c205603f58659d68f7944f26 else 0x8f7a496f00edce5a82798cc92f00e784fd97969ce5a60969465a4794100fd87968c25a27)) else (if c < 1415 then 0x9610848303f69d97516354047da0f1ea5ac6969925ab09689e5aa48fbc84a9a1bb025a90 else (if c < 1416 then 0x6da6db69158449438793d125b1593d025b1a6d0d25ad4712ea5b0a96bea5aea6d0c25ad0 else 0x6358259e666801627095f0e5b9096e125b7096d865b501c346585796d225b303f6de5b27))) else (if c < 1420 then (if c < 1418 then 0x93d0a5bd0961aa5bc496eea5a209631e5ba0123dc4a90962c997611b7c4fdc796cc23180 else (if c < 1419 then 0x9629e57c99625e5c3993d225c209622192c5970406e959701a5a60961de5a4296fde5be7 else 0x194042ca70b25824601c7c05dc6176c859981b184474011cc44022194002ca60b25c2461)) else (if c < 1421 then 0x1c34163d05904163c01b180474111cc040231de809461251487d711de8494602514c7d70 else (if c < 1422 then 0x65dc25cd0973025cb8972a25c98972225c789718a5c5065e465c411f84047e01c3460170 else 0x745825d246de965d157184a5d0269f125cf7069c02a2469c165ce50cb1020140c7401a48)))) else (if c < 1429 then (if c < 1426 then (if c < 1424 then 0xb990251011c60402465e065d319730e5b52806159be26dee9b15769ba8b02758f88d87a else (if c < 1425 then 0x62180480011fc17b205edc17b101252440b0207287d77259188f9017e4059f40b1e02465 else 0x8065d63f0977425dc2976c25da7976525d86975c25d63975425d48974c25cd2971006c60)) else (if c < 1427 then 0x18640538065f825e50975025e49978e65e29978665e03977e65de1621846f33120425b60 else (if c < 1428 then 0x8c65a5eaa8809a5e90852025e8082a9e5e700696e42600ae402b800ce801a6b69c1a5e68 else 0x8071d9801979665d51805825b70880ce01b7807de01a76704198b165fd570a069b494f43))) else (if c < 1432 then (if c < 1430 then 0x97c101a760af420aa997bd061e015ae1a7c697b8434400691197a097b425d6097b0a5eb8 else (if c < 1431 then 0x8184e15e396e021b2182a0e01d949c519bf069e8972c359002327897ca2060097c4215d0 else 0x97dc06ef022b91c61097d888b601e541981097d425d8097d1e5f3665ec65ed2975c62f61)) else (if c < 1433 then 0x857ce5b909370a14935dc65c6235e90e5fb797eaa508497e6215d497e0079a01280a1480 else (if c < 1434 then 0x1e55d97c6981025da6980c2602098042600097fc65fe097f4d982197d5e5d9597f2a5093 else 0x66d2e5c00982665088982160608981e879a01232a2020981806f101e549b7a09815088b0))))))) else (if c < 1483 then (if c < 1459 then (if c < 1447 then (if c < 1441 then (if c < 1438 then (if c < 1436 then 0x7459e60c9141dc39e5660c260b09770260a265f466040976c6546a8812d618867001b7cb else (if c < 1437 then 0x8c6a99dc9745e998da97022610897eca60f28c9de60e7069c04ae78c66260d8142c03b79 else 0x1b986618a985ea616a9856a6145984ea61299844038a06610660b39774448309706a58d7)) else (if c < 1439 then 0x986c198557ac48fdd7330642fa013740c8419866996d11b9d65fb798682619065b065fc0 else (if c < 1440 then 0x3f7dc2ff013f513b3b13f9241298079d988550e4cfde70bfc04f4011c0261c0121818371 else 0x3f89c4d721428261f0661e992d53f85c4c731418261e73f81c4ca014082416998741986a))) else (if c < 1444 then (if c < 1442 then 0x3f91d472133e8592e350e8d1c1746464fe373308e61d49870661b0124425b309885e620a else (if c < 1443 then 0x987c153331418047a065c855321988c996f09878153109889c502711e0185313f95d52e1 else 0xa35998a154d865b3066246620054d46624a142a847c964c85534164bd992f3987d15336)) else (if c < 1445 then 0x7325262816c7da627270d4262646985ddaa01124044810b21e6255695e07f440a3509585 else (if c < 1446 then 0x98ac091d72470c2a8898a91b6d098a81b6a174641c3606db01b7006dac0d8e0362026290 else 0x98cc2632198c421a9198c0262f098b86104098b4209f71178c2c602035c28d498b05a576)))) else (if c < 1453 then (if c < 1450 then (if c < 1448 then 0x98dae635b50f0e21708bb1614b080d8205705ce41b6e05849d4f5050f8143d098d162eb5 else (if c < 1449 then 0x8435a3ab01198046510b21e6395827e07fc00aa2263846986493a50a35a637550fc26370 else 0xb20263d098f8a216098f422131886422150885014fc05cb4263c48bdd263b280ac263a1)) else (if c < 1451 then 0x5e9426440990ca642593812641484364497b206c264008410081990b21263f770d689657 else (if c < 1452 then 0x80ae847ba206c2648086a4082000b18a64746c7e494970b2026455991926450941417b80 else 0x9935dcc9924bd428a89932a64c0970c202ca95701648066d4264b99649264a5938166497))) else (if c < 1456 then (if c < 1454 then 0x994825ba05e1c162609944659269940a6430993de2f7712a402c879939a2eb62025028a7 else (if c < 1455 then 0x330e665c293d0265d09970265b9996a265939962665719958a65509951e6430994a66535 else 0x51040fe7013adc10d4997de65e75100df0f06dbc0cfc03f9a8cc401364806801158ccfb8)) else (if c < 1457 then 0x1bb0193019981cfe9713fc0865792842218051d00fe8113e9810d511b5947329884249e0 else (if c < 1458 then 0x9986848d0140c266079990a6632122c04ff099880feb2141e43c709984d93113fa9c5036 else 0x33a1c6c5099a4174800e4819634518926682999ca66623399266299994048f0141c26610))))) else (if c < 1471 then (if c < 1465 then (if c < 1462 then (if c < 1460 then 0x54d8266b0995c26144620c266a3921823e62995426129921023e435191d96567c041e657 else (if c < 1461 then 0x99d8267501b142674399cc2672099c42670099bda66e41ac8266d246ccc50bb0e4ee66c3 else 0x921523e575eb01463b6592d96415eb11463146ca51b273fbde679799e01cd6099dee6771)) else (if c < 1463 then 0x13a80ce6b33985553799fea6567984c267e099f4267c099ede67a0921423e59995a66134 else (if c < 1464 then 0x9a10a683a9a0aa683b9a0ae66e599b9268127c09de66270dc8ce7b3fc1cce717c00a6800 else 0x799e1c38833ae996655eb411b6746d1cff2733a5668a89a25e68859a1c268603fc4a685b))) else (if c < 1468 then (if c < 1466 then 0x9a41665a6985c268f89a38268d69a31e68b0922423e999961a61545ebc1467a65a29f036 else (if c < 1467 then 0x9a58e695b9a52e693b99c86682b99c026928921ca3e7951968ff37920c26919518ad5198 else 0x79a08ceca659d57ae4519951b7946d5cff5733a9669c79a6d269aa9a64269803fd0e6977)) else (if c < 1469 then 0x3fd9e65429a8019631567de69fa996ce61809a78269d7922823ea9922123e8751a29f040 else (if c < 1470 then 0xe48840249a9426a403fdca6a3a9a88a6a1b9a56e693a99cc2683a99c466599985819695 else 0x9ab5038a29ab126ab09aaa80ae89a98039390e4a040209aa426a8a9a9c000009a9903937)))) else (if c < 1477 then (if c < 1474 then (if c < 1472 then 0x9ac6574889ac1d74825ec117b009abc26ae89ab4038a89ab026ab49aa940ae29abd26ae2 else (if c < 1473 then 0x9a59267409a10267449ad8a6b589ada26b521aca26b421ac8a6b303fe026b279ac5e6b29 else 0x9950a6ba2132804ae7920c26b99995226ba8920d26b977c00a6b829adc26a209a5826a24)) else (if c < 1475 then 0x1b146685b1b1404a403fe9d469a65aa8ceda65a95469546e251b873fe5cced5135c84a1a else (if c < 1476 then 0x9adca6a409a6066a419a60267519a18267509af426bc09aec0ffb29a8ea69769a8ee6977 else 0x997026190922c23eb351a8596b17c141e69633b8596b051a811b9246e4cffc233b826bb0))) else (if c < 1480 then (if c < 1478 then 0x12b8049809b0026bf23ff8a67ab57bc26be03ff4a68ba9a2ed6110997066191922c63eb2 else (if c < 1479 then 0x9a05a67cb99d8161109b1026c309b0826bf09a74268c09a75268c499a8267b099a926c12 else 0x9a3aa68eb99f6e6c5033bc4cef09a94269919a49e68d89a94669909a49a68d999d866870)) else (if c < 1481 then 0x99fc266b09b1c04a101260a6c009a7aa68f69a7ae68f7620c667eb620c26c603ffca6b32 else (if c < 1482 then 0x74681001b9b289e6a01388a6c929b24e6c889b2251ba69af8269f09a40669f19a40266b1 else 0xe82e6cf079a8880900e80500379b38e61a09b3461510400826cc78fb1018f79b2cde6b0)))))) else (if c < 1507 then (if c < 1495 then (if c < 1489 then (if c < 1486 then (if c < 1484 then 0x9b48a6bca4011c49970f1ea6d16986904aa02195e6d048fb1e6d13986826d008fb248094 else (if c < 1485 then 0x9b6266d799b59e6d6921a4049a09af826c0a9b56a6d42123dc4aa09afc26bd29b4e90057 else 0x69402a406a0526db36dd8e6dc26a0426db60ca101a640ca001a609b6826d979b61e6d77)) else (if c < 1487 then 0x6a05e6e1518a0056b49b8026df49b7826da75ecd9d1c770e497b33746ca6dda6dd9a6dc8 else (if c < 1488 then 0x5ed8170876a0297b408c8c26e50883466e40069c02bf482b426e37817426e200d2102014 else 0x9bac205d59ba94863022b99b7609ba5083c01e5626e809b9c26e609b812324a883ae10a7))) else (if c < 1492 then (if c < 1490 then 0x9bbc26ee49ba025bc19375620f16ddc57b50585a25bb49bb6655d09bb2879a81229620d0 else (if c < 1491 then 0x96eea6f5a8c8c26f40141d03a03746ea6f3a141c03a069bc826f109bc026f149bc126ee0 else 0xbfdc4f949bd99eb224019c2fa0139026f209b049d1d796ed66f55069404ae08c8d26f44)) else (if c < 1493 then 0x9acc26f749bdc26f619be426f8a4025c4d721444262204021c4c73140826f70905110070 else (if c < 1494 then 0x9be0a6fb01445c4980403026fa0402c146b065b80cf0065b9146b446ec11bb440280cf04 else 0x7040270009bfc66fe29c0c270219c04270019bfc26fe39bf426fc12c0526fd19bf00b015)))) else (if c < 1501 then (if c < 1498 then (if c < 1496 then 0x5cdc1709359181617853e852701129411feb9c18270509c11270319c082701178181df20 else (if c < 1497 then 0x59185617924c81770b53e81270066f017ea45cdc57092667c59db166f057ea524c85770a else 0x93782211086c6632618bd06211186c6215b1854c610b282b820a22817c60285667c19db0)) else (if c < 1499 then 0x9b19a6c26941864de18c9822f40817c20284856c21530842ce5be09640255f0952425060 else (if c < 1500 then 0x6c70270a09c24670806978e70712439090d60a35270702439490d70a35a5be1964066d40 else 0x732d270d09c30670b06c705df301134844c40b18270a19c24270816978a70d19c30270b1))) else (if c < 1504 then (if c < 1502 then 0x697ddb7906c75da821697d8cf4136340cf312c050d8d133d00cf302c05671009c3c270e2 else (if c < 1503 then 0x9c4c671209c44671109b0da154085505d1f073311b7916c759c66071a41c65070401a820 else 0x8554215519c6c271a09c64671819c5c2716a9c64271809c5c6716b9c54271309c5027121)) else (if c < 1505 then 0x254a42a809c7c9c67033d44cf509c7c271e29c749c6449c70671d39c700cf2633c9e6c46 else (if c < 1506 then 0x9c92a2f309c8ee1b038dfc046201186c2c899c8820a179c862027424d1c28d09c829a5e7 else 0x6c70096020b18a72599c5e2727a9c9a215809c9427160854ae15708570215605ce014fb0))))) else (if c < 1519 then (if c < 1513 then (if c < 1510 then (if c < 1508 then 0x80a699bd0591c272c7963c272b5952104792206c272a486c267292809e894290b2127280 else (if c < 1509 then 0x963de73068bccc96f00a29e72f6732e096f10a2a272d29c64a72e29cb42718096fc25070 else 0x9ccaa71b29ccca73209c6984a409b54199e0667867311963d84aab0b18273078bcca7310)) else (if c < 1511 then 0x65c05970051b411bca46f2d00db70201c1f09cdc273607a60273519cd8673509cd067340 else (if c < 1512 then 0x9ce427380998c66231127826fab9b15a49f09056a1590998c26230927c6415b8564546d1 else 0x7c401c1f071a00cf71403accf701378806809cf0a73b2115ca73a29cece73a333da0cf69))) else (if c < 1516 then (if c < 1514 then 0x9990997114045c4ff01bb0177f19280215a051b81010013da410d011b2546c69be6d00fb else (if c < 1515 then 0x1298841000aa50240a404de73da9ce4a73e7123dc50b09ce1a6b329cf410122142ec3c70 else 0x9cfcc3cc712ac0d01034050d00024b4040b02011840250a38423da2010c402a0aa402405)) else (if c < 1517 then 0x9d121b7e19d155a7709d1243366043d43367043d274309d04e74239d02674199d00e73f9 else (if c < 1518 then 0x9d20a74789d0e19e1273361c6bb69d69a75b6784c10e00a999b7e09d151c6a29d181a771 else 0x829ee751b818da75000cd8c066869dc274f90d84c36f09d38274d89d30a74b29d28a7492)))) else (if c < 1525 then (if c < 1522 then (if c < 1520 then 0xef1c39e59d54275439d38a2f89858960a65677cda74501a402bc68868275308584e752a else (if c < 1521 then 0x678296195069c048e09581275a8942c275928869e7584818c275720ea103b796df9e7564 else 0xea103a0b9d7c275e29d76275e89d74a75b89d70a75b29d56659379431a21b681919b7f6)) else (if c < 1523 then 0x858cdc6c60695c4a1a942ea7622858427619942d676288585276170ea003a0171a827602 else (if c < 1524 then 0x989010167131cc50a0905e501570bfc033949d8c1eb324051c2fa013a4275f29b1ea1636 else 0x40689019251d4598c133f4598c051d411c224708d018233f42763b9bedd0177132805110))) else (if c < 1528 then (if c < 1526 then 0x9d941b2159da09c3b09d911a6379d9c676609d945b2149d915a63811a1028d411a1428d6 else (if c < 1527 then 0x9da8147729da42769151e414fd051e01c3c0363c0d8f1787804510114082a889d9c27661 else 0x9389276ea9388276c46c84276da70ee847d90b21276c06c85049900b18a76a09dac947a0)) else (if c < 1529 then 0x1a0045829dc4a771333fa0cfe99dbc2770a9dbc17b9070f697b945924047d70b20276e5 else (if c < 1530 then 0x1bb0198d19288147c04070007570435277379dc9d47b37c441d20033fc501bb33fc04e52 else 0x9cf9d01e7142c086579994d98e14075c5073)))))))))))
def hint5 (i : Nat) : Nat := (hint5C (i / 16) >>> ((i % 16) * 18)) &&& 262143
def hoff5C (c : Nat) : Nat := (if c < 78 then (if c < 39 then (if c < 19 then (if c < 9 then (if c < 4 then (if c < 2 then (if c < 1 then 0x1d3018a017c0164015c0141012100d900cb00b300ab0090006f002600180000 else 0x3620358034a03410335032e031502c802c002a50285023d022f0217020f01f4) else (if c < 3 then 0x4230417040a03ff03f403e903d703ce03c203b903ad03a40398038f037d0374 else 0x4ea04df04d404c904b704ac04a00495048a047f046d04620457044c043a042e)) else (if c < 6 then (if c < 5 then 0x58e058c057a0578056c0568054f054c053c053a05280526051a0516050004f5 else 0x5fd05fb05f505f305ed05db05d905d205cb05c205bb05b705b105a0059e059c) else (if c < 7 then 0x661065b0656065206450641063c0638062d06280623061c0614060d06070603 else (if c < 8 then 0x6fe06e706df06c606c406ad06a506a3068a0682067e06790673066d06690665 else 0x7c107bf07b307b007a807a807970750074e0736073407280726070e070c0700)))) else (if c < 14 then (if c < 11 then (if c < 10 then 0x81b0815080a080407fe07f907ee07e807e407de07da07d807d207cf07c907c7 else 0x899088d086508610854084f084b08450841083c08380832082e08290825081f) else (if c < 12 then 0x93c093a092b092909170914090008fe08ec08ea08da08d608be08bb08b5089b else (if c < 13 then 0x9bd09b809ac09a4099e09960990098a09760974096e096c0966095b09540940 else 0xa260a1a0a150a100a0a0a040a0009fb09f309ee09e909e409de09d809cc09c5))) else (if c < 16 then (if c < 15 then 0xb7a0b660b1c0b190b080ae80aa00a9c0a8e0a8a0a710a670a4f0a4b0a340a2a else 0xbea0be40bde0bd80bcf0bc70bc10bbb0bb50ba80ba00b9a0b960b8f0b8b0b7d) else (if c < 17 then 0xd0c0cfc0cf20cee0cdd0cda0cc80cc60cba0cae0c930c5f0c0f0c0b0c060bf0 else (if c < 18 then 0xdc30d770d690d640d5d0d570d500d480d430d3d0d380d2c0d230d1c0d150d12 else 0xfc30f7a0f6c0f540f4a0f2c0f050eb90eab0ea10e830e630e1b0e0d0e050de7))))) else (if c < 29 then (if c < 24 then (if c < 21 then (if c < 20 then 0x10fa10ee10e310d810cd10bb10b210a6109d1091108a106e1057100a10020fe4 else 0x11dd11c711bc11b011a7119b118f1184117b1169114c1141112f11241118110f) else (if c < 22 then 0x125d124c124a12441242124012321230121e121c121611f911f711f511e311e1 else (if c < 23 then 0x12a512a1129d129712951290128b12841280127c127812721270126c12671263 else 0x134d133f133d1327131f131d130712ff12fd12e412e112df12c912c712c512ad))) else (if c < 26 then (if c < 25 then 0x140f140a1406140013fc13fa13f413f413e113d1138a13881372136a13681350 else 0x14591453144d144914441440143e14381432142c142814261420141e14181413) else (if c < 27 then 0x14f514f314ef14d614d314cf14b914b614b414a214a01494146814631461145b else (if c < 28 then 0x15861571156b15661560155815521550154b15351533152515231511150f150b else 0x160115fe15fc15e615de15d815d615d015bb15b315af15aa15a415921590158c)))) else (if c < 34 then (if c < 31 then (if c < 30 then 0x16d016ce16bc16ba16b6169f169d1697169716871641163f16291627161b1619 else 0x176f1756174f1747174017291722171a1718170116fa16f416f216e616e416d2) else (if c < 32 then 0x1825180e180717ff17f817e117da17d217cd17b617af17a7179f1786177f1777 else (if c < 33 then 0x18eb18dc18d118c618be18ad18a31899188f1886187c185d185a184e1832182a else 0x19cb19c819c519b119a0195919511947193f19321929191f19161908190018f4))) else (if c < 36 then (if c < 35 then 0x1a431a3e1a281a211a1d1a171a0c1a081a0219fd19f719f019ea19e219db19cf else 0x1ad21acc1ac51abe1ab91ab31aa81aa01a8f1a8a1a821a6f1a6a1a631a5e1a58) else (if c < 37 then 0x1bc91bc41bb91bb31baf1ba81b961b8f1b891b761b711b6c1b611b561b3b1b1f else (if c < 38 then 0x1c321c2a1c241c1d1c161c121c061c001bfb1bf61bf01beb1be41bdf1bd21bcd else 0x1ca21c9a1c911c8d1c811c7c1c701c6a1c631c5c1c551c501c4a1c451c3e1c39)))))) else (if c < 58 then (if c < 48 then (if c < 43 then (if c < 41 then (if c < 40 then 0x1d0e1d0b1d081cf21cec1ce81ce21cdd1cd91cd41cce1cc11cbd1cb91cac1ca8 else 0x1d6b1d6a1d661d521d501d4a1d451d411d3c1d381d321d2e1d261d221d181d13) else (if c < 42 then 0x1e031df81df31dd31dcb1dc21dbf1db51db21da81da51d9b1d911d871d7b1d70 else 0x1ebe1e721e571e531e4e1e4a1e451e411e3c1e361e2c1e251e1d1e181e111e0b)) else (if c < 45 then (if c < 44 then 0x204d203520201ffc1fe21fce1fb51fa11f851f751f5b1f4b1f321f161efc1ee0 else 0x21cb21b921a4218d21772157213e212c2113210120e920d520c0209d208c2068) else (if c < 46 then 0x2310230c22f022e922d522c222aa22972282225e224b2236221d220b21f521e1 else (if c < 47 then 0x2376236e236a2366236523612350234923452344234023392335232d23292317 else 0x23f623f523e323da23ba23b923ad23a823a2239a2396239223882383237f237a)))) else (if c < 53 then (if c < 50 then (if c < 49 then 0x24b524b424a22499247624752460245f244f244d24362433241f241e24072406 else 0x251f251d25152511250724ff24fb24f724f324ee24ea24e524db24da24c624c5) else (if c < 51 then 0x25652562255825532548254425412540253c253925362531252d252a25272522 else (if c < 52 then 0x25b025a9259f259e259a25982592258d258925872583258025752571256d256b else 0x2611260d26092605260125f725f325e725e225dc25d425d325cb25ca25c125b9))) else (if c < 55 then (if c < 54 then 0x26672660265e26572656264e264c26442642263a2638262e262d261f261b2617 else 0x26ea26e926e326cb26c726c026bd26b5269d269b26982693267c267a2674266d) else (if c < 56 then 0x274d27472744273c27382733272f27252722271a271627102709270226ff26ef else (if c < 57 then 0x2823281f28182814280d280527ff27f027d627d227ce27b727a6275f27572750 else 0x28cb28c728bb28b328ac28a2289a28932880287b2875285c2845283d28382830))))) else (if c < 68 then (if c < 63 then (if c < 60 then (if c < 59 then 0x295c2951294c29482941292c29252911290c290628fc28f628e928e228d828d2 else 0x2a1b29d129cc29c129ba29b629b129ad29a72993298e29882977296c29652961) else (if c < 61 then 0x2aa72aa32a9d2a972a8a2a832a7d2a762a702a682a642a5d2a532a4c2a472a33 else (if c < 62 then 0x2b142b0e2b092b052aff2af82af42af02ae42ae02ad92ad22ac92ac42ab82ab3 else 0x2ba62ba12b9c2b972b922b8a2b862b802b702b502b4c2b492b332b2b2b252b18))) else (if c < 65 then (if c < 64 then 0x2c1a2c0c2c012bfe2bf32bf02be72be42bdb2bd02bc62bba2bb72bb52bb02bab else 0x2c922c8d2c872c822c7c2c762c702c6a2c5f2c592c502c4a2c472c2e2c282c1f) else (if c < 66 then 0x2d802d7b2d622d5b2d512d462d262d1f2d152d0b2ced2ce32ce12cca2cc02cb4 else (if c < 67 then 0x2e4b2e372e2b2e1f2e132e0f2e072dec2de22ddd2dc62dbf2db52dad2d912d8a else 0x2ef82eef2ee42edb2ecd2ec52ec22eaf2ea42e9c2e922e832e7a2e732e692e53)))) else (if c < 73 then (if c < 70 then (if c < 69 then 0x2f602f5d2f592f542f502f4d2f492f432f3b2f382f362f2b2f232f1a2f0d2f05 else 0x2fc22fbd2fb62fb22faf2fa22f9c2f982f912f8b2f872f7a2f732f6a2f682f66) else (if c < 71 then 0x3061305930503037302f3028300f30072fff2ff52fda2fd62fd32fcf2fca2fc5 else (if c < 72 then 0x3118310e310b310230e830e030db30c230bb30b330ac3093308c3084307f3068 else 0x31ca31be31b631ac31a43197318e3183317a316d31643158314f31403134312c))) else (if c < 75 then (if c < 74 then 0x3221321a3213320f320231f831f631f231ed31e931e331df31dc31d431cf31cc else 0x327b32773271326f326932643260325a32553252324c324832393233322d3226) else (if c < 76 then 0x32d132d032ca32c832c032bc32bb32ad32aa32a932a53291328d32863281327f else (if c < 77 then 0x33253320331a3312330b3308330632fa32ec32eb32e732e632df32dd32db32d9 else 0x33863381337b33763371336a3364335e335a334c3346333d33343332332e3329))))))) else (if c < 117 then (if c < 97 then (if c < 87 then (if c < 82 then (if c < 80 then (if c < 79 then 0x33e333df33d933d333cc33c533c133bb33b733b233b033ad339f33983393338c else 0x343934373433343134293428342234203418341334123404340333ff33e833e4) else (if c < 81 then 0x34f234ec34df34d934d134ca34c434c134bc34a53494344d34473440343c343b else 0x357a35683563355f35533549354135393532352b3524351f3507350034fc34f6)) else (if c < 84 then (if c < 83 then 0x35fb35f735f335ec35e435dc35d635ca35c335bf35b735a1359b358e35893581 else 0x367c36753671366b36653652364d36493643363a3633362c362536213615360e) else (if c < 85 then 0x36f736f336ef36e336de36da36d436c836bf36bb36af36a93698368d36893682 else (if c < 86 then 0x37c537b737ad37a637a337a0378a3782377c377837753765374e3707370236fe else 0x3829381f38193813380b3805380037f937f237ee37e137da37d737d537cf37ca)))) else (if c < 92 then (if c < 89 then (if c < 88 then 0x388a3889387b38763872386d386938643862385c38573854385138373832382d else 0x38da38d338d038ce38c038b638b438b338ac38aa38a638a4389c389b38953893) else (if c < 90 then 0x395c3958394f39493944393e39353930392b39173912390e38fc38f738f138e2 else (if c < 91 then 0x39db39d539d039ce39c439c339b439b339b239a2399839903974397039673961 else 0x3a353a2f3a2a3a253a203a183a0d3a083a0339fd39fa39f639f139ea39e739e2))) else (if c < 94 then (if c < 93 then 0x3ac93ac33abe3aba3aa93aa43a9f3a8c3a8a3a7e3a763a523a4e3a453a3d3a39 else 0x3b583b503b4b3b323b313b303b203b163b0e3af23aee3ae83ae23adc3ad83acf) else (if c < 95 then 0x3bb53bb23ba53ba13b9e3b9a3b953b8e3b8b3b863b7f3b7e3b763b6f3b683b67 else (if c < 96 then 0x3c263c1b3c1a3c193c0f3c093c033be23bde3bd83bd33bce3bcb3bc53bc13bba else 0x3c873c843c7d3c773c733c6f3c683c643c5f3c513c4e3c473c413c3b3c323c2a))))) else (if c < 107 then (if c < 102 then (if c < 99 then (if c < 98 then 0x3d693d4d3d423d3a3d1d3d143d093d023cea3cdf3cd83cc13cb53cb03c8f3c8b else 0x3e403e343e283e1a3e133e0b3df73df03dd33dcb3dc63daa3da03d9d3d803d71) else (if c < 100 then 0x3ec13ec03eb63eb43eb13e973e943e8a3e863e823e7f3e733e693e603e553e4b else (if c < 101 then 0x3f203f1c3f0a3f063f013efd3ef93eed3eec3ee93ee33edf3ed83ed43ec93ec2 else 0x3fd53fc43fbc3fb83f9d3f9a3f993f883f7c3f743f573f523f4b3f443f2d3f27))) else (if c < 104 then (if c < 103 then 0x406c40694051404b403b401a4016400f400c40043ffb3ff63ff13fea3fe13fd8 else 0x40e440e140da40d440ce40c940c240bb40b140ac40a040994082407f407c4070) else (if c < 105 then 0x42e8429c428b4281425d423c41f341e241d841b4419241484137412c410840e9 else (if c < 106 then 0x445b444d443f443044234416440943fc43e843dc43b843984350433f4333430f else 0x454945414528451d451544fb44f044e144cc44bf44b144a444974489447c446f)))) else (if c < 112 then (if c < 109 then (if c < 108 then 0x4610460545f845ee45df45d445c345b845b745a6459b4596457f4574456d4554 else 0x4692468f468446824681466e466d466c465646554654463f463d463c4629461d) else (if c < 110 then 0x46d746d446c946c546c246bf46bb46b846b446b146a746a446a1469d46994696 else (if c < 111 then 0x474f4738472c472547044700470046fb46fb46f746f546f046ec46e846e346dd else 0x48204819480147f847ed47e847d047c747bc47b5479e47954789478447634758))) else (if c < 114 then (if c < 113 then 0x48fe48f548e648df48da48be48b448b148954886487e4862485748514834482b else 0x499c499849954990498a498049754969495d49534947493949314924491d4906) else (if c < 115 then 0x49f749f149ec49e749e649e549db49d849d549bb49b849b249ac49a849a549a2 else (if c < 116 then 0x4a504a4c4a474a414a394a344a304a1e4a1a4a174a114a0d4a0a4a0649ff49fa else 0x4ac54ac04abd4ab84ab54aaf4aaa4aa84a9e4a9d4a9c4a8c4a824a7a4a5e4a59)))))) else (if c < 137 then (if c < 127 then (if c < 122 then (if c < 119 then (if c < 118 then 0x4b394b354b314b2d4b294b244b204b1c4b084b054af74af34ad94ad44ad14aca else 0x4bae4baa4ba54ba34b9b4b954b924b7a4b794b784b654b614b5e4b4c4b484b3f) else (if c < 120 then 0x4c004bfd4bef4beb4be74be34bdc4bd94bd14bce4bcb4bc64bc14bbf4bba4bb6 else (if c < 121 then 0x4c624c614c5c4c584c514c4c4c454c404c3b4c364c314c2e4c2b4c1c4c1a4c17 else 0x4ccb4cc84cbf4cbb4cb74cb34cae4ca94ca54ca14c8d4c884c854c7e4c794c74))) else (if c < 124 then (if c < 123 then 0x4d3c4d394d344d2d4d294d244d224d1a4d144d104cf74cf64cf54ce44ce04cdd else 0x4dc74da94da54d9f4d9b4d944d8c4d844d774d5b4d564d514d4d4d4a4d494d42) else (if c < 125 then 0x4e234e204e194e144e0f4e0a4e014dfd4df54dee4de84de34de04dde4dd24dcd else (if c < 126 then 0x4ee94edf4ed84ec04eb54eb14e954e8b4e824e6b4e604e5c4e414e3d4e384e33 else 0x4fd24fb54fac4fab4f944f854f7d4f614f574f504f394f2f4f2a4f124f084f01)))) else (if c < 132 then (if c < 129 then (if c < 128 then 0x50655062505d505c50515047503a502f5025501a500c50014ff54fec4fdd4fd7 else 0x50bf50bb50b250af50a750a2509d50985096509450935092507e507a5073506c) else (if c < 130 then 0x5167515b5156513d5131512b5126510e510250fd50e750d250d150ce50c950c3 else (if c < 131 then 0x52c452bd52b852a152955291527b525a5211520b520751f151d151895183517e else 0x534b5334532e53285320531b5314530d530652f852f152ea52e052d952d252cb))) else (if c < 134 then (if c < 133 then 0x53c753be53b953b253ad53a1539d5393538d538c537f537b5376536e53555350 else 0x54a254a0548d548954875474547354705464544053f753f453f053d753d353cb) else (if c < 135 then 0x550b550054fc54f654f254ed54e854e154dd54d854d554d354c054bd54bb54a6 else (if c < 136 then 0x556c55665565555f555a55575553554d554955435541553a552355195514550f else 0x55d055be55bb55b255ae55a955a3559f559b55975584557f557b55755574556f))))) else (if c < 147 then (if c < 142 then (if c < 139 then (if c < 138 then 0x562856245621561e561856165611561056095605560255eb55ea55e955d755d3 else 0x567c567756755673566556645663564e564b56455642563e563a56345633562b) else (if c < 140 then 0x56cf56cb56c556c156bb56b356ae56aa569956965692568f568956845683567f else (if c < 141 then 0x574e57485743573f573c573757345733572b5726570f570e570d56fd56f356eb else 0x579e579857945791578d578a578657835782578157755772576f575757545751))) else (if c < 144 then (if c < 143 then 0x5810580c580857f057ef57ee57de57db57d957c857c357c057bc57b757b357af else 0x586e586d58595855584e5848583958385831582e582958265820581b58185817) else (if c < 145 then 0x58e058d658d258b058ae58aa58a4589e589a5896589358915885588358805870 else (if c < 146 then 0x59b5599f5995599259795974597159555950594b592e59245921590d58fc58f9 else 0x5a235a205a1f5a115a0d5a075a0359fb59f359f059e859e359d659d259bc59b8)))) else (if c < 152 then (if c < 149 then (if c < 148 then 0x5ab25a9f5a9d5a9a5a835a825a7d5a5c5a5b5a585a3f5a3c5a365a345a2c5a29 else 0x5b185b145b0e5b0a5b025af95aef5aec5ae25ae05adf5acc5acb5aca5ab55ab3) else (if c < 150 then 0x5bd35bcc5bb45ba95ba15b845b795b6d5b505b445b405b255b215b215b1d5b18 else (if c < 151 then 0x5c975c965c8b5c825c7c5c695c5e5c5a5c545c365c2c5c2b5c145c055bfc5bde else 0x5cec5ce95ce85cd45ccc5cca5cc95cc45cc35cc15cbf5cbe5cbd5cab5ca75ca1))) else (if c < 154 then (if c < 153 then 0x5d605d5c5d5a5d595d4b5d475d435d3e5d395d385d265d1e5d1d5d075d045d03 else 0x5e805e605e5d5e5a5e475e445e425e2d5e295e255e0e5e0d5e015dec5db35d60) else (if c < 155 then 0x5efe5efc5efb5ee65ede5edd5ec75ebf5ebd5eac5ea65ea45ea05e9a5e925e90 else (if c < 156 then 0x5f875f735f715f6c5f505f4f5f4e5f445f405f3c5f385f335f325f1e5f165f15 else 0x5fa45f9e5f965f8a5f88))))))))
def hoff5 (i : Nat) : Nat := (hoff5C (i / 16) >>> ((i % 16) * 16)) &&& 65535

def cnt : Nat → Nat
  | 0 => 2
  | 1 => 78
  | 2 => 2501
  | _ => 10100

def recOf : Nat → Nat → Nat
  | 0, idx => rec6 idx
  | 1, idx => rec5 idx
  | _, idx => rec4 idx

def nodeLen : Nat → Nat → Nat
  | 0, idx => if idx == 1 then 10 else 9
  | d + 1, idx =>
    let v := recOf d idx
    nodeLen d (v >>> 15) + 1 - (if ((v >>> 5) &&& 1) == 1 then 0 else 1) - (if ((v >>> 4) &&& 1) == 1 then 0 else 1)

def nodeAt : Nat → Nat → Nat → List Word
  | 0, a, idx => startRot (idx == 1) a
  | d + 1, a, idx =>
    let v := recOf d idx
    childFrom (nodeAt d (compAuto a (v &&& 15)) (v >>> 15))
      ((v >>> 11) &&& 15) ((v >>> 7) &&& 15)
      (((v >>> 6) &&& 1) == 1) (((v >>> 5) &&& 1) == 1) (((v >>> 4) &&& 1) == 1)

def recOkD (d : Nat) : Bool :=
  (List.range (cnt (d + 1))).all fun idx =>
    let v := recOf d idx
    let p := v >>> 15
    let i := (v >>> 11) &&& 15
    let j := (v >>> 7) &&& 15
    let ra := v &&& 15
    let plen := nodeLen d p
    decide (p < cnt d) && decide (i < j) && decide (j < plen) && decide (ra < 12)

set_option maxHeartbeats 0 in
theorem rec0_ok : recOkD 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem rec1_ok : recOkD 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem rec2_ok : recOkD 2 = true := by decide +kernel

theorem rec_props {d idx : Nat} (hd : d < 3) (hidx : idx < cnt (d + 1)) :
    let v := recOf d idx
    (v >>> 15) < cnt d ∧ ((v >>> 11) &&& 15) < ((v >>> 7) &&& 15) ∧
    ((v >>> 7) &&& 15) < nodeLen d (v >>> 15) ∧ (v &&& 15) < 12 := by
  have hok : recOkD d = true := by
    interval_cases d
    · exact rec0_ok
    · exact rec1_ok
    · exact rec2_ok
  have hh := List.all_eq_true.mp hok idx (List.mem_range.mpr hidx)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  exact ⟨hh.1.1.1, hh.1.1.2, hh.1.2, hh.2⟩

theorem nodeAt_length (d : Nat) (hd : d ≤ 3) :
    ∀ a idx, a < 12 → idx < cnt d → (nodeAt d a idx).length = nodeLen d idx := by
  induction d with
  | zero =>
    intro a idx ha hidx
    simp only [nodeAt, nodeLen]
    have h0 : (startRot (idx == 1) a).length = (if idx == 1 then 10 else 9) := by
      have hm := map_rotW_starting (idx == 1) ha
      rw [← hm, List.length_map]
      cases h1 : (idx == 1) <;> decide
    exact h0
  | succ d ih =>
    intro a idx ha hidx
    obtain ⟨hp, hij, hjp, hra⟩ := rec_props (by omega) hidx
    simp only [nodeAt, nodeLen, childFrom, List.length_cons]
    have hplen := ih (by omega) (compAuto a (recOf d idx &&& 15)) (recOf d idx >>> 15) (compAuto_lt ha hra) hp
    have hj' : ((recOf d idx >>> 7) &&& 15) < (nodeAt d (compAuto a (recOf d idx &&& 15)) (recOf d idx >>> 15)).length := by
      omega
    have h2 : 2 ≤ nodeLen d (recOf d idx >>> 15) := by omega
    rw [keepGo_length _ hij hj', hplen]
    cases (((recOf d idx >>> 5) &&& 1) == 1) <;> cases (((recOf d idx >>> 4) &&& 1) == 1) <;> simp <;> omega

theorem map_rotW_nodeAt (d : Nat) (hd : d ≤ 3) :
    ∀ a b idx, a < 12 → b < 12 → idx < cnt d →
      (nodeAt d b idx).map (rotW a) = nodeAt d (compAuto a b) idx := by
  induction d with
  | zero =>
    intro a b idx ha hb _
    simp only [nodeAt]
    rw [← map_rotW_starting (idx == 1) hb, ← map_rotW_starting (idx == 1) (compAuto_lt ha hb), List.map_map]
    apply List.map_congr_left
    intro w _
    exact rotW_comp ha hb w
  | succ d ih =>
    intro a b idx ha hb hidx
    obtain ⟨hp, hij, hjp, hra⟩ := rec_props (by omega) hidx
    simp only [nodeAt]
    have hplen := nodeAt_length d (by omega) (compAuto b (recOf d idx &&& 15)) (recOf d idx >>> 15) (compAuto_lt hb hra) hp
    have hi' : ((recOf d idx >>> 11) &&& 15) < (nodeAt d (compAuto b (recOf d idx &&& 15)) (recOf d idx >>> 15)).length := by omega
    have hj' : ((recOf d idx >>> 7) &&& 15) < (nodeAt d (compAuto b (recOf d idx &&& 15)) (recOf d idx >>> 15)).length := by omega
    rw [map_rotW_childFrom _ _ _ hi' hj', ih (by omega) a (compAuto b (recOf d idx &&& 15)) (recOf d idx >>> 15) ha (compAuto_lt hb hra) hp,
      ← compAuto_assoc ha hb hra]

def unionN : List Word → Nat
  | [] => 0
  | w :: ws => deltaN w ||| unionN ws

theorem unionN_testBit_ge (ws : List Word) {m : Nat} (hm : 258 ≤ m) :
    (unionN ws).testBit m = false := by
  induction ws with
  | nil => simp [unionN]
  | cons w ws ih => simp [unionN, Nat.testBit_or, deltaN_testBit_ge w hm, ih]

theorem unionN_testBit_of_mem {ws : List Word} {w : Word} (hw : w ∈ ws) {m : Nat}
    (hb : (deltaN w).testBit m = true) : (unionN ws).testBit m = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    simp only [unionN, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | hx
    · exact Or.inl hb
    · exact Or.inr (ih hx)

theorem unionN_append (xs ys : List Word) : unionN (xs ++ ys) = unionN xs ||| unionN ys := by
  induction xs with
  | nil => simp [unionN]
  | cons x xs ih => simp [unionN, ih, Nat.lor_assoc]

def addSuff : List Word → List (Word × Nat × Nat)
  | [] => []
  | w :: ws =>
    let d := deltaN w
    match addSuff ws with
    | [] => [(w, d, 0)]
    | (w2, d2, s2) :: rest => (w, d, d2 ||| s2) :: (w2, d2, s2) :: rest

theorem addSuff_head_or : ∀ (ws : List Word),
    match addSuff ws with
    | [] => unionN ws = 0
    | (_, d, s) :: _ => d ||| s = unionN ws := by
  intro ws
  induction ws with
  | nil => simp [addSuff, unionN]
  | cons w ws ih =>
    simp only [addSuff, unionN]
    cases hs : addSuff ws with
    | nil => rw [hs] at ih; simp [ih]
    | cons p rest =>
      rcases p with ⟨w2, d2, s2⟩
      rw [hs] at ih
      simp only [ih]

theorem addSuff_length (ws : List Word) : (addSuff ws).length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [addSuff, List.length_cons]
    cases hs : addSuff ws with
    | nil => rw [hs] at ih; simp at ih; simp [ih]
    | cons p rest =>
      rcases p with ⟨w2, d2, s2⟩
      rw [hs] at ih
      simpa using ih

theorem addSuff_getElem (ws : List Word) :
    ∀ u (hu : u < ws.length) (hu' : u < (addSuff ws).length),
      (addSuff ws)[u]'hu' = (ws[u]'hu, deltaN (ws[u]'hu), unionN (ws.drop (u + 1))) := by
  induction ws with
  | nil => intro u hu _; simp at hu
  | cons w ws ih =>
    intro u hu hu'
    have hho := addSuff_head_or ws
    have hlen := addSuff_length ws
    match hs : addSuff ws with
    | [] =>
      rw [hs] at hho hlen
      have hws0 : ws.length = 0 := by simpa using hlen.symm
      cases u with
      | zero =>
        simp only [addSuff, hs, List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, hho]
      | succ u => simp at hu; omega
    | (w2, d2, s2) :: rest =>
      rw [hs] at hho hlen
      cases u with
      | zero =>
        simp only [addSuff, hs, List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, hho]
      | succ u =>
        have hu1 : u < ws.length := by simpa using hu
        have hu1' : u < (addSuff ws).length := by rw [addSuff_length]; exact hu1
        have hih := ih u hu1 hu1'
        simp only [addSuff, hs, List.getElem_cons_succ, List.drop_succ_cons]
        simpa [hs] using hih

def chkCase (ws : List Word) (i j maxLen N : Nat) (childAt : Nat → Nat → List Word)
    (getHint : Nat → Nat) (w : Word) (ka kb : Bool) (clen cov pos : Nat) : Option Nat :=
  if clen > maxLen || cov != allN then some pos
  else
    let h := getHint pos
    let a := h &&& 15
    let cid := h >>> 4
    if a < 12 && cid < N && sameWordSet (childFromW ws i j ka kb w) (childAt a cid) then some (pos + 1)
    else none

def goOp (ws : List Word) (i j n maxLen N : Nat) (childAt : Nat → Nat → List Word)
    (getHint : Nat → Nat) (wa wb : Word) (da db cr : Nat) (op : Bool) (pos : Nat) : Option Nat :=
  let w := mix op wa wb
  if ws.contains w then some pos
  else
    let dw := deltaN w
    match chkCase ws i j maxLen N childAt getHint w false false (n - 1) (cr ||| dw) pos with
    | none => none
    | some p1 => match chkCase ws i j maxLen N childAt getHint w false true n ((cr ||| db) ||| dw) p1 with
      | none => none
      | some p2 => match chkCase ws i j maxLen N childAt getHint w true false n ((cr ||| da) ||| dw) p2 with
        | none => none
        | some p3 => chkCase ws i j maxLen N childAt getHint w true true (n + 1) (((cr ||| da) ||| db) ||| dw) p3

def goJ (ws : List Word) (i n maxLen N : Nat) (childAt : Nat → Nat → List Word)
    (getHint : Nat → Nat) (wa : Word) (da : Nat) (j prefJ pos : Nat) :
    List (Word × Nat × Nat) → Option Nat
  | [] => some pos
  | (wb, db, suffJ) :: bs =>
    let cr := prefJ ||| suffJ
    match goOp ws i j n maxLen N childAt getHint wa wb da db cr false pos with
    | none => none
    | some p1 => match goOp ws i j n maxLen N childAt getHint wa wb da db cr true p1 with
      | none => none
      | some p2 => goJ ws i n maxLen N childAt getHint wa da (j + 1) (prefJ ||| db) p2 bs

def goI (ws : List Word) (n maxLen N : Nat) (childAt : Nat → Nat → List Word)
    (getHint : Nat → Nat) (i prefI pos : Nat) :
    List (Word × Nat × Nat) → Option Nat
  | [] => some pos
  | (wa, da, _) :: rest =>
    match goJ ws i n maxLen N childAt getHint wa da (i + 1) prefI pos rest with
    | none => none
    | some p1 => goI ws n maxLen N childAt getHint (i + 1) (prefI ||| da) p1 rest

def checkStepF (ws : List Word) (maxLen N : Nat) (childAt : Nat → Nat → List Word)
    (getHint : Nat → Nat) (pos0 : Nat) : Bool :=
  (goI ws ws.length maxLen N childAt getHint 0 0 pos0 (addSuff ws)).isSome

theorem goI_hit_real {ws : List Word} {n maxLen N : Nat} {childAt : Nat → Nat → List Word}
    {getHint : Nat → Nat} :
    ∀ (l1 : List (Word × Nat × Nat)) (wa : Word) (da sa : Nat) (rest : List (Word × Nat × Nat))
      (i0 pref0 pos0 posEnd : Nat),
      (∀ p ∈ l1, p.2.1 = deltaN p.1) →
      goI ws n maxLen N childAt getHint i0 pref0 pos0 (l1 ++ (wa, da, sa) :: rest) = some posEnd →
      ∃ pos1 pos2,
        goJ ws (i0 + l1.length) n maxLen N childAt getHint wa da (i0 + l1.length + 1)
          (pref0 ||| unionN (l1.map Prod.fst)) pos1 rest = some pos2 := by
  intro l1
  induction l1 with
  | nil =>
    intro wa da sa rest i0 pref0 pos0 posEnd _ h
    simp only [List.nil_append, goI] at h
    cases hj : goJ ws i0 n maxLen N childAt getHint wa da (i0 + 1) pref0 pos0 rest with
    | none => rw [hj] at h; cases h
    | some p1 => exact ⟨pos0, p1, by simpa [unionN] using hj⟩
  | cons p xs ih =>
    intro wa da sa rest i0 pref0 pos0 posEnd hds h
    rcases p with ⟨wx, dx, sx⟩
    have hdx : dx = deltaN wx := hds (wx, dx, sx) List.mem_cons_self
    simp only [List.cons_append, goI] at h
    cases hj : goJ ws i0 n maxLen N childAt getHint wx dx (i0 + 1) pref0 pos0 (xs ++ (wa, da, sa) :: rest) with
    | none => rw [hj] at h; cases h
    | some p1 =>
      rw [hj] at h; dsimp only at h
      obtain ⟨pos1, pos2, hres⟩ := ih wa da sa rest (i0 + 1) (pref0 ||| dx) p1 posEnd
        (fun q hq => hds q (List.mem_cons_of_mem _ hq)) h
      have hlen : i0 + 1 + xs.length = i0 + (xs.length + 1) := by omega
      have hor : (pref0 ||| dx) ||| unionN (xs.map Prod.fst) = pref0 ||| unionN ((wx, dx, sx).1 :: xs.map Prod.fst) := by
        simp only [unionN, hdx, Nat.lor_assoc]
      rw [hlen, hor] at hres
      exact ⟨pos1, pos2, hres⟩

theorem goJ_hit {ws : List Word} {i n maxLen N : Nat} {childAt : Nat → Nat → List Word}
    {getHint : Nat → Nat} {wa : Word} {da : Nat} :
    ∀ (l2 : List (Word × Nat × Nat)) (wb : Word) (db sb : Nat) (l3 : List (Word × Nat × Nat))
      (j0 pref0 pos0 posEnd : Nat),
      (∀ p ∈ l2, p.2.1 = deltaN p.1) →
      goJ ws i n maxLen N childAt getHint wa da j0 pref0 pos0 (l2 ++ (wb, db, sb) :: l3) = some posEnd →
      ∀ op : Bool, ∃ pos1 pos2,
        goOp ws i (j0 + l2.length) n maxLen N childAt getHint wa wb da db
          ((pref0 ||| unionN (l2.map Prod.fst)) ||| sb) op pos1 = some pos2 := by
  intro l2
  induction l2 with
  | nil =>
    intro wb db sb l3 j0 pref0 pos0 posEnd _ h op
    simp only [List.nil_append, goJ] at h
    cases hf : goOp ws i j0 n maxLen N childAt getHint wa wb da db (pref0 ||| sb) false pos0 with
    | none => rw [hf] at h; cases h
    | some p1 =>
      rw [hf] at h; dsimp only at h
      cases ht : goOp ws i j0 n maxLen N childAt getHint wa wb da db (pref0 ||| sb) true p1 with
      | none => rw [ht] at h; cases h
      | some p2 =>
        cases op
        · exact ⟨pos0, p1, by simpa [unionN] using hf⟩
        · exact ⟨p1, p2, by simpa [unionN] using ht⟩
  | cons p xs ih =>
    intro wb db sb l3 j0 pref0 pos0 posEnd hds h op
    rcases p with ⟨wx, dx, sx⟩
    have hdx : dx = deltaN wx := hds (wx, dx, sx) List.mem_cons_self
    simp only [List.cons_append, goJ] at h
    cases hf : goOp ws i j0 n maxLen N childAt getHint wa wx da dx (pref0 ||| sx) false pos0 with
    | none => rw [hf] at h; cases h
    | some p1 =>
      rw [hf] at h; dsimp only at h
      cases ht : goOp ws i j0 n maxLen N childAt getHint wa wx da dx (pref0 ||| sx) true p1 with
      | none => rw [ht] at h; cases h
      | some p2 =>
        rw [ht] at h; dsimp only at h
        obtain ⟨pos1, pos2, hres⟩ := ih wb db sb l3 (j0 + 1) (pref0 ||| dx) p2 posEnd
          (fun q hq => hds q (List.mem_cons_of_mem _ hq)) h op
        have hlen : j0 + 1 + xs.length = j0 + (xs.length + 1) := by omega
        have hor : (pref0 ||| dx) ||| unionN (xs.map Prod.fst) = pref0 ||| unionN ((wx, dx, sx).1 :: xs.map Prod.fst) := by
          simp only [unionN, hdx, Nat.lor_assoc]
        rw [hlen, hor] at hres
        exact ⟨pos1, pos2, hres⟩

theorem cov_allN_of_covers {ws : List Word} {i j : Nat} (hij : i < j) (hj : j < ws.length)
    (w : Word) (ka kb : Bool)
    (hc : Covers (w :: keepGo 0 i j ka kb ws).toFinset) :
    let cr := (unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))
    let da := deltaN (ws[i]'(by omega))
    let db := deltaN (ws[j]'hj)
    let dw := deltaN w
    (match ka, kb with
     | false, false => cr ||| dw
     | false, true  => (cr ||| db) ||| dw
     | true, false  => (cr ||| da) ||| dw
     | true, true   => ((cr ||| da) ||| db) ||| dw) = allN := by
  have hge (x y : Nat) (hx : ∀ m, 258 ≤ m → x.testBit m = false) (hy : ∀ m, 258 ≤ m → y.testBit m = false) :
      ∀ m, 258 ≤ m → (x ||| y).testBit m = false := by
    intro m hm; simp [Nat.testBit_or, hx m hm, hy m hm]
  have hcr_ge : ∀ m, 258 ≤ m → ((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))).testBit m = false :=
    hge _ _ (hge _ _ (fun m hm => unionN_testBit_ge _ hm) (fun m hm => unionN_testBit_ge _ hm)) (fun m hm => unionN_testBit_ge _ hm)
  have hmem_cr : ∀ u (hu : u < ws.length), u ≠ i → u ≠ j →
      ∀ m, (deltaN (ws[u]'hu)).testBit m = true →
      ((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))).testBit m = true := by
    intro u hu hui huj m hb
    simp only [Nat.testBit_or, Bool.or_eq_true]
    by_cases h1 : u < i
    · left; left
      have hm : ws[u]'hu ∈ ws.take i := by
        have hlt : u < (ws.take i).length := by simp; omega
        have heq : (ws.take i)[u]'hlt = ws[u]'hu := List.getElem_take
        rw [← heq]; exact List.getElem_mem hlt
      exact unionN_testBit_of_mem hm hb
    · by_cases h2 : u < j
      · left; right
        have hm : ws[u]'hu ∈ (ws.drop (i + 1)).take (j - i - 1) := by
          have hlt : u - (i + 1) < ((ws.drop (i + 1)).take (j - i - 1)).length := by simp; omega
          have heq : ((ws.drop (i + 1)).take (j - i - 1))[u - (i + 1)]'hlt = ws[u]'hu := by
            rw [List.getElem_take, List.getElem_drop]
            congr 1; omega
          rw [← heq]; exact List.getElem_mem hlt
        exact unionN_testBit_of_mem hm hb
      · right
        have hm : ws[u]'hu ∈ ws.drop (j + 1) := by
          have hlt : u - (j + 1) < (ws.drop (j + 1)).length := by simp; omega
          have heq : (ws.drop (j + 1))[u - (j + 1)]'hlt = ws[u]'hu := by
            rw [List.getElem_drop]; congr 1; omega
          rw [← heq]; exact List.getElem_mem hlt
        exact unionN_testBit_of_mem hm hb
  cases ka <;> cases kb <;> apply Nat.eq_of_testBit_eq <;> intro m <;> rw [allN_testBit] <;>
    (by_cases hm : m < 258
     · simp only [hm, decide_true]
       obtain ⟨v, hv, hd⟩ := hc ⟨m, hm⟩
       have hdv : (deltaN v).testBit m = true := by rw [deltaN_testBit_lt v hm]; exact bne_iff_ne.mpr hd
       simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, keepGo_mem, Nat.zero_add] at hv
       rcases hv with rfl | ⟨u, hu, rfl, hkeep⟩
       · simp [Nat.testBit_or, hdv]
       · by_cases hui : u = i
         · subst hui; simp at hkeep <;> simp [Nat.testBit_or, hdv]
         · by_cases huj : u = j
           · subst huj; simp at hkeep <;> simp [Nat.testBit_or, hdv]
           · simp [Nat.testBit_or, hmem_cr u hu hui huj m hdv]
     · simp only [hm, decide_false]
       have hgeM : 258 ≤ m := by omega
       simp [Nat.testBit_or, hcr_ge m hgeM, deltaN_testBit_ge _ hgeM])

theorem checkStepF_sound {ws : List Word} (nd : ws.Nodup) {k d : Nat} (hd : d < 3)
    {getHint : Nat → Nat} {pos0 : Nat}
    (hchk : checkStepF ws (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint pos0 = true)
    (hchild : ∀ cid < cnt (d + 1), ¬ Can k (nodeAt (d + 1) 0 cid).toFinset)
    (hlen7 : 7 ≤ ws.length) :
    ¬ Can (k + 1) ws.toFinset := by
  have hno : ∀ m ≤ k + 1, ¬ Can m ws.toFinset := by
    intro m
    induction m with
    | zero =>
      intro _ h0
      have hc := h0.2
      rw [List.toFinset_card_of_nodup nd] at hc
      omega
    | succ m ih =>
      intro hm h
      rcases h with h' | ⟨_, a, ha, b, hb, op, t, hab, _, _, hfr, ht, hs, hc⟩
      · exact ih (by omega) h'
      have hcK : Can k (insert (mix op a b) t) := can_mono (by omega) hc
      have ham : a ∈ ws := List.mem_toFinset.mp ha
      have hbm : b ∈ ws := List.mem_toFinset.mp hb
      obtain ⟨ia, hia, rfl⟩ := List.getElem_of_mem ham
      obtain ⟨ib, hib, rfl⟩ := List.getElem_of_mem hbm
      have hiab : ia ≠ ib := fun e => hab (by subst e; rfl)
      have stepIJ (i j : Nat) (hi : i < ws.length) (hj : j < ws.length) (hij : i < j)
          (hfr' : mix op ws[i] ws[j] ∉ ws.toFinset)
          (hs' : ws.toFinset ⊆ insert ws[i] (insert ws[j] t))
          (hc' : Can k (insert (mix op ws[i] ws[j]) t)) : False := by
        let w := mix op ws[i] ws[j]
        let ka := decide (ws[i] ∈ t)
        let kb := decide (ws[j] ∈ t)
        let ch := childFromW ws i j ka kb w
        have hch_set : ch.toFinset = insert w t := by
          simp only [ch, childFromW, List.toFinset_cons, keepGo_toFinset nd hi hj]
          congr 1
          ext x
          simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
          constructor
          · rintro ⟨hxw, hxa, hxb⟩
            have hu := hs' (List.mem_toFinset.mpr hxw)
            simp only [Finset.mem_insert] at hu
            rcases hu with rfl | rfl | hxt
            · rcases hxa with h1 | h1
              · exact of_decide_eq_true h1
              · exact (h1 rfl).elim
            · rcases hxb with h1 | h1
              · exact of_decide_eq_true h1
              · exact (h1 rfl).elim
            · exact hxt
          · intro hxt
            refine ⟨List.mem_toFinset.mp (ht hxt), ?_, ?_⟩
            · by_cases h1 : x = ws[i]
              · subst x; left; exact decide_eq_true hxt
              · right; exact h1
            · by_cases h1 : x = ws[j]
              · subst x; left; exact decide_eq_true hxt
              · right; exact h1
        have hch_nd : ch.Nodup := by
          refine List.nodup_cons.mpr ⟨?_, nd.sublist (keepGo_sublist 0 i j ka kb ws)⟩
          intro hm
          exact hfr' (List.mem_toFinset.mpr ((keepGo_sublist 0 i j ka kb ws).subset hm))
        have hcan_ch : Can k ch.toFinset := by rwa [hch_set]
        have hch_len : ch.length ≤ 6 + k := by
          have hsz := can_size hcan_ch
          rw [List.toFinset_card_of_nodup hch_nd] at hsz; exact hsz
        have hlen_ch : ch.length = ws.length + 1 - (if ka then 0 else 1) - (if kb then 0 else 1) := by
          simp only [ch, childFromW, List.length_cons, keepGo_length ws hij hj ka kb]
          have h2 : 2 ≤ ws.length := by omega
          cases ka <;> cases kb <;> simp <;> omega
        have hsome : ∃ posEnd, goI ws ws.length (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint 0 0 pos0 (addSuff ws) = some posEnd :=
          Option.isSome_iff_exists.mp hchk
        obtain ⟨posEnd, hgoI⟩ := hsome
        have hlen_as := addSuff_length ws
        let l1 := (addSuff ws).take i
        let l2 := ((addSuff ws).drop (i + 1)).take (j - i - 1)
        let l3 := (addSuff ws).drop (j + 1)
        have hsplit1 : addSuff ws = l1 ++ (ws[i], deltaN ws[i], unionN (ws.drop (i + 1))) :: (addSuff ws).drop (i + 1) := by
          have h1 : l1 ++ (addSuff ws).drop i = addSuff ws := List.take_append_drop i (addSuff ws)
          have hi_as : i < (addSuff ws).length := by omega
          have h2 : (addSuff ws).drop i = (addSuff ws)[i]'hi_as :: (addSuff ws).drop (i + 1) :=
            List.drop_eq_getElem_cons hi_as
          rw [addSuff_getElem ws i hi hi_as] at h2
          conv_lhs => rw [← h1, h2]
        have hsplit2 : (addSuff ws).drop (i + 1) = l2 ++ (ws[j], deltaN ws[j], unionN (ws.drop (j + 1))) :: l3 := by
          have h1 : l2 ++ ((addSuff ws).drop (i + 1)).drop (j - i - 1) = (addSuff ws).drop (i + 1) :=
            List.take_append_drop (j - i - 1) ((addSuff ws).drop (i + 1))
          have hlt2 : j - i - 1 < ((addSuff ws).drop (i + 1)).length := by simp [hlen_as]; omega
          have h2 : ((addSuff ws).drop (i + 1)).drop (j - i - 1) =
              ((addSuff ws).drop (i + 1))[j - i - 1]'hlt2 :: (((addSuff ws).drop (i + 1)).drop (j - i - 1 + 1)) :=
            List.drop_eq_getElem_cons hlt2
          have hg2 : ((addSuff ws).drop (i + 1))[j - i - 1]'hlt2 = (ws[j], deltaN ws[j], unionN (ws.drop (j + 1))) := by
            rw [List.getElem_drop]
            have heq : i + 1 + (j - i - 1) = j := by omega
            simp only [heq]
            exact addSuff_getElem ws j hj (by omega)
          have hd2 : ((addSuff ws).drop (i + 1)).drop (j - i - 1 + 1) = l3 := by
            simp only [l3, List.drop_drop]; congr 1; omega
          conv_lhs => rw [← h1, h2, hg2, hd2]
        have hl1_ds : ∀ p ∈ l1, p.2.1 = deltaN p.1 := by
          intro p hp
          obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hp
          have hu' : u < ws.length := by simp only [l1, List.length_take, hlen_as] at hu; omega
          rw [List.getElem_take, addSuff_getElem ws u hu' (by omega)]
        have hl2_ds : ∀ p ∈ l2, p.2.1 = deltaN p.1 := by
          intro p hp
          obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hp
          have hu' : i + 1 + u < ws.length := by simp only [l2, List.length_take, List.length_drop, hlen_as] at hu; omega
          rw [List.getElem_take, List.getElem_drop, addSuff_getElem ws (i + 1 + u) hu' (by omega)]
        rw [hsplit1] at hgoI
        obtain ⟨pos1, pos2, hgoJ⟩ := goI_hit_real l1 ws[i] (deltaN ws[i]) (unionN (ws.drop (i + 1))) ((addSuff ws).drop (i + 1)) 0 0 pos0 posEnd hl1_ds hgoI
        have hl1_len : l1.length = i := by simp [l1, hlen_as]; omega
        have hl2_len : l2.length = j - i - 1 := by simp [l2, hlen_as]; omega
        have hl1_map : l1.map Prod.fst = ws.take i := by
          apply List.ext_getElem
          · simp [l1, hlen_as]
          · intro u h1 h2
            have hu' : u < ws.length := by simp at h2; omega
            simp only [l1, List.getElem_map, List.getElem_take, addSuff_getElem ws u hu' (by omega)]
        have hl2_map : l2.map Prod.fst = (ws.drop (i + 1)).take (j - i - 1) := by
          apply List.ext_getElem
          · simp [l2, hlen_as]
          · intro u h1 h2
            have hu' : i + 1 + u < ws.length := by simp at h2; omega
            simp only [l2, List.getElem_map, List.getElem_take, List.getElem_drop, addSuff_getElem ws (i + 1 + u) hu' (by omega)]
        rw [hl1_len, Nat.zero_add, Nat.zero_or, hl1_map, hsplit2] at hgoJ
        obtain ⟨pos3, pos4, hgoOp⟩ := goJ_hit l2 ws[j] (deltaN ws[j]) (unionN (ws.drop (j + 1))) l3 (i + 1) (unionN (ws.take i)) pos1 pos2 hl2_ds hgoJ op
        have hij_eq : i + 1 + l2.length = j := by omega
        rw [hij_eq, hl2_map] at hgoOp
        have hnc : ws.contains (mix op ws[i] ws[j]) = false := by
          rw [Bool.eq_false_iff]; intro hmem
          exact hfr' (List.mem_toFinset.mpr (List.contains_iff_mem.mp hmem))
        simp only [goOp, hnc, Bool.false_eq_true, ite_false] at hgoOp
        have extract_chk {clen cov posA posB : Nat}
            (hcase : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w ka kb clen cov posA = some posB)
            (hlenOk : clen ≤ 6 + k) (hcovOk : cov = allN) : False := by
          unfold chkCase at hcase
          have hskip : (decide (clen > 6 + k) || (cov != allN)) = false := by
            simp [hcovOk]; omega
          rw [if_neg (by rw [hskip]; decide)] at hcase
          dsimp only at hcase
          split_ifs at hcase with hgood
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hgood
          let aRot := getHint posA &&& 15
          let cid := getHint posA >>> 4
          have ha12 : aRot < 12 := hgood.1.1
          have hcid : cid < cnt (d + 1) := hgood.1.2
          have hsetEq : ch.toFinset = (nodeAt (d + 1) aRot cid).toFinset := sameWordSet_eq hch_nd hgood.2
          have hcanA : Can k (nodeAt (d + 1) aRot cid).toFinset := hsetEq ▸ hcan_ch
          have hcanInv : Can k ((nodeAt (d + 1) aRot cid).toFinset.image (rotW (invAuto aRot))) :=
            can_auto (invAuto_lt ha12) hcanA
          have himg : (nodeAt (d + 1) aRot cid).toFinset.image (rotW (invAuto aRot)) =
              ((nodeAt (d + 1) aRot cid).map (rotW (invAuto aRot))).toFinset := by
            ext v; simp [List.mem_toFinset]
          rw [himg, map_rotW_nodeAt (d + 1) (by omega) (invAuto aRot) aRot cid (invAuto_lt ha12) ha12 hcid,
            compAuto_inv_left ha12] at hcanInv
          exact hchild cid hcid hcanInv
        cases hka : ka <;> cases hkb : kb
        · rw [hka, hkb] at hlen_ch; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen_ch
          have hcov := cov_allN_of_covers hij hj w false false (by simpa [ch, childFromW, hka, hkb] using can_covers hcan_ch)
          dsimp only at hcov
          cases hc1 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w false false (ws.length - 1) (((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN w) pos3 with
          | none => rw [hc1] at hgoOp; cases hgoOp
          | some p1 => exact extract_chk (by simpa [hka, hkb] using hc1) (by omega) hcov
        · rw [hka, hkb] at hlen_ch; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen_ch
          have hcov := cov_allN_of_covers hij hj w false true (by simpa [ch, childFromW, hka, hkb] using can_covers hcan_ch)
          dsimp only at hcov
          cases hc1 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w false false (ws.length - 1) (((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN w) pos3 with
          | none => rw [hc1] at hgoOp; cases hgoOp
          | some p1 =>
            rw [hc1] at hgoOp; dsimp only at hgoOp
            cases hc2 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w false true ws.length ((((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN ws[j]) ||| deltaN w) p1 with
            | none => rw [hc2] at hgoOp; cases hgoOp
            | some p2 => exact extract_chk (by simpa [hka, hkb] using hc2) (by omega) hcov
        · rw [hka, hkb] at hlen_ch; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen_ch
          have hcov := cov_allN_of_covers hij hj w true false (by simpa [ch, childFromW, hka, hkb] using can_covers hcan_ch)
          dsimp only at hcov
          cases hc1 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w false false (ws.length - 1) (((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN w) pos3 with
          | none => rw [hc1] at hgoOp; cases hgoOp
          | some p1 =>
            rw [hc1] at hgoOp; dsimp only at hgoOp
            cases hc2 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w false true ws.length ((((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN ws[j]) ||| deltaN w) p1 with
            | none => rw [hc2] at hgoOp; cases hgoOp
            | some p2 =>
              rw [hc2] at hgoOp; dsimp only at hgoOp
              cases hc3 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w true false ws.length ((((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN ws[i]) ||| deltaN w) p2 with
              | none => rw [hc3] at hgoOp; cases hgoOp
              | some p3 => exact extract_chk (by simpa [hka, hkb] using hc3) (by omega) hcov
        · rw [hka, hkb] at hlen_ch; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen_ch
          have hcov := cov_allN_of_covers hij hj w true true (by simpa [ch, childFromW, hka, hkb] using can_covers hcan_ch)
          dsimp only at hcov
          cases hc1 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w false false (ws.length - 1) (((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN w) pos3 with
          | none => rw [hc1] at hgoOp; cases hgoOp
          | some p1 =>
            rw [hc1] at hgoOp; dsimp only at hgoOp
            cases hc2 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w false true ws.length ((((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN ws[j]) ||| deltaN w) p1 with
            | none => rw [hc2] at hgoOp; cases hgoOp
            | some p2 =>
              rw [hc2] at hgoOp; dsimp only at hgoOp
              cases hc3 : chkCase ws i j (6 + k) (cnt (d + 1)) (nodeAt (d + 1)) getHint w true false ws.length ((((unionN (ws.take i) ||| unionN ((ws.drop (i + 1)).take (j - i - 1))) ||| unionN (ws.drop (j + 1))) ||| deltaN ws[i]) ||| deltaN w) p2 with
              | none => rw [hc3] at hgoOp; cases hgoOp
              | some p3 =>
                rw [hc3] at hgoOp; dsimp only at hgoOp
                exact extract_chk (by simpa [hka, hkb] using hgoOp) (by omega) hcov
      rcases Nat.lt_or_gt_of_ne hiab with hlt | hgt
      · exact stepIJ ia ib hia hib hlt hfr hs hcK
      · rw [mix_comm] at hfr hcK
        rw [Finset.insert_comm] at hs
        exact stepIJ ib ia hib hia hgt hfr hs hcK
  exact hno (k + 1) (Nat.le_refl _)

abbrev NPair := Nat × Nat
abbrev NItem := NPair × Nat

def toNP (w : Word) : NPair := (w.toNat &&& allN, w.toNat >>> 258)
def toNI (w : Word) : NItem := (toNP w, deltaN w)
def toNList (ws : List Word) : List NItem := ws.map toNI

theorem toNP_inj {a b : Word} (h : toNP a = toNP b) : a = b := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < 258
  · have ht := congrArg (fun x : Nat => x.testBit i) h1
    simp only [toNP, Nat.testBit_and, allN_testBit, hlt, decide_true, Bool.and_true] at ht
    exact ht
  · have ht := congrArg (fun x : Nat => x.testBit (i - 258)) h2
    simp only [toNP, Nat.testBit_shiftRight] at ht
    have heq : 258 + (i - 258) = i := by omega
    rw [heq] at ht
    exact ht

theorem toNP_mix (op : Bool) (a b : Word) :
    toNP (mix op a b) =
      if op then ((toNP a).1 ||| (toNP b).1, (toNP a).2 ||| (toNP b).2)
      else ((toNP a).1 &&& (toNP b).1, (toNP a).2 &&& (toNP b).2) := by
  cases op
  · apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro m
      simp only [mix, toNP, Bool.false_eq_true, ite_false, BitVec.toNat_and, Nat.testBit_and, allN_testBit]
      cases a.toNat.testBit m <;> cases b.toNat.testBit m <;> cases decide (m < 258) <;> rfl
    · apply Nat.eq_of_testBit_eq; intro m
      simp only [mix, toNP, Bool.false_eq_true, ite_false, BitVec.toNat_and, Nat.testBit_and, Nat.testBit_shiftRight]
  · apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro m
      simp only [mix, toNP, ite_true, BitVec.toNat_or, Nat.testBit_and, Nat.testBit_or, allN_testBit]
      cases a.toNat.testBit m <;> cases b.toNat.testBit m <;> cases decide (m < 258) <;> rfl
    · apply Nat.eq_of_testBit_eq; intro m
      simp only [mix, toNP, ite_true, BitVec.toNat_or, Nat.testBit_or, Nat.testBit_shiftRight]

def unionM : List NItem → Nat
  | [] => 0
  | p :: xs => p.2 ||| unionM xs

theorem unionM_toNList (ws : List Word) : unionM (toNList ws) = unionN ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [toNList, List.map_cons, toNI, unionM, unionN]
    exact congrArg (deltaN w ||| ·) ih

theorem unionM_append (xs ys : List NItem) : unionM (xs ++ ys) = unionM xs ||| unionM ys := by
  induction xs with
  | nil => simp [unionM]
  | cons x xs ih => simp [unionM, ih, Nat.lor_assoc]

def innerLoop (go : List NItem → Bool) (k n : Nat) (a : NPair) (da : Nat)
    (allWs : List NItem) (prefB : Nat) : List NItem → Bool
  | [] => false
  | (b, db) :: bs =>
    let cr := prefB ||| unionM bs
    let chkOp (w1 w2 : Nat) : Bool :=
      let dw := w1 ^^^ w2
      if (cr ||| dw) == allN then
        if allWs.any (fun q => q.1.1 == w1 && q.1.2 == w2) then false
        else if go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2) && !(q.1.1 == b.1 && q.1.2 == b.2))) then true
        else if n ≤ k + 6 &&
            ((((cr ||| da) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == b.1 && q.1.2 == b.2)))) ||
             (((cr ||| db) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2))))) then true
        else if n ≤ k + 5 && go (((w1, w2), dw) :: allWs) then true
        else false
      else if n ≤ k + 6 then
        let okB := ((cr ||| da) ||| dw) == allN
        let okA := ((cr ||| db) ||| dw) == allN
        if !okB && !okA && !(n ≤ k + 5) then false
        else if allWs.any (fun q => q.1.1 == w1 && q.1.2 == w2) then false
        else if (okB && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == b.1 && q.1.2 == b.2)))) ||
                (okA && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2)))) then true
        else if n ≤ k + 5 && go (((w1, w2), dw) :: allWs) then true
        else false
      else false
    chkOp (a.1 &&& b.1) (a.2 &&& b.2) || chkOp (a.1 ||| b.1) (a.2 ||| b.2) ||
      innerLoop go k n a da allWs (prefB ||| db) bs

def outerLoop (go : List NItem → Bool) (k n : Nat) (allWs : List NItem) (pref : Nat) : List NItem → Bool
  | [] => false
  | (a, da) :: rest =>
    innerLoop go k n a da allWs pref rest || outerLoop go k n allWs (pref ||| da) rest

def searchL : Nat → List NItem → Bool
  | 0, xs => xs.length ≤ 6
  | k + 1, xs =>
    let n := xs.length
    if n ≤ 6 then true
    else if n > k + 7 then false
    else outerLoop (searchL k) k n xs 0 xs

theorem chkOp_hit {c0 cB cA fr g0 gB gA gBoth : Bool} {n k : Nat}
    (hfr : fr = false)
    (hc : (c0 && g0) = true ∨ (n ≤ k + 6 ∧ ((cB && gB) = true ∨ (cA && gA) = true)) ∨ (n ≤ k + 5 ∧ gBoth = true)) :
    (if c0 then
      if fr then false
      else if g0 then true
      else if n ≤ k + 6 && ((cB && gB) || (cA && gA)) then true
      else if n ≤ k + 5 && gBoth then true
      else false
    else if n ≤ k + 6 then
      if !cB && !cA && !(n ≤ k + 5) then false
      else if fr then false
      else if (cB && gB) || (cA && gA) then true
      else if n ≤ k + 5 && gBoth then true
      else false
    else false) = true := by
  subst hfr
  rcases hc with h0 | ⟨h6, h1 | h2⟩ | ⟨h5, h3⟩
  · cases c0 <;> cases g0 <;> simp_all
  · cases cB <;> cases gB <;> cases c0 <;> cases g0 <;> simp_all
  · cases cA <;> cases gA <;> cases c0 <;> cases g0 <;> simp_all
  · have h6 : n ≤ k + 6 := by omega
    cases c0 <;> cases g0 <;> cases cB <;> cases gB <;> cases cA <;> cases gA <;> cases gBoth <;> simp_all

theorem innerLoop_hit {go k n a da allWs} :
    ∀ (l2 : List NItem) (b : NPair) (db : Nat) (l3 : List NItem) (pref0 : Nat) (op : Bool),
      let w1 := if op then a.1 ||| b.1 else a.1 &&& b.1
      let w2 := if op then a.2 ||| b.2 else a.2 &&& b.2
      let dw := w1 ^^^ w2
      let cr := (pref0 ||| unionM l2) ||| unionM l3
      allWs.any (fun q => q.1.1 == w1 && q.1.2 == w2) = false →
      (((cr ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2) && !(q.1.1 == b.1 && q.1.2 == b.2)))) = true ∨
       (n ≤ k + 6 ∧
         ((((cr ||| da) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == b.1 && q.1.2 == b.2)))) = true ∨
          (((cr ||| db) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2)))) = true)) ∨
       (n ≤ k + 5 ∧ go (((w1, w2), dw) :: allWs) = true)) →
      innerLoop go k n a da allWs pref0 (l2 ++ (b, db) :: l3) = true := by
  intro l2
  induction l2 with
  | nil =>
    intro b db l3 pref0 op
    dsimp only
    intro hfr hcond
    rw [List.nil_append]
    unfold innerLoop
    dsimp only
    rw [Bool.or_eq_true]
    left
    have hcr0 : (pref0 ||| unionM []) ||| unionM l3 = pref0 ||| unionM l3 := by simp [unionM]
    rw [hcr0] at hcond
    rw [Bool.or_eq_true]
    cases op
    · left; exact chkOp_hit hfr hcond
    · right; exact chkOp_hit hfr hcond
  | cons x xs ih =>
    intro b db l3 pref0 op
    dsimp only
    intro hfr hcond
    rcases x with ⟨bx, dx⟩
    rw [List.cons_append]
    unfold innerLoop
    dsimp only
    rw [Bool.or_eq_true]
    right
    apply ih b db l3 (pref0 ||| dx) op hfr
    have hor : ((pref0 ||| dx) ||| unionM xs) ||| unionM l3 = (pref0 ||| unionM ((bx, dx) :: xs)) ||| unionM l3 := by
      simp [unionM, Nat.lor_assoc]
    rwa [hor]

theorem outerLoop_hit {go k n allWs} :
    ∀ (l1 : List NItem) (a : NPair) (da : Nat) (l2 : List NItem) (b : NPair) (db : Nat) (l3 : List NItem)
      (pref0 : Nat) (op : Bool),
      let w1 := if op then a.1 ||| b.1 else a.1 &&& b.1
      let w2 := if op then a.2 ||| b.2 else a.2 &&& b.2
      let dw := w1 ^^^ w2
      let cr := ((pref0 ||| unionM l1) ||| unionM l2) ||| unionM l3
      allWs.any (fun q => q.1.1 == w1 && q.1.2 == w2) = false →
      (((cr ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2) && !(q.1.1 == b.1 && q.1.2 == b.2)))) = true ∨
       (n ≤ k + 6 ∧
         ((((cr ||| da) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == b.1 && q.1.2 == b.2)))) = true ∨
          (((cr ||| db) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2)))) = true)) ∨
       (n ≤ k + 5 ∧ go (((w1, w2), dw) :: allWs) = true)) →
      outerLoop go k n allWs pref0 (l1 ++ (a, da) :: (l2 ++ (b, db) :: l3)) = true := by
  intro l1
  induction l1 with
  | nil =>
    intro a da l2 b db l3 pref0 op
    dsimp only
    intro hfr hcond
    simp only [List.nil_append, outerLoop, Bool.or_eq_true]
    left
    have hcr0 : ((pref0 ||| unionM []) ||| unionM l2) ||| unionM l3 = (pref0 ||| unionM l2) ||| unionM l3 := by simp [unionM]
    rw [hcr0] at hcond
    exact innerLoop_hit l2 b db l3 pref0 op hfr hcond
  | cons x xs ih =>
    intro a da l2 b db l3 pref0 op
    dsimp only
    intro hfr hcond
    rcases x with ⟨ax, dx⟩
    simp only [List.cons_append, outerLoop, Bool.or_eq_true]
    right
    apply ih a da l2 b db l3 (pref0 ||| dx) op hfr
    have hor : (((pref0 ||| dx) ||| unionM xs) ||| unionM l2) ||| unionM l3 =
        ((pref0 ||| unionM ((ax, dx) :: xs)) ||| unionM l2) ||| unionM l3 := by
      simp [unionM, Nat.lor_assoc]
    rwa [hor]

theorem mem_order {α : Type} : ∀ {l : List α} {a b : α}, a ∈ l → b ∈ l → a ≠ b →
    (∃ l1 l2 l3, l = l1 ++ a :: (l2 ++ b :: l3)) ∨ (∃ l1 l2 l3, l = l1 ++ b :: (l2 ++ a :: l3)) := by
  intro l a b ha hb hab
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact (hab rfl).elim
      · obtain ⟨l2, l3, rfl⟩ := List.append_of_mem hb'
        exact Or.inl ⟨[], l2, l3, rfl⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨l2, l3, rfl⟩ := List.append_of_mem ha'
        exact Or.inr ⟨[], l2, l3, rfl⟩
      · rcases ih ha' hb' with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
        · exact Or.inl ⟨x :: l1, l2, l3, rfl⟩
        · exact Or.inr ⟨x :: l1, l2, l3, rfl⟩

theorem toNList_filter_eq (ws : List Word) (p : Word → Bool) (q : NPair → Bool)
    (hpq : ∀ x, q (toNP x) = p x) :
    (toNList ws).filter (fun r => q r.1) = toNList (ws.filter p) := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    simp only [toNList, List.map_cons, List.filter_cons, toNI, hpq]
    cases hp : p x <;> simp [toNList, toNI] at ih ⊢ <;> exact ih

theorem cov_searchL_allN {l1 l2 l3 : List Word} {a b w : Word} (ka kb : Bool)
    (hc : Covers (w :: (l1 ++ (if ka then [a] else []) ++ l2 ++ (if kb then [b] else []) ++ l3)).toFinset) :
    let cr := ((0 ||| unionM (toNList l1)) ||| unionM (toNList l2)) ||| unionM (toNList l3)
    let da := deltaN a; let db := deltaN b; let dw := deltaN w
    (match ka, kb with
     | false, false => cr ||| dw
     | true, false  => (cr ||| da) ||| dw
     | false, true  => (cr ||| db) ||| dw
     | true, true   => allN) = allN := by
  have hge (x y : Nat) (hx : ∀ m, 258 ≤ m → x.testBit m = false) (hy : ∀ m, 258 ≤ m → y.testBit m = false) :
      ∀ m, 258 ≤ m → (x ||| y).testBit m = false := by
    intro m hm; simp [Nat.testBit_or, hx m hm, hy m hm]
  have hcr_ge : ∀ m, 258 ≤ m → (((0 ||| unionM (toNList l1)) ||| unionM (toNList l2)) ||| unionM (toNList l3)).testBit m = false := by
    simp only [Nat.zero_or, unionM_toNList]
    exact hge _ _ (hge _ _ (fun m hm => unionN_testBit_ge _ hm) (fun m hm => unionN_testBit_ge _ hm)) (fun m hm => unionN_testBit_ge _ hm)
  cases ka <;> cases kb
  · apply Nat.eq_of_testBit_eq; intro m; rw [allN_testBit]
    by_cases hm : m < 258
    · simp only [hm, decide_true, Nat.zero_or, unionM_toNList]
      obtain ⟨v, hv, hd⟩ := hc ⟨m, hm⟩
      have hdv : (deltaN v).testBit m = true := by rw [deltaN_testBit_lt v hm]; exact bne_iff_ne.mpr hd
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, Bool.false_eq_true, ite_false,
        List.append_nil, List.mem_append] at hv
      rcases hv with rfl | ((h1 | h2) | h3)
      · simp [Nat.testBit_or, hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h1 hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h2 hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h3 hdv]
    · simp only [hm, decide_false]
      have hgeM : 258 ≤ m := by omega
      simp only [Nat.zero_or, unionM_toNList, Nat.testBit_or, unionN_testBit_ge _ hgeM, deltaN_testBit_ge _ hgeM]; rfl
  · apply Nat.eq_of_testBit_eq; intro m; rw [allN_testBit]
    by_cases hm : m < 258
    · simp only [hm, decide_true, Nat.zero_or, unionM_toNList]
      obtain ⟨v, hv, hd⟩ := hc ⟨m, hm⟩
      have hdv : (deltaN v).testBit m = true := by rw [deltaN_testBit_lt v hm]; exact bne_iff_ne.mpr hd
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, Bool.false_eq_true, ite_false, ite_true,
        List.append_nil, List.mem_append, List.mem_singleton] at hv
      rcases hv with rfl | (((h1 | h2) | rfl) | h3)
      · simp [Nat.testBit_or, hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h1 hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h2 hdv]
      · simp [Nat.testBit_or, hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h3 hdv]
    · simp only [hm, decide_false]
      have hgeM : 258 ≤ m := by omega
      simp only [Nat.zero_or, unionM_toNList, Nat.testBit_or, unionN_testBit_ge _ hgeM, deltaN_testBit_ge _ hgeM]; rfl
  · apply Nat.eq_of_testBit_eq; intro m; rw [allN_testBit]
    by_cases hm : m < 258
    · simp only [hm, decide_true, Nat.zero_or, unionM_toNList]
      obtain ⟨v, hv, hd⟩ := hc ⟨m, hm⟩
      have hdv : (deltaN v).testBit m = true := by rw [deltaN_testBit_lt v hm]; exact bne_iff_ne.mpr hd
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, Bool.false_eq_true, ite_false, ite_true,
        List.append_nil, List.mem_append, List.mem_singleton] at hv
      rcases hv with rfl | (((h1 | rfl) | h2) | h3)
      · simp [Nat.testBit_or, hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h1 hdv]
      · simp [Nat.testBit_or, hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h2 hdv]
      · simp [Nat.testBit_or, unionN_testBit_of_mem h3 hdv]
    · simp only [hm, decide_false]
      have hgeM : 258 ≤ m := by omega
      simp only [Nat.zero_or, unionM_toNList, Nat.testBit_or, unionN_testBit_ge _ hgeM, deltaN_testBit_ge _ hgeM]; rfl
  · rfl

theorem searchL_sound (fuel : Nat) (ws : List Word) (nd : ws.Nodup)
    {k : Nat} (hk : k ≤ fuel) (h : Can k ws.toFinset) : searchL fuel (toNList ws) = true := by
  induction fuel generalizing ws k with
  | zero =>
    have : k = 0 := by omega
    subst k
    have hc := h.2
    rw [List.toFinset_card_of_nodup nd] at hc
    simpa [searchL, toNList] using hc
  | succ fuel ih =>
    unfold searchL; dsimp only
    split
    · rfl
    split
    · have := can_size h
      rw [List.toFinset_card_of_nodup nd] at this
      simp only [toNList, List.length_map] at *
      omega
    rename_i big fits
    have takeStep (a b : Word) (l1 l2 l3 : List Word) (hws : ws = l1 ++ a :: (l2 ++ b :: l3))
        (hab : a ≠ b) (op : Bool) (t : Finset Word) (kt : Nat) (hkt : kt ≤ fuel)
        (fresh : mix op a b ∉ ws.toFinset) (ht : t ⊆ ws.toFinset)
        (hs : ws.toFinset ⊆ insert a (insert b t)) (hc : Can kt (insert (mix op a b) t)) :
        outerLoop (searchL fuel) fuel (toNList ws).length (toNList ws) 0 (toNList ws) = true := by
      let w := mix op a b
      have ha : a ∈ ws := by rw [hws]; simp
      have hb : b ∈ ws := by rw [hws]; simp
      have hsplit : toNList ws = toNList l1 ++ toNI a :: (toNList l2 ++ toNI b :: toNList l3) := by
        rw [hws]; simp [toNList]
      have hnpw := toNP_mix op a b
      have hdw_eq : (if op then (toNP a).1 ||| (toNP b).1 else (toNP a).1 &&& (toNP b).1) ^^^
          (if op then (toNP a).2 ||| (toNP b).2 else (toNP a).2 &&& (toNP b).2) = deltaN w := by
        have h1 := congrArg Prod.fst hnpw
        have h2 := congrArg Prod.snd hnpw
        cases op <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h1 h2 ⊢ <;> rw [← h1, ← h2] <;> rfl
      have hpair_eq : (if op then (toNP a).1 ||| (toNP b).1 else (toNP a).1 &&& (toNP b).1,
          if op then (toNP a).2 ||| (toNP b).2 else (toNP a).2 &&& (toNP b).2) = toNP w := by
        cases op <;> simpa using hnpw.symm
      have hfresh_b : (toNList ws).any (fun q =>
          q.1.1 == (if op then (toNP a).1 ||| (toNP b).1 else (toNP a).1 &&& (toNP b).1) &&
          q.1.2 == (if op then (toNP a).2 ||| (toNP b).2 else (toNP a).2 &&& (toNP b).2)) = false := by
        rw [List.any_eq_false]
        intro q hq heq
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
        simp only [toNI, Bool.and_eq_true, beq_iff_eq] at heq
        have hnpu : toNP u = toNP w := by rw [← hpair_eq]; exact Prod.ext heq.1 heq.2
        have huw : u = w := toNP_inj hnpu
        subst huw; exact fresh (List.mem_toFinset.mpr hu)
      have useF (ka kb : Bool) (ea : ka = decide (a ∈ t)) (eb : kb = decide (b ∈ t)) :
          let sub := ws.filter (fun x => (ka || x != a) && (kb || x != b))
          (w :: sub).toFinset = insert w t ∧ (w :: sub).Nodup ∧ (w :: sub).length ≤ 6 + fuel ∧
          searchL fuel (toNList (w :: sub)) = true := by
        let sub := ws.filter (fun x => (ka || x != a) && (kb || x != b))
        have hsub : sub.toFinset = t := by
          ext x
          simp only [sub, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
          constructor
          · rintro ⟨hxw, hxa, hxb⟩
            have hu := hs (List.mem_toFinset.mpr hxw)
            simp only [Finset.mem_insert] at hu
            rcases hu with rfl | rfl | hxt
            · rcases hxa with hka | hne
              · rw [ea] at hka; exact of_decide_eq_true hka
              · exact (hne rfl).elim
            · rcases hxb with hkb | hne
              · rw [eb] at hkb; exact of_decide_eq_true hkb
              · exact (hne rfl).elim
            · exact hxt
          · intro hxt
            refine ⟨List.mem_toFinset.mp (ht hxt), ?_, ?_⟩
            · by_cases hxa : x = a
              · subst x; left; rw [ea]; exact decide_eq_true hxt
              · right; exact hxa
            · by_cases hxb : x = b
              · subst x; left; rw [eb]; exact decide_eq_true hxt
              · right; exact hxb
        have heqF : (w :: sub).toFinset = insert w t := by rw [List.toFinset_cons, hsub]
        have hnd : (w :: sub).Nodup :=
          List.nodup_cons.mpr ⟨fun h => fresh (List.mem_toFinset.mpr (List.mem_of_mem_filter h)), nd.filter _⟩
        have hcan : Can kt (w :: sub).toFinset := by rwa [heqF]
        have hlen := can_size hcan
        rw [List.toFinset_card_of_nodup hnd] at hlen
        exact ⟨heqF, hnd, Nat.le_trans hlen (by omega), ih _ hnd hkt hcan⟩
      have hnp_beq (x y : Word) : (toNP x == toNP y) = (x == y) := by
        cases h1 : (x == y)
        · simp only [beq_eq_false_iff_ne] at h1 ⊢; intro he; exact h1 (toNP_inj he)
        · rw [beq_iff_eq.mp h1]; simp
      have hnp_eq2 (x y : Word) : ((toNP x).1 == (toNP y).1 && (toNP x).2 == (toNP y).2) = (x == y) := by
        cases h1 : (x == y)
        · simp only [beq_eq_false_iff_ne] at h1
          rw [Bool.eq_false_iff]; intro he
          simp only [Bool.and_eq_true, beq_iff_eq] at he
          exact h1 (toNP_inj (Prod.ext he.1 he.2))
        · rw [beq_iff_eq.mp h1]; simp
      have hfl0 : (toNList ws).filter (fun q => !(q.1.1 == (toNP a).1 && q.1.2 == (toNP a).2) && !(q.1.1 == (toNP b).1 && q.1.2 == (toNP b).2)) =
          toNList (ws.filter (fun x => (false || x != a) && (false || x != b))) :=
        toNList_filter_eq ws _ (fun r => !(r.1 == (toNP a).1 && r.2 == (toNP a).2) && !(r.1 == (toNP b).1 && r.2 == (toNP b).2))
          (fun x => by simp [hnp_eq2, bne])
      have hflB : (toNList ws).filter (fun q => !(q.1.1 == (toNP b).1 && q.1.2 == (toNP b).2)) =
          toNList (ws.filter (fun x => (true || x != a) && (false || x != b))) :=
        toNList_filter_eq ws _ (fun r => !(r.1 == (toNP b).1 && r.2 == (toNP b).2))
          (fun x => by simp [hnp_eq2, bne])
      have hflA : (toNList ws).filter (fun q => !(q.1.1 == (toNP a).1 && q.1.2 == (toNP a).2)) =
          toNList (ws.filter (fun x => (false || x != a) && (true || x != b))) :=
        toNList_filter_eq ws _ (fun r => !(r.1 == (toNP a).1 && r.2 == (toNP a).2))
          (fun x => by simp [hnp_eq2, bne])
      have hsub_toFinset (ka kb : Bool) :
          (ws.filter (fun x => (ka || x != a) && (kb || x != b))).toFinset =
            (l1 ++ (if ka then [a] else []) ++ l2 ++ (if kb then [b] else []) ++ l3).toFinset := by
        have hnd' := nd
        rw [hws] at hnd'
        have h1 : a ∉ l1 ∧ a ∉ l2 ∧ a ∉ l3 ∧ b ∉ l1 ∧ b ∉ l2 ∧ b ∉ l3 := by
          simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons] at hnd'
          refine ⟨fun h => hnd'.2.2 a h a (Or.inl rfl) rfl,
            fun h => hnd'.2.1.1 (Or.inl h),
            fun h => hnd'.2.1.1 (Or.inr (Or.inr h)),
            fun h => hnd'.2.2 b h b (Or.inr (Or.inr (Or.inl rfl))) rfl,
            fun h => hnd'.2.1.2.2.2 b h b (Or.inl rfl) rfl,
            fun h => hnd'.2.1.2.2.1.1 h⟩
        ext x
        simp only [hws, List.mem_toFinset, List.mem_filter, List.mem_append, List.mem_cons,
          Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
        cases ka <;> cases kb <;>
          simp only [Bool.false_eq_true, false_or, or_false, true_or, true_and, and_true, ite_false, ite_true, List.not_mem_nil, List.mem_singleton]
        · constructor
          · rintro ⟨(hx | rfl | hx | rfl | hx), hxa, hxb⟩
            · exact Or.inl (Or.inl hx)
            · exact (hxa rfl).elim
            · exact Or.inl (Or.inr hx)
            · exact (hxb rfl).elim
            · exact Or.inr hx
          · rintro ((hx | hx) | hx)
            · exact ⟨Or.inl hx, fun e => h1.1 (e ▸ hx), fun e => h1.2.2.2.1 (e ▸ hx)⟩
            · exact ⟨Or.inr (Or.inr (Or.inl hx)), fun e => h1.2.1 (e ▸ hx), fun e => h1.2.2.2.2.1 (e ▸ hx)⟩
            · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr hx))), fun e => h1.2.2.1 (e ▸ hx), fun e => h1.2.2.2.2.2 (e ▸ hx)⟩
        · constructor
          · rintro ⟨(hx | rfl | hx | rfl | hx), hxa⟩
            · exact Or.inl (Or.inl (Or.inl hx))
            · exact (hxa rfl).elim
            · exact Or.inl (Or.inl (Or.inr hx))
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr hx
          · rintro (((hx | hx) | rfl) | hx)
            · exact ⟨Or.inl hx, fun e => h1.1 (e ▸ hx)⟩
            · exact ⟨Or.inr (Or.inr (Or.inl hx)), fun e => h1.2.1 (e ▸ hx)⟩
            · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), hab.symm⟩
            · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr hx))), fun e => h1.2.2.1 (e ▸ hx)⟩
        · constructor
          · rintro ⟨(hx | rfl | hx | rfl | hx), hxb⟩
            · exact Or.inl (Or.inl (Or.inl hx))
            · exact Or.inl (Or.inl (Or.inr rfl))
            · exact Or.inl (Or.inr hx)
            · exact (hxb rfl).elim
            · exact Or.inr hx
          · rintro (((hx | rfl) | hx) | hx)
            · exact ⟨Or.inl hx, fun e => h1.2.2.2.1 (e ▸ hx)⟩
            · exact ⟨Or.inr (Or.inl rfl), hab⟩
            · exact ⟨Or.inr (Or.inr (Or.inl hx)), fun e => h1.2.2.2.2.1 (e ▸ hx)⟩
            · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr hx))), fun e => h1.2.2.2.2.2 (e ▸ hx)⟩
        · constructor
          · rintro (hx | rfl | hx | rfl | hx)
            · exact Or.inl (Or.inl (Or.inl (Or.inl hx)))
            · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
            · exact Or.inl (Or.inl (Or.inr hx))
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr hx
          · rintro ((((hx | rfl) | hx) | rfl) | hx)
            · exact Or.inl hx
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl hx))
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
      nth_rw 3 [hsplit]
      apply outerLoop_hit (toNList l1) (toNP a) (deltaN a) (toNList l2) (toNP b) (deltaN b) (toNList l3) 0 op hfresh_b
      by_cases ha_t : a ∈ t <;> by_cases hb_t : b ∈ t
      · obtain ⟨_, _, hlen, hsf⟩ := useF true true (by simp [ha_t]) (by simp [hb_t])
        right; right
        have hlen' : ws.length ≤ fuel + 5 := by
          simp only [List.length_cons, Bool.true_or, Bool.and_self, List.filter_true] at hlen; omega
        refine ⟨by simpa [toNList] using hlen', ?_⟩
        rw [hpair_eq, hdw_eq]
        simpa [toNList, toNI, List.filter_true] using hsf
      · obtain ⟨heqF, _, hlen, hsf⟩ := useF true false (by simp [ha_t]) (by simp [hb_t])
        have hcov := cov_searchL_allN (l1:=l1) (l2:=l2) (l3:=l3) (a:=a) (b:=b) (w:=w) true false (by
          have h1 := can_covers hc
          rw [← heqF, List.toFinset_cons, hsub_toFinset true false, ← List.toFinset_cons] at h1
          exact h1)
        dsimp only at hcov
        have hsub_len : (ws.filter (fun x => (true || x != a) && (false || x != b))).length = ws.length - 1 := by
          have hp := List.perm_cons_erase hb
          have : (ws.filter (fun x => (true || x != a) && (false || x != b))).Perm (ws.erase b) := by
            simp only [Bool.true_or, Bool.false_or, Bool.true_and]
            have h1 := hp.filter (fun x => x != b)
            have hnb : (ws.erase b).filter (fun x => x != b) = ws.erase b := by
              rw [List.filter_eq_self]; intro x hx; exact bne_iff_ne.mpr (fun e => nd.not_mem_erase (e ▸ hx))
            simpa [hnb] using h1
          rw [this.length_eq, List.length_erase_of_mem hb]
        have hpos : 1 ≤ ws.length := List.length_pos_of_mem hb
        right; left
        refine ⟨by simp only [List.length_cons] at hlen; simp only [toNList, List.length_map]; omega, Or.inl ?_⟩
        rw [hpair_eq, hdw_eq, hflB, hcov]
        simpa [toNList, toNI] using hsf
      · obtain ⟨heqF, _, hlen, hsf⟩ := useF false true (by simp [ha_t]) (by simp [hb_t])
        have hcov := cov_searchL_allN (l1:=l1) (l2:=l2) (l3:=l3) (a:=a) (b:=b) (w:=w) false true (by
          have h1 := can_covers hc
          rw [← heqF, List.toFinset_cons, hsub_toFinset false true, ← List.toFinset_cons] at h1
          exact h1)
        dsimp only at hcov
        have hsub_len : (ws.filter (fun x => (false || x != a) && (true || x != b))).length = ws.length - 1 := by
          have hp := List.perm_cons_erase ha
          have : (ws.filter (fun x => (false || x != a) && (true || x != b))).Perm (ws.erase a) := by
            simp only [Bool.false_or, Bool.true_or, Bool.and_true]
            have h1 := hp.filter (fun x => x != a)
            have hna : (ws.erase a).filter (fun x => x != a) = ws.erase a := by
              rw [List.filter_eq_self]; intro x hx; exact bne_iff_ne.mpr (fun e => nd.not_mem_erase (e ▸ hx))
            simpa [hna] using h1
          rw [this.length_eq, List.length_erase_of_mem ha]
        have hpos : 1 ≤ ws.length := List.length_pos_of_mem ha
        right; left
        refine ⟨by simp only [List.length_cons] at hlen; simp only [toNList, List.length_map]; omega, Or.inr ?_⟩
        rw [hpair_eq, hdw_eq, hflA, hcov]
        simpa [toNList, toNI] using hsf
      · obtain ⟨heqF, _, _, hsf⟩ := useF false false (by simp [ha_t]) (by simp [hb_t])
        have hcov := cov_searchL_allN (l1:=l1) (l2:=l2) (l3:=l3) (a:=a) (b:=b) (w:=w) false false (by
          have h1 := can_covers hc
          rw [← heqF, List.toFinset_cons, hsub_toFinset false false, ← List.toFinset_cons] at h1
          exact h1)
        dsimp only at hcov
        left
        rw [hpair_eq, hdw_eq, hfl0, hcov]
        simpa [toNList, toNI] using hsf
    induction k with
    | zero =>
      have := h.2; rw [List.toFinset_card_of_nodup nd] at this
      simp only [toNList, List.length_map] at big; omega
    | succ k ik =>
      rcases h with h | ⟨_, a, ha, b, hb, op, t, hab, _, _, fr, ht, hs, hc⟩
      · exact ik (by omega) h
      rcases mem_order (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with ⟨l1, l2, l3, hord⟩ | ⟨l1, l2, l3, hord⟩
      · exact takeStep a b l1 l2 l3 hord hab op t k (by omega) fr ht hs hc
      · rw [mix_comm] at fr hc
        rw [Finset.insert_comm] at hs
        exact takeStep b a l1 l2 l3 hord hab.symm op t k (by omega) fr ht hs hc


def rwn0 : NPair := (0x7e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07, 0x210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f)
def rwn1 : NPair := (0x3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038, 0x3e0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279)
def rwn2 : NPair := (0x1f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0, 0x421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0)
def rwn3 : NPair := (0xffc0000fffe00001f80001ff00000001ffc000007ffc000, 0x84208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480)
def rwn4 : NPair := (0x3ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000, 0x3ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802)
def rwn5 : NPair := (0x7fffffc00000000fffffffffe000000000, 0x10842084210822109042108882108917fffffc00802010fffffffffe000101004)
def rwn6 : NPair := (0x3fffffe000000007ffffffffffffff0000000000000000000, 0x21084108421044213ffffff004001007ffffffffffffff0100400040102000020)
def rwn7 : NPair := (0x3fffffe0000000003ffffffffffffff8000000000000000000000000000000000, 0x3ffffff0002080003ffffffffffffffa108211000041004208821085000002100)
def rwn8 : NPair := (0x3fffffffffffffffc000000000000000000000000000000000000000000000000, 0x3fffffffffffffffe084210008210004210422110882228411042108004210000)

def startRotN (z : Bool) (a : Nat) : List NPair :=
  match z, a with
  | false, 0 => [rwn0,rwn1,rwn2,rwn3,rwn4,rwn5,rwn6,rwn7,rwn8]
  | false, 1 => [rwn0,rwn5,rwn8,rwn3,rwn4,rwn1,rwn7,rwn6,rwn2]
  | false, 2 => [rwn1,rwn0,rwn5,rwn8,rwn6,rwn2,rwn4,rwn7,rwn3]
  | false, 3 => [rwn5,rwn0,rwn1,rwn2,rwn7,rwn8,rwn4,rwn6,rwn3]
  | false, 4 => [rwn2,rwn1,rwn0,rwn5,rwn7,rwn3,rwn6,rwn4,rwn8]
  | false, 5 => [rwn8,rwn5,rwn0,rwn1,rwn6,rwn3,rwn7,rwn4,rwn2]
  | false, 6 => [rwn3,rwn2,rwn1,rwn0,rwn4,rwn8,rwn7,rwn6,rwn5]
  | false, 7 => [rwn3,rwn8,rwn5,rwn0,rwn4,rwn2,rwn6,rwn7,rwn1]
  | false, 8 => [rwn1,rwn2,rwn3,rwn8,rwn6,rwn0,rwn7,rwn4,rwn5]
  | false, 9 => [rwn5,rwn8,rwn3,rwn2,rwn7,rwn0,rwn6,rwn4,rwn1]
  | false, 10 => [rwn8,rwn3,rwn2,rwn1,rwn6,rwn5,rwn4,rwn7,rwn0]
  | false, 11 => [rwn2,rwn3,rwn8,rwn5,rwn7,rwn1,rwn4,rwn6,rwn0]
  | true, 0 => [rwn0,rwn1,rwn2,rwn3,rwn4,rwn5,rwn6,rwn7,rwn8, (0x7e1f803ff83e00f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc7, 0x631fe3f8c7ff8fe05f8be4330fe27efc22fc7e3f2fffcf86218fe33e68fe7fdf)]
  | true, 1 => [rwn0,rwn5,rwn8,rwn3,rwn4,rwn1,rwn7,rwn6,rwn2, (0x3fffffffffffffffc0f83e00003e01e000000001f0fc3c00000000000003e3e07, 0x3fffffffffffffffe1fc3f01187f03e4630c6633f8fe3e8c330c631a22c7f3e0f)]
  | true, 2 => [rwn1,rwn0,rwn5,rwn8,rwn6,rwn2,rwn4,rwn7,rwn3, (0x3e0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038, 0x3e8fa2857d092fd2924a52bf8fd29f37fffffc44912455fffffffffe5e7d2127d)]
  | true, 3 => [rwn5,rwn0,rwn1,rwn2,rwn7,rwn8,rwn4,rwn6,rwn3, (0x3e0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038, 0x3e8fa2857d092fd2924a52bf8fd29f37fffffc44912455fffffffffe5e7d2127d)]
  | true, 4 => [rwn2,rwn1,rwn0,rwn5,rwn7,rwn3,rwn6,rwn4,rwn8, (0x7e1f803ff83e00f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc7, 0x631fe3f8c7ff8fe05f8be4330fe27efc22fc7e3f2fffcf86218fe33e68fe7fdf)]
  | true, 5 => [rwn8,rwn5,rwn0,rwn1,rwn6,rwn3,rwn7,rwn4,rwn2, (0x3fffffffffffffffc0f83e00003e01e000000001f0fc3c00000000000003e3e07, 0x3fffffffffffffffe1fc3f01187f03e4630c6633f8fe3e8c330c631a22c7f3e0f)]
  | true, 6 => [rwn3,rwn2,rwn1,rwn0,rwn4,rwn8,rwn7,rwn6,rwn5, (0x3e0f80007c0007c000ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038, 0x3e4f8a437c831fc64affc23f4ffffe218df988cdff0cc537e5ffcdf0df7ffc6f9)]
  | true, 7 => [rwn3,rwn8,rwn5,rwn0,rwn4,rwn2,rwn6,rwn7,rwn1, (0xffc0000fffe007fffffc01ff0000fffffffffe007ffc000, 0x18c628c6318a3314d8ffd08ccfffe917fffffc89ff2890fffffffffe897ffd484)]
  | true, 8 => [rwn1,rwn2,rwn3,rwn8,rwn6,rwn0,rwn7,rwn4,rwn5, (0x3e0f80007c0007c000ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038, 0x3e4f8a437c831fc64affc23f4ffffe218df988cdff0cc537e5ffcdf0df7ffc6f9)]
  | true, 9 => [rwn5,rwn8,rwn3,rwn2,rwn7,rwn0,rwn6,rwn4,rwn1, (0xffc0000fffe007fffffc01ff0000fffffffffe007ffc000, 0x18c628c6318a3314d8ffd08ccfffe917fffffc89ff2890fffffffffe897ffd484)]
  | true, 10 => [rwn8,rwn3,rwn2,rwn1,rwn6,rwn5,rwn4,rwn7,rwn0, (0x3fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0, 0x3fffffffffffffffe494a54228a5244fe127e3f12affe2fc5114bf29e44a57fd0)]
  | true, 11 => [rwn2,rwn3,rwn8,rwn5,rwn7,rwn1,rwn4,rwn6,rwn0, (0x3fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0, 0x3fffffffffffffffe494a54228a5244fe127e3f12affe2fc5114bf29e44a57fd0)]
  | _, _ => []

def mixN (op : Bool) (a b : NPair) : NPair :=
  if op then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)

def keepGoN (t i j : Nat) (ka kb : Bool) : List NPair → List NPair
  | [] => []
  | w :: ws =>
    if (t == i && !ka) || (t == j && !kb) then keepGoN (t + 1) i j ka kb ws
    else w :: keepGoN (t + 1) i j ka kb ws

def childFromN (ws : List NPair) (i j : Nat) (op ka kb : Bool) : List NPair :=
  mixN op (ws.getD i (0, 0)) (ws.getD j (0, 0)) :: keepGoN 0 i j ka kb ws

def nodeAtN : Nat → Nat → Nat → List NPair
  | 0, a, idx => startRotN (idx == 1) a
  | d + 1, a, idx =>
    let v := recOf d idx
    childFromN (nodeAtN d (compAuto a (v &&& 15)) (v >>> 15))
      ((v >>> 11) &&& 15) ((v >>> 7) &&& 15)
      (((v >>> 6) &&& 1) == 1) (((v >>> 5) &&& 1) == 1) (((v >>> 4) &&& 1) == 1)

theorem startRotN_eq (z : Bool) {a : Nat} (ha : a < 12) :
    startRotN z a = (startRot z a).map toNP := by
  cases z <;> interval_cases a <;> decide +kernel

theorem keepGoN_map (t i j : Nat) (ka kb : Bool) (ws : List Word) :
    keepGoN t i j ka kb (ws.map toNP) = (keepGo t i j ka kb ws).map toNP := by
  induction ws generalizing t with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, keepGoN, keepGo]
    split_ifs
    · exact ih (t + 1)
    · simp only [List.map_cons, ih (t + 1)]

theorem childFromN_map (ws : List Word) {i j : Nat} (hi : i < ws.length) (hj : j < ws.length)
    (op ka kb : Bool) :
    childFromN (ws.map toNP) i j op ka kb = (childFrom ws i j op ka kb).map toNP := by
  have hget (t : Nat) (ht : t < ws.length) : (ws.map toNP).getD t (0, 0) = toNP (ws.getD t 0) := by
    rw [List.getD_eq_getElem _ _ (by simp [ht]), List.getElem_map, List.getD_eq_getElem _ _ ht]
  simp only [childFromN, childFrom, List.map_cons, hget i hi, hget j hj, keepGoN_map]
  congr 1
  exact (toNP_mix op (ws.getD i 0) (ws.getD j 0)).symm

theorem nodeAtN_eq (d : Nat) (hd : d ≤ 3) :
    ∀ a idx, a < 12 → idx < cnt d → nodeAtN d a idx = (nodeAt d a idx).map toNP := by
  induction d with
  | zero =>
    intro a idx ha _
    exact startRotN_eq (idx == 1) ha
  | succ d ih =>
    intro a idx ha hidx
    obtain ⟨hp, hij, hjp, hra⟩ := rec_props (by omega) hidx
    simp only [nodeAtN, nodeAt]
    have hplen := nodeAt_length d (by omega) (compAuto a (recOf d idx &&& 15)) (recOf d idx >>> 15) (compAuto_lt ha hra) hp
    have hi' : ((recOf d idx >>> 11) &&& 15) < (nodeAt d (compAuto a (recOf d idx &&& 15)) (recOf d idx >>> 15)).length := by omega
    have hj' : ((recOf d idx >>> 7) &&& 15) < (nodeAt d (compAuto a (recOf d idx &&& 15)) (recOf d idx >>> 15)).length := by omega
    rw [ih (by omega) _ _ (compAuto_lt ha hra) hp, childFromN_map _ hi' hj']

def memNP (w : NPair) : List NPair → Bool
  | [] => false
  | x :: xs => (x.1 == w.1 && x.2 == w.2) || memNP w xs

def sameNP (xs ys : List NPair) : Bool :=
  xs.length == ys.length && xs.all (fun x => memNP x ys)

theorem memNP_map (w : Word) (ws : List Word) :
    memNP (toNP w) (ws.map toNP) = ws.contains w := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, memNP, List.contains_cons, ih]
    congr 1
    by_cases h : x = w
    · subst h; simp
    · have h1 : (w == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      have h2 : ((toNP x).1 == (toNP w).1 && (toNP x).2 == (toNP w).2) = false := by
        rw [Bool.eq_false_iff]; intro he
        simp only [Bool.and_eq_true, beq_iff_eq] at he
        exact h (toNP_inj (Prod.ext he.1 he.2))
      rw [h1, h2]

theorem sameNP_map (xs ys : List Word) :
    sameNP (xs.map toNP) (ys.map toNP) = sameWordSet xs ys := by
  simp only [sameNP, sameWordSet, List.length_map, List.all_map]
  have hfun : (fun x => memNP (toNP x) (ys.map toNP)) = (fun x => ys.contains x) :=
    funext (fun x => memNP_map x ys)
  simp only [Function.comp_def, hfun]

def addSuffNP : List NPair → List (NPair × Nat × Nat)
  | [] => []
  | w :: ws =>
    let d := w.1 ^^^ w.2
    match addSuffNP ws with
    | [] => [(w, d, 0)]
    | (w2, d2, s2) :: rest => (w, d, d2 ||| s2) :: (w2, d2, s2) :: rest

theorem addSuffNP_map (ws : List Word) :
    addSuffNP (ws.map toNP) = (addSuff ws).map (fun p => (toNP p.1, p.2.1, p.2.2)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, addSuffNP, addSuff]
    rw [ih]
    cases addSuff ws with
    | nil => rfl
    | cons p rest =>
      rcases p with ⟨w2, d2, s2⟩
      rfl

def chkCaseN (ws : List NPair) (i j maxLen N : Nat) (childAt : Nat → Nat → List NPair)
    (getHint : Nat → Nat) (w : NPair) (ka kb : Bool) (clen cov pos : Nat) : Option Nat :=
  if clen > maxLen || cov != allN then some pos
  else
    let h := getHint pos
    let a := h &&& 15
    let cid := h >>> 4
    if a < 12 && cid < N && sameNP (w :: keepGoN 0 i j ka kb ws) (childAt a cid) then some (pos + 1)
    else none

def goOpN (ws : List NPair) (i j n maxLen N : Nat) (childAt : Nat → Nat → List NPair)
    (getHint : Nat → Nat) (wa wb : NPair) (da db cr : Nat) (op : Bool) (pos : Nat) : Option Nat :=
  let w := mixN op wa wb
  if memNP w ws then some pos
  else
    let dw := w.1 ^^^ w.2
    match chkCaseN ws i j maxLen N childAt getHint w false false (n - 1) (cr ||| dw) pos with
    | none => none
    | some p1 => match chkCaseN ws i j maxLen N childAt getHint w false true n ((cr ||| db) ||| dw) p1 with
      | none => none
      | some p2 => match chkCaseN ws i j maxLen N childAt getHint w true false n ((cr ||| da) ||| dw) p2 with
        | none => none
        | some p3 => chkCaseN ws i j maxLen N childAt getHint w true true (n + 1) (((cr ||| da) ||| db) ||| dw) p3

def goJN (ws : List NPair) (i n maxLen N : Nat) (childAt : Nat → Nat → List NPair)
    (getHint : Nat → Nat) (wa : NPair) (da : Nat) (j prefJ pos : Nat) :
    List (NPair × Nat × Nat) → Option Nat
  | [] => some pos
  | (wb, db, suffJ) :: bs =>
    let cr := prefJ ||| suffJ
    match goOpN ws i j n maxLen N childAt getHint wa wb da db cr false pos with
    | none => none
    | some p1 => match goOpN ws i j n maxLen N childAt getHint wa wb da db cr true p1 with
      | none => none
      | some p2 => goJN ws i n maxLen N childAt getHint wa da (j + 1) (prefJ ||| db) p2 bs

def goIN (ws : List NPair) (n maxLen N : Nat) (childAt : Nat → Nat → List NPair)
    (getHint : Nat → Nat) (i prefI pos : Nat) :
    List (NPair × Nat × Nat) → Option Nat
  | [] => some pos
  | (wa, da, _) :: rest =>
    match goJN ws i n maxLen N childAt getHint wa da (i + 1) prefI pos rest with
    | none => none
    | some p1 => goIN ws n maxLen N childAt getHint (i + 1) (prefI ||| da) p1 rest

def checkStepN (ws : List NPair) (maxLen N : Nat) (childAt : Nat → Nat → List NPair)
    (getHint : Nat → Nat) (pos0 : Nat) : Bool :=
  (goIN ws ws.length maxLen N childAt getHint 0 0 pos0 (addSuffNP ws)).isSome

theorem chkCaseN_eq {ws : List Word} {d : Nat} (hd : d < 3) {i j maxLen : Nat} {getHint : Nat → Nat}
    {w : Word} {ka kb : Bool} {clen cov pos : Nat} :
    chkCaseN (ws.map toNP) i j maxLen (cnt (d + 1)) (nodeAtN (d + 1)) getHint (toNP w) ka kb clen cov pos =
      chkCase ws i j maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint w ka kb clen cov pos := by
  unfold chkCaseN chkCase
  split_ifs with hskip
  · rfl
  · dsimp only
    by_cases hb : (getHint pos &&& 15) < 12 ∧ (getHint pos >>> 4) < cnt (d + 1)
    · have hnd := nodeAtN_eq (d + 1) (by omega) (getHint pos &&& 15) (getHint pos >>> 4) hb.1 hb.2
      have hsame : sameNP (toNP w :: keepGoN 0 i j ka kb (ws.map toNP)) (nodeAtN (d + 1) (getHint pos &&& 15) (getHint pos >>> 4)) =
          sameWordSet (childFromW ws i j ka kb w) (nodeAt (d + 1) (getHint pos &&& 15) (getHint pos >>> 4)) := by
        rw [keepGoN_map, hnd]
        exact sameNP_map (w :: keepGo 0 i j ka kb ws) _
      simp [hb.1, hb.2, hsame]
    · have hbf : (decide ((getHint pos &&& 15) < 12) && decide ((getHint pos >>> 4) < cnt (d + 1))) = false := by
        rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact hb h
      simp [hbf]

theorem goOpN_eq {ws : List Word} {d : Nat} (hd : d < 3) {i j n maxLen : Nat} {getHint : Nat → Nat}
    {wa wb : Word} {da db cr : Nat} {op : Bool} {pos : Nat} :
    goOpN (ws.map toNP) i j n maxLen (cnt (d + 1)) (nodeAtN (d + 1)) getHint (toNP wa) (toNP wb) da db cr op pos =
      goOp ws i j n maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint wa wb da db cr op pos := by
  unfold goOpN goOp
  dsimp only
  have hmix : mixN op (toNP wa) (toNP wb) = toNP (mix op wa wb) := (toNP_mix op wa wb).symm
  rw [hmix, memNP_map]
  have hdw : (toNP (mix op wa wb)).1 ^^^ (toNP (mix op wa wb)).2 = deltaN (mix op wa wb) := rfl
  rw [hdw]
  split_ifs
  · rfl
  · simp only [chkCaseN_eq hd]

theorem goJN_eq {ws : List Word} {d : Nat} (hd : d < 3) {i n maxLen : Nat} {getHint : Nat → Nat}
    {wa : Word} {da : Nat} :
    ∀ (bs : List (Word × Nat × Nat)) (j prefJ pos : Nat),
      goJN (ws.map toNP) i n maxLen (cnt (d + 1)) (nodeAtN (d + 1)) getHint (toNP wa) da j prefJ pos
          (bs.map (fun p => (toNP p.1, p.2.1, p.2.2))) =
        goJ ws i n maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint wa da j prefJ pos bs := by
  intro bs
  induction bs with
  | nil => intro j prefJ pos; rfl
  | cons p bs ih =>
    intro j prefJ pos
    rcases p with ⟨wb, db, suffJ⟩
    simp only [List.map_cons, goJN, goJ, goOpN_eq hd]
    cases h1 : goOp ws i j n maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint wa wb da db (prefJ ||| suffJ) false pos with
    | none => simp [h1]
    | some p1 =>
      simp only [h1]
      cases h2 : goOp ws i j n maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint wa wb da db (prefJ ||| suffJ) true p1 with
      | none => simp [h2]
      | some p2 => simp only [h2]; exact ih (j + 1) (prefJ ||| db) p2

theorem goIN_eq {ws : List Word} {d : Nat} (hd : d < 3) {n maxLen : Nat} {getHint : Nat → Nat} :
    ∀ (xs : List (Word × Nat × Nat)) (i prefI pos : Nat),
      goIN (ws.map toNP) n maxLen (cnt (d + 1)) (nodeAtN (d + 1)) getHint i prefI pos
          (xs.map (fun p => (toNP p.1, p.2.1, p.2.2))) =
        goI ws n maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint i prefI pos xs := by
  intro xs
  induction xs with
  | nil => intro i prefI pos; rfl
  | cons p rest ih =>
    intro i prefI pos
    rcases p with ⟨wa, da, sa⟩
    simp only [List.map_cons, goIN, goI, goJN_eq hd]
    cases h1 : goJ ws i n maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint wa da (i + 1) prefI pos rest with
    | none => simp [h1]
    | some p1 => simp only [h1]; exact ih (i + 1) (prefI ||| da) p1

theorem checkStepN_eq {ws : List Word} {d : Nat} (hd : d < 3) {maxLen : Nat} {getHint : Nat → Nat} {pos0 : Nat} :
    checkStepN (ws.map toNP) maxLen (cnt (d + 1)) (nodeAtN (d + 1)) getHint pos0 =
      checkStepF ws maxLen (cnt (d + 1)) (nodeAt (d + 1)) getHint pos0 := by
  simp only [checkStepN, checkStepF, List.length_map, addSuffNP_map, goIN_eq hd]

def addSuffI : List NItem → List (NPair × Nat × Nat)
  | [] => []
  | (w, d) :: ws =>
    match addSuffI ws with
    | [] => [(w, d, 0)]
    | (w2, d2, s2) :: rest => (w, d, d2 ||| s2) :: (w2, d2, s2) :: rest

theorem addSuffI_head : ∀ (ws : List NItem),
    match addSuffI ws with
    | [] => unionM ws = 0
    | (_, d, s) :: _ => d ||| s = unionM ws := by
  intro ws
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    rcases p with ⟨w, d⟩
    simp only [addSuffI, unionM]
    cases hs : addSuffI ws with
    | nil => rw [hs] at ih; simp [ih]
    | cons q rest =>
      rcases q with ⟨w2, d2, s2⟩
      rw [hs] at ih
      simp only [ih]

def inner1 (a : NPair) (prefB : Nat) : List (NPair × Nat × Nat) → Bool
  | [] => false
  | (b, db, suffB) :: bs =>
    let cr := prefB ||| suffB
    (((cr ||| ((a.1 &&& b.1) ^^^ (a.2 &&& b.2))) == allN) ||
     ((cr ||| ((a.1 ||| b.1) ^^^ (a.2 ||| b.2))) == allN)) ||
    inner1 a (prefB ||| db) bs

def outer1 (pref : Nat) : List (NPair × Nat × Nat) → Bool
  | [] => false
  | (a, da, _) :: rest =>
    inner1 a pref rest || outer1 (pref ||| da) rest

def innerTight (go : List NItem → Bool) (a : NPair) (allWs : List NItem) (prefB : Nat) : List (NPair × Nat × Nat) → Bool
  | [] => false
  | (b, db, suffB) :: bs =>
    let cr := prefB ||| suffB
    let chk (w1 w2 : Nat) : Bool :=
      let dw := w1 ^^^ w2
      if (cr ||| dw) == allN then
        if allWs.any (fun q => q.1.1 == w1 && q.1.2 == w2) then false
        else go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2) && !(q.1.1 == b.1 && q.1.2 == b.2)))
      else false
    chk (a.1 &&& b.1) (a.2 &&& b.2) || chk (a.1 ||| b.1) (a.2 ||| b.2) ||
      innerTight go a allWs (prefB ||| db) bs

def outerTight (go : List NItem → Bool) (allWs : List NItem) (pref : Nat) : List (NPair × Nat × Nat) → Bool
  | [] => false
  | (a, da, _) :: rest =>
    innerTight go a allWs pref rest || outerTight go allWs (pref ||| da) rest

def innerLoop2 (go : List NItem → Bool) (k n : Nat) (a : NPair) (da : Nat)
    (allWs : List NItem) (prefB : Nat) : List (NPair × Nat × Nat) → Bool
  | [] => false
  | (b, db, suffB) :: bs =>
    let cr := prefB ||| suffB
    let chkOp (w1 w2 : Nat) : Bool :=
      let dw := w1 ^^^ w2
      if (cr ||| dw) == allN then
        if allWs.any (fun q => q.1.1 == w1 && q.1.2 == w2) then false
        else if go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2) && !(q.1.1 == b.1 && q.1.2 == b.2))) then true
        else if n ≤ k + 6 &&
            ((((cr ||| da) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == b.1 && q.1.2 == b.2)))) ||
             (((cr ||| db) ||| dw) == allN && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2))))) then true
        else if n ≤ k + 5 && go (((w1, w2), dw) :: allWs) then true
        else false
      else if n ≤ k + 6 then
        let okB := ((cr ||| da) ||| dw) == allN
        let okA := ((cr ||| db) ||| dw) == allN
        if !okB && !okA && !(n ≤ k + 5) then false
        else if allWs.any (fun q => q.1.1 == w1 && q.1.2 == w2) then false
        else if (okB && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == b.1 && q.1.2 == b.2)))) ||
                (okA && go (((w1, w2), dw) :: allWs.filter (fun q => !(q.1.1 == a.1 && q.1.2 == a.2)))) then true
        else if n ≤ k + 5 && go (((w1, w2), dw) :: allWs) then true
        else false
      else false
    chkOp (a.1 &&& b.1) (a.2 &&& b.2) || chkOp (a.1 ||| b.1) (a.2 ||| b.2) ||
      innerLoop2 go k n a da allWs (prefB ||| db) bs

def outerLoop2 (go : List NItem → Bool) (k n : Nat) (allWs : List NItem) (pref : Nat) : List (NPair × Nat × Nat) → Bool
  | [] => false
  | (a, da, _) :: rest =>
    innerLoop2 go k n a da allWs pref rest || outerLoop2 go k n allWs (pref ||| da) rest

def searchL3 : Nat → List NItem → Bool
  | 0, xs => xs.length ≤ 6
  | 1, xs =>
    let n := xs.length
    if n ≤ 6 then true
    else if n > 7 then false
    else outer1 0 (addSuffI xs)
  | k + 1, xs =>
    let n := xs.length
    if n ≤ 6 then true
    else if n > k + 7 then false
    else if n == k + 7 then outerTight (searchL3 k) xs 0 (addSuffI xs)
    else outerLoop2 (searchL3 k) k n xs 0 (addSuffI xs)

theorem innerLoop2_imp {go1 go2 : List NItem → Bool} (hgo : ∀ xs, go1 xs = true → go2 xs = true)
    {k n : Nat} {a : NPair} {da : Nat} {allWs : List NItem} :
    ∀ (bs : List NItem) (prefB : Nat),
      innerLoop go1 k n a da allWs prefB bs = true →
      innerLoop2 go2 k n a da allWs prefB (addSuffI bs) = true := by
  have hchk {c0 cB cA fr g01 gB1 gA1 g1 g02 gB2 gA2 g2 : Bool}
      (h0 : g01 = true → g02 = true) (hB : gB1 = true → gB2 = true)
      (hA : gA1 = true → gA2 = true) (h3 : g1 = true → g2 = true) :
      (if c0 then
        if fr then false else if g01 then true
        else if n ≤ k + 6 && ((cB && gB1) || (cA && gA1)) then true
        else if n ≤ k + 5 && g1 then true else false
      else if n ≤ k + 6 then
        if !cB && !cA && !(n ≤ k + 5) then false else if fr then false
        else if (cB && gB1) || (cA && gA1) then true
        else if n ≤ k + 5 && g1 then true else false
      else false) = true →
      (if c0 then
        if fr then false else if g02 then true
        else if n ≤ k + 6 && ((cB && gB2) || (cA && gA2)) then true
        else if n ≤ k + 5 && g2 then true else false
      else if n ≤ k + 6 then
        if !cB && !cA && !(n ≤ k + 5) then false else if fr then false
        else if (cB && gB2) || (cA && gA2) then true
        else if n ≤ k + 5 && g2 then true else false
      else false) = true := by
    cases c0 <;> cases fr <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;>
      (try intro hx; cases hx) <;>
      split_ifs <;> simp_all <;> cases cB <;> cases cA <;> simp_all
  intro bs
  induction bs with
  | nil => intro _ h; cases h
  | cons p bs ih =>
    intro prefB h
    rcases p with ⟨b, db⟩
    have hhd := addSuffI_head bs
    unfold innerLoop at h
    dsimp only at h
    simp only [addSuffI]
    cases hs : addSuffI bs with
    | nil =>
      rw [hs] at hhd
      unfold innerLoop2
      dsimp only
      rw [hhd] at h
      rw [Bool.or_eq_true, Bool.or_eq_true] at h ⊢
      rcases h with (h1 | h2) | h3
      · left; left; exact hchk (hgo _) (hgo _) (hgo _) (hgo _) h1
      · left; right; exact hchk (hgo _) (hgo _) (hgo _) (hgo _) h2
      · right; exact hs ▸ ih (prefB ||| db) h3
    | cons q rest =>
      rcases q with ⟨w2, d2, s2⟩
      rw [hs] at hhd
      unfold innerLoop2
      dsimp only
      rw [← hhd] at h
      rw [Bool.or_eq_true, Bool.or_eq_true] at h ⊢
      rcases h with (h1 | h2) | h3
      · left; left; exact hchk (hgo _) (hgo _) (hgo _) (hgo _) h1
      · left; right; exact hchk (hgo _) (hgo _) (hgo _) (hgo _) h2
      · right; exact hs ▸ ih (prefB ||| db) h3

theorem outerLoop2_imp {go1 go2 : List NItem → Bool} (hgo : ∀ xs, go1 xs = true → go2 xs = true)
    {k n : Nat} {allWs : List NItem} :
    ∀ (xs : List NItem) (pref : Nat),
      outerLoop go1 k n allWs pref xs = true →
      outerLoop2 go2 k n allWs pref (addSuffI xs) = true := by
  intro xs
  induction xs with
  | nil => intro _ h; cases h
  | cons p rest ih =>
    intro pref h
    rcases p with ⟨a, da⟩
    simp only [outerLoop, Bool.or_eq_true] at h
    simp only [addSuffI]
    cases hs : addSuffI rest with
    | nil =>
      unfold outerLoop2; rw [Bool.or_eq_true]
      rcases h with h1 | h2
      · left; rw [← hs]; exact innerLoop2_imp hgo rest pref h1
      · right; rw [← hs]; exact ih (pref ||| da) h2
    | cons q r2 =>
      rcases q with ⟨w2, d2, s2⟩
      unfold outerLoop2; rw [Bool.or_eq_true]
      rcases h with h1 | h2
      · left; rw [← hs]; exact innerLoop2_imp hgo rest pref h1
      · right; rw [← hs]; exact ih (pref ||| da) h2

theorem innerTight_imp {go : List NItem → Bool} {k : Nat} {a : NPair} {da : Nat} {allWs : List NItem} :
    ∀ (sbs : List (NPair × Nat × Nat)) (prefB : Nat),
      innerLoop2 go k (k + 7) a da allWs prefB sbs = true →
      innerTight go a allWs prefB sbs = true := by
  have h6 : ¬(k + 7 ≤ k + 6) := by omega
  have h5 : ¬(k + 7 ≤ k + 5) := by omega
  intro sbs
  induction sbs with
  | nil => intro _ h; cases h
  | cons p bs ih =>
    intro prefB h
    rcases p with ⟨b, db, suffB⟩
    unfold innerLoop2 at h; unfold innerTight
    dsimp only at h ⊢
    simp only [h6, h5, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, Bool.or_eq_true] at h ⊢
    rcases h with (h1 | h2) | h3
    · left; left
      split_ifs at h1 ⊢ <;> simp_all
    · left; right
      split_ifs at h2 ⊢ <;> simp_all
    · right; exact ih (prefB ||| db) h3

theorem outerTight_imp {go : List NItem → Bool} {k : Nat} {allWs : List NItem} :
    ∀ (sxs : List (NPair × Nat × Nat)) (pref : Nat),
      outerLoop2 go k (k + 7) allWs pref sxs = true →
      outerTight go allWs pref sxs = true := by
  intro sxs
  induction sxs with
  | nil => intro _ h; cases h
  | cons p rest ih =>
    intro pref h
    rcases p with ⟨a, da, sa⟩
    simp only [outerLoop2, outerTight, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · left; exact innerTight_imp rest pref h1
    · right; exact ih (pref ||| da) h2

theorem inner1_of_tight {go : List NItem → Bool} {a : NPair} {allWs : List NItem} :
    ∀ (sbs : List (NPair × Nat × Nat)) (prefB : Nat),
      innerTight go a allWs prefB sbs = true →
      inner1 a prefB sbs = true := by
  intro sbs
  induction sbs with
  | nil => intro _ h; cases h
  | cons p bs ih =>
    intro prefB h
    rcases p with ⟨b, db, suffB⟩
    unfold innerTight at h; unfold inner1; dsimp only at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with (h1 | h2) | h3
    · left; left
      by_cases hc : ((prefB ||| suffB) ||| ((a.1 &&& b.1) ^^^ (a.2 &&& b.2)) == allN) = true
      · exact hc
      · rw [if_neg hc] at h1; cases h1
    · left; right
      by_cases hc : ((prefB ||| suffB) ||| ((a.1 ||| b.1) ^^^ (a.2 ||| b.2)) == allN) = true
      · exact hc
      · rw [if_neg hc] at h2; cases h2
    · right; exact ih (prefB ||| db) h3

theorem outer1_of_tight {go : List NItem → Bool} {allWs : List NItem} :
    ∀ (sxs : List (NPair × Nat × Nat)) (pref : Nat),
      outerTight go allWs pref sxs = true →
      outer1 pref sxs = true := by
  intro sxs
  induction sxs with
  | nil => intro _ h; cases h
  | cons p rest ih =>
    intro pref h
    rcases p with ⟨a, da, sa⟩
    simp only [outerTight, outer1, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · left; exact inner1_of_tight rest pref h1
    · right; exact ih (pref ||| da) h2

theorem searchL3_of_searchL (fuel : Nat) :
    ∀ xs, searchL fuel xs = true → searchL3 fuel xs = true := by
  induction fuel with
  | zero => intro xs h; exact h
  | succ k ih =>
    intro xs h
    cases k with
    | zero =>
      change searchL3 1 xs = true
      simp only [searchL] at h
      simp only [searchL3]
      by_cases h6 : xs.length ≤ 6
      · simp [h6]
      · simp only [h6, ite_false] at h ⊢
        by_cases h7 : xs.length > 7
        · simp [h7] at h
        · simp only [h7, ite_false] at h ⊢
          have hlen : xs.length = 7 := by omega
          rw [hlen] at h
          exact outer1_of_tight (addSuffI xs) 0 (outerTight_imp (addSuffI xs) 0 (outerLoop2_imp (fun _ hx => hx) xs 0 h))
    | succ k =>
      simp only [searchL, searchL3] at h ⊢
      by_cases h6 : xs.length ≤ 6
      · simp [h6]
      · simp only [h6, ite_false] at h ⊢
        by_cases h7 : xs.length > k + 1 + 7
        · simp [h7] at h
        · simp only [h7, ite_false] at h ⊢
          by_cases h8 : (xs.length == k + 1 + 7) = true
          · rw [if_pos h8]
            have hlen : xs.length = k + 1 + 7 := beq_iff_eq.mp h8
            rw [hlen] at h
            exact outerTight_imp (addSuffI xs) 0 (outerLoop2_imp ih xs 0 h)
          · rw [if_neg h8]
            exact outerLoop2_imp ih xs 0 h


def checkK4Range (s len : Nat) : Bool :=
  (List.range len).all fun d =>
    let ws := nodeAtN 3 0 (s + d)
    decide ws.Nodup && !searchL3 4 (ws.map fun w => (w, w.1 ^^^ w.2))

def checkK5Range (s len : Nat) : Bool :=
  (List.range len).all fun d =>
    let p := s + d
    let ws := nodeAtN 2 0 p
    decide ws.Nodup && decide (7 ≤ ws.length) && checkStepN ws 10 10100 (nodeAtN 3) hint5 (hoff5 p)

def checkK6Range (s len : Nat) : Bool :=
  (List.range len).all fun d =>
    let p := s + d
    let ws := nodeAtN 1 0 p
    decide ws.Nodup && decide (7 ≤ ws.length) && checkStepN ws 11 2501 (nodeAtN 2) hint6 (hoff6 p)

set_option maxHeartbeats 0 in
theorem k4_b0 : checkK4Range 0 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b1 : checkK4Range 100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b2 : checkK4Range 200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b3 : checkK4Range 300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b4 : checkK4Range 400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b5 : checkK4Range 500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b6 : checkK4Range 600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b7 : checkK4Range 700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b8 : checkK4Range 800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b9 : checkK4Range 900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b10 : checkK4Range 1000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b11 : checkK4Range 1100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b12 : checkK4Range 1200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b13 : checkK4Range 1300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b14 : checkK4Range 1400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b15 : checkK4Range 1500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b16 : checkK4Range 1600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b17 : checkK4Range 1700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b18 : checkK4Range 1800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b19 : checkK4Range 1900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b20 : checkK4Range 2000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b21 : checkK4Range 2100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b22 : checkK4Range 2200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b23 : checkK4Range 2300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b24 : checkK4Range 2400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b25 : checkK4Range 2500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b26 : checkK4Range 2600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b27 : checkK4Range 2700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b28 : checkK4Range 2800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b29 : checkK4Range 2900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b30 : checkK4Range 3000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b31 : checkK4Range 3100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b32 : checkK4Range 3200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b33 : checkK4Range 3300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b34 : checkK4Range 3400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b35 : checkK4Range 3500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b36 : checkK4Range 3600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b37 : checkK4Range 3700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b38 : checkK4Range 3800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b39 : checkK4Range 3900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b40 : checkK4Range 4000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b41 : checkK4Range 4100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b42 : checkK4Range 4200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b43 : checkK4Range 4300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b44 : checkK4Range 4400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b45 : checkK4Range 4500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b46 : checkK4Range 4600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b47 : checkK4Range 4700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b48 : checkK4Range 4800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b49 : checkK4Range 4900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b50 : checkK4Range 5000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b51 : checkK4Range 5100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b52 : checkK4Range 5200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b53 : checkK4Range 5300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b54 : checkK4Range 5400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b55 : checkK4Range 5500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b56 : checkK4Range 5600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b57 : checkK4Range 5700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b58 : checkK4Range 5800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b59 : checkK4Range 5900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b60 : checkK4Range 6000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b61 : checkK4Range 6100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b62 : checkK4Range 6200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b63 : checkK4Range 6300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b64 : checkK4Range 6400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b65 : checkK4Range 6500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b66 : checkK4Range 6600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b67 : checkK4Range 6700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b68 : checkK4Range 6800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b69 : checkK4Range 6900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b70 : checkK4Range 7000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b71 : checkK4Range 7100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b72 : checkK4Range 7200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b73 : checkK4Range 7300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b74 : checkK4Range 7400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b75 : checkK4Range 7500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b76 : checkK4Range 7600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b77 : checkK4Range 7700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b78 : checkK4Range 7800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b79 : checkK4Range 7900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b80 : checkK4Range 8000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b81 : checkK4Range 8100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b82 : checkK4Range 8200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b83 : checkK4Range 8300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b84 : checkK4Range 8400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b85 : checkK4Range 8500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b86 : checkK4Range 8600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b87 : checkK4Range 8700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b88 : checkK4Range 8800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b89 : checkK4Range 8900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b90 : checkK4Range 9000 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b91 : checkK4Range 9100 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b92 : checkK4Range 9200 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b93 : checkK4Range 9300 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b94 : checkK4Range 9400 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b95 : checkK4Range 9500 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b96 : checkK4Range 9600 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b97 : checkK4Range 9700 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b98 : checkK4Range 9800 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b99 : checkK4Range 9900 100 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k4_b100 : checkK4Range 10000 100 = true := by decide +kernel

theorem k4_imp (cid : Nat) (hcid : cid < cnt 3) : ¬ Can 4 (nodeAt 3 0 cid).toFinset := by
  have hq : cid / 100 < 101 := by simp only [cnt] at hcid; omega
  have hok : decide (nodeAtN 3 0 cid).Nodup && !searchL3 4 ((nodeAtN 3 0 cid).map fun w => (w, w.1 ^^^ w.2)) = true := by
    have hsplit : cid = 100 * (cid / 100) + cid % 100 := (Nat.div_add_mod cid 100).symm
    have hrun : ∀ s len d, d < len → checkK4Range s len = true →
        decide (nodeAtN 3 0 (s + d)).Nodup && !searchL3 4 ((nodeAtN 3 0 (s + d)).map fun w => (w, w.1 ^^^ w.2)) = true :=
      fun s len d hd hb => List.all_eq_true.mp hb d (List.mem_range.mpr hd)
    rw [hsplit]
    interval_cases hqv : cid / 100
    · exact hrun 0 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b0
    · exact hrun 100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b1
    · exact hrun 200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b2
    · exact hrun 300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b3
    · exact hrun 400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b4
    · exact hrun 500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b5
    · exact hrun 600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b6
    · exact hrun 700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b7
    · exact hrun 800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b8
    · exact hrun 900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b9
    · exact hrun 1000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b10
    · exact hrun 1100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b11
    · exact hrun 1200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b12
    · exact hrun 1300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b13
    · exact hrun 1400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b14
    · exact hrun 1500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b15
    · exact hrun 1600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b16
    · exact hrun 1700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b17
    · exact hrun 1800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b18
    · exact hrun 1900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b19
    · exact hrun 2000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b20
    · exact hrun 2100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b21
    · exact hrun 2200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b22
    · exact hrun 2300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b23
    · exact hrun 2400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b24
    · exact hrun 2500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b25
    · exact hrun 2600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b26
    · exact hrun 2700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b27
    · exact hrun 2800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b28
    · exact hrun 2900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b29
    · exact hrun 3000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b30
    · exact hrun 3100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b31
    · exact hrun 3200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b32
    · exact hrun 3300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b33
    · exact hrun 3400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b34
    · exact hrun 3500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b35
    · exact hrun 3600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b36
    · exact hrun 3700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b37
    · exact hrun 3800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b38
    · exact hrun 3900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b39
    · exact hrun 4000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b40
    · exact hrun 4100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b41
    · exact hrun 4200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b42
    · exact hrun 4300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b43
    · exact hrun 4400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b44
    · exact hrun 4500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b45
    · exact hrun 4600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b46
    · exact hrun 4700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b47
    · exact hrun 4800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b48
    · exact hrun 4900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b49
    · exact hrun 5000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b50
    · exact hrun 5100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b51
    · exact hrun 5200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b52
    · exact hrun 5300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b53
    · exact hrun 5400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b54
    · exact hrun 5500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b55
    · exact hrun 5600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b56
    · exact hrun 5700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b57
    · exact hrun 5800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b58
    · exact hrun 5900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b59
    · exact hrun 6000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b60
    · exact hrun 6100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b61
    · exact hrun 6200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b62
    · exact hrun 6300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b63
    · exact hrun 6400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b64
    · exact hrun 6500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b65
    · exact hrun 6600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b66
    · exact hrun 6700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b67
    · exact hrun 6800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b68
    · exact hrun 6900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b69
    · exact hrun 7000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b70
    · exact hrun 7100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b71
    · exact hrun 7200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b72
    · exact hrun 7300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b73
    · exact hrun 7400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b74
    · exact hrun 7500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b75
    · exact hrun 7600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b76
    · exact hrun 7700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b77
    · exact hrun 7800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b78
    · exact hrun 7900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b79
    · exact hrun 8000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b80
    · exact hrun 8100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b81
    · exact hrun 8200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b82
    · exact hrun 8300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b83
    · exact hrun 8400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b84
    · exact hrun 8500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b85
    · exact hrun 8600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b86
    · exact hrun 8700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b87
    · exact hrun 8800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b88
    · exact hrun 8900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b89
    · exact hrun 9000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b90
    · exact hrun 9100 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b91
    · exact hrun 9200 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b92
    · exact hrun 9300 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b93
    · exact hrun 9400 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b94
    · exact hrun 9500 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b95
    · exact hrun 9600 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b96
    · exact hrun 9700 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b97
    · exact hrun 9800 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b98
    · exact hrun 9900 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b99
    · exact hrun 10000 100 (cid % 100) (by simp only [cnt] at hcid; omega) k4_b100
  rw [nodeAtN_eq 3 (by decide) 0 cid (by decide) hcid] at hok
  have hndN : ((nodeAt 3 0 cid).map toNP).Nodup := of_decide_eq_true ((Bool.and_eq_true ..).mp hok).1
  have hnd : (nodeAt 3 0 cid).Nodup := (List.nodup_map_iff (fun _ _ => toNP_inj)).mp hndN
  have hmap : ((nodeAt 3 0 cid).map toNP).map (fun w => (w, w.1 ^^^ w.2)) = toNList (nodeAt 3 0 cid) := by
    rw [List.map_map]; rfl
  have hsf : searchL3 4 (toNList (nodeAt 3 0 cid)) = false := by
    have h2 := ((Bool.and_eq_true ..).mp hok).2
    rw [hmap] at h2
    cases h1 : searchL3 4 (toNList (nodeAt 3 0 cid)) <;> simp [h1] at h2 ⊢
  intro h
  have hs := searchL3_of_searchL 4 _ (searchL_sound 4 (nodeAt 3 0 cid) hnd (Nat.le_refl _) h)
  rw [hsf] at hs; cases hs

set_option maxHeartbeats 0 in
theorem k5_b0 : checkK5Range 0 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b1 : checkK5Range 50 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b2 : checkK5Range 100 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b3 : checkK5Range 150 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b4 : checkK5Range 200 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b5 : checkK5Range 250 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b6 : checkK5Range 300 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b7 : checkK5Range 350 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b8 : checkK5Range 400 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b9 : checkK5Range 450 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b10 : checkK5Range 500 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b11 : checkK5Range 550 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b12 : checkK5Range 600 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b13 : checkK5Range 650 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b14 : checkK5Range 700 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b15 : checkK5Range 750 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b16 : checkK5Range 800 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b17 : checkK5Range 850 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b18 : checkK5Range 900 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b19 : checkK5Range 950 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b20 : checkK5Range 1000 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b21 : checkK5Range 1050 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b22 : checkK5Range 1100 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b23 : checkK5Range 1150 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b24 : checkK5Range 1200 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b25 : checkK5Range 1250 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b26 : checkK5Range 1300 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b27 : checkK5Range 1350 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b28 : checkK5Range 1400 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b29 : checkK5Range 1450 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b30 : checkK5Range 1500 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b31 : checkK5Range 1550 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b32 : checkK5Range 1600 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b33 : checkK5Range 1650 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b34 : checkK5Range 1700 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b35 : checkK5Range 1750 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b36 : checkK5Range 1800 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b37 : checkK5Range 1850 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b38 : checkK5Range 1900 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b39 : checkK5Range 1950 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b40 : checkK5Range 2000 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b41 : checkK5Range 2050 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b42 : checkK5Range 2100 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b43 : checkK5Range 2150 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b44 : checkK5Range 2200 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b45 : checkK5Range 2250 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b46 : checkK5Range 2300 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b47 : checkK5Range 2350 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b48 : checkK5Range 2400 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b49 : checkK5Range 2450 50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k5_b50 : checkK5Range 2500 1 = true := by decide +kernel

theorem k5_imp (cid : Nat) (hcid : cid < cnt 2) : ¬ Can 5 (nodeAt 2 0 cid).toFinset := by
  have hq : cid / 50 < 51 := by simp only [cnt] at hcid; omega
  have hok : decide (nodeAtN 2 0 cid).Nodup && decide (7 ≤ (nodeAtN 2 0 cid).length) &&
      checkStepN (nodeAtN 2 0 cid) 10 10100 (nodeAtN 3) hint5 (hoff5 cid) = true := by
    have hsplit : cid = 50 * (cid / 50) + cid % 50 := (Nat.div_add_mod cid 50).symm
    have hrun : ∀ s len d, d < len → checkK5Range s len = true →
        decide (nodeAtN 2 0 (s + d)).Nodup && decide (7 ≤ (nodeAtN 2 0 (s + d)).length) &&
        checkStepN (nodeAtN 2 0 (s + d)) 10 10100 (nodeAtN 3) hint5 (hoff5 (s + d)) = true :=
      fun s len d hd hb => List.all_eq_true.mp hb d (List.mem_range.mpr hd)
    rw [hsplit]
    interval_cases hqv : cid / 50
    · exact hrun 0 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b0
    · exact hrun 50 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b1
    · exact hrun 100 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b2
    · exact hrun 150 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b3
    · exact hrun 200 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b4
    · exact hrun 250 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b5
    · exact hrun 300 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b6
    · exact hrun 350 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b7
    · exact hrun 400 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b8
    · exact hrun 450 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b9
    · exact hrun 500 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b10
    · exact hrun 550 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b11
    · exact hrun 600 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b12
    · exact hrun 650 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b13
    · exact hrun 700 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b14
    · exact hrun 750 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b15
    · exact hrun 800 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b16
    · exact hrun 850 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b17
    · exact hrun 900 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b18
    · exact hrun 950 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b19
    · exact hrun 1000 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b20
    · exact hrun 1050 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b21
    · exact hrun 1100 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b22
    · exact hrun 1150 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b23
    · exact hrun 1200 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b24
    · exact hrun 1250 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b25
    · exact hrun 1300 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b26
    · exact hrun 1350 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b27
    · exact hrun 1400 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b28
    · exact hrun 1450 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b29
    · exact hrun 1500 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b30
    · exact hrun 1550 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b31
    · exact hrun 1600 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b32
    · exact hrun 1650 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b33
    · exact hrun 1700 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b34
    · exact hrun 1750 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b35
    · exact hrun 1800 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b36
    · exact hrun 1850 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b37
    · exact hrun 1900 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b38
    · exact hrun 1950 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b39
    · exact hrun 2000 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b40
    · exact hrun 2050 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b41
    · exact hrun 2100 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b42
    · exact hrun 2150 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b43
    · exact hrun 2200 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b44
    · exact hrun 2250 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b45
    · exact hrun 2300 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b46
    · exact hrun 2350 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b47
    · exact hrun 2400 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b48
    · exact hrun 2450 50 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b49
    · exact hrun 2500 1 (cid % 50) (by simp only [cnt] at hcid; omega) k5_b50
  rw [nodeAtN_eq 2 (by decide) 0 cid (by decide) hcid] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_map] at hok
  have hnd : (nodeAt 2 0 cid).Nodup := (List.nodup_map_iff (fun _ _ => toNP_inj)).mp hok.1.1
  have hchk : checkStepF (nodeAt 2 0 cid) 10 (cnt 3) (nodeAt 3) hint5 (hoff5 cid) = true := by
    rw [← checkStepN_eq (d:=2) (by decide)]; exact hok.2
  exact checkStepF_sound hnd (k:=4) (d:=2) (by decide) hchk k4_imp hok.1.2

set_option maxHeartbeats 0 in
theorem k6_b0 : checkK6Range 0 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k6_b1 : checkK6Range 10 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k6_b2 : checkK6Range 20 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k6_b3 : checkK6Range 30 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k6_b4 : checkK6Range 40 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k6_b5 : checkK6Range 50 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k6_b6 : checkK6Range 60 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem k6_b7 : checkK6Range 70 8 = true := by decide +kernel

theorem k6_imp (cid : Nat) (hcid : cid < cnt 1) : ¬ Can 6 (nodeAt 1 0 cid).toFinset := by
  have hq : cid / 10 < 8 := by simp only [cnt] at hcid; omega
  have hok : decide (nodeAtN 1 0 cid).Nodup && decide (7 ≤ (nodeAtN 1 0 cid).length) &&
      checkStepN (nodeAtN 1 0 cid) 11 2501 (nodeAtN 2) hint6 (hoff6 cid) = true := by
    have hsplit : cid = 10 * (cid / 10) + cid % 10 := (Nat.div_add_mod cid 10).symm
    have hrun : ∀ s len d, d < len → checkK6Range s len = true →
        decide (nodeAtN 1 0 (s + d)).Nodup && decide (7 ≤ (nodeAtN 1 0 (s + d)).length) &&
        checkStepN (nodeAtN 1 0 (s + d)) 11 2501 (nodeAtN 2) hint6 (hoff6 (s + d)) = true :=
      fun s len d hd hb => List.all_eq_true.mp hb d (List.mem_range.mpr hd)
    rw [hsplit]
    interval_cases hqv : cid / 10
    · exact hrun 0 10 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b0
    · exact hrun 10 10 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b1
    · exact hrun 20 10 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b2
    · exact hrun 30 10 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b3
    · exact hrun 40 10 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b4
    · exact hrun 50 10 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b5
    · exact hrun 60 10 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b6
    · exact hrun 70 8 (cid % 10) (by simp only [cnt] at hcid; omega) k6_b7
  rw [nodeAtN_eq 1 (by decide) 0 cid (by decide) hcid] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_map] at hok
  have hnd : (nodeAt 1 0 cid).Nodup := (List.nodup_map_iff (fun _ _ => toNP_inj)).mp hok.1.1
  have hchk : checkStepF (nodeAt 1 0 cid) 11 (cnt 2) (nodeAt 2) hint6 (hoff6 cid) = true := by
    rw [← checkStepN_eq (d:=1) (by decide)]; exact hok.2
  exact checkStepF_sound hnd (k:=5) (d:=1) (by decide) hchk k5_imp hok.1.2

set_option maxHeartbeats 0 in
theorem k7_ok :
    (List.range 2).all (fun p =>
      let ws := nodeAtN 0 0 p
      decide ws.Nodup && decide (7 ≤ ws.length) && checkStepN ws 12 78 (nodeAtN 1) hint7 (hoff7 p)) = true := by
  decide +kernel

theorem noRoot (z : Bool) : ¬ Can 7 (starting z).toFinset := by
  let p := if z then 1 else 0
  have hp : p < 2 := by cases z <;> decide
  have heq : nodeAt 0 0 p = starting z := by
    simp only [nodeAt, p]
    have h1 := map_rotW_starting z (by decide : 0 < 12)
    have h2 : (starting z).map (rotW 0) = starting z := by
      have : rotW 0 = id := funext rotW_zero
      rw [this, List.map_id]
    cases z <;> simpa [h2] using h1.symm
  have hok := List.all_eq_true.mp k7_ok p (List.mem_range.mpr hp)
  rw [nodeAtN_eq 0 (by decide) 0 p (by decide) hp] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_map] at hok
  have hnd : (nodeAt 0 0 p).Nodup := (List.nodup_map_iff (fun _ _ => toNP_inj)).mp hok.1.1
  have hchk : checkStepF (nodeAt 0 0 p) 12 (cnt 1) (nodeAt 1) hint7 (hoff7 p) = true := by
    rw [← checkStepN_eq (d:=0) (by decide)]; exact hok.2
  rw [← heq]
  exact checkStepF_sound hnd (k:=6) (d:=0) (by decide) hchk k6_imp hok.1.2

theorem fromRoots' :
    ∀ ws ∈ (raw ++ [seed]).sublists, ws.Nodup →
      unionBits ws &&& mask = mask → ¬ Can 7 ws.toFinset := by
  intro ws hm _ hc
  have hp := List.all_eq_true.mp onlyRoots ws hm
  simp only [hc, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with rfl | rfl
  · exact noRoot false
  · exact noRoot true

theorem mainStep : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size = (8 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∀ (x6 : Finset ℕ), x6.card ≤ (6 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool) (x9 : Fin (9 : ℕ) → Bool), (∀ x10 ∈ x6, (x2.wires (List.ofFn x8)).getD x10 Bool.false = (x2.wires (List.ofFn x9)).getD x10 Bool.false) ∧ x1 x8 ≠ x1 x9 :=
  reduction fromRoots'

end PEqualNP.Outside.L_meta_3268

theorem PEqualNP.Outside.L_meta_3268 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size = (8 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∀ (x6 : Finset ℕ), x6.card ≤ (6 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool) (x9 : Fin (9 : ℕ) → Bool), (∀ x10 ∈ x6, (x2.wires (List.ofFn x8)).getD x10 Bool.false = (x2.wires (List.ofFn x9)).getD x10 Bool.false) ∧ x1 x8 ≠ x1 x9 :=
  PEqualNP.Outside.L_meta_3268.mainStep
