import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1620

-- A bit records the value on one of 58 assignments. The low 21 bits
-- are the edge assignments, and the upper 37 are maximal independent sets.
-- An index outside the 14 inputs is mapped to the last input.
def column (v : BitVec 4) : BitVec 58 :=
  if v = 0 then 95229015649943559 else
  if v = 1 then 63038587666488 else
  if v = 2 then 256462815680 else
  if v = 3 then 4292497062759936 else
  if v = 4 then 8521481482240 else
  if v = 5 then 14003410187812864 else
  if v = 6 then 55389823207997440 else
  if v = 7 then 189297016294081033 else
  if v = 8 then 155696362464477250 else
  if v = 9 then 218994303132270608 else
  if v = 10 then 183565875465490436 else
  if v = 11 then 229736628138025984 else
  if v = 12 then 270286071508633728 else
  288160007407550752

def gate (op : Bool) (x y : BitVec 58) : BitVec 58 :=
  if op then x &&& y else x ||| y

def pos (x : BitVec 58) : BitVec 21 := x.extractLsb' 0 21
def neg (x : BitVec 58) : BitVec 37 := x.extractLsb' 21 37
def pCount (x : BitVec 58) : BitVec 21 := (pos x).cpop
def nCount (x : BitVec 58) : BitVec 37 := (~~~neg x).cpop

def count {w : Nat} (x : BitVec w) : Nat := x.cpopNatRec w 0

lemma count_toNat {w : Nat} (x : BitVec w) : x.cpop.toNat = count x := by
  simp only [BitVec.cpop, BitVec.toNat_ofNat, count]
  apply Nat.mod_eq_of_lt
  have h : x.cpopNatRec w 0 ≤ w := by
    simpa using (BitVec.cpopNatRec_le (x := x) (acc := 0) w)
  exact lt_of_le_of_lt h Nat.lt_two_pow_self

lemma count_union_aux {w : Nat} (x y : BitVec w) (n : Nat) :
    (x ||| y).cpopNatRec n 0 + (x &&& y).cpopNatRec n 0 =
    x.cpopNatRec n 0 + y.cpopNatRec n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BitVec.cpopNatRec_succ, BitVec.getLsbD_or, BitVec.getLsbD_and]
    simp only [Nat.zero_add, BitVec.cpopNatRec_eq (acc := Bool.toNat _)]
    cases hx : x.getLsbD n <;> cases hy : y.getLsbD n <;> simp [hx, hy] <;> omega

lemma count_and_le_aux {w : Nat} (x y : BitVec w) (n : Nat) :
    (x &&& y).cpopNatRec n 0 ≤ x.cpopNatRec n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BitVec.cpopNatRec_succ, BitVec.getLsbD_and]
    simp only [Nat.zero_add, BitVec.cpopNatRec_eq (acc := Bool.toNat _)]
    cases hx : x.getLsbD n <;> cases hy : y.getLsbD n <;> simp [hx, hy] <;> omega

lemma count_or {w : Nat} (x y : BitVec w) : count (x ||| y) ≤ count x + count y := by
  have h := count_union_aux x y w
  unfold count
  omega

lemma count_and_left {w : Nat} (x y : BitVec w) : count (x &&& y) ≤ count x :=
  count_and_le_aux x y w

lemma count_and_right {w : Nat} (x y : BitVec w) : count (x &&& y) ≤ count y := by
  rw [BitVec.and_comm]
  exact count_and_left y x

lemma count_all (w : Nat) : count (BitVec.allOnes w) = w := by
  rw [← count_toNat, BitVec.cpop_allOnes]
  simp [Nat.mod_eq_of_lt Nat.lt_two_pow_self]

def good (x : BitVec 58) : Nat := count (pos x)
def bad (x : BitVec 58) : Nat := count (~~~neg x)

lemma good_and (x y : BitVec 58) :
    good (x &&& y) ≤ good x ∧ good (x &&& y) ≤ good y := by
  simpa only [good, pos, BitVec.extractLsb'_and] using
    And.intro (count_and_left (pos x) (pos y))
      (count_and_right (pos x) (pos y))

lemma good_or (x y : BitVec 58) :
    good (x ||| y) ≤ good x + good y := by
  simpa only [good, pos, BitVec.extractLsb'_or] using
    count_or (pos x) (pos y)

lemma bad_and (x y : BitVec 58) :
    bad (x &&& y) ≤ bad x + bad y := by
  simpa only [bad, neg, BitVec.extractLsb'_and, BitVec.not_and] using
    count_or (~~~neg x) (~~~neg y)

lemma bad_or (x y : BitVec 58) :
    bad (x ||| y) ≤ bad x ∧ bad (x ||| y) ≤ bad y := by
  simpa only [bad, neg, BitVec.extractLsb'_or, BitVec.not_or] using
    And.intro (count_and_left (~~~neg x) (~~~neg y))
      (count_and_right (~~~neg x) (~~~neg y))

lemma clean_or (x y : BitVec 58) (h : neg (x ||| y) = 0) :
    neg x = 0 ∧ neg y = 0 := by
  rw [neg, BitVec.extractLsb'_or] at h
  exact BitVec.or_eq_zero_iff.mp h

lemma full_and (x y : BitVec 58) (h : pos (x &&& y) = 2097151) :
    pos x = 2097151 ∧ pos y = 2097151 := by
  rw [pos, BitVec.extractLsb'_and] at h
  exact BitVec.and_eq_allOnes_iff.mp h

lemma clean_is_max_bad (x : BitVec 58) (h : neg x = 0) :
    bad x = 37 := by
  rw [bad, h]
  exact count_all 37

lemma full_is_max_good (x : BitVec 58) (h : pos x = 2097151) :
    good x = 21 := by
  rw [good, h]
  exact count_all 21

-- Depth-three counts impose bounds on either type of depth-four root gate.
def Bound3 (x : BitVec 58) : Prop :=
  (neg x = 0 → good x ≤ 5) ∧
  (pos x = 2097151 → bad x ≤ 9) ∧
  (11 ≤ good x → bad x ≤ 18)

def Bound4 (x : BitVec 58) : Prop :=
  (neg x = 0 → good x ≤ 10) ∧
  (pos x = 2097151 → bad x ≤ 18)

lemma and_step (x y : BitVec 58) (hx : Bound3 x) (hy : Bound3 y) :
    Bound4 (x &&& y) := by
  constructor
  · intro h
    by_contra! h'
    have ⟨hl, hr⟩ := good_and x y
    have hx' := hx.2.2 (by omega)
    have hy' := hy.2.2 (by omega)
    have hb := bad_and x y
    have ht := clean_is_max_bad _ h
    omega
  · intro h
    have ⟨hl, hr⟩ := full_and x y h
    have hx' := hx.2.1 hl
    have hy' := hy.2.1 hr
    have hb := bad_and x y
    omega

lemma or_step (x y : BitVec 58) (hx : Bound3 x) (hy : Bound3 y) :
    Bound4 (x ||| y) := by
  constructor
  · intro h
    have ⟨hl, hr⟩ := clean_or x y h
    have hx' := hx.1 hl
    have hy' := hy.1 hr
    have hg := good_or x y
    omega
  · intro h
    by_contra! h'
    have ⟨hl, hr⟩ := bad_or x y
    have hx' : good x ≤ 10 := by
      by_contra! hh
      have := hx.2.2 (by omega)
      omega
    have hy' : good y ≤ 10 := by
      by_contra! hh
      have := hy.2.2 (by omega)
      omega
    have hg := good_or x y
    have ht := full_is_max_good _ h
    omega

lemma no_and_root (x y : BitVec 58) (hx : Bound4 x) (hy : Bound4 y) :
    x &&& y ≠ 2097151 := by
  intro h
  have hp : pos (x &&& y) = 2097151 := by rw [h]; decide
  have hn : neg (x &&& y) = 0 := by rw [h]; decide
  have ⟨hl, hr⟩ := full_and x y hp
  have hx' := hx.2 hl
  have hy' := hy.2 hr
  have hb := bad_and x y
  have ht := clean_is_max_bad _ hn
  omega

lemma no_or_root (x y : BitVec 58) (hx : Bound4 x) (hy : Bound4 y) :
    x ||| y ≠ 2097151 := by
  intro h
  have hp : pos (x ||| y) = 2097151 := by rw [h]; decide
  have hn : neg (x ||| y) = 0 := by rw [h]; decide
  have ⟨hl, hr⟩ := clean_or x y hn
  have hx' := hx.1 hl
  have hy' := hy.1 hr
  have hg := good_or x y
  have ht := full_is_max_good _ hp
  omega


-- A shorter tree can be padded with conjunctions of identical children.
def feasible : Nat → BitVec 58 → Prop
  | 0, t => ∃ v : BitVec 4, t = column v
  | k + 1, t => ∃ (op : Bool) (a b : BitVec 58),
      feasible k a ∧ feasible k b ∧ t = gate op a b

def pairs : List (BitVec 58) := [
  95229015649943559, 63038587666488, 256462815680, 4292497062759936,
  8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
  155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
  270286071508633728, 288160007407550752, 95274182876594239, 17871361015808,
  95229233422401991, 38690357248, 63221765505528, 73284976640,
  98888193979452935, 633318733250560, 4355534297763384, 1352663040,
  4292751074004928, 2451570688, 95235063194611719, 2473936814080,
  70185669128248, 1374400020480, 8777837343168, 106954752,
  4301018365984256, 178257920, 104658453169143815, 4573972668612608,
  14066427290157112, 21485322240, 14003653759435200, 12891193344,
  17944063519198720, 351843731374080, 14011931637837824, 31457280,
  132533796724277255, 18085042133663744, 55443790554202168, 9071241461760,
  55390078859215296, 811597824, 58486051349204480, 1196268921552896,
  55397520049467392, 824640012288, 69182127156985856, 211106238824448,
  284526031944024591, 1, 189360054881747513, 8,
  189297126119834569, 146637062144, 193589513356840457, 512,
  189300589885157897, 4947890405376, 194152481127891465, 9147945354002432,
  208516754697880073, 36170084804198400, 250925378114420807, 2,
  155723098906427514, 36302145716224, 155696618927292866, 64,
  157455583520493122, 2533276006744064, 155699386228437058, 5497717522432,
  160411081215803458, 9288691436486656, 211086185672212546, 262144,
  191866593364673099, 153126785393885184, 241600541374316567, 72622777407897600,
  219057341719937080, 16, 218994385548247504, 174046838784,
  220472048112668176, 2814752082362368, 218996227309105168, 6597304647680,
  232997713320050704, 32768, 274384126339743760, 524288,
  264171595797922329, 144119723628429312, 228319279526477906, 146371386070269952,
  278794891115433991, 4, 183584863526391868, 44050526765056,
  183565922817085892, 209111220224, 184480669318061572, 3377703210188800,
  183574396946968580, 4096, 197569285653237764, 65536,
  201792204849352708, 37163493824135168, 192718768688927245, 180144123070644224,
  192860064594595910, 146402173335371776, 256193051121782804, 146367127475978240,
  248386819281921031, 76578824506048512, 229746799973246008, 52866752446464,
  229736631197771200, 253403070464, 234029125200784896, 1024,
  229745149619500032, 8192, 230229209378956288, 13510828946882560,
  285126451344974848, 1048576, 265911111072622089, 153122533359484928,
  232275401719948354, 153157588882554880, 232557977357820944, 216172953912475648,
  269151924997141508, 144150578606374912, 275423028523960455, 90092058634616832,
  270286163055610040, 62947040690176, 270286327971449280, 128,
  274578568571391616, 2048, 270286071775000704, 8521215115264,
  284289481696315520, 131072, 271623078461442176, 54052816255188992,
  279434154905569929, 180148932897144832, 281826563967027394, 144155870006083584,
  273100995457353872, 216179379183550464, 273663981414193284, 180187965559930880,
  283797140974742656, 216225558671917056, 288180112185114919, 95208910872379392,
  288223045995217208, 32, 288160263870366176, 256,
  288160011075473184, 4292493394837504, 288168528889016608, 16384,
  288160037504008480, 14003380091355136, 288169628947726624, 55380201667821568,
  288165101863715625, 189291921837916160, 288200707751035234, 155655662120992768,
  288166778658930992, 218987531880890368, 288204198057693476, 183521684815347712,
  288213054549681440, 229683580995895296, 288230101273954720, 270215977642229760]
def pairsAt (i : Fin 196) : BitVec 58 := pairs.getD i.val 0

def rareAnd : List (BitVec 58) := [
  157485068542312058, 160440562240450682, 162102957249658434, 162126665401994874,
  184499700389453820, 193511254686768766, 194156160203617225, 196443039968260683,
  201810961080586748, 202636677267398596, 202655343128157756, 208520162930619337,
  210803849512686541, 213301956045669321, 213305149488099849, 220474054420266960,
  229516373085978194, 230239383988708856, 232495579198366842, 241602268785865175,
  243007995458916311, 243009566896881175, 248396718992795135, 248809034796475847,
  248818928723403839, 250643020300985815, 256544907742257108, 264173043480851417,
  264489647800644187, 265341550528664541, 265553210816437846, 266262957253699529,
  268515855337760331, 268728062449330137, 269153299502020092, 269297610411554765,
  269439172571640958, 269721472262059476, 271623169989572792, 273875109138077884,
  275423115996199103, 276689666957015175, 276689753711970495, 277674968155355287,
  280630424005147273, 281826637356890362, 281967448128125643, 282248941358742169,
  282389687974164690, 282882295583414925, 282952677282224382, 284430461058559167,
  286330417269058810, 286682261871045783, 287174844732357820, 288169662426894112,
  288174194590466857, 288180141608390439, 288184651370516279, 288189462209122087,
  288189484640485671, 288200723091935074, 288201408441205611, 288203081092222834,
  288205022875705124, 288209429419873069, 288209712991002470, 288210829733125940,
  288215528516085031, 288218002987673385, 288218553347728738, 288219928882373943,
  288230140775647655, 288230248200162217, 288230279752632759, 288230311467112868,
  288230371893603751]
def rareAndAt (i : Fin 77) : BitVec 58 := rareAnd.getD i.val 0

def rareOr : List (BitVec 58) := [
  70368742109688, 4301272305926080, 4355715294564344, 4362681211452984,
  14012175108796864, 14066601873867256, 14073574350647352, 17944304641347520,
  17952584801451520, 18007079279365688, 55397775600021952, 55443973190975992,
  55450387875655736, 58486304819384256, 58493748014513664, 58540017613278776,
  69182369923301824, 69189823973289984, 69236073019965496, 71996880313093632,
  95235280895766983, 95274331661140479, 95279130901246015, 98888409335992263,
  98894241381514759, 98933359855537727, 104658662347473351, 104664500684451847,
  104703603207536703, 108036156513553927, 132534013687235015, 132539294508937223,
  132570167589470271, 135067074878508551, 141822496750927879, 155725847790383226,
  157458607248801346, 157482319691910778, 160414104973471810, 160437813360689274,
  162099933525544514, 183584906580922876, 184480716634005444, 184499657368477244,
  189300699675259849, 191869067301515851, 192718807379284941, 192877935955611774,
  193001360500003407, 193493383327850054, 193511254686768766, 194152586656580553,
  194156054708482569, 196440566033515083, 196443039968260683, 201792252194656708,
  201810918030250044, 202636629955649028, 208516864253101001, 208520053408952841,
  210803810824425997, 210803849512686541, 213301850785415689, 218996309718790608,
  220472130258112464, 220473972279016976, 228320104166518866, 229515548448034386,
  229516373085978194, 229746802762458616, 230229212432410048, 230239381203690552,
  232284472961410170, 232486507959002178, 232495579198366842, 232557978169419216,
  232840552945329234, 241600619493229015, 241602190671147031, 243007917608439319,
  248386822306014663, 248396716237136959, 248809031776576519, 250643019491484695,
  250643020300985815, 256193064012976596, 256544894853160468, 256544907742257108,
  264171669082899417, 264172970197971481, 264173043480851417, 264489372920611419,
  265341546231599645, 265482842070159446, 265911113524193225, 266262954804225545,
  266262957253699529, 268445486591256139, 268728062178797081, 269151925104096708,
  269153299397162044, 269153299502020092, 269297610375902733, 269438897691636806,
  269721472255767572, 270286163311491256, 271623078721517696, 271623169737885880,
  273100995488839824, 273664002899515580, 273875087654852740, 273875109138077884,
  274226965962791060, 275423028754675847, 275423115773872319, 276689666730494087,
  277674968125966487, 277674968155355287, 279434155083856521, 280630423828957833,
  280630424005147273, 281826564074010818, 281826637252004090, 281826637356890362,
  281967448092445387, 282248941348227737, 282389687967844562, 282811926835305101,
  282952672985159878, 283797142327405752, 283937879088049801, 284430459707993223,
  284430461058559167, 286330416998526146, 286611893124770960, 287174844721872004,
  288160041161445152, 288165123349267241, 288166780011597616, 288167337562522425,
  288169632345116448, 288169659037892896, 288174173107012393, 288174194590466857,
  288180115817385767, 288180137984508199, 288184650019946807, 288184651370516279,
  288189458845286695, 288200710202609506, 288200720642457954, 288200723091935074,
  288201404143911787, 288203080821686642, 288204198235954980, 288205022699540772,
  288205022875705124, 288209154538033965, 288209712955347302, 288210829722636596,
  288213054581368096, 288215528486495527, 288215528516085031, 288218002976958249,
  288218553341207906, 288219654002369840, 288221854669305124, 288230102087387552,
  288230119687211490, 288230139964311975, 288230140775647655, 288230247927794601,
  288230275455568304, 288230311458986404, 288230371857952160]
def rareOrAt (i : Fin 175) : BitVec 58 := rareOr.getD i.val 0

def pairIndex (a b : BitVec 4) (op : Bool) : Fin 196 :=
  let a := min a.toNat 13
  let b := min b.toNat 13
  let i := min a b
  let j := max a b
  let k := if i = j then i else 14 + (j * (j - 1) / 2 + i) * 2 + op.toNat
  ⟨k % 196, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma pairIndex_ok :
    ∀ a b : Fin 16, ∀ op : Bool,
      gate op (column ⟨a⟩) (column ⟨b⟩) = pairsAt (pairIndex ⟨a⟩ ⟨b⟩ op) := by
  decide +kernel

lemma depthOne_in (t : BitVec 58) (ht : feasible 1 t) :
    ∃ i : Fin 196, t = pairsAt i := by
  rcases ht with ⟨op, _, _, ⟨⟨a⟩, rfl⟩, ⟨⟨b⟩, rfl⟩, rfl⟩
  exact ⟨_, pairIndex_ok a b op⟩

def Bound2 (t : BitVec 58) : Prop :=
  (neg t = 0 → good t ≤ 2) ∧
  (6 ≤ good t → bad t ≤ 18) ∧ good t ≤ 12 ∧
  (11 ≤ good t → bad t ≤ 10) ∧
  (11 ≤ good t → 9 ≤ bad t → ∃ i : Fin 77, t = rareAndAt i) ∧
  (9 ≤ good t → 10 ≤ bad t → ∃ i : Fin 175, t = rareOrAt i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma bounds_table (i : Fin 196) :
    ∀ j : Fin 196, ∀ op : Bool,
      (let t := gate op (pairsAt i) (pairsAt j)
       (neg t = 0 → good t ≤ 2) ∧
       (6 ≤ good t → bad t ≤ 18) ∧ good t ≤ 12 ∧
       (11 ≤ good t → bad t ≤ 10) ∧
       (11 ≤ good t → 9 ≤ bad t → ∃ a : Fin 77, t = rareAndAt a) ∧
       (9 ≤ good t → 10 ≤ bad t → ∃ b : Fin 175, t = rareOrAt b)) := by
  fin_cases i <;> decide +kernel

lemma depthTwo_bound (t : BitVec 58) (ht : feasible 2 t) : Bound2 t := by
  rcases ht with ⟨op, a, b, ha, hb, rfl⟩
  obtain ⟨i, rfl⟩ := depthOne_in a ha
  obtain ⟨j, rfl⟩ := depthOne_in b hb
  exact bounds_table i j op

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma and_exceptions (i : Fin 77) :
    ∀ j : Fin 77, 11 ≤ good (rareAndAt i &&& rareAndAt j) →
      bad (rareAndAt i &&& rareAndAt j) ≤ 18 := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma or_exceptions (i : Fin 175) :
    ∀ j : Fin 175, pos (rareOrAt i ||| rareOrAt j) = 2097151 →
      bad (rareOrAt i ||| rareOrAt j) ≤ 9 := by
  fin_cases i <;> decide +kernel

lemma depthThree_and (a b : BitVec 58) (ha : Bound2 a) (hb : Bound2 b) :
    Bound3 (a &&& b) := by
  obtain ⟨_, ha6, ha12, ha10, hae, _⟩ := ha
  obtain ⟨_, hb6, hb12, hb10, hbe, _⟩ := hb
  have ⟨hpa, hpb⟩ := good_and a b
  have hq := bad_and a b
  refine ⟨?_, ?_, ?_⟩
  · intro h
    by_contra! hl
    have ha' := ha6 (by omega)
    have hb' := hb6 (by omega)
    have hneg := clean_is_max_bad _ h
    omega
  · intro h
    have hpos := full_is_max_good _ h
    omega
  · intro h
    by_contra! hl
    have ha' := ha10 (by omega)
    have hb' := hb10 (by omega)
    obtain ⟨i, rfl⟩ := hae (by omega) (by omega)
    obtain ⟨j, rfl⟩ := hbe (by omega) (by omega)
    have := and_exceptions i j h
    omega

lemma depthThree_or (a b : BitVec 58) (ha : Bound2 a) (hb : Bound2 b) :
    Bound3 (a ||| b) := by
  obtain ⟨ha2, ha6, ha12, _, _, hae⟩ := ha
  obtain ⟨hb2, hb6, hb12, _, _, hbe⟩ := hb
  have ⟨hqa, hqb⟩ := bad_or a b
  have hp := good_or a b
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨hna, hnb⟩ := clean_or a b h
    have := ha2 hna
    have := hb2 hnb
    omega
  · intro h
    by_contra! hl
    have hpos := full_is_max_good _ h
    obtain ⟨i, rfl⟩ := hae (by omega) (by omega)
    obtain ⟨j, rfl⟩ := hbe (by omega) (by omega)
    have := or_exceptions i j h
    omega
  · intro h
    by_contra! hl
    have hp' : good a ≤ 5 := by
      by_contra! hh
      have := ha6 hh
      omega
    have hq' : good b ≤ 5 := by
      by_contra! hh
      have := hb6 hh
      omega
    omega

lemma depthThree_bound (t : BitVec 58) (ht : feasible 3 t) : Bound3 t := by
  rcases ht with ⟨op, a, b, ha, hb, rfl⟩
  cases op
  · exact depthThree_or a b (depthTwo_bound a ha) (depthTwo_bound b hb)
  · exact depthThree_and a b (depthTwo_bound a ha) (depthTwo_bound b hb)

lemma depthFour_bound (t : BitVec 58) (ht : feasible 4 t) : Bound4 t := by
  rcases ht with ⟨op, a, b, ha, hb, rfl⟩
  cases op
  · exact or_step a b (depthThree_bound a ha) (depthThree_bound b hb)
  · exact and_step a b (depthThree_bound a ha) (depthThree_bound b hb)

lemma depthFive_excludes_target : ¬ feasible 5 2097151 := by
  rintro ⟨op, a, b, ha, hb, h⟩
  cases op
  · exact no_or_root a b (depthFour_bound a ha) (depthFour_bound b hb) h.symm
  · exact no_and_root a b (depthFour_bound a ha) (depthFour_bound b hb) h.symm

def sample (j : Fin 58) (i : Fin 14) : Bool :=
  (column (BitVec.ofNat 4 i.val)).getLsbD j.val

def profile (f : (Fin 14 → Bool) → Bool) : BitVec 58 :=
  (BitVec.ofBoolListLE (List.ofFn fun j : Fin 58 => f (sample j))).cast (by simp)

lemma profile_bit (f : (Fin 14 → Bool) → Bool) (j : Nat) :
    (profile f).getLsbD j =
      if h : j < 58 then f (sample ⟨j, h⟩) else false := by
  simp only [profile, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp_all

lemma profile_variable (i : Fin 14) :
    profile (fun x => x i) = column (BitVec.ofNat 4 i.val) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [profile_bit, dite_eq_left hj]
  rfl

lemma profile_and (f g : (Fin 14 → Bool) → Bool) :
    profile (fun x => f x && g x) = profile f &&& profile g := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, profile_bit, dite_eq_left hj]

lemma profile_or (f g : (Fin 14 → Bool) → Bool) :
    profile (fun x => f x || g x) = profile f ||| profile g := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, profile_bit, dite_eq_left hj]

def level (k : Nat) : Set ((Fin 14 → Bool) → Bool) :=
  { f | feasible k (profile f) }

lemma level_variable (i : Fin 14) : (fun x : Fin 14 → Bool => x i) ∈ level 0 := by
  exact ⟨BitVec.ofNat 4 i.val, profile_variable i⟩

lemma level_mono (k : Nat) (f : (Fin 14 → Bool) → Bool) (hf : f ∈ level k) :
    f ∈ level (k + 1) := by
  refine ⟨true, profile f, profile f, hf, hf, ?_⟩
  simp [gate]

lemma level_gates (k : Nat) (f g : (Fin 14 → Bool) → Bool)
    (hf : f ∈ level k) (hg : g ∈ level k) :
    (fun y => f y && g y) ∈ level (k + 1) ∧
    (fun y => f y || g y) ∈ level (k + 1) :=
  ⟨⟨true, profile f, profile g, hf, hg, profile_and f g⟩,
    ⟨false, profile f, profile g, hf, hg, profile_or f g⟩⟩

def target (z : Fin 14 → Bool) : Bool :=
  (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)

lemma target_profile : profile target = 2097151 := by
  decide +kernel

end PEqualNP.Outside.L_meta_1620

theorem PEqualNP.Outside.L_meta_1620 : ¬ (∀ T : ℕ → Set ((Fin 14 → Bool) → Bool), (∀ i : Fin 14, (fun x : Fin 14 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 14 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 14 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 14 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 14 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 14 → Bool => (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)) ∈ T 5) := by
  intro h
  open PEqualNP.Outside.L_meta_1620 in
  have ht : target ∈ level 5 := h level level_variable level_mono level_gates
  open PEqualNP.Outside.L_meta_1620 in
  change feasible 5 (profile target) at ht
  open PEqualNP.Outside.L_meta_1620 in
  rw [target_profile] at ht
  exact PEqualNP.Outside.L_meta_1620.depthFive_excludes_target ht
