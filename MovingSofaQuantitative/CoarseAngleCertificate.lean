module

public import MovingSofaQuantitative.MidpointEntry
public import MovingSofaStability.Global

/-!
# Exact coarse terminal-angle separation

UNCOMPILED SOURCE. The rational outer search and its acceptance predicate
are defined in Lean, with no external script, generated acceptance file, or
foreign solver in the proof path. The intended theorem is the coarse entry
fact used by the effective
angle argument:

  deficit < 1/5000  ->  tan(omega/2) > 4/5.

The search is over rational outer envelopes.  Every branching and clipping
predicate is exact; there is no floating acceptance test.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative
namespace CoarseAngleCertificate

abbrev Q := ℚ
abbrev QPoint := Q×Q
abbrev Polygon := List QPoint
abbrev Box := List (Q×Q)

def dotQ (p n : QPoint) : Q := p.1*n.1+p.2*n.2
def crossQ (p q : QPoint) : Q := p.1*q.2-p.2*q.1

def normal (r : Q) : QPoint :=
  ((1-r^2)/(1+r^2),2*r/(1+r^2))

def segmentIntersect (a b n : QPoint) (h : Q) : QPoint :=
  let da:=dotQ a n-h
  let db:=dotQ b n-h
  let λ:=da/(da-db)
  (a.1+λ*(b.1-a.1),a.2+λ*(b.2-a.2))

def clip (P : Polygon) (n : QPoint) (h : Q) : Polygon :=
  (P.zip (P.tail++P.take 1)).foldl (fun out e =>
    let ina : Bool := decide (dotQ e.1 n≤h)
    let inb : Bool := decide (dotQ e.2 n≤h)
    if ina && inb then out++[e.2]
    else if ina && !inb then out++[segmentIntersect e.1 e.2 n h]
    else if !ina && inb then out++[segmentIntersect e.1 e.2 n h,e.2]
    else out) []

def twiceArea (P : Polygon) : Q :=
  |(P.zip (P.tail++P.take 1)).foldl
    (fun s e => s+crossQ e.1 e.2) 0|

def area (P : Polygon) : Q := twiceArea P/2

def clipLower (P : Polygon) (n : QPoint) (h : Q) : Polygon :=
  clip P (-n.1,-n.2) (-h)

def hallway (Ps : List Polygon) (n : QPoint) (lo hi vlo vhi : Q) : List Polygon :=
  (Ps.flatMap fun P =>
    let P:=clip (clipLower P n lo) n hi
    let v:=(-n.2,n.1)
    let A:=clip (clipLower P v vlo) v vhi
    if area A=0 then [] else [A]).filter (fun P=>0<area P)

def baseButterfly (lo hi : Q) : List Polygon :=
  let na:=normal lo
  let nb:=normal hi
  let xmin:=-nb.2/nb.1
  let xmax:=1/nb.1
  let R : Polygon := [(xmin,0),(xmax,0),(xmax,1),(xmin,1)]
  let R:=clipLower R nb 0
  let A:=clip R na 1
  let B:=clip (clip R nb 1) (-na.1,-na.2) (-1)
  [A,B].filter (fun P=>0<area P)

def interTangents : List Q := [1/10,1/4,2/5,3/5]

def dyadicDown (bits : Nat) (x : Q) : Q :=
  (Int.floor (x*(2^bits)))/(2^bits)
def dyadicUp (bits : Nat) (x : Q) : Q := -dyadicDown bits (-x)

def supportRange (Ps : List Polygon) (n : QPoint) : Q×Q :=
  let xs:=(Ps.flatMap id).map (fun p=>dotQ p n)
  (xs.foldl min xs.head!,xs.foldl max xs.head!)

def rootBox (lo hi : Q) : Box :=
  let Ps:=baseButterfly lo hi
  interTangents.flatMap fun r =>
    let n:=normal r
    let v:=(-n.2,n.1)
    let a:=supportRange Ps n
    let b:=supportRange Ps v
    [(dyadicDown 32 a.1,dyadicUp 32 a.2),
     (dyadicDown 32 b.1,dyadicUp 32 b.2)]

/-- There are exactly eight support coordinates: two for each of the
four intermediate normals. This guards the native search's indexing scheme,
which must use stride two, not stride four. -/
theorem rootBox_length (lo hi : Q) : (rootBox lo hi).length = 8 := by
  simp [rootBox, interTangents]

theorem paired_coordinate_indices (i : Fin 4) :
    2 * i.val < 8 ∧ 2 * i.val + 1 < 8 := by
  omega

def polygons (lo hi : Q) (box : Box) : List Polygon :=
  (interTangents.zipIdx.foldl (fun Ps rn =>
    let n:=normal rn.1
    -- Each intermediate normal contributes two coordinates: normal and tangent.
    let j:=2*rn.2
    hallway Ps n
      (box[j]!).1 (box[j]!).2 (box[j+1]!).1 (box[j+1]!).2)
    (baseButterfly lo hi))

def bound (lo hi : Q) (box : Box) : Q :=
  (polygons lo hi box).foldl (fun s P=>s+area P) 0

/-- Safe lower support contraction: if the portion below h has area below the
target, an actual subset of target area cannot have support <=h. -/
def contractCoordinate (lo hi : Q) (target : Q)
    (box : Box) (j : Nat) : Option Box :=
  let Ps:=polygons lo hi box
  if (Ps.foldl (fun s P=>s+area P) 0)<target then none
  else
    let n0:=normal (interTangents[j/2]!)
    let n:=if j%2=0 then n0 else (-n0.2,n0.1)
    let a:=box[j]!
    let hi':=min a.2 (dyadicUp 32
      ((Ps.flatMap id).map (fun p=>dotQ p n) |>.foldl max a.1))
    let mid:=(a.1+hi')/2
    let lowArea:=Ps.foldl (fun s P=>s+area (clip P n mid)) 0
    let lo':=if lowArea<target then max a.1 (dyadicDown 32 mid) else a.1
    if hi'<lo' then none else some (box.set j (lo',hi'))

def contractPass (lo hi target : Q) (box : Box) : Option Box :=
  (List.range box.length).foldlM (contractCoordinate lo hi target) box

def contract (lo hi target : Q) (box : Box) : Option Box := do
  let b←contractPass lo hi target box
  let b←contractPass lo hi target b
  contractPass lo hi target b

def widestCoordinate (box : Box) : Nat :=
  (List.range box.length).foldl
    (fun j k=>if box[j]!.2-box[j]!.1<box[k]!.2-box[k]!.1 then k else j) 0

def split (box : Box) : Box×Box :=
  let j:=widestCoordinate box
  let a:=box[j]!
  let m:=(a.1+a.2)/2
  (box.set j (a.1,m),box.set j (m,a.2))

inductive SearchTree
  | pruned
  | branch (j : Nat) (left right : SearchTree)
  deriving Decidable,Repr

def checkTree (lo hi target : Q) : Box→SearchTree→Bool
  | box,.pruned => bound lo hi box<target
  | box,.branch _ l r =>
      match contract lo hi target (split box).1,
            contract lo hi target (split box).2 with
      | none,none => true
      | some bl,none => checkTree lo hi target bl l
      | none,some br => checkTree lo hi target br r
      | some bl,some br => checkTree lo hi target bl l &&
                           checkTree lo hi target br r

/-- Deterministic depth-first tree generation. The exact node cap used by the
research computation is more than enough for every slab. -/
def searchTree (lo hi target : Q) : Nat→Box→SearchTree
  | 0,_ => .pruned
  | n+1,box =>
      if bound lo hi box<target then .pruned
      else
        let s:=split box
        .branch (widestCoordinate box)
          (match contract lo hi target s.1 with
           | none=>.pruned | some b=>searchTree lo hi target n b)
          (match contract lo hi target s.2 with
           | none=>.pruned | some b=>searchTree lo hi target n b)

def slabCheck (i : Fin 20) : Bool :=
  let lo:Q:=(60+i.val)/100
  let hi:Q:=(61+i.val)/100
  let target:Q:=2219/1000
  let root:=rootBox lo hi
  match contract lo hi target root with
  | none=>true
  | some b=>checkTree lo hi target b (searchTree lo hi target 6000 b)

def closedCheck : Bool := (List.ofFn slabCheck).all id

/-- Polygon clipping is outer-safe for every set satisfying the represented
support inequalities. -/
theorem clip_outer_safe {S : Set Point} {P : Polygon} {n : QPoint} {h : Q}
    (hSP : S⊆rationalPolygon P)
    (hsupp : ∀p∈S,dot p (n.1,n.2)≤h) :
    S⊆rationalPolygon (clip P n h) := by
  exact rational_polygon_clip_contains hSP hsupp

/-- Support contraction preserves every candidate of area at least target. -/
theorem contract_safe {S : Set Point} {lo hi target : Q} {box b : Box}
    (harea : target≤area S)
    (hbox : candidateInBox S lo hi box)
    (hc : contract lo hi target box=some b) :
    candidateInBox S lo hi b := by
  unfold contract at hc
  exact support_quantile_contraction_safe harea hbox hc

/-- A passing search tree bounds the area of every candidate in its root. -/
theorem checkTree_sound {lo hi target : Q} {box : Box} {T : SearchTree}
    (hc : checkTree lo hi target box T=true) :
    ∀S : Set Point,MeasurableSet S →
      terminalPinnedCandidate S lo hi box →
      area S<target := by
  induction T generalizing box with
  | pruned =>
      intro S hS hcand
      have hsub:=candidate_subset_polygons hcand
      exact (area_mono_polygons hS hsub).trans_lt
        (by simpa [checkTree] using hc)
  | branch j l r ihl ihr =>
      intro S hS hcand
      have hs:=support_box_split_complete hcand (split box)
      rcases hs with hs|hs
      · cases hcl : contract lo hi target (split box).1 with
        | none =>
            exact False.elim (contract_none_excludes
              hcand.area_lower hs hcl)
        | some bl =>
            have hb:=contract_safe hcand.area_lower hs hcl
            exact ihl (and_of_and_left hc) S hS hb
      · cases hcr : contract lo hi target (split box).2 with
        | none =>
            exact False.elim (contract_none_excludes
              hcand.area_lower hs hcr)
        | some br =>
            have hb:=contract_safe hcand.area_lower hs hcr
            exact ihr (and_of_and_right hc) S hS hb

/-- Terminal strip plus intermediate hallways put every actual moving sofa in
the appropriate terminal-pinned outer search class. -/
theorem moving_sofa_terminal_candidate {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    {i : Fin 20}
    (hr : ((60+i.val:ℚ)/100:ℝ)≤tan(ω/2))
    (hr' : tan(ω/2)≤((61+i.val:ℚ)/100:ℝ))
    (harea : (2219/1000:ℝ)≤area S) :
    ∃v : Point, terminalPinnedCandidate
      (Rigid.translate v '' S) ((60+i.val)/100) ((61+i.val)/100)
      (rootBox ((60+i.val)/100) ((61+i.val)/100)) := by
  obtain ⟨v,hpin⟩:=terminal_support_pin hS
  refine ⟨v,?_⟩
  exact terminal_candidate_of_motion hS hpin hr hr' harea interTangents

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem closed_reduction : closedCheck=true := by decide

/-- Exact finite coverage of the twenty half-angle slabs [0.60,0.61],
[0.61,0.62], ..., [0.79,0.80]. Endpoints are included so no gap can
remain at a rational grid boundary. -/
theorem exists_hundredth_slab {r : ℝ}
    (hr0 : (3/5:ℝ)≤r) (hr1 : r≤4/5) :
    ∃ i : Fin 20, i.val<20 ∧
      (((60+i.val:ℚ)/100:ℚ):ℝ)≤r ∧
      r≤(((61+i.val:ℚ)/100:ℚ):ℝ) := by
  by_cases h0 : r≤(61/100:ℝ)
  · refine ⟨⟨0,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [hr0]
    · norm_num
      linarith [h0]
  by_cases h1 : r≤(62/100:ℝ)
  · refine ⟨⟨1,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h0]
    · norm_num
      linarith [h1]
  by_cases h2 : r≤(63/100:ℝ)
  · refine ⟨⟨2,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h1]
    · norm_num
      linarith [h2]
  by_cases h3 : r≤(64/100:ℝ)
  · refine ⟨⟨3,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h2]
    · norm_num
      linarith [h3]
  by_cases h4 : r≤(65/100:ℝ)
  · refine ⟨⟨4,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h3]
    · norm_num
      linarith [h4]
  by_cases h5 : r≤(66/100:ℝ)
  · refine ⟨⟨5,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h4]
    · norm_num
      linarith [h5]
  by_cases h6 : r≤(67/100:ℝ)
  · refine ⟨⟨6,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h5]
    · norm_num
      linarith [h6]
  by_cases h7 : r≤(68/100:ℝ)
  · refine ⟨⟨7,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h6]
    · norm_num
      linarith [h7]
  by_cases h8 : r≤(69/100:ℝ)
  · refine ⟨⟨8,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h7]
    · norm_num
      linarith [h8]
  by_cases h9 : r≤(70/100:ℝ)
  · refine ⟨⟨9,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h8]
    · norm_num
      linarith [h9]
  by_cases h10 : r≤(71/100:ℝ)
  · refine ⟨⟨10,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h9]
    · norm_num
      linarith [h10]
  by_cases h11 : r≤(72/100:ℝ)
  · refine ⟨⟨11,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h10]
    · norm_num
      linarith [h11]
  by_cases h12 : r≤(73/100:ℝ)
  · refine ⟨⟨12,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h11]
    · norm_num
      linarith [h12]
  by_cases h13 : r≤(74/100:ℝ)
  · refine ⟨⟨13,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h12]
    · norm_num
      linarith [h13]
  by_cases h14 : r≤(75/100:ℝ)
  · refine ⟨⟨14,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h13]
    · norm_num
      linarith [h14]
  by_cases h15 : r≤(76/100:ℝ)
  · refine ⟨⟨15,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h14]
    · norm_num
      linarith [h15]
  by_cases h16 : r≤(77/100:ℝ)
  · refine ⟨⟨16,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h15]
    · norm_num
      linarith [h16]
  by_cases h17 : r≤(78/100:ℝ)
  · refine ⟨⟨17,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h16]
    · norm_num
      linarith [h17]
  by_cases h18 : r≤(79/100:ℝ)
  · refine ⟨⟨18,by decide⟩,by decide,?_,?_⟩
    · norm_num
      linarith [not_le.mp h17]
    · norm_num
      linarith [h18]
  refine ⟨⟨19,by decide⟩,by decide,?_,?_⟩
  · norm_num
    linarith [not_le.mp h18]
  · norm_num
    linarith [hr1]

/-- Coarse lower bound for the half-angle tangent.

At the threshold omega = arccos(5/11), the half-angle identity gives
tan(omega/2)^2 = 3/8 > 9/25.  The following proof avoids evaluating
an arctangent numerically. -/
theorem coarse_half_angle_lower {ω : ℝ}
    (hω0 : arccos (5/11:ℝ)≤ω)
    (hω1 : ω≤2*arctan (4/5:ℝ)) :
    (3/5:ℝ)≤tan (ω/2) := by
  have hbase : 0≤ω := (arccos_nonneg _).trans hω0
  have hπstrict : ω<π := by
    have htan := arctan_lt_pi_div_two (4/5:ℝ)
    linarith [hω1,htan]
  have hπ : ω≤π := hπstrict.le
  have hcosbound : cos ω≤5/11 := by
    have hcos0 := cos_le_cos_of_nonneg_of_le_pi
      (arccos_nonneg (5/11:ℝ)) hω0 hπ
    have heq : cos (arccos (5/11:ℝ))=5/11 := by
      exact cos_arccos (by norm_num) (by norm_num)
    rw [heq] at hcos0
    exact hcos0
  let x:=ω/2
  have hx0 : 0≤x := by dsimp [x]; linarith
  have hx1 : x<π/2 := by dsimp [x]; linarith [hπstrict]
  have hcx : 0<cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [hx0,pi_pos],hx1⟩
  have hsx : 0≤sin x :=
    sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [hx1,pi_pos])
  have htan_eq : tan x*cos x=sin x := by
    rw [tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcx]
  have htan0 : 0≤tan x := by
    rw [tan_eq_sin_div_cos]
    exact div_nonneg hsx hcx.le
  have htrig : cos ω = cos x^2-sin x^2 := by
    have heq : ω=x+x := by dsimp [x]; ring
    rw [heq,cos_add]
    ring
  have hunit : sin x^2+cos x^2=1 := sin_sq_add_cos_sq x
  have hsinLower : (3/11:ℝ)≤sin x^2 := by
    nlinarith [hcosbound,htrig,hunit]
  have hcosUpper : cos x^2≤8/11 := by
    nlinarith [hcosbound,htrig,hunit]
  have hcos2pos : 0<cos x^2 := sq_pos_of_pos hcx
  have hquadratic : sin x^2=(tan x)^2*cos x^2 := by
    nlinarith [htan_eq]
  by_contra hn
  have ht : tan x<3/5 := lt_of_not_ge hn
  have hsquare : (tan x)^2<(3/5:ℝ)^2 := sq_lt_sq₀ htan0 ht
  have hprod : (tan x)^2*cos x^2<
      (3/5:ℝ)^2*cos x^2 :=
    mul_lt_mul_of_pos_right hsquare hcos2pos
  have hupper : (3/5:ℝ)^2*cos x^2≤(3/5)^2*(8/11) :=
    mul_le_mul_of_nonneg_left hcosUpper (by norm_num)
  rw [hquadratic] at hsinLower
  nlinarith [hprod,hupper,hsinLower]

/-- Exact cosine of the doubled threshold angle; no floating evaluation. -/
private theorem cos_twice_arctan_four_fifths :
    cos (2*arctan (4/5:ℝ))=9/41 := by
  let a : ℝ:=arctan (4/5:ℝ)
  have ha0 : 0<a := arctan_pos (by norm_num : (0:ℝ)<4/5)
  have ha1 : a<π/2 := arctan_lt_pi_div_two _
  have hca : 0<cos a :=
    cos_pos_of_mem_Ioo ⟨by linarith [ha0,pi_pos],ha1⟩
  have htan : tan a=4/5 := tan_arctan _
  have hsin : sin a=(4/5:ℝ)*cos a := by
    rw [tan_eq_sin_div_cos] at htan
    exact (div_eq_iff hca.ne').mp htan
  have hunit : sin a^2+cos a^2=1 := sin_sq_add_cos_sq a
  have heq : 2*a=a+a := by ring
  change cos (2*a)=9/41
  rw [heq,cos_add]
  rw [hsin] at hunit ⊢
  nlinarith [hunit]

/-- Upper half-angle bound on the full coarse slab range, including its
terminal endpoint. The direct cosine argument avoids relying on an
unidentified project-specific tangent-monotonicity helper. -/
theorem coarse_half_angle_upper {ω : ℝ}
    (hω0 : 0≤ω) (hω1 : ω≤2*arctan (4/5:ℝ)) :
    tan (ω/2)≤4/5 := by
  let a : ℝ:=arctan (4/5:ℝ)
  have ha1 : a<π/2 := arctan_lt_pi_div_two _
  have hcos0 : (9/41:ℝ)≤cos ω := by
    have hc:=cos_le_cos_of_nonneg_of_le_pi hω0
      (by simpa [a] using hω1)
      (by linarith [ha1,pi_pos] : 2*a≤π)
    rw [show cos (2*a)=9/41 by
      simpa [a] using cos_twice_arctan_four_fifths] at hc
    exact hc
  let x:=ω/2
  have hx0 : 0≤x := by dsimp [x]; linarith
  have hx1 : x<π/2 := by dsimp [x]; linarith [hω1,ha1]
  have hcx : 0<cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [hx0,pi_pos],hx1⟩
  have hsx : 0≤sin x :=
    sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [hx1,pi_pos])
  have htan_eq : tan x*cos x=sin x := by
    rw [tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcx]
  have htan0 : 0≤tan x := by
    rw [tan_eq_sin_div_cos]
    exact div_nonneg hsx hcx.le
  have htrig : cos ω=cos x^2-sin x^2 := by
    have heq : ω=x+x := by dsimp [x]; ring
    rw [heq,cos_add]
    ring
  have hunit : sin x^2+cos x^2=1 := sin_sq_add_cos_sq x
  have hcosLower : (25/41:ℝ)≤cos x^2 := by
    nlinarith [hcos0,htrig,hunit]
  have hsinUpper : sin x^2≤16/41 := by
    nlinarith [hcos0,htrig,hunit]
  have hcos2pos : 0<cos x^2 := sq_pos_of_pos hcx
  have hquadratic : sin x^2=(tan x)^2*cos x^2 := by
    nlinarith [htan_eq]
  by_contra hn
  have ht : (4/5:ℝ)<tan x := lt_of_not_ge hn
  have hsquare : (4/5:ℝ)^2<(tan x)^2 :=
    sq_lt_sq₀ (by norm_num) ht
  have hprod : (4/5:ℝ)^2*cos x^2<(tan x)^2*cos x^2 :=
    mul_lt_mul_of_pos_right hsquare hcos2pos
  have hlower : (4/5:ℝ)^2*(25/41)≤(4/5)^2*cos x^2 :=
    mul_le_mul_of_nonneg_left hcosLower (by norm_num)
  rw [hquadratic] at hprod
  nlinarith [hprod,hlower,hsinUpper]

theorem coarse_area_separation {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hω0 : arccos (5/11:ℝ)≤ω)
    (hω1 : ω≤2*arctan (4/5:ℝ)) :
    area S<2219/1000 := by
  have hr0 : (3/5:ℝ)≤tan(ω/2) :=
    coarse_half_angle_lower hω0 hω1
  have hr1 : tan(ω/2)≤4/5 :=
    coarse_half_angle_upper ((arccos_nonneg _).trans hω0) hω1
  obtain ⟨i,hi,hr,hr'⟩:=exists_hundredth_slab hr0 hr1
  by_contra hn
  have harea : (2219/1000:ℝ)≤area S:=not_lt.mp hn
  obtain ⟨v,hcand⟩:=moving_sofa_terminal_candidate hS hr hr' harea
  have hc : slabCheck i=true := by
    have h:=closed_reduction
    simpa [closedCheck,List.all_eq_true] using List.get_ofFn h i
  unfold slabCheck at hc
  split at hc
  · exact contract_none_excludes harea hcand ‹_›
  · exact (checkTree_sound hc (Rigid.measurableSet_image
      (ms_isCompact_of_isMovingSofaWithAngle hS).measurableSet)
      ‹_›).not_le (by simpa using harea)

/-- Coarse angle entry used internally by the effective modulus. -/
theorem coarse_angle_entry {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hω : ω∈Icc (arccos (5/11:ℝ)) (π/2))
    (hdef : sofaDeficit P S<1/5000) :
    2*arctan (4/5:ℝ)<ω := by
  have hM : 2774/1250≤area (gerverSofa P):=
    (gerverSofa_area_mem hP hbox).1.trans (by norm_num)
  have harea : 2219/1000≤area S := by
    unfold sofaDeficit at hdef
    linarith
  by_contra hn
  have hs:=coarse_area_separation hS hω.1 (not_lt.mp hn)
  linarith

end CoarseAngleCertificate
end MovingSofaQuantitative
