import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block508

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block508

open Set

def block508W1 : Rat := ((4407779173425467 : Rat) / 10000000000000000)
def block508W2 : Rat := (0 : Rat)
def block508W3 : Rat := ((864039561583851 : Rat) / 2000000000000000)
def block508W4 : Rat := ((2281006057628347 : Rat) / 250000000000000000)
def block508S1 : Rat := ((18174751 : Rat) / 10000000)
def block508S2 : Rat := ((511587 : Rat) / 200000)
def block508S3 : Rat := ((130202610803571428727 : Rat) / 50000000000000000000)
def block508S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block508V (y : ℝ) : ℝ :=
  ratPotential block508W1 block508W2 block508W3 block508W4 block508S1 block508S2 block508S3 block508S4 y

def block508LeftParamsCertificate : Bool :=
  allBoxesSameParams block508LeftBoxes block508W1 block508W2 block508W3 block508W4 block508S1 block508S2 block508S3 block508S4

theorem block508LeftParamsCertificate_eq_true :
    block508LeftParamsCertificate = true := by
  native_decide

theorem block508_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block508LeftL : ℝ) (block508LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block508S1 : ℝ))
    (hy2ne : y ≠ (block508S2 : ℝ))
    (hy3ne : y ≠ (block508S3 : ℝ))
    (hy4ne : y ≠ (block508S4 : ℝ)) :
    0 < block508V y := by
  have hcert := block508LeftCertificate_eq_true
  unfold block508LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block508LeftBoxes) (lo := block508LeftL) (hi := block508LeftR)
    (w1 := block508W1) (w2 := block508W2) (w3 := block508W3) (w4 := block508W4)
    (s1 := block508S1) (s2 := block508S2) (s3 := block508S3) (s4 := block508S4)
    hboxes hcover block508LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block508RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block508RightChunk000 block508W1 block508W2 block508W3 block508W4 block508S1 block508S2 block508S3 block508S4

theorem block508RightChunk000ParamsCertificate_eq_true :
    block508RightChunk000ParamsCertificate = true := by
  native_decide

theorem block508_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block508RightChunk000L : ℝ) (block508RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block508S1 : ℝ))
    (hy2ne : y ≠ (block508S2 : ℝ))
    (hy3ne : y ≠ (block508S3 : ℝ))
    (hy4ne : y ≠ (block508S4 : ℝ)) :
    0 < block508V y := by
  have hcert := block508RightChunk000Certificate_eq_true
  unfold block508RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block508RightChunk000) (lo := block508RightChunk000L) (hi := block508RightChunk000R)
    (w1 := block508W1) (w2 := block508W2) (w3 := block508W3) (w4 := block508W4)
    (s1 := block508S1) (s2 := block508S2) (s3 := block508S3) (s4 := block508S4)
    hboxes hcover block508RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block508_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block508RightL : ℝ) (block508RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block508S1 : ℝ))
    (hy2ne : y ≠ (block508S2 : ℝ))
    (hy3ne : y ≠ (block508S3 : ℝ))
    (hy4ne : y ≠ (block508S4 : ℝ)) :
    0 < block508V y := by
  have hL : (block508RightChunk000L : ℝ) = (block508RightL : ℝ) := by
    norm_num [block508RightChunk000L, block508RightL]
  have hR : (block508RightChunk000R : ℝ) = (block508RightR : ℝ) := by
    norm_num [block508RightChunk000R, block508RightR]
  have hyc : y ∈ Icc (block508RightChunk000L : ℝ) (block508RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block508_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block508_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block508LeftL : ℝ) (block508LeftR : ℝ) →
    y ≠ 0 → y ≠ (block508S1 : ℝ) → y ≠ (block508S2 : ℝ) →
    y ≠ (block508S3 : ℝ) → y ≠ (block508S4 : ℝ) → 0 < block508V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block508RightL : ℝ) (block508RightR : ℝ) →
    y ≠ 0 → y ≠ (block508S1 : ℝ) → y ≠ (block508S2 : ℝ) →
    y ≠ (block508S3 : ℝ) → y ≠ (block508S4 : ℝ) → 0 < block508V y)

theorem block508_reallog_certificate_proof :
    block508_reallog_certificate := by
  exact ⟨block508_left_V_pos, block508_right_V_pos⟩

end Block508
end M1817475
end Erdos1038Lean
