import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block254

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block254

open Set

def block254W1 : Rat := ((8508559764306283 : Rat) / 10000000000000000)
def block254W2 : Rat := ((1121202467766577 : Rat) / 12500000000000000)
def block254W3 : Rat := ((11123277178336273 : Rat) / 200000000000000000)
def block254W4 : Rat := ((95538515698991 : Rat) / 500000000000000)
def block254S1 : Rat := ((18174751 : Rat) / 10000000)
def block254S2 : Rat := ((511587 : Rat) / 200000)
def block254S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block254S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block254V (y : ℝ) : ℝ :=
  ratPotential block254W1 block254W2 block254W3 block254W4 block254S1 block254S2 block254S3 block254S4 y

def block254LeftParamsCertificate : Bool :=
  allBoxesSameParams block254LeftBoxes block254W1 block254W2 block254W3 block254W4 block254S1 block254S2 block254S3 block254S4

theorem block254LeftParamsCertificate_eq_true :
    block254LeftParamsCertificate = true := by
  native_decide

theorem block254_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block254LeftL : ℝ) (block254LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block254S1 : ℝ))
    (hy2ne : y ≠ (block254S2 : ℝ))
    (hy3ne : y ≠ (block254S3 : ℝ))
    (hy4ne : y ≠ (block254S4 : ℝ)) :
    0 < block254V y := by
  have hcert := block254LeftCertificate_eq_true
  unfold block254LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block254LeftBoxes) (lo := block254LeftL) (hi := block254LeftR)
    (w1 := block254W1) (w2 := block254W2) (w3 := block254W3) (w4 := block254W4)
    (s1 := block254S1) (s2 := block254S2) (s3 := block254S3) (s4 := block254S4)
    hboxes hcover block254LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block254RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block254RightChunk000 block254W1 block254W2 block254W3 block254W4 block254S1 block254S2 block254S3 block254S4

theorem block254RightChunk000ParamsCertificate_eq_true :
    block254RightChunk000ParamsCertificate = true := by
  native_decide

theorem block254_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block254RightChunk000L : ℝ) (block254RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block254S1 : ℝ))
    (hy2ne : y ≠ (block254S2 : ℝ))
    (hy3ne : y ≠ (block254S3 : ℝ))
    (hy4ne : y ≠ (block254S4 : ℝ)) :
    0 < block254V y := by
  have hcert := block254RightChunk000Certificate_eq_true
  unfold block254RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block254RightChunk000) (lo := block254RightChunk000L) (hi := block254RightChunk000R)
    (w1 := block254W1) (w2 := block254W2) (w3 := block254W3) (w4 := block254W4)
    (s1 := block254S1) (s2 := block254S2) (s3 := block254S3) (s4 := block254S4)
    hboxes hcover block254RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block254_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block254RightL : ℝ) (block254RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block254S1 : ℝ))
    (hy2ne : y ≠ (block254S2 : ℝ))
    (hy3ne : y ≠ (block254S3 : ℝ))
    (hy4ne : y ≠ (block254S4 : ℝ)) :
    0 < block254V y := by
  have hL : (block254RightChunk000L : ℝ) = (block254RightL : ℝ) := by
    norm_num [block254RightChunk000L, block254RightL]
  have hR : (block254RightChunk000R : ℝ) = (block254RightR : ℝ) := by
    norm_num [block254RightChunk000R, block254RightR]
  have hyc : y ∈ Icc (block254RightChunk000L : ℝ) (block254RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block254_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block254_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block254LeftL : ℝ) (block254LeftR : ℝ) →
    y ≠ 0 → y ≠ (block254S1 : ℝ) → y ≠ (block254S2 : ℝ) →
    y ≠ (block254S3 : ℝ) → y ≠ (block254S4 : ℝ) → 0 < block254V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block254RightL : ℝ) (block254RightR : ℝ) →
    y ≠ 0 → y ≠ (block254S1 : ℝ) → y ≠ (block254S2 : ℝ) →
    y ≠ (block254S3 : ℝ) → y ≠ (block254S4 : ℝ) → 0 < block254V y)

theorem block254_reallog_certificate_proof :
    block254_reallog_certificate := by
  exact ⟨block254_left_V_pos, block254_right_V_pos⟩

end Block254
end M1817475
end Erdos1038Lean
