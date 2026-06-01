import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block253

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block253

open Set

def block253W1 : Rat := ((8511329491207369 : Rat) / 10000000000000000)
def block253W2 : Rat := ((8941744206210933 : Rat) / 100000000000000000)
def block253W3 : Rat := ((336092179201333 : Rat) / 6250000000000000)
def block253W4 : Rat := ((1932740651455037 : Rat) / 10000000000000000)
def block253S1 : Rat := ((18174751 : Rat) / 10000000)
def block253S2 : Rat := ((511587 : Rat) / 200000)
def block253S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block253S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block253V (y : ℝ) : ℝ :=
  ratPotential block253W1 block253W2 block253W3 block253W4 block253S1 block253S2 block253S3 block253S4 y

def block253LeftParamsCertificate : Bool :=
  allBoxesSameParams block253LeftBoxes block253W1 block253W2 block253W3 block253W4 block253S1 block253S2 block253S3 block253S4

theorem block253LeftParamsCertificate_eq_true :
    block253LeftParamsCertificate = true := by
  native_decide

theorem block253_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block253LeftL : ℝ) (block253LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block253S1 : ℝ))
    (hy2ne : y ≠ (block253S2 : ℝ))
    (hy3ne : y ≠ (block253S3 : ℝ))
    (hy4ne : y ≠ (block253S4 : ℝ)) :
    0 < block253V y := by
  have hcert := block253LeftCertificate_eq_true
  unfold block253LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block253LeftBoxes) (lo := block253LeftL) (hi := block253LeftR)
    (w1 := block253W1) (w2 := block253W2) (w3 := block253W3) (w4 := block253W4)
    (s1 := block253S1) (s2 := block253S2) (s3 := block253S3) (s4 := block253S4)
    hboxes hcover block253LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block253RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block253RightChunk000 block253W1 block253W2 block253W3 block253W4 block253S1 block253S2 block253S3 block253S4

theorem block253RightChunk000ParamsCertificate_eq_true :
    block253RightChunk000ParamsCertificate = true := by
  native_decide

theorem block253_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block253RightChunk000L : ℝ) (block253RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block253S1 : ℝ))
    (hy2ne : y ≠ (block253S2 : ℝ))
    (hy3ne : y ≠ (block253S3 : ℝ))
    (hy4ne : y ≠ (block253S4 : ℝ)) :
    0 < block253V y := by
  have hcert := block253RightChunk000Certificate_eq_true
  unfold block253RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block253RightChunk000) (lo := block253RightChunk000L) (hi := block253RightChunk000R)
    (w1 := block253W1) (w2 := block253W2) (w3 := block253W3) (w4 := block253W4)
    (s1 := block253S1) (s2 := block253S2) (s3 := block253S3) (s4 := block253S4)
    hboxes hcover block253RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block253_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block253RightL : ℝ) (block253RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block253S1 : ℝ))
    (hy2ne : y ≠ (block253S2 : ℝ))
    (hy3ne : y ≠ (block253S3 : ℝ))
    (hy4ne : y ≠ (block253S4 : ℝ)) :
    0 < block253V y := by
  have hL : (block253RightChunk000L : ℝ) = (block253RightL : ℝ) := by
    norm_num [block253RightChunk000L, block253RightL]
  have hR : (block253RightChunk000R : ℝ) = (block253RightR : ℝ) := by
    norm_num [block253RightChunk000R, block253RightR]
  have hyc : y ∈ Icc (block253RightChunk000L : ℝ) (block253RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block253_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block253_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block253LeftL : ℝ) (block253LeftR : ℝ) →
    y ≠ 0 → y ≠ (block253S1 : ℝ) → y ≠ (block253S2 : ℝ) →
    y ≠ (block253S3 : ℝ) → y ≠ (block253S4 : ℝ) → 0 < block253V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block253RightL : ℝ) (block253RightR : ℝ) →
    y ≠ 0 → y ≠ (block253S1 : ℝ) → y ≠ (block253S2 : ℝ) →
    y ≠ (block253S3 : ℝ) → y ≠ (block253S4 : ℝ) → 0 < block253V y)

theorem block253_reallog_certificate_proof :
    block253_reallog_certificate := by
  exact ⟨block253_left_V_pos, block253_right_V_pos⟩

end Block253
end M1817475
end Erdos1038Lean
