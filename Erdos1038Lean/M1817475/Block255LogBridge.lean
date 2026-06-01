import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block255

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block255

open Set

def block255W1 : Rat := ((424905440846783 : Rat) / 500000000000000)
def block255W2 : Rat := ((902509357273447 : Rat) / 10000000000000000)
def block255W3 : Rat := ((28416285571510963 : Rat) / 500000000000000000)
def block255W4 : Rat := ((1893160985043469 : Rat) / 10000000000000000)
def block255S1 : Rat := ((18174751 : Rat) / 10000000)
def block255S2 : Rat := ((511587 : Rat) / 200000)
def block255S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block255S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block255V (y : ℝ) : ℝ :=
  ratPotential block255W1 block255W2 block255W3 block255W4 block255S1 block255S2 block255S3 block255S4 y

def block255LeftParamsCertificate : Bool :=
  allBoxesSameParams block255LeftBoxes block255W1 block255W2 block255W3 block255W4 block255S1 block255S2 block255S3 block255S4

theorem block255LeftParamsCertificate_eq_true :
    block255LeftParamsCertificate = true := by
  native_decide

theorem block255_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block255LeftL : ℝ) (block255LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block255S1 : ℝ))
    (hy2ne : y ≠ (block255S2 : ℝ))
    (hy3ne : y ≠ (block255S3 : ℝ))
    (hy4ne : y ≠ (block255S4 : ℝ)) :
    0 < block255V y := by
  have hcert := block255LeftCertificate_eq_true
  unfold block255LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block255LeftBoxes) (lo := block255LeftL) (hi := block255LeftR)
    (w1 := block255W1) (w2 := block255W2) (w3 := block255W3) (w4 := block255W4)
    (s1 := block255S1) (s2 := block255S2) (s3 := block255S3) (s4 := block255S4)
    hboxes hcover block255LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block255RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block255RightChunk000 block255W1 block255W2 block255W3 block255W4 block255S1 block255S2 block255S3 block255S4

theorem block255RightChunk000ParamsCertificate_eq_true :
    block255RightChunk000ParamsCertificate = true := by
  native_decide

theorem block255_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block255RightChunk000L : ℝ) (block255RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block255S1 : ℝ))
    (hy2ne : y ≠ (block255S2 : ℝ))
    (hy3ne : y ≠ (block255S3 : ℝ))
    (hy4ne : y ≠ (block255S4 : ℝ)) :
    0 < block255V y := by
  have hcert := block255RightChunk000Certificate_eq_true
  unfold block255RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block255RightChunk000) (lo := block255RightChunk000L) (hi := block255RightChunk000R)
    (w1 := block255W1) (w2 := block255W2) (w3 := block255W3) (w4 := block255W4)
    (s1 := block255S1) (s2 := block255S2) (s3 := block255S3) (s4 := block255S4)
    hboxes hcover block255RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block255_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block255RightL : ℝ) (block255RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block255S1 : ℝ))
    (hy2ne : y ≠ (block255S2 : ℝ))
    (hy3ne : y ≠ (block255S3 : ℝ))
    (hy4ne : y ≠ (block255S4 : ℝ)) :
    0 < block255V y := by
  have hL : (block255RightChunk000L : ℝ) = (block255RightL : ℝ) := by
    norm_num [block255RightChunk000L, block255RightL]
  have hR : (block255RightChunk000R : ℝ) = (block255RightR : ℝ) := by
    norm_num [block255RightChunk000R, block255RightR]
  have hyc : y ∈ Icc (block255RightChunk000L : ℝ) (block255RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block255_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block255_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block255LeftL : ℝ) (block255LeftR : ℝ) →
    y ≠ 0 → y ≠ (block255S1 : ℝ) → y ≠ (block255S2 : ℝ) →
    y ≠ (block255S3 : ℝ) → y ≠ (block255S4 : ℝ) → 0 < block255V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block255RightL : ℝ) (block255RightR : ℝ) →
    y ≠ 0 → y ≠ (block255S1 : ℝ) → y ≠ (block255S2 : ℝ) →
    y ≠ (block255S3 : ℝ) → y ≠ (block255S4 : ℝ) → 0 < block255V y)

theorem block255_reallog_certificate_proof :
    block255_reallog_certificate := by
  exact ⟨block255_left_V_pos, block255_right_V_pos⟩

end Block255
end M1817475
end Erdos1038Lean
