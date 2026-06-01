import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block383

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block383

open Set

def block383W1 : Rat := ((422262635623031 : Rat) / 500000000000000)
def block383W2 : Rat := ((4631139403900129 : Rat) / 100000000000000000)
def block383W3 : Rat := ((795746713398921 : Rat) / 5000000000000000)
def block383W4 : Rat := ((562398753295951 : Rat) / 4000000000000000)
def block383S1 : Rat := ((18174751 : Rat) / 10000000)
def block383S2 : Rat := ((511587 : Rat) / 200000)
def block383S3 : Rat := ((132646249196428571477 : Rat) / 50000000000000000000)
def block383S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block383V (y : ℝ) : ℝ :=
  ratPotential block383W1 block383W2 block383W3 block383W4 block383S1 block383S2 block383S3 block383S4 y

def block383LeftParamsCertificate : Bool :=
  allBoxesSameParams block383LeftBoxes block383W1 block383W2 block383W3 block383W4 block383S1 block383S2 block383S3 block383S4

theorem block383LeftParamsCertificate_eq_true :
    block383LeftParamsCertificate = true := by
  native_decide

theorem block383_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block383LeftL : ℝ) (block383LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block383S1 : ℝ))
    (hy2ne : y ≠ (block383S2 : ℝ))
    (hy3ne : y ≠ (block383S3 : ℝ))
    (hy4ne : y ≠ (block383S4 : ℝ)) :
    0 < block383V y := by
  have hcert := block383LeftCertificate_eq_true
  unfold block383LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block383LeftBoxes) (lo := block383LeftL) (hi := block383LeftR)
    (w1 := block383W1) (w2 := block383W2) (w3 := block383W3) (w4 := block383W4)
    (s1 := block383S1) (s2 := block383S2) (s3 := block383S3) (s4 := block383S4)
    hboxes hcover block383LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block383RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block383RightChunk000 block383W1 block383W2 block383W3 block383W4 block383S1 block383S2 block383S3 block383S4

theorem block383RightChunk000ParamsCertificate_eq_true :
    block383RightChunk000ParamsCertificate = true := by
  native_decide

theorem block383_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block383RightChunk000L : ℝ) (block383RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block383S1 : ℝ))
    (hy2ne : y ≠ (block383S2 : ℝ))
    (hy3ne : y ≠ (block383S3 : ℝ))
    (hy4ne : y ≠ (block383S4 : ℝ)) :
    0 < block383V y := by
  have hcert := block383RightChunk000Certificate_eq_true
  unfold block383RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block383RightChunk000) (lo := block383RightChunk000L) (hi := block383RightChunk000R)
    (w1 := block383W1) (w2 := block383W2) (w3 := block383W3) (w4 := block383W4)
    (s1 := block383S1) (s2 := block383S2) (s3 := block383S3) (s4 := block383S4)
    hboxes hcover block383RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block383_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block383RightL : ℝ) (block383RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block383S1 : ℝ))
    (hy2ne : y ≠ (block383S2 : ℝ))
    (hy3ne : y ≠ (block383S3 : ℝ))
    (hy4ne : y ≠ (block383S4 : ℝ)) :
    0 < block383V y := by
  have hL : (block383RightChunk000L : ℝ) = (block383RightL : ℝ) := by
    norm_num [block383RightChunk000L, block383RightL]
  have hR : (block383RightChunk000R : ℝ) = (block383RightR : ℝ) := by
    norm_num [block383RightChunk000R, block383RightR]
  have hyc : y ∈ Icc (block383RightChunk000L : ℝ) (block383RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block383_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block383_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block383LeftL : ℝ) (block383LeftR : ℝ) →
    y ≠ 0 → y ≠ (block383S1 : ℝ) → y ≠ (block383S2 : ℝ) →
    y ≠ (block383S3 : ℝ) → y ≠ (block383S4 : ℝ) → 0 < block383V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block383RightL : ℝ) (block383RightR : ℝ) →
    y ≠ 0 → y ≠ (block383S1 : ℝ) → y ≠ (block383S2 : ℝ) →
    y ≠ (block383S3 : ℝ) → y ≠ (block383S4 : ℝ) → 0 < block383V y)

theorem block383_reallog_certificate_proof :
    block383_reallog_certificate := by
  exact ⟨block383_left_V_pos, block383_right_V_pos⟩

end Block383
end M1817475
end Erdos1038Lean
