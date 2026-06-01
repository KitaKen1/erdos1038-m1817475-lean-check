import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block329

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block329

open Set

def block329W1 : Rat := ((4759439258797193 : Rat) / 5000000000000000)
def block329W2 : Rat := ((2358401064624571 : Rat) / 50000000000000000)
def block329W3 : Rat := ((1431366440282023 : Rat) / 10000000000000000)
def block329W4 : Rat := ((1708894130599483 : Rat) / 12500000000000000)
def block329S1 : Rat := ((18174751 : Rat) / 10000000)
def block329S2 : Rat := ((511587 : Rat) / 200000)
def block329S3 : Rat := ((26740380196428571429 : Rat) / 10000000000000000000)
def block329S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block329V (y : ℝ) : ℝ :=
  ratPotential block329W1 block329W2 block329W3 block329W4 block329S1 block329S2 block329S3 block329S4 y

def block329LeftParamsCertificate : Bool :=
  allBoxesSameParams block329LeftBoxes block329W1 block329W2 block329W3 block329W4 block329S1 block329S2 block329S3 block329S4

theorem block329LeftParamsCertificate_eq_true :
    block329LeftParamsCertificate = true := by
  native_decide

theorem block329_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block329LeftL : ℝ) (block329LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block329S1 : ℝ))
    (hy2ne : y ≠ (block329S2 : ℝ))
    (hy3ne : y ≠ (block329S3 : ℝ))
    (hy4ne : y ≠ (block329S4 : ℝ)) :
    0 < block329V y := by
  have hcert := block329LeftCertificate_eq_true
  unfold block329LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block329LeftBoxes) (lo := block329LeftL) (hi := block329LeftR)
    (w1 := block329W1) (w2 := block329W2) (w3 := block329W3) (w4 := block329W4)
    (s1 := block329S1) (s2 := block329S2) (s3 := block329S3) (s4 := block329S4)
    hboxes hcover block329LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block329RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block329RightChunk000 block329W1 block329W2 block329W3 block329W4 block329S1 block329S2 block329S3 block329S4

theorem block329RightChunk000ParamsCertificate_eq_true :
    block329RightChunk000ParamsCertificate = true := by
  native_decide

theorem block329_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block329RightChunk000L : ℝ) (block329RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block329S1 : ℝ))
    (hy2ne : y ≠ (block329S2 : ℝ))
    (hy3ne : y ≠ (block329S3 : ℝ))
    (hy4ne : y ≠ (block329S4 : ℝ)) :
    0 < block329V y := by
  have hcert := block329RightChunk000Certificate_eq_true
  unfold block329RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block329RightChunk000) (lo := block329RightChunk000L) (hi := block329RightChunk000R)
    (w1 := block329W1) (w2 := block329W2) (w3 := block329W3) (w4 := block329W4)
    (s1 := block329S1) (s2 := block329S2) (s3 := block329S3) (s4 := block329S4)
    hboxes hcover block329RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block329_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block329RightL : ℝ) (block329RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block329S1 : ℝ))
    (hy2ne : y ≠ (block329S2 : ℝ))
    (hy3ne : y ≠ (block329S3 : ℝ))
    (hy4ne : y ≠ (block329S4 : ℝ)) :
    0 < block329V y := by
  have hL : (block329RightChunk000L : ℝ) = (block329RightL : ℝ) := by
    norm_num [block329RightChunk000L, block329RightL]
  have hR : (block329RightChunk000R : ℝ) = (block329RightR : ℝ) := by
    norm_num [block329RightChunk000R, block329RightR]
  have hyc : y ∈ Icc (block329RightChunk000L : ℝ) (block329RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block329_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block329_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block329LeftL : ℝ) (block329LeftR : ℝ) →
    y ≠ 0 → y ≠ (block329S1 : ℝ) → y ≠ (block329S2 : ℝ) →
    y ≠ (block329S3 : ℝ) → y ≠ (block329S4 : ℝ) → 0 < block329V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block329RightL : ℝ) (block329RightR : ℝ) →
    y ≠ 0 → y ≠ (block329S1 : ℝ) → y ≠ (block329S2 : ℝ) →
    y ≠ (block329S3 : ℝ) → y ≠ (block329S4 : ℝ) → 0 < block329V y)

theorem block329_reallog_certificate_proof :
    block329_reallog_certificate := by
  exact ⟨block329_left_V_pos, block329_right_V_pos⟩

end Block329
end M1817475
end Erdos1038Lean
