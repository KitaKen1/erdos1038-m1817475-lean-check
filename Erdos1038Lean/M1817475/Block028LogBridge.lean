import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block028

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block028

open Set

def block028W1 : Rat := ((469047370338611 : Rat) / 200000000000000)
def block028W2 : Rat := (0 : Rat)
def block028W3 : Rat := (0 : Rat)
def block028W4 : Rat := ((28466650568511037 : Rat) / 100000000000000000)
def block028S1 : Rat := ((18174751 : Rat) / 10000000)
def block028S2 : Rat := ((511587 : Rat) / 200000)
def block028S3 : Rat := ((107000619 : Rat) / 40000000)
def block028S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block028V (y : ℝ) : ℝ :=
  ratPotential block028W1 block028W2 block028W3 block028W4 block028S1 block028S2 block028S3 block028S4 y

def block028LeftParamsCertificate : Bool :=
  allBoxesSameParams block028LeftBoxes block028W1 block028W2 block028W3 block028W4 block028S1 block028S2 block028S3 block028S4

theorem block028LeftParamsCertificate_eq_true :
    block028LeftParamsCertificate = true := by
  native_decide

theorem block028_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block028LeftL : ℝ) (block028LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block028S1 : ℝ))
    (hy2ne : y ≠ (block028S2 : ℝ))
    (hy3ne : y ≠ (block028S3 : ℝ))
    (hy4ne : y ≠ (block028S4 : ℝ)) :
    0 < block028V y := by
  have hcert := block028LeftCertificate_eq_true
  unfold block028LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block028LeftBoxes) (lo := block028LeftL) (hi := block028LeftR)
    (w1 := block028W1) (w2 := block028W2) (w3 := block028W3) (w4 := block028W4)
    (s1 := block028S1) (s2 := block028S2) (s3 := block028S3) (s4 := block028S4)
    hboxes hcover block028LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block028RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block028RightChunk000 block028W1 block028W2 block028W3 block028W4 block028S1 block028S2 block028S3 block028S4

theorem block028RightChunk000ParamsCertificate_eq_true :
    block028RightChunk000ParamsCertificate = true := by
  native_decide

theorem block028_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block028RightChunk000L : ℝ) (block028RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block028S1 : ℝ))
    (hy2ne : y ≠ (block028S2 : ℝ))
    (hy3ne : y ≠ (block028S3 : ℝ))
    (hy4ne : y ≠ (block028S4 : ℝ)) :
    0 < block028V y := by
  have hcert := block028RightChunk000Certificate_eq_true
  unfold block028RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block028RightChunk000) (lo := block028RightChunk000L) (hi := block028RightChunk000R)
    (w1 := block028W1) (w2 := block028W2) (w3 := block028W3) (w4 := block028W4)
    (s1 := block028S1) (s2 := block028S2) (s3 := block028S3) (s4 := block028S4)
    hboxes hcover block028RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block028_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block028RightL : ℝ) (block028RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block028S1 : ℝ))
    (hy2ne : y ≠ (block028S2 : ℝ))
    (hy3ne : y ≠ (block028S3 : ℝ))
    (hy4ne : y ≠ (block028S4 : ℝ)) :
    0 < block028V y := by
  have hL : (block028RightChunk000L : ℝ) = (block028RightL : ℝ) := by
    norm_num [block028RightChunk000L, block028RightL]
  have hR : (block028RightChunk000R : ℝ) = (block028RightR : ℝ) := by
    norm_num [block028RightChunk000R, block028RightR]
  have hyc : y ∈ Icc (block028RightChunk000L : ℝ) (block028RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block028_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block028_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block028LeftL : ℝ) (block028LeftR : ℝ) →
    y ≠ 0 → y ≠ (block028S1 : ℝ) → y ≠ (block028S2 : ℝ) →
    y ≠ (block028S3 : ℝ) → y ≠ (block028S4 : ℝ) → 0 < block028V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block028RightL : ℝ) (block028RightR : ℝ) →
    y ≠ 0 → y ≠ (block028S1 : ℝ) → y ≠ (block028S2 : ℝ) →
    y ≠ (block028S3 : ℝ) → y ≠ (block028S4 : ℝ) → 0 < block028V y)

theorem block028_reallog_certificate_proof :
    block028_reallog_certificate := by
  exact ⟨block028_left_V_pos, block028_right_V_pos⟩

end Block028
end M1817475
end Erdos1038Lean
