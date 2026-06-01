import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block522

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block522

open Set

def block522W1 : Rat := ((4162030561196761 : Rat) / 10000000000000000)
def block522W2 : Rat := (0 : Rat)
def block522W3 : Rat := ((44916133327417923 : Rat) / 100000000000000000)
def block522W4 : Rat := (0 : Rat)
def block522S1 : Rat := ((18174751 : Rat) / 10000000)
def block522S2 : Rat := ((511587 : Rat) / 200000)
def block522S3 : Rat := ((129928923303571428739 : Rat) / 50000000000000000000)
def block522S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block522V (y : ℝ) : ℝ :=
  ratPotential block522W1 block522W2 block522W3 block522W4 block522S1 block522S2 block522S3 block522S4 y

def block522LeftParamsCertificate : Bool :=
  allBoxesSameParams block522LeftBoxes block522W1 block522W2 block522W3 block522W4 block522S1 block522S2 block522S3 block522S4

theorem block522LeftParamsCertificate_eq_true :
    block522LeftParamsCertificate = true := by
  native_decide

theorem block522_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block522LeftL : ℝ) (block522LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block522S1 : ℝ))
    (hy2ne : y ≠ (block522S2 : ℝ))
    (hy3ne : y ≠ (block522S3 : ℝ))
    (hy4ne : y ≠ (block522S4 : ℝ)) :
    0 < block522V y := by
  have hcert := block522LeftCertificate_eq_true
  unfold block522LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block522LeftBoxes) (lo := block522LeftL) (hi := block522LeftR)
    (w1 := block522W1) (w2 := block522W2) (w3 := block522W3) (w4 := block522W4)
    (s1 := block522S1) (s2 := block522S2) (s3 := block522S3) (s4 := block522S4)
    hboxes hcover block522LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block522RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block522RightChunk000 block522W1 block522W2 block522W3 block522W4 block522S1 block522S2 block522S3 block522S4

theorem block522RightChunk000ParamsCertificate_eq_true :
    block522RightChunk000ParamsCertificate = true := by
  native_decide

theorem block522_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block522RightChunk000L : ℝ) (block522RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block522S1 : ℝ))
    (hy2ne : y ≠ (block522S2 : ℝ))
    (hy3ne : y ≠ (block522S3 : ℝ))
    (hy4ne : y ≠ (block522S4 : ℝ)) :
    0 < block522V y := by
  have hcert := block522RightChunk000Certificate_eq_true
  unfold block522RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block522RightChunk000) (lo := block522RightChunk000L) (hi := block522RightChunk000R)
    (w1 := block522W1) (w2 := block522W2) (w3 := block522W3) (w4 := block522W4)
    (s1 := block522S1) (s2 := block522S2) (s3 := block522S3) (s4 := block522S4)
    hboxes hcover block522RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block522_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block522RightL : ℝ) (block522RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block522S1 : ℝ))
    (hy2ne : y ≠ (block522S2 : ℝ))
    (hy3ne : y ≠ (block522S3 : ℝ))
    (hy4ne : y ≠ (block522S4 : ℝ)) :
    0 < block522V y := by
  have hL : (block522RightChunk000L : ℝ) = (block522RightL : ℝ) := by
    norm_num [block522RightChunk000L, block522RightL]
  have hR : (block522RightChunk000R : ℝ) = (block522RightR : ℝ) := by
    norm_num [block522RightChunk000R, block522RightR]
  have hyc : y ∈ Icc (block522RightChunk000L : ℝ) (block522RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block522_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block522_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block522LeftL : ℝ) (block522LeftR : ℝ) →
    y ≠ 0 → y ≠ (block522S1 : ℝ) → y ≠ (block522S2 : ℝ) →
    y ≠ (block522S3 : ℝ) → y ≠ (block522S4 : ℝ) → 0 < block522V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block522RightL : ℝ) (block522RightR : ℝ) →
    y ≠ 0 → y ≠ (block522S1 : ℝ) → y ≠ (block522S2 : ℝ) →
    y ≠ (block522S3 : ℝ) → y ≠ (block522S4 : ℝ) → 0 < block522V y)

theorem block522_reallog_certificate_proof :
    block522_reallog_certificate := by
  exact ⟨block522_left_V_pos, block522_right_V_pos⟩

end Block522
end M1817475
end Erdos1038Lean
