import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block525

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block525

open Set

def block525W1 : Rat := ((2065183251460157 : Rat) / 5000000000000000)
def block525W2 : Rat := (0 : Rat)
def block525W3 : Rat := ((56287156761467 : Rat) / 125000000000000)
def block525W4 : Rat := (0 : Rat)
def block525S1 : Rat := ((18174751 : Rat) / 10000000)
def block525S2 : Rat := ((511587 : Rat) / 200000)
def block525S3 : Rat := ((129870275982142857313 : Rat) / 50000000000000000000)
def block525S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block525V (y : ℝ) : ℝ :=
  ratPotential block525W1 block525W2 block525W3 block525W4 block525S1 block525S2 block525S3 block525S4 y

def block525LeftParamsCertificate : Bool :=
  allBoxesSameParams block525LeftBoxes block525W1 block525W2 block525W3 block525W4 block525S1 block525S2 block525S3 block525S4

theorem block525LeftParamsCertificate_eq_true :
    block525LeftParamsCertificate = true := by
  native_decide

theorem block525_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block525LeftL : ℝ) (block525LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block525S1 : ℝ))
    (hy2ne : y ≠ (block525S2 : ℝ))
    (hy3ne : y ≠ (block525S3 : ℝ))
    (hy4ne : y ≠ (block525S4 : ℝ)) :
    0 < block525V y := by
  have hcert := block525LeftCertificate_eq_true
  unfold block525LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block525LeftBoxes) (lo := block525LeftL) (hi := block525LeftR)
    (w1 := block525W1) (w2 := block525W2) (w3 := block525W3) (w4 := block525W4)
    (s1 := block525S1) (s2 := block525S2) (s3 := block525S3) (s4 := block525S4)
    hboxes hcover block525LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block525RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block525RightChunk000 block525W1 block525W2 block525W3 block525W4 block525S1 block525S2 block525S3 block525S4

theorem block525RightChunk000ParamsCertificate_eq_true :
    block525RightChunk000ParamsCertificate = true := by
  native_decide

theorem block525_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block525RightChunk000L : ℝ) (block525RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block525S1 : ℝ))
    (hy2ne : y ≠ (block525S2 : ℝ))
    (hy3ne : y ≠ (block525S3 : ℝ))
    (hy4ne : y ≠ (block525S4 : ℝ)) :
    0 < block525V y := by
  have hcert := block525RightChunk000Certificate_eq_true
  unfold block525RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block525RightChunk000) (lo := block525RightChunk000L) (hi := block525RightChunk000R)
    (w1 := block525W1) (w2 := block525W2) (w3 := block525W3) (w4 := block525W4)
    (s1 := block525S1) (s2 := block525S2) (s3 := block525S3) (s4 := block525S4)
    hboxes hcover block525RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block525_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block525RightL : ℝ) (block525RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block525S1 : ℝ))
    (hy2ne : y ≠ (block525S2 : ℝ))
    (hy3ne : y ≠ (block525S3 : ℝ))
    (hy4ne : y ≠ (block525S4 : ℝ)) :
    0 < block525V y := by
  have hL : (block525RightChunk000L : ℝ) = (block525RightL : ℝ) := by
    norm_num [block525RightChunk000L, block525RightL]
  have hR : (block525RightChunk000R : ℝ) = (block525RightR : ℝ) := by
    norm_num [block525RightChunk000R, block525RightR]
  have hyc : y ∈ Icc (block525RightChunk000L : ℝ) (block525RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block525_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block525_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block525LeftL : ℝ) (block525LeftR : ℝ) →
    y ≠ 0 → y ≠ (block525S1 : ℝ) → y ≠ (block525S2 : ℝ) →
    y ≠ (block525S3 : ℝ) → y ≠ (block525S4 : ℝ) → 0 < block525V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block525RightL : ℝ) (block525RightR : ℝ) →
    y ≠ 0 → y ≠ (block525S1 : ℝ) → y ≠ (block525S2 : ℝ) →
    y ≠ (block525S3 : ℝ) → y ≠ (block525S4 : ℝ) → 0 < block525V y)

theorem block525_reallog_certificate_proof :
    block525_reallog_certificate := by
  exact ⟨block525_left_V_pos, block525_right_V_pos⟩

end Block525
end M1817475
end Erdos1038Lean
