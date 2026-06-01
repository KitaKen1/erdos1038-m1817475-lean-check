import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block055

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block055

open Set

def block055W1 : Rat := ((2767627551382381 : Rat) / 1000000000000000)
def block055W2 : Rat := (0 : Rat)
def block055W3 : Rat := (0 : Rat)
def block055W4 : Rat := ((1322314959685451 : Rat) / 5000000000000000)
def block055S1 : Rat := ((18174751 : Rat) / 10000000)
def block055S2 : Rat := ((511587 : Rat) / 200000)
def block055S3 : Rat := ((107000619 : Rat) / 40000000)
def block055S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block055V (y : ℝ) : ℝ :=
  ratPotential block055W1 block055W2 block055W3 block055W4 block055S1 block055S2 block055S3 block055S4 y

def block055LeftParamsCertificate : Bool :=
  allBoxesSameParams block055LeftBoxes block055W1 block055W2 block055W3 block055W4 block055S1 block055S2 block055S3 block055S4

theorem block055LeftParamsCertificate_eq_true :
    block055LeftParamsCertificate = true := by
  native_decide

theorem block055_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block055LeftL : ℝ) (block055LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block055S1 : ℝ))
    (hy2ne : y ≠ (block055S2 : ℝ))
    (hy3ne : y ≠ (block055S3 : ℝ))
    (hy4ne : y ≠ (block055S4 : ℝ)) :
    0 < block055V y := by
  have hcert := block055LeftCertificate_eq_true
  unfold block055LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block055LeftBoxes) (lo := block055LeftL) (hi := block055LeftR)
    (w1 := block055W1) (w2 := block055W2) (w3 := block055W3) (w4 := block055W4)
    (s1 := block055S1) (s2 := block055S2) (s3 := block055S3) (s4 := block055S4)
    hboxes hcover block055LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block055RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block055RightChunk000 block055W1 block055W2 block055W3 block055W4 block055S1 block055S2 block055S3 block055S4

theorem block055RightChunk000ParamsCertificate_eq_true :
    block055RightChunk000ParamsCertificate = true := by
  native_decide

theorem block055_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block055RightChunk000L : ℝ) (block055RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block055S1 : ℝ))
    (hy2ne : y ≠ (block055S2 : ℝ))
    (hy3ne : y ≠ (block055S3 : ℝ))
    (hy4ne : y ≠ (block055S4 : ℝ)) :
    0 < block055V y := by
  have hcert := block055RightChunk000Certificate_eq_true
  unfold block055RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block055RightChunk000) (lo := block055RightChunk000L) (hi := block055RightChunk000R)
    (w1 := block055W1) (w2 := block055W2) (w3 := block055W3) (w4 := block055W4)
    (s1 := block055S1) (s2 := block055S2) (s3 := block055S3) (s4 := block055S4)
    hboxes hcover block055RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block055_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block055RightL : ℝ) (block055RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block055S1 : ℝ))
    (hy2ne : y ≠ (block055S2 : ℝ))
    (hy3ne : y ≠ (block055S3 : ℝ))
    (hy4ne : y ≠ (block055S4 : ℝ)) :
    0 < block055V y := by
  have hL : (block055RightChunk000L : ℝ) = (block055RightL : ℝ) := by
    norm_num [block055RightChunk000L, block055RightL]
  have hR : (block055RightChunk000R : ℝ) = (block055RightR : ℝ) := by
    norm_num [block055RightChunk000R, block055RightR]
  have hyc : y ∈ Icc (block055RightChunk000L : ℝ) (block055RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block055_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block055_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block055LeftL : ℝ) (block055LeftR : ℝ) →
    y ≠ 0 → y ≠ (block055S1 : ℝ) → y ≠ (block055S2 : ℝ) →
    y ≠ (block055S3 : ℝ) → y ≠ (block055S4 : ℝ) → 0 < block055V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block055RightL : ℝ) (block055RightR : ℝ) →
    y ≠ 0 → y ≠ (block055S1 : ℝ) → y ≠ (block055S2 : ℝ) →
    y ≠ (block055S3 : ℝ) → y ≠ (block055S4 : ℝ) → 0 < block055V y)

theorem block055_reallog_certificate_proof :
    block055_reallog_certificate := by
  exact ⟨block055_left_V_pos, block055_right_V_pos⟩

end Block055
end M1817475
end Erdos1038Lean
