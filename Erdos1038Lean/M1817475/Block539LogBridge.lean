import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block539

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block539

open Set

def block539W1 : Rat := ((39863705330847393 : Rat) / 100000000000000000)
def block539W2 : Rat := (0 : Rat)
def block539W3 : Rat := ((1139030951178799 : Rat) / 2500000000000000)
def block539W4 : Rat := (0 : Rat)
def block539S1 : Rat := ((18174751 : Rat) / 10000000)
def block539S2 : Rat := ((511587 : Rat) / 200000)
def block539S3 : Rat := ((5183863539285714293 : Rat) / 2000000000000000000)
def block539S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block539V (y : ℝ) : ℝ :=
  ratPotential block539W1 block539W2 block539W3 block539W4 block539S1 block539S2 block539S3 block539S4 y

def block539LeftParamsCertificate : Bool :=
  allBoxesSameParams block539LeftBoxes block539W1 block539W2 block539W3 block539W4 block539S1 block539S2 block539S3 block539S4

theorem block539LeftParamsCertificate_eq_true :
    block539LeftParamsCertificate = true := by
  native_decide

theorem block539_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block539LeftL : ℝ) (block539LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block539S1 : ℝ))
    (hy2ne : y ≠ (block539S2 : ℝ))
    (hy3ne : y ≠ (block539S3 : ℝ))
    (hy4ne : y ≠ (block539S4 : ℝ)) :
    0 < block539V y := by
  have hcert := block539LeftCertificate_eq_true
  unfold block539LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block539LeftBoxes) (lo := block539LeftL) (hi := block539LeftR)
    (w1 := block539W1) (w2 := block539W2) (w3 := block539W3) (w4 := block539W4)
    (s1 := block539S1) (s2 := block539S2) (s3 := block539S3) (s4 := block539S4)
    hboxes hcover block539LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block539RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block539RightChunk000 block539W1 block539W2 block539W3 block539W4 block539S1 block539S2 block539S3 block539S4

theorem block539RightChunk000ParamsCertificate_eq_true :
    block539RightChunk000ParamsCertificate = true := by
  native_decide

theorem block539_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block539RightChunk000L : ℝ) (block539RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block539S1 : ℝ))
    (hy2ne : y ≠ (block539S2 : ℝ))
    (hy3ne : y ≠ (block539S3 : ℝ))
    (hy4ne : y ≠ (block539S4 : ℝ)) :
    0 < block539V y := by
  have hcert := block539RightChunk000Certificate_eq_true
  unfold block539RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block539RightChunk000) (lo := block539RightChunk000L) (hi := block539RightChunk000R)
    (w1 := block539W1) (w2 := block539W2) (w3 := block539W3) (w4 := block539W4)
    (s1 := block539S1) (s2 := block539S2) (s3 := block539S3) (s4 := block539S4)
    hboxes hcover block539RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block539_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block539RightL : ℝ) (block539RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block539S1 : ℝ))
    (hy2ne : y ≠ (block539S2 : ℝ))
    (hy3ne : y ≠ (block539S3 : ℝ))
    (hy4ne : y ≠ (block539S4 : ℝ)) :
    0 < block539V y := by
  have hL : (block539RightChunk000L : ℝ) = (block539RightL : ℝ) := by
    norm_num [block539RightChunk000L, block539RightL]
  have hR : (block539RightChunk000R : ℝ) = (block539RightR : ℝ) := by
    norm_num [block539RightChunk000R, block539RightR]
  have hyc : y ∈ Icc (block539RightChunk000L : ℝ) (block539RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block539_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block539_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block539LeftL : ℝ) (block539LeftR : ℝ) →
    y ≠ 0 → y ≠ (block539S1 : ℝ) → y ≠ (block539S2 : ℝ) →
    y ≠ (block539S3 : ℝ) → y ≠ (block539S4 : ℝ) → 0 < block539V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block539RightL : ℝ) (block539RightR : ℝ) →
    y ≠ 0 → y ≠ (block539S1 : ℝ) → y ≠ (block539S2 : ℝ) →
    y ≠ (block539S3 : ℝ) → y ≠ (block539S4 : ℝ) → 0 < block539V y)

theorem block539_reallog_certificate_proof :
    block539_reallog_certificate := by
  exact ⟨block539_left_V_pos, block539_right_V_pos⟩

end Block539
end M1817475
end Erdos1038Lean
