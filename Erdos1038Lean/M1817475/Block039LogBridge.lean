import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block039

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block039

open Set

def block039W1 : Rat := ((500109613365779 : Rat) / 200000000000000)
def block039W2 : Rat := (0 : Rat)
def block039W3 : Rat := (0 : Rat)
def block039W4 : Rat := ((13842100683343947 : Rat) / 50000000000000000)
def block039S1 : Rat := ((18174751 : Rat) / 10000000)
def block039S2 : Rat := ((511587 : Rat) / 200000)
def block039S3 : Rat := ((107000619 : Rat) / 40000000)
def block039S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block039V (y : ℝ) : ℝ :=
  ratPotential block039W1 block039W2 block039W3 block039W4 block039S1 block039S2 block039S3 block039S4 y

def block039LeftParamsCertificate : Bool :=
  allBoxesSameParams block039LeftBoxes block039W1 block039W2 block039W3 block039W4 block039S1 block039S2 block039S3 block039S4

theorem block039LeftParamsCertificate_eq_true :
    block039LeftParamsCertificate = true := by
  native_decide

theorem block039_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block039LeftL : ℝ) (block039LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block039S1 : ℝ))
    (hy2ne : y ≠ (block039S2 : ℝ))
    (hy3ne : y ≠ (block039S3 : ℝ))
    (hy4ne : y ≠ (block039S4 : ℝ)) :
    0 < block039V y := by
  have hcert := block039LeftCertificate_eq_true
  unfold block039LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block039LeftBoxes) (lo := block039LeftL) (hi := block039LeftR)
    (w1 := block039W1) (w2 := block039W2) (w3 := block039W3) (w4 := block039W4)
    (s1 := block039S1) (s2 := block039S2) (s3 := block039S3) (s4 := block039S4)
    hboxes hcover block039LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block039RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block039RightChunk000 block039W1 block039W2 block039W3 block039W4 block039S1 block039S2 block039S3 block039S4

theorem block039RightChunk000ParamsCertificate_eq_true :
    block039RightChunk000ParamsCertificate = true := by
  native_decide

theorem block039_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block039RightChunk000L : ℝ) (block039RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block039S1 : ℝ))
    (hy2ne : y ≠ (block039S2 : ℝ))
    (hy3ne : y ≠ (block039S3 : ℝ))
    (hy4ne : y ≠ (block039S4 : ℝ)) :
    0 < block039V y := by
  have hcert := block039RightChunk000Certificate_eq_true
  unfold block039RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block039RightChunk000) (lo := block039RightChunk000L) (hi := block039RightChunk000R)
    (w1 := block039W1) (w2 := block039W2) (w3 := block039W3) (w4 := block039W4)
    (s1 := block039S1) (s2 := block039S2) (s3 := block039S3) (s4 := block039S4)
    hboxes hcover block039RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block039_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block039RightL : ℝ) (block039RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block039S1 : ℝ))
    (hy2ne : y ≠ (block039S2 : ℝ))
    (hy3ne : y ≠ (block039S3 : ℝ))
    (hy4ne : y ≠ (block039S4 : ℝ)) :
    0 < block039V y := by
  have hL : (block039RightChunk000L : ℝ) = (block039RightL : ℝ) := by
    norm_num [block039RightChunk000L, block039RightL]
  have hR : (block039RightChunk000R : ℝ) = (block039RightR : ℝ) := by
    norm_num [block039RightChunk000R, block039RightR]
  have hyc : y ∈ Icc (block039RightChunk000L : ℝ) (block039RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block039_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block039_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block039LeftL : ℝ) (block039LeftR : ℝ) →
    y ≠ 0 → y ≠ (block039S1 : ℝ) → y ≠ (block039S2 : ℝ) →
    y ≠ (block039S3 : ℝ) → y ≠ (block039S4 : ℝ) → 0 < block039V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block039RightL : ℝ) (block039RightR : ℝ) →
    y ≠ 0 → y ≠ (block039S1 : ℝ) → y ≠ (block039S2 : ℝ) →
    y ≠ (block039S3 : ℝ) → y ≠ (block039S4 : ℝ) → 0 < block039V y)

theorem block039_reallog_certificate_proof :
    block039_reallog_certificate := by
  exact ⟨block039_left_V_pos, block039_right_V_pos⟩

end Block039
end M1817475
end Erdos1038Lean
