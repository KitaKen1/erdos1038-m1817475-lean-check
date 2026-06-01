import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block365

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block365

open Set

def block365W1 : Rat := ((4385175594620171 : Rat) / 5000000000000000)
def block365W2 : Rat := ((4718283260655517 : Rat) / 100000000000000000)
def block365W3 : Rat := ((191919844960061 : Rat) / 1250000000000000)
def block365W4 : Rat := ((6963079232325303 : Rat) / 50000000000000000)
def block365S1 : Rat := ((18174751 : Rat) / 10000000)
def block365S2 : Rat := ((511587 : Rat) / 200000)
def block365S3 : Rat := ((132998133125000000033 : Rat) / 50000000000000000000)
def block365S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block365V (y : ℝ) : ℝ :=
  ratPotential block365W1 block365W2 block365W3 block365W4 block365S1 block365S2 block365S3 block365S4 y

def block365LeftParamsCertificate : Bool :=
  allBoxesSameParams block365LeftBoxes block365W1 block365W2 block365W3 block365W4 block365S1 block365S2 block365S3 block365S4

theorem block365LeftParamsCertificate_eq_true :
    block365LeftParamsCertificate = true := by
  native_decide

theorem block365_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block365LeftL : ℝ) (block365LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block365S1 : ℝ))
    (hy2ne : y ≠ (block365S2 : ℝ))
    (hy3ne : y ≠ (block365S3 : ℝ))
    (hy4ne : y ≠ (block365S4 : ℝ)) :
    0 < block365V y := by
  have hcert := block365LeftCertificate_eq_true
  unfold block365LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block365LeftBoxes) (lo := block365LeftL) (hi := block365LeftR)
    (w1 := block365W1) (w2 := block365W2) (w3 := block365W3) (w4 := block365W4)
    (s1 := block365S1) (s2 := block365S2) (s3 := block365S3) (s4 := block365S4)
    hboxes hcover block365LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block365RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block365RightChunk000 block365W1 block365W2 block365W3 block365W4 block365S1 block365S2 block365S3 block365S4

theorem block365RightChunk000ParamsCertificate_eq_true :
    block365RightChunk000ParamsCertificate = true := by
  native_decide

theorem block365_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block365RightChunk000L : ℝ) (block365RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block365S1 : ℝ))
    (hy2ne : y ≠ (block365S2 : ℝ))
    (hy3ne : y ≠ (block365S3 : ℝ))
    (hy4ne : y ≠ (block365S4 : ℝ)) :
    0 < block365V y := by
  have hcert := block365RightChunk000Certificate_eq_true
  unfold block365RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block365RightChunk000) (lo := block365RightChunk000L) (hi := block365RightChunk000R)
    (w1 := block365W1) (w2 := block365W2) (w3 := block365W3) (w4 := block365W4)
    (s1 := block365S1) (s2 := block365S2) (s3 := block365S3) (s4 := block365S4)
    hboxes hcover block365RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block365_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block365RightL : ℝ) (block365RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block365S1 : ℝ))
    (hy2ne : y ≠ (block365S2 : ℝ))
    (hy3ne : y ≠ (block365S3 : ℝ))
    (hy4ne : y ≠ (block365S4 : ℝ)) :
    0 < block365V y := by
  have hL : (block365RightChunk000L : ℝ) = (block365RightL : ℝ) := by
    norm_num [block365RightChunk000L, block365RightL]
  have hR : (block365RightChunk000R : ℝ) = (block365RightR : ℝ) := by
    norm_num [block365RightChunk000R, block365RightR]
  have hyc : y ∈ Icc (block365RightChunk000L : ℝ) (block365RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block365_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block365_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block365LeftL : ℝ) (block365LeftR : ℝ) →
    y ≠ 0 → y ≠ (block365S1 : ℝ) → y ≠ (block365S2 : ℝ) →
    y ≠ (block365S3 : ℝ) → y ≠ (block365S4 : ℝ) → 0 < block365V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block365RightL : ℝ) (block365RightR : ℝ) →
    y ≠ 0 → y ≠ (block365S1 : ℝ) → y ≠ (block365S2 : ℝ) →
    y ≠ (block365S3 : ℝ) → y ≠ (block365S4 : ℝ) → 0 < block365V y)

theorem block365_reallog_certificate_proof :
    block365_reallog_certificate := by
  exact ⟨block365_left_V_pos, block365_right_V_pos⟩

end Block365
end M1817475
end Erdos1038Lean
