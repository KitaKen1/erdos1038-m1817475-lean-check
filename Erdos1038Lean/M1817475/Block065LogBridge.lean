import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block065

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block065

open Set

def block065W1 : Rat := ((23731481791951 : Rat) / 8000000000000)
def block065W2 : Rat := (0 : Rat)
def block065W3 : Rat := (0 : Rat)
def block065W4 : Rat := ((5119942273001269 : Rat) / 20000000000000000)
def block065S1 : Rat := ((18174751 : Rat) / 10000000)
def block065S2 : Rat := ((511587 : Rat) / 200000)
def block065S3 : Rat := ((107000619 : Rat) / 40000000)
def block065S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block065V (y : ℝ) : ℝ :=
  ratPotential block065W1 block065W2 block065W3 block065W4 block065S1 block065S2 block065S3 block065S4 y

def block065LeftParamsCertificate : Bool :=
  allBoxesSameParams block065LeftBoxes block065W1 block065W2 block065W3 block065W4 block065S1 block065S2 block065S3 block065S4

theorem block065LeftParamsCertificate_eq_true :
    block065LeftParamsCertificate = true := by
  native_decide

theorem block065_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block065LeftL : ℝ) (block065LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block065S1 : ℝ))
    (hy2ne : y ≠ (block065S2 : ℝ))
    (hy3ne : y ≠ (block065S3 : ℝ))
    (hy4ne : y ≠ (block065S4 : ℝ)) :
    0 < block065V y := by
  have hcert := block065LeftCertificate_eq_true
  unfold block065LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block065LeftBoxes) (lo := block065LeftL) (hi := block065LeftR)
    (w1 := block065W1) (w2 := block065W2) (w3 := block065W3) (w4 := block065W4)
    (s1 := block065S1) (s2 := block065S2) (s3 := block065S3) (s4 := block065S4)
    hboxes hcover block065LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block065RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block065RightChunk000 block065W1 block065W2 block065W3 block065W4 block065S1 block065S2 block065S3 block065S4

theorem block065RightChunk000ParamsCertificate_eq_true :
    block065RightChunk000ParamsCertificate = true := by
  native_decide

theorem block065_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block065RightChunk000L : ℝ) (block065RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block065S1 : ℝ))
    (hy2ne : y ≠ (block065S2 : ℝ))
    (hy3ne : y ≠ (block065S3 : ℝ))
    (hy4ne : y ≠ (block065S4 : ℝ)) :
    0 < block065V y := by
  have hcert := block065RightChunk000Certificate_eq_true
  unfold block065RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block065RightChunk000) (lo := block065RightChunk000L) (hi := block065RightChunk000R)
    (w1 := block065W1) (w2 := block065W2) (w3 := block065W3) (w4 := block065W4)
    (s1 := block065S1) (s2 := block065S2) (s3 := block065S3) (s4 := block065S4)
    hboxes hcover block065RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block065_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block065RightL : ℝ) (block065RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block065S1 : ℝ))
    (hy2ne : y ≠ (block065S2 : ℝ))
    (hy3ne : y ≠ (block065S3 : ℝ))
    (hy4ne : y ≠ (block065S4 : ℝ)) :
    0 < block065V y := by
  have hL : (block065RightChunk000L : ℝ) = (block065RightL : ℝ) := by
    norm_num [block065RightChunk000L, block065RightL]
  have hR : (block065RightChunk000R : ℝ) = (block065RightR : ℝ) := by
    norm_num [block065RightChunk000R, block065RightR]
  have hyc : y ∈ Icc (block065RightChunk000L : ℝ) (block065RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block065_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block065_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block065LeftL : ℝ) (block065LeftR : ℝ) →
    y ≠ 0 → y ≠ (block065S1 : ℝ) → y ≠ (block065S2 : ℝ) →
    y ≠ (block065S3 : ℝ) → y ≠ (block065S4 : ℝ) → 0 < block065V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block065RightL : ℝ) (block065RightR : ℝ) →
    y ≠ 0 → y ≠ (block065S1 : ℝ) → y ≠ (block065S2 : ℝ) →
    y ≠ (block065S3 : ℝ) → y ≠ (block065S4 : ℝ) → 0 < block065V y)

theorem block065_reallog_certificate_proof :
    block065_reallog_certificate := by
  exact ⟨block065_left_V_pos, block065_right_V_pos⟩

end Block065
end M1817475
end Erdos1038Lean
