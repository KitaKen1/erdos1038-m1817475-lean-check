import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block032

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block032

open Set

def block032W1 : Rat := ((23994216624151767 : Rat) / 10000000000000000)
def block032W2 : Rat := (0 : Rat)
def block032W3 : Rat := (0 : Rat)
def block032W4 : Rat := ((14093943751902477 : Rat) / 50000000000000000)
def block032S1 : Rat := ((18174751 : Rat) / 10000000)
def block032S2 : Rat := ((511587 : Rat) / 200000)
def block032S3 : Rat := ((107000619 : Rat) / 40000000)
def block032S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block032V (y : ℝ) : ℝ :=
  ratPotential block032W1 block032W2 block032W3 block032W4 block032S1 block032S2 block032S3 block032S4 y

def block032LeftParamsCertificate : Bool :=
  allBoxesSameParams block032LeftBoxes block032W1 block032W2 block032W3 block032W4 block032S1 block032S2 block032S3 block032S4

theorem block032LeftParamsCertificate_eq_true :
    block032LeftParamsCertificate = true := by
  native_decide

theorem block032_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block032LeftL : ℝ) (block032LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block032S1 : ℝ))
    (hy2ne : y ≠ (block032S2 : ℝ))
    (hy3ne : y ≠ (block032S3 : ℝ))
    (hy4ne : y ≠ (block032S4 : ℝ)) :
    0 < block032V y := by
  have hcert := block032LeftCertificate_eq_true
  unfold block032LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block032LeftBoxes) (lo := block032LeftL) (hi := block032LeftR)
    (w1 := block032W1) (w2 := block032W2) (w3 := block032W3) (w4 := block032W4)
    (s1 := block032S1) (s2 := block032S2) (s3 := block032S3) (s4 := block032S4)
    hboxes hcover block032LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block032RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block032RightChunk000 block032W1 block032W2 block032W3 block032W4 block032S1 block032S2 block032S3 block032S4

theorem block032RightChunk000ParamsCertificate_eq_true :
    block032RightChunk000ParamsCertificate = true := by
  native_decide

theorem block032_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block032RightChunk000L : ℝ) (block032RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block032S1 : ℝ))
    (hy2ne : y ≠ (block032S2 : ℝ))
    (hy3ne : y ≠ (block032S3 : ℝ))
    (hy4ne : y ≠ (block032S4 : ℝ)) :
    0 < block032V y := by
  have hcert := block032RightChunk000Certificate_eq_true
  unfold block032RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block032RightChunk000) (lo := block032RightChunk000L) (hi := block032RightChunk000R)
    (w1 := block032W1) (w2 := block032W2) (w3 := block032W3) (w4 := block032W4)
    (s1 := block032S1) (s2 := block032S2) (s3 := block032S3) (s4 := block032S4)
    hboxes hcover block032RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block032_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block032RightL : ℝ) (block032RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block032S1 : ℝ))
    (hy2ne : y ≠ (block032S2 : ℝ))
    (hy3ne : y ≠ (block032S3 : ℝ))
    (hy4ne : y ≠ (block032S4 : ℝ)) :
    0 < block032V y := by
  have hL : (block032RightChunk000L : ℝ) = (block032RightL : ℝ) := by
    norm_num [block032RightChunk000L, block032RightL]
  have hR : (block032RightChunk000R : ℝ) = (block032RightR : ℝ) := by
    norm_num [block032RightChunk000R, block032RightR]
  have hyc : y ∈ Icc (block032RightChunk000L : ℝ) (block032RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block032_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block032_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block032LeftL : ℝ) (block032LeftR : ℝ) →
    y ≠ 0 → y ≠ (block032S1 : ℝ) → y ≠ (block032S2 : ℝ) →
    y ≠ (block032S3 : ℝ) → y ≠ (block032S4 : ℝ) → 0 < block032V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block032RightL : ℝ) (block032RightR : ℝ) →
    y ≠ 0 → y ≠ (block032S1 : ℝ) → y ≠ (block032S2 : ℝ) →
    y ≠ (block032S3 : ℝ) → y ≠ (block032S4 : ℝ) → 0 < block032V y)

theorem block032_reallog_certificate_proof :
    block032_reallog_certificate := by
  exact ⟨block032_left_V_pos, block032_right_V_pos⟩

end Block032
end M1817475
end Erdos1038Lean
