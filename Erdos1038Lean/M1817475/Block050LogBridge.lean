import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block050

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block050

open Set

def block050W1 : Rat := ((5356250835502177 : Rat) / 2000000000000000)
def block050W2 : Rat := (0 : Rat)
def block050W3 : Rat := (0 : Rat)
def block050W4 : Rat := ((26847315610469197 : Rat) / 100000000000000000)
def block050S1 : Rat := ((18174751 : Rat) / 10000000)
def block050S2 : Rat := ((511587 : Rat) / 200000)
def block050S3 : Rat := ((107000619 : Rat) / 40000000)
def block050S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block050V (y : ℝ) : ℝ :=
  ratPotential block050W1 block050W2 block050W3 block050W4 block050S1 block050S2 block050S3 block050S4 y

def block050LeftParamsCertificate : Bool :=
  allBoxesSameParams block050LeftBoxes block050W1 block050W2 block050W3 block050W4 block050S1 block050S2 block050S3 block050S4

theorem block050LeftParamsCertificate_eq_true :
    block050LeftParamsCertificate = true := by
  native_decide

theorem block050_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block050LeftL : ℝ) (block050LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block050S1 : ℝ))
    (hy2ne : y ≠ (block050S2 : ℝ))
    (hy3ne : y ≠ (block050S3 : ℝ))
    (hy4ne : y ≠ (block050S4 : ℝ)) :
    0 < block050V y := by
  have hcert := block050LeftCertificate_eq_true
  unfold block050LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block050LeftBoxes) (lo := block050LeftL) (hi := block050LeftR)
    (w1 := block050W1) (w2 := block050W2) (w3 := block050W3) (w4 := block050W4)
    (s1 := block050S1) (s2 := block050S2) (s3 := block050S3) (s4 := block050S4)
    hboxes hcover block050LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block050RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block050RightChunk000 block050W1 block050W2 block050W3 block050W4 block050S1 block050S2 block050S3 block050S4

theorem block050RightChunk000ParamsCertificate_eq_true :
    block050RightChunk000ParamsCertificate = true := by
  native_decide

theorem block050_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block050RightChunk000L : ℝ) (block050RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block050S1 : ℝ))
    (hy2ne : y ≠ (block050S2 : ℝ))
    (hy3ne : y ≠ (block050S3 : ℝ))
    (hy4ne : y ≠ (block050S4 : ℝ)) :
    0 < block050V y := by
  have hcert := block050RightChunk000Certificate_eq_true
  unfold block050RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block050RightChunk000) (lo := block050RightChunk000L) (hi := block050RightChunk000R)
    (w1 := block050W1) (w2 := block050W2) (w3 := block050W3) (w4 := block050W4)
    (s1 := block050S1) (s2 := block050S2) (s3 := block050S3) (s4 := block050S4)
    hboxes hcover block050RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block050_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block050RightL : ℝ) (block050RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block050S1 : ℝ))
    (hy2ne : y ≠ (block050S2 : ℝ))
    (hy3ne : y ≠ (block050S3 : ℝ))
    (hy4ne : y ≠ (block050S4 : ℝ)) :
    0 < block050V y := by
  have hL : (block050RightChunk000L : ℝ) = (block050RightL : ℝ) := by
    norm_num [block050RightChunk000L, block050RightL]
  have hR : (block050RightChunk000R : ℝ) = (block050RightR : ℝ) := by
    norm_num [block050RightChunk000R, block050RightR]
  have hyc : y ∈ Icc (block050RightChunk000L : ℝ) (block050RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block050_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block050_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block050LeftL : ℝ) (block050LeftR : ℝ) →
    y ≠ 0 → y ≠ (block050S1 : ℝ) → y ≠ (block050S2 : ℝ) →
    y ≠ (block050S3 : ℝ) → y ≠ (block050S4 : ℝ) → 0 < block050V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block050RightL : ℝ) (block050RightR : ℝ) →
    y ≠ 0 → y ≠ (block050S1 : ℝ) → y ≠ (block050S2 : ℝ) →
    y ≠ (block050S3 : ℝ) → y ≠ (block050S4 : ℝ) → 0 < block050V y)

theorem block050_reallog_certificate_proof :
    block050_reallog_certificate := by
  exact ⟨block050_left_V_pos, block050_right_V_pos⟩

end Block050
end M1817475
end Erdos1038Lean
