import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block153

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block153

open Set

def block153W1 : Rat := ((2150590673129823 : Rat) / 1000000000000000)
def block153W2 : Rat := (0 : Rat)
def block153W3 : Rat := ((1710723400931659 : Rat) / 10000000000000000)
def block153W4 : Rat := ((1026914375764253 : Rat) / 12500000000000000)
def block153S1 : Rat := ((18174751 : Rat) / 10000000)
def block153S2 : Rat := ((511587 : Rat) / 200000)
def block153S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block153S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block153V (y : ℝ) : ℝ :=
  ratPotential block153W1 block153W2 block153W3 block153W4 block153S1 block153S2 block153S3 block153S4 y

def block153LeftParamsCertificate : Bool :=
  allBoxesSameParams block153LeftBoxes block153W1 block153W2 block153W3 block153W4 block153S1 block153S2 block153S3 block153S4

theorem block153LeftParamsCertificate_eq_true :
    block153LeftParamsCertificate = true := by
  native_decide

theorem block153_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block153LeftL : ℝ) (block153LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block153S1 : ℝ))
    (hy2ne : y ≠ (block153S2 : ℝ))
    (hy3ne : y ≠ (block153S3 : ℝ))
    (hy4ne : y ≠ (block153S4 : ℝ)) :
    0 < block153V y := by
  have hcert := block153LeftCertificate_eq_true
  unfold block153LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block153LeftBoxes) (lo := block153LeftL) (hi := block153LeftR)
    (w1 := block153W1) (w2 := block153W2) (w3 := block153W3) (w4 := block153W4)
    (s1 := block153S1) (s2 := block153S2) (s3 := block153S3) (s4 := block153S4)
    hboxes hcover block153LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block153RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block153RightChunk000 block153W1 block153W2 block153W3 block153W4 block153S1 block153S2 block153S3 block153S4

theorem block153RightChunk000ParamsCertificate_eq_true :
    block153RightChunk000ParamsCertificate = true := by
  native_decide

theorem block153_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block153RightChunk000L : ℝ) (block153RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block153S1 : ℝ))
    (hy2ne : y ≠ (block153S2 : ℝ))
    (hy3ne : y ≠ (block153S3 : ℝ))
    (hy4ne : y ≠ (block153S4 : ℝ)) :
    0 < block153V y := by
  have hcert := block153RightChunk000Certificate_eq_true
  unfold block153RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block153RightChunk000) (lo := block153RightChunk000L) (hi := block153RightChunk000R)
    (w1 := block153W1) (w2 := block153W2) (w3 := block153W3) (w4 := block153W4)
    (s1 := block153S1) (s2 := block153S2) (s3 := block153S3) (s4 := block153S4)
    hboxes hcover block153RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block153_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block153RightL : ℝ) (block153RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block153S1 : ℝ))
    (hy2ne : y ≠ (block153S2 : ℝ))
    (hy3ne : y ≠ (block153S3 : ℝ))
    (hy4ne : y ≠ (block153S4 : ℝ)) :
    0 < block153V y := by
  have hL : (block153RightChunk000L : ℝ) = (block153RightL : ℝ) := by
    norm_num [block153RightChunk000L, block153RightL]
  have hR : (block153RightChunk000R : ℝ) = (block153RightR : ℝ) := by
    norm_num [block153RightChunk000R, block153RightR]
  have hyc : y ∈ Icc (block153RightChunk000L : ℝ) (block153RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block153_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block153_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block153LeftL : ℝ) (block153LeftR : ℝ) →
    y ≠ 0 → y ≠ (block153S1 : ℝ) → y ≠ (block153S2 : ℝ) →
    y ≠ (block153S3 : ℝ) → y ≠ (block153S4 : ℝ) → 0 < block153V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block153RightL : ℝ) (block153RightR : ℝ) →
    y ≠ 0 → y ≠ (block153S1 : ℝ) → y ≠ (block153S2 : ℝ) →
    y ≠ (block153S3 : ℝ) → y ≠ (block153S4 : ℝ) → 0 < block153V y)

theorem block153_reallog_certificate_proof :
    block153_reallog_certificate := by
  exact ⟨block153_left_V_pos, block153_right_V_pos⟩

end Block153
end M1817475
end Erdos1038Lean
