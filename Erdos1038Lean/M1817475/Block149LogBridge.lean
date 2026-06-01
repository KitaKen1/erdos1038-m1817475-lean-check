import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block149

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block149

open Set

def block149W1 : Rat := ((276348077213021 : Rat) / 125000000000000)
def block149W2 : Rat := (0 : Rat)
def block149W3 : Rat := ((81464561082579 : Rat) / 500000000000000)
def block149W4 : Rat := ((8770255509541919 : Rat) / 100000000000000000)
def block149S1 : Rat := ((18174751 : Rat) / 10000000)
def block149S2 : Rat := ((511587 : Rat) / 200000)
def block149S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block149S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block149V (y : ℝ) : ℝ :=
  ratPotential block149W1 block149W2 block149W3 block149W4 block149S1 block149S2 block149S3 block149S4 y

def block149LeftParamsCertificate : Bool :=
  allBoxesSameParams block149LeftBoxes block149W1 block149W2 block149W3 block149W4 block149S1 block149S2 block149S3 block149S4

theorem block149LeftParamsCertificate_eq_true :
    block149LeftParamsCertificate = true := by
  native_decide

theorem block149_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block149LeftL : ℝ) (block149LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block149S1 : ℝ))
    (hy2ne : y ≠ (block149S2 : ℝ))
    (hy3ne : y ≠ (block149S3 : ℝ))
    (hy4ne : y ≠ (block149S4 : ℝ)) :
    0 < block149V y := by
  have hcert := block149LeftCertificate_eq_true
  unfold block149LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block149LeftBoxes) (lo := block149LeftL) (hi := block149LeftR)
    (w1 := block149W1) (w2 := block149W2) (w3 := block149W3) (w4 := block149W4)
    (s1 := block149S1) (s2 := block149S2) (s3 := block149S3) (s4 := block149S4)
    hboxes hcover block149LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block149RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block149RightChunk000 block149W1 block149W2 block149W3 block149W4 block149S1 block149S2 block149S3 block149S4

theorem block149RightChunk000ParamsCertificate_eq_true :
    block149RightChunk000ParamsCertificate = true := by
  native_decide

theorem block149_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block149RightChunk000L : ℝ) (block149RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block149S1 : ℝ))
    (hy2ne : y ≠ (block149S2 : ℝ))
    (hy3ne : y ≠ (block149S3 : ℝ))
    (hy4ne : y ≠ (block149S4 : ℝ)) :
    0 < block149V y := by
  have hcert := block149RightChunk000Certificate_eq_true
  unfold block149RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block149RightChunk000) (lo := block149RightChunk000L) (hi := block149RightChunk000R)
    (w1 := block149W1) (w2 := block149W2) (w3 := block149W3) (w4 := block149W4)
    (s1 := block149S1) (s2 := block149S2) (s3 := block149S3) (s4 := block149S4)
    hboxes hcover block149RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block149_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block149RightL : ℝ) (block149RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block149S1 : ℝ))
    (hy2ne : y ≠ (block149S2 : ℝ))
    (hy3ne : y ≠ (block149S3 : ℝ))
    (hy4ne : y ≠ (block149S4 : ℝ)) :
    0 < block149V y := by
  have hL : (block149RightChunk000L : ℝ) = (block149RightL : ℝ) := by
    norm_num [block149RightChunk000L, block149RightL]
  have hR : (block149RightChunk000R : ℝ) = (block149RightR : ℝ) := by
    norm_num [block149RightChunk000R, block149RightR]
  have hyc : y ∈ Icc (block149RightChunk000L : ℝ) (block149RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block149_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block149_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block149LeftL : ℝ) (block149LeftR : ℝ) →
    y ≠ 0 → y ≠ (block149S1 : ℝ) → y ≠ (block149S2 : ℝ) →
    y ≠ (block149S3 : ℝ) → y ≠ (block149S4 : ℝ) → 0 < block149V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block149RightL : ℝ) (block149RightR : ℝ) →
    y ≠ 0 → y ≠ (block149S1 : ℝ) → y ≠ (block149S2 : ℝ) →
    y ≠ (block149S3 : ℝ) → y ≠ (block149S4 : ℝ) → 0 < block149V y)

theorem block149_reallog_certificate_proof :
    block149_reallog_certificate := by
  exact ⟨block149_left_V_pos, block149_right_V_pos⟩

end Block149
end M1817475
end Erdos1038Lean
