import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block529

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block529

open Set

def block529W1 : Rat := ((2555373976446311 : Rat) / 6250000000000000)
def block529W2 : Rat := (0 : Rat)
def block529W3 : Rat := ((11295336568198551 : Rat) / 25000000000000000)
def block529W4 : Rat := (0 : Rat)
def block529S1 : Rat := ((18174751 : Rat) / 10000000)
def block529S2 : Rat := ((511587 : Rat) / 200000)
def block529S3 : Rat := ((25958415910714285749 : Rat) / 10000000000000000000)
def block529S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block529V (y : ℝ) : ℝ :=
  ratPotential block529W1 block529W2 block529W3 block529W4 block529S1 block529S2 block529S3 block529S4 y

def block529LeftParamsCertificate : Bool :=
  allBoxesSameParams block529LeftBoxes block529W1 block529W2 block529W3 block529W4 block529S1 block529S2 block529S3 block529S4

theorem block529LeftParamsCertificate_eq_true :
    block529LeftParamsCertificate = true := by
  native_decide

theorem block529_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block529LeftL : ℝ) (block529LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block529S1 : ℝ))
    (hy2ne : y ≠ (block529S2 : ℝ))
    (hy3ne : y ≠ (block529S3 : ℝ))
    (hy4ne : y ≠ (block529S4 : ℝ)) :
    0 < block529V y := by
  have hcert := block529LeftCertificate_eq_true
  unfold block529LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block529LeftBoxes) (lo := block529LeftL) (hi := block529LeftR)
    (w1 := block529W1) (w2 := block529W2) (w3 := block529W3) (w4 := block529W4)
    (s1 := block529S1) (s2 := block529S2) (s3 := block529S3) (s4 := block529S4)
    hboxes hcover block529LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block529RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block529RightChunk000 block529W1 block529W2 block529W3 block529W4 block529S1 block529S2 block529S3 block529S4

theorem block529RightChunk000ParamsCertificate_eq_true :
    block529RightChunk000ParamsCertificate = true := by
  native_decide

theorem block529_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block529RightChunk000L : ℝ) (block529RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block529S1 : ℝ))
    (hy2ne : y ≠ (block529S2 : ℝ))
    (hy3ne : y ≠ (block529S3 : ℝ))
    (hy4ne : y ≠ (block529S4 : ℝ)) :
    0 < block529V y := by
  have hcert := block529RightChunk000Certificate_eq_true
  unfold block529RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block529RightChunk000) (lo := block529RightChunk000L) (hi := block529RightChunk000R)
    (w1 := block529W1) (w2 := block529W2) (w3 := block529W3) (w4 := block529W4)
    (s1 := block529S1) (s2 := block529S2) (s3 := block529S3) (s4 := block529S4)
    hboxes hcover block529RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block529_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block529RightL : ℝ) (block529RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block529S1 : ℝ))
    (hy2ne : y ≠ (block529S2 : ℝ))
    (hy3ne : y ≠ (block529S3 : ℝ))
    (hy4ne : y ≠ (block529S4 : ℝ)) :
    0 < block529V y := by
  have hL : (block529RightChunk000L : ℝ) = (block529RightL : ℝ) := by
    norm_num [block529RightChunk000L, block529RightL]
  have hR : (block529RightChunk000R : ℝ) = (block529RightR : ℝ) := by
    norm_num [block529RightChunk000R, block529RightR]
  have hyc : y ∈ Icc (block529RightChunk000L : ℝ) (block529RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block529_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block529_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block529LeftL : ℝ) (block529LeftR : ℝ) →
    y ≠ 0 → y ≠ (block529S1 : ℝ) → y ≠ (block529S2 : ℝ) →
    y ≠ (block529S3 : ℝ) → y ≠ (block529S4 : ℝ) → 0 < block529V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block529RightL : ℝ) (block529RightR : ℝ) →
    y ≠ 0 → y ≠ (block529S1 : ℝ) → y ≠ (block529S2 : ℝ) →
    y ≠ (block529S3 : ℝ) → y ≠ (block529S4 : ℝ) → 0 < block529V y)

theorem block529_reallog_certificate_proof :
    block529_reallog_certificate := by
  exact ⟨block529_left_V_pos, block529_right_V_pos⟩

end Block529
end M1817475
end Erdos1038Lean
