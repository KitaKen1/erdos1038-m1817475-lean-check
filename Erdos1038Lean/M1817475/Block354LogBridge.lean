import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block354

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block354

open Set

def block354W1 : Rat := ((8981828514220107 : Rat) / 10000000000000000)
def block354W2 : Rat := ((4755536156841607 : Rat) / 100000000000000000)
def block354W3 : Rat := ((15001305437149837 : Rat) / 100000000000000000)
def block354W4 : Rat := ((1732450594830973 : Rat) / 12500000000000000)
def block354S1 : Rat := ((18174751 : Rat) / 10000000)
def block354S2 : Rat := ((511587 : Rat) / 200000)
def block354S3 : Rat := ((26642634660714285719 : Rat) / 10000000000000000000)
def block354S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block354V (y : ℝ) : ℝ :=
  ratPotential block354W1 block354W2 block354W3 block354W4 block354S1 block354S2 block354S3 block354S4 y

def block354LeftParamsCertificate : Bool :=
  allBoxesSameParams block354LeftBoxes block354W1 block354W2 block354W3 block354W4 block354S1 block354S2 block354S3 block354S4

theorem block354LeftParamsCertificate_eq_true :
    block354LeftParamsCertificate = true := by
  native_decide

theorem block354_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block354LeftL : ℝ) (block354LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block354S1 : ℝ))
    (hy2ne : y ≠ (block354S2 : ℝ))
    (hy3ne : y ≠ (block354S3 : ℝ))
    (hy4ne : y ≠ (block354S4 : ℝ)) :
    0 < block354V y := by
  have hcert := block354LeftCertificate_eq_true
  unfold block354LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block354LeftBoxes) (lo := block354LeftL) (hi := block354LeftR)
    (w1 := block354W1) (w2 := block354W2) (w3 := block354W3) (w4 := block354W4)
    (s1 := block354S1) (s2 := block354S2) (s3 := block354S3) (s4 := block354S4)
    hboxes hcover block354LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block354RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block354RightChunk000 block354W1 block354W2 block354W3 block354W4 block354S1 block354S2 block354S3 block354S4

theorem block354RightChunk000ParamsCertificate_eq_true :
    block354RightChunk000ParamsCertificate = true := by
  native_decide

theorem block354_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block354RightChunk000L : ℝ) (block354RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block354S1 : ℝ))
    (hy2ne : y ≠ (block354S2 : ℝ))
    (hy3ne : y ≠ (block354S3 : ℝ))
    (hy4ne : y ≠ (block354S4 : ℝ)) :
    0 < block354V y := by
  have hcert := block354RightChunk000Certificate_eq_true
  unfold block354RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block354RightChunk000) (lo := block354RightChunk000L) (hi := block354RightChunk000R)
    (w1 := block354W1) (w2 := block354W2) (w3 := block354W3) (w4 := block354W4)
    (s1 := block354S1) (s2 := block354S2) (s3 := block354S3) (s4 := block354S4)
    hboxes hcover block354RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block354_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block354RightL : ℝ) (block354RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block354S1 : ℝ))
    (hy2ne : y ≠ (block354S2 : ℝ))
    (hy3ne : y ≠ (block354S3 : ℝ))
    (hy4ne : y ≠ (block354S4 : ℝ)) :
    0 < block354V y := by
  have hL : (block354RightChunk000L : ℝ) = (block354RightL : ℝ) := by
    norm_num [block354RightChunk000L, block354RightL]
  have hR : (block354RightChunk000R : ℝ) = (block354RightR : ℝ) := by
    norm_num [block354RightChunk000R, block354RightR]
  have hyc : y ∈ Icc (block354RightChunk000L : ℝ) (block354RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block354_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block354_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block354LeftL : ℝ) (block354LeftR : ℝ) →
    y ≠ 0 → y ≠ (block354S1 : ℝ) → y ≠ (block354S2 : ℝ) →
    y ≠ (block354S3 : ℝ) → y ≠ (block354S4 : ℝ) → 0 < block354V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block354RightL : ℝ) (block354RightR : ℝ) →
    y ≠ 0 → y ≠ (block354S1 : ℝ) → y ≠ (block354S2 : ℝ) →
    y ≠ (block354S3 : ℝ) → y ≠ (block354S4 : ℝ) → 0 < block354V y)

theorem block354_reallog_certificate_proof :
    block354_reallog_certificate := by
  exact ⟨block354_left_V_pos, block354_right_V_pos⟩

end Block354
end M1817475
end Erdos1038Lean
