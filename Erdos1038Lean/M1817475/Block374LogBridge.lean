import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block374

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block374

open Set

def block374W1 : Rat := ((4302110285965343 : Rat) / 5000000000000000)
def block374W2 : Rat := ((4690307221895797 : Rat) / 100000000000000000)
def block374W3 : Rat := ((7805681711712567 : Rat) / 50000000000000000)
def block374W4 : Rat := ((2800603080335723 : Rat) / 20000000000000000)
def block374S1 : Rat := ((18174751 : Rat) / 10000000)
def block374S2 : Rat := ((511587 : Rat) / 200000)
def block374S3 : Rat := ((26564438232142857151 : Rat) / 10000000000000000000)
def block374S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block374V (y : ℝ) : ℝ :=
  ratPotential block374W1 block374W2 block374W3 block374W4 block374S1 block374S2 block374S3 block374S4 y

def block374LeftParamsCertificate : Bool :=
  allBoxesSameParams block374LeftBoxes block374W1 block374W2 block374W3 block374W4 block374S1 block374S2 block374S3 block374S4

theorem block374LeftParamsCertificate_eq_true :
    block374LeftParamsCertificate = true := by
  native_decide

theorem block374_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block374LeftL : ℝ) (block374LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block374S1 : ℝ))
    (hy2ne : y ≠ (block374S2 : ℝ))
    (hy3ne : y ≠ (block374S3 : ℝ))
    (hy4ne : y ≠ (block374S4 : ℝ)) :
    0 < block374V y := by
  have hcert := block374LeftCertificate_eq_true
  unfold block374LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block374LeftBoxes) (lo := block374LeftL) (hi := block374LeftR)
    (w1 := block374W1) (w2 := block374W2) (w3 := block374W3) (w4 := block374W4)
    (s1 := block374S1) (s2 := block374S2) (s3 := block374S3) (s4 := block374S4)
    hboxes hcover block374LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block374RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block374RightChunk000 block374W1 block374W2 block374W3 block374W4 block374S1 block374S2 block374S3 block374S4

theorem block374RightChunk000ParamsCertificate_eq_true :
    block374RightChunk000ParamsCertificate = true := by
  native_decide

theorem block374_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block374RightChunk000L : ℝ) (block374RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block374S1 : ℝ))
    (hy2ne : y ≠ (block374S2 : ℝ))
    (hy3ne : y ≠ (block374S3 : ℝ))
    (hy4ne : y ≠ (block374S4 : ℝ)) :
    0 < block374V y := by
  have hcert := block374RightChunk000Certificate_eq_true
  unfold block374RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block374RightChunk000) (lo := block374RightChunk000L) (hi := block374RightChunk000R)
    (w1 := block374W1) (w2 := block374W2) (w3 := block374W3) (w4 := block374W4)
    (s1 := block374S1) (s2 := block374S2) (s3 := block374S3) (s4 := block374S4)
    hboxes hcover block374RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block374_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block374RightL : ℝ) (block374RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block374S1 : ℝ))
    (hy2ne : y ≠ (block374S2 : ℝ))
    (hy3ne : y ≠ (block374S3 : ℝ))
    (hy4ne : y ≠ (block374S4 : ℝ)) :
    0 < block374V y := by
  have hL : (block374RightChunk000L : ℝ) = (block374RightL : ℝ) := by
    norm_num [block374RightChunk000L, block374RightL]
  have hR : (block374RightChunk000R : ℝ) = (block374RightR : ℝ) := by
    norm_num [block374RightChunk000R, block374RightR]
  have hyc : y ∈ Icc (block374RightChunk000L : ℝ) (block374RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block374_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block374_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block374LeftL : ℝ) (block374LeftR : ℝ) →
    y ≠ 0 → y ≠ (block374S1 : ℝ) → y ≠ (block374S2 : ℝ) →
    y ≠ (block374S3 : ℝ) → y ≠ (block374S4 : ℝ) → 0 < block374V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block374RightL : ℝ) (block374RightR : ℝ) →
    y ≠ 0 → y ≠ (block374S1 : ℝ) → y ≠ (block374S2 : ℝ) →
    y ≠ (block374S3 : ℝ) → y ≠ (block374S4 : ℝ) → 0 < block374V y)

theorem block374_reallog_certificate_proof :
    block374_reallog_certificate := by
  exact ⟨block374_left_V_pos, block374_right_V_pos⟩

end Block374
end M1817475
end Erdos1038Lean
