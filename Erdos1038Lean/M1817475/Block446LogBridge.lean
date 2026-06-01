import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block446

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block446

open Set

def block446W1 : Rat := ((3044482177346239 : Rat) / 5000000000000000)
def block446W2 : Rat := (0 : Rat)
def block446W3 : Rat := ((1638832147587969 : Rat) / 5000000000000000)
def block446W4 : Rat := ((3493931264385431 : Rat) / 50000000000000000)
def block446S1 : Rat := ((18174751 : Rat) / 10000000)
def block446S2 : Rat := ((511587 : Rat) / 200000)
def block446S3 : Rat := ((131414655446428571531 : Rat) / 50000000000000000000)
def block446S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block446V (y : ℝ) : ℝ :=
  ratPotential block446W1 block446W2 block446W3 block446W4 block446S1 block446S2 block446S3 block446S4 y

def block446LeftParamsCertificate : Bool :=
  allBoxesSameParams block446LeftBoxes block446W1 block446W2 block446W3 block446W4 block446S1 block446S2 block446S3 block446S4

theorem block446LeftParamsCertificate_eq_true :
    block446LeftParamsCertificate = true := by
  native_decide

theorem block446_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block446LeftL : ℝ) (block446LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block446S1 : ℝ))
    (hy2ne : y ≠ (block446S2 : ℝ))
    (hy3ne : y ≠ (block446S3 : ℝ))
    (hy4ne : y ≠ (block446S4 : ℝ)) :
    0 < block446V y := by
  have hcert := block446LeftCertificate_eq_true
  unfold block446LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block446LeftBoxes) (lo := block446LeftL) (hi := block446LeftR)
    (w1 := block446W1) (w2 := block446W2) (w3 := block446W3) (w4 := block446W4)
    (s1 := block446S1) (s2 := block446S2) (s3 := block446S3) (s4 := block446S4)
    hboxes hcover block446LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block446RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block446RightChunk000 block446W1 block446W2 block446W3 block446W4 block446S1 block446S2 block446S3 block446S4

theorem block446RightChunk000ParamsCertificate_eq_true :
    block446RightChunk000ParamsCertificate = true := by
  native_decide

theorem block446_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block446RightChunk000L : ℝ) (block446RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block446S1 : ℝ))
    (hy2ne : y ≠ (block446S2 : ℝ))
    (hy3ne : y ≠ (block446S3 : ℝ))
    (hy4ne : y ≠ (block446S4 : ℝ)) :
    0 < block446V y := by
  have hcert := block446RightChunk000Certificate_eq_true
  unfold block446RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block446RightChunk000) (lo := block446RightChunk000L) (hi := block446RightChunk000R)
    (w1 := block446W1) (w2 := block446W2) (w3 := block446W3) (w4 := block446W4)
    (s1 := block446S1) (s2 := block446S2) (s3 := block446S3) (s4 := block446S4)
    hboxes hcover block446RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block446_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block446RightL : ℝ) (block446RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block446S1 : ℝ))
    (hy2ne : y ≠ (block446S2 : ℝ))
    (hy3ne : y ≠ (block446S3 : ℝ))
    (hy4ne : y ≠ (block446S4 : ℝ)) :
    0 < block446V y := by
  have hL : (block446RightChunk000L : ℝ) = (block446RightL : ℝ) := by
    norm_num [block446RightChunk000L, block446RightL]
  have hR : (block446RightChunk000R : ℝ) = (block446RightR : ℝ) := by
    norm_num [block446RightChunk000R, block446RightR]
  have hyc : y ∈ Icc (block446RightChunk000L : ℝ) (block446RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block446_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block446_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block446LeftL : ℝ) (block446LeftR : ℝ) →
    y ≠ 0 → y ≠ (block446S1 : ℝ) → y ≠ (block446S2 : ℝ) →
    y ≠ (block446S3 : ℝ) → y ≠ (block446S4 : ℝ) → 0 < block446V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block446RightL : ℝ) (block446RightR : ℝ) →
    y ≠ 0 → y ≠ (block446S1 : ℝ) → y ≠ (block446S2 : ℝ) →
    y ≠ (block446S3 : ℝ) → y ≠ (block446S4 : ℝ) → 0 < block446V y)

theorem block446_reallog_certificate_proof :
    block446_reallog_certificate := by
  exact ⟨block446_left_V_pos, block446_right_V_pos⟩

end Block446
end M1817475
end Erdos1038Lean
