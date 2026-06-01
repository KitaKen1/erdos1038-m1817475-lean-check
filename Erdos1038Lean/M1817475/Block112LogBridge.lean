import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block112

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block112

open Set

def block112W1 : Rat := ((3119358939896063 : Rat) / 1250000000000000)
def block112W2 : Rat := (0 : Rat)
def block112W3 : Rat := ((6981827285682303 : Rat) / 100000000000000000)
def block112W4 : Rat := ((3546624311118291 : Rat) / 20000000000000000)
def block112S1 : Rat := ((18174751 : Rat) / 10000000)
def block112S2 : Rat := ((511587 : Rat) / 200000)
def block112S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block112S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block112V (y : ℝ) : ℝ :=
  ratPotential block112W1 block112W2 block112W3 block112W4 block112S1 block112S2 block112S3 block112S4 y

def block112LeftParamsCertificate : Bool :=
  allBoxesSameParams block112LeftBoxes block112W1 block112W2 block112W3 block112W4 block112S1 block112S2 block112S3 block112S4

theorem block112LeftParamsCertificate_eq_true :
    block112LeftParamsCertificate = true := by
  native_decide

theorem block112_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block112LeftL : ℝ) (block112LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block112S1 : ℝ))
    (hy2ne : y ≠ (block112S2 : ℝ))
    (hy3ne : y ≠ (block112S3 : ℝ))
    (hy4ne : y ≠ (block112S4 : ℝ)) :
    0 < block112V y := by
  have hcert := block112LeftCertificate_eq_true
  unfold block112LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block112LeftBoxes) (lo := block112LeftL) (hi := block112LeftR)
    (w1 := block112W1) (w2 := block112W2) (w3 := block112W3) (w4 := block112W4)
    (s1 := block112S1) (s2 := block112S2) (s3 := block112S3) (s4 := block112S4)
    hboxes hcover block112LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block112RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block112RightChunk000 block112W1 block112W2 block112W3 block112W4 block112S1 block112S2 block112S3 block112S4

theorem block112RightChunk000ParamsCertificate_eq_true :
    block112RightChunk000ParamsCertificate = true := by
  native_decide

theorem block112_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block112RightChunk000L : ℝ) (block112RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block112S1 : ℝ))
    (hy2ne : y ≠ (block112S2 : ℝ))
    (hy3ne : y ≠ (block112S3 : ℝ))
    (hy4ne : y ≠ (block112S4 : ℝ)) :
    0 < block112V y := by
  have hcert := block112RightChunk000Certificate_eq_true
  unfold block112RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block112RightChunk000) (lo := block112RightChunk000L) (hi := block112RightChunk000R)
    (w1 := block112W1) (w2 := block112W2) (w3 := block112W3) (w4 := block112W4)
    (s1 := block112S1) (s2 := block112S2) (s3 := block112S3) (s4 := block112S4)
    hboxes hcover block112RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block112_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block112RightL : ℝ) (block112RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block112S1 : ℝ))
    (hy2ne : y ≠ (block112S2 : ℝ))
    (hy3ne : y ≠ (block112S3 : ℝ))
    (hy4ne : y ≠ (block112S4 : ℝ)) :
    0 < block112V y := by
  have hL : (block112RightChunk000L : ℝ) = (block112RightL : ℝ) := by
    norm_num [block112RightChunk000L, block112RightL]
  have hR : (block112RightChunk000R : ℝ) = (block112RightR : ℝ) := by
    norm_num [block112RightChunk000R, block112RightR]
  have hyc : y ∈ Icc (block112RightChunk000L : ℝ) (block112RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block112_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block112_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block112LeftL : ℝ) (block112LeftR : ℝ) →
    y ≠ 0 → y ≠ (block112S1 : ℝ) → y ≠ (block112S2 : ℝ) →
    y ≠ (block112S3 : ℝ) → y ≠ (block112S4 : ℝ) → 0 < block112V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block112RightL : ℝ) (block112RightR : ℝ) →
    y ≠ 0 → y ≠ (block112S1 : ℝ) → y ≠ (block112S2 : ℝ) →
    y ≠ (block112S3 : ℝ) → y ≠ (block112S4 : ℝ) → 0 < block112V y)

theorem block112_reallog_certificate_proof :
    block112_reallog_certificate := by
  exact ⟨block112_left_V_pos, block112_right_V_pos⟩

end Block112
end M1817475
end Erdos1038Lean
