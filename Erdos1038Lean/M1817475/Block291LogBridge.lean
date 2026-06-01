import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block291

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block291

open Set

def block291W1 : Rat := ((10242378811684019 : Rat) / 10000000000000000)
def block291W2 : Rat := ((3888136741015867 : Rat) / 100000000000000000)
def block291W3 : Rat := ((27877758250730517 : Rat) / 100000000000000000)
def block291W4 : Rat := (0 : Rat)
def block291S1 : Rat := ((18174751 : Rat) / 10000000)
def block291S2 : Rat := ((511587 : Rat) / 200000)
def block291S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block291S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block291V (y : ℝ) : ℝ :=
  ratPotential block291W1 block291W2 block291W3 block291W4 block291S1 block291S2 block291S3 block291S4 y

def block291LeftParamsCertificate : Bool :=
  allBoxesSameParams block291LeftBoxes block291W1 block291W2 block291W3 block291W4 block291S1 block291S2 block291S3 block291S4

theorem block291LeftParamsCertificate_eq_true :
    block291LeftParamsCertificate = true := by
  native_decide

theorem block291_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block291LeftL : ℝ) (block291LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block291S1 : ℝ))
    (hy2ne : y ≠ (block291S2 : ℝ))
    (hy3ne : y ≠ (block291S3 : ℝ))
    (hy4ne : y ≠ (block291S4 : ℝ)) :
    0 < block291V y := by
  have hcert := block291LeftCertificate_eq_true
  unfold block291LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block291LeftBoxes) (lo := block291LeftL) (hi := block291LeftR)
    (w1 := block291W1) (w2 := block291W2) (w3 := block291W3) (w4 := block291W4)
    (s1 := block291S1) (s2 := block291S2) (s3 := block291S3) (s4 := block291S4)
    hboxes hcover block291LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block291RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block291RightChunk000 block291W1 block291W2 block291W3 block291W4 block291S1 block291S2 block291S3 block291S4

theorem block291RightChunk000ParamsCertificate_eq_true :
    block291RightChunk000ParamsCertificate = true := by
  native_decide

theorem block291_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block291RightChunk000L : ℝ) (block291RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block291S1 : ℝ))
    (hy2ne : y ≠ (block291S2 : ℝ))
    (hy3ne : y ≠ (block291S3 : ℝ))
    (hy4ne : y ≠ (block291S4 : ℝ)) :
    0 < block291V y := by
  have hcert := block291RightChunk000Certificate_eq_true
  unfold block291RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block291RightChunk000) (lo := block291RightChunk000L) (hi := block291RightChunk000R)
    (w1 := block291W1) (w2 := block291W2) (w3 := block291W3) (w4 := block291W4)
    (s1 := block291S1) (s2 := block291S2) (s3 := block291S3) (s4 := block291S4)
    hboxes hcover block291RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block291_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block291RightL : ℝ) (block291RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block291S1 : ℝ))
    (hy2ne : y ≠ (block291S2 : ℝ))
    (hy3ne : y ≠ (block291S3 : ℝ))
    (hy4ne : y ≠ (block291S4 : ℝ)) :
    0 < block291V y := by
  have hL : (block291RightChunk000L : ℝ) = (block291RightL : ℝ) := by
    norm_num [block291RightChunk000L, block291RightL]
  have hR : (block291RightChunk000R : ℝ) = (block291RightR : ℝ) := by
    norm_num [block291RightChunk000R, block291RightR]
  have hyc : y ∈ Icc (block291RightChunk000L : ℝ) (block291RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block291_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block291_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block291LeftL : ℝ) (block291LeftR : ℝ) →
    y ≠ 0 → y ≠ (block291S1 : ℝ) → y ≠ (block291S2 : ℝ) →
    y ≠ (block291S3 : ℝ) → y ≠ (block291S4 : ℝ) → 0 < block291V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block291RightL : ℝ) (block291RightR : ℝ) →
    y ≠ 0 → y ≠ (block291S1 : ℝ) → y ≠ (block291S2 : ℝ) →
    y ≠ (block291S3 : ℝ) → y ≠ (block291S4 : ℝ) → 0 < block291V y)

theorem block291_reallog_certificate_proof :
    block291_reallog_certificate := by
  exact ⟨block291_left_V_pos, block291_right_V_pos⟩

end Block291
end M1817475
end Erdos1038Lean
