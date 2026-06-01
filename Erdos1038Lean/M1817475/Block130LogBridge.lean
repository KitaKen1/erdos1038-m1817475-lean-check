import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block130

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block130

open Set

def block130W1 : Rat := ((2552331336945371 : Rat) / 1000000000000000)
def block130W2 : Rat := (0 : Rat)
def block130W3 : Rat := ((10577843004246221 : Rat) / 100000000000000000)
def block130W4 : Rat := ((169717626709443 : Rat) / 1250000000000000)
def block130S1 : Rat := ((18174751 : Rat) / 10000000)
def block130S2 : Rat := ((511587 : Rat) / 200000)
def block130S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block130S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block130V (y : ℝ) : ℝ :=
  ratPotential block130W1 block130W2 block130W3 block130W4 block130S1 block130S2 block130S3 block130S4 y

def block130LeftParamsCertificate : Bool :=
  allBoxesSameParams block130LeftBoxes block130W1 block130W2 block130W3 block130W4 block130S1 block130S2 block130S3 block130S4

theorem block130LeftParamsCertificate_eq_true :
    block130LeftParamsCertificate = true := by
  native_decide

theorem block130_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block130LeftL : ℝ) (block130LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block130S1 : ℝ))
    (hy2ne : y ≠ (block130S2 : ℝ))
    (hy3ne : y ≠ (block130S3 : ℝ))
    (hy4ne : y ≠ (block130S4 : ℝ)) :
    0 < block130V y := by
  have hcert := block130LeftCertificate_eq_true
  unfold block130LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block130LeftBoxes) (lo := block130LeftL) (hi := block130LeftR)
    (w1 := block130W1) (w2 := block130W2) (w3 := block130W3) (w4 := block130W4)
    (s1 := block130S1) (s2 := block130S2) (s3 := block130S3) (s4 := block130S4)
    hboxes hcover block130LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block130RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block130RightChunk000 block130W1 block130W2 block130W3 block130W4 block130S1 block130S2 block130S3 block130S4

theorem block130RightChunk000ParamsCertificate_eq_true :
    block130RightChunk000ParamsCertificate = true := by
  native_decide

theorem block130_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block130RightChunk000L : ℝ) (block130RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block130S1 : ℝ))
    (hy2ne : y ≠ (block130S2 : ℝ))
    (hy3ne : y ≠ (block130S3 : ℝ))
    (hy4ne : y ≠ (block130S4 : ℝ)) :
    0 < block130V y := by
  have hcert := block130RightChunk000Certificate_eq_true
  unfold block130RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block130RightChunk000) (lo := block130RightChunk000L) (hi := block130RightChunk000R)
    (w1 := block130W1) (w2 := block130W2) (w3 := block130W3) (w4 := block130W4)
    (s1 := block130S1) (s2 := block130S2) (s3 := block130S3) (s4 := block130S4)
    hboxes hcover block130RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block130_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block130RightL : ℝ) (block130RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block130S1 : ℝ))
    (hy2ne : y ≠ (block130S2 : ℝ))
    (hy3ne : y ≠ (block130S3 : ℝ))
    (hy4ne : y ≠ (block130S4 : ℝ)) :
    0 < block130V y := by
  have hL : (block130RightChunk000L : ℝ) = (block130RightL : ℝ) := by
    norm_num [block130RightChunk000L, block130RightL]
  have hR : (block130RightChunk000R : ℝ) = (block130RightR : ℝ) := by
    norm_num [block130RightChunk000R, block130RightR]
  have hyc : y ∈ Icc (block130RightChunk000L : ℝ) (block130RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block130_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block130_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block130LeftL : ℝ) (block130LeftR : ℝ) →
    y ≠ 0 → y ≠ (block130S1 : ℝ) → y ≠ (block130S2 : ℝ) →
    y ≠ (block130S3 : ℝ) → y ≠ (block130S4 : ℝ) → 0 < block130V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block130RightL : ℝ) (block130RightR : ℝ) →
    y ≠ 0 → y ≠ (block130S1 : ℝ) → y ≠ (block130S2 : ℝ) →
    y ≠ (block130S3 : ℝ) → y ≠ (block130S4 : ℝ) → 0 < block130V y)

theorem block130_reallog_certificate_proof :
    block130_reallog_certificate := by
  exact ⟨block130_left_V_pos, block130_right_V_pos⟩

end Block130
end M1817475
end Erdos1038Lean
