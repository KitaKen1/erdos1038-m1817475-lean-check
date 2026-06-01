import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block016

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block016

open Set

def block016W1 : Rat := ((845824143343439 : Rat) / 100000000000000)
def block016W2 : Rat := (0 : Rat)
def block016W3 : Rat := (0 : Rat)
def block016W4 : Rat := ((4960924743124191 : Rat) / 20000000000000000)
def block016S1 : Rat := ((18174751 : Rat) / 10000000)
def block016S2 : Rat := ((511587 : Rat) / 200000)
def block016S3 : Rat := ((107000619 : Rat) / 40000000)
def block016S4 : Rat := ((17676753593749999363 : Rat) / 6250000000000000000)

noncomputable def block016V (y : ℝ) : ℝ :=
  ratPotential block016W1 block016W2 block016W3 block016W4 block016S1 block016S2 block016S3 block016S4 y

def block016LeftParamsCertificate : Bool :=
  allBoxesSameParams block016LeftBoxes block016W1 block016W2 block016W3 block016W4 block016S1 block016S2 block016S3 block016S4

theorem block016LeftParamsCertificate_eq_true :
    block016LeftParamsCertificate = true := by
  native_decide

theorem block016_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block016LeftL : ℝ) (block016LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block016S1 : ℝ))
    (hy2ne : y ≠ (block016S2 : ℝ))
    (hy3ne : y ≠ (block016S3 : ℝ))
    (hy4ne : y ≠ (block016S4 : ℝ)) :
    0 < block016V y := by
  have hcert := block016LeftCertificate_eq_true
  unfold block016LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block016LeftBoxes) (lo := block016LeftL) (hi := block016LeftR)
    (w1 := block016W1) (w2 := block016W2) (w3 := block016W3) (w4 := block016W4)
    (s1 := block016S1) (s2 := block016S2) (s3 := block016S3) (s4 := block016S4)
    hboxes hcover block016LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block016RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block016RightChunk000 block016W1 block016W2 block016W3 block016W4 block016S1 block016S2 block016S3 block016S4

theorem block016RightChunk000ParamsCertificate_eq_true :
    block016RightChunk000ParamsCertificate = true := by
  native_decide

theorem block016_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block016RightChunk000L : ℝ) (block016RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block016S1 : ℝ))
    (hy2ne : y ≠ (block016S2 : ℝ))
    (hy3ne : y ≠ (block016S3 : ℝ))
    (hy4ne : y ≠ (block016S4 : ℝ)) :
    0 < block016V y := by
  have hcert := block016RightChunk000Certificate_eq_true
  unfold block016RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block016RightChunk000) (lo := block016RightChunk000L) (hi := block016RightChunk000R)
    (w1 := block016W1) (w2 := block016W2) (w3 := block016W3) (w4 := block016W4)
    (s1 := block016S1) (s2 := block016S2) (s3 := block016S3) (s4 := block016S4)
    hboxes hcover block016RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block016_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block016RightL : ℝ) (block016RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block016S1 : ℝ))
    (hy2ne : y ≠ (block016S2 : ℝ))
    (hy3ne : y ≠ (block016S3 : ℝ))
    (hy4ne : y ≠ (block016S4 : ℝ)) :
    0 < block016V y := by
  have hL : (block016RightChunk000L : ℝ) = (block016RightL : ℝ) := by
    norm_num [block016RightChunk000L, block016RightL]
  have hR : (block016RightChunk000R : ℝ) = (block016RightR : ℝ) := by
    norm_num [block016RightChunk000R, block016RightR]
  have hyc : y ∈ Icc (block016RightChunk000L : ℝ) (block016RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block016_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block016_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block016LeftL : ℝ) (block016LeftR : ℝ) →
    y ≠ 0 → y ≠ (block016S1 : ℝ) → y ≠ (block016S2 : ℝ) →
    y ≠ (block016S3 : ℝ) → y ≠ (block016S4 : ℝ) → 0 < block016V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block016RightL : ℝ) (block016RightR : ℝ) →
    y ≠ 0 → y ≠ (block016S1 : ℝ) → y ≠ (block016S2 : ℝ) →
    y ≠ (block016S3 : ℝ) → y ≠ (block016S4 : ℝ) → 0 < block016V y)

theorem block016_reallog_certificate_proof :
    block016_reallog_certificate := by
  exact ⟨block016_left_V_pos, block016_right_V_pos⟩

end Block016
end M1817475
end Erdos1038Lean
