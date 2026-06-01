import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block113

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block113

open Set

def block113W1 : Rat := ((1237295825864317 : Rat) / 500000000000000)
def block113W2 : Rat := (0 : Rat)
def block113W3 : Rat := ((3623069392678179 : Rat) / 50000000000000000)
def block113W4 : Rat := ((3501176163036211 : Rat) / 20000000000000000)
def block113S1 : Rat := ((18174751 : Rat) / 10000000)
def block113S2 : Rat := ((511587 : Rat) / 200000)
def block113S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block113S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block113V (y : ℝ) : ℝ :=
  ratPotential block113W1 block113W2 block113W3 block113W4 block113S1 block113S2 block113S3 block113S4 y

def block113LeftParamsCertificate : Bool :=
  allBoxesSameParams block113LeftBoxes block113W1 block113W2 block113W3 block113W4 block113S1 block113S2 block113S3 block113S4

theorem block113LeftParamsCertificate_eq_true :
    block113LeftParamsCertificate = true := by
  native_decide

theorem block113_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block113LeftL : ℝ) (block113LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block113S1 : ℝ))
    (hy2ne : y ≠ (block113S2 : ℝ))
    (hy3ne : y ≠ (block113S3 : ℝ))
    (hy4ne : y ≠ (block113S4 : ℝ)) :
    0 < block113V y := by
  have hcert := block113LeftCertificate_eq_true
  unfold block113LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block113LeftBoxes) (lo := block113LeftL) (hi := block113LeftR)
    (w1 := block113W1) (w2 := block113W2) (w3 := block113W3) (w4 := block113W4)
    (s1 := block113S1) (s2 := block113S2) (s3 := block113S3) (s4 := block113S4)
    hboxes hcover block113LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block113RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block113RightChunk000 block113W1 block113W2 block113W3 block113W4 block113S1 block113S2 block113S3 block113S4

theorem block113RightChunk000ParamsCertificate_eq_true :
    block113RightChunk000ParamsCertificate = true := by
  native_decide

theorem block113_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block113RightChunk000L : ℝ) (block113RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block113S1 : ℝ))
    (hy2ne : y ≠ (block113S2 : ℝ))
    (hy3ne : y ≠ (block113S3 : ℝ))
    (hy4ne : y ≠ (block113S4 : ℝ)) :
    0 < block113V y := by
  have hcert := block113RightChunk000Certificate_eq_true
  unfold block113RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block113RightChunk000) (lo := block113RightChunk000L) (hi := block113RightChunk000R)
    (w1 := block113W1) (w2 := block113W2) (w3 := block113W3) (w4 := block113W4)
    (s1 := block113S1) (s2 := block113S2) (s3 := block113S3) (s4 := block113S4)
    hboxes hcover block113RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block113_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block113RightL : ℝ) (block113RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block113S1 : ℝ))
    (hy2ne : y ≠ (block113S2 : ℝ))
    (hy3ne : y ≠ (block113S3 : ℝ))
    (hy4ne : y ≠ (block113S4 : ℝ)) :
    0 < block113V y := by
  have hL : (block113RightChunk000L : ℝ) = (block113RightL : ℝ) := by
    norm_num [block113RightChunk000L, block113RightL]
  have hR : (block113RightChunk000R : ℝ) = (block113RightR : ℝ) := by
    norm_num [block113RightChunk000R, block113RightR]
  have hyc : y ∈ Icc (block113RightChunk000L : ℝ) (block113RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block113_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block113_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block113LeftL : ℝ) (block113LeftR : ℝ) →
    y ≠ 0 → y ≠ (block113S1 : ℝ) → y ≠ (block113S2 : ℝ) →
    y ≠ (block113S3 : ℝ) → y ≠ (block113S4 : ℝ) → 0 < block113V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block113RightL : ℝ) (block113RightR : ℝ) →
    y ≠ 0 → y ≠ (block113S1 : ℝ) → y ≠ (block113S2 : ℝ) →
    y ≠ (block113S3 : ℝ) → y ≠ (block113S4 : ℝ) → 0 < block113V y)

theorem block113_reallog_certificate_proof :
    block113_reallog_certificate := by
  exact ⟨block113_left_V_pos, block113_right_V_pos⟩

end Block113
end M1817475
end Erdos1038Lean
