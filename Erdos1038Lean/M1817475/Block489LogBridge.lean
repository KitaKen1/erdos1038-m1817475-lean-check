import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block489

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block489

open Set

def block489W1 : Rat := ((24531402619075507 : Rat) / 50000000000000000)
def block489W2 : Rat := (0 : Rat)
def block489W3 : Rat := ((39390556694517537 : Rat) / 100000000000000000)
def block489W4 : Rat := ((1637134898445999 : Rat) / 50000000000000000)
def block489S1 : Rat := ((18174751 : Rat) / 10000000)
def block489S2 : Rat := ((511587 : Rat) / 200000)
def block489S3 : Rat := ((5222961753571428577 : Rat) / 2000000000000000000)
def block489S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block489V (y : ℝ) : ℝ :=
  ratPotential block489W1 block489W2 block489W3 block489W4 block489S1 block489S2 block489S3 block489S4 y

def block489LeftParamsCertificate : Bool :=
  allBoxesSameParams block489LeftBoxes block489W1 block489W2 block489W3 block489W4 block489S1 block489S2 block489S3 block489S4

theorem block489LeftParamsCertificate_eq_true :
    block489LeftParamsCertificate = true := by
  native_decide

theorem block489_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block489LeftL : ℝ) (block489LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block489S1 : ℝ))
    (hy2ne : y ≠ (block489S2 : ℝ))
    (hy3ne : y ≠ (block489S3 : ℝ))
    (hy4ne : y ≠ (block489S4 : ℝ)) :
    0 < block489V y := by
  have hcert := block489LeftCertificate_eq_true
  unfold block489LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block489LeftBoxes) (lo := block489LeftL) (hi := block489LeftR)
    (w1 := block489W1) (w2 := block489W2) (w3 := block489W3) (w4 := block489W4)
    (s1 := block489S1) (s2 := block489S2) (s3 := block489S3) (s4 := block489S4)
    hboxes hcover block489LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block489RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block489RightChunk000 block489W1 block489W2 block489W3 block489W4 block489S1 block489S2 block489S3 block489S4

theorem block489RightChunk000ParamsCertificate_eq_true :
    block489RightChunk000ParamsCertificate = true := by
  native_decide

theorem block489_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block489RightChunk000L : ℝ) (block489RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block489S1 : ℝ))
    (hy2ne : y ≠ (block489S2 : ℝ))
    (hy3ne : y ≠ (block489S3 : ℝ))
    (hy4ne : y ≠ (block489S4 : ℝ)) :
    0 < block489V y := by
  have hcert := block489RightChunk000Certificate_eq_true
  unfold block489RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block489RightChunk000) (lo := block489RightChunk000L) (hi := block489RightChunk000R)
    (w1 := block489W1) (w2 := block489W2) (w3 := block489W3) (w4 := block489W4)
    (s1 := block489S1) (s2 := block489S2) (s3 := block489S3) (s4 := block489S4)
    hboxes hcover block489RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block489_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block489RightL : ℝ) (block489RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block489S1 : ℝ))
    (hy2ne : y ≠ (block489S2 : ℝ))
    (hy3ne : y ≠ (block489S3 : ℝ))
    (hy4ne : y ≠ (block489S4 : ℝ)) :
    0 < block489V y := by
  have hL : (block489RightChunk000L : ℝ) = (block489RightL : ℝ) := by
    norm_num [block489RightChunk000L, block489RightL]
  have hR : (block489RightChunk000R : ℝ) = (block489RightR : ℝ) := by
    norm_num [block489RightChunk000R, block489RightR]
  have hyc : y ∈ Icc (block489RightChunk000L : ℝ) (block489RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block489_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block489_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block489LeftL : ℝ) (block489LeftR : ℝ) →
    y ≠ 0 → y ≠ (block489S1 : ℝ) → y ≠ (block489S2 : ℝ) →
    y ≠ (block489S3 : ℝ) → y ≠ (block489S4 : ℝ) → 0 < block489V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block489RightL : ℝ) (block489RightR : ℝ) →
    y ≠ 0 → y ≠ (block489S1 : ℝ) → y ≠ (block489S2 : ℝ) →
    y ≠ (block489S3 : ℝ) → y ≠ (block489S4 : ℝ) → 0 < block489V y)

theorem block489_reallog_certificate_proof :
    block489_reallog_certificate := by
  exact ⟨block489_left_V_pos, block489_right_V_pos⟩

end Block489
end M1817475
end Erdos1038Lean
