import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block128

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block128

open Set

def block128W1 : Rat := ((6400915321647589 : Rat) / 2500000000000000)
def block128W2 : Rat := (0 : Rat)
def block128W3 : Rat := ((640703723010551 : Rat) / 6250000000000000)
def block128W4 : Rat := ((6972934541529449 : Rat) / 50000000000000000)
def block128S1 : Rat := ((18174751 : Rat) / 10000000)
def block128S2 : Rat := ((511587 : Rat) / 200000)
def block128S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block128S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block128V (y : ℝ) : ℝ :=
  ratPotential block128W1 block128W2 block128W3 block128W4 block128S1 block128S2 block128S3 block128S4 y

def block128LeftParamsCertificate : Bool :=
  allBoxesSameParams block128LeftBoxes block128W1 block128W2 block128W3 block128W4 block128S1 block128S2 block128S3 block128S4

theorem block128LeftParamsCertificate_eq_true :
    block128LeftParamsCertificate = true := by
  native_decide

theorem block128_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block128LeftL : ℝ) (block128LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block128S1 : ℝ))
    (hy2ne : y ≠ (block128S2 : ℝ))
    (hy3ne : y ≠ (block128S3 : ℝ))
    (hy4ne : y ≠ (block128S4 : ℝ)) :
    0 < block128V y := by
  have hcert := block128LeftCertificate_eq_true
  unfold block128LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block128LeftBoxes) (lo := block128LeftL) (hi := block128LeftR)
    (w1 := block128W1) (w2 := block128W2) (w3 := block128W3) (w4 := block128W4)
    (s1 := block128S1) (s2 := block128S2) (s3 := block128S3) (s4 := block128S4)
    hboxes hcover block128LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block128RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block128RightChunk000 block128W1 block128W2 block128W3 block128W4 block128S1 block128S2 block128S3 block128S4

theorem block128RightChunk000ParamsCertificate_eq_true :
    block128RightChunk000ParamsCertificate = true := by
  native_decide

theorem block128_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block128RightChunk000L : ℝ) (block128RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block128S1 : ℝ))
    (hy2ne : y ≠ (block128S2 : ℝ))
    (hy3ne : y ≠ (block128S3 : ℝ))
    (hy4ne : y ≠ (block128S4 : ℝ)) :
    0 < block128V y := by
  have hcert := block128RightChunk000Certificate_eq_true
  unfold block128RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block128RightChunk000) (lo := block128RightChunk000L) (hi := block128RightChunk000R)
    (w1 := block128W1) (w2 := block128W2) (w3 := block128W3) (w4 := block128W4)
    (s1 := block128S1) (s2 := block128S2) (s3 := block128S3) (s4 := block128S4)
    hboxes hcover block128RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block128_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block128RightL : ℝ) (block128RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block128S1 : ℝ))
    (hy2ne : y ≠ (block128S2 : ℝ))
    (hy3ne : y ≠ (block128S3 : ℝ))
    (hy4ne : y ≠ (block128S4 : ℝ)) :
    0 < block128V y := by
  have hL : (block128RightChunk000L : ℝ) = (block128RightL : ℝ) := by
    norm_num [block128RightChunk000L, block128RightL]
  have hR : (block128RightChunk000R : ℝ) = (block128RightR : ℝ) := by
    norm_num [block128RightChunk000R, block128RightR]
  have hyc : y ∈ Icc (block128RightChunk000L : ℝ) (block128RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block128_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block128_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block128LeftL : ℝ) (block128LeftR : ℝ) →
    y ≠ 0 → y ≠ (block128S1 : ℝ) → y ≠ (block128S2 : ℝ) →
    y ≠ (block128S3 : ℝ) → y ≠ (block128S4 : ℝ) → 0 < block128V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block128RightL : ℝ) (block128RightR : ℝ) →
    y ≠ 0 → y ≠ (block128S1 : ℝ) → y ≠ (block128S2 : ℝ) →
    y ≠ (block128S3 : ℝ) → y ≠ (block128S4 : ℝ) → 0 < block128V y)

theorem block128_reallog_certificate_proof :
    block128_reallog_certificate := by
  exact ⟨block128_left_V_pos, block128_right_V_pos⟩

end Block128
end M1817475
end Erdos1038Lean
