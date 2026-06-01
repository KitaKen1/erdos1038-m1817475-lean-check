import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block085

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block085

open Set

def block085W1 : Rat := ((3469107550694479 : Rat) / 1000000000000000)
def block085W2 : Rat := (0 : Rat)
def block085W3 : Rat := (0 : Rat)
def block085W4 : Rat := ((2960600525620569 : Rat) / 12500000000000000)
def block085S1 : Rat := ((18174751 : Rat) / 10000000)
def block085S2 : Rat := ((511587 : Rat) / 200000)
def block085S3 : Rat := ((107000619 : Rat) / 40000000)
def block085S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block085V (y : ℝ) : ℝ :=
  ratPotential block085W1 block085W2 block085W3 block085W4 block085S1 block085S2 block085S3 block085S4 y

def block085LeftParamsCertificate : Bool :=
  allBoxesSameParams block085LeftBoxes block085W1 block085W2 block085W3 block085W4 block085S1 block085S2 block085S3 block085S4

theorem block085LeftParamsCertificate_eq_true :
    block085LeftParamsCertificate = true := by
  native_decide

theorem block085_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block085LeftL : ℝ) (block085LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block085S1 : ℝ))
    (hy2ne : y ≠ (block085S2 : ℝ))
    (hy3ne : y ≠ (block085S3 : ℝ))
    (hy4ne : y ≠ (block085S4 : ℝ)) :
    0 < block085V y := by
  have hcert := block085LeftCertificate_eq_true
  unfold block085LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block085LeftBoxes) (lo := block085LeftL) (hi := block085LeftR)
    (w1 := block085W1) (w2 := block085W2) (w3 := block085W3) (w4 := block085W4)
    (s1 := block085S1) (s2 := block085S2) (s3 := block085S3) (s4 := block085S4)
    hboxes hcover block085LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block085RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block085RightChunk000 block085W1 block085W2 block085W3 block085W4 block085S1 block085S2 block085S3 block085S4

theorem block085RightChunk000ParamsCertificate_eq_true :
    block085RightChunk000ParamsCertificate = true := by
  native_decide

theorem block085_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block085RightChunk000L : ℝ) (block085RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block085S1 : ℝ))
    (hy2ne : y ≠ (block085S2 : ℝ))
    (hy3ne : y ≠ (block085S3 : ℝ))
    (hy4ne : y ≠ (block085S4 : ℝ)) :
    0 < block085V y := by
  have hcert := block085RightChunk000Certificate_eq_true
  unfold block085RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block085RightChunk000) (lo := block085RightChunk000L) (hi := block085RightChunk000R)
    (w1 := block085W1) (w2 := block085W2) (w3 := block085W3) (w4 := block085W4)
    (s1 := block085S1) (s2 := block085S2) (s3 := block085S3) (s4 := block085S4)
    hboxes hcover block085RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block085_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block085RightL : ℝ) (block085RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block085S1 : ℝ))
    (hy2ne : y ≠ (block085S2 : ℝ))
    (hy3ne : y ≠ (block085S3 : ℝ))
    (hy4ne : y ≠ (block085S4 : ℝ)) :
    0 < block085V y := by
  have hL : (block085RightChunk000L : ℝ) = (block085RightL : ℝ) := by
    norm_num [block085RightChunk000L, block085RightL]
  have hR : (block085RightChunk000R : ℝ) = (block085RightR : ℝ) := by
    norm_num [block085RightChunk000R, block085RightR]
  have hyc : y ∈ Icc (block085RightChunk000L : ℝ) (block085RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block085_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block085_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block085LeftL : ℝ) (block085LeftR : ℝ) →
    y ≠ 0 → y ≠ (block085S1 : ℝ) → y ≠ (block085S2 : ℝ) →
    y ≠ (block085S3 : ℝ) → y ≠ (block085S4 : ℝ) → 0 < block085V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block085RightL : ℝ) (block085RightR : ℝ) →
    y ≠ 0 → y ≠ (block085S1 : ℝ) → y ≠ (block085S2 : ℝ) →
    y ≠ (block085S3 : ℝ) → y ≠ (block085S4 : ℝ) → 0 < block085V y)

theorem block085_reallog_certificate_proof :
    block085_reallog_certificate := by
  exact ⟨block085_left_V_pos, block085_right_V_pos⟩

end Block085
end M1817475
end Erdos1038Lean
