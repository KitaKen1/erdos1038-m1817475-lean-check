import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block458

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block458

open Set

def block458W1 : Rat := ((5748051992446679 : Rat) / 10000000000000000)
def block458W2 : Rat := (0 : Rat)
def block458W3 : Rat := ((3440551674749179 : Rat) / 10000000000000000)
def block458W4 : Rat := ((30641069628378863 : Rat) / 500000000000000000)
def block458S1 : Rat := ((18174751 : Rat) / 10000000)
def block458S2 : Rat := ((511587 : Rat) / 200000)
def block458S3 : Rat := ((131180066160714285827 : Rat) / 50000000000000000000)
def block458S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block458V (y : ℝ) : ℝ :=
  ratPotential block458W1 block458W2 block458W3 block458W4 block458S1 block458S2 block458S3 block458S4 y

def block458LeftParamsCertificate : Bool :=
  allBoxesSameParams block458LeftBoxes block458W1 block458W2 block458W3 block458W4 block458S1 block458S2 block458S3 block458S4

theorem block458LeftParamsCertificate_eq_true :
    block458LeftParamsCertificate = true := by
  native_decide

theorem block458_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block458LeftL : ℝ) (block458LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block458S1 : ℝ))
    (hy2ne : y ≠ (block458S2 : ℝ))
    (hy3ne : y ≠ (block458S3 : ℝ))
    (hy4ne : y ≠ (block458S4 : ℝ)) :
    0 < block458V y := by
  have hcert := block458LeftCertificate_eq_true
  unfold block458LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block458LeftBoxes) (lo := block458LeftL) (hi := block458LeftR)
    (w1 := block458W1) (w2 := block458W2) (w3 := block458W3) (w4 := block458W4)
    (s1 := block458S1) (s2 := block458S2) (s3 := block458S3) (s4 := block458S4)
    hboxes hcover block458LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block458RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block458RightChunk000 block458W1 block458W2 block458W3 block458W4 block458S1 block458S2 block458S3 block458S4

theorem block458RightChunk000ParamsCertificate_eq_true :
    block458RightChunk000ParamsCertificate = true := by
  native_decide

theorem block458_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block458RightChunk000L : ℝ) (block458RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block458S1 : ℝ))
    (hy2ne : y ≠ (block458S2 : ℝ))
    (hy3ne : y ≠ (block458S3 : ℝ))
    (hy4ne : y ≠ (block458S4 : ℝ)) :
    0 < block458V y := by
  have hcert := block458RightChunk000Certificate_eq_true
  unfold block458RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block458RightChunk000) (lo := block458RightChunk000L) (hi := block458RightChunk000R)
    (w1 := block458W1) (w2 := block458W2) (w3 := block458W3) (w4 := block458W4)
    (s1 := block458S1) (s2 := block458S2) (s3 := block458S3) (s4 := block458S4)
    hboxes hcover block458RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block458_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block458RightL : ℝ) (block458RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block458S1 : ℝ))
    (hy2ne : y ≠ (block458S2 : ℝ))
    (hy3ne : y ≠ (block458S3 : ℝ))
    (hy4ne : y ≠ (block458S4 : ℝ)) :
    0 < block458V y := by
  have hL : (block458RightChunk000L : ℝ) = (block458RightL : ℝ) := by
    norm_num [block458RightChunk000L, block458RightL]
  have hR : (block458RightChunk000R : ℝ) = (block458RightR : ℝ) := by
    norm_num [block458RightChunk000R, block458RightR]
  have hyc : y ∈ Icc (block458RightChunk000L : ℝ) (block458RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block458_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block458_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block458LeftL : ℝ) (block458LeftR : ℝ) →
    y ≠ 0 → y ≠ (block458S1 : ℝ) → y ≠ (block458S2 : ℝ) →
    y ≠ (block458S3 : ℝ) → y ≠ (block458S4 : ℝ) → 0 < block458V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block458RightL : ℝ) (block458RightR : ℝ) →
    y ≠ 0 → y ≠ (block458S1 : ℝ) → y ≠ (block458S2 : ℝ) →
    y ≠ (block458S3 : ℝ) → y ≠ (block458S4 : ℝ) → 0 < block458V y)

theorem block458_reallog_certificate_proof :
    block458_reallog_certificate := by
  exact ⟨block458_left_V_pos, block458_right_V_pos⟩

end Block458
end M1817475
end Erdos1038Lean
