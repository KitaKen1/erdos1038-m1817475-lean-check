import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block495

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block495

open Set

def block495W1 : Rat := ((4745842668562189 : Rat) / 10000000000000000)
def block495W2 : Rat := (0 : Rat)
def block495W3 : Rat := ((2027152975990763 : Rat) / 5000000000000000)
def block495W4 : Rat := ((5141648260047691 : Rat) / 200000000000000000)
def block495S1 : Rat := ((18174751 : Rat) / 10000000)
def block495S2 : Rat := ((511587 : Rat) / 200000)
def block495S3 : Rat := ((130456749196428571573 : Rat) / 50000000000000000000)
def block495S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block495V (y : ℝ) : ℝ :=
  ratPotential block495W1 block495W2 block495W3 block495W4 block495S1 block495S2 block495S3 block495S4 y

def block495LeftParamsCertificate : Bool :=
  allBoxesSameParams block495LeftBoxes block495W1 block495W2 block495W3 block495W4 block495S1 block495S2 block495S3 block495S4

theorem block495LeftParamsCertificate_eq_true :
    block495LeftParamsCertificate = true := by
  native_decide

theorem block495_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block495LeftL : ℝ) (block495LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block495S1 : ℝ))
    (hy2ne : y ≠ (block495S2 : ℝ))
    (hy3ne : y ≠ (block495S3 : ℝ))
    (hy4ne : y ≠ (block495S4 : ℝ)) :
    0 < block495V y := by
  have hcert := block495LeftCertificate_eq_true
  unfold block495LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block495LeftBoxes) (lo := block495LeftL) (hi := block495LeftR)
    (w1 := block495W1) (w2 := block495W2) (w3 := block495W3) (w4 := block495W4)
    (s1 := block495S1) (s2 := block495S2) (s3 := block495S3) (s4 := block495S4)
    hboxes hcover block495LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block495RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block495RightChunk000 block495W1 block495W2 block495W3 block495W4 block495S1 block495S2 block495S3 block495S4

theorem block495RightChunk000ParamsCertificate_eq_true :
    block495RightChunk000ParamsCertificate = true := by
  native_decide

theorem block495_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block495RightChunk000L : ℝ) (block495RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block495S1 : ℝ))
    (hy2ne : y ≠ (block495S2 : ℝ))
    (hy3ne : y ≠ (block495S3 : ℝ))
    (hy4ne : y ≠ (block495S4 : ℝ)) :
    0 < block495V y := by
  have hcert := block495RightChunk000Certificate_eq_true
  unfold block495RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block495RightChunk000) (lo := block495RightChunk000L) (hi := block495RightChunk000R)
    (w1 := block495W1) (w2 := block495W2) (w3 := block495W3) (w4 := block495W4)
    (s1 := block495S1) (s2 := block495S2) (s3 := block495S3) (s4 := block495S4)
    hboxes hcover block495RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block495_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block495RightL : ℝ) (block495RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block495S1 : ℝ))
    (hy2ne : y ≠ (block495S2 : ℝ))
    (hy3ne : y ≠ (block495S3 : ℝ))
    (hy4ne : y ≠ (block495S4 : ℝ)) :
    0 < block495V y := by
  have hL : (block495RightChunk000L : ℝ) = (block495RightL : ℝ) := by
    norm_num [block495RightChunk000L, block495RightL]
  have hR : (block495RightChunk000R : ℝ) = (block495RightR : ℝ) := by
    norm_num [block495RightChunk000R, block495RightR]
  have hyc : y ∈ Icc (block495RightChunk000L : ℝ) (block495RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block495_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block495_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block495LeftL : ℝ) (block495LeftR : ℝ) →
    y ≠ 0 → y ≠ (block495S1 : ℝ) → y ≠ (block495S2 : ℝ) →
    y ≠ (block495S3 : ℝ) → y ≠ (block495S4 : ℝ) → 0 < block495V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block495RightL : ℝ) (block495RightR : ℝ) →
    y ≠ 0 → y ≠ (block495S1 : ℝ) → y ≠ (block495S2 : ℝ) →
    y ≠ (block495S3 : ℝ) → y ≠ (block495S4 : ℝ) → 0 < block495V y)

theorem block495_reallog_certificate_proof :
    block495_reallog_certificate := by
  exact ⟨block495_left_V_pos, block495_right_V_pos⟩

end Block495
end M1817475
end Erdos1038Lean
