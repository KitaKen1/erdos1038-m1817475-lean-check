import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block083

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block083

open Set

def block083W1 : Rat := ((8527272642863759 : Rat) / 2500000000000000)
def block083W2 : Rat := (0 : Rat)
def block083W3 : Rat := (0 : Rat)
def block083W4 : Rat := ((23892242809011377 : Rat) / 100000000000000000)
def block083S1 : Rat := ((18174751 : Rat) / 10000000)
def block083S2 : Rat := ((511587 : Rat) / 200000)
def block083S3 : Rat := ((107000619 : Rat) / 40000000)
def block083S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block083V (y : ℝ) : ℝ :=
  ratPotential block083W1 block083W2 block083W3 block083W4 block083S1 block083S2 block083S3 block083S4 y

def block083LeftParamsCertificate : Bool :=
  allBoxesSameParams block083LeftBoxes block083W1 block083W2 block083W3 block083W4 block083S1 block083S2 block083S3 block083S4

theorem block083LeftParamsCertificate_eq_true :
    block083LeftParamsCertificate = true := by
  native_decide

theorem block083_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block083LeftL : ℝ) (block083LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block083S1 : ℝ))
    (hy2ne : y ≠ (block083S2 : ℝ))
    (hy3ne : y ≠ (block083S3 : ℝ))
    (hy4ne : y ≠ (block083S4 : ℝ)) :
    0 < block083V y := by
  have hcert := block083LeftCertificate_eq_true
  unfold block083LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block083LeftBoxes) (lo := block083LeftL) (hi := block083LeftR)
    (w1 := block083W1) (w2 := block083W2) (w3 := block083W3) (w4 := block083W4)
    (s1 := block083S1) (s2 := block083S2) (s3 := block083S3) (s4 := block083S4)
    hboxes hcover block083LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block083RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block083RightChunk000 block083W1 block083W2 block083W3 block083W4 block083S1 block083S2 block083S3 block083S4

theorem block083RightChunk000ParamsCertificate_eq_true :
    block083RightChunk000ParamsCertificate = true := by
  native_decide

theorem block083_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block083RightChunk000L : ℝ) (block083RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block083S1 : ℝ))
    (hy2ne : y ≠ (block083S2 : ℝ))
    (hy3ne : y ≠ (block083S3 : ℝ))
    (hy4ne : y ≠ (block083S4 : ℝ)) :
    0 < block083V y := by
  have hcert := block083RightChunk000Certificate_eq_true
  unfold block083RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block083RightChunk000) (lo := block083RightChunk000L) (hi := block083RightChunk000R)
    (w1 := block083W1) (w2 := block083W2) (w3 := block083W3) (w4 := block083W4)
    (s1 := block083S1) (s2 := block083S2) (s3 := block083S3) (s4 := block083S4)
    hboxes hcover block083RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block083_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block083RightL : ℝ) (block083RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block083S1 : ℝ))
    (hy2ne : y ≠ (block083S2 : ℝ))
    (hy3ne : y ≠ (block083S3 : ℝ))
    (hy4ne : y ≠ (block083S4 : ℝ)) :
    0 < block083V y := by
  have hL : (block083RightChunk000L : ℝ) = (block083RightL : ℝ) := by
    norm_num [block083RightChunk000L, block083RightL]
  have hR : (block083RightChunk000R : ℝ) = (block083RightR : ℝ) := by
    norm_num [block083RightChunk000R, block083RightR]
  have hyc : y ∈ Icc (block083RightChunk000L : ℝ) (block083RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block083_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block083_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block083LeftL : ℝ) (block083LeftR : ℝ) →
    y ≠ 0 → y ≠ (block083S1 : ℝ) → y ≠ (block083S2 : ℝ) →
    y ≠ (block083S3 : ℝ) → y ≠ (block083S4 : ℝ) → 0 < block083V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block083RightL : ℝ) (block083RightR : ℝ) →
    y ≠ 0 → y ≠ (block083S1 : ℝ) → y ≠ (block083S2 : ℝ) →
    y ≠ (block083S3 : ℝ) → y ≠ (block083S4 : ℝ) → 0 < block083V y)

theorem block083_reallog_certificate_proof :
    block083_reallog_certificate := by
  exact ⟨block083_left_V_pos, block083_right_V_pos⟩

end Block083
end M1817475
end Erdos1038Lean
