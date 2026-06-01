import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block445

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block445

open Set

def block445W1 : Rat := ((1529819650852339 : Rat) / 2500000000000000)
def block445W2 : Rat := (0 : Rat)
def block445W3 : Rat := ((1631791862527547 : Rat) / 5000000000000000)
def block445W4 : Rat := ((706279022310347 : Rat) / 10000000000000000)
def block445S1 : Rat := ((18174751 : Rat) / 10000000)
def block445S2 : Rat := ((511587 : Rat) / 200000)
def block445S3 : Rat := ((131434204553571428673 : Rat) / 50000000000000000000)
def block445S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block445V (y : ℝ) : ℝ :=
  ratPotential block445W1 block445W2 block445W3 block445W4 block445S1 block445S2 block445S3 block445S4 y

def block445LeftParamsCertificate : Bool :=
  allBoxesSameParams block445LeftBoxes block445W1 block445W2 block445W3 block445W4 block445S1 block445S2 block445S3 block445S4

theorem block445LeftParamsCertificate_eq_true :
    block445LeftParamsCertificate = true := by
  native_decide

theorem block445_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block445LeftL : ℝ) (block445LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block445S1 : ℝ))
    (hy2ne : y ≠ (block445S2 : ℝ))
    (hy3ne : y ≠ (block445S3 : ℝ))
    (hy4ne : y ≠ (block445S4 : ℝ)) :
    0 < block445V y := by
  have hcert := block445LeftCertificate_eq_true
  unfold block445LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block445LeftBoxes) (lo := block445LeftL) (hi := block445LeftR)
    (w1 := block445W1) (w2 := block445W2) (w3 := block445W3) (w4 := block445W4)
    (s1 := block445S1) (s2 := block445S2) (s3 := block445S3) (s4 := block445S4)
    hboxes hcover block445LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block445RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block445RightChunk000 block445W1 block445W2 block445W3 block445W4 block445S1 block445S2 block445S3 block445S4

theorem block445RightChunk000ParamsCertificate_eq_true :
    block445RightChunk000ParamsCertificate = true := by
  native_decide

theorem block445_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block445RightChunk000L : ℝ) (block445RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block445S1 : ℝ))
    (hy2ne : y ≠ (block445S2 : ℝ))
    (hy3ne : y ≠ (block445S3 : ℝ))
    (hy4ne : y ≠ (block445S4 : ℝ)) :
    0 < block445V y := by
  have hcert := block445RightChunk000Certificate_eq_true
  unfold block445RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block445RightChunk000) (lo := block445RightChunk000L) (hi := block445RightChunk000R)
    (w1 := block445W1) (w2 := block445W2) (w3 := block445W3) (w4 := block445W4)
    (s1 := block445S1) (s2 := block445S2) (s3 := block445S3) (s4 := block445S4)
    hboxes hcover block445RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block445_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block445RightL : ℝ) (block445RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block445S1 : ℝ))
    (hy2ne : y ≠ (block445S2 : ℝ))
    (hy3ne : y ≠ (block445S3 : ℝ))
    (hy4ne : y ≠ (block445S4 : ℝ)) :
    0 < block445V y := by
  have hL : (block445RightChunk000L : ℝ) = (block445RightL : ℝ) := by
    norm_num [block445RightChunk000L, block445RightL]
  have hR : (block445RightChunk000R : ℝ) = (block445RightR : ℝ) := by
    norm_num [block445RightChunk000R, block445RightR]
  have hyc : y ∈ Icc (block445RightChunk000L : ℝ) (block445RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block445_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block445_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block445LeftL : ℝ) (block445LeftR : ℝ) →
    y ≠ 0 → y ≠ (block445S1 : ℝ) → y ≠ (block445S2 : ℝ) →
    y ≠ (block445S3 : ℝ) → y ≠ (block445S4 : ℝ) → 0 < block445V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block445RightL : ℝ) (block445RightR : ℝ) →
    y ≠ 0 → y ≠ (block445S1 : ℝ) → y ≠ (block445S2 : ℝ) →
    y ≠ (block445S3 : ℝ) → y ≠ (block445S4 : ℝ) → 0 < block445V y)

theorem block445_reallog_certificate_proof :
    block445_reallog_certificate := by
  exact ⟨block445_left_V_pos, block445_right_V_pos⟩

end Block445
end M1817475
end Erdos1038Lean
