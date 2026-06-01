import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block434

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block434

open Set

def block434W1 : Rat := ((3221170577460579 : Rat) / 5000000000000000)
def block434W2 : Rat := (0 : Rat)
def block434W3 : Rat := ((312688430912729 : Rat) / 1000000000000000)
def block434W4 : Rat := ((1936797403448337 : Rat) / 25000000000000000)
def block434S1 : Rat := ((18174751 : Rat) / 10000000)
def block434S2 : Rat := ((511587 : Rat) / 200000)
def block434S3 : Rat := ((26329848946428571447 : Rat) / 10000000000000000000)
def block434S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block434V (y : ℝ) : ℝ :=
  ratPotential block434W1 block434W2 block434W3 block434W4 block434S1 block434S2 block434S3 block434S4 y

def block434LeftParamsCertificate : Bool :=
  allBoxesSameParams block434LeftBoxes block434W1 block434W2 block434W3 block434W4 block434S1 block434S2 block434S3 block434S4

theorem block434LeftParamsCertificate_eq_true :
    block434LeftParamsCertificate = true := by
  native_decide

theorem block434_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block434LeftL : ℝ) (block434LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block434S1 : ℝ))
    (hy2ne : y ≠ (block434S2 : ℝ))
    (hy3ne : y ≠ (block434S3 : ℝ))
    (hy4ne : y ≠ (block434S4 : ℝ)) :
    0 < block434V y := by
  have hcert := block434LeftCertificate_eq_true
  unfold block434LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block434LeftBoxes) (lo := block434LeftL) (hi := block434LeftR)
    (w1 := block434W1) (w2 := block434W2) (w3 := block434W3) (w4 := block434W4)
    (s1 := block434S1) (s2 := block434S2) (s3 := block434S3) (s4 := block434S4)
    hboxes hcover block434LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block434RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block434RightChunk000 block434W1 block434W2 block434W3 block434W4 block434S1 block434S2 block434S3 block434S4

theorem block434RightChunk000ParamsCertificate_eq_true :
    block434RightChunk000ParamsCertificate = true := by
  native_decide

theorem block434_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block434RightChunk000L : ℝ) (block434RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block434S1 : ℝ))
    (hy2ne : y ≠ (block434S2 : ℝ))
    (hy3ne : y ≠ (block434S3 : ℝ))
    (hy4ne : y ≠ (block434S4 : ℝ)) :
    0 < block434V y := by
  have hcert := block434RightChunk000Certificate_eq_true
  unfold block434RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block434RightChunk000) (lo := block434RightChunk000L) (hi := block434RightChunk000R)
    (w1 := block434W1) (w2 := block434W2) (w3 := block434W3) (w4 := block434W4)
    (s1 := block434S1) (s2 := block434S2) (s3 := block434S3) (s4 := block434S4)
    hboxes hcover block434RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block434_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block434RightL : ℝ) (block434RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block434S1 : ℝ))
    (hy2ne : y ≠ (block434S2 : ℝ))
    (hy3ne : y ≠ (block434S3 : ℝ))
    (hy4ne : y ≠ (block434S4 : ℝ)) :
    0 < block434V y := by
  have hL : (block434RightChunk000L : ℝ) = (block434RightL : ℝ) := by
    norm_num [block434RightChunk000L, block434RightL]
  have hR : (block434RightChunk000R : ℝ) = (block434RightR : ℝ) := by
    norm_num [block434RightChunk000R, block434RightR]
  have hyc : y ∈ Icc (block434RightChunk000L : ℝ) (block434RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block434_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block434_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block434LeftL : ℝ) (block434LeftR : ℝ) →
    y ≠ 0 → y ≠ (block434S1 : ℝ) → y ≠ (block434S2 : ℝ) →
    y ≠ (block434S3 : ℝ) → y ≠ (block434S4 : ℝ) → 0 < block434V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block434RightL : ℝ) (block434RightR : ℝ) →
    y ≠ 0 → y ≠ (block434S1 : ℝ) → y ≠ (block434S2 : ℝ) →
    y ≠ (block434S3 : ℝ) → y ≠ (block434S4 : ℝ) → 0 < block434V y)

theorem block434_reallog_certificate_proof :
    block434_reallog_certificate := by
  exact ⟨block434_left_V_pos, block434_right_V_pos⟩

end Block434
end M1817475
end Erdos1038Lean
