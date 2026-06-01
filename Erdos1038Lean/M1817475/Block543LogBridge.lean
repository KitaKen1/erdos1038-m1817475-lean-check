import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block543

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block543

open Set

def block543W1 : Rat := ((4932914584446723 : Rat) / 12500000000000000)
def block543W2 : Rat := (0 : Rat)
def block543W3 : Rat := ((22856768610709613 : Rat) / 50000000000000000)
def block543W4 : Rat := (0 : Rat)
def block543S1 : Rat := ((18174751 : Rat) / 10000000)
def block543S2 : Rat := ((511587 : Rat) / 200000)
def block543S3 : Rat := ((129518392053571428757 : Rat) / 50000000000000000000)
def block543S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block543V (y : ℝ) : ℝ :=
  ratPotential block543W1 block543W2 block543W3 block543W4 block543S1 block543S2 block543S3 block543S4 y

def block543LeftParamsCertificate : Bool :=
  allBoxesSameParams block543LeftBoxes block543W1 block543W2 block543W3 block543W4 block543S1 block543S2 block543S3 block543S4

theorem block543LeftParamsCertificate_eq_true :
    block543LeftParamsCertificate = true := by
  native_decide

theorem block543_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block543LeftL : ℝ) (block543LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block543S1 : ℝ))
    (hy2ne : y ≠ (block543S2 : ℝ))
    (hy3ne : y ≠ (block543S3 : ℝ))
    (hy4ne : y ≠ (block543S4 : ℝ)) :
    0 < block543V y := by
  have hcert := block543LeftCertificate_eq_true
  unfold block543LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block543LeftBoxes) (lo := block543LeftL) (hi := block543LeftR)
    (w1 := block543W1) (w2 := block543W2) (w3 := block543W3) (w4 := block543W4)
    (s1 := block543S1) (s2 := block543S2) (s3 := block543S3) (s4 := block543S4)
    hboxes hcover block543LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block543RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block543RightChunk000 block543W1 block543W2 block543W3 block543W4 block543S1 block543S2 block543S3 block543S4

theorem block543RightChunk000ParamsCertificate_eq_true :
    block543RightChunk000ParamsCertificate = true := by
  native_decide

theorem block543_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block543RightChunk000L : ℝ) (block543RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block543S1 : ℝ))
    (hy2ne : y ≠ (block543S2 : ℝ))
    (hy3ne : y ≠ (block543S3 : ℝ))
    (hy4ne : y ≠ (block543S4 : ℝ)) :
    0 < block543V y := by
  have hcert := block543RightChunk000Certificate_eq_true
  unfold block543RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block543RightChunk000) (lo := block543RightChunk000L) (hi := block543RightChunk000R)
    (w1 := block543W1) (w2 := block543W2) (w3 := block543W3) (w4 := block543W4)
    (s1 := block543S1) (s2 := block543S2) (s3 := block543S3) (s4 := block543S4)
    hboxes hcover block543RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block543_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block543RightL : ℝ) (block543RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block543S1 : ℝ))
    (hy2ne : y ≠ (block543S2 : ℝ))
    (hy3ne : y ≠ (block543S3 : ℝ))
    (hy4ne : y ≠ (block543S4 : ℝ)) :
    0 < block543V y := by
  have hL : (block543RightChunk000L : ℝ) = (block543RightL : ℝ) := by
    norm_num [block543RightChunk000L, block543RightL]
  have hR : (block543RightChunk000R : ℝ) = (block543RightR : ℝ) := by
    norm_num [block543RightChunk000R, block543RightR]
  have hyc : y ∈ Icc (block543RightChunk000L : ℝ) (block543RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block543_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block543_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block543LeftL : ℝ) (block543LeftR : ℝ) →
    y ≠ 0 → y ≠ (block543S1 : ℝ) → y ≠ (block543S2 : ℝ) →
    y ≠ (block543S3 : ℝ) → y ≠ (block543S4 : ℝ) → 0 < block543V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block543RightL : ℝ) (block543RightR : ℝ) →
    y ≠ 0 → y ≠ (block543S1 : ℝ) → y ≠ (block543S2 : ℝ) →
    y ≠ (block543S3 : ℝ) → y ≠ (block543S4 : ℝ) → 0 < block543V y)

theorem block543_reallog_certificate_proof :
    block543_reallog_certificate := by
  exact ⟨block543_left_V_pos, block543_right_V_pos⟩

end Block543
end M1817475
end Erdos1038Lean
