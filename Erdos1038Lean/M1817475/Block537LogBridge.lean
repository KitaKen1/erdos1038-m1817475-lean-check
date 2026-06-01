import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block537

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block537

open Set

def block537W1 : Rat := ((8013140583568007 : Rat) / 20000000000000000)
def block537W2 : Rat := (0 : Rat)
def block537W3 : Rat := ((45485162465163587 : Rat) / 100000000000000000)
def block537W4 : Rat := (0 : Rat)
def block537S1 : Rat := ((18174751 : Rat) / 10000000)
def block537S2 : Rat := ((511587 : Rat) / 200000)
def block537S3 : Rat := ((129635686696428571609 : Rat) / 50000000000000000000)
def block537S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block537V (y : ℝ) : ℝ :=
  ratPotential block537W1 block537W2 block537W3 block537W4 block537S1 block537S2 block537S3 block537S4 y

def block537LeftParamsCertificate : Bool :=
  allBoxesSameParams block537LeftBoxes block537W1 block537W2 block537W3 block537W4 block537S1 block537S2 block537S3 block537S4

theorem block537LeftParamsCertificate_eq_true :
    block537LeftParamsCertificate = true := by
  native_decide

theorem block537_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block537LeftL : ℝ) (block537LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block537S1 : ℝ))
    (hy2ne : y ≠ (block537S2 : ℝ))
    (hy3ne : y ≠ (block537S3 : ℝ))
    (hy4ne : y ≠ (block537S4 : ℝ)) :
    0 < block537V y := by
  have hcert := block537LeftCertificate_eq_true
  unfold block537LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block537LeftBoxes) (lo := block537LeftL) (hi := block537LeftR)
    (w1 := block537W1) (w2 := block537W2) (w3 := block537W3) (w4 := block537W4)
    (s1 := block537S1) (s2 := block537S2) (s3 := block537S3) (s4 := block537S4)
    hboxes hcover block537LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block537RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block537RightChunk000 block537W1 block537W2 block537W3 block537W4 block537S1 block537S2 block537S3 block537S4

theorem block537RightChunk000ParamsCertificate_eq_true :
    block537RightChunk000ParamsCertificate = true := by
  native_decide

theorem block537_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block537RightChunk000L : ℝ) (block537RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block537S1 : ℝ))
    (hy2ne : y ≠ (block537S2 : ℝ))
    (hy3ne : y ≠ (block537S3 : ℝ))
    (hy4ne : y ≠ (block537S4 : ℝ)) :
    0 < block537V y := by
  have hcert := block537RightChunk000Certificate_eq_true
  unfold block537RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block537RightChunk000) (lo := block537RightChunk000L) (hi := block537RightChunk000R)
    (w1 := block537W1) (w2 := block537W2) (w3 := block537W3) (w4 := block537W4)
    (s1 := block537S1) (s2 := block537S2) (s3 := block537S3) (s4 := block537S4)
    hboxes hcover block537RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block537_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block537RightL : ℝ) (block537RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block537S1 : ℝ))
    (hy2ne : y ≠ (block537S2 : ℝ))
    (hy3ne : y ≠ (block537S3 : ℝ))
    (hy4ne : y ≠ (block537S4 : ℝ)) :
    0 < block537V y := by
  have hL : (block537RightChunk000L : ℝ) = (block537RightL : ℝ) := by
    norm_num [block537RightChunk000L, block537RightL]
  have hR : (block537RightChunk000R : ℝ) = (block537RightR : ℝ) := by
    norm_num [block537RightChunk000R, block537RightR]
  have hyc : y ∈ Icc (block537RightChunk000L : ℝ) (block537RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block537_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block537_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block537LeftL : ℝ) (block537LeftR : ℝ) →
    y ≠ 0 → y ≠ (block537S1 : ℝ) → y ≠ (block537S2 : ℝ) →
    y ≠ (block537S3 : ℝ) → y ≠ (block537S4 : ℝ) → 0 < block537V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block537RightL : ℝ) (block537RightR : ℝ) →
    y ≠ 0 → y ≠ (block537S1 : ℝ) → y ≠ (block537S2 : ℝ) →
    y ≠ (block537S3 : ℝ) → y ≠ (block537S4 : ℝ) → 0 < block537V y)

theorem block537_reallog_certificate_proof :
    block537_reallog_certificate := by
  exact ⟨block537_left_V_pos, block537_right_V_pos⟩

end Block537
end M1817475
end Erdos1038Lean
