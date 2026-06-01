import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block462

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block462

open Set

def block462W1 : Rat := ((1409292799639193 : Rat) / 2500000000000000)
def block462W2 : Rat := (0 : Rat)
def block462W3 : Rat := ((17487971810564257 : Rat) / 50000000000000000)
def block462W4 : Rat := ((5818846064925579 : Rat) / 100000000000000000)
def block462S1 : Rat := ((18174751 : Rat) / 10000000)
def block462S2 : Rat := ((511587 : Rat) / 200000)
def block462S3 : Rat := ((131101869732142857259 : Rat) / 50000000000000000000)
def block462S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block462V (y : ℝ) : ℝ :=
  ratPotential block462W1 block462W2 block462W3 block462W4 block462S1 block462S2 block462S3 block462S4 y

def block462LeftParamsCertificate : Bool :=
  allBoxesSameParams block462LeftBoxes block462W1 block462W2 block462W3 block462W4 block462S1 block462S2 block462S3 block462S4

theorem block462LeftParamsCertificate_eq_true :
    block462LeftParamsCertificate = true := by
  native_decide

theorem block462_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block462LeftL : ℝ) (block462LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block462S1 : ℝ))
    (hy2ne : y ≠ (block462S2 : ℝ))
    (hy3ne : y ≠ (block462S3 : ℝ))
    (hy4ne : y ≠ (block462S4 : ℝ)) :
    0 < block462V y := by
  have hcert := block462LeftCertificate_eq_true
  unfold block462LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block462LeftBoxes) (lo := block462LeftL) (hi := block462LeftR)
    (w1 := block462W1) (w2 := block462W2) (w3 := block462W3) (w4 := block462W4)
    (s1 := block462S1) (s2 := block462S2) (s3 := block462S3) (s4 := block462S4)
    hboxes hcover block462LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block462RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block462RightChunk000 block462W1 block462W2 block462W3 block462W4 block462S1 block462S2 block462S3 block462S4

theorem block462RightChunk000ParamsCertificate_eq_true :
    block462RightChunk000ParamsCertificate = true := by
  native_decide

theorem block462_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block462RightChunk000L : ℝ) (block462RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block462S1 : ℝ))
    (hy2ne : y ≠ (block462S2 : ℝ))
    (hy3ne : y ≠ (block462S3 : ℝ))
    (hy4ne : y ≠ (block462S4 : ℝ)) :
    0 < block462V y := by
  have hcert := block462RightChunk000Certificate_eq_true
  unfold block462RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block462RightChunk000) (lo := block462RightChunk000L) (hi := block462RightChunk000R)
    (w1 := block462W1) (w2 := block462W2) (w3 := block462W3) (w4 := block462W4)
    (s1 := block462S1) (s2 := block462S2) (s3 := block462S3) (s4 := block462S4)
    hboxes hcover block462RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block462_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block462RightL : ℝ) (block462RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block462S1 : ℝ))
    (hy2ne : y ≠ (block462S2 : ℝ))
    (hy3ne : y ≠ (block462S3 : ℝ))
    (hy4ne : y ≠ (block462S4 : ℝ)) :
    0 < block462V y := by
  have hL : (block462RightChunk000L : ℝ) = (block462RightL : ℝ) := by
    norm_num [block462RightChunk000L, block462RightL]
  have hR : (block462RightChunk000R : ℝ) = (block462RightR : ℝ) := by
    norm_num [block462RightChunk000R, block462RightR]
  have hyc : y ∈ Icc (block462RightChunk000L : ℝ) (block462RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block462_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block462_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block462LeftL : ℝ) (block462LeftR : ℝ) →
    y ≠ 0 → y ≠ (block462S1 : ℝ) → y ≠ (block462S2 : ℝ) →
    y ≠ (block462S3 : ℝ) → y ≠ (block462S4 : ℝ) → 0 < block462V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block462RightL : ℝ) (block462RightR : ℝ) →
    y ≠ 0 → y ≠ (block462S1 : ℝ) → y ≠ (block462S2 : ℝ) →
    y ≠ (block462S3 : ℝ) → y ≠ (block462S4 : ℝ) → 0 < block462V y)

theorem block462_reallog_certificate_proof :
    block462_reallog_certificate := by
  exact ⟨block462_left_V_pos, block462_right_V_pos⟩

end Block462
end M1817475
end Erdos1038Lean
