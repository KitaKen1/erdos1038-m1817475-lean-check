import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block485

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block485

open Set

def block485W1 : Rat := ((5012236974794787 : Rat) / 10000000000000000)
def block485W2 : Rat := (0 : Rat)
def block485W3 : Rat := ((483426769830921 : Rat) / 1250000000000000)
def block485W4 : Rat := ((925510026295349 : Rat) / 25000000000000000)
def block485S1 : Rat := ((18174751 : Rat) / 10000000)
def block485S2 : Rat := ((511587 : Rat) / 200000)
def block485S3 : Rat := ((130652240267857142993 : Rat) / 50000000000000000000)
def block485S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block485V (y : ℝ) : ℝ :=
  ratPotential block485W1 block485W2 block485W3 block485W4 block485S1 block485S2 block485S3 block485S4 y

def block485LeftParamsCertificate : Bool :=
  allBoxesSameParams block485LeftBoxes block485W1 block485W2 block485W3 block485W4 block485S1 block485S2 block485S3 block485S4

theorem block485LeftParamsCertificate_eq_true :
    block485LeftParamsCertificate = true := by
  native_decide

theorem block485_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block485LeftL : ℝ) (block485LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block485S1 : ℝ))
    (hy2ne : y ≠ (block485S2 : ℝ))
    (hy3ne : y ≠ (block485S3 : ℝ))
    (hy4ne : y ≠ (block485S4 : ℝ)) :
    0 < block485V y := by
  have hcert := block485LeftCertificate_eq_true
  unfold block485LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block485LeftBoxes) (lo := block485LeftL) (hi := block485LeftR)
    (w1 := block485W1) (w2 := block485W2) (w3 := block485W3) (w4 := block485W4)
    (s1 := block485S1) (s2 := block485S2) (s3 := block485S3) (s4 := block485S4)
    hboxes hcover block485LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block485RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block485RightChunk000 block485W1 block485W2 block485W3 block485W4 block485S1 block485S2 block485S3 block485S4

theorem block485RightChunk000ParamsCertificate_eq_true :
    block485RightChunk000ParamsCertificate = true := by
  native_decide

theorem block485_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block485RightChunk000L : ℝ) (block485RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block485S1 : ℝ))
    (hy2ne : y ≠ (block485S2 : ℝ))
    (hy3ne : y ≠ (block485S3 : ℝ))
    (hy4ne : y ≠ (block485S4 : ℝ)) :
    0 < block485V y := by
  have hcert := block485RightChunk000Certificate_eq_true
  unfold block485RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block485RightChunk000) (lo := block485RightChunk000L) (hi := block485RightChunk000R)
    (w1 := block485W1) (w2 := block485W2) (w3 := block485W3) (w4 := block485W4)
    (s1 := block485S1) (s2 := block485S2) (s3 := block485S3) (s4 := block485S4)
    hboxes hcover block485RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block485_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block485RightL : ℝ) (block485RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block485S1 : ℝ))
    (hy2ne : y ≠ (block485S2 : ℝ))
    (hy3ne : y ≠ (block485S3 : ℝ))
    (hy4ne : y ≠ (block485S4 : ℝ)) :
    0 < block485V y := by
  have hL : (block485RightChunk000L : ℝ) = (block485RightL : ℝ) := by
    norm_num [block485RightChunk000L, block485RightL]
  have hR : (block485RightChunk000R : ℝ) = (block485RightR : ℝ) := by
    norm_num [block485RightChunk000R, block485RightR]
  have hyc : y ∈ Icc (block485RightChunk000L : ℝ) (block485RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block485_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block485_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block485LeftL : ℝ) (block485LeftR : ℝ) →
    y ≠ 0 → y ≠ (block485S1 : ℝ) → y ≠ (block485S2 : ℝ) →
    y ≠ (block485S3 : ℝ) → y ≠ (block485S4 : ℝ) → 0 < block485V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block485RightL : ℝ) (block485RightR : ℝ) →
    y ≠ 0 → y ≠ (block485S1 : ℝ) → y ≠ (block485S2 : ℝ) →
    y ≠ (block485S3 : ℝ) → y ≠ (block485S4 : ℝ) → 0 < block485V y)

theorem block485_reallog_certificate_proof :
    block485_reallog_certificate := by
  exact ⟨block485_left_V_pos, block485_right_V_pos⟩

end Block485
end M1817475
end Erdos1038Lean
