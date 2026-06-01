import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block515

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block515

open Set

def block515W1 : Rat := ((1059266271026933 : Rat) / 2500000000000000)
def block515W2 : Rat := (0 : Rat)
def block515W3 : Rat := ((44651490918562303 : Rat) / 100000000000000000)
def block515W4 : Rat := (0 : Rat)
def block515S1 : Rat := ((18174751 : Rat) / 10000000)
def block515S2 : Rat := ((511587 : Rat) / 200000)
def block515S3 : Rat := ((130065767053571428733 : Rat) / 50000000000000000000)
def block515S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block515V (y : ℝ) : ℝ :=
  ratPotential block515W1 block515W2 block515W3 block515W4 block515S1 block515S2 block515S3 block515S4 y

def block515LeftParamsCertificate : Bool :=
  allBoxesSameParams block515LeftBoxes block515W1 block515W2 block515W3 block515W4 block515S1 block515S2 block515S3 block515S4

theorem block515LeftParamsCertificate_eq_true :
    block515LeftParamsCertificate = true := by
  native_decide

theorem block515_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block515LeftL : ℝ) (block515LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block515S1 : ℝ))
    (hy2ne : y ≠ (block515S2 : ℝ))
    (hy3ne : y ≠ (block515S3 : ℝ))
    (hy4ne : y ≠ (block515S4 : ℝ)) :
    0 < block515V y := by
  have hcert := block515LeftCertificate_eq_true
  unfold block515LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block515LeftBoxes) (lo := block515LeftL) (hi := block515LeftR)
    (w1 := block515W1) (w2 := block515W2) (w3 := block515W3) (w4 := block515W4)
    (s1 := block515S1) (s2 := block515S2) (s3 := block515S3) (s4 := block515S4)
    hboxes hcover block515LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block515RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block515RightChunk000 block515W1 block515W2 block515W3 block515W4 block515S1 block515S2 block515S3 block515S4

theorem block515RightChunk000ParamsCertificate_eq_true :
    block515RightChunk000ParamsCertificate = true := by
  native_decide

theorem block515_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block515RightChunk000L : ℝ) (block515RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block515S1 : ℝ))
    (hy2ne : y ≠ (block515S2 : ℝ))
    (hy3ne : y ≠ (block515S3 : ℝ))
    (hy4ne : y ≠ (block515S4 : ℝ)) :
    0 < block515V y := by
  have hcert := block515RightChunk000Certificate_eq_true
  unfold block515RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block515RightChunk000) (lo := block515RightChunk000L) (hi := block515RightChunk000R)
    (w1 := block515W1) (w2 := block515W2) (w3 := block515W3) (w4 := block515W4)
    (s1 := block515S1) (s2 := block515S2) (s3 := block515S3) (s4 := block515S4)
    hboxes hcover block515RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block515_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block515RightL : ℝ) (block515RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block515S1 : ℝ))
    (hy2ne : y ≠ (block515S2 : ℝ))
    (hy3ne : y ≠ (block515S3 : ℝ))
    (hy4ne : y ≠ (block515S4 : ℝ)) :
    0 < block515V y := by
  have hL : (block515RightChunk000L : ℝ) = (block515RightL : ℝ) := by
    norm_num [block515RightChunk000L, block515RightL]
  have hR : (block515RightChunk000R : ℝ) = (block515RightR : ℝ) := by
    norm_num [block515RightChunk000R, block515RightR]
  have hyc : y ∈ Icc (block515RightChunk000L : ℝ) (block515RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block515_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block515_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block515LeftL : ℝ) (block515LeftR : ℝ) →
    y ≠ 0 → y ≠ (block515S1 : ℝ) → y ≠ (block515S2 : ℝ) →
    y ≠ (block515S3 : ℝ) → y ≠ (block515S4 : ℝ) → 0 < block515V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block515RightL : ℝ) (block515RightR : ℝ) →
    y ≠ 0 → y ≠ (block515S1 : ℝ) → y ≠ (block515S2 : ℝ) →
    y ≠ (block515S3 : ℝ) → y ≠ (block515S4 : ℝ) → 0 < block515V y)

theorem block515_reallog_certificate_proof :
    block515_reallog_certificate := by
  exact ⟨block515_left_V_pos, block515_right_V_pos⟩

end Block515
end M1817475
end Erdos1038Lean
