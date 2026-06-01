import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block431

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block431

open Set

def block431W1 : Rat := ((6531046464273399 : Rat) / 10000000000000000)
def block431W2 : Rat := (0 : Rat)
def block431W3 : Rat := ((96630763089379 : Rat) / 312500000000000)
def block431W4 : Rat := ((7913290147598923 : Rat) / 100000000000000000)
def block431S1 : Rat := ((18174751 : Rat) / 10000000)
def block431S2 : Rat := ((511587 : Rat) / 200000)
def block431S3 : Rat := ((131707892053571428661 : Rat) / 50000000000000000000)
def block431S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block431V (y : ℝ) : ℝ :=
  ratPotential block431W1 block431W2 block431W3 block431W4 block431S1 block431S2 block431S3 block431S4 y

def block431LeftParamsCertificate : Bool :=
  allBoxesSameParams block431LeftBoxes block431W1 block431W2 block431W3 block431W4 block431S1 block431S2 block431S3 block431S4

theorem block431LeftParamsCertificate_eq_true :
    block431LeftParamsCertificate = true := by
  native_decide

theorem block431_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block431LeftL : ℝ) (block431LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block431S1 : ℝ))
    (hy2ne : y ≠ (block431S2 : ℝ))
    (hy3ne : y ≠ (block431S3 : ℝ))
    (hy4ne : y ≠ (block431S4 : ℝ)) :
    0 < block431V y := by
  have hcert := block431LeftCertificate_eq_true
  unfold block431LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block431LeftBoxes) (lo := block431LeftL) (hi := block431LeftR)
    (w1 := block431W1) (w2 := block431W2) (w3 := block431W3) (w4 := block431W4)
    (s1 := block431S1) (s2 := block431S2) (s3 := block431S3) (s4 := block431S4)
    hboxes hcover block431LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block431RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block431RightChunk000 block431W1 block431W2 block431W3 block431W4 block431S1 block431S2 block431S3 block431S4

theorem block431RightChunk000ParamsCertificate_eq_true :
    block431RightChunk000ParamsCertificate = true := by
  native_decide

theorem block431_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block431RightChunk000L : ℝ) (block431RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block431S1 : ℝ))
    (hy2ne : y ≠ (block431S2 : ℝ))
    (hy3ne : y ≠ (block431S3 : ℝ))
    (hy4ne : y ≠ (block431S4 : ℝ)) :
    0 < block431V y := by
  have hcert := block431RightChunk000Certificate_eq_true
  unfold block431RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block431RightChunk000) (lo := block431RightChunk000L) (hi := block431RightChunk000R)
    (w1 := block431W1) (w2 := block431W2) (w3 := block431W3) (w4 := block431W4)
    (s1 := block431S1) (s2 := block431S2) (s3 := block431S3) (s4 := block431S4)
    hboxes hcover block431RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block431_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block431RightL : ℝ) (block431RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block431S1 : ℝ))
    (hy2ne : y ≠ (block431S2 : ℝ))
    (hy3ne : y ≠ (block431S3 : ℝ))
    (hy4ne : y ≠ (block431S4 : ℝ)) :
    0 < block431V y := by
  have hL : (block431RightChunk000L : ℝ) = (block431RightL : ℝ) := by
    norm_num [block431RightChunk000L, block431RightL]
  have hR : (block431RightChunk000R : ℝ) = (block431RightR : ℝ) := by
    norm_num [block431RightChunk000R, block431RightR]
  have hyc : y ∈ Icc (block431RightChunk000L : ℝ) (block431RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block431_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block431_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block431LeftL : ℝ) (block431LeftR : ℝ) →
    y ≠ 0 → y ≠ (block431S1 : ℝ) → y ≠ (block431S2 : ℝ) →
    y ≠ (block431S3 : ℝ) → y ≠ (block431S4 : ℝ) → 0 < block431V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block431RightL : ℝ) (block431RightR : ℝ) →
    y ≠ 0 → y ≠ (block431S1 : ℝ) → y ≠ (block431S2 : ℝ) →
    y ≠ (block431S3 : ℝ) → y ≠ (block431S4 : ℝ) → 0 < block431V y)

theorem block431_reallog_certificate_proof :
    block431_reallog_certificate := by
  exact ⟨block431_left_V_pos, block431_right_V_pos⟩

end Block431
end M1817475
end Erdos1038Lean
