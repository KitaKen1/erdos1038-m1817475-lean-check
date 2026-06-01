import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block025

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block025

open Set

def block025W1 : Rat := ((23061763465848077 : Rat) / 10000000000000000)
def block025W2 : Rat := (0 : Rat)
def block025W3 : Rat := (0 : Rat)
def block025W4 : Rat := ((14335835671281977 : Rat) / 50000000000000000)
def block025S1 : Rat := ((18174751 : Rat) / 10000000)
def block025S2 : Rat := ((511587 : Rat) / 200000)
def block025S3 : Rat := ((107000619 : Rat) / 40000000)
def block025S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block025V (y : ℝ) : ℝ :=
  ratPotential block025W1 block025W2 block025W3 block025W4 block025S1 block025S2 block025S3 block025S4 y

def block025LeftParamsCertificate : Bool :=
  allBoxesSameParams block025LeftBoxes block025W1 block025W2 block025W3 block025W4 block025S1 block025S2 block025S3 block025S4

theorem block025LeftParamsCertificate_eq_true :
    block025LeftParamsCertificate = true := by
  native_decide

theorem block025_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block025LeftL : ℝ) (block025LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block025S1 : ℝ))
    (hy2ne : y ≠ (block025S2 : ℝ))
    (hy3ne : y ≠ (block025S3 : ℝ))
    (hy4ne : y ≠ (block025S4 : ℝ)) :
    0 < block025V y := by
  have hcert := block025LeftCertificate_eq_true
  unfold block025LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block025LeftBoxes) (lo := block025LeftL) (hi := block025LeftR)
    (w1 := block025W1) (w2 := block025W2) (w3 := block025W3) (w4 := block025W4)
    (s1 := block025S1) (s2 := block025S2) (s3 := block025S3) (s4 := block025S4)
    hboxes hcover block025LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block025RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block025RightChunk000 block025W1 block025W2 block025W3 block025W4 block025S1 block025S2 block025S3 block025S4

theorem block025RightChunk000ParamsCertificate_eq_true :
    block025RightChunk000ParamsCertificate = true := by
  native_decide

theorem block025_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block025RightChunk000L : ℝ) (block025RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block025S1 : ℝ))
    (hy2ne : y ≠ (block025S2 : ℝ))
    (hy3ne : y ≠ (block025S3 : ℝ))
    (hy4ne : y ≠ (block025S4 : ℝ)) :
    0 < block025V y := by
  have hcert := block025RightChunk000Certificate_eq_true
  unfold block025RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block025RightChunk000) (lo := block025RightChunk000L) (hi := block025RightChunk000R)
    (w1 := block025W1) (w2 := block025W2) (w3 := block025W3) (w4 := block025W4)
    (s1 := block025S1) (s2 := block025S2) (s3 := block025S3) (s4 := block025S4)
    hboxes hcover block025RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block025_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block025RightL : ℝ) (block025RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block025S1 : ℝ))
    (hy2ne : y ≠ (block025S2 : ℝ))
    (hy3ne : y ≠ (block025S3 : ℝ))
    (hy4ne : y ≠ (block025S4 : ℝ)) :
    0 < block025V y := by
  have hL : (block025RightChunk000L : ℝ) = (block025RightL : ℝ) := by
    norm_num [block025RightChunk000L, block025RightL]
  have hR : (block025RightChunk000R : ℝ) = (block025RightR : ℝ) := by
    norm_num [block025RightChunk000R, block025RightR]
  have hyc : y ∈ Icc (block025RightChunk000L : ℝ) (block025RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block025_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block025_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block025LeftL : ℝ) (block025LeftR : ℝ) →
    y ≠ 0 → y ≠ (block025S1 : ℝ) → y ≠ (block025S2 : ℝ) →
    y ≠ (block025S3 : ℝ) → y ≠ (block025S4 : ℝ) → 0 < block025V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block025RightL : ℝ) (block025RightR : ℝ) →
    y ≠ 0 → y ≠ (block025S1 : ℝ) → y ≠ (block025S2 : ℝ) →
    y ≠ (block025S3 : ℝ) → y ≠ (block025S4 : ℝ) → 0 < block025V y)

theorem block025_reallog_certificate_proof :
    block025_reallog_certificate := by
  exact ⟨block025_left_V_pos, block025_right_V_pos⟩

end Block025
end M1817475
end Erdos1038Lean
