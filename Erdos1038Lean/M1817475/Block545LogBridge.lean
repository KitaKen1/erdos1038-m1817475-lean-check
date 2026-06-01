import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block545

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block545

open Set

def block545W1 : Rat := ((1963245143370107 : Rat) / 5000000000000000)
def block545W2 : Rat := (0 : Rat)
def block545W3 : Rat := ((228948807258609 : Rat) / 500000000000000)
def block545W4 : Rat := (0 : Rat)
def block545S1 : Rat := ((18174751 : Rat) / 10000000)
def block545S2 : Rat := ((511587 : Rat) / 200000)
def block545S3 : Rat := ((129479293839285714473 : Rat) / 50000000000000000000)
def block545S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block545V (y : ℝ) : ℝ :=
  ratPotential block545W1 block545W2 block545W3 block545W4 block545S1 block545S2 block545S3 block545S4 y

def block545LeftParamsCertificate : Bool :=
  allBoxesSameParams block545LeftBoxes block545W1 block545W2 block545W3 block545W4 block545S1 block545S2 block545S3 block545S4

theorem block545LeftParamsCertificate_eq_true :
    block545LeftParamsCertificate = true := by
  native_decide

theorem block545_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block545LeftL : ℝ) (block545LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block545S1 : ℝ))
    (hy2ne : y ≠ (block545S2 : ℝ))
    (hy3ne : y ≠ (block545S3 : ℝ))
    (hy4ne : y ≠ (block545S4 : ℝ)) :
    0 < block545V y := by
  have hcert := block545LeftCertificate_eq_true
  unfold block545LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block545LeftBoxes) (lo := block545LeftL) (hi := block545LeftR)
    (w1 := block545W1) (w2 := block545W2) (w3 := block545W3) (w4 := block545W4)
    (s1 := block545S1) (s2 := block545S2) (s3 := block545S3) (s4 := block545S4)
    hboxes hcover block545LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block545RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block545RightChunk000 block545W1 block545W2 block545W3 block545W4 block545S1 block545S2 block545S3 block545S4

theorem block545RightChunk000ParamsCertificate_eq_true :
    block545RightChunk000ParamsCertificate = true := by
  native_decide

theorem block545_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block545RightChunk000L : ℝ) (block545RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block545S1 : ℝ))
    (hy2ne : y ≠ (block545S2 : ℝ))
    (hy3ne : y ≠ (block545S3 : ℝ))
    (hy4ne : y ≠ (block545S4 : ℝ)) :
    0 < block545V y := by
  have hcert := block545RightChunk000Certificate_eq_true
  unfold block545RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block545RightChunk000) (lo := block545RightChunk000L) (hi := block545RightChunk000R)
    (w1 := block545W1) (w2 := block545W2) (w3 := block545W3) (w4 := block545W4)
    (s1 := block545S1) (s2 := block545S2) (s3 := block545S3) (s4 := block545S4)
    hboxes hcover block545RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block545_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block545RightL : ℝ) (block545RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block545S1 : ℝ))
    (hy2ne : y ≠ (block545S2 : ℝ))
    (hy3ne : y ≠ (block545S3 : ℝ))
    (hy4ne : y ≠ (block545S4 : ℝ)) :
    0 < block545V y := by
  have hL : (block545RightChunk000L : ℝ) = (block545RightL : ℝ) := by
    norm_num [block545RightChunk000L, block545RightL]
  have hR : (block545RightChunk000R : ℝ) = (block545RightR : ℝ) := by
    norm_num [block545RightChunk000R, block545RightR]
  have hyc : y ∈ Icc (block545RightChunk000L : ℝ) (block545RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block545_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block545_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block545LeftL : ℝ) (block545LeftR : ℝ) →
    y ≠ 0 → y ≠ (block545S1 : ℝ) → y ≠ (block545S2 : ℝ) →
    y ≠ (block545S3 : ℝ) → y ≠ (block545S4 : ℝ) → 0 < block545V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block545RightL : ℝ) (block545RightR : ℝ) →
    y ≠ 0 → y ≠ (block545S1 : ℝ) → y ≠ (block545S2 : ℝ) →
    y ≠ (block545S3 : ℝ) → y ≠ (block545S4 : ℝ) → 0 < block545V y)

theorem block545_reallog_certificate_proof :
    block545_reallog_certificate := by
  exact ⟨block545_left_V_pos, block545_right_V_pos⟩

end Block545
end M1817475
end Erdos1038Lean
