import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block282

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block282

open Set

def block282W1 : Rat := ((10289938628935629 : Rat) / 10000000000000000)
def block282W2 : Rat := ((2135240267007591 : Rat) / 62500000000000000)
def block282W3 : Rat := ((14255218390878843 : Rat) / 50000000000000000)
def block282W4 : Rat := (0 : Rat)
def block282S1 : Rat := ((18174751 : Rat) / 10000000)
def block282S2 : Rat := ((511587 : Rat) / 200000)
def block282S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block282S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block282V (y : ℝ) : ℝ :=
  ratPotential block282W1 block282W2 block282W3 block282W4 block282S1 block282S2 block282S3 block282S4 y

def block282LeftParamsCertificate : Bool :=
  allBoxesSameParams block282LeftBoxes block282W1 block282W2 block282W3 block282W4 block282S1 block282S2 block282S3 block282S4

theorem block282LeftParamsCertificate_eq_true :
    block282LeftParamsCertificate = true := by
  native_decide

theorem block282_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block282LeftL : ℝ) (block282LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block282S1 : ℝ))
    (hy2ne : y ≠ (block282S2 : ℝ))
    (hy3ne : y ≠ (block282S3 : ℝ))
    (hy4ne : y ≠ (block282S4 : ℝ)) :
    0 < block282V y := by
  have hcert := block282LeftCertificate_eq_true
  unfold block282LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block282LeftBoxes) (lo := block282LeftL) (hi := block282LeftR)
    (w1 := block282W1) (w2 := block282W2) (w3 := block282W3) (w4 := block282W4)
    (s1 := block282S1) (s2 := block282S2) (s3 := block282S3) (s4 := block282S4)
    hboxes hcover block282LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block282RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block282RightChunk000 block282W1 block282W2 block282W3 block282W4 block282S1 block282S2 block282S3 block282S4

theorem block282RightChunk000ParamsCertificate_eq_true :
    block282RightChunk000ParamsCertificate = true := by
  native_decide

theorem block282_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block282RightChunk000L : ℝ) (block282RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block282S1 : ℝ))
    (hy2ne : y ≠ (block282S2 : ℝ))
    (hy3ne : y ≠ (block282S3 : ℝ))
    (hy4ne : y ≠ (block282S4 : ℝ)) :
    0 < block282V y := by
  have hcert := block282RightChunk000Certificate_eq_true
  unfold block282RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block282RightChunk000) (lo := block282RightChunk000L) (hi := block282RightChunk000R)
    (w1 := block282W1) (w2 := block282W2) (w3 := block282W3) (w4 := block282W4)
    (s1 := block282S1) (s2 := block282S2) (s3 := block282S3) (s4 := block282S4)
    hboxes hcover block282RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block282_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block282RightL : ℝ) (block282RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block282S1 : ℝ))
    (hy2ne : y ≠ (block282S2 : ℝ))
    (hy3ne : y ≠ (block282S3 : ℝ))
    (hy4ne : y ≠ (block282S4 : ℝ)) :
    0 < block282V y := by
  have hL : (block282RightChunk000L : ℝ) = (block282RightL : ℝ) := by
    norm_num [block282RightChunk000L, block282RightL]
  have hR : (block282RightChunk000R : ℝ) = (block282RightR : ℝ) := by
    norm_num [block282RightChunk000R, block282RightR]
  have hyc : y ∈ Icc (block282RightChunk000L : ℝ) (block282RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block282_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block282_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block282LeftL : ℝ) (block282LeftR : ℝ) →
    y ≠ 0 → y ≠ (block282S1 : ℝ) → y ≠ (block282S2 : ℝ) →
    y ≠ (block282S3 : ℝ) → y ≠ (block282S4 : ℝ) → 0 < block282V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block282RightL : ℝ) (block282RightR : ℝ) →
    y ≠ 0 → y ≠ (block282S1 : ℝ) → y ≠ (block282S2 : ℝ) →
    y ≠ (block282S3 : ℝ) → y ≠ (block282S4 : ℝ) → 0 < block282V y)

theorem block282_reallog_certificate_proof :
    block282_reallog_certificate := by
  exact ⟨block282_left_V_pos, block282_right_V_pos⟩

end Block282
end M1817475
end Erdos1038Lean
