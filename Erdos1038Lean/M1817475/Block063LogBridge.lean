import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block063

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block063

open Set

def block063W1 : Rat := ((7310875087661679 : Rat) / 2500000000000000)
def block063W2 : Rat := (0 : Rat)
def block063W3 : Rat := (0 : Rat)
def block063W4 : Rat := ((1288707362155691 : Rat) / 5000000000000000)
def block063S1 : Rat := ((18174751 : Rat) / 10000000)
def block063S2 : Rat := ((511587 : Rat) / 200000)
def block063S3 : Rat := ((107000619 : Rat) / 40000000)
def block063S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block063V (y : ℝ) : ℝ :=
  ratPotential block063W1 block063W2 block063W3 block063W4 block063S1 block063S2 block063S3 block063S4 y

def block063LeftParamsCertificate : Bool :=
  allBoxesSameParams block063LeftBoxes block063W1 block063W2 block063W3 block063W4 block063S1 block063S2 block063S3 block063S4

theorem block063LeftParamsCertificate_eq_true :
    block063LeftParamsCertificate = true := by
  native_decide

theorem block063_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block063LeftL : ℝ) (block063LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block063S1 : ℝ))
    (hy2ne : y ≠ (block063S2 : ℝ))
    (hy3ne : y ≠ (block063S3 : ℝ))
    (hy4ne : y ≠ (block063S4 : ℝ)) :
    0 < block063V y := by
  have hcert := block063LeftCertificate_eq_true
  unfold block063LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block063LeftBoxes) (lo := block063LeftL) (hi := block063LeftR)
    (w1 := block063W1) (w2 := block063W2) (w3 := block063W3) (w4 := block063W4)
    (s1 := block063S1) (s2 := block063S2) (s3 := block063S3) (s4 := block063S4)
    hboxes hcover block063LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block063RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block063RightChunk000 block063W1 block063W2 block063W3 block063W4 block063S1 block063S2 block063S3 block063S4

theorem block063RightChunk000ParamsCertificate_eq_true :
    block063RightChunk000ParamsCertificate = true := by
  native_decide

theorem block063_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block063RightChunk000L : ℝ) (block063RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block063S1 : ℝ))
    (hy2ne : y ≠ (block063S2 : ℝ))
    (hy3ne : y ≠ (block063S3 : ℝ))
    (hy4ne : y ≠ (block063S4 : ℝ)) :
    0 < block063V y := by
  have hcert := block063RightChunk000Certificate_eq_true
  unfold block063RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block063RightChunk000) (lo := block063RightChunk000L) (hi := block063RightChunk000R)
    (w1 := block063W1) (w2 := block063W2) (w3 := block063W3) (w4 := block063W4)
    (s1 := block063S1) (s2 := block063S2) (s3 := block063S3) (s4 := block063S4)
    hboxes hcover block063RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block063_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block063RightL : ℝ) (block063RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block063S1 : ℝ))
    (hy2ne : y ≠ (block063S2 : ℝ))
    (hy3ne : y ≠ (block063S3 : ℝ))
    (hy4ne : y ≠ (block063S4 : ℝ)) :
    0 < block063V y := by
  have hL : (block063RightChunk000L : ℝ) = (block063RightL : ℝ) := by
    norm_num [block063RightChunk000L, block063RightL]
  have hR : (block063RightChunk000R : ℝ) = (block063RightR : ℝ) := by
    norm_num [block063RightChunk000R, block063RightR]
  have hyc : y ∈ Icc (block063RightChunk000L : ℝ) (block063RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block063_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block063_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block063LeftL : ℝ) (block063LeftR : ℝ) →
    y ≠ 0 → y ≠ (block063S1 : ℝ) → y ≠ (block063S2 : ℝ) →
    y ≠ (block063S3 : ℝ) → y ≠ (block063S4 : ℝ) → 0 < block063V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block063RightL : ℝ) (block063RightR : ℝ) →
    y ≠ 0 → y ≠ (block063S1 : ℝ) → y ≠ (block063S2 : ℝ) →
    y ≠ (block063S3 : ℝ) → y ≠ (block063S4 : ℝ) → 0 < block063V y)

theorem block063_reallog_certificate_proof :
    block063_reallog_certificate := by
  exact ⟨block063_left_V_pos, block063_right_V_pos⟩

end Block063
end M1817475
end Erdos1038Lean
