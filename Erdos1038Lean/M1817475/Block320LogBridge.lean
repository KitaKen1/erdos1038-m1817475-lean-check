import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block320

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block320

open Set

def block320W1 : Rat := ((9411988214393121 : Rat) / 10000000000000000)
def block320W2 : Rat := ((1367942865867497 : Rat) / 20000000000000000)
def block320W3 : Rat := ((2525996512775417 : Rat) / 10000000000000000)
def block320W4 : Rat := (0 : Rat)
def block320S1 : Rat := ((18174751 : Rat) / 10000000)
def block320S2 : Rat := ((511587 : Rat) / 200000)
def block320S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block320S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block320V (y : ℝ) : ℝ :=
  ratPotential block320W1 block320W2 block320W3 block320W4 block320S1 block320S2 block320S3 block320S4 y

def block320LeftParamsCertificate : Bool :=
  allBoxesSameParams block320LeftBoxes block320W1 block320W2 block320W3 block320W4 block320S1 block320S2 block320S3 block320S4

theorem block320LeftParamsCertificate_eq_true :
    block320LeftParamsCertificate = true := by
  native_decide

theorem block320_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block320LeftL : ℝ) (block320LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block320S1 : ℝ))
    (hy2ne : y ≠ (block320S2 : ℝ))
    (hy3ne : y ≠ (block320S3 : ℝ))
    (hy4ne : y ≠ (block320S4 : ℝ)) :
    0 < block320V y := by
  have hcert := block320LeftCertificate_eq_true
  unfold block320LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block320LeftBoxes) (lo := block320LeftL) (hi := block320LeftR)
    (w1 := block320W1) (w2 := block320W2) (w3 := block320W3) (w4 := block320W4)
    (s1 := block320S1) (s2 := block320S2) (s3 := block320S3) (s4 := block320S4)
    hboxes hcover block320LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block320RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block320RightChunk000 block320W1 block320W2 block320W3 block320W4 block320S1 block320S2 block320S3 block320S4

theorem block320RightChunk000ParamsCertificate_eq_true :
    block320RightChunk000ParamsCertificate = true := by
  native_decide

theorem block320_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block320RightChunk000L : ℝ) (block320RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block320S1 : ℝ))
    (hy2ne : y ≠ (block320S2 : ℝ))
    (hy3ne : y ≠ (block320S3 : ℝ))
    (hy4ne : y ≠ (block320S4 : ℝ)) :
    0 < block320V y := by
  have hcert := block320RightChunk000Certificate_eq_true
  unfold block320RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block320RightChunk000) (lo := block320RightChunk000L) (hi := block320RightChunk000R)
    (w1 := block320W1) (w2 := block320W2) (w3 := block320W3) (w4 := block320W4)
    (s1 := block320S1) (s2 := block320S2) (s3 := block320S3) (s4 := block320S4)
    hboxes hcover block320RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block320_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block320RightL : ℝ) (block320RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block320S1 : ℝ))
    (hy2ne : y ≠ (block320S2 : ℝ))
    (hy3ne : y ≠ (block320S3 : ℝ))
    (hy4ne : y ≠ (block320S4 : ℝ)) :
    0 < block320V y := by
  have hL : (block320RightChunk000L : ℝ) = (block320RightL : ℝ) := by
    norm_num [block320RightChunk000L, block320RightL]
  have hR : (block320RightChunk000R : ℝ) = (block320RightR : ℝ) := by
    norm_num [block320RightChunk000R, block320RightR]
  have hyc : y ∈ Icc (block320RightChunk000L : ℝ) (block320RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block320_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block320_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block320LeftL : ℝ) (block320LeftR : ℝ) →
    y ≠ 0 → y ≠ (block320S1 : ℝ) → y ≠ (block320S2 : ℝ) →
    y ≠ (block320S3 : ℝ) → y ≠ (block320S4 : ℝ) → 0 < block320V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block320RightL : ℝ) (block320RightR : ℝ) →
    y ≠ 0 → y ≠ (block320S1 : ℝ) → y ≠ (block320S2 : ℝ) →
    y ≠ (block320S3 : ℝ) → y ≠ (block320S4 : ℝ) → 0 < block320V y)

theorem block320_reallog_certificate_proof :
    block320_reallog_certificate := by
  exact ⟨block320_left_V_pos, block320_right_V_pos⟩

end Block320
end M1817475
end Erdos1038Lean
