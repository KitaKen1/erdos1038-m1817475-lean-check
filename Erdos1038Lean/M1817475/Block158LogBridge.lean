import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block158

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block158

open Set

def block158W1 : Rat := ((18699629862222447 : Rat) / 10000000000000000)
def block158W2 : Rat := (0 : Rat)
def block158W3 : Rat := ((1602382889761217 : Rat) / 10000000000000000)
def block158W4 : Rat := ((10659795420268289 : Rat) / 100000000000000000)
def block158S1 : Rat := ((18174751 : Rat) / 10000000)
def block158S2 : Rat := ((511587 : Rat) / 200000)
def block158S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block158S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block158V (y : ℝ) : ℝ :=
  ratPotential block158W1 block158W2 block158W3 block158W4 block158S1 block158S2 block158S3 block158S4 y

def block158LeftParamsCertificate : Bool :=
  allBoxesSameParams block158LeftBoxes block158W1 block158W2 block158W3 block158W4 block158S1 block158S2 block158S3 block158S4

theorem block158LeftParamsCertificate_eq_true :
    block158LeftParamsCertificate = true := by
  native_decide

theorem block158_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block158LeftL : ℝ) (block158LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block158S1 : ℝ))
    (hy2ne : y ≠ (block158S2 : ℝ))
    (hy3ne : y ≠ (block158S3 : ℝ))
    (hy4ne : y ≠ (block158S4 : ℝ)) :
    0 < block158V y := by
  have hcert := block158LeftCertificate_eq_true
  unfold block158LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block158LeftBoxes) (lo := block158LeftL) (hi := block158LeftR)
    (w1 := block158W1) (w2 := block158W2) (w3 := block158W3) (w4 := block158W4)
    (s1 := block158S1) (s2 := block158S2) (s3 := block158S3) (s4 := block158S4)
    hboxes hcover block158LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block158RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block158RightChunk000 block158W1 block158W2 block158W3 block158W4 block158S1 block158S2 block158S3 block158S4

theorem block158RightChunk000ParamsCertificate_eq_true :
    block158RightChunk000ParamsCertificate = true := by
  native_decide

theorem block158_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block158RightChunk000L : ℝ) (block158RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block158S1 : ℝ))
    (hy2ne : y ≠ (block158S2 : ℝ))
    (hy3ne : y ≠ (block158S3 : ℝ))
    (hy4ne : y ≠ (block158S4 : ℝ)) :
    0 < block158V y := by
  have hcert := block158RightChunk000Certificate_eq_true
  unfold block158RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block158RightChunk000) (lo := block158RightChunk000L) (hi := block158RightChunk000R)
    (w1 := block158W1) (w2 := block158W2) (w3 := block158W3) (w4 := block158W4)
    (s1 := block158S1) (s2 := block158S2) (s3 := block158S3) (s4 := block158S4)
    hboxes hcover block158RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block158_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block158RightL : ℝ) (block158RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block158S1 : ℝ))
    (hy2ne : y ≠ (block158S2 : ℝ))
    (hy3ne : y ≠ (block158S3 : ℝ))
    (hy4ne : y ≠ (block158S4 : ℝ)) :
    0 < block158V y := by
  have hL : (block158RightChunk000L : ℝ) = (block158RightL : ℝ) := by
    norm_num [block158RightChunk000L, block158RightL]
  have hR : (block158RightChunk000R : ℝ) = (block158RightR : ℝ) := by
    norm_num [block158RightChunk000R, block158RightR]
  have hyc : y ∈ Icc (block158RightChunk000L : ℝ) (block158RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block158_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block158_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block158LeftL : ℝ) (block158LeftR : ℝ) →
    y ≠ 0 → y ≠ (block158S1 : ℝ) → y ≠ (block158S2 : ℝ) →
    y ≠ (block158S3 : ℝ) → y ≠ (block158S4 : ℝ) → 0 < block158V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block158RightL : ℝ) (block158RightR : ℝ) →
    y ≠ 0 → y ≠ (block158S1 : ℝ) → y ≠ (block158S2 : ℝ) →
    y ≠ (block158S3 : ℝ) → y ≠ (block158S4 : ℝ) → 0 < block158V y)

theorem block158_reallog_certificate_proof :
    block158_reallog_certificate := by
  exact ⟨block158_left_V_pos, block158_right_V_pos⟩

end Block158
end M1817475
end Erdos1038Lean
