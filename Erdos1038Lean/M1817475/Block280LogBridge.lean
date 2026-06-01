import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block280

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block280

open Set

def block280W1 : Rat := ((10289339114851233 : Rat) / 10000000000000000)
def block280W2 : Rat := ((16657304437197363 : Rat) / 500000000000000000)
def block280W3 : Rat := ((5728579038445677 : Rat) / 20000000000000000)
def block280W4 : Rat := (0 : Rat)
def block280S1 : Rat := ((18174751 : Rat) / 10000000)
def block280S2 : Rat := ((511587 : Rat) / 200000)
def block280S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block280S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block280V (y : ℝ) : ℝ :=
  ratPotential block280W1 block280W2 block280W3 block280W4 block280S1 block280S2 block280S3 block280S4 y

def block280LeftParamsCertificate : Bool :=
  allBoxesSameParams block280LeftBoxes block280W1 block280W2 block280W3 block280W4 block280S1 block280S2 block280S3 block280S4

theorem block280LeftParamsCertificate_eq_true :
    block280LeftParamsCertificate = true := by
  native_decide

theorem block280_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block280LeftL : ℝ) (block280LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block280S1 : ℝ))
    (hy2ne : y ≠ (block280S2 : ℝ))
    (hy3ne : y ≠ (block280S3 : ℝ))
    (hy4ne : y ≠ (block280S4 : ℝ)) :
    0 < block280V y := by
  have hcert := block280LeftCertificate_eq_true
  unfold block280LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block280LeftBoxes) (lo := block280LeftL) (hi := block280LeftR)
    (w1 := block280W1) (w2 := block280W2) (w3 := block280W3) (w4 := block280W4)
    (s1 := block280S1) (s2 := block280S2) (s3 := block280S3) (s4 := block280S4)
    hboxes hcover block280LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block280RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block280RightChunk000 block280W1 block280W2 block280W3 block280W4 block280S1 block280S2 block280S3 block280S4

theorem block280RightChunk000ParamsCertificate_eq_true :
    block280RightChunk000ParamsCertificate = true := by
  native_decide

theorem block280_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block280RightChunk000L : ℝ) (block280RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block280S1 : ℝ))
    (hy2ne : y ≠ (block280S2 : ℝ))
    (hy3ne : y ≠ (block280S3 : ℝ))
    (hy4ne : y ≠ (block280S4 : ℝ)) :
    0 < block280V y := by
  have hcert := block280RightChunk000Certificate_eq_true
  unfold block280RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block280RightChunk000) (lo := block280RightChunk000L) (hi := block280RightChunk000R)
    (w1 := block280W1) (w2 := block280W2) (w3 := block280W3) (w4 := block280W4)
    (s1 := block280S1) (s2 := block280S2) (s3 := block280S3) (s4 := block280S4)
    hboxes hcover block280RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block280_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block280RightL : ℝ) (block280RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block280S1 : ℝ))
    (hy2ne : y ≠ (block280S2 : ℝ))
    (hy3ne : y ≠ (block280S3 : ℝ))
    (hy4ne : y ≠ (block280S4 : ℝ)) :
    0 < block280V y := by
  have hL : (block280RightChunk000L : ℝ) = (block280RightL : ℝ) := by
    norm_num [block280RightChunk000L, block280RightL]
  have hR : (block280RightChunk000R : ℝ) = (block280RightR : ℝ) := by
    norm_num [block280RightChunk000R, block280RightR]
  have hyc : y ∈ Icc (block280RightChunk000L : ℝ) (block280RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block280_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block280_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block280LeftL : ℝ) (block280LeftR : ℝ) →
    y ≠ 0 → y ≠ (block280S1 : ℝ) → y ≠ (block280S2 : ℝ) →
    y ≠ (block280S3 : ℝ) → y ≠ (block280S4 : ℝ) → 0 < block280V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block280RightL : ℝ) (block280RightR : ℝ) →
    y ≠ 0 → y ≠ (block280S1 : ℝ) → y ≠ (block280S2 : ℝ) →
    y ≠ (block280S3 : ℝ) → y ≠ (block280S4 : ℝ) → 0 < block280V y)

theorem block280_reallog_certificate_proof :
    block280_reallog_certificate := by
  exact ⟨block280_left_V_pos, block280_right_V_pos⟩

end Block280
end M1817475
end Erdos1038Lean
