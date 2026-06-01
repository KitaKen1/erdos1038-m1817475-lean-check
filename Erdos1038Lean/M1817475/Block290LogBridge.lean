import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block290

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block290

open Set

def block290W1 : Rat := ((10270117595800017 : Rat) / 10000000000000000)
def block290W2 : Rat := ((3796853901458541 : Rat) / 100000000000000000)
def block290W3 : Rat := ((349541384225821 : Rat) / 1250000000000000)
def block290W4 : Rat := (0 : Rat)
def block290S1 : Rat := ((18174751 : Rat) / 10000000)
def block290S2 : Rat := ((511587 : Rat) / 200000)
def block290S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block290S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block290V (y : ℝ) : ℝ :=
  ratPotential block290W1 block290W2 block290W3 block290W4 block290S1 block290S2 block290S3 block290S4 y

def block290LeftParamsCertificate : Bool :=
  allBoxesSameParams block290LeftBoxes block290W1 block290W2 block290W3 block290W4 block290S1 block290S2 block290S3 block290S4

theorem block290LeftParamsCertificate_eq_true :
    block290LeftParamsCertificate = true := by
  native_decide

theorem block290_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block290LeftL : ℝ) (block290LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block290S1 : ℝ))
    (hy2ne : y ≠ (block290S2 : ℝ))
    (hy3ne : y ≠ (block290S3 : ℝ))
    (hy4ne : y ≠ (block290S4 : ℝ)) :
    0 < block290V y := by
  have hcert := block290LeftCertificate_eq_true
  unfold block290LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block290LeftBoxes) (lo := block290LeftL) (hi := block290LeftR)
    (w1 := block290W1) (w2 := block290W2) (w3 := block290W3) (w4 := block290W4)
    (s1 := block290S1) (s2 := block290S2) (s3 := block290S3) (s4 := block290S4)
    hboxes hcover block290LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block290RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block290RightChunk000 block290W1 block290W2 block290W3 block290W4 block290S1 block290S2 block290S3 block290S4

theorem block290RightChunk000ParamsCertificate_eq_true :
    block290RightChunk000ParamsCertificate = true := by
  native_decide

theorem block290_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block290RightChunk000L : ℝ) (block290RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block290S1 : ℝ))
    (hy2ne : y ≠ (block290S2 : ℝ))
    (hy3ne : y ≠ (block290S3 : ℝ))
    (hy4ne : y ≠ (block290S4 : ℝ)) :
    0 < block290V y := by
  have hcert := block290RightChunk000Certificate_eq_true
  unfold block290RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block290RightChunk000) (lo := block290RightChunk000L) (hi := block290RightChunk000R)
    (w1 := block290W1) (w2 := block290W2) (w3 := block290W3) (w4 := block290W4)
    (s1 := block290S1) (s2 := block290S2) (s3 := block290S3) (s4 := block290S4)
    hboxes hcover block290RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block290_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block290RightL : ℝ) (block290RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block290S1 : ℝ))
    (hy2ne : y ≠ (block290S2 : ℝ))
    (hy3ne : y ≠ (block290S3 : ℝ))
    (hy4ne : y ≠ (block290S4 : ℝ)) :
    0 < block290V y := by
  have hL : (block290RightChunk000L : ℝ) = (block290RightL : ℝ) := by
    norm_num [block290RightChunk000L, block290RightL]
  have hR : (block290RightChunk000R : ℝ) = (block290RightR : ℝ) := by
    norm_num [block290RightChunk000R, block290RightR]
  have hyc : y ∈ Icc (block290RightChunk000L : ℝ) (block290RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block290_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block290_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block290LeftL : ℝ) (block290LeftR : ℝ) →
    y ≠ 0 → y ≠ (block290S1 : ℝ) → y ≠ (block290S2 : ℝ) →
    y ≠ (block290S3 : ℝ) → y ≠ (block290S4 : ℝ) → 0 < block290V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block290RightL : ℝ) (block290RightR : ℝ) →
    y ≠ 0 → y ≠ (block290S1 : ℝ) → y ≠ (block290S2 : ℝ) →
    y ≠ (block290S3 : ℝ) → y ≠ (block290S4 : ℝ) → 0 < block290V y)

theorem block290_reallog_certificate_proof :
    block290_reallog_certificate := by
  exact ⟨block290_left_V_pos, block290_right_V_pos⟩

end Block290
end M1817475
end Erdos1038Lean
