import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block269

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block269

open Set

def block269W1 : Rat := ((2057273042178649 : Rat) / 2000000000000000)
def block269W2 : Rat := ((5738575520482337 : Rat) / 200000000000000000)
def block269W3 : Rat := ((14683518859142447 : Rat) / 50000000000000000)
def block269W4 : Rat := (0 : Rat)
def block269S1 : Rat := ((18174751 : Rat) / 10000000)
def block269S2 : Rat := ((511587 : Rat) / 200000)
def block269S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block269S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block269V (y : ℝ) : ℝ :=
  ratPotential block269W1 block269W2 block269W3 block269W4 block269S1 block269S2 block269S3 block269S4 y

def block269LeftParamsCertificate : Bool :=
  allBoxesSameParams block269LeftBoxes block269W1 block269W2 block269W3 block269W4 block269S1 block269S2 block269S3 block269S4

theorem block269LeftParamsCertificate_eq_true :
    block269LeftParamsCertificate = true := by
  native_decide

theorem block269_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block269LeftL : ℝ) (block269LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block269S1 : ℝ))
    (hy2ne : y ≠ (block269S2 : ℝ))
    (hy3ne : y ≠ (block269S3 : ℝ))
    (hy4ne : y ≠ (block269S4 : ℝ)) :
    0 < block269V y := by
  have hcert := block269LeftCertificate_eq_true
  unfold block269LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block269LeftBoxes) (lo := block269LeftL) (hi := block269LeftR)
    (w1 := block269W1) (w2 := block269W2) (w3 := block269W3) (w4 := block269W4)
    (s1 := block269S1) (s2 := block269S2) (s3 := block269S3) (s4 := block269S4)
    hboxes hcover block269LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block269RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block269RightChunk000 block269W1 block269W2 block269W3 block269W4 block269S1 block269S2 block269S3 block269S4

theorem block269RightChunk000ParamsCertificate_eq_true :
    block269RightChunk000ParamsCertificate = true := by
  native_decide

theorem block269_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block269RightChunk000L : ℝ) (block269RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block269S1 : ℝ))
    (hy2ne : y ≠ (block269S2 : ℝ))
    (hy3ne : y ≠ (block269S3 : ℝ))
    (hy4ne : y ≠ (block269S4 : ℝ)) :
    0 < block269V y := by
  have hcert := block269RightChunk000Certificate_eq_true
  unfold block269RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block269RightChunk000) (lo := block269RightChunk000L) (hi := block269RightChunk000R)
    (w1 := block269W1) (w2 := block269W2) (w3 := block269W3) (w4 := block269W4)
    (s1 := block269S1) (s2 := block269S2) (s3 := block269S3) (s4 := block269S4)
    hboxes hcover block269RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block269_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block269RightL : ℝ) (block269RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block269S1 : ℝ))
    (hy2ne : y ≠ (block269S2 : ℝ))
    (hy3ne : y ≠ (block269S3 : ℝ))
    (hy4ne : y ≠ (block269S4 : ℝ)) :
    0 < block269V y := by
  have hL : (block269RightChunk000L : ℝ) = (block269RightL : ℝ) := by
    norm_num [block269RightChunk000L, block269RightL]
  have hR : (block269RightChunk000R : ℝ) = (block269RightR : ℝ) := by
    norm_num [block269RightChunk000R, block269RightR]
  have hyc : y ∈ Icc (block269RightChunk000L : ℝ) (block269RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block269_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block269_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block269LeftL : ℝ) (block269LeftR : ℝ) →
    y ≠ 0 → y ≠ (block269S1 : ℝ) → y ≠ (block269S2 : ℝ) →
    y ≠ (block269S3 : ℝ) → y ≠ (block269S4 : ℝ) → 0 < block269V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block269RightL : ℝ) (block269RightR : ℝ) →
    y ≠ 0 → y ≠ (block269S1 : ℝ) → y ≠ (block269S2 : ℝ) →
    y ≠ (block269S3 : ℝ) → y ≠ (block269S4 : ℝ) → 0 < block269V y)

theorem block269_reallog_certificate_proof :
    block269_reallog_certificate := by
  exact ⟨block269_left_V_pos, block269_right_V_pos⟩

end Block269
end M1817475
end Erdos1038Lean
