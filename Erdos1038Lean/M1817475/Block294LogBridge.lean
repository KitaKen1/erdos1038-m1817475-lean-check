import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block294

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block294

open Set

def block294W1 : Rat := ((2031760370300269 : Rat) / 2000000000000000)
def block294W2 : Rat := ((8332230287780383 : Rat) / 200000000000000000)
def block294W3 : Rat := ((1104768687047889 : Rat) / 4000000000000000)
def block294W4 : Rat := (0 : Rat)
def block294S1 : Rat := ((18174751 : Rat) / 10000000)
def block294S2 : Rat := ((511587 : Rat) / 200000)
def block294S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block294S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block294V (y : ℝ) : ℝ :=
  ratPotential block294W1 block294W2 block294W3 block294W4 block294S1 block294S2 block294S3 block294S4 y

def block294LeftParamsCertificate : Bool :=
  allBoxesSameParams block294LeftBoxes block294W1 block294W2 block294W3 block294W4 block294S1 block294S2 block294S3 block294S4

theorem block294LeftParamsCertificate_eq_true :
    block294LeftParamsCertificate = true := by
  native_decide

theorem block294_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block294LeftL : ℝ) (block294LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block294S1 : ℝ))
    (hy2ne : y ≠ (block294S2 : ℝ))
    (hy3ne : y ≠ (block294S3 : ℝ))
    (hy4ne : y ≠ (block294S4 : ℝ)) :
    0 < block294V y := by
  have hcert := block294LeftCertificate_eq_true
  unfold block294LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block294LeftBoxes) (lo := block294LeftL) (hi := block294LeftR)
    (w1 := block294W1) (w2 := block294W2) (w3 := block294W3) (w4 := block294W4)
    (s1 := block294S1) (s2 := block294S2) (s3 := block294S3) (s4 := block294S4)
    hboxes hcover block294LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block294RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block294RightChunk000 block294W1 block294W2 block294W3 block294W4 block294S1 block294S2 block294S3 block294S4

theorem block294RightChunk000ParamsCertificate_eq_true :
    block294RightChunk000ParamsCertificate = true := by
  native_decide

theorem block294_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block294RightChunk000L : ℝ) (block294RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block294S1 : ℝ))
    (hy2ne : y ≠ (block294S2 : ℝ))
    (hy3ne : y ≠ (block294S3 : ℝ))
    (hy4ne : y ≠ (block294S4 : ℝ)) :
    0 < block294V y := by
  have hcert := block294RightChunk000Certificate_eq_true
  unfold block294RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block294RightChunk000) (lo := block294RightChunk000L) (hi := block294RightChunk000R)
    (w1 := block294W1) (w2 := block294W2) (w3 := block294W3) (w4 := block294W4)
    (s1 := block294S1) (s2 := block294S2) (s3 := block294S3) (s4 := block294S4)
    hboxes hcover block294RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block294_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block294RightL : ℝ) (block294RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block294S1 : ℝ))
    (hy2ne : y ≠ (block294S2 : ℝ))
    (hy3ne : y ≠ (block294S3 : ℝ))
    (hy4ne : y ≠ (block294S4 : ℝ)) :
    0 < block294V y := by
  have hL : (block294RightChunk000L : ℝ) = (block294RightL : ℝ) := by
    norm_num [block294RightChunk000L, block294RightL]
  have hR : (block294RightChunk000R : ℝ) = (block294RightR : ℝ) := by
    norm_num [block294RightChunk000R, block294RightR]
  have hyc : y ∈ Icc (block294RightChunk000L : ℝ) (block294RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block294_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block294_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block294LeftL : ℝ) (block294LeftR : ℝ) →
    y ≠ 0 → y ≠ (block294S1 : ℝ) → y ≠ (block294S2 : ℝ) →
    y ≠ (block294S3 : ℝ) → y ≠ (block294S4 : ℝ) → 0 < block294V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block294RightL : ℝ) (block294RightR : ℝ) →
    y ≠ 0 → y ≠ (block294S1 : ℝ) → y ≠ (block294S2 : ℝ) →
    y ≠ (block294S3 : ℝ) → y ≠ (block294S4 : ℝ) → 0 < block294V y)

theorem block294_reallog_certificate_proof :
    block294_reallog_certificate := by
  exact ⟨block294_left_V_pos, block294_right_V_pos⟩

end Block294
end M1817475
end Erdos1038Lean
