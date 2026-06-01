import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block358

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block358

open Set

def block358W1 : Rat := ((2225243964898163 : Rat) / 2500000000000000)
def block358W2 : Rat := ((4753310348523179 : Rat) / 100000000000000000)
def block358W3 : Rat := ((1890056571812761 : Rat) / 12500000000000000)
def block358W4 : Rat := ((1735726401084859 : Rat) / 12500000000000000)
def block358S1 : Rat := ((18174751 : Rat) / 10000000)
def block358S2 : Rat := ((511587 : Rat) / 200000)
def block358S3 : Rat := ((133134976875000000027 : Rat) / 50000000000000000000)
def block358S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block358V (y : ℝ) : ℝ :=
  ratPotential block358W1 block358W2 block358W3 block358W4 block358S1 block358S2 block358S3 block358S4 y

def block358LeftParamsCertificate : Bool :=
  allBoxesSameParams block358LeftBoxes block358W1 block358W2 block358W3 block358W4 block358S1 block358S2 block358S3 block358S4

theorem block358LeftParamsCertificate_eq_true :
    block358LeftParamsCertificate = true := by
  native_decide

theorem block358_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block358LeftL : ℝ) (block358LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block358S1 : ℝ))
    (hy2ne : y ≠ (block358S2 : ℝ))
    (hy3ne : y ≠ (block358S3 : ℝ))
    (hy4ne : y ≠ (block358S4 : ℝ)) :
    0 < block358V y := by
  have hcert := block358LeftCertificate_eq_true
  unfold block358LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block358LeftBoxes) (lo := block358LeftL) (hi := block358LeftR)
    (w1 := block358W1) (w2 := block358W2) (w3 := block358W3) (w4 := block358W4)
    (s1 := block358S1) (s2 := block358S2) (s3 := block358S3) (s4 := block358S4)
    hboxes hcover block358LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block358RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block358RightChunk000 block358W1 block358W2 block358W3 block358W4 block358S1 block358S2 block358S3 block358S4

theorem block358RightChunk000ParamsCertificate_eq_true :
    block358RightChunk000ParamsCertificate = true := by
  native_decide

theorem block358_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block358RightChunk000L : ℝ) (block358RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block358S1 : ℝ))
    (hy2ne : y ≠ (block358S2 : ℝ))
    (hy3ne : y ≠ (block358S3 : ℝ))
    (hy4ne : y ≠ (block358S4 : ℝ)) :
    0 < block358V y := by
  have hcert := block358RightChunk000Certificate_eq_true
  unfold block358RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block358RightChunk000) (lo := block358RightChunk000L) (hi := block358RightChunk000R)
    (w1 := block358W1) (w2 := block358W2) (w3 := block358W3) (w4 := block358W4)
    (s1 := block358S1) (s2 := block358S2) (s3 := block358S3) (s4 := block358S4)
    hboxes hcover block358RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block358_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block358RightL : ℝ) (block358RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block358S1 : ℝ))
    (hy2ne : y ≠ (block358S2 : ℝ))
    (hy3ne : y ≠ (block358S3 : ℝ))
    (hy4ne : y ≠ (block358S4 : ℝ)) :
    0 < block358V y := by
  have hL : (block358RightChunk000L : ℝ) = (block358RightL : ℝ) := by
    norm_num [block358RightChunk000L, block358RightL]
  have hR : (block358RightChunk000R : ℝ) = (block358RightR : ℝ) := by
    norm_num [block358RightChunk000R, block358RightR]
  have hyc : y ∈ Icc (block358RightChunk000L : ℝ) (block358RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block358_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block358_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block358LeftL : ℝ) (block358LeftR : ℝ) →
    y ≠ 0 → y ≠ (block358S1 : ℝ) → y ≠ (block358S2 : ℝ) →
    y ≠ (block358S3 : ℝ) → y ≠ (block358S4 : ℝ) → 0 < block358V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block358RightL : ℝ) (block358RightR : ℝ) →
    y ≠ 0 → y ≠ (block358S1 : ℝ) → y ≠ (block358S2 : ℝ) →
    y ≠ (block358S3 : ℝ) → y ≠ (block358S4 : ℝ) → 0 < block358V y)

theorem block358_reallog_certificate_proof :
    block358_reallog_certificate := by
  exact ⟨block358_left_V_pos, block358_right_V_pos⟩

end Block358
end M1817475
end Erdos1038Lean
