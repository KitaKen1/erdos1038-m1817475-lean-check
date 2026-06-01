import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block296

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block296

open Set

def block296W1 : Rat := ((10102785015469553 : Rat) / 10000000000000000)
def block296W2 : Rat := ((21774395629272157 : Rat) / 500000000000000000)
def block296W3 : Rat := ((3430661367615323 : Rat) / 12500000000000000)
def block296W4 : Rat := (0 : Rat)
def block296S1 : Rat := ((18174751 : Rat) / 10000000)
def block296S2 : Rat := ((511587 : Rat) / 200000)
def block296S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block296S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block296V (y : ℝ) : ℝ :=
  ratPotential block296W1 block296W2 block296W3 block296W4 block296S1 block296S2 block296S3 block296S4 y

def block296LeftParamsCertificate : Bool :=
  allBoxesSameParams block296LeftBoxes block296W1 block296W2 block296W3 block296W4 block296S1 block296S2 block296S3 block296S4

theorem block296LeftParamsCertificate_eq_true :
    block296LeftParamsCertificate = true := by
  native_decide

theorem block296_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block296LeftL : ℝ) (block296LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block296S1 : ℝ))
    (hy2ne : y ≠ (block296S2 : ℝ))
    (hy3ne : y ≠ (block296S3 : ℝ))
    (hy4ne : y ≠ (block296S4 : ℝ)) :
    0 < block296V y := by
  have hcert := block296LeftCertificate_eq_true
  unfold block296LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block296LeftBoxes) (lo := block296LeftL) (hi := block296LeftR)
    (w1 := block296W1) (w2 := block296W2) (w3 := block296W3) (w4 := block296W4)
    (s1 := block296S1) (s2 := block296S2) (s3 := block296S3) (s4 := block296S4)
    hboxes hcover block296LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block296RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block296RightChunk000 block296W1 block296W2 block296W3 block296W4 block296S1 block296S2 block296S3 block296S4

theorem block296RightChunk000ParamsCertificate_eq_true :
    block296RightChunk000ParamsCertificate = true := by
  native_decide

theorem block296_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block296RightChunk000L : ℝ) (block296RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block296S1 : ℝ))
    (hy2ne : y ≠ (block296S2 : ℝ))
    (hy3ne : y ≠ (block296S3 : ℝ))
    (hy4ne : y ≠ (block296S4 : ℝ)) :
    0 < block296V y := by
  have hcert := block296RightChunk000Certificate_eq_true
  unfold block296RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block296RightChunk000) (lo := block296RightChunk000L) (hi := block296RightChunk000R)
    (w1 := block296W1) (w2 := block296W2) (w3 := block296W3) (w4 := block296W4)
    (s1 := block296S1) (s2 := block296S2) (s3 := block296S3) (s4 := block296S4)
    hboxes hcover block296RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block296_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block296RightL : ℝ) (block296RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block296S1 : ℝ))
    (hy2ne : y ≠ (block296S2 : ℝ))
    (hy3ne : y ≠ (block296S3 : ℝ))
    (hy4ne : y ≠ (block296S4 : ℝ)) :
    0 < block296V y := by
  have hL : (block296RightChunk000L : ℝ) = (block296RightL : ℝ) := by
    norm_num [block296RightChunk000L, block296RightL]
  have hR : (block296RightChunk000R : ℝ) = (block296RightR : ℝ) := by
    norm_num [block296RightChunk000R, block296RightR]
  have hyc : y ∈ Icc (block296RightChunk000L : ℝ) (block296RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block296_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block296_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block296LeftL : ℝ) (block296LeftR : ℝ) →
    y ≠ 0 → y ≠ (block296S1 : ℝ) → y ≠ (block296S2 : ℝ) →
    y ≠ (block296S3 : ℝ) → y ≠ (block296S4 : ℝ) → 0 < block296V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block296RightL : ℝ) (block296RightR : ℝ) →
    y ≠ 0 → y ≠ (block296S1 : ℝ) → y ≠ (block296S2 : ℝ) →
    y ≠ (block296S3 : ℝ) → y ≠ (block296S4 : ℝ) → 0 < block296V y)

theorem block296_reallog_certificate_proof :
    block296_reallog_certificate := by
  exact ⟨block296_left_V_pos, block296_right_V_pos⟩

end Block296
end M1817475
end Erdos1038Lean
