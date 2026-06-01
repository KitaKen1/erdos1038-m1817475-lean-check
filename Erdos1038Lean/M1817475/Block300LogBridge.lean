import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block300

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block300

open Set

def block300W1 : Rat := ((78047089639739 : Rat) / 78125000000000)
def block300W2 : Rat := ((592591459460429 : Rat) / 12500000000000000)
def block300W3 : Rat := ((135468379005417 : Rat) / 500000000000000)
def block300W4 : Rat := (0 : Rat)
def block300S1 : Rat := ((18174751 : Rat) / 10000000)
def block300S2 : Rat := ((511587 : Rat) / 200000)
def block300S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block300S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block300V (y : ℝ) : ℝ :=
  ratPotential block300W1 block300W2 block300W3 block300W4 block300S1 block300S2 block300S3 block300S4 y

def block300LeftParamsCertificate : Bool :=
  allBoxesSameParams block300LeftBoxes block300W1 block300W2 block300W3 block300W4 block300S1 block300S2 block300S3 block300S4

theorem block300LeftParamsCertificate_eq_true :
    block300LeftParamsCertificate = true := by
  native_decide

theorem block300_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block300LeftL : ℝ) (block300LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block300S1 : ℝ))
    (hy2ne : y ≠ (block300S2 : ℝ))
    (hy3ne : y ≠ (block300S3 : ℝ))
    (hy4ne : y ≠ (block300S4 : ℝ)) :
    0 < block300V y := by
  have hcert := block300LeftCertificate_eq_true
  unfold block300LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block300LeftBoxes) (lo := block300LeftL) (hi := block300LeftR)
    (w1 := block300W1) (w2 := block300W2) (w3 := block300W3) (w4 := block300W4)
    (s1 := block300S1) (s2 := block300S2) (s3 := block300S3) (s4 := block300S4)
    hboxes hcover block300LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block300RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block300RightChunk000 block300W1 block300W2 block300W3 block300W4 block300S1 block300S2 block300S3 block300S4

theorem block300RightChunk000ParamsCertificate_eq_true :
    block300RightChunk000ParamsCertificate = true := by
  native_decide

theorem block300_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block300RightChunk000L : ℝ) (block300RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block300S1 : ℝ))
    (hy2ne : y ≠ (block300S2 : ℝ))
    (hy3ne : y ≠ (block300S3 : ℝ))
    (hy4ne : y ≠ (block300S4 : ℝ)) :
    0 < block300V y := by
  have hcert := block300RightChunk000Certificate_eq_true
  unfold block300RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block300RightChunk000) (lo := block300RightChunk000L) (hi := block300RightChunk000R)
    (w1 := block300W1) (w2 := block300W2) (w3 := block300W3) (w4 := block300W4)
    (s1 := block300S1) (s2 := block300S2) (s3 := block300S3) (s4 := block300S4)
    hboxes hcover block300RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block300_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block300RightL : ℝ) (block300RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block300S1 : ℝ))
    (hy2ne : y ≠ (block300S2 : ℝ))
    (hy3ne : y ≠ (block300S3 : ℝ))
    (hy4ne : y ≠ (block300S4 : ℝ)) :
    0 < block300V y := by
  have hL : (block300RightChunk000L : ℝ) = (block300RightL : ℝ) := by
    norm_num [block300RightChunk000L, block300RightL]
  have hR : (block300RightChunk000R : ℝ) = (block300RightR : ℝ) := by
    norm_num [block300RightChunk000R, block300RightR]
  have hyc : y ∈ Icc (block300RightChunk000L : ℝ) (block300RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block300_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block300_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block300LeftL : ℝ) (block300LeftR : ℝ) →
    y ≠ 0 → y ≠ (block300S1 : ℝ) → y ≠ (block300S2 : ℝ) →
    y ≠ (block300S3 : ℝ) → y ≠ (block300S4 : ℝ) → 0 < block300V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block300RightL : ℝ) (block300RightR : ℝ) →
    y ≠ 0 → y ≠ (block300S1 : ℝ) → y ≠ (block300S2 : ℝ) →
    y ≠ (block300S3 : ℝ) → y ≠ (block300S4 : ℝ) → 0 < block300V y)

theorem block300_reallog_certificate_proof :
    block300_reallog_certificate := by
  exact ⟨block300_left_V_pos, block300_right_V_pos⟩

end Block300
end M1817475
end Erdos1038Lean
