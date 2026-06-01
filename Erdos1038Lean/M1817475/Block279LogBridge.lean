import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block279

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block279

open Set

def block279W1 : Rat := ((10285203227633293 : Rat) / 10000000000000000)
def block279W2 : Rat := ((1647730287288221 : Rat) / 50000000000000000)
def block279W3 : Rat := ((1435326641936179 : Rat) / 5000000000000000)
def block279W4 : Rat := (0 : Rat)
def block279S1 : Rat := ((18174751 : Rat) / 10000000)
def block279S2 : Rat := ((511587 : Rat) / 200000)
def block279S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block279S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block279V (y : ℝ) : ℝ :=
  ratPotential block279W1 block279W2 block279W3 block279W4 block279S1 block279S2 block279S3 block279S4 y

def block279LeftParamsCertificate : Bool :=
  allBoxesSameParams block279LeftBoxes block279W1 block279W2 block279W3 block279W4 block279S1 block279S2 block279S3 block279S4

theorem block279LeftParamsCertificate_eq_true :
    block279LeftParamsCertificate = true := by
  native_decide

theorem block279_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block279LeftL : ℝ) (block279LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block279S1 : ℝ))
    (hy2ne : y ≠ (block279S2 : ℝ))
    (hy3ne : y ≠ (block279S3 : ℝ))
    (hy4ne : y ≠ (block279S4 : ℝ)) :
    0 < block279V y := by
  have hcert := block279LeftCertificate_eq_true
  unfold block279LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block279LeftBoxes) (lo := block279LeftL) (hi := block279LeftR)
    (w1 := block279W1) (w2 := block279W2) (w3 := block279W3) (w4 := block279W4)
    (s1 := block279S1) (s2 := block279S2) (s3 := block279S3) (s4 := block279S4)
    hboxes hcover block279LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block279RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block279RightChunk000 block279W1 block279W2 block279W3 block279W4 block279S1 block279S2 block279S3 block279S4

theorem block279RightChunk000ParamsCertificate_eq_true :
    block279RightChunk000ParamsCertificate = true := by
  native_decide

theorem block279_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block279RightChunk000L : ℝ) (block279RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block279S1 : ℝ))
    (hy2ne : y ≠ (block279S2 : ℝ))
    (hy3ne : y ≠ (block279S3 : ℝ))
    (hy4ne : y ≠ (block279S4 : ℝ)) :
    0 < block279V y := by
  have hcert := block279RightChunk000Certificate_eq_true
  unfold block279RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block279RightChunk000) (lo := block279RightChunk000L) (hi := block279RightChunk000R)
    (w1 := block279W1) (w2 := block279W2) (w3 := block279W3) (w4 := block279W4)
    (s1 := block279S1) (s2 := block279S2) (s3 := block279S3) (s4 := block279S4)
    hboxes hcover block279RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block279_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block279RightL : ℝ) (block279RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block279S1 : ℝ))
    (hy2ne : y ≠ (block279S2 : ℝ))
    (hy3ne : y ≠ (block279S3 : ℝ))
    (hy4ne : y ≠ (block279S4 : ℝ)) :
    0 < block279V y := by
  have hL : (block279RightChunk000L : ℝ) = (block279RightL : ℝ) := by
    norm_num [block279RightChunk000L, block279RightL]
  have hR : (block279RightChunk000R : ℝ) = (block279RightR : ℝ) := by
    norm_num [block279RightChunk000R, block279RightR]
  have hyc : y ∈ Icc (block279RightChunk000L : ℝ) (block279RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block279_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block279_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block279LeftL : ℝ) (block279LeftR : ℝ) →
    y ≠ 0 → y ≠ (block279S1 : ℝ) → y ≠ (block279S2 : ℝ) →
    y ≠ (block279S3 : ℝ) → y ≠ (block279S4 : ℝ) → 0 < block279V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block279RightL : ℝ) (block279RightR : ℝ) →
    y ≠ 0 → y ≠ (block279S1 : ℝ) → y ≠ (block279S2 : ℝ) →
    y ≠ (block279S3 : ℝ) → y ≠ (block279S4 : ℝ) → 0 < block279V y)

theorem block279_reallog_certificate_proof :
    block279_reallog_certificate := by
  exact ⟨block279_left_V_pos, block279_right_V_pos⟩

end Block279
end M1817475
end Erdos1038Lean
