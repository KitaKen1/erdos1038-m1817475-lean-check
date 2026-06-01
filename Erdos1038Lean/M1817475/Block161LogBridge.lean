import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block161

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block161

open Set

def block161W1 : Rat := ((929206980264691 : Rat) / 500000000000000)
def block161W2 : Rat := (0 : Rat)
def block161W3 : Rat := ((8103019062853553 : Rat) / 50000000000000000)
def block161W4 : Rat := ((5263339521820941 : Rat) / 50000000000000000)
def block161S1 : Rat := ((18174751 : Rat) / 10000000)
def block161S2 : Rat := ((511587 : Rat) / 200000)
def block161S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block161S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block161V (y : ℝ) : ℝ :=
  ratPotential block161W1 block161W2 block161W3 block161W4 block161S1 block161S2 block161S3 block161S4 y

def block161LeftParamsCertificate : Bool :=
  allBoxesSameParams block161LeftBoxes block161W1 block161W2 block161W3 block161W4 block161S1 block161S2 block161S3 block161S4

theorem block161LeftParamsCertificate_eq_true :
    block161LeftParamsCertificate = true := by
  native_decide

theorem block161_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block161LeftL : ℝ) (block161LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block161S1 : ℝ))
    (hy2ne : y ≠ (block161S2 : ℝ))
    (hy3ne : y ≠ (block161S3 : ℝ))
    (hy4ne : y ≠ (block161S4 : ℝ)) :
    0 < block161V y := by
  have hcert := block161LeftCertificate_eq_true
  unfold block161LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block161LeftBoxes) (lo := block161LeftL) (hi := block161LeftR)
    (w1 := block161W1) (w2 := block161W2) (w3 := block161W3) (w4 := block161W4)
    (s1 := block161S1) (s2 := block161S2) (s3 := block161S3) (s4 := block161S4)
    hboxes hcover block161LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block161RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block161RightChunk000 block161W1 block161W2 block161W3 block161W4 block161S1 block161S2 block161S3 block161S4

theorem block161RightChunk000ParamsCertificate_eq_true :
    block161RightChunk000ParamsCertificate = true := by
  native_decide

theorem block161_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block161RightChunk000L : ℝ) (block161RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block161S1 : ℝ))
    (hy2ne : y ≠ (block161S2 : ℝ))
    (hy3ne : y ≠ (block161S3 : ℝ))
    (hy4ne : y ≠ (block161S4 : ℝ)) :
    0 < block161V y := by
  have hcert := block161RightChunk000Certificate_eq_true
  unfold block161RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block161RightChunk000) (lo := block161RightChunk000L) (hi := block161RightChunk000R)
    (w1 := block161W1) (w2 := block161W2) (w3 := block161W3) (w4 := block161W4)
    (s1 := block161S1) (s2 := block161S2) (s3 := block161S3) (s4 := block161S4)
    hboxes hcover block161RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block161_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block161RightL : ℝ) (block161RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block161S1 : ℝ))
    (hy2ne : y ≠ (block161S2 : ℝ))
    (hy3ne : y ≠ (block161S3 : ℝ))
    (hy4ne : y ≠ (block161S4 : ℝ)) :
    0 < block161V y := by
  have hL : (block161RightChunk000L : ℝ) = (block161RightL : ℝ) := by
    norm_num [block161RightChunk000L, block161RightL]
  have hR : (block161RightChunk000R : ℝ) = (block161RightR : ℝ) := by
    norm_num [block161RightChunk000R, block161RightR]
  have hyc : y ∈ Icc (block161RightChunk000L : ℝ) (block161RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block161_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block161_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block161LeftL : ℝ) (block161LeftR : ℝ) →
    y ≠ 0 → y ≠ (block161S1 : ℝ) → y ≠ (block161S2 : ℝ) →
    y ≠ (block161S3 : ℝ) → y ≠ (block161S4 : ℝ) → 0 < block161V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block161RightL : ℝ) (block161RightR : ℝ) →
    y ≠ 0 → y ≠ (block161S1 : ℝ) → y ≠ (block161S2 : ℝ) →
    y ≠ (block161S3 : ℝ) → y ≠ (block161S4 : ℝ) → 0 < block161V y)

theorem block161_reallog_certificate_proof :
    block161_reallog_certificate := by
  exact ⟨block161_left_V_pos, block161_right_V_pos⟩

end Block161
end M1817475
end Erdos1038Lean
