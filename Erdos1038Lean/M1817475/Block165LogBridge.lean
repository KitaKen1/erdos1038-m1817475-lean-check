import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block165

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block165

open Set

def block165W1 : Rat := ((9212476283452431 : Rat) / 5000000000000000)
def block165W2 : Rat := (0 : Rat)
def block165W3 : Rat := ((4115073596850479 : Rat) / 25000000000000000)
def block165W4 : Rat := ((517123569283297 : Rat) / 5000000000000000)
def block165S1 : Rat := ((18174751 : Rat) / 10000000)
def block165S2 : Rat := ((511587 : Rat) / 200000)
def block165S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block165S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block165V (y : ℝ) : ℝ :=
  ratPotential block165W1 block165W2 block165W3 block165W4 block165S1 block165S2 block165S3 block165S4 y

def block165LeftParamsCertificate : Bool :=
  allBoxesSameParams block165LeftBoxes block165W1 block165W2 block165W3 block165W4 block165S1 block165S2 block165S3 block165S4

theorem block165LeftParamsCertificate_eq_true :
    block165LeftParamsCertificate = true := by
  native_decide

theorem block165_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block165LeftL : ℝ) (block165LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block165S1 : ℝ))
    (hy2ne : y ≠ (block165S2 : ℝ))
    (hy3ne : y ≠ (block165S3 : ℝ))
    (hy4ne : y ≠ (block165S4 : ℝ)) :
    0 < block165V y := by
  have hcert := block165LeftCertificate_eq_true
  unfold block165LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block165LeftBoxes) (lo := block165LeftL) (hi := block165LeftR)
    (w1 := block165W1) (w2 := block165W2) (w3 := block165W3) (w4 := block165W4)
    (s1 := block165S1) (s2 := block165S2) (s3 := block165S3) (s4 := block165S4)
    hboxes hcover block165LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block165RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block165RightChunk000 block165W1 block165W2 block165W3 block165W4 block165S1 block165S2 block165S3 block165S4

theorem block165RightChunk000ParamsCertificate_eq_true :
    block165RightChunk000ParamsCertificate = true := by
  native_decide

theorem block165_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block165RightChunk000L : ℝ) (block165RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block165S1 : ℝ))
    (hy2ne : y ≠ (block165S2 : ℝ))
    (hy3ne : y ≠ (block165S3 : ℝ))
    (hy4ne : y ≠ (block165S4 : ℝ)) :
    0 < block165V y := by
  have hcert := block165RightChunk000Certificate_eq_true
  unfold block165RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block165RightChunk000) (lo := block165RightChunk000L) (hi := block165RightChunk000R)
    (w1 := block165W1) (w2 := block165W2) (w3 := block165W3) (w4 := block165W4)
    (s1 := block165S1) (s2 := block165S2) (s3 := block165S3) (s4 := block165S4)
    hboxes hcover block165RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block165_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block165RightL : ℝ) (block165RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block165S1 : ℝ))
    (hy2ne : y ≠ (block165S2 : ℝ))
    (hy3ne : y ≠ (block165S3 : ℝ))
    (hy4ne : y ≠ (block165S4 : ℝ)) :
    0 < block165V y := by
  have hL : (block165RightChunk000L : ℝ) = (block165RightL : ℝ) := by
    norm_num [block165RightChunk000L, block165RightL]
  have hR : (block165RightChunk000R : ℝ) = (block165RightR : ℝ) := by
    norm_num [block165RightChunk000R, block165RightR]
  have hyc : y ∈ Icc (block165RightChunk000L : ℝ) (block165RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block165_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block165_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block165LeftL : ℝ) (block165LeftR : ℝ) →
    y ≠ 0 → y ≠ (block165S1 : ℝ) → y ≠ (block165S2 : ℝ) →
    y ≠ (block165S3 : ℝ) → y ≠ (block165S4 : ℝ) → 0 < block165V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block165RightL : ℝ) (block165RightR : ℝ) →
    y ≠ 0 → y ≠ (block165S1 : ℝ) → y ≠ (block165S2 : ℝ) →
    y ≠ (block165S3 : ℝ) → y ≠ (block165S4 : ℝ) → 0 < block165V y)

theorem block165_reallog_certificate_proof :
    block165_reallog_certificate := by
  exact ⟨block165_left_V_pos, block165_right_V_pos⟩

end Block165
end M1817475
end Erdos1038Lean
