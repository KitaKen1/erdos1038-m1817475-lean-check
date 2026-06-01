import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block467

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block467

open Set

def block467W1 : Rat := ((549828225947349 : Rat) / 1000000000000000)
def block467W2 : Rat := (0 : Rat)
def block467W3 : Rat := ((3572890015554167 : Rat) / 10000000000000000)
def block467W4 : Rat := ((843832792316569 : Rat) / 15625000000000000)
def block467S1 : Rat := ((18174751 : Rat) / 10000000)
def block467S2 : Rat := ((511587 : Rat) / 200000)
def block467S3 : Rat := ((131004124196428571549 : Rat) / 50000000000000000000)
def block467S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block467V (y : ℝ) : ℝ :=
  ratPotential block467W1 block467W2 block467W3 block467W4 block467S1 block467S2 block467S3 block467S4 y

def block467LeftParamsCertificate : Bool :=
  allBoxesSameParams block467LeftBoxes block467W1 block467W2 block467W3 block467W4 block467S1 block467S2 block467S3 block467S4

theorem block467LeftParamsCertificate_eq_true :
    block467LeftParamsCertificate = true := by
  native_decide

theorem block467_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block467LeftL : ℝ) (block467LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block467S1 : ℝ))
    (hy2ne : y ≠ (block467S2 : ℝ))
    (hy3ne : y ≠ (block467S3 : ℝ))
    (hy4ne : y ≠ (block467S4 : ℝ)) :
    0 < block467V y := by
  have hcert := block467LeftCertificate_eq_true
  unfold block467LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block467LeftBoxes) (lo := block467LeftL) (hi := block467LeftR)
    (w1 := block467W1) (w2 := block467W2) (w3 := block467W3) (w4 := block467W4)
    (s1 := block467S1) (s2 := block467S2) (s3 := block467S3) (s4 := block467S4)
    hboxes hcover block467LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block467RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block467RightChunk000 block467W1 block467W2 block467W3 block467W4 block467S1 block467S2 block467S3 block467S4

theorem block467RightChunk000ParamsCertificate_eq_true :
    block467RightChunk000ParamsCertificate = true := by
  native_decide

theorem block467_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block467RightChunk000L : ℝ) (block467RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block467S1 : ℝ))
    (hy2ne : y ≠ (block467S2 : ℝ))
    (hy3ne : y ≠ (block467S3 : ℝ))
    (hy4ne : y ≠ (block467S4 : ℝ)) :
    0 < block467V y := by
  have hcert := block467RightChunk000Certificate_eq_true
  unfold block467RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block467RightChunk000) (lo := block467RightChunk000L) (hi := block467RightChunk000R)
    (w1 := block467W1) (w2 := block467W2) (w3 := block467W3) (w4 := block467W4)
    (s1 := block467S1) (s2 := block467S2) (s3 := block467S3) (s4 := block467S4)
    hboxes hcover block467RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block467_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block467RightL : ℝ) (block467RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block467S1 : ℝ))
    (hy2ne : y ≠ (block467S2 : ℝ))
    (hy3ne : y ≠ (block467S3 : ℝ))
    (hy4ne : y ≠ (block467S4 : ℝ)) :
    0 < block467V y := by
  have hL : (block467RightChunk000L : ℝ) = (block467RightL : ℝ) := by
    norm_num [block467RightChunk000L, block467RightL]
  have hR : (block467RightChunk000R : ℝ) = (block467RightR : ℝ) := by
    norm_num [block467RightChunk000R, block467RightR]
  have hyc : y ∈ Icc (block467RightChunk000L : ℝ) (block467RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block467_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block467_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block467LeftL : ℝ) (block467LeftR : ℝ) →
    y ≠ 0 → y ≠ (block467S1 : ℝ) → y ≠ (block467S2 : ℝ) →
    y ≠ (block467S3 : ℝ) → y ≠ (block467S4 : ℝ) → 0 < block467V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block467RightL : ℝ) (block467RightR : ℝ) →
    y ≠ 0 → y ≠ (block467S1 : ℝ) → y ≠ (block467S2 : ℝ) →
    y ≠ (block467S3 : ℝ) → y ≠ (block467S4 : ℝ) → 0 < block467V y)

theorem block467_reallog_certificate_proof :
    block467_reallog_certificate := by
  exact ⟨block467_left_V_pos, block467_right_V_pos⟩

end Block467
end M1817475
end Erdos1038Lean
