import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block122

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block122

open Set

def block122W1 : Rat := ((2851268233568583 : Rat) / 1250000000000000)
def block122W2 : Rat := (0 : Rat)
def block122W3 : Rat := ((4912487409790657 : Rat) / 50000000000000000)
def block122W4 : Rat := ((240104986586997 : Rat) / 1562500000000000)
def block122S1 : Rat := ((18174751 : Rat) / 10000000)
def block122S2 : Rat := ((511587 : Rat) / 200000)
def block122S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block122S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block122V (y : ℝ) : ℝ :=
  ratPotential block122W1 block122W2 block122W3 block122W4 block122S1 block122S2 block122S3 block122S4 y

def block122LeftParamsCertificate : Bool :=
  allBoxesSameParams block122LeftBoxes block122W1 block122W2 block122W3 block122W4 block122S1 block122S2 block122S3 block122S4

theorem block122LeftParamsCertificate_eq_true :
    block122LeftParamsCertificate = true := by
  native_decide

theorem block122_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block122LeftL : ℝ) (block122LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block122S1 : ℝ))
    (hy2ne : y ≠ (block122S2 : ℝ))
    (hy3ne : y ≠ (block122S3 : ℝ))
    (hy4ne : y ≠ (block122S4 : ℝ)) :
    0 < block122V y := by
  have hcert := block122LeftCertificate_eq_true
  unfold block122LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block122LeftBoxes) (lo := block122LeftL) (hi := block122LeftR)
    (w1 := block122W1) (w2 := block122W2) (w3 := block122W3) (w4 := block122W4)
    (s1 := block122S1) (s2 := block122S2) (s3 := block122S3) (s4 := block122S4)
    hboxes hcover block122LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block122RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block122RightChunk000 block122W1 block122W2 block122W3 block122W4 block122S1 block122S2 block122S3 block122S4

theorem block122RightChunk000ParamsCertificate_eq_true :
    block122RightChunk000ParamsCertificate = true := by
  native_decide

theorem block122_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block122RightChunk000L : ℝ) (block122RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block122S1 : ℝ))
    (hy2ne : y ≠ (block122S2 : ℝ))
    (hy3ne : y ≠ (block122S3 : ℝ))
    (hy4ne : y ≠ (block122S4 : ℝ)) :
    0 < block122V y := by
  have hcert := block122RightChunk000Certificate_eq_true
  unfold block122RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block122RightChunk000) (lo := block122RightChunk000L) (hi := block122RightChunk000R)
    (w1 := block122W1) (w2 := block122W2) (w3 := block122W3) (w4 := block122W4)
    (s1 := block122S1) (s2 := block122S2) (s3 := block122S3) (s4 := block122S4)
    hboxes hcover block122RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block122_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block122RightL : ℝ) (block122RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block122S1 : ℝ))
    (hy2ne : y ≠ (block122S2 : ℝ))
    (hy3ne : y ≠ (block122S3 : ℝ))
    (hy4ne : y ≠ (block122S4 : ℝ)) :
    0 < block122V y := by
  have hL : (block122RightChunk000L : ℝ) = (block122RightL : ℝ) := by
    norm_num [block122RightChunk000L, block122RightL]
  have hR : (block122RightChunk000R : ℝ) = (block122RightR : ℝ) := by
    norm_num [block122RightChunk000R, block122RightR]
  have hyc : y ∈ Icc (block122RightChunk000L : ℝ) (block122RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block122_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block122_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block122LeftL : ℝ) (block122LeftR : ℝ) →
    y ≠ 0 → y ≠ (block122S1 : ℝ) → y ≠ (block122S2 : ℝ) →
    y ≠ (block122S3 : ℝ) → y ≠ (block122S4 : ℝ) → 0 < block122V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block122RightL : ℝ) (block122RightR : ℝ) →
    y ≠ 0 → y ≠ (block122S1 : ℝ) → y ≠ (block122S2 : ℝ) →
    y ≠ (block122S3 : ℝ) → y ≠ (block122S4 : ℝ) → 0 < block122V y)

theorem block122_reallog_certificate_proof :
    block122_reallog_certificate := by
  exact ⟨block122_left_V_pos, block122_right_V_pos⟩

end Block122
end M1817475
end Erdos1038Lean
