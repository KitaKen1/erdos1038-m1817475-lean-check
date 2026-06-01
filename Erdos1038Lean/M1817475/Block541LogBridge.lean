import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block541

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block541

open Set

def block541W1 : Rat := ((3966291379401927 : Rat) / 10000000000000000)
def block541W2 : Rat := (0 : Rat)
def block541W3 : Rat := ((9127472570898103 : Rat) / 20000000000000000)
def block541W4 : Rat := (0 : Rat)
def block541S1 : Rat := ((18174751 : Rat) / 10000000)
def block541S2 : Rat := ((511587 : Rat) / 200000)
def block541S3 : Rat := ((129557490267857143041 : Rat) / 50000000000000000000)
def block541S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block541V (y : ℝ) : ℝ :=
  ratPotential block541W1 block541W2 block541W3 block541W4 block541S1 block541S2 block541S3 block541S4 y

def block541LeftParamsCertificate : Bool :=
  allBoxesSameParams block541LeftBoxes block541W1 block541W2 block541W3 block541W4 block541S1 block541S2 block541S3 block541S4

theorem block541LeftParamsCertificate_eq_true :
    block541LeftParamsCertificate = true := by
  native_decide

theorem block541_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block541LeftL : ℝ) (block541LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block541S1 : ℝ))
    (hy2ne : y ≠ (block541S2 : ℝ))
    (hy3ne : y ≠ (block541S3 : ℝ))
    (hy4ne : y ≠ (block541S4 : ℝ)) :
    0 < block541V y := by
  have hcert := block541LeftCertificate_eq_true
  unfold block541LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block541LeftBoxes) (lo := block541LeftL) (hi := block541LeftR)
    (w1 := block541W1) (w2 := block541W2) (w3 := block541W3) (w4 := block541W4)
    (s1 := block541S1) (s2 := block541S2) (s3 := block541S3) (s4 := block541S4)
    hboxes hcover block541LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block541RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block541RightChunk000 block541W1 block541W2 block541W3 block541W4 block541S1 block541S2 block541S3 block541S4

theorem block541RightChunk000ParamsCertificate_eq_true :
    block541RightChunk000ParamsCertificate = true := by
  native_decide

theorem block541_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block541RightChunk000L : ℝ) (block541RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block541S1 : ℝ))
    (hy2ne : y ≠ (block541S2 : ℝ))
    (hy3ne : y ≠ (block541S3 : ℝ))
    (hy4ne : y ≠ (block541S4 : ℝ)) :
    0 < block541V y := by
  have hcert := block541RightChunk000Certificate_eq_true
  unfold block541RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block541RightChunk000) (lo := block541RightChunk000L) (hi := block541RightChunk000R)
    (w1 := block541W1) (w2 := block541W2) (w3 := block541W3) (w4 := block541W4)
    (s1 := block541S1) (s2 := block541S2) (s3 := block541S3) (s4 := block541S4)
    hboxes hcover block541RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block541_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block541RightL : ℝ) (block541RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block541S1 : ℝ))
    (hy2ne : y ≠ (block541S2 : ℝ))
    (hy3ne : y ≠ (block541S3 : ℝ))
    (hy4ne : y ≠ (block541S4 : ℝ)) :
    0 < block541V y := by
  have hL : (block541RightChunk000L : ℝ) = (block541RightL : ℝ) := by
    norm_num [block541RightChunk000L, block541RightL]
  have hR : (block541RightChunk000R : ℝ) = (block541RightR : ℝ) := by
    norm_num [block541RightChunk000R, block541RightR]
  have hyc : y ∈ Icc (block541RightChunk000L : ℝ) (block541RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block541_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block541_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block541LeftL : ℝ) (block541LeftR : ℝ) →
    y ≠ 0 → y ≠ (block541S1 : ℝ) → y ≠ (block541S2 : ℝ) →
    y ≠ (block541S3 : ℝ) → y ≠ (block541S4 : ℝ) → 0 < block541V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block541RightL : ℝ) (block541RightR : ℝ) →
    y ≠ 0 → y ≠ (block541S1 : ℝ) → y ≠ (block541S2 : ℝ) →
    y ≠ (block541S3 : ℝ) → y ≠ (block541S4 : ℝ) → 0 < block541V y)

theorem block541_reallog_certificate_proof :
    block541_reallog_certificate := by
  exact ⟨block541_left_V_pos, block541_right_V_pos⟩

end Block541
end M1817475
end Erdos1038Lean
