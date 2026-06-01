import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block062

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block062

open Set

def block062W1 : Rat := ((29037664662611267 : Rat) / 10000000000000000)
def block062W2 : Rat := (0 : Rat)
def block062W3 : Rat := (0 : Rat)
def block062W4 : Rat := ((25860365577022637 : Rat) / 100000000000000000)
def block062S1 : Rat := ((18174751 : Rat) / 10000000)
def block062S2 : Rat := ((511587 : Rat) / 200000)
def block062S3 : Rat := ((107000619 : Rat) / 40000000)
def block062S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block062V (y : ℝ) : ℝ :=
  ratPotential block062W1 block062W2 block062W3 block062W4 block062S1 block062S2 block062S3 block062S4 y

def block062LeftParamsCertificate : Bool :=
  allBoxesSameParams block062LeftBoxes block062W1 block062W2 block062W3 block062W4 block062S1 block062S2 block062S3 block062S4

theorem block062LeftParamsCertificate_eq_true :
    block062LeftParamsCertificate = true := by
  native_decide

theorem block062_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block062LeftL : ℝ) (block062LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block062S1 : ℝ))
    (hy2ne : y ≠ (block062S2 : ℝ))
    (hy3ne : y ≠ (block062S3 : ℝ))
    (hy4ne : y ≠ (block062S4 : ℝ)) :
    0 < block062V y := by
  have hcert := block062LeftCertificate_eq_true
  unfold block062LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block062LeftBoxes) (lo := block062LeftL) (hi := block062LeftR)
    (w1 := block062W1) (w2 := block062W2) (w3 := block062W3) (w4 := block062W4)
    (s1 := block062S1) (s2 := block062S2) (s3 := block062S3) (s4 := block062S4)
    hboxes hcover block062LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block062RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block062RightChunk000 block062W1 block062W2 block062W3 block062W4 block062S1 block062S2 block062S3 block062S4

theorem block062RightChunk000ParamsCertificate_eq_true :
    block062RightChunk000ParamsCertificate = true := by
  native_decide

theorem block062_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block062RightChunk000L : ℝ) (block062RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block062S1 : ℝ))
    (hy2ne : y ≠ (block062S2 : ℝ))
    (hy3ne : y ≠ (block062S3 : ℝ))
    (hy4ne : y ≠ (block062S4 : ℝ)) :
    0 < block062V y := by
  have hcert := block062RightChunk000Certificate_eq_true
  unfold block062RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block062RightChunk000) (lo := block062RightChunk000L) (hi := block062RightChunk000R)
    (w1 := block062W1) (w2 := block062W2) (w3 := block062W3) (w4 := block062W4)
    (s1 := block062S1) (s2 := block062S2) (s3 := block062S3) (s4 := block062S4)
    hboxes hcover block062RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block062_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block062RightL : ℝ) (block062RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block062S1 : ℝ))
    (hy2ne : y ≠ (block062S2 : ℝ))
    (hy3ne : y ≠ (block062S3 : ℝ))
    (hy4ne : y ≠ (block062S4 : ℝ)) :
    0 < block062V y := by
  have hL : (block062RightChunk000L : ℝ) = (block062RightL : ℝ) := by
    norm_num [block062RightChunk000L, block062RightL]
  have hR : (block062RightChunk000R : ℝ) = (block062RightR : ℝ) := by
    norm_num [block062RightChunk000R, block062RightR]
  have hyc : y ∈ Icc (block062RightChunk000L : ℝ) (block062RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block062_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block062_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block062LeftL : ℝ) (block062LeftR : ℝ) →
    y ≠ 0 → y ≠ (block062S1 : ℝ) → y ≠ (block062S2 : ℝ) →
    y ≠ (block062S3 : ℝ) → y ≠ (block062S4 : ℝ) → 0 < block062V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block062RightL : ℝ) (block062RightR : ℝ) →
    y ≠ 0 → y ≠ (block062S1 : ℝ) → y ≠ (block062S2 : ℝ) →
    y ≠ (block062S3 : ℝ) → y ≠ (block062S4 : ℝ) → 0 < block062V y)

theorem block062_reallog_certificate_proof :
    block062_reallog_certificate := by
  exact ⟨block062_left_V_pos, block062_right_V_pos⟩

end Block062
end M1817475
end Erdos1038Lean
