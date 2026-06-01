import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block556

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block556

open Set

def block556W1 : Rat := ((4774286349365283 : Rat) / 12500000000000000)
def block556W2 : Rat := (0 : Rat)
def block556W3 : Rat := ((231049499231437 : Rat) / 500000000000000)
def block556W4 : Rat := (0 : Rat)
def block556S1 : Rat := ((18174751 : Rat) / 10000000)
def block556S2 : Rat := ((511587 : Rat) / 200000)
def block556S3 : Rat := ((129264253660714285911 : Rat) / 50000000000000000000)
def block556S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block556V (y : ℝ) : ℝ :=
  ratPotential block556W1 block556W2 block556W3 block556W4 block556S1 block556S2 block556S3 block556S4 y

def block556LeftParamsCertificate : Bool :=
  allBoxesSameParams block556LeftBoxes block556W1 block556W2 block556W3 block556W4 block556S1 block556S2 block556S3 block556S4

theorem block556LeftParamsCertificate_eq_true :
    block556LeftParamsCertificate = true := by
  native_decide

theorem block556_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block556LeftL : ℝ) (block556LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block556S1 : ℝ))
    (hy2ne : y ≠ (block556S2 : ℝ))
    (hy3ne : y ≠ (block556S3 : ℝ))
    (hy4ne : y ≠ (block556S4 : ℝ)) :
    0 < block556V y := by
  have hcert := block556LeftCertificate_eq_true
  unfold block556LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block556LeftBoxes) (lo := block556LeftL) (hi := block556LeftR)
    (w1 := block556W1) (w2 := block556W2) (w3 := block556W3) (w4 := block556W4)
    (s1 := block556S1) (s2 := block556S2) (s3 := block556S3) (s4 := block556S4)
    hboxes hcover block556LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block556RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block556RightChunk000 block556W1 block556W2 block556W3 block556W4 block556S1 block556S2 block556S3 block556S4

theorem block556RightChunk000ParamsCertificate_eq_true :
    block556RightChunk000ParamsCertificate = true := by
  native_decide

theorem block556_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block556RightChunk000L : ℝ) (block556RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block556S1 : ℝ))
    (hy2ne : y ≠ (block556S2 : ℝ))
    (hy3ne : y ≠ (block556S3 : ℝ))
    (hy4ne : y ≠ (block556S4 : ℝ)) :
    0 < block556V y := by
  have hcert := block556RightChunk000Certificate_eq_true
  unfold block556RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block556RightChunk000) (lo := block556RightChunk000L) (hi := block556RightChunk000R)
    (w1 := block556W1) (w2 := block556W2) (w3 := block556W3) (w4 := block556W4)
    (s1 := block556S1) (s2 := block556S2) (s3 := block556S3) (s4 := block556S4)
    hboxes hcover block556RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block556_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block556RightL : ℝ) (block556RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block556S1 : ℝ))
    (hy2ne : y ≠ (block556S2 : ℝ))
    (hy3ne : y ≠ (block556S3 : ℝ))
    (hy4ne : y ≠ (block556S4 : ℝ)) :
    0 < block556V y := by
  have hL : (block556RightChunk000L : ℝ) = (block556RightL : ℝ) := by
    norm_num [block556RightChunk000L, block556RightL]
  have hR : (block556RightChunk000R : ℝ) = (block556RightR : ℝ) := by
    norm_num [block556RightChunk000R, block556RightR]
  have hyc : y ∈ Icc (block556RightChunk000L : ℝ) (block556RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block556_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block556_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block556LeftL : ℝ) (block556LeftR : ℝ) →
    y ≠ 0 → y ≠ (block556S1 : ℝ) → y ≠ (block556S2 : ℝ) →
    y ≠ (block556S3 : ℝ) → y ≠ (block556S4 : ℝ) → 0 < block556V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block556RightL : ℝ) (block556RightR : ℝ) →
    y ≠ 0 → y ≠ (block556S1 : ℝ) → y ≠ (block556S2 : ℝ) →
    y ≠ (block556S3 : ℝ) → y ≠ (block556S4 : ℝ) → 0 < block556V y)

theorem block556_reallog_certificate_proof :
    block556_reallog_certificate := by
  exact ⟨block556_left_V_pos, block556_right_V_pos⟩

end Block556
end M1817475
end Erdos1038Lean
