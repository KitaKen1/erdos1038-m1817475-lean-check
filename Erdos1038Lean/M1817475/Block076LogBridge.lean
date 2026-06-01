import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block076

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block076

open Set

def block076W1 : Rat := ((3222422458036679 : Rat) / 1000000000000000)
def block076W2 : Rat := (0 : Rat)
def block076W3 : Rat := (0 : Rat)
def block076W4 : Rat := ((614706422367069 : Rat) / 2500000000000000)
def block076S1 : Rat := ((18174751 : Rat) / 10000000)
def block076S2 : Rat := ((511587 : Rat) / 200000)
def block076S3 : Rat := ((107000619 : Rat) / 40000000)
def block076S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block076V (y : ℝ) : ℝ :=
  ratPotential block076W1 block076W2 block076W3 block076W4 block076S1 block076S2 block076S3 block076S4 y

def block076LeftParamsCertificate : Bool :=
  allBoxesSameParams block076LeftBoxes block076W1 block076W2 block076W3 block076W4 block076S1 block076S2 block076S3 block076S4

theorem block076LeftParamsCertificate_eq_true :
    block076LeftParamsCertificate = true := by
  native_decide

theorem block076_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block076LeftL : ℝ) (block076LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block076S1 : ℝ))
    (hy2ne : y ≠ (block076S2 : ℝ))
    (hy3ne : y ≠ (block076S3 : ℝ))
    (hy4ne : y ≠ (block076S4 : ℝ)) :
    0 < block076V y := by
  have hcert := block076LeftCertificate_eq_true
  unfold block076LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block076LeftBoxes) (lo := block076LeftL) (hi := block076LeftR)
    (w1 := block076W1) (w2 := block076W2) (w3 := block076W3) (w4 := block076W4)
    (s1 := block076S1) (s2 := block076S2) (s3 := block076S3) (s4 := block076S4)
    hboxes hcover block076LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block076RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block076RightChunk000 block076W1 block076W2 block076W3 block076W4 block076S1 block076S2 block076S3 block076S4

theorem block076RightChunk000ParamsCertificate_eq_true :
    block076RightChunk000ParamsCertificate = true := by
  native_decide

theorem block076_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block076RightChunk000L : ℝ) (block076RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block076S1 : ℝ))
    (hy2ne : y ≠ (block076S2 : ℝ))
    (hy3ne : y ≠ (block076S3 : ℝ))
    (hy4ne : y ≠ (block076S4 : ℝ)) :
    0 < block076V y := by
  have hcert := block076RightChunk000Certificate_eq_true
  unfold block076RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block076RightChunk000) (lo := block076RightChunk000L) (hi := block076RightChunk000R)
    (w1 := block076W1) (w2 := block076W2) (w3 := block076W3) (w4 := block076W4)
    (s1 := block076S1) (s2 := block076S2) (s3 := block076S3) (s4 := block076S4)
    hboxes hcover block076RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block076_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block076RightL : ℝ) (block076RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block076S1 : ℝ))
    (hy2ne : y ≠ (block076S2 : ℝ))
    (hy3ne : y ≠ (block076S3 : ℝ))
    (hy4ne : y ≠ (block076S4 : ℝ)) :
    0 < block076V y := by
  have hL : (block076RightChunk000L : ℝ) = (block076RightL : ℝ) := by
    norm_num [block076RightChunk000L, block076RightL]
  have hR : (block076RightChunk000R : ℝ) = (block076RightR : ℝ) := by
    norm_num [block076RightChunk000R, block076RightR]
  have hyc : y ∈ Icc (block076RightChunk000L : ℝ) (block076RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block076_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block076_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block076LeftL : ℝ) (block076LeftR : ℝ) →
    y ≠ 0 → y ≠ (block076S1 : ℝ) → y ≠ (block076S2 : ℝ) →
    y ≠ (block076S3 : ℝ) → y ≠ (block076S4 : ℝ) → 0 < block076V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block076RightL : ℝ) (block076RightR : ℝ) →
    y ≠ 0 → y ≠ (block076S1 : ℝ) → y ≠ (block076S2 : ℝ) →
    y ≠ (block076S3 : ℝ) → y ≠ (block076S4 : ℝ) → 0 < block076V y)

theorem block076_reallog_certificate_proof :
    block076_reallog_certificate := by
  exact ⟨block076_left_V_pos, block076_right_V_pos⟩

end Block076
end M1817475
end Erdos1038Lean
