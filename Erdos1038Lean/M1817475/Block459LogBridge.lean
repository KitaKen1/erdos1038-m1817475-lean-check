import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block459

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block459

open Set

def block459W1 : Rat := ((2860061216691561 : Rat) / 5000000000000000)
def block459W2 : Rat := (0 : Rat)
def block459W3 : Rat := ((3454752121055683 : Rat) / 10000000000000000)
def block459W4 : Rat := ((6051430260822989 : Rat) / 100000000000000000)
def block459S1 : Rat := ((18174751 : Rat) / 10000000)
def block459S2 : Rat := ((511587 : Rat) / 200000)
def block459S3 : Rat := ((26232103410714285737 : Rat) / 10000000000000000000)
def block459S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block459V (y : ℝ) : ℝ :=
  ratPotential block459W1 block459W2 block459W3 block459W4 block459S1 block459S2 block459S3 block459S4 y

def block459LeftParamsCertificate : Bool :=
  allBoxesSameParams block459LeftBoxes block459W1 block459W2 block459W3 block459W4 block459S1 block459S2 block459S3 block459S4

theorem block459LeftParamsCertificate_eq_true :
    block459LeftParamsCertificate = true := by
  native_decide

theorem block459_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block459LeftL : ℝ) (block459LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block459S1 : ℝ))
    (hy2ne : y ≠ (block459S2 : ℝ))
    (hy3ne : y ≠ (block459S3 : ℝ))
    (hy4ne : y ≠ (block459S4 : ℝ)) :
    0 < block459V y := by
  have hcert := block459LeftCertificate_eq_true
  unfold block459LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block459LeftBoxes) (lo := block459LeftL) (hi := block459LeftR)
    (w1 := block459W1) (w2 := block459W2) (w3 := block459W3) (w4 := block459W4)
    (s1 := block459S1) (s2 := block459S2) (s3 := block459S3) (s4 := block459S4)
    hboxes hcover block459LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block459RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block459RightChunk000 block459W1 block459W2 block459W3 block459W4 block459S1 block459S2 block459S3 block459S4

theorem block459RightChunk000ParamsCertificate_eq_true :
    block459RightChunk000ParamsCertificate = true := by
  native_decide

theorem block459_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block459RightChunk000L : ℝ) (block459RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block459S1 : ℝ))
    (hy2ne : y ≠ (block459S2 : ℝ))
    (hy3ne : y ≠ (block459S3 : ℝ))
    (hy4ne : y ≠ (block459S4 : ℝ)) :
    0 < block459V y := by
  have hcert := block459RightChunk000Certificate_eq_true
  unfold block459RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block459RightChunk000) (lo := block459RightChunk000L) (hi := block459RightChunk000R)
    (w1 := block459W1) (w2 := block459W2) (w3 := block459W3) (w4 := block459W4)
    (s1 := block459S1) (s2 := block459S2) (s3 := block459S3) (s4 := block459S4)
    hboxes hcover block459RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block459_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block459RightL : ℝ) (block459RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block459S1 : ℝ))
    (hy2ne : y ≠ (block459S2 : ℝ))
    (hy3ne : y ≠ (block459S3 : ℝ))
    (hy4ne : y ≠ (block459S4 : ℝ)) :
    0 < block459V y := by
  have hL : (block459RightChunk000L : ℝ) = (block459RightL : ℝ) := by
    norm_num [block459RightChunk000L, block459RightL]
  have hR : (block459RightChunk000R : ℝ) = (block459RightR : ℝ) := by
    norm_num [block459RightChunk000R, block459RightR]
  have hyc : y ∈ Icc (block459RightChunk000L : ℝ) (block459RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block459_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block459_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block459LeftL : ℝ) (block459LeftR : ℝ) →
    y ≠ 0 → y ≠ (block459S1 : ℝ) → y ≠ (block459S2 : ℝ) →
    y ≠ (block459S3 : ℝ) → y ≠ (block459S4 : ℝ) → 0 < block459V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block459RightL : ℝ) (block459RightR : ℝ) →
    y ≠ 0 → y ≠ (block459S1 : ℝ) → y ≠ (block459S2 : ℝ) →
    y ≠ (block459S3 : ℝ) → y ≠ (block459S4 : ℝ) → 0 < block459V y)

theorem block459_reallog_certificate_proof :
    block459_reallog_certificate := by
  exact ⟨block459_left_V_pos, block459_right_V_pos⟩

end Block459
end M1817475
end Erdos1038Lean
