import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block546

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block546

open Set

def block546W1 : Rat := ((19583068120234423 : Rat) / 50000000000000000)
def block546W2 : Rat := (0 : Rat)
def block546W3 : Rat := ((1432121636333597 : Rat) / 3125000000000000)
def block546W4 : Rat := (0 : Rat)
def block546S1 : Rat := ((18174751 : Rat) / 10000000)
def block546S2 : Rat := ((511587 : Rat) / 200000)
def block546S3 : Rat := ((129459744732142857331 : Rat) / 50000000000000000000)
def block546S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block546V (y : ℝ) : ℝ :=
  ratPotential block546W1 block546W2 block546W3 block546W4 block546S1 block546S2 block546S3 block546S4 y

def block546LeftParamsCertificate : Bool :=
  allBoxesSameParams block546LeftBoxes block546W1 block546W2 block546W3 block546W4 block546S1 block546S2 block546S3 block546S4

theorem block546LeftParamsCertificate_eq_true :
    block546LeftParamsCertificate = true := by
  native_decide

theorem block546_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block546LeftL : ℝ) (block546LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block546S1 : ℝ))
    (hy2ne : y ≠ (block546S2 : ℝ))
    (hy3ne : y ≠ (block546S3 : ℝ))
    (hy4ne : y ≠ (block546S4 : ℝ)) :
    0 < block546V y := by
  have hcert := block546LeftCertificate_eq_true
  unfold block546LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block546LeftBoxes) (lo := block546LeftL) (hi := block546LeftR)
    (w1 := block546W1) (w2 := block546W2) (w3 := block546W3) (w4 := block546W4)
    (s1 := block546S1) (s2 := block546S2) (s3 := block546S3) (s4 := block546S4)
    hboxes hcover block546LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block546RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block546RightChunk000 block546W1 block546W2 block546W3 block546W4 block546S1 block546S2 block546S3 block546S4

theorem block546RightChunk000ParamsCertificate_eq_true :
    block546RightChunk000ParamsCertificate = true := by
  native_decide

theorem block546_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block546RightChunk000L : ℝ) (block546RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block546S1 : ℝ))
    (hy2ne : y ≠ (block546S2 : ℝ))
    (hy3ne : y ≠ (block546S3 : ℝ))
    (hy4ne : y ≠ (block546S4 : ℝ)) :
    0 < block546V y := by
  have hcert := block546RightChunk000Certificate_eq_true
  unfold block546RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block546RightChunk000) (lo := block546RightChunk000L) (hi := block546RightChunk000R)
    (w1 := block546W1) (w2 := block546W2) (w3 := block546W3) (w4 := block546W4)
    (s1 := block546S1) (s2 := block546S2) (s3 := block546S3) (s4 := block546S4)
    hboxes hcover block546RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block546_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block546RightL : ℝ) (block546RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block546S1 : ℝ))
    (hy2ne : y ≠ (block546S2 : ℝ))
    (hy3ne : y ≠ (block546S3 : ℝ))
    (hy4ne : y ≠ (block546S4 : ℝ)) :
    0 < block546V y := by
  have hL : (block546RightChunk000L : ℝ) = (block546RightL : ℝ) := by
    norm_num [block546RightChunk000L, block546RightL]
  have hR : (block546RightChunk000R : ℝ) = (block546RightR : ℝ) := by
    norm_num [block546RightChunk000R, block546RightR]
  have hyc : y ∈ Icc (block546RightChunk000L : ℝ) (block546RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block546_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block546_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block546LeftL : ℝ) (block546LeftR : ℝ) →
    y ≠ 0 → y ≠ (block546S1 : ℝ) → y ≠ (block546S2 : ℝ) →
    y ≠ (block546S3 : ℝ) → y ≠ (block546S4 : ℝ) → 0 < block546V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block546RightL : ℝ) (block546RightR : ℝ) →
    y ≠ 0 → y ≠ (block546S1 : ℝ) → y ≠ (block546S2 : ℝ) →
    y ≠ (block546S3 : ℝ) → y ≠ (block546S4 : ℝ) → 0 < block546V y)

theorem block546_reallog_certificate_proof :
    block546_reallog_certificate := by
  exact ⟨block546_left_V_pos, block546_right_V_pos⟩

end Block546
end M1817475
end Erdos1038Lean
