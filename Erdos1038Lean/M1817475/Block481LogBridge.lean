import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block481

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block481

open Set

def block481W1 : Rat := ((1279298522677727 : Rat) / 2500000000000000)
def block481W2 : Rat := (0 : Rat)
def block481W3 : Rat := ((759974227930197 : Rat) / 2000000000000000)
def block481W4 : Rat := ((10243597341487701 : Rat) / 250000000000000000)
def block481S1 : Rat := ((18174751 : Rat) / 10000000)
def block481S2 : Rat := ((511587 : Rat) / 200000)
def block481S3 : Rat := ((130730436696428571561 : Rat) / 50000000000000000000)
def block481S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block481V (y : ℝ) : ℝ :=
  ratPotential block481W1 block481W2 block481W3 block481W4 block481S1 block481S2 block481S3 block481S4 y

def block481LeftParamsCertificate : Bool :=
  allBoxesSameParams block481LeftBoxes block481W1 block481W2 block481W3 block481W4 block481S1 block481S2 block481S3 block481S4

theorem block481LeftParamsCertificate_eq_true :
    block481LeftParamsCertificate = true := by
  native_decide

theorem block481_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block481LeftL : ℝ) (block481LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block481S1 : ℝ))
    (hy2ne : y ≠ (block481S2 : ℝ))
    (hy3ne : y ≠ (block481S3 : ℝ))
    (hy4ne : y ≠ (block481S4 : ℝ)) :
    0 < block481V y := by
  have hcert := block481LeftCertificate_eq_true
  unfold block481LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block481LeftBoxes) (lo := block481LeftL) (hi := block481LeftR)
    (w1 := block481W1) (w2 := block481W2) (w3 := block481W3) (w4 := block481W4)
    (s1 := block481S1) (s2 := block481S2) (s3 := block481S3) (s4 := block481S4)
    hboxes hcover block481LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block481RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block481RightChunk000 block481W1 block481W2 block481W3 block481W4 block481S1 block481S2 block481S3 block481S4

theorem block481RightChunk000ParamsCertificate_eq_true :
    block481RightChunk000ParamsCertificate = true := by
  native_decide

theorem block481_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block481RightChunk000L : ℝ) (block481RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block481S1 : ℝ))
    (hy2ne : y ≠ (block481S2 : ℝ))
    (hy3ne : y ≠ (block481S3 : ℝ))
    (hy4ne : y ≠ (block481S4 : ℝ)) :
    0 < block481V y := by
  have hcert := block481RightChunk000Certificate_eq_true
  unfold block481RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block481RightChunk000) (lo := block481RightChunk000L) (hi := block481RightChunk000R)
    (w1 := block481W1) (w2 := block481W2) (w3 := block481W3) (w4 := block481W4)
    (s1 := block481S1) (s2 := block481S2) (s3 := block481S3) (s4 := block481S4)
    hboxes hcover block481RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block481_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block481RightL : ℝ) (block481RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block481S1 : ℝ))
    (hy2ne : y ≠ (block481S2 : ℝ))
    (hy3ne : y ≠ (block481S3 : ℝ))
    (hy4ne : y ≠ (block481S4 : ℝ)) :
    0 < block481V y := by
  have hL : (block481RightChunk000L : ℝ) = (block481RightL : ℝ) := by
    norm_num [block481RightChunk000L, block481RightL]
  have hR : (block481RightChunk000R : ℝ) = (block481RightR : ℝ) := by
    norm_num [block481RightChunk000R, block481RightR]
  have hyc : y ∈ Icc (block481RightChunk000L : ℝ) (block481RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block481_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block481_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block481LeftL : ℝ) (block481LeftR : ℝ) →
    y ≠ 0 → y ≠ (block481S1 : ℝ) → y ≠ (block481S2 : ℝ) →
    y ≠ (block481S3 : ℝ) → y ≠ (block481S4 : ℝ) → 0 < block481V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block481RightL : ℝ) (block481RightR : ℝ) →
    y ≠ 0 → y ≠ (block481S1 : ℝ) → y ≠ (block481S2 : ℝ) →
    y ≠ (block481S3 : ℝ) → y ≠ (block481S4 : ℝ) → 0 < block481V y)

theorem block481_reallog_certificate_proof :
    block481_reallog_certificate := by
  exact ⟨block481_left_V_pos, block481_right_V_pos⟩

end Block481
end M1817475
end Erdos1038Lean
