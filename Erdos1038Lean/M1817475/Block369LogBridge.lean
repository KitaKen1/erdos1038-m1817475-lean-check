import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block369

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block369

open Set

def block369W1 : Rat := ((4346453091963343 : Rat) / 5000000000000000)
def block369W2 : Rat := ((4713951059812557 : Rat) / 100000000000000000)
def block369W3 : Rat := ((3866768956438603 : Rat) / 25000000000000000)
def block369W4 : Rat := ((3489423322919047 : Rat) / 25000000000000000)
def block369S1 : Rat := ((18174751 : Rat) / 10000000)
def block369S2 : Rat := ((511587 : Rat) / 200000)
def block369S3 : Rat := ((26583987339285714293 : Rat) / 10000000000000000000)
def block369S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block369V (y : ℝ) : ℝ :=
  ratPotential block369W1 block369W2 block369W3 block369W4 block369S1 block369S2 block369S3 block369S4 y

def block369LeftParamsCertificate : Bool :=
  allBoxesSameParams block369LeftBoxes block369W1 block369W2 block369W3 block369W4 block369S1 block369S2 block369S3 block369S4

theorem block369LeftParamsCertificate_eq_true :
    block369LeftParamsCertificate = true := by
  native_decide

theorem block369_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block369LeftL : ℝ) (block369LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block369S1 : ℝ))
    (hy2ne : y ≠ (block369S2 : ℝ))
    (hy3ne : y ≠ (block369S3 : ℝ))
    (hy4ne : y ≠ (block369S4 : ℝ)) :
    0 < block369V y := by
  have hcert := block369LeftCertificate_eq_true
  unfold block369LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block369LeftBoxes) (lo := block369LeftL) (hi := block369LeftR)
    (w1 := block369W1) (w2 := block369W2) (w3 := block369W3) (w4 := block369W4)
    (s1 := block369S1) (s2 := block369S2) (s3 := block369S3) (s4 := block369S4)
    hboxes hcover block369LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block369RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block369RightChunk000 block369W1 block369W2 block369W3 block369W4 block369S1 block369S2 block369S3 block369S4

theorem block369RightChunk000ParamsCertificate_eq_true :
    block369RightChunk000ParamsCertificate = true := by
  native_decide

theorem block369_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block369RightChunk000L : ℝ) (block369RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block369S1 : ℝ))
    (hy2ne : y ≠ (block369S2 : ℝ))
    (hy3ne : y ≠ (block369S3 : ℝ))
    (hy4ne : y ≠ (block369S4 : ℝ)) :
    0 < block369V y := by
  have hcert := block369RightChunk000Certificate_eq_true
  unfold block369RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block369RightChunk000) (lo := block369RightChunk000L) (hi := block369RightChunk000R)
    (w1 := block369W1) (w2 := block369W2) (w3 := block369W3) (w4 := block369W4)
    (s1 := block369S1) (s2 := block369S2) (s3 := block369S3) (s4 := block369S4)
    hboxes hcover block369RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block369_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block369RightL : ℝ) (block369RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block369S1 : ℝ))
    (hy2ne : y ≠ (block369S2 : ℝ))
    (hy3ne : y ≠ (block369S3 : ℝ))
    (hy4ne : y ≠ (block369S4 : ℝ)) :
    0 < block369V y := by
  have hL : (block369RightChunk000L : ℝ) = (block369RightL : ℝ) := by
    norm_num [block369RightChunk000L, block369RightL]
  have hR : (block369RightChunk000R : ℝ) = (block369RightR : ℝ) := by
    norm_num [block369RightChunk000R, block369RightR]
  have hyc : y ∈ Icc (block369RightChunk000L : ℝ) (block369RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block369_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block369_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block369LeftL : ℝ) (block369LeftR : ℝ) →
    y ≠ 0 → y ≠ (block369S1 : ℝ) → y ≠ (block369S2 : ℝ) →
    y ≠ (block369S3 : ℝ) → y ≠ (block369S4 : ℝ) → 0 < block369V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block369RightL : ℝ) (block369RightR : ℝ) →
    y ≠ 0 → y ≠ (block369S1 : ℝ) → y ≠ (block369S2 : ℝ) →
    y ≠ (block369S3 : ℝ) → y ≠ (block369S4 : ℝ) → 0 < block369V y)

theorem block369_reallog_certificate_proof :
    block369_reallog_certificate := by
  exact ⟨block369_left_V_pos, block369_right_V_pos⟩

end Block369
end M1817475
end Erdos1038Lean
