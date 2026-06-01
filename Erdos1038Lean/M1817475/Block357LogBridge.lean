import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block357

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block357

open Set

def block357W1 : Rat := ((8925239812349339 : Rat) / 10000000000000000)
def block357W2 : Rat := ((4746668847949669 : Rat) / 100000000000000000)
def block357W3 : Rat := ((15085724289713587 : Rat) / 100000000000000000)
def block357W4 : Rat := ((138859369824647 : Rat) / 1000000000000000)
def block357S1 : Rat := ((18174751 : Rat) / 10000000)
def block357S2 : Rat := ((511587 : Rat) / 200000)
def block357S3 : Rat := ((133154525982142857169 : Rat) / 50000000000000000000)
def block357S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block357V (y : ℝ) : ℝ :=
  ratPotential block357W1 block357W2 block357W3 block357W4 block357S1 block357S2 block357S3 block357S4 y

def block357LeftParamsCertificate : Bool :=
  allBoxesSameParams block357LeftBoxes block357W1 block357W2 block357W3 block357W4 block357S1 block357S2 block357S3 block357S4

theorem block357LeftParamsCertificate_eq_true :
    block357LeftParamsCertificate = true := by
  native_decide

theorem block357_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block357LeftL : ℝ) (block357LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block357S1 : ℝ))
    (hy2ne : y ≠ (block357S2 : ℝ))
    (hy3ne : y ≠ (block357S3 : ℝ))
    (hy4ne : y ≠ (block357S4 : ℝ)) :
    0 < block357V y := by
  have hcert := block357LeftCertificate_eq_true
  unfold block357LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block357LeftBoxes) (lo := block357LeftL) (hi := block357LeftR)
    (w1 := block357W1) (w2 := block357W2) (w3 := block357W3) (w4 := block357W4)
    (s1 := block357S1) (s2 := block357S2) (s3 := block357S3) (s4 := block357S4)
    hboxes hcover block357LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block357RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block357RightChunk000 block357W1 block357W2 block357W3 block357W4 block357S1 block357S2 block357S3 block357S4

theorem block357RightChunk000ParamsCertificate_eq_true :
    block357RightChunk000ParamsCertificate = true := by
  native_decide

theorem block357_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block357RightChunk000L : ℝ) (block357RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block357S1 : ℝ))
    (hy2ne : y ≠ (block357S2 : ℝ))
    (hy3ne : y ≠ (block357S3 : ℝ))
    (hy4ne : y ≠ (block357S4 : ℝ)) :
    0 < block357V y := by
  have hcert := block357RightChunk000Certificate_eq_true
  unfold block357RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block357RightChunk000) (lo := block357RightChunk000L) (hi := block357RightChunk000R)
    (w1 := block357W1) (w2 := block357W2) (w3 := block357W3) (w4 := block357W4)
    (s1 := block357S1) (s2 := block357S2) (s3 := block357S3) (s4 := block357S4)
    hboxes hcover block357RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block357_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block357RightL : ℝ) (block357RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block357S1 : ℝ))
    (hy2ne : y ≠ (block357S2 : ℝ))
    (hy3ne : y ≠ (block357S3 : ℝ))
    (hy4ne : y ≠ (block357S4 : ℝ)) :
    0 < block357V y := by
  have hL : (block357RightChunk000L : ℝ) = (block357RightL : ℝ) := by
    norm_num [block357RightChunk000L, block357RightL]
  have hR : (block357RightChunk000R : ℝ) = (block357RightR : ℝ) := by
    norm_num [block357RightChunk000R, block357RightR]
  have hyc : y ∈ Icc (block357RightChunk000L : ℝ) (block357RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block357_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block357_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block357LeftL : ℝ) (block357LeftR : ℝ) →
    y ≠ 0 → y ≠ (block357S1 : ℝ) → y ≠ (block357S2 : ℝ) →
    y ≠ (block357S3 : ℝ) → y ≠ (block357S4 : ℝ) → 0 < block357V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block357RightL : ℝ) (block357RightR : ℝ) →
    y ≠ 0 → y ≠ (block357S1 : ℝ) → y ≠ (block357S2 : ℝ) →
    y ≠ (block357S3 : ℝ) → y ≠ (block357S4 : ℝ) → 0 < block357V y)

theorem block357_reallog_certificate_proof :
    block357_reallog_certificate := by
  exact ⟨block357_left_V_pos, block357_right_V_pos⟩

end Block357
end M1817475
end Erdos1038Lean
