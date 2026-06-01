import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block532

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block532

open Set

def block532W1 : Rat := ((405760481397953 : Rat) / 1000000000000000)
def block532W2 : Rat := (0 : Rat)
def block532W3 : Rat := ((45295186887399747 : Rat) / 100000000000000000)
def block532W4 : Rat := (0 : Rat)
def block532S1 : Rat := ((18174751 : Rat) / 10000000)
def block532S2 : Rat := ((511587 : Rat) / 200000)
def block532S3 : Rat := ((129733432232142857319 : Rat) / 50000000000000000000)
def block532S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block532V (y : ℝ) : ℝ :=
  ratPotential block532W1 block532W2 block532W3 block532W4 block532S1 block532S2 block532S3 block532S4 y

def block532LeftParamsCertificate : Bool :=
  allBoxesSameParams block532LeftBoxes block532W1 block532W2 block532W3 block532W4 block532S1 block532S2 block532S3 block532S4

theorem block532LeftParamsCertificate_eq_true :
    block532LeftParamsCertificate = true := by
  native_decide

theorem block532_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block532LeftL : ℝ) (block532LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block532S1 : ℝ))
    (hy2ne : y ≠ (block532S2 : ℝ))
    (hy3ne : y ≠ (block532S3 : ℝ))
    (hy4ne : y ≠ (block532S4 : ℝ)) :
    0 < block532V y := by
  have hcert := block532LeftCertificate_eq_true
  unfold block532LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block532LeftBoxes) (lo := block532LeftL) (hi := block532LeftR)
    (w1 := block532W1) (w2 := block532W2) (w3 := block532W3) (w4 := block532W4)
    (s1 := block532S1) (s2 := block532S2) (s3 := block532S3) (s4 := block532S4)
    hboxes hcover block532LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block532RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block532RightChunk000 block532W1 block532W2 block532W3 block532W4 block532S1 block532S2 block532S3 block532S4

theorem block532RightChunk000ParamsCertificate_eq_true :
    block532RightChunk000ParamsCertificate = true := by
  native_decide

theorem block532_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block532RightChunk000L : ℝ) (block532RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block532S1 : ℝ))
    (hy2ne : y ≠ (block532S2 : ℝ))
    (hy3ne : y ≠ (block532S3 : ℝ))
    (hy4ne : y ≠ (block532S4 : ℝ)) :
    0 < block532V y := by
  have hcert := block532RightChunk000Certificate_eq_true
  unfold block532RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block532RightChunk000) (lo := block532RightChunk000L) (hi := block532RightChunk000R)
    (w1 := block532W1) (w2 := block532W2) (w3 := block532W3) (w4 := block532W4)
    (s1 := block532S1) (s2 := block532S2) (s3 := block532S3) (s4 := block532S4)
    hboxes hcover block532RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block532_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block532RightL : ℝ) (block532RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block532S1 : ℝ))
    (hy2ne : y ≠ (block532S2 : ℝ))
    (hy3ne : y ≠ (block532S3 : ℝ))
    (hy4ne : y ≠ (block532S4 : ℝ)) :
    0 < block532V y := by
  have hL : (block532RightChunk000L : ℝ) = (block532RightL : ℝ) := by
    norm_num [block532RightChunk000L, block532RightL]
  have hR : (block532RightChunk000R : ℝ) = (block532RightR : ℝ) := by
    norm_num [block532RightChunk000R, block532RightR]
  have hyc : y ∈ Icc (block532RightChunk000L : ℝ) (block532RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block532_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block532_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block532LeftL : ℝ) (block532LeftR : ℝ) →
    y ≠ 0 → y ≠ (block532S1 : ℝ) → y ≠ (block532S2 : ℝ) →
    y ≠ (block532S3 : ℝ) → y ≠ (block532S4 : ℝ) → 0 < block532V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block532RightL : ℝ) (block532RightR : ℝ) →
    y ≠ 0 → y ≠ (block532S1 : ℝ) → y ≠ (block532S2 : ℝ) →
    y ≠ (block532S3 : ℝ) → y ≠ (block532S4 : ℝ) → 0 < block532V y)

theorem block532_reallog_certificate_proof :
    block532_reallog_certificate := by
  exact ⟨block532_left_V_pos, block532_right_V_pos⟩

end Block532
end M1817475
end Erdos1038Lean
