import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block551

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block551

open Set

def block551W1 : Rat := ((3867665129543719 : Rat) / 10000000000000000)
def block551W2 : Rat := (0 : Rat)
def block551W3 : Rat := ((1150468410562061 : Rat) / 2500000000000000)
def block551W4 : Rat := (0 : Rat)
def block551S1 : Rat := ((18174751 : Rat) / 10000000)
def block551S2 : Rat := ((511587 : Rat) / 200000)
def block551S3 : Rat := ((129361999196428571621 : Rat) / 50000000000000000000)
def block551S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block551V (y : ℝ) : ℝ :=
  ratPotential block551W1 block551W2 block551W3 block551W4 block551S1 block551S2 block551S3 block551S4 y

def block551LeftParamsCertificate : Bool :=
  allBoxesSameParams block551LeftBoxes block551W1 block551W2 block551W3 block551W4 block551S1 block551S2 block551S3 block551S4

theorem block551LeftParamsCertificate_eq_true :
    block551LeftParamsCertificate = true := by
  native_decide

theorem block551_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block551LeftL : ℝ) (block551LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block551S1 : ℝ))
    (hy2ne : y ≠ (block551S2 : ℝ))
    (hy3ne : y ≠ (block551S3 : ℝ))
    (hy4ne : y ≠ (block551S4 : ℝ)) :
    0 < block551V y := by
  have hcert := block551LeftCertificate_eq_true
  unfold block551LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block551LeftBoxes) (lo := block551LeftL) (hi := block551LeftR)
    (w1 := block551W1) (w2 := block551W2) (w3 := block551W3) (w4 := block551W4)
    (s1 := block551S1) (s2 := block551S2) (s3 := block551S3) (s4 := block551S4)
    hboxes hcover block551LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block551RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block551RightChunk000 block551W1 block551W2 block551W3 block551W4 block551S1 block551S2 block551S3 block551S4

theorem block551RightChunk000ParamsCertificate_eq_true :
    block551RightChunk000ParamsCertificate = true := by
  native_decide

theorem block551_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block551RightChunk000L : ℝ) (block551RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block551S1 : ℝ))
    (hy2ne : y ≠ (block551S2 : ℝ))
    (hy3ne : y ≠ (block551S3 : ℝ))
    (hy4ne : y ≠ (block551S4 : ℝ)) :
    0 < block551V y := by
  have hcert := block551RightChunk000Certificate_eq_true
  unfold block551RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block551RightChunk000) (lo := block551RightChunk000L) (hi := block551RightChunk000R)
    (w1 := block551W1) (w2 := block551W2) (w3 := block551W3) (w4 := block551W4)
    (s1 := block551S1) (s2 := block551S2) (s3 := block551S3) (s4 := block551S4)
    hboxes hcover block551RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block551_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block551RightL : ℝ) (block551RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block551S1 : ℝ))
    (hy2ne : y ≠ (block551S2 : ℝ))
    (hy3ne : y ≠ (block551S3 : ℝ))
    (hy4ne : y ≠ (block551S4 : ℝ)) :
    0 < block551V y := by
  have hL : (block551RightChunk000L : ℝ) = (block551RightL : ℝ) := by
    norm_num [block551RightChunk000L, block551RightL]
  have hR : (block551RightChunk000R : ℝ) = (block551RightR : ℝ) := by
    norm_num [block551RightChunk000R, block551RightR]
  have hyc : y ∈ Icc (block551RightChunk000L : ℝ) (block551RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block551_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block551_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block551LeftL : ℝ) (block551LeftR : ℝ) →
    y ≠ 0 → y ≠ (block551S1 : ℝ) → y ≠ (block551S2 : ℝ) →
    y ≠ (block551S3 : ℝ) → y ≠ (block551S4 : ℝ) → 0 < block551V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block551RightL : ℝ) (block551RightR : ℝ) →
    y ≠ 0 → y ≠ (block551S1 : ℝ) → y ≠ (block551S2 : ℝ) →
    y ≠ (block551S3 : ℝ) → y ≠ (block551S4 : ℝ) → 0 < block551V y)

theorem block551_reallog_certificate_proof :
    block551_reallog_certificate := by
  exact ⟨block551_left_V_pos, block551_right_V_pos⟩

end Block551
end M1817475
end Erdos1038Lean
