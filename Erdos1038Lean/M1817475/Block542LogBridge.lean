import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block542

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block542

open Set

def block542W1 : Rat := ((3956296662383291 : Rat) / 10000000000000000)
def block542W2 : Rat := (0 : Rat)
def block542W3 : Rat := ((4567544382447293 : Rat) / 10000000000000000)
def block542W4 : Rat := (0 : Rat)
def block542S1 : Rat := ((18174751 : Rat) / 10000000)
def block542S2 : Rat := ((511587 : Rat) / 200000)
def block542S3 : Rat := ((129537941160714285899 : Rat) / 50000000000000000000)
def block542S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block542V (y : ℝ) : ℝ :=
  ratPotential block542W1 block542W2 block542W3 block542W4 block542S1 block542S2 block542S3 block542S4 y

def block542LeftParamsCertificate : Bool :=
  allBoxesSameParams block542LeftBoxes block542W1 block542W2 block542W3 block542W4 block542S1 block542S2 block542S3 block542S4

theorem block542LeftParamsCertificate_eq_true :
    block542LeftParamsCertificate = true := by
  native_decide

theorem block542_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block542LeftL : ℝ) (block542LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block542S1 : ℝ))
    (hy2ne : y ≠ (block542S2 : ℝ))
    (hy3ne : y ≠ (block542S3 : ℝ))
    (hy4ne : y ≠ (block542S4 : ℝ)) :
    0 < block542V y := by
  have hcert := block542LeftCertificate_eq_true
  unfold block542LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block542LeftBoxes) (lo := block542LeftL) (hi := block542LeftR)
    (w1 := block542W1) (w2 := block542W2) (w3 := block542W3) (w4 := block542W4)
    (s1 := block542S1) (s2 := block542S2) (s3 := block542S3) (s4 := block542S4)
    hboxes hcover block542LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block542RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block542RightChunk000 block542W1 block542W2 block542W3 block542W4 block542S1 block542S2 block542S3 block542S4

theorem block542RightChunk000ParamsCertificate_eq_true :
    block542RightChunk000ParamsCertificate = true := by
  native_decide

theorem block542_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block542RightChunk000L : ℝ) (block542RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block542S1 : ℝ))
    (hy2ne : y ≠ (block542S2 : ℝ))
    (hy3ne : y ≠ (block542S3 : ℝ))
    (hy4ne : y ≠ (block542S4 : ℝ)) :
    0 < block542V y := by
  have hcert := block542RightChunk000Certificate_eq_true
  unfold block542RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block542RightChunk000) (lo := block542RightChunk000L) (hi := block542RightChunk000R)
    (w1 := block542W1) (w2 := block542W2) (w3 := block542W3) (w4 := block542W4)
    (s1 := block542S1) (s2 := block542S2) (s3 := block542S3) (s4 := block542S4)
    hboxes hcover block542RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block542_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block542RightL : ℝ) (block542RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block542S1 : ℝ))
    (hy2ne : y ≠ (block542S2 : ℝ))
    (hy3ne : y ≠ (block542S3 : ℝ))
    (hy4ne : y ≠ (block542S4 : ℝ)) :
    0 < block542V y := by
  have hL : (block542RightChunk000L : ℝ) = (block542RightL : ℝ) := by
    norm_num [block542RightChunk000L, block542RightL]
  have hR : (block542RightChunk000R : ℝ) = (block542RightR : ℝ) := by
    norm_num [block542RightChunk000R, block542RightR]
  have hyc : y ∈ Icc (block542RightChunk000L : ℝ) (block542RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block542_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block542_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block542LeftL : ℝ) (block542LeftR : ℝ) →
    y ≠ 0 → y ≠ (block542S1 : ℝ) → y ≠ (block542S2 : ℝ) →
    y ≠ (block542S3 : ℝ) → y ≠ (block542S4 : ℝ) → 0 < block542V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block542RightL : ℝ) (block542RightR : ℝ) →
    y ≠ 0 → y ≠ (block542S1 : ℝ) → y ≠ (block542S2 : ℝ) →
    y ≠ (block542S3 : ℝ) → y ≠ (block542S4 : ℝ) → 0 < block542V y)

theorem block542_reallog_certificate_proof :
    block542_reallog_certificate := by
  exact ⟨block542_left_V_pos, block542_right_V_pos⟩

end Block542
end M1817475
end Erdos1038Lean
