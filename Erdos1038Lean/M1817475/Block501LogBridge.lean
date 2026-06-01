import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block501

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block501

open Set

def block501W1 : Rat := ((45890646384130307 : Rat) / 100000000000000000)
def block501W2 : Rat := (0 : Rat)
def block501W3 : Rat := ((41731980004982383 : Rat) / 100000000000000000)
def block501W4 : Rat := ((1836523050319719 : Rat) / 100000000000000000)
def block501S1 : Rat := ((18174751 : Rat) / 10000000)
def block501S2 : Rat := ((511587 : Rat) / 200000)
def block501S3 : Rat := ((130339454553571428721 : Rat) / 50000000000000000000)
def block501S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block501V (y : ℝ) : ℝ :=
  ratPotential block501W1 block501W2 block501W3 block501W4 block501S1 block501S2 block501S3 block501S4 y

def block501LeftParamsCertificate : Bool :=
  allBoxesSameParams block501LeftBoxes block501W1 block501W2 block501W3 block501W4 block501S1 block501S2 block501S3 block501S4

theorem block501LeftParamsCertificate_eq_true :
    block501LeftParamsCertificate = true := by
  native_decide

theorem block501_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block501LeftL : ℝ) (block501LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block501S1 : ℝ))
    (hy2ne : y ≠ (block501S2 : ℝ))
    (hy3ne : y ≠ (block501S3 : ℝ))
    (hy4ne : y ≠ (block501S4 : ℝ)) :
    0 < block501V y := by
  have hcert := block501LeftCertificate_eq_true
  unfold block501LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block501LeftBoxes) (lo := block501LeftL) (hi := block501LeftR)
    (w1 := block501W1) (w2 := block501W2) (w3 := block501W3) (w4 := block501W4)
    (s1 := block501S1) (s2 := block501S2) (s3 := block501S3) (s4 := block501S4)
    hboxes hcover block501LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block501RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block501RightChunk000 block501W1 block501W2 block501W3 block501W4 block501S1 block501S2 block501S3 block501S4

theorem block501RightChunk000ParamsCertificate_eq_true :
    block501RightChunk000ParamsCertificate = true := by
  native_decide

theorem block501_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block501RightChunk000L : ℝ) (block501RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block501S1 : ℝ))
    (hy2ne : y ≠ (block501S2 : ℝ))
    (hy3ne : y ≠ (block501S3 : ℝ))
    (hy4ne : y ≠ (block501S4 : ℝ)) :
    0 < block501V y := by
  have hcert := block501RightChunk000Certificate_eq_true
  unfold block501RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block501RightChunk000) (lo := block501RightChunk000L) (hi := block501RightChunk000R)
    (w1 := block501W1) (w2 := block501W2) (w3 := block501W3) (w4 := block501W4)
    (s1 := block501S1) (s2 := block501S2) (s3 := block501S3) (s4 := block501S4)
    hboxes hcover block501RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block501_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block501RightL : ℝ) (block501RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block501S1 : ℝ))
    (hy2ne : y ≠ (block501S2 : ℝ))
    (hy3ne : y ≠ (block501S3 : ℝ))
    (hy4ne : y ≠ (block501S4 : ℝ)) :
    0 < block501V y := by
  have hL : (block501RightChunk000L : ℝ) = (block501RightL : ℝ) := by
    norm_num [block501RightChunk000L, block501RightL]
  have hR : (block501RightChunk000R : ℝ) = (block501RightR : ℝ) := by
    norm_num [block501RightChunk000R, block501RightR]
  have hyc : y ∈ Icc (block501RightChunk000L : ℝ) (block501RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block501_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block501_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block501LeftL : ℝ) (block501LeftR : ℝ) →
    y ≠ 0 → y ≠ (block501S1 : ℝ) → y ≠ (block501S2 : ℝ) →
    y ≠ (block501S3 : ℝ) → y ≠ (block501S4 : ℝ) → 0 < block501V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block501RightL : ℝ) (block501RightR : ℝ) →
    y ≠ 0 → y ≠ (block501S1 : ℝ) → y ≠ (block501S2 : ℝ) →
    y ≠ (block501S3 : ℝ) → y ≠ (block501S4 : ℝ) → 0 < block501V y)

theorem block501_reallog_certificate_proof :
    block501_reallog_certificate := by
  exact ⟨block501_left_V_pos, block501_right_V_pos⟩

end Block501
end M1817475
end Erdos1038Lean
