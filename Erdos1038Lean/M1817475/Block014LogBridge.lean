import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block014

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block014

open Set

def block014W1 : Rat := ((84252604322053 : Rat) / 10000000000000)
def block014W2 : Rat := (0 : Rat)
def block014W3 : Rat := (0 : Rat)
def block014W4 : Rat := ((1276576527811551 : Rat) / 5000000000000000)
def block014S1 : Rat := ((18174751 : Rat) / 10000000)
def block014S2 : Rat := ((511587 : Rat) / 200000)
def block014S3 : Rat := ((107000619 : Rat) / 40000000)
def block014S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block014V (y : ℝ) : ℝ :=
  ratPotential block014W1 block014W2 block014W3 block014W4 block014S1 block014S2 block014S3 block014S4 y

def block014LeftParamsCertificate : Bool :=
  allBoxesSameParams block014LeftBoxes block014W1 block014W2 block014W3 block014W4 block014S1 block014S2 block014S3 block014S4

theorem block014LeftParamsCertificate_eq_true :
    block014LeftParamsCertificate = true := by
  native_decide

theorem block014_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block014LeftL : ℝ) (block014LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block014S1 : ℝ))
    (hy2ne : y ≠ (block014S2 : ℝ))
    (hy3ne : y ≠ (block014S3 : ℝ))
    (hy4ne : y ≠ (block014S4 : ℝ)) :
    0 < block014V y := by
  have hcert := block014LeftCertificate_eq_true
  unfold block014LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block014LeftBoxes) (lo := block014LeftL) (hi := block014LeftR)
    (w1 := block014W1) (w2 := block014W2) (w3 := block014W3) (w4 := block014W4)
    (s1 := block014S1) (s2 := block014S2) (s3 := block014S3) (s4 := block014S4)
    hboxes hcover block014LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block014RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block014RightChunk000 block014W1 block014W2 block014W3 block014W4 block014S1 block014S2 block014S3 block014S4

theorem block014RightChunk000ParamsCertificate_eq_true :
    block014RightChunk000ParamsCertificate = true := by
  native_decide

theorem block014_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block014RightChunk000L : ℝ) (block014RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block014S1 : ℝ))
    (hy2ne : y ≠ (block014S2 : ℝ))
    (hy3ne : y ≠ (block014S3 : ℝ))
    (hy4ne : y ≠ (block014S4 : ℝ)) :
    0 < block014V y := by
  have hcert := block014RightChunk000Certificate_eq_true
  unfold block014RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block014RightChunk000) (lo := block014RightChunk000L) (hi := block014RightChunk000R)
    (w1 := block014W1) (w2 := block014W2) (w3 := block014W3) (w4 := block014W4)
    (s1 := block014S1) (s2 := block014S2) (s3 := block014S3) (s4 := block014S4)
    hboxes hcover block014RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block014_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block014RightL : ℝ) (block014RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block014S1 : ℝ))
    (hy2ne : y ≠ (block014S2 : ℝ))
    (hy3ne : y ≠ (block014S3 : ℝ))
    (hy4ne : y ≠ (block014S4 : ℝ)) :
    0 < block014V y := by
  have hL : (block014RightChunk000L : ℝ) = (block014RightL : ℝ) := by
    norm_num [block014RightChunk000L, block014RightL]
  have hR : (block014RightChunk000R : ℝ) = (block014RightR : ℝ) := by
    norm_num [block014RightChunk000R, block014RightR]
  have hyc : y ∈ Icc (block014RightChunk000L : ℝ) (block014RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block014_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block014_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block014LeftL : ℝ) (block014LeftR : ℝ) →
    y ≠ 0 → y ≠ (block014S1 : ℝ) → y ≠ (block014S2 : ℝ) →
    y ≠ (block014S3 : ℝ) → y ≠ (block014S4 : ℝ) → 0 < block014V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block014RightL : ℝ) (block014RightR : ℝ) →
    y ≠ 0 → y ≠ (block014S1 : ℝ) → y ≠ (block014S2 : ℝ) →
    y ≠ (block014S3 : ℝ) → y ≠ (block014S4 : ℝ) → 0 < block014V y)

theorem block014_reallog_certificate_proof :
    block014_reallog_certificate := by
  exact ⟨block014_left_V_pos, block014_right_V_pos⟩

end Block014
end M1817475
end Erdos1038Lean
