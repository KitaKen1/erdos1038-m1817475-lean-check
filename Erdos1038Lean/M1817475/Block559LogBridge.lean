import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block559

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block559

open Set

def block559W1 : Rat := ((947705654295203 : Rat) / 2500000000000000)
def block559W2 : Rat := (0 : Rat)
def block559W3 : Rat := ((2316237659221787 : Rat) / 5000000000000000)
def block559W4 : Rat := (0 : Rat)
def block559S1 : Rat := ((18174751 : Rat) / 10000000)
def block559S2 : Rat := ((511587 : Rat) / 200000)
def block559S3 : Rat := ((25841121267857142897 : Rat) / 10000000000000000000)
def block559S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block559V (y : ℝ) : ℝ :=
  ratPotential block559W1 block559W2 block559W3 block559W4 block559S1 block559S2 block559S3 block559S4 y

def block559LeftParamsCertificate : Bool :=
  allBoxesSameParams block559LeftBoxes block559W1 block559W2 block559W3 block559W4 block559S1 block559S2 block559S3 block559S4

theorem block559LeftParamsCertificate_eq_true :
    block559LeftParamsCertificate = true := by
  native_decide

theorem block559_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block559LeftL : ℝ) (block559LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block559S1 : ℝ))
    (hy2ne : y ≠ (block559S2 : ℝ))
    (hy3ne : y ≠ (block559S3 : ℝ))
    (hy4ne : y ≠ (block559S4 : ℝ)) :
    0 < block559V y := by
  have hcert := block559LeftCertificate_eq_true
  unfold block559LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block559LeftBoxes) (lo := block559LeftL) (hi := block559LeftR)
    (w1 := block559W1) (w2 := block559W2) (w3 := block559W3) (w4 := block559W4)
    (s1 := block559S1) (s2 := block559S2) (s3 := block559S3) (s4 := block559S4)
    hboxes hcover block559LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block559RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block559RightChunk000 block559W1 block559W2 block559W3 block559W4 block559S1 block559S2 block559S3 block559S4

theorem block559RightChunk000ParamsCertificate_eq_true :
    block559RightChunk000ParamsCertificate = true := by
  native_decide

theorem block559_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block559RightChunk000L : ℝ) (block559RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block559S1 : ℝ))
    (hy2ne : y ≠ (block559S2 : ℝ))
    (hy3ne : y ≠ (block559S3 : ℝ))
    (hy4ne : y ≠ (block559S4 : ℝ)) :
    0 < block559V y := by
  have hcert := block559RightChunk000Certificate_eq_true
  unfold block559RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block559RightChunk000) (lo := block559RightChunk000L) (hi := block559RightChunk000R)
    (w1 := block559W1) (w2 := block559W2) (w3 := block559W3) (w4 := block559W4)
    (s1 := block559S1) (s2 := block559S2) (s3 := block559S3) (s4 := block559S4)
    hboxes hcover block559RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block559_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block559RightL : ℝ) (block559RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block559S1 : ℝ))
    (hy2ne : y ≠ (block559S2 : ℝ))
    (hy3ne : y ≠ (block559S3 : ℝ))
    (hy4ne : y ≠ (block559S4 : ℝ)) :
    0 < block559V y := by
  have hL : (block559RightChunk000L : ℝ) = (block559RightL : ℝ) := by
    norm_num [block559RightChunk000L, block559RightL]
  have hR : (block559RightChunk000R : ℝ) = (block559RightR : ℝ) := by
    norm_num [block559RightChunk000R, block559RightR]
  have hyc : y ∈ Icc (block559RightChunk000L : ℝ) (block559RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block559_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block559_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block559LeftL : ℝ) (block559LeftR : ℝ) →
    y ≠ 0 → y ≠ (block559S1 : ℝ) → y ≠ (block559S2 : ℝ) →
    y ≠ (block559S3 : ℝ) → y ≠ (block559S4 : ℝ) → 0 < block559V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block559RightL : ℝ) (block559RightR : ℝ) →
    y ≠ 0 → y ≠ (block559S1 : ℝ) → y ≠ (block559S2 : ℝ) →
    y ≠ (block559S3 : ℝ) → y ≠ (block559S4 : ℝ) → 0 < block559V y)

theorem block559_reallog_certificate_proof :
    block559_reallog_certificate := by
  exact ⟨block559_left_V_pos, block559_right_V_pos⟩

end Block559
end M1817475
end Erdos1038Lean
