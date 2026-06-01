import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block064

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block064

open Set

def block064W1 : Rat := ((2945237238356709 : Rat) / 1000000000000000)
def block064W2 : Rat := (0 : Rat)
def block064W3 : Rat := (0 : Rat)
def block064W4 : Rat := ((2568726654338841 : Rat) / 10000000000000000)
def block064S1 : Rat := ((18174751 : Rat) / 10000000)
def block064S2 : Rat := ((511587 : Rat) / 200000)
def block064S3 : Rat := ((107000619 : Rat) / 40000000)
def block064S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block064V (y : ℝ) : ℝ :=
  ratPotential block064W1 block064W2 block064W3 block064W4 block064S1 block064S2 block064S3 block064S4 y

def block064LeftParamsCertificate : Bool :=
  allBoxesSameParams block064LeftBoxes block064W1 block064W2 block064W3 block064W4 block064S1 block064S2 block064S3 block064S4

theorem block064LeftParamsCertificate_eq_true :
    block064LeftParamsCertificate = true := by
  native_decide

theorem block064_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block064LeftL : ℝ) (block064LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block064S1 : ℝ))
    (hy2ne : y ≠ (block064S2 : ℝ))
    (hy3ne : y ≠ (block064S3 : ℝ))
    (hy4ne : y ≠ (block064S4 : ℝ)) :
    0 < block064V y := by
  have hcert := block064LeftCertificate_eq_true
  unfold block064LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block064LeftBoxes) (lo := block064LeftL) (hi := block064LeftR)
    (w1 := block064W1) (w2 := block064W2) (w3 := block064W3) (w4 := block064W4)
    (s1 := block064S1) (s2 := block064S2) (s3 := block064S3) (s4 := block064S4)
    hboxes hcover block064LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block064RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block064RightChunk000 block064W1 block064W2 block064W3 block064W4 block064S1 block064S2 block064S3 block064S4

theorem block064RightChunk000ParamsCertificate_eq_true :
    block064RightChunk000ParamsCertificate = true := by
  native_decide

theorem block064_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block064RightChunk000L : ℝ) (block064RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block064S1 : ℝ))
    (hy2ne : y ≠ (block064S2 : ℝ))
    (hy3ne : y ≠ (block064S3 : ℝ))
    (hy4ne : y ≠ (block064S4 : ℝ)) :
    0 < block064V y := by
  have hcert := block064RightChunk000Certificate_eq_true
  unfold block064RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block064RightChunk000) (lo := block064RightChunk000L) (hi := block064RightChunk000R)
    (w1 := block064W1) (w2 := block064W2) (w3 := block064W3) (w4 := block064W4)
    (s1 := block064S1) (s2 := block064S2) (s3 := block064S3) (s4 := block064S4)
    hboxes hcover block064RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block064_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block064RightL : ℝ) (block064RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block064S1 : ℝ))
    (hy2ne : y ≠ (block064S2 : ℝ))
    (hy3ne : y ≠ (block064S3 : ℝ))
    (hy4ne : y ≠ (block064S4 : ℝ)) :
    0 < block064V y := by
  have hL : (block064RightChunk000L : ℝ) = (block064RightL : ℝ) := by
    norm_num [block064RightChunk000L, block064RightL]
  have hR : (block064RightChunk000R : ℝ) = (block064RightR : ℝ) := by
    norm_num [block064RightChunk000R, block064RightR]
  have hyc : y ∈ Icc (block064RightChunk000L : ℝ) (block064RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block064_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block064_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block064LeftL : ℝ) (block064LeftR : ℝ) →
    y ≠ 0 → y ≠ (block064S1 : ℝ) → y ≠ (block064S2 : ℝ) →
    y ≠ (block064S3 : ℝ) → y ≠ (block064S4 : ℝ) → 0 < block064V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block064RightL : ℝ) (block064RightR : ℝ) →
    y ≠ 0 → y ≠ (block064S1 : ℝ) → y ≠ (block064S2 : ℝ) →
    y ≠ (block064S3 : ℝ) → y ≠ (block064S4 : ℝ) → 0 < block064V y)

theorem block064_reallog_certificate_proof :
    block064_reallog_certificate := by
  exact ⟨block064_left_V_pos, block064_right_V_pos⟩

end Block064
end M1817475
end Erdos1038Lean
