import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block533

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block533

open Set

def block533W1 : Rat := ((1264792551800693 : Rat) / 3125000000000000)
def block533W2 : Rat := (0 : Rat)
def block533W3 : Rat := ((9066631555190281 : Rat) / 20000000000000000)
def block533W4 : Rat := (0 : Rat)
def block533S1 : Rat := ((18174751 : Rat) / 10000000)
def block533S2 : Rat := ((511587 : Rat) / 200000)
def block533S3 : Rat := ((129713883125000000177 : Rat) / 50000000000000000000)
def block533S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block533V (y : ℝ) : ℝ :=
  ratPotential block533W1 block533W2 block533W3 block533W4 block533S1 block533S2 block533S3 block533S4 y

def block533LeftParamsCertificate : Bool :=
  allBoxesSameParams block533LeftBoxes block533W1 block533W2 block533W3 block533W4 block533S1 block533S2 block533S3 block533S4

theorem block533LeftParamsCertificate_eq_true :
    block533LeftParamsCertificate = true := by
  native_decide

theorem block533_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block533LeftL : ℝ) (block533LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block533S1 : ℝ))
    (hy2ne : y ≠ (block533S2 : ℝ))
    (hy3ne : y ≠ (block533S3 : ℝ))
    (hy4ne : y ≠ (block533S4 : ℝ)) :
    0 < block533V y := by
  have hcert := block533LeftCertificate_eq_true
  unfold block533LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block533LeftBoxes) (lo := block533LeftL) (hi := block533LeftR)
    (w1 := block533W1) (w2 := block533W2) (w3 := block533W3) (w4 := block533W4)
    (s1 := block533S1) (s2 := block533S2) (s3 := block533S3) (s4 := block533S4)
    hboxes hcover block533LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block533RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block533RightChunk000 block533W1 block533W2 block533W3 block533W4 block533S1 block533S2 block533S3 block533S4

theorem block533RightChunk000ParamsCertificate_eq_true :
    block533RightChunk000ParamsCertificate = true := by
  native_decide

theorem block533_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block533RightChunk000L : ℝ) (block533RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block533S1 : ℝ))
    (hy2ne : y ≠ (block533S2 : ℝ))
    (hy3ne : y ≠ (block533S3 : ℝ))
    (hy4ne : y ≠ (block533S4 : ℝ)) :
    0 < block533V y := by
  have hcert := block533RightChunk000Certificate_eq_true
  unfold block533RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block533RightChunk000) (lo := block533RightChunk000L) (hi := block533RightChunk000R)
    (w1 := block533W1) (w2 := block533W2) (w3 := block533W3) (w4 := block533W4)
    (s1 := block533S1) (s2 := block533S2) (s3 := block533S3) (s4 := block533S4)
    hboxes hcover block533RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block533_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block533RightL : ℝ) (block533RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block533S1 : ℝ))
    (hy2ne : y ≠ (block533S2 : ℝ))
    (hy3ne : y ≠ (block533S3 : ℝ))
    (hy4ne : y ≠ (block533S4 : ℝ)) :
    0 < block533V y := by
  have hL : (block533RightChunk000L : ℝ) = (block533RightL : ℝ) := by
    norm_num [block533RightChunk000L, block533RightL]
  have hR : (block533RightChunk000R : ℝ) = (block533RightR : ℝ) := by
    norm_num [block533RightChunk000R, block533RightR]
  have hyc : y ∈ Icc (block533RightChunk000L : ℝ) (block533RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block533_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block533_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block533LeftL : ℝ) (block533LeftR : ℝ) →
    y ≠ 0 → y ≠ (block533S1 : ℝ) → y ≠ (block533S2 : ℝ) →
    y ≠ (block533S3 : ℝ) → y ≠ (block533S4 : ℝ) → 0 < block533V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block533RightL : ℝ) (block533RightR : ℝ) →
    y ≠ 0 → y ≠ (block533S1 : ℝ) → y ≠ (block533S2 : ℝ) →
    y ≠ (block533S3 : ℝ) → y ≠ (block533S4 : ℝ) → 0 < block533V y)

theorem block533_reallog_certificate_proof :
    block533_reallog_certificate := by
  exact ⟨block533_left_V_pos, block533_right_V_pos⟩

end Block533
end M1817475
end Erdos1038Lean
