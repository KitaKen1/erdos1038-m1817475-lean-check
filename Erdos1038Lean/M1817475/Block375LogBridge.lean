import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block375

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block375

open Set

def block375W1 : Rat := ((8586168311867867 : Rat) / 10000000000000000)
def block375W2 : Rat := ((4677473788702693 : Rat) / 100000000000000000)
def block375W3 : Rat := ((15661859488264807 : Rat) / 100000000000000000)
def block375W4 : Rat := ((8749679626733 : Rat) / 62500000000000)
def block375S1 : Rat := ((18174751 : Rat) / 10000000)
def block375S2 : Rat := ((511587 : Rat) / 200000)
def block375S3 : Rat := ((132802642053571428613 : Rat) / 50000000000000000000)
def block375S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block375V (y : ℝ) : ℝ :=
  ratPotential block375W1 block375W2 block375W3 block375W4 block375S1 block375S2 block375S3 block375S4 y

def block375LeftParamsCertificate : Bool :=
  allBoxesSameParams block375LeftBoxes block375W1 block375W2 block375W3 block375W4 block375S1 block375S2 block375S3 block375S4

theorem block375LeftParamsCertificate_eq_true :
    block375LeftParamsCertificate = true := by
  native_decide

theorem block375_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block375LeftL : ℝ) (block375LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block375S1 : ℝ))
    (hy2ne : y ≠ (block375S2 : ℝ))
    (hy3ne : y ≠ (block375S3 : ℝ))
    (hy4ne : y ≠ (block375S4 : ℝ)) :
    0 < block375V y := by
  have hcert := block375LeftCertificate_eq_true
  unfold block375LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block375LeftBoxes) (lo := block375LeftL) (hi := block375LeftR)
    (w1 := block375W1) (w2 := block375W2) (w3 := block375W3) (w4 := block375W4)
    (s1 := block375S1) (s2 := block375S2) (s3 := block375S3) (s4 := block375S4)
    hboxes hcover block375LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block375RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block375RightChunk000 block375W1 block375W2 block375W3 block375W4 block375S1 block375S2 block375S3 block375S4

theorem block375RightChunk000ParamsCertificate_eq_true :
    block375RightChunk000ParamsCertificate = true := by
  native_decide

theorem block375_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block375RightChunk000L : ℝ) (block375RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block375S1 : ℝ))
    (hy2ne : y ≠ (block375S2 : ℝ))
    (hy3ne : y ≠ (block375S3 : ℝ))
    (hy4ne : y ≠ (block375S4 : ℝ)) :
    0 < block375V y := by
  have hcert := block375RightChunk000Certificate_eq_true
  unfold block375RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block375RightChunk000) (lo := block375RightChunk000L) (hi := block375RightChunk000R)
    (w1 := block375W1) (w2 := block375W2) (w3 := block375W3) (w4 := block375W4)
    (s1 := block375S1) (s2 := block375S2) (s3 := block375S3) (s4 := block375S4)
    hboxes hcover block375RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block375_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block375RightL : ℝ) (block375RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block375S1 : ℝ))
    (hy2ne : y ≠ (block375S2 : ℝ))
    (hy3ne : y ≠ (block375S3 : ℝ))
    (hy4ne : y ≠ (block375S4 : ℝ)) :
    0 < block375V y := by
  have hL : (block375RightChunk000L : ℝ) = (block375RightL : ℝ) := by
    norm_num [block375RightChunk000L, block375RightL]
  have hR : (block375RightChunk000R : ℝ) = (block375RightR : ℝ) := by
    norm_num [block375RightChunk000R, block375RightR]
  have hyc : y ∈ Icc (block375RightChunk000L : ℝ) (block375RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block375_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block375_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block375LeftL : ℝ) (block375LeftR : ℝ) →
    y ≠ 0 → y ≠ (block375S1 : ℝ) → y ≠ (block375S2 : ℝ) →
    y ≠ (block375S3 : ℝ) → y ≠ (block375S4 : ℝ) → 0 < block375V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block375RightL : ℝ) (block375RightR : ℝ) →
    y ≠ 0 → y ≠ (block375S1 : ℝ) → y ≠ (block375S2 : ℝ) →
    y ≠ (block375S3 : ℝ) → y ≠ (block375S4 : ℝ) → 0 < block375V y)

theorem block375_reallog_certificate_proof :
    block375_reallog_certificate := by
  exact ⟨block375_left_V_pos, block375_right_V_pos⟩

end Block375
end M1817475
end Erdos1038Lean
