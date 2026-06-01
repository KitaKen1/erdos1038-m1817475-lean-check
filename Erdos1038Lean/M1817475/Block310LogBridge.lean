import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block310

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block310

open Set

def block310W1 : Rat := ((2425996695284511 : Rat) / 2500000000000000)
def block310W2 : Rat := ((2877170079590101 : Rat) / 50000000000000000)
def block310W3 : Rat := ((5238538706335727 : Rat) / 20000000000000000)
def block310W4 : Rat := (0 : Rat)
def block310S1 : Rat := ((18174751 : Rat) / 10000000)
def block310S2 : Rat := ((511587 : Rat) / 200000)
def block310S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block310S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block310V (y : ℝ) : ℝ :=
  ratPotential block310W1 block310W2 block310W3 block310W4 block310S1 block310S2 block310S3 block310S4 y

def block310LeftParamsCertificate : Bool :=
  allBoxesSameParams block310LeftBoxes block310W1 block310W2 block310W3 block310W4 block310S1 block310S2 block310S3 block310S4

theorem block310LeftParamsCertificate_eq_true :
    block310LeftParamsCertificate = true := by
  native_decide

theorem block310_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block310LeftL : ℝ) (block310LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block310S1 : ℝ))
    (hy2ne : y ≠ (block310S2 : ℝ))
    (hy3ne : y ≠ (block310S3 : ℝ))
    (hy4ne : y ≠ (block310S4 : ℝ)) :
    0 < block310V y := by
  have hcert := block310LeftCertificate_eq_true
  unfold block310LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block310LeftBoxes) (lo := block310LeftL) (hi := block310LeftR)
    (w1 := block310W1) (w2 := block310W2) (w3 := block310W3) (w4 := block310W4)
    (s1 := block310S1) (s2 := block310S2) (s3 := block310S3) (s4 := block310S4)
    hboxes hcover block310LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block310RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block310RightChunk000 block310W1 block310W2 block310W3 block310W4 block310S1 block310S2 block310S3 block310S4

theorem block310RightChunk000ParamsCertificate_eq_true :
    block310RightChunk000ParamsCertificate = true := by
  native_decide

theorem block310_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block310RightChunk000L : ℝ) (block310RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block310S1 : ℝ))
    (hy2ne : y ≠ (block310S2 : ℝ))
    (hy3ne : y ≠ (block310S3 : ℝ))
    (hy4ne : y ≠ (block310S4 : ℝ)) :
    0 < block310V y := by
  have hcert := block310RightChunk000Certificate_eq_true
  unfold block310RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block310RightChunk000) (lo := block310RightChunk000L) (hi := block310RightChunk000R)
    (w1 := block310W1) (w2 := block310W2) (w3 := block310W3) (w4 := block310W4)
    (s1 := block310S1) (s2 := block310S2) (s3 := block310S3) (s4 := block310S4)
    hboxes hcover block310RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block310_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block310RightL : ℝ) (block310RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block310S1 : ℝ))
    (hy2ne : y ≠ (block310S2 : ℝ))
    (hy3ne : y ≠ (block310S3 : ℝ))
    (hy4ne : y ≠ (block310S4 : ℝ)) :
    0 < block310V y := by
  have hL : (block310RightChunk000L : ℝ) = (block310RightL : ℝ) := by
    norm_num [block310RightChunk000L, block310RightL]
  have hR : (block310RightChunk000R : ℝ) = (block310RightR : ℝ) := by
    norm_num [block310RightChunk000R, block310RightR]
  have hyc : y ∈ Icc (block310RightChunk000L : ℝ) (block310RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block310_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block310_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block310LeftL : ℝ) (block310LeftR : ℝ) →
    y ≠ 0 → y ≠ (block310S1 : ℝ) → y ≠ (block310S2 : ℝ) →
    y ≠ (block310S3 : ℝ) → y ≠ (block310S4 : ℝ) → 0 < block310V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block310RightL : ℝ) (block310RightR : ℝ) →
    y ≠ 0 → y ≠ (block310S1 : ℝ) → y ≠ (block310S2 : ℝ) →
    y ≠ (block310S3 : ℝ) → y ≠ (block310S4 : ℝ) → 0 < block310V y)

theorem block310_reallog_certificate_proof :
    block310_reallog_certificate := by
  exact ⟨block310_left_V_pos, block310_right_V_pos⟩

end Block310
end M1817475
end Erdos1038Lean
