import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block104

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block104

open Set

def block104W1 : Rat := ((51941590137797 : Rat) / 20000000000000)
def block104W2 : Rat := (0 : Rat)
def block104W3 : Rat := ((2711948425671987 : Rat) / 50000000000000000)
def block104W4 : Rat := ((19267647085394773 : Rat) / 100000000000000000)
def block104S1 : Rat := ((18174751 : Rat) / 10000000)
def block104S2 : Rat := ((511587 : Rat) / 200000)
def block104S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block104S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block104V (y : ℝ) : ℝ :=
  ratPotential block104W1 block104W2 block104W3 block104W4 block104S1 block104S2 block104S3 block104S4 y

def block104LeftParamsCertificate : Bool :=
  allBoxesSameParams block104LeftBoxes block104W1 block104W2 block104W3 block104W4 block104S1 block104S2 block104S3 block104S4

theorem block104LeftParamsCertificate_eq_true :
    block104LeftParamsCertificate = true := by
  native_decide

theorem block104_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block104LeftL : ℝ) (block104LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block104S1 : ℝ))
    (hy2ne : y ≠ (block104S2 : ℝ))
    (hy3ne : y ≠ (block104S3 : ℝ))
    (hy4ne : y ≠ (block104S4 : ℝ)) :
    0 < block104V y := by
  have hcert := block104LeftCertificate_eq_true
  unfold block104LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block104LeftBoxes) (lo := block104LeftL) (hi := block104LeftR)
    (w1 := block104W1) (w2 := block104W2) (w3 := block104W3) (w4 := block104W4)
    (s1 := block104S1) (s2 := block104S2) (s3 := block104S3) (s4 := block104S4)
    hboxes hcover block104LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block104RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block104RightChunk000 block104W1 block104W2 block104W3 block104W4 block104S1 block104S2 block104S3 block104S4

theorem block104RightChunk000ParamsCertificate_eq_true :
    block104RightChunk000ParamsCertificate = true := by
  native_decide

theorem block104_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block104RightChunk000L : ℝ) (block104RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block104S1 : ℝ))
    (hy2ne : y ≠ (block104S2 : ℝ))
    (hy3ne : y ≠ (block104S3 : ℝ))
    (hy4ne : y ≠ (block104S4 : ℝ)) :
    0 < block104V y := by
  have hcert := block104RightChunk000Certificate_eq_true
  unfold block104RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block104RightChunk000) (lo := block104RightChunk000L) (hi := block104RightChunk000R)
    (w1 := block104W1) (w2 := block104W2) (w3 := block104W3) (w4 := block104W4)
    (s1 := block104S1) (s2 := block104S2) (s3 := block104S3) (s4 := block104S4)
    hboxes hcover block104RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block104_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block104RightL : ℝ) (block104RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block104S1 : ℝ))
    (hy2ne : y ≠ (block104S2 : ℝ))
    (hy3ne : y ≠ (block104S3 : ℝ))
    (hy4ne : y ≠ (block104S4 : ℝ)) :
    0 < block104V y := by
  have hL : (block104RightChunk000L : ℝ) = (block104RightL : ℝ) := by
    norm_num [block104RightChunk000L, block104RightL]
  have hR : (block104RightChunk000R : ℝ) = (block104RightR : ℝ) := by
    norm_num [block104RightChunk000R, block104RightR]
  have hyc : y ∈ Icc (block104RightChunk000L : ℝ) (block104RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block104_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block104_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block104LeftL : ℝ) (block104LeftR : ℝ) →
    y ≠ 0 → y ≠ (block104S1 : ℝ) → y ≠ (block104S2 : ℝ) →
    y ≠ (block104S3 : ℝ) → y ≠ (block104S4 : ℝ) → 0 < block104V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block104RightL : ℝ) (block104RightR : ℝ) →
    y ≠ 0 → y ≠ (block104S1 : ℝ) → y ≠ (block104S2 : ℝ) →
    y ≠ (block104S3 : ℝ) → y ≠ (block104S4 : ℝ) → 0 < block104V y)

theorem block104_reallog_certificate_proof :
    block104_reallog_certificate := by
  exact ⟨block104_left_V_pos, block104_right_V_pos⟩

end Block104
end M1817475
end Erdos1038Lean
