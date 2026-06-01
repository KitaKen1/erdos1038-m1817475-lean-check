import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block550

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block550

open Set

def block550W1 : Rat := ((3877397301946119 : Rat) / 10000000000000000)
def block550W2 : Rat := (0 : Rat)
def block550W3 : Rat := ((919610844301537 : Rat) / 2000000000000000)
def block550W4 : Rat := (0 : Rat)
def block550S1 : Rat := ((18174751 : Rat) / 10000000)
def block550S2 : Rat := ((511587 : Rat) / 200000)
def block550S3 : Rat := ((129381548303571428763 : Rat) / 50000000000000000000)
def block550S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block550V (y : ℝ) : ℝ :=
  ratPotential block550W1 block550W2 block550W3 block550W4 block550S1 block550S2 block550S3 block550S4 y

def block550LeftParamsCertificate : Bool :=
  allBoxesSameParams block550LeftBoxes block550W1 block550W2 block550W3 block550W4 block550S1 block550S2 block550S3 block550S4

theorem block550LeftParamsCertificate_eq_true :
    block550LeftParamsCertificate = true := by
  native_decide

theorem block550_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block550LeftL : ℝ) (block550LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block550S1 : ℝ))
    (hy2ne : y ≠ (block550S2 : ℝ))
    (hy3ne : y ≠ (block550S3 : ℝ))
    (hy4ne : y ≠ (block550S4 : ℝ)) :
    0 < block550V y := by
  have hcert := block550LeftCertificate_eq_true
  unfold block550LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block550LeftBoxes) (lo := block550LeftL) (hi := block550LeftR)
    (w1 := block550W1) (w2 := block550W2) (w3 := block550W3) (w4 := block550W4)
    (s1 := block550S1) (s2 := block550S2) (s3 := block550S3) (s4 := block550S4)
    hboxes hcover block550LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block550RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block550RightChunk000 block550W1 block550W2 block550W3 block550W4 block550S1 block550S2 block550S3 block550S4

theorem block550RightChunk000ParamsCertificate_eq_true :
    block550RightChunk000ParamsCertificate = true := by
  native_decide

theorem block550_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block550RightChunk000L : ℝ) (block550RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block550S1 : ℝ))
    (hy2ne : y ≠ (block550S2 : ℝ))
    (hy3ne : y ≠ (block550S3 : ℝ))
    (hy4ne : y ≠ (block550S4 : ℝ)) :
    0 < block550V y := by
  have hcert := block550RightChunk000Certificate_eq_true
  unfold block550RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block550RightChunk000) (lo := block550RightChunk000L) (hi := block550RightChunk000R)
    (w1 := block550W1) (w2 := block550W2) (w3 := block550W3) (w4 := block550W4)
    (s1 := block550S1) (s2 := block550S2) (s3 := block550S3) (s4 := block550S4)
    hboxes hcover block550RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block550_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block550RightL : ℝ) (block550RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block550S1 : ℝ))
    (hy2ne : y ≠ (block550S2 : ℝ))
    (hy3ne : y ≠ (block550S3 : ℝ))
    (hy4ne : y ≠ (block550S4 : ℝ)) :
    0 < block550V y := by
  have hL : (block550RightChunk000L : ℝ) = (block550RightL : ℝ) := by
    norm_num [block550RightChunk000L, block550RightL]
  have hR : (block550RightChunk000R : ℝ) = (block550RightR : ℝ) := by
    norm_num [block550RightChunk000R, block550RightR]
  have hyc : y ∈ Icc (block550RightChunk000L : ℝ) (block550RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block550_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block550_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block550LeftL : ℝ) (block550LeftR : ℝ) →
    y ≠ 0 → y ≠ (block550S1 : ℝ) → y ≠ (block550S2 : ℝ) →
    y ≠ (block550S3 : ℝ) → y ≠ (block550S4 : ℝ) → 0 < block550V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block550RightL : ℝ) (block550RightR : ℝ) →
    y ≠ 0 → y ≠ (block550S1 : ℝ) → y ≠ (block550S2 : ℝ) →
    y ≠ (block550S3 : ℝ) → y ≠ (block550S4 : ℝ) → 0 < block550V y)

theorem block550_reallog_certificate_proof :
    block550_reallog_certificate := by
  exact ⟨block550_left_V_pos, block550_right_V_pos⟩

end Block550
end M1817475
end Erdos1038Lean
