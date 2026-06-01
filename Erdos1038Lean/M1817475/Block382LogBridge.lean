import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block382

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block382

open Set

def block382W1 : Rat := ((8461476788786779 : Rat) / 10000000000000000)
def block382W2 : Rat := ((4635765727394103 : Rat) / 100000000000000000)
def block382W3 : Rat := ((635737878120171 : Rat) / 4000000000000000)
def block382W4 : Rat := ((14045395341796207 : Rat) / 100000000000000000)
def block382S1 : Rat := ((18174751 : Rat) / 10000000)
def block382S2 : Rat := ((511587 : Rat) / 200000)
def block382S3 : Rat := ((132665798303571428619 : Rat) / 50000000000000000000)
def block382S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block382V (y : ℝ) : ℝ :=
  ratPotential block382W1 block382W2 block382W3 block382W4 block382S1 block382S2 block382S3 block382S4 y

def block382LeftParamsCertificate : Bool :=
  allBoxesSameParams block382LeftBoxes block382W1 block382W2 block382W3 block382W4 block382S1 block382S2 block382S3 block382S4

theorem block382LeftParamsCertificate_eq_true :
    block382LeftParamsCertificate = true := by
  native_decide

theorem block382_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block382LeftL : ℝ) (block382LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block382S1 : ℝ))
    (hy2ne : y ≠ (block382S2 : ℝ))
    (hy3ne : y ≠ (block382S3 : ℝ))
    (hy4ne : y ≠ (block382S4 : ℝ)) :
    0 < block382V y := by
  have hcert := block382LeftCertificate_eq_true
  unfold block382LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block382LeftBoxes) (lo := block382LeftL) (hi := block382LeftR)
    (w1 := block382W1) (w2 := block382W2) (w3 := block382W3) (w4 := block382W4)
    (s1 := block382S1) (s2 := block382S2) (s3 := block382S3) (s4 := block382S4)
    hboxes hcover block382LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block382RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block382RightChunk000 block382W1 block382W2 block382W3 block382W4 block382S1 block382S2 block382S3 block382S4

theorem block382RightChunk000ParamsCertificate_eq_true :
    block382RightChunk000ParamsCertificate = true := by
  native_decide

theorem block382_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block382RightChunk000L : ℝ) (block382RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block382S1 : ℝ))
    (hy2ne : y ≠ (block382S2 : ℝ))
    (hy3ne : y ≠ (block382S3 : ℝ))
    (hy4ne : y ≠ (block382S4 : ℝ)) :
    0 < block382V y := by
  have hcert := block382RightChunk000Certificate_eq_true
  unfold block382RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block382RightChunk000) (lo := block382RightChunk000L) (hi := block382RightChunk000R)
    (w1 := block382W1) (w2 := block382W2) (w3 := block382W3) (w4 := block382W4)
    (s1 := block382S1) (s2 := block382S2) (s3 := block382S3) (s4 := block382S4)
    hboxes hcover block382RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block382_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block382RightL : ℝ) (block382RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block382S1 : ℝ))
    (hy2ne : y ≠ (block382S2 : ℝ))
    (hy3ne : y ≠ (block382S3 : ℝ))
    (hy4ne : y ≠ (block382S4 : ℝ)) :
    0 < block382V y := by
  have hL : (block382RightChunk000L : ℝ) = (block382RightL : ℝ) := by
    norm_num [block382RightChunk000L, block382RightL]
  have hR : (block382RightChunk000R : ℝ) = (block382RightR : ℝ) := by
    norm_num [block382RightChunk000R, block382RightR]
  have hyc : y ∈ Icc (block382RightChunk000L : ℝ) (block382RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block382_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block382_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block382LeftL : ℝ) (block382LeftR : ℝ) →
    y ≠ 0 → y ≠ (block382S1 : ℝ) → y ≠ (block382S2 : ℝ) →
    y ≠ (block382S3 : ℝ) → y ≠ (block382S4 : ℝ) → 0 < block382V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block382RightL : ℝ) (block382RightR : ℝ) →
    y ≠ 0 → y ≠ (block382S1 : ℝ) → y ≠ (block382S2 : ℝ) →
    y ≠ (block382S3 : ℝ) → y ≠ (block382S4 : ℝ) → 0 < block382V y)

theorem block382_reallog_certificate_proof :
    block382_reallog_certificate := by
  exact ⟨block382_left_V_pos, block382_right_V_pos⟩

end Block382
end M1817475
end Erdos1038Lean
