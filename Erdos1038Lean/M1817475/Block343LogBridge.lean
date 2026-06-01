import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block343

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block343

open Set

def block343W1 : Rat := ((575551735415353 : Rat) / 625000000000000)
def block343W2 : Rat := ((474892195352379 : Rat) / 10000000000000000)
def block343W3 : Rat := ((1470156391212689 : Rat) / 10000000000000000)
def block343W4 : Rat := ((1721389586602471 : Rat) / 12500000000000000)
def block343S1 : Rat := ((18174751 : Rat) / 10000000)
def block343S2 : Rat := ((511587 : Rat) / 200000)
def block343S3 : Rat := ((133428213482142857157 : Rat) / 50000000000000000000)
def block343S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block343V (y : ℝ) : ℝ :=
  ratPotential block343W1 block343W2 block343W3 block343W4 block343S1 block343S2 block343S3 block343S4 y

def block343LeftParamsCertificate : Bool :=
  allBoxesSameParams block343LeftBoxes block343W1 block343W2 block343W3 block343W4 block343S1 block343S2 block343S3 block343S4

theorem block343LeftParamsCertificate_eq_true :
    block343LeftParamsCertificate = true := by
  native_decide

theorem block343_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block343LeftL : ℝ) (block343LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block343S1 : ℝ))
    (hy2ne : y ≠ (block343S2 : ℝ))
    (hy3ne : y ≠ (block343S3 : ℝ))
    (hy4ne : y ≠ (block343S4 : ℝ)) :
    0 < block343V y := by
  have hcert := block343LeftCertificate_eq_true
  unfold block343LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block343LeftBoxes) (lo := block343LeftL) (hi := block343LeftR)
    (w1 := block343W1) (w2 := block343W2) (w3 := block343W3) (w4 := block343W4)
    (s1 := block343S1) (s2 := block343S2) (s3 := block343S3) (s4 := block343S4)
    hboxes hcover block343LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block343RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block343RightChunk000 block343W1 block343W2 block343W3 block343W4 block343S1 block343S2 block343S3 block343S4

theorem block343RightChunk000ParamsCertificate_eq_true :
    block343RightChunk000ParamsCertificate = true := by
  native_decide

theorem block343_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block343RightChunk000L : ℝ) (block343RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block343S1 : ℝ))
    (hy2ne : y ≠ (block343S2 : ℝ))
    (hy3ne : y ≠ (block343S3 : ℝ))
    (hy4ne : y ≠ (block343S4 : ℝ)) :
    0 < block343V y := by
  have hcert := block343RightChunk000Certificate_eq_true
  unfold block343RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block343RightChunk000) (lo := block343RightChunk000L) (hi := block343RightChunk000R)
    (w1 := block343W1) (w2 := block343W2) (w3 := block343W3) (w4 := block343W4)
    (s1 := block343S1) (s2 := block343S2) (s3 := block343S3) (s4 := block343S4)
    hboxes hcover block343RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block343_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block343RightL : ℝ) (block343RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block343S1 : ℝ))
    (hy2ne : y ≠ (block343S2 : ℝ))
    (hy3ne : y ≠ (block343S3 : ℝ))
    (hy4ne : y ≠ (block343S4 : ℝ)) :
    0 < block343V y := by
  have hL : (block343RightChunk000L : ℝ) = (block343RightL : ℝ) := by
    norm_num [block343RightChunk000L, block343RightL]
  have hR : (block343RightChunk000R : ℝ) = (block343RightR : ℝ) := by
    norm_num [block343RightChunk000R, block343RightR]
  have hyc : y ∈ Icc (block343RightChunk000L : ℝ) (block343RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block343_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block343_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block343LeftL : ℝ) (block343LeftR : ℝ) →
    y ≠ 0 → y ≠ (block343S1 : ℝ) → y ≠ (block343S2 : ℝ) →
    y ≠ (block343S3 : ℝ) → y ≠ (block343S4 : ℝ) → 0 < block343V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block343RightL : ℝ) (block343RightR : ℝ) →
    y ≠ 0 → y ≠ (block343S1 : ℝ) → y ≠ (block343S2 : ℝ) →
    y ≠ (block343S3 : ℝ) → y ≠ (block343S4 : ℝ) → 0 < block343V y)

theorem block343_reallog_certificate_proof :
    block343_reallog_certificate := by
  exact ⟨block343_left_V_pos, block343_right_V_pos⟩

end Block343
end M1817475
end Erdos1038Lean
