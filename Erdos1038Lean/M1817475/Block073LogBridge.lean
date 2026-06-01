import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block073

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block073

open Set

def block073W1 : Rat := ((3935182970869241 : Rat) / 1250000000000000)
def block073W2 : Rat := (0 : Rat)
def block073W3 : Rat := (0 : Rat)
def block073W4 : Rat := ((497468336832753 : Rat) / 2000000000000000)
def block073S1 : Rat := ((18174751 : Rat) / 10000000)
def block073S2 : Rat := ((511587 : Rat) / 200000)
def block073S3 : Rat := ((107000619 : Rat) / 40000000)
def block073S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block073V (y : ℝ) : ℝ :=
  ratPotential block073W1 block073W2 block073W3 block073W4 block073S1 block073S2 block073S3 block073S4 y

def block073LeftParamsCertificate : Bool :=
  allBoxesSameParams block073LeftBoxes block073W1 block073W2 block073W3 block073W4 block073S1 block073S2 block073S3 block073S4

theorem block073LeftParamsCertificate_eq_true :
    block073LeftParamsCertificate = true := by
  native_decide

theorem block073_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block073LeftL : ℝ) (block073LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block073S1 : ℝ))
    (hy2ne : y ≠ (block073S2 : ℝ))
    (hy3ne : y ≠ (block073S3 : ℝ))
    (hy4ne : y ≠ (block073S4 : ℝ)) :
    0 < block073V y := by
  have hcert := block073LeftCertificate_eq_true
  unfold block073LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block073LeftBoxes) (lo := block073LeftL) (hi := block073LeftR)
    (w1 := block073W1) (w2 := block073W2) (w3 := block073W3) (w4 := block073W4)
    (s1 := block073S1) (s2 := block073S2) (s3 := block073S3) (s4 := block073S4)
    hboxes hcover block073LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block073RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block073RightChunk000 block073W1 block073W2 block073W3 block073W4 block073S1 block073S2 block073S3 block073S4

theorem block073RightChunk000ParamsCertificate_eq_true :
    block073RightChunk000ParamsCertificate = true := by
  native_decide

theorem block073_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block073RightChunk000L : ℝ) (block073RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block073S1 : ℝ))
    (hy2ne : y ≠ (block073S2 : ℝ))
    (hy3ne : y ≠ (block073S3 : ℝ))
    (hy4ne : y ≠ (block073S4 : ℝ)) :
    0 < block073V y := by
  have hcert := block073RightChunk000Certificate_eq_true
  unfold block073RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block073RightChunk000) (lo := block073RightChunk000L) (hi := block073RightChunk000R)
    (w1 := block073W1) (w2 := block073W2) (w3 := block073W3) (w4 := block073W4)
    (s1 := block073S1) (s2 := block073S2) (s3 := block073S3) (s4 := block073S4)
    hboxes hcover block073RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block073_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block073RightL : ℝ) (block073RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block073S1 : ℝ))
    (hy2ne : y ≠ (block073S2 : ℝ))
    (hy3ne : y ≠ (block073S3 : ℝ))
    (hy4ne : y ≠ (block073S4 : ℝ)) :
    0 < block073V y := by
  have hL : (block073RightChunk000L : ℝ) = (block073RightL : ℝ) := by
    norm_num [block073RightChunk000L, block073RightL]
  have hR : (block073RightChunk000R : ℝ) = (block073RightR : ℝ) := by
    norm_num [block073RightChunk000R, block073RightR]
  have hyc : y ∈ Icc (block073RightChunk000L : ℝ) (block073RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block073_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block073_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block073LeftL : ℝ) (block073LeftR : ℝ) →
    y ≠ 0 → y ≠ (block073S1 : ℝ) → y ≠ (block073S2 : ℝ) →
    y ≠ (block073S3 : ℝ) → y ≠ (block073S4 : ℝ) → 0 < block073V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block073RightL : ℝ) (block073RightR : ℝ) →
    y ≠ 0 → y ≠ (block073S1 : ℝ) → y ≠ (block073S2 : ℝ) →
    y ≠ (block073S3 : ℝ) → y ≠ (block073S4 : ℝ) → 0 < block073V y)

theorem block073_reallog_certificate_proof :
    block073_reallog_certificate := by
  exact ⟨block073_left_V_pos, block073_right_V_pos⟩

end Block073
end M1817475
end Erdos1038Lean
