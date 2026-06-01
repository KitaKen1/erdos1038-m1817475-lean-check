import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block024

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block024

open Set

def block024W1 : Rat := ((1146721402554001 : Rat) / 500000000000000)
def block024W2 : Rat := (0 : Rat)
def block024W3 : Rat := (0 : Rat)
def block024W4 : Rat := ((1436963358026579 : Rat) / 5000000000000000)
def block024S1 : Rat := ((18174751 : Rat) / 10000000)
def block024S2 : Rat := ((511587 : Rat) / 200000)
def block024S3 : Rat := ((107000619 : Rat) / 40000000)
def block024S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block024V (y : ℝ) : ℝ :=
  ratPotential block024W1 block024W2 block024W3 block024W4 block024S1 block024S2 block024S3 block024S4 y

def block024LeftParamsCertificate : Bool :=
  allBoxesSameParams block024LeftBoxes block024W1 block024W2 block024W3 block024W4 block024S1 block024S2 block024S3 block024S4

theorem block024LeftParamsCertificate_eq_true :
    block024LeftParamsCertificate = true := by
  native_decide

theorem block024_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block024LeftL : ℝ) (block024LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block024S1 : ℝ))
    (hy2ne : y ≠ (block024S2 : ℝ))
    (hy3ne : y ≠ (block024S3 : ℝ))
    (hy4ne : y ≠ (block024S4 : ℝ)) :
    0 < block024V y := by
  have hcert := block024LeftCertificate_eq_true
  unfold block024LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block024LeftBoxes) (lo := block024LeftL) (hi := block024LeftR)
    (w1 := block024W1) (w2 := block024W2) (w3 := block024W3) (w4 := block024W4)
    (s1 := block024S1) (s2 := block024S2) (s3 := block024S3) (s4 := block024S4)
    hboxes hcover block024LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block024RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block024RightChunk000 block024W1 block024W2 block024W3 block024W4 block024S1 block024S2 block024S3 block024S4

theorem block024RightChunk000ParamsCertificate_eq_true :
    block024RightChunk000ParamsCertificate = true := by
  native_decide

theorem block024_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block024RightChunk000L : ℝ) (block024RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block024S1 : ℝ))
    (hy2ne : y ≠ (block024S2 : ℝ))
    (hy3ne : y ≠ (block024S3 : ℝ))
    (hy4ne : y ≠ (block024S4 : ℝ)) :
    0 < block024V y := by
  have hcert := block024RightChunk000Certificate_eq_true
  unfold block024RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block024RightChunk000) (lo := block024RightChunk000L) (hi := block024RightChunk000R)
    (w1 := block024W1) (w2 := block024W2) (w3 := block024W3) (w4 := block024W4)
    (s1 := block024S1) (s2 := block024S2) (s3 := block024S3) (s4 := block024S4)
    hboxes hcover block024RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block024_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block024RightL : ℝ) (block024RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block024S1 : ℝ))
    (hy2ne : y ≠ (block024S2 : ℝ))
    (hy3ne : y ≠ (block024S3 : ℝ))
    (hy4ne : y ≠ (block024S4 : ℝ)) :
    0 < block024V y := by
  have hL : (block024RightChunk000L : ℝ) = (block024RightL : ℝ) := by
    norm_num [block024RightChunk000L, block024RightL]
  have hR : (block024RightChunk000R : ℝ) = (block024RightR : ℝ) := by
    norm_num [block024RightChunk000R, block024RightR]
  have hyc : y ∈ Icc (block024RightChunk000L : ℝ) (block024RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block024_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block024_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block024LeftL : ℝ) (block024LeftR : ℝ) →
    y ≠ 0 → y ≠ (block024S1 : ℝ) → y ≠ (block024S2 : ℝ) →
    y ≠ (block024S3 : ℝ) → y ≠ (block024S4 : ℝ) → 0 < block024V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block024RightL : ℝ) (block024RightR : ℝ) →
    y ≠ 0 → y ≠ (block024S1 : ℝ) → y ≠ (block024S2 : ℝ) →
    y ≠ (block024S3 : ℝ) → y ≠ (block024S4 : ℝ) → 0 < block024V y)

theorem block024_reallog_certificate_proof :
    block024_reallog_certificate := by
  exact ⟨block024_left_V_pos, block024_right_V_pos⟩

end Block024
end M1817475
end Erdos1038Lean
