import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block089

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block089

open Set

def block089W1 : Rat := ((1436816864222083 : Rat) / 400000000000000)
def block089W2 : Rat := (0 : Rat)
def block089W3 : Rat := (0 : Rat)
def block089W4 : Rat := ((23257339968202329 : Rat) / 100000000000000000)
def block089S1 : Rat := ((18174751 : Rat) / 10000000)
def block089S2 : Rat := ((511587 : Rat) / 200000)
def block089S3 : Rat := ((107000619 : Rat) / 40000000)
def block089S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block089V (y : ℝ) : ℝ :=
  ratPotential block089W1 block089W2 block089W3 block089W4 block089S1 block089S2 block089S3 block089S4 y

def block089LeftParamsCertificate : Bool :=
  allBoxesSameParams block089LeftBoxes block089W1 block089W2 block089W3 block089W4 block089S1 block089S2 block089S3 block089S4

theorem block089LeftParamsCertificate_eq_true :
    block089LeftParamsCertificate = true := by
  native_decide

theorem block089_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block089LeftL : ℝ) (block089LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block089S1 : ℝ))
    (hy2ne : y ≠ (block089S2 : ℝ))
    (hy3ne : y ≠ (block089S3 : ℝ))
    (hy4ne : y ≠ (block089S4 : ℝ)) :
    0 < block089V y := by
  have hcert := block089LeftCertificate_eq_true
  unfold block089LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block089LeftBoxes) (lo := block089LeftL) (hi := block089LeftR)
    (w1 := block089W1) (w2 := block089W2) (w3 := block089W3) (w4 := block089W4)
    (s1 := block089S1) (s2 := block089S2) (s3 := block089S3) (s4 := block089S4)
    hboxes hcover block089LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block089RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block089RightChunk000 block089W1 block089W2 block089W3 block089W4 block089S1 block089S2 block089S3 block089S4

theorem block089RightChunk000ParamsCertificate_eq_true :
    block089RightChunk000ParamsCertificate = true := by
  native_decide

theorem block089_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block089RightChunk000L : ℝ) (block089RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block089S1 : ℝ))
    (hy2ne : y ≠ (block089S2 : ℝ))
    (hy3ne : y ≠ (block089S3 : ℝ))
    (hy4ne : y ≠ (block089S4 : ℝ)) :
    0 < block089V y := by
  have hcert := block089RightChunk000Certificate_eq_true
  unfold block089RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block089RightChunk000) (lo := block089RightChunk000L) (hi := block089RightChunk000R)
    (w1 := block089W1) (w2 := block089W2) (w3 := block089W3) (w4 := block089W4)
    (s1 := block089S1) (s2 := block089S2) (s3 := block089S3) (s4 := block089S4)
    hboxes hcover block089RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block089_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block089RightL : ℝ) (block089RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block089S1 : ℝ))
    (hy2ne : y ≠ (block089S2 : ℝ))
    (hy3ne : y ≠ (block089S3 : ℝ))
    (hy4ne : y ≠ (block089S4 : ℝ)) :
    0 < block089V y := by
  have hL : (block089RightChunk000L : ℝ) = (block089RightL : ℝ) := by
    norm_num [block089RightChunk000L, block089RightL]
  have hR : (block089RightChunk000R : ℝ) = (block089RightR : ℝ) := by
    norm_num [block089RightChunk000R, block089RightR]
  have hyc : y ∈ Icc (block089RightChunk000L : ℝ) (block089RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block089_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block089_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block089LeftL : ℝ) (block089LeftR : ℝ) →
    y ≠ 0 → y ≠ (block089S1 : ℝ) → y ≠ (block089S2 : ℝ) →
    y ≠ (block089S3 : ℝ) → y ≠ (block089S4 : ℝ) → 0 < block089V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block089RightL : ℝ) (block089RightR : ℝ) →
    y ≠ 0 → y ≠ (block089S1 : ℝ) → y ≠ (block089S2 : ℝ) →
    y ≠ (block089S3 : ℝ) → y ≠ (block089S4 : ℝ) → 0 < block089V y)

theorem block089_reallog_certificate_proof :
    block089_reallog_certificate := by
  exact ⟨block089_left_V_pos, block089_right_V_pos⟩

end Block089
end M1817475
end Erdos1038Lean
