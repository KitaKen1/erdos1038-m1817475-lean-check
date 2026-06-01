import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block552

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block552

open Set

def block552W1 : Rat := ((19289807266045683 : Rat) / 50000000000000000)
def block552W2 : Rat := (0 : Rat)
def block552W3 : Rat := ((2302847170231451 : Rat) / 5000000000000000)
def block552W4 : Rat := (0 : Rat)
def block552S1 : Rat := ((18174751 : Rat) / 10000000)
def block552S2 : Rat := ((511587 : Rat) / 200000)
def block552S3 : Rat := ((129342450089285714479 : Rat) / 50000000000000000000)
def block552S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block552V (y : ℝ) : ℝ :=
  ratPotential block552W1 block552W2 block552W3 block552W4 block552S1 block552S2 block552S3 block552S4 y

def block552LeftParamsCertificate : Bool :=
  allBoxesSameParams block552LeftBoxes block552W1 block552W2 block552W3 block552W4 block552S1 block552S2 block552S3 block552S4

theorem block552LeftParamsCertificate_eq_true :
    block552LeftParamsCertificate = true := by
  native_decide

theorem block552_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block552LeftL : ℝ) (block552LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block552S1 : ℝ))
    (hy2ne : y ≠ (block552S2 : ℝ))
    (hy3ne : y ≠ (block552S3 : ℝ))
    (hy4ne : y ≠ (block552S4 : ℝ)) :
    0 < block552V y := by
  have hcert := block552LeftCertificate_eq_true
  unfold block552LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block552LeftBoxes) (lo := block552LeftL) (hi := block552LeftR)
    (w1 := block552W1) (w2 := block552W2) (w3 := block552W3) (w4 := block552W4)
    (s1 := block552S1) (s2 := block552S2) (s3 := block552S3) (s4 := block552S4)
    hboxes hcover block552LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block552RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block552RightChunk000 block552W1 block552W2 block552W3 block552W4 block552S1 block552S2 block552S3 block552S4

theorem block552RightChunk000ParamsCertificate_eq_true :
    block552RightChunk000ParamsCertificate = true := by
  native_decide

theorem block552_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block552RightChunk000L : ℝ) (block552RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block552S1 : ℝ))
    (hy2ne : y ≠ (block552S2 : ℝ))
    (hy3ne : y ≠ (block552S3 : ℝ))
    (hy4ne : y ≠ (block552S4 : ℝ)) :
    0 < block552V y := by
  have hcert := block552RightChunk000Certificate_eq_true
  unfold block552RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block552RightChunk000) (lo := block552RightChunk000L) (hi := block552RightChunk000R)
    (w1 := block552W1) (w2 := block552W2) (w3 := block552W3) (w4 := block552W4)
    (s1 := block552S1) (s2 := block552S2) (s3 := block552S3) (s4 := block552S4)
    hboxes hcover block552RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block552_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block552RightL : ℝ) (block552RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block552S1 : ℝ))
    (hy2ne : y ≠ (block552S2 : ℝ))
    (hy3ne : y ≠ (block552S3 : ℝ))
    (hy4ne : y ≠ (block552S4 : ℝ)) :
    0 < block552V y := by
  have hL : (block552RightChunk000L : ℝ) = (block552RightL : ℝ) := by
    norm_num [block552RightChunk000L, block552RightL]
  have hR : (block552RightChunk000R : ℝ) = (block552RightR : ℝ) := by
    norm_num [block552RightChunk000R, block552RightR]
  have hyc : y ∈ Icc (block552RightChunk000L : ℝ) (block552RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block552_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block552_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block552LeftL : ℝ) (block552LeftR : ℝ) →
    y ≠ 0 → y ≠ (block552S1 : ℝ) → y ≠ (block552S2 : ℝ) →
    y ≠ (block552S3 : ℝ) → y ≠ (block552S4 : ℝ) → 0 < block552V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block552RightL : ℝ) (block552RightR : ℝ) →
    y ≠ 0 → y ≠ (block552S1 : ℝ) → y ≠ (block552S2 : ℝ) →
    y ≠ (block552S3 : ℝ) → y ≠ (block552S4 : ℝ) → 0 < block552V y)

theorem block552_reallog_certificate_proof :
    block552_reallog_certificate := by
  exact ⟨block552_left_V_pos, block552_right_V_pos⟩

end Block552
end M1817475
end Erdos1038Lean
