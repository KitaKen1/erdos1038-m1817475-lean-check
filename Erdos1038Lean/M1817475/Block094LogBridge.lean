import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block094

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block094

open Set

def block094W1 : Rat := ((2179178215080593 : Rat) / 1000000000000000)
def block094W2 : Rat := (0 : Rat)
def block094W3 : Rat := ((6397602518619737 : Rat) / 100000000000000000)
def block094W4 : Rat := ((1994003341453323 : Rat) / 10000000000000000)
def block094S1 : Rat := ((18174751 : Rat) / 10000000)
def block094S2 : Rat := ((511587 : Rat) / 200000)
def block094S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block094S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block094V (y : ℝ) : ℝ :=
  ratPotential block094W1 block094W2 block094W3 block094W4 block094S1 block094S2 block094S3 block094S4 y

def block094LeftParamsCertificate : Bool :=
  allBoxesSameParams block094LeftBoxes block094W1 block094W2 block094W3 block094W4 block094S1 block094S2 block094S3 block094S4

theorem block094LeftParamsCertificate_eq_true :
    block094LeftParamsCertificate = true := by
  native_decide

theorem block094_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block094LeftL : ℝ) (block094LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block094S1 : ℝ))
    (hy2ne : y ≠ (block094S2 : ℝ))
    (hy3ne : y ≠ (block094S3 : ℝ))
    (hy4ne : y ≠ (block094S4 : ℝ)) :
    0 < block094V y := by
  have hcert := block094LeftCertificate_eq_true
  unfold block094LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block094LeftBoxes) (lo := block094LeftL) (hi := block094LeftR)
    (w1 := block094W1) (w2 := block094W2) (w3 := block094W3) (w4 := block094W4)
    (s1 := block094S1) (s2 := block094S2) (s3 := block094S3) (s4 := block094S4)
    hboxes hcover block094LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block094RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block094RightChunk000 block094W1 block094W2 block094W3 block094W4 block094S1 block094S2 block094S3 block094S4

theorem block094RightChunk000ParamsCertificate_eq_true :
    block094RightChunk000ParamsCertificate = true := by
  native_decide

theorem block094_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block094RightChunk000L : ℝ) (block094RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block094S1 : ℝ))
    (hy2ne : y ≠ (block094S2 : ℝ))
    (hy3ne : y ≠ (block094S3 : ℝ))
    (hy4ne : y ≠ (block094S4 : ℝ)) :
    0 < block094V y := by
  have hcert := block094RightChunk000Certificate_eq_true
  unfold block094RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block094RightChunk000) (lo := block094RightChunk000L) (hi := block094RightChunk000R)
    (w1 := block094W1) (w2 := block094W2) (w3 := block094W3) (w4 := block094W4)
    (s1 := block094S1) (s2 := block094S2) (s3 := block094S3) (s4 := block094S4)
    hboxes hcover block094RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block094_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block094RightL : ℝ) (block094RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block094S1 : ℝ))
    (hy2ne : y ≠ (block094S2 : ℝ))
    (hy3ne : y ≠ (block094S3 : ℝ))
    (hy4ne : y ≠ (block094S4 : ℝ)) :
    0 < block094V y := by
  have hL : (block094RightChunk000L : ℝ) = (block094RightL : ℝ) := by
    norm_num [block094RightChunk000L, block094RightL]
  have hR : (block094RightChunk000R : ℝ) = (block094RightR : ℝ) := by
    norm_num [block094RightChunk000R, block094RightR]
  have hyc : y ∈ Icc (block094RightChunk000L : ℝ) (block094RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block094_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block094_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block094LeftL : ℝ) (block094LeftR : ℝ) →
    y ≠ 0 → y ≠ (block094S1 : ℝ) → y ≠ (block094S2 : ℝ) →
    y ≠ (block094S3 : ℝ) → y ≠ (block094S4 : ℝ) → 0 < block094V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block094RightL : ℝ) (block094RightR : ℝ) →
    y ≠ 0 → y ≠ (block094S1 : ℝ) → y ≠ (block094S2 : ℝ) →
    y ≠ (block094S3 : ℝ) → y ≠ (block094S4 : ℝ) → 0 < block094V y)

theorem block094_reallog_certificate_proof :
    block094_reallog_certificate := by
  exact ⟨block094_left_V_pos, block094_right_V_pos⟩

end Block094
end M1817475
end Erdos1038Lean
