import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block143

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block143

open Set

def block143W1 : Rat := ((1219291632912201 : Rat) / 500000000000000)
def block143W2 : Rat := (0 : Rat)
def block143W3 : Rat := ((13299457297468403 : Rat) / 100000000000000000)
def block143W4 : Rat := ((2716337663984589 : Rat) / 25000000000000000)
def block143S1 : Rat := ((18174751 : Rat) / 10000000)
def block143S2 : Rat := ((511587 : Rat) / 200000)
def block143S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block143S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block143V (y : ℝ) : ℝ :=
  ratPotential block143W1 block143W2 block143W3 block143W4 block143S1 block143S2 block143S3 block143S4 y

def block143LeftParamsCertificate : Bool :=
  allBoxesSameParams block143LeftBoxes block143W1 block143W2 block143W3 block143W4 block143S1 block143S2 block143S3 block143S4

theorem block143LeftParamsCertificate_eq_true :
    block143LeftParamsCertificate = true := by
  native_decide

theorem block143_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block143LeftL : ℝ) (block143LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block143S1 : ℝ))
    (hy2ne : y ≠ (block143S2 : ℝ))
    (hy3ne : y ≠ (block143S3 : ℝ))
    (hy4ne : y ≠ (block143S4 : ℝ)) :
    0 < block143V y := by
  have hcert := block143LeftCertificate_eq_true
  unfold block143LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block143LeftBoxes) (lo := block143LeftL) (hi := block143LeftR)
    (w1 := block143W1) (w2 := block143W2) (w3 := block143W3) (w4 := block143W4)
    (s1 := block143S1) (s2 := block143S2) (s3 := block143S3) (s4 := block143S4)
    hboxes hcover block143LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block143RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block143RightChunk000 block143W1 block143W2 block143W3 block143W4 block143S1 block143S2 block143S3 block143S4

theorem block143RightChunk000ParamsCertificate_eq_true :
    block143RightChunk000ParamsCertificate = true := by
  native_decide

theorem block143_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block143RightChunk000L : ℝ) (block143RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block143S1 : ℝ))
    (hy2ne : y ≠ (block143S2 : ℝ))
    (hy3ne : y ≠ (block143S3 : ℝ))
    (hy4ne : y ≠ (block143S4 : ℝ)) :
    0 < block143V y := by
  have hcert := block143RightChunk000Certificate_eq_true
  unfold block143RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block143RightChunk000) (lo := block143RightChunk000L) (hi := block143RightChunk000R)
    (w1 := block143W1) (w2 := block143W2) (w3 := block143W3) (w4 := block143W4)
    (s1 := block143S1) (s2 := block143S2) (s3 := block143S3) (s4 := block143S4)
    hboxes hcover block143RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block143_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block143RightL : ℝ) (block143RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block143S1 : ℝ))
    (hy2ne : y ≠ (block143S2 : ℝ))
    (hy3ne : y ≠ (block143S3 : ℝ))
    (hy4ne : y ≠ (block143S4 : ℝ)) :
    0 < block143V y := by
  have hL : (block143RightChunk000L : ℝ) = (block143RightL : ℝ) := by
    norm_num [block143RightChunk000L, block143RightL]
  have hR : (block143RightChunk000R : ℝ) = (block143RightR : ℝ) := by
    norm_num [block143RightChunk000R, block143RightR]
  have hyc : y ∈ Icc (block143RightChunk000L : ℝ) (block143RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block143_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block143_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block143LeftL : ℝ) (block143LeftR : ℝ) →
    y ≠ 0 → y ≠ (block143S1 : ℝ) → y ≠ (block143S2 : ℝ) →
    y ≠ (block143S3 : ℝ) → y ≠ (block143S4 : ℝ) → 0 < block143V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block143RightL : ℝ) (block143RightR : ℝ) →
    y ≠ 0 → y ≠ (block143S1 : ℝ) → y ≠ (block143S2 : ℝ) →
    y ≠ (block143S3 : ℝ) → y ≠ (block143S4 : ℝ) → 0 < block143V y)

theorem block143_reallog_certificate_proof :
    block143_reallog_certificate := by
  exact ⟨block143_left_V_pos, block143_right_V_pos⟩

end Block143
end M1817475
end Erdos1038Lean
