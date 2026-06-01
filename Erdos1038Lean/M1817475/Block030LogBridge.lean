import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block030

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block030

open Set

def block030W1 : Rat := ((5930049037506221 : Rat) / 2500000000000000)
def block030W2 : Rat := (0 : Rat)
def block030W3 : Rat := (0 : Rat)
def block030W4 : Rat := ((14164029170721673 : Rat) / 50000000000000000)
def block030S1 : Rat := ((18174751 : Rat) / 10000000)
def block030S2 : Rat := ((511587 : Rat) / 200000)
def block030S3 : Rat := ((107000619 : Rat) / 40000000)
def block030S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block030V (y : ℝ) : ℝ :=
  ratPotential block030W1 block030W2 block030W3 block030W4 block030S1 block030S2 block030S3 block030S4 y

def block030LeftParamsCertificate : Bool :=
  allBoxesSameParams block030LeftBoxes block030W1 block030W2 block030W3 block030W4 block030S1 block030S2 block030S3 block030S4

theorem block030LeftParamsCertificate_eq_true :
    block030LeftParamsCertificate = true := by
  native_decide

theorem block030_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block030LeftL : ℝ) (block030LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block030S1 : ℝ))
    (hy2ne : y ≠ (block030S2 : ℝ))
    (hy3ne : y ≠ (block030S3 : ℝ))
    (hy4ne : y ≠ (block030S4 : ℝ)) :
    0 < block030V y := by
  have hcert := block030LeftCertificate_eq_true
  unfold block030LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block030LeftBoxes) (lo := block030LeftL) (hi := block030LeftR)
    (w1 := block030W1) (w2 := block030W2) (w3 := block030W3) (w4 := block030W4)
    (s1 := block030S1) (s2 := block030S2) (s3 := block030S3) (s4 := block030S4)
    hboxes hcover block030LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block030RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block030RightChunk000 block030W1 block030W2 block030W3 block030W4 block030S1 block030S2 block030S3 block030S4

theorem block030RightChunk000ParamsCertificate_eq_true :
    block030RightChunk000ParamsCertificate = true := by
  native_decide

theorem block030_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block030RightChunk000L : ℝ) (block030RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block030S1 : ℝ))
    (hy2ne : y ≠ (block030S2 : ℝ))
    (hy3ne : y ≠ (block030S3 : ℝ))
    (hy4ne : y ≠ (block030S4 : ℝ)) :
    0 < block030V y := by
  have hcert := block030RightChunk000Certificate_eq_true
  unfold block030RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block030RightChunk000) (lo := block030RightChunk000L) (hi := block030RightChunk000R)
    (w1 := block030W1) (w2 := block030W2) (w3 := block030W3) (w4 := block030W4)
    (s1 := block030S1) (s2 := block030S2) (s3 := block030S3) (s4 := block030S4)
    hboxes hcover block030RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block030_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block030RightL : ℝ) (block030RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block030S1 : ℝ))
    (hy2ne : y ≠ (block030S2 : ℝ))
    (hy3ne : y ≠ (block030S3 : ℝ))
    (hy4ne : y ≠ (block030S4 : ℝ)) :
    0 < block030V y := by
  have hL : (block030RightChunk000L : ℝ) = (block030RightL : ℝ) := by
    norm_num [block030RightChunk000L, block030RightL]
  have hR : (block030RightChunk000R : ℝ) = (block030RightR : ℝ) := by
    norm_num [block030RightChunk000R, block030RightR]
  have hyc : y ∈ Icc (block030RightChunk000L : ℝ) (block030RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block030_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block030_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block030LeftL : ℝ) (block030LeftR : ℝ) →
    y ≠ 0 → y ≠ (block030S1 : ℝ) → y ≠ (block030S2 : ℝ) →
    y ≠ (block030S3 : ℝ) → y ≠ (block030S4 : ℝ) → 0 < block030V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block030RightL : ℝ) (block030RightR : ℝ) →
    y ≠ 0 → y ≠ (block030S1 : ℝ) → y ≠ (block030S2 : ℝ) →
    y ≠ (block030S3 : ℝ) → y ≠ (block030S4 : ℝ) → 0 < block030V y)

theorem block030_reallog_certificate_proof :
    block030_reallog_certificate := by
  exact ⟨block030_left_V_pos, block030_right_V_pos⟩

end Block030
end M1817475
end Erdos1038Lean
