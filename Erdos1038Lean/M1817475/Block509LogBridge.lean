import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block509

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block509

open Set

def block509W1 : Rat := ((4381733241571899 : Rat) / 10000000000000000)
def block509W2 : Rat := (0 : Rat)
def block509W3 : Rat := ((10855805860893 : Rat) / 25000000000000)
def block509W4 : Rat := ((7713926097802143 : Rat) / 1000000000000000000)
def block509S1 : Rat := ((18174751 : Rat) / 10000000)
def block509S2 : Rat := ((511587 : Rat) / 200000)
def block509S3 : Rat := ((26036612339285714317 : Rat) / 10000000000000000000)
def block509S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block509V (y : ℝ) : ℝ :=
  ratPotential block509W1 block509W2 block509W3 block509W4 block509S1 block509S2 block509S3 block509S4 y

def block509LeftParamsCertificate : Bool :=
  allBoxesSameParams block509LeftBoxes block509W1 block509W2 block509W3 block509W4 block509S1 block509S2 block509S3 block509S4

theorem block509LeftParamsCertificate_eq_true :
    block509LeftParamsCertificate = true := by
  native_decide

theorem block509_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block509LeftL : ℝ) (block509LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block509S1 : ℝ))
    (hy2ne : y ≠ (block509S2 : ℝ))
    (hy3ne : y ≠ (block509S3 : ℝ))
    (hy4ne : y ≠ (block509S4 : ℝ)) :
    0 < block509V y := by
  have hcert := block509LeftCertificate_eq_true
  unfold block509LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block509LeftBoxes) (lo := block509LeftL) (hi := block509LeftR)
    (w1 := block509W1) (w2 := block509W2) (w3 := block509W3) (w4 := block509W4)
    (s1 := block509S1) (s2 := block509S2) (s3 := block509S3) (s4 := block509S4)
    hboxes hcover block509LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block509RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block509RightChunk000 block509W1 block509W2 block509W3 block509W4 block509S1 block509S2 block509S3 block509S4

theorem block509RightChunk000ParamsCertificate_eq_true :
    block509RightChunk000ParamsCertificate = true := by
  native_decide

theorem block509_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block509RightChunk000L : ℝ) (block509RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block509S1 : ℝ))
    (hy2ne : y ≠ (block509S2 : ℝ))
    (hy3ne : y ≠ (block509S3 : ℝ))
    (hy4ne : y ≠ (block509S4 : ℝ)) :
    0 < block509V y := by
  have hcert := block509RightChunk000Certificate_eq_true
  unfold block509RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block509RightChunk000) (lo := block509RightChunk000L) (hi := block509RightChunk000R)
    (w1 := block509W1) (w2 := block509W2) (w3 := block509W3) (w4 := block509W4)
    (s1 := block509S1) (s2 := block509S2) (s3 := block509S3) (s4 := block509S4)
    hboxes hcover block509RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block509_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block509RightL : ℝ) (block509RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block509S1 : ℝ))
    (hy2ne : y ≠ (block509S2 : ℝ))
    (hy3ne : y ≠ (block509S3 : ℝ))
    (hy4ne : y ≠ (block509S4 : ℝ)) :
    0 < block509V y := by
  have hL : (block509RightChunk000L : ℝ) = (block509RightL : ℝ) := by
    norm_num [block509RightChunk000L, block509RightL]
  have hR : (block509RightChunk000R : ℝ) = (block509RightR : ℝ) := by
    norm_num [block509RightChunk000R, block509RightR]
  have hyc : y ∈ Icc (block509RightChunk000L : ℝ) (block509RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block509_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block509_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block509LeftL : ℝ) (block509LeftR : ℝ) →
    y ≠ 0 → y ≠ (block509S1 : ℝ) → y ≠ (block509S2 : ℝ) →
    y ≠ (block509S3 : ℝ) → y ≠ (block509S4 : ℝ) → 0 < block509V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block509RightL : ℝ) (block509RightR : ℝ) →
    y ≠ 0 → y ≠ (block509S1 : ℝ) → y ≠ (block509S2 : ℝ) →
    y ≠ (block509S3 : ℝ) → y ≠ (block509S4 : ℝ) → 0 < block509V y)

theorem block509_reallog_certificate_proof :
    block509_reallog_certificate := by
  exact ⟨block509_left_V_pos, block509_right_V_pos⟩

end Block509
end M1817475
end Erdos1038Lean
