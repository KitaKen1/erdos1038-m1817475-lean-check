import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block037

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block037

open Set

def block037W1 : Rat := ((4941579519493101 : Rat) / 2000000000000000)
def block037W2 : Rat := (0 : Rat)
def block037W3 : Rat := (0 : Rat)
def block037W4 : Rat := ((5566051759838433 : Rat) / 20000000000000000)
def block037S1 : Rat := ((18174751 : Rat) / 10000000)
def block037S2 : Rat := ((511587 : Rat) / 200000)
def block037S3 : Rat := ((107000619 : Rat) / 40000000)
def block037S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block037V (y : ℝ) : ℝ :=
  ratPotential block037W1 block037W2 block037W3 block037W4 block037S1 block037S2 block037S3 block037S4 y

def block037LeftParamsCertificate : Bool :=
  allBoxesSameParams block037LeftBoxes block037W1 block037W2 block037W3 block037W4 block037S1 block037S2 block037S3 block037S4

theorem block037LeftParamsCertificate_eq_true :
    block037LeftParamsCertificate = true := by
  native_decide

theorem block037_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block037LeftL : ℝ) (block037LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block037S1 : ℝ))
    (hy2ne : y ≠ (block037S2 : ℝ))
    (hy3ne : y ≠ (block037S3 : ℝ))
    (hy4ne : y ≠ (block037S4 : ℝ)) :
    0 < block037V y := by
  have hcert := block037LeftCertificate_eq_true
  unfold block037LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block037LeftBoxes) (lo := block037LeftL) (hi := block037LeftR)
    (w1 := block037W1) (w2 := block037W2) (w3 := block037W3) (w4 := block037W4)
    (s1 := block037S1) (s2 := block037S2) (s3 := block037S3) (s4 := block037S4)
    hboxes hcover block037LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block037RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block037RightChunk000 block037W1 block037W2 block037W3 block037W4 block037S1 block037S2 block037S3 block037S4

theorem block037RightChunk000ParamsCertificate_eq_true :
    block037RightChunk000ParamsCertificate = true := by
  native_decide

theorem block037_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block037RightChunk000L : ℝ) (block037RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block037S1 : ℝ))
    (hy2ne : y ≠ (block037S2 : ℝ))
    (hy3ne : y ≠ (block037S3 : ℝ))
    (hy4ne : y ≠ (block037S4 : ℝ)) :
    0 < block037V y := by
  have hcert := block037RightChunk000Certificate_eq_true
  unfold block037RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block037RightChunk000) (lo := block037RightChunk000L) (hi := block037RightChunk000R)
    (w1 := block037W1) (w2 := block037W2) (w3 := block037W3) (w4 := block037W4)
    (s1 := block037S1) (s2 := block037S2) (s3 := block037S3) (s4 := block037S4)
    hboxes hcover block037RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block037_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block037RightL : ℝ) (block037RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block037S1 : ℝ))
    (hy2ne : y ≠ (block037S2 : ℝ))
    (hy3ne : y ≠ (block037S3 : ℝ))
    (hy4ne : y ≠ (block037S4 : ℝ)) :
    0 < block037V y := by
  have hL : (block037RightChunk000L : ℝ) = (block037RightL : ℝ) := by
    norm_num [block037RightChunk000L, block037RightL]
  have hR : (block037RightChunk000R : ℝ) = (block037RightR : ℝ) := by
    norm_num [block037RightChunk000R, block037RightR]
  have hyc : y ∈ Icc (block037RightChunk000L : ℝ) (block037RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block037_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block037_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block037LeftL : ℝ) (block037LeftR : ℝ) →
    y ≠ 0 → y ≠ (block037S1 : ℝ) → y ≠ (block037S2 : ℝ) →
    y ≠ (block037S3 : ℝ) → y ≠ (block037S4 : ℝ) → 0 < block037V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block037RightL : ℝ) (block037RightR : ℝ) →
    y ≠ 0 → y ≠ (block037S1 : ℝ) → y ≠ (block037S2 : ℝ) →
    y ≠ (block037S3 : ℝ) → y ≠ (block037S4 : ℝ) → 0 < block037V y)

theorem block037_reallog_certificate_proof :
    block037_reallog_certificate := by
  exact ⟨block037_left_V_pos, block037_right_V_pos⟩

end Block037
end M1817475
end Erdos1038Lean
