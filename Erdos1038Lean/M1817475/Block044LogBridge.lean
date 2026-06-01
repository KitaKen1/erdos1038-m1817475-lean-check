import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block044

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block044

open Set

def block044W1 : Rat := ((25782119724248767 : Rat) / 10000000000000000)
def block044W2 : Rat := (0 : Rat)
def block044W3 : Rat := (0 : Rat)
def block044W4 : Rat := ((27311091522764747 : Rat) / 100000000000000000)
def block044S1 : Rat := ((18174751 : Rat) / 10000000)
def block044S2 : Rat := ((511587 : Rat) / 200000)
def block044S3 : Rat := ((107000619 : Rat) / 40000000)
def block044S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block044V (y : ℝ) : ℝ :=
  ratPotential block044W1 block044W2 block044W3 block044W4 block044S1 block044S2 block044S3 block044S4 y

def block044LeftParamsCertificate : Bool :=
  allBoxesSameParams block044LeftBoxes block044W1 block044W2 block044W3 block044W4 block044S1 block044S2 block044S3 block044S4

theorem block044LeftParamsCertificate_eq_true :
    block044LeftParamsCertificate = true := by
  native_decide

theorem block044_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block044LeftL : ℝ) (block044LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block044S1 : ℝ))
    (hy2ne : y ≠ (block044S2 : ℝ))
    (hy3ne : y ≠ (block044S3 : ℝ))
    (hy4ne : y ≠ (block044S4 : ℝ)) :
    0 < block044V y := by
  have hcert := block044LeftCertificate_eq_true
  unfold block044LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block044LeftBoxes) (lo := block044LeftL) (hi := block044LeftR)
    (w1 := block044W1) (w2 := block044W2) (w3 := block044W3) (w4 := block044W4)
    (s1 := block044S1) (s2 := block044S2) (s3 := block044S3) (s4 := block044S4)
    hboxes hcover block044LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block044RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block044RightChunk000 block044W1 block044W2 block044W3 block044W4 block044S1 block044S2 block044S3 block044S4

theorem block044RightChunk000ParamsCertificate_eq_true :
    block044RightChunk000ParamsCertificate = true := by
  native_decide

theorem block044_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block044RightChunk000L : ℝ) (block044RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block044S1 : ℝ))
    (hy2ne : y ≠ (block044S2 : ℝ))
    (hy3ne : y ≠ (block044S3 : ℝ))
    (hy4ne : y ≠ (block044S4 : ℝ)) :
    0 < block044V y := by
  have hcert := block044RightChunk000Certificate_eq_true
  unfold block044RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block044RightChunk000) (lo := block044RightChunk000L) (hi := block044RightChunk000R)
    (w1 := block044W1) (w2 := block044W2) (w3 := block044W3) (w4 := block044W4)
    (s1 := block044S1) (s2 := block044S2) (s3 := block044S3) (s4 := block044S4)
    hboxes hcover block044RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block044_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block044RightL : ℝ) (block044RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block044S1 : ℝ))
    (hy2ne : y ≠ (block044S2 : ℝ))
    (hy3ne : y ≠ (block044S3 : ℝ))
    (hy4ne : y ≠ (block044S4 : ℝ)) :
    0 < block044V y := by
  have hL : (block044RightChunk000L : ℝ) = (block044RightL : ℝ) := by
    norm_num [block044RightChunk000L, block044RightL]
  have hR : (block044RightChunk000R : ℝ) = (block044RightR : ℝ) := by
    norm_num [block044RightChunk000R, block044RightR]
  have hyc : y ∈ Icc (block044RightChunk000L : ℝ) (block044RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block044_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block044_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block044LeftL : ℝ) (block044LeftR : ℝ) →
    y ≠ 0 → y ≠ (block044S1 : ℝ) → y ≠ (block044S2 : ℝ) →
    y ≠ (block044S3 : ℝ) → y ≠ (block044S4 : ℝ) → 0 < block044V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block044RightL : ℝ) (block044RightR : ℝ) →
    y ≠ 0 → y ≠ (block044S1 : ℝ) → y ≠ (block044S2 : ℝ) →
    y ≠ (block044S3 : ℝ) → y ≠ (block044S4 : ℝ) → 0 < block044V y)

theorem block044_reallog_certificate_proof :
    block044_reallog_certificate := by
  exact ⟨block044_left_V_pos, block044_right_V_pos⟩

end Block044
end M1817475
end Erdos1038Lean
