import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block061

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block061

open Set

def block061W1 : Rat := ((115339184286651 : Rat) / 40000000000000)
def block061W2 : Rat := (0 : Rat)
def block061W3 : Rat := (0 : Rat)
def block061W4 : Rat := ((2594593333037339 : Rat) / 10000000000000000)
def block061S1 : Rat := ((18174751 : Rat) / 10000000)
def block061S2 : Rat := ((511587 : Rat) / 200000)
def block061S3 : Rat := ((107000619 : Rat) / 40000000)
def block061S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block061V (y : ℝ) : ℝ :=
  ratPotential block061W1 block061W2 block061W3 block061W4 block061S1 block061S2 block061S3 block061S4 y

def block061LeftParamsCertificate : Bool :=
  allBoxesSameParams block061LeftBoxes block061W1 block061W2 block061W3 block061W4 block061S1 block061S2 block061S3 block061S4

theorem block061LeftParamsCertificate_eq_true :
    block061LeftParamsCertificate = true := by
  native_decide

theorem block061_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block061LeftL : ℝ) (block061LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block061S1 : ℝ))
    (hy2ne : y ≠ (block061S2 : ℝ))
    (hy3ne : y ≠ (block061S3 : ℝ))
    (hy4ne : y ≠ (block061S4 : ℝ)) :
    0 < block061V y := by
  have hcert := block061LeftCertificate_eq_true
  unfold block061LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block061LeftBoxes) (lo := block061LeftL) (hi := block061LeftR)
    (w1 := block061W1) (w2 := block061W2) (w3 := block061W3) (w4 := block061W4)
    (s1 := block061S1) (s2 := block061S2) (s3 := block061S3) (s4 := block061S4)
    hboxes hcover block061LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block061RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block061RightChunk000 block061W1 block061W2 block061W3 block061W4 block061S1 block061S2 block061S3 block061S4

theorem block061RightChunk000ParamsCertificate_eq_true :
    block061RightChunk000ParamsCertificate = true := by
  native_decide

theorem block061_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block061RightChunk000L : ℝ) (block061RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block061S1 : ℝ))
    (hy2ne : y ≠ (block061S2 : ℝ))
    (hy3ne : y ≠ (block061S3 : ℝ))
    (hy4ne : y ≠ (block061S4 : ℝ)) :
    0 < block061V y := by
  have hcert := block061RightChunk000Certificate_eq_true
  unfold block061RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block061RightChunk000) (lo := block061RightChunk000L) (hi := block061RightChunk000R)
    (w1 := block061W1) (w2 := block061W2) (w3 := block061W3) (w4 := block061W4)
    (s1 := block061S1) (s2 := block061S2) (s3 := block061S3) (s4 := block061S4)
    hboxes hcover block061RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block061_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block061RightL : ℝ) (block061RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block061S1 : ℝ))
    (hy2ne : y ≠ (block061S2 : ℝ))
    (hy3ne : y ≠ (block061S3 : ℝ))
    (hy4ne : y ≠ (block061S4 : ℝ)) :
    0 < block061V y := by
  have hL : (block061RightChunk000L : ℝ) = (block061RightL : ℝ) := by
    norm_num [block061RightChunk000L, block061RightL]
  have hR : (block061RightChunk000R : ℝ) = (block061RightR : ℝ) := by
    norm_num [block061RightChunk000R, block061RightR]
  have hyc : y ∈ Icc (block061RightChunk000L : ℝ) (block061RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block061_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block061_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block061LeftL : ℝ) (block061LeftR : ℝ) →
    y ≠ 0 → y ≠ (block061S1 : ℝ) → y ≠ (block061S2 : ℝ) →
    y ≠ (block061S3 : ℝ) → y ≠ (block061S4 : ℝ) → 0 < block061V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block061RightL : ℝ) (block061RightR : ℝ) →
    y ≠ 0 → y ≠ (block061S1 : ℝ) → y ≠ (block061S2 : ℝ) →
    y ≠ (block061S3 : ℝ) → y ≠ (block061S4 : ℝ) → 0 < block061V y)

theorem block061_reallog_certificate_proof :
    block061_reallog_certificate := by
  exact ⟨block061_left_V_pos, block061_right_V_pos⟩

end Block061
end M1817475
end Erdos1038Lean
