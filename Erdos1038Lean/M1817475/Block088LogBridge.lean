import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block088

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block088

open Set

def block088W1 : Rat := ((3560451427969959 : Rat) / 1000000000000000)
def block088W2 : Rat := (0 : Rat)
def block088W3 : Rat := (0 : Rat)
def block088W4 : Rat := ((1168292018409439 : Rat) / 5000000000000000)
def block088S1 : Rat := ((18174751 : Rat) / 10000000)
def block088S2 : Rat := ((511587 : Rat) / 200000)
def block088S3 : Rat := ((107000619 : Rat) / 40000000)
def block088S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block088V (y : ℝ) : ℝ :=
  ratPotential block088W1 block088W2 block088W3 block088W4 block088S1 block088S2 block088S3 block088S4 y

def block088LeftParamsCertificate : Bool :=
  allBoxesSameParams block088LeftBoxes block088W1 block088W2 block088W3 block088W4 block088S1 block088S2 block088S3 block088S4

theorem block088LeftParamsCertificate_eq_true :
    block088LeftParamsCertificate = true := by
  native_decide

theorem block088_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block088LeftL : ℝ) (block088LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block088S1 : ℝ))
    (hy2ne : y ≠ (block088S2 : ℝ))
    (hy3ne : y ≠ (block088S3 : ℝ))
    (hy4ne : y ≠ (block088S4 : ℝ)) :
    0 < block088V y := by
  have hcert := block088LeftCertificate_eq_true
  unfold block088LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block088LeftBoxes) (lo := block088LeftL) (hi := block088LeftR)
    (w1 := block088W1) (w2 := block088W2) (w3 := block088W3) (w4 := block088W4)
    (s1 := block088S1) (s2 := block088S2) (s3 := block088S3) (s4 := block088S4)
    hboxes hcover block088LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block088RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block088RightChunk000 block088W1 block088W2 block088W3 block088W4 block088S1 block088S2 block088S3 block088S4

theorem block088RightChunk000ParamsCertificate_eq_true :
    block088RightChunk000ParamsCertificate = true := by
  native_decide

theorem block088_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block088RightChunk000L : ℝ) (block088RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block088S1 : ℝ))
    (hy2ne : y ≠ (block088S2 : ℝ))
    (hy3ne : y ≠ (block088S3 : ℝ))
    (hy4ne : y ≠ (block088S4 : ℝ)) :
    0 < block088V y := by
  have hcert := block088RightChunk000Certificate_eq_true
  unfold block088RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block088RightChunk000) (lo := block088RightChunk000L) (hi := block088RightChunk000R)
    (w1 := block088W1) (w2 := block088W2) (w3 := block088W3) (w4 := block088W4)
    (s1 := block088S1) (s2 := block088S2) (s3 := block088S3) (s4 := block088S4)
    hboxes hcover block088RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block088_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block088RightL : ℝ) (block088RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block088S1 : ℝ))
    (hy2ne : y ≠ (block088S2 : ℝ))
    (hy3ne : y ≠ (block088S3 : ℝ))
    (hy4ne : y ≠ (block088S4 : ℝ)) :
    0 < block088V y := by
  have hL : (block088RightChunk000L : ℝ) = (block088RightL : ℝ) := by
    norm_num [block088RightChunk000L, block088RightL]
  have hR : (block088RightChunk000R : ℝ) = (block088RightR : ℝ) := by
    norm_num [block088RightChunk000R, block088RightR]
  have hyc : y ∈ Icc (block088RightChunk000L : ℝ) (block088RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block088_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block088_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block088LeftL : ℝ) (block088LeftR : ℝ) →
    y ≠ 0 → y ≠ (block088S1 : ℝ) → y ≠ (block088S2 : ℝ) →
    y ≠ (block088S3 : ℝ) → y ≠ (block088S4 : ℝ) → 0 < block088V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block088RightL : ℝ) (block088RightR : ℝ) →
    y ≠ 0 → y ≠ (block088S1 : ℝ) → y ≠ (block088S2 : ℝ) →
    y ≠ (block088S3 : ℝ) → y ≠ (block088S4 : ℝ) → 0 < block088V y)

theorem block088_reallog_certificate_proof :
    block088_reallog_certificate := by
  exact ⟨block088_left_V_pos, block088_right_V_pos⟩

end Block088
end M1817475
end Erdos1038Lean
