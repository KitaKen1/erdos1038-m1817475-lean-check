import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block396

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block396

open Set

def block396W1 : Rat := ((3512351882148123 : Rat) / 5000000000000000)
def block396W2 : Rat := (0 : Rat)
def block396W3 : Rat := ((3747134027076899 : Rat) / 10000000000000000)
def block396W4 : Rat := (0 : Rat)
def block396S1 : Rat := ((18174751 : Rat) / 10000000)
def block396S2 : Rat := ((511587 : Rat) / 200000)
def block396S3 : Rat := ((133095878660714285743 : Rat) / 50000000000000000000)
def block396S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block396V (y : ℝ) : ℝ :=
  ratPotential block396W1 block396W2 block396W3 block396W4 block396S1 block396S2 block396S3 block396S4 y

def block396LeftParamsCertificate : Bool :=
  allBoxesSameParams block396LeftBoxes block396W1 block396W2 block396W3 block396W4 block396S1 block396S2 block396S3 block396S4

theorem block396LeftParamsCertificate_eq_true :
    block396LeftParamsCertificate = true := by
  native_decide

theorem block396_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block396LeftL : ℝ) (block396LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block396S1 : ℝ))
    (hy2ne : y ≠ (block396S2 : ℝ))
    (hy3ne : y ≠ (block396S3 : ℝ))
    (hy4ne : y ≠ (block396S4 : ℝ)) :
    0 < block396V y := by
  have hcert := block396LeftCertificate_eq_true
  unfold block396LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block396LeftBoxes) (lo := block396LeftL) (hi := block396LeftR)
    (w1 := block396W1) (w2 := block396W2) (w3 := block396W3) (w4 := block396W4)
    (s1 := block396S1) (s2 := block396S2) (s3 := block396S3) (s4 := block396S4)
    hboxes hcover block396LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block396RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block396RightChunk000 block396W1 block396W2 block396W3 block396W4 block396S1 block396S2 block396S3 block396S4

theorem block396RightChunk000ParamsCertificate_eq_true :
    block396RightChunk000ParamsCertificate = true := by
  native_decide

theorem block396_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block396RightChunk000L : ℝ) (block396RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block396S1 : ℝ))
    (hy2ne : y ≠ (block396S2 : ℝ))
    (hy3ne : y ≠ (block396S3 : ℝ))
    (hy4ne : y ≠ (block396S4 : ℝ)) :
    0 < block396V y := by
  have hcert := block396RightChunk000Certificate_eq_true
  unfold block396RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block396RightChunk000) (lo := block396RightChunk000L) (hi := block396RightChunk000R)
    (w1 := block396W1) (w2 := block396W2) (w3 := block396W3) (w4 := block396W4)
    (s1 := block396S1) (s2 := block396S2) (s3 := block396S3) (s4 := block396S4)
    hboxes hcover block396RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block396_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block396RightL : ℝ) (block396RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block396S1 : ℝ))
    (hy2ne : y ≠ (block396S2 : ℝ))
    (hy3ne : y ≠ (block396S3 : ℝ))
    (hy4ne : y ≠ (block396S4 : ℝ)) :
    0 < block396V y := by
  have hL : (block396RightChunk000L : ℝ) = (block396RightL : ℝ) := by
    norm_num [block396RightChunk000L, block396RightL]
  have hR : (block396RightChunk000R : ℝ) = (block396RightR : ℝ) := by
    norm_num [block396RightChunk000R, block396RightR]
  have hyc : y ∈ Icc (block396RightChunk000L : ℝ) (block396RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block396_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block396_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block396LeftL : ℝ) (block396LeftR : ℝ) →
    y ≠ 0 → y ≠ (block396S1 : ℝ) → y ≠ (block396S2 : ℝ) →
    y ≠ (block396S3 : ℝ) → y ≠ (block396S4 : ℝ) → 0 < block396V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block396RightL : ℝ) (block396RightR : ℝ) →
    y ≠ 0 → y ≠ (block396S1 : ℝ) → y ≠ (block396S2 : ℝ) →
    y ≠ (block396S3 : ℝ) → y ≠ (block396S4 : ℝ) → 0 < block396V y)

theorem block396_reallog_certificate_proof :
    block396_reallog_certificate := by
  exact ⟨block396_left_V_pos, block396_right_V_pos⟩

end Block396
end M1817475
end Erdos1038Lean
