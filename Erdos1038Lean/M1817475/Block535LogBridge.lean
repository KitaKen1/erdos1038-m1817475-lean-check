import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block535

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block535

open Set

def block535W1 : Rat := ((125840368111617 : Rat) / 312500000000000)
def block535W2 : Rat := (0 : Rat)
def block535W3 : Rat := ((2270456790718763 : Rat) / 5000000000000000)
def block535W4 : Rat := (0 : Rat)
def block535S1 : Rat := ((18174751 : Rat) / 10000000)
def block535S2 : Rat := ((511587 : Rat) / 200000)
def block535S3 : Rat := ((129674784910714285893 : Rat) / 50000000000000000000)
def block535S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block535V (y : ℝ) : ℝ :=
  ratPotential block535W1 block535W2 block535W3 block535W4 block535S1 block535S2 block535S3 block535S4 y

def block535LeftParamsCertificate : Bool :=
  allBoxesSameParams block535LeftBoxes block535W1 block535W2 block535W3 block535W4 block535S1 block535S2 block535S3 block535S4

theorem block535LeftParamsCertificate_eq_true :
    block535LeftParamsCertificate = true := by
  native_decide

theorem block535_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block535LeftL : ℝ) (block535LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block535S1 : ℝ))
    (hy2ne : y ≠ (block535S2 : ℝ))
    (hy3ne : y ≠ (block535S3 : ℝ))
    (hy4ne : y ≠ (block535S4 : ℝ)) :
    0 < block535V y := by
  have hcert := block535LeftCertificate_eq_true
  unfold block535LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block535LeftBoxes) (lo := block535LeftL) (hi := block535LeftR)
    (w1 := block535W1) (w2 := block535W2) (w3 := block535W3) (w4 := block535W4)
    (s1 := block535S1) (s2 := block535S2) (s3 := block535S3) (s4 := block535S4)
    hboxes hcover block535LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block535RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block535RightChunk000 block535W1 block535W2 block535W3 block535W4 block535S1 block535S2 block535S3 block535S4

theorem block535RightChunk000ParamsCertificate_eq_true :
    block535RightChunk000ParamsCertificate = true := by
  native_decide

theorem block535_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block535RightChunk000L : ℝ) (block535RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block535S1 : ℝ))
    (hy2ne : y ≠ (block535S2 : ℝ))
    (hy3ne : y ≠ (block535S3 : ℝ))
    (hy4ne : y ≠ (block535S4 : ℝ)) :
    0 < block535V y := by
  have hcert := block535RightChunk000Certificate_eq_true
  unfold block535RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block535RightChunk000) (lo := block535RightChunk000L) (hi := block535RightChunk000R)
    (w1 := block535W1) (w2 := block535W2) (w3 := block535W3) (w4 := block535W4)
    (s1 := block535S1) (s2 := block535S2) (s3 := block535S3) (s4 := block535S4)
    hboxes hcover block535RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block535_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block535RightL : ℝ) (block535RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block535S1 : ℝ))
    (hy2ne : y ≠ (block535S2 : ℝ))
    (hy3ne : y ≠ (block535S3 : ℝ))
    (hy4ne : y ≠ (block535S4 : ℝ)) :
    0 < block535V y := by
  have hL : (block535RightChunk000L : ℝ) = (block535RightL : ℝ) := by
    norm_num [block535RightChunk000L, block535RightL]
  have hR : (block535RightChunk000R : ℝ) = (block535RightR : ℝ) := by
    norm_num [block535RightChunk000R, block535RightR]
  have hyc : y ∈ Icc (block535RightChunk000L : ℝ) (block535RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block535_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block535_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block535LeftL : ℝ) (block535LeftR : ℝ) →
    y ≠ 0 → y ≠ (block535S1 : ℝ) → y ≠ (block535S2 : ℝ) →
    y ≠ (block535S3 : ℝ) → y ≠ (block535S4 : ℝ) → 0 < block535V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block535RightL : ℝ) (block535RightR : ℝ) →
    y ≠ 0 → y ≠ (block535S1 : ℝ) → y ≠ (block535S2 : ℝ) →
    y ≠ (block535S3 : ℝ) → y ≠ (block535S4 : ℝ) → 0 < block535V y)

theorem block535_reallog_certificate_proof :
    block535_reallog_certificate := by
  exact ⟨block535_left_V_pos, block535_right_V_pos⟩

end Block535
end M1817475
end Erdos1038Lean
