import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block160

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block160

open Set

def block160W1 : Rat := ((1862363023132751 : Rat) / 1000000000000000)
def block160W2 : Rat := (0 : Rat)
def block160W3 : Rat := ((403585754856923 : Rat) / 2500000000000000)
def block160W4 : Rat := ((5286136064751453 : Rat) / 50000000000000000)
def block160S1 : Rat := ((18174751 : Rat) / 10000000)
def block160S2 : Rat := ((511587 : Rat) / 200000)
def block160S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block160S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block160V (y : ℝ) : ℝ :=
  ratPotential block160W1 block160W2 block160W3 block160W4 block160S1 block160S2 block160S3 block160S4 y

def block160LeftParamsCertificate : Bool :=
  allBoxesSameParams block160LeftBoxes block160W1 block160W2 block160W3 block160W4 block160S1 block160S2 block160S3 block160S4

theorem block160LeftParamsCertificate_eq_true :
    block160LeftParamsCertificate = true := by
  native_decide

theorem block160_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block160LeftL : ℝ) (block160LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block160S1 : ℝ))
    (hy2ne : y ≠ (block160S2 : ℝ))
    (hy3ne : y ≠ (block160S3 : ℝ))
    (hy4ne : y ≠ (block160S4 : ℝ)) :
    0 < block160V y := by
  have hcert := block160LeftCertificate_eq_true
  unfold block160LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block160LeftBoxes) (lo := block160LeftL) (hi := block160LeftR)
    (w1 := block160W1) (w2 := block160W2) (w3 := block160W3) (w4 := block160W4)
    (s1 := block160S1) (s2 := block160S2) (s3 := block160S3) (s4 := block160S4)
    hboxes hcover block160LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block160RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block160RightChunk000 block160W1 block160W2 block160W3 block160W4 block160S1 block160S2 block160S3 block160S4

theorem block160RightChunk000ParamsCertificate_eq_true :
    block160RightChunk000ParamsCertificate = true := by
  native_decide

theorem block160_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block160RightChunk000L : ℝ) (block160RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block160S1 : ℝ))
    (hy2ne : y ≠ (block160S2 : ℝ))
    (hy3ne : y ≠ (block160S3 : ℝ))
    (hy4ne : y ≠ (block160S4 : ℝ)) :
    0 < block160V y := by
  have hcert := block160RightChunk000Certificate_eq_true
  unfold block160RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block160RightChunk000) (lo := block160RightChunk000L) (hi := block160RightChunk000R)
    (w1 := block160W1) (w2 := block160W2) (w3 := block160W3) (w4 := block160W4)
    (s1 := block160S1) (s2 := block160S2) (s3 := block160S3) (s4 := block160S4)
    hboxes hcover block160RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block160_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block160RightL : ℝ) (block160RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block160S1 : ℝ))
    (hy2ne : y ≠ (block160S2 : ℝ))
    (hy3ne : y ≠ (block160S3 : ℝ))
    (hy4ne : y ≠ (block160S4 : ℝ)) :
    0 < block160V y := by
  have hL : (block160RightChunk000L : ℝ) = (block160RightL : ℝ) := by
    norm_num [block160RightChunk000L, block160RightL]
  have hR : (block160RightChunk000R : ℝ) = (block160RightR : ℝ) := by
    norm_num [block160RightChunk000R, block160RightR]
  have hyc : y ∈ Icc (block160RightChunk000L : ℝ) (block160RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block160_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block160_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block160LeftL : ℝ) (block160LeftR : ℝ) →
    y ≠ 0 → y ≠ (block160S1 : ℝ) → y ≠ (block160S2 : ℝ) →
    y ≠ (block160S3 : ℝ) → y ≠ (block160S4 : ℝ) → 0 < block160V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block160RightL : ℝ) (block160RightR : ℝ) →
    y ≠ 0 → y ≠ (block160S1 : ℝ) → y ≠ (block160S2 : ℝ) →
    y ≠ (block160S3 : ℝ) → y ≠ (block160S4 : ℝ) → 0 < block160V y)

theorem block160_reallog_certificate_proof :
    block160_reallog_certificate := by
  exact ⟨block160_left_V_pos, block160_right_V_pos⟩

end Block160
end M1817475
end Erdos1038Lean
