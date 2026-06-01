import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block371

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block371

open Set

def block371W1 : Rat := ((4328520317754733 : Rat) / 5000000000000000)
def block371W2 : Rat := ((587901964035271 : Rat) / 12500000000000000)
def block371W3 : Rat := ((7764853880545483 : Rat) / 50000000000000000)
def block371W4 : Rat := ((3493168885887861 : Rat) / 25000000000000000)
def block371S1 : Rat := ((18174751 : Rat) / 10000000)
def block371S2 : Rat := ((511587 : Rat) / 200000)
def block371S3 : Rat := ((132880838482142857181 : Rat) / 50000000000000000000)
def block371S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block371V (y : ℝ) : ℝ :=
  ratPotential block371W1 block371W2 block371W3 block371W4 block371S1 block371S2 block371S3 block371S4 y

def block371LeftParamsCertificate : Bool :=
  allBoxesSameParams block371LeftBoxes block371W1 block371W2 block371W3 block371W4 block371S1 block371S2 block371S3 block371S4

theorem block371LeftParamsCertificate_eq_true :
    block371LeftParamsCertificate = true := by
  native_decide

theorem block371_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block371LeftL : ℝ) (block371LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block371S1 : ℝ))
    (hy2ne : y ≠ (block371S2 : ℝ))
    (hy3ne : y ≠ (block371S3 : ℝ))
    (hy4ne : y ≠ (block371S4 : ℝ)) :
    0 < block371V y := by
  have hcert := block371LeftCertificate_eq_true
  unfold block371LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block371LeftBoxes) (lo := block371LeftL) (hi := block371LeftR)
    (w1 := block371W1) (w2 := block371W2) (w3 := block371W3) (w4 := block371W4)
    (s1 := block371S1) (s2 := block371S2) (s3 := block371S3) (s4 := block371S4)
    hboxes hcover block371LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block371RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block371RightChunk000 block371W1 block371W2 block371W3 block371W4 block371S1 block371S2 block371S3 block371S4

theorem block371RightChunk000ParamsCertificate_eq_true :
    block371RightChunk000ParamsCertificate = true := by
  native_decide

theorem block371_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block371RightChunk000L : ℝ) (block371RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block371S1 : ℝ))
    (hy2ne : y ≠ (block371S2 : ℝ))
    (hy3ne : y ≠ (block371S3 : ℝ))
    (hy4ne : y ≠ (block371S4 : ℝ)) :
    0 < block371V y := by
  have hcert := block371RightChunk000Certificate_eq_true
  unfold block371RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block371RightChunk000) (lo := block371RightChunk000L) (hi := block371RightChunk000R)
    (w1 := block371W1) (w2 := block371W2) (w3 := block371W3) (w4 := block371W4)
    (s1 := block371S1) (s2 := block371S2) (s3 := block371S3) (s4 := block371S4)
    hboxes hcover block371RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block371_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block371RightL : ℝ) (block371RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block371S1 : ℝ))
    (hy2ne : y ≠ (block371S2 : ℝ))
    (hy3ne : y ≠ (block371S3 : ℝ))
    (hy4ne : y ≠ (block371S4 : ℝ)) :
    0 < block371V y := by
  have hL : (block371RightChunk000L : ℝ) = (block371RightL : ℝ) := by
    norm_num [block371RightChunk000L, block371RightL]
  have hR : (block371RightChunk000R : ℝ) = (block371RightR : ℝ) := by
    norm_num [block371RightChunk000R, block371RightR]
  have hyc : y ∈ Icc (block371RightChunk000L : ℝ) (block371RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block371_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block371_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block371LeftL : ℝ) (block371LeftR : ℝ) →
    y ≠ 0 → y ≠ (block371S1 : ℝ) → y ≠ (block371S2 : ℝ) →
    y ≠ (block371S3 : ℝ) → y ≠ (block371S4 : ℝ) → 0 < block371V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block371RightL : ℝ) (block371RightR : ℝ) →
    y ≠ 0 → y ≠ (block371S1 : ℝ) → y ≠ (block371S2 : ℝ) →
    y ≠ (block371S3 : ℝ) → y ≠ (block371S4 : ℝ) → 0 < block371V y)

theorem block371_reallog_certificate_proof :
    block371_reallog_certificate := by
  exact ⟨block371_left_V_pos, block371_right_V_pos⟩

end Block371
end M1817475
end Erdos1038Lean
