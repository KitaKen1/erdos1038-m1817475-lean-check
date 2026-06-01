import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block426

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block426

open Set

def block426W1 : Rat := ((668312718632457 : Rat) / 1000000000000000)
def block426W2 : Rat := (0 : Rat)
def block426W3 : Rat := ((758535436199429 : Rat) / 2500000000000000)
def block426W4 : Rat := ((163805436099913 : Rat) / 2000000000000000)
def block426S1 : Rat := ((18174751 : Rat) / 10000000)
def block426S2 : Rat := ((511587 : Rat) / 200000)
def block426S3 : Rat := ((131805637589285714371 : Rat) / 50000000000000000000)
def block426S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block426V (y : ℝ) : ℝ :=
  ratPotential block426W1 block426W2 block426W3 block426W4 block426S1 block426S2 block426S3 block426S4 y

def block426LeftParamsCertificate : Bool :=
  allBoxesSameParams block426LeftBoxes block426W1 block426W2 block426W3 block426W4 block426S1 block426S2 block426S3 block426S4

theorem block426LeftParamsCertificate_eq_true :
    block426LeftParamsCertificate = true := by
  native_decide

theorem block426_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block426LeftL : ℝ) (block426LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block426S1 : ℝ))
    (hy2ne : y ≠ (block426S2 : ℝ))
    (hy3ne : y ≠ (block426S3 : ℝ))
    (hy4ne : y ≠ (block426S4 : ℝ)) :
    0 < block426V y := by
  have hcert := block426LeftCertificate_eq_true
  unfold block426LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block426LeftBoxes) (lo := block426LeftL) (hi := block426LeftR)
    (w1 := block426W1) (w2 := block426W2) (w3 := block426W3) (w4 := block426W4)
    (s1 := block426S1) (s2 := block426S2) (s3 := block426S3) (s4 := block426S4)
    hboxes hcover block426LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block426RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block426RightChunk000 block426W1 block426W2 block426W3 block426W4 block426S1 block426S2 block426S3 block426S4

theorem block426RightChunk000ParamsCertificate_eq_true :
    block426RightChunk000ParamsCertificate = true := by
  native_decide

theorem block426_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block426RightChunk000L : ℝ) (block426RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block426S1 : ℝ))
    (hy2ne : y ≠ (block426S2 : ℝ))
    (hy3ne : y ≠ (block426S3 : ℝ))
    (hy4ne : y ≠ (block426S4 : ℝ)) :
    0 < block426V y := by
  have hcert := block426RightChunk000Certificate_eq_true
  unfold block426RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block426RightChunk000) (lo := block426RightChunk000L) (hi := block426RightChunk000R)
    (w1 := block426W1) (w2 := block426W2) (w3 := block426W3) (w4 := block426W4)
    (s1 := block426S1) (s2 := block426S2) (s3 := block426S3) (s4 := block426S4)
    hboxes hcover block426RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block426_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block426RightL : ℝ) (block426RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block426S1 : ℝ))
    (hy2ne : y ≠ (block426S2 : ℝ))
    (hy3ne : y ≠ (block426S3 : ℝ))
    (hy4ne : y ≠ (block426S4 : ℝ)) :
    0 < block426V y := by
  have hL : (block426RightChunk000L : ℝ) = (block426RightL : ℝ) := by
    norm_num [block426RightChunk000L, block426RightL]
  have hR : (block426RightChunk000R : ℝ) = (block426RightR : ℝ) := by
    norm_num [block426RightChunk000R, block426RightR]
  have hyc : y ∈ Icc (block426RightChunk000L : ℝ) (block426RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block426_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block426_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block426LeftL : ℝ) (block426LeftR : ℝ) →
    y ≠ 0 → y ≠ (block426S1 : ℝ) → y ≠ (block426S2 : ℝ) →
    y ≠ (block426S3 : ℝ) → y ≠ (block426S4 : ℝ) → 0 < block426V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block426RightL : ℝ) (block426RightR : ℝ) →
    y ≠ 0 → y ≠ (block426S1 : ℝ) → y ≠ (block426S2 : ℝ) →
    y ≠ (block426S3 : ℝ) → y ≠ (block426S4 : ℝ) → 0 < block426V y)

theorem block426_reallog_certificate_proof :
    block426_reallog_certificate := by
  exact ⟨block426_left_V_pos, block426_right_V_pos⟩

end Block426
end M1817475
end Erdos1038Lean
