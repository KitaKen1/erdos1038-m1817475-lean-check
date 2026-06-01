import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block511

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block511

open Set

def block511W1 : Rat := ((2166121136880221 : Rat) / 5000000000000000)
def block511W2 : Rat := (0 : Rat)
def block511W3 : Rat := ((2192005073546529 : Rat) / 5000000000000000)
def block511W4 : Rat := ((2544125740123163 : Rat) / 500000000000000000)
def block511S1 : Rat := ((18174751 : Rat) / 10000000)
def block511S2 : Rat := ((511587 : Rat) / 200000)
def block511S3 : Rat := ((130143963482142857301 : Rat) / 50000000000000000000)
def block511S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block511V (y : ℝ) : ℝ :=
  ratPotential block511W1 block511W2 block511W3 block511W4 block511S1 block511S2 block511S3 block511S4 y

def block511LeftParamsCertificate : Bool :=
  allBoxesSameParams block511LeftBoxes block511W1 block511W2 block511W3 block511W4 block511S1 block511S2 block511S3 block511S4

theorem block511LeftParamsCertificate_eq_true :
    block511LeftParamsCertificate = true := by
  native_decide

theorem block511_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block511LeftL : ℝ) (block511LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block511S1 : ℝ))
    (hy2ne : y ≠ (block511S2 : ℝ))
    (hy3ne : y ≠ (block511S3 : ℝ))
    (hy4ne : y ≠ (block511S4 : ℝ)) :
    0 < block511V y := by
  have hcert := block511LeftCertificate_eq_true
  unfold block511LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block511LeftBoxes) (lo := block511LeftL) (hi := block511LeftR)
    (w1 := block511W1) (w2 := block511W2) (w3 := block511W3) (w4 := block511W4)
    (s1 := block511S1) (s2 := block511S2) (s3 := block511S3) (s4 := block511S4)
    hboxes hcover block511LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block511RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block511RightChunk000 block511W1 block511W2 block511W3 block511W4 block511S1 block511S2 block511S3 block511S4

theorem block511RightChunk000ParamsCertificate_eq_true :
    block511RightChunk000ParamsCertificate = true := by
  native_decide

theorem block511_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block511RightChunk000L : ℝ) (block511RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block511S1 : ℝ))
    (hy2ne : y ≠ (block511S2 : ℝ))
    (hy3ne : y ≠ (block511S3 : ℝ))
    (hy4ne : y ≠ (block511S4 : ℝ)) :
    0 < block511V y := by
  have hcert := block511RightChunk000Certificate_eq_true
  unfold block511RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block511RightChunk000) (lo := block511RightChunk000L) (hi := block511RightChunk000R)
    (w1 := block511W1) (w2 := block511W2) (w3 := block511W3) (w4 := block511W4)
    (s1 := block511S1) (s2 := block511S2) (s3 := block511S3) (s4 := block511S4)
    hboxes hcover block511RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block511_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block511RightL : ℝ) (block511RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block511S1 : ℝ))
    (hy2ne : y ≠ (block511S2 : ℝ))
    (hy3ne : y ≠ (block511S3 : ℝ))
    (hy4ne : y ≠ (block511S4 : ℝ)) :
    0 < block511V y := by
  have hL : (block511RightChunk000L : ℝ) = (block511RightL : ℝ) := by
    norm_num [block511RightChunk000L, block511RightL]
  have hR : (block511RightChunk000R : ℝ) = (block511RightR : ℝ) := by
    norm_num [block511RightChunk000R, block511RightR]
  have hyc : y ∈ Icc (block511RightChunk000L : ℝ) (block511RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block511_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block511_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block511LeftL : ℝ) (block511LeftR : ℝ) →
    y ≠ 0 → y ≠ (block511S1 : ℝ) → y ≠ (block511S2 : ℝ) →
    y ≠ (block511S3 : ℝ) → y ≠ (block511S4 : ℝ) → 0 < block511V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block511RightL : ℝ) (block511RightR : ℝ) →
    y ≠ 0 → y ≠ (block511S1 : ℝ) → y ≠ (block511S2 : ℝ) →
    y ≠ (block511S3 : ℝ) → y ≠ (block511S4 : ℝ) → 0 < block511V y)

theorem block511_reallog_certificate_proof :
    block511_reallog_certificate := by
  exact ⟨block511_left_V_pos, block511_right_V_pos⟩

end Block511
end M1817475
end Erdos1038Lean
