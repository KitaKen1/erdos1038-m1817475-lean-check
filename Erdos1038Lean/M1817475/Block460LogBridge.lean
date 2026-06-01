import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block460

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block460

open Set

def block460W1 : Rat := ((5692333146199 : Rat) / 10000000000000)
def block460W2 : Rat := (0 : Rat)
def block460W3 : Rat := ((17344963297627647 : Rat) / 50000000000000000)
def block460W4 : Rat := ((597427466475837 : Rat) / 10000000000000000)
def block460S1 : Rat := ((18174751 : Rat) / 10000000)
def block460S2 : Rat := ((511587 : Rat) / 200000)
def block460S3 : Rat := ((131140967946428571543 : Rat) / 50000000000000000000)
def block460S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block460V (y : ℝ) : ℝ :=
  ratPotential block460W1 block460W2 block460W3 block460W4 block460S1 block460S2 block460S3 block460S4 y

def block460LeftParamsCertificate : Bool :=
  allBoxesSameParams block460LeftBoxes block460W1 block460W2 block460W3 block460W4 block460S1 block460S2 block460S3 block460S4

theorem block460LeftParamsCertificate_eq_true :
    block460LeftParamsCertificate = true := by
  native_decide

theorem block460_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block460LeftL : ℝ) (block460LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block460S1 : ℝ))
    (hy2ne : y ≠ (block460S2 : ℝ))
    (hy3ne : y ≠ (block460S3 : ℝ))
    (hy4ne : y ≠ (block460S4 : ℝ)) :
    0 < block460V y := by
  have hcert := block460LeftCertificate_eq_true
  unfold block460LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block460LeftBoxes) (lo := block460LeftL) (hi := block460LeftR)
    (w1 := block460W1) (w2 := block460W2) (w3 := block460W3) (w4 := block460W4)
    (s1 := block460S1) (s2 := block460S2) (s3 := block460S3) (s4 := block460S4)
    hboxes hcover block460LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block460RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block460RightChunk000 block460W1 block460W2 block460W3 block460W4 block460S1 block460S2 block460S3 block460S4

theorem block460RightChunk000ParamsCertificate_eq_true :
    block460RightChunk000ParamsCertificate = true := by
  native_decide

theorem block460_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block460RightChunk000L : ℝ) (block460RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block460S1 : ℝ))
    (hy2ne : y ≠ (block460S2 : ℝ))
    (hy3ne : y ≠ (block460S3 : ℝ))
    (hy4ne : y ≠ (block460S4 : ℝ)) :
    0 < block460V y := by
  have hcert := block460RightChunk000Certificate_eq_true
  unfold block460RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block460RightChunk000) (lo := block460RightChunk000L) (hi := block460RightChunk000R)
    (w1 := block460W1) (w2 := block460W2) (w3 := block460W3) (w4 := block460W4)
    (s1 := block460S1) (s2 := block460S2) (s3 := block460S3) (s4 := block460S4)
    hboxes hcover block460RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block460_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block460RightL : ℝ) (block460RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block460S1 : ℝ))
    (hy2ne : y ≠ (block460S2 : ℝ))
    (hy3ne : y ≠ (block460S3 : ℝ))
    (hy4ne : y ≠ (block460S4 : ℝ)) :
    0 < block460V y := by
  have hL : (block460RightChunk000L : ℝ) = (block460RightL : ℝ) := by
    norm_num [block460RightChunk000L, block460RightL]
  have hR : (block460RightChunk000R : ℝ) = (block460RightR : ℝ) := by
    norm_num [block460RightChunk000R, block460RightR]
  have hyc : y ∈ Icc (block460RightChunk000L : ℝ) (block460RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block460_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block460_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block460LeftL : ℝ) (block460LeftR : ℝ) →
    y ≠ 0 → y ≠ (block460S1 : ℝ) → y ≠ (block460S2 : ℝ) →
    y ≠ (block460S3 : ℝ) → y ≠ (block460S4 : ℝ) → 0 < block460V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block460RightL : ℝ) (block460RightR : ℝ) →
    y ≠ 0 → y ≠ (block460S1 : ℝ) → y ≠ (block460S2 : ℝ) →
    y ≠ (block460S3 : ℝ) → y ≠ (block460S4 : ℝ) → 0 < block460V y)

theorem block460_reallog_certificate_proof :
    block460_reallog_certificate := by
  exact ⟨block460_left_V_pos, block460_right_V_pos⟩

end Block460
end M1817475
end Erdos1038Lean
