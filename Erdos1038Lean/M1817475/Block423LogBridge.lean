import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block423

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block423

open Set

def block423W1 : Rat := ((1355236900436627 : Rat) / 2000000000000000)
def block423W2 : Rat := (0 : Rat)
def block423W3 : Rat := ((2999759219855843 : Rat) / 10000000000000000)
def block423W4 : Rat := ((4176169748259023 : Rat) / 50000000000000000)
def block423S1 : Rat := ((18174751 : Rat) / 10000000)
def block423S2 : Rat := ((511587 : Rat) / 200000)
def block423S3 : Rat := ((131864284910714285797 : Rat) / 50000000000000000000)
def block423S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block423V (y : ℝ) : ℝ :=
  ratPotential block423W1 block423W2 block423W3 block423W4 block423S1 block423S2 block423S3 block423S4 y

def block423LeftParamsCertificate : Bool :=
  allBoxesSameParams block423LeftBoxes block423W1 block423W2 block423W3 block423W4 block423S1 block423S2 block423S3 block423S4

theorem block423LeftParamsCertificate_eq_true :
    block423LeftParamsCertificate = true := by
  native_decide

theorem block423_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block423LeftL : ℝ) (block423LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block423S1 : ℝ))
    (hy2ne : y ≠ (block423S2 : ℝ))
    (hy3ne : y ≠ (block423S3 : ℝ))
    (hy4ne : y ≠ (block423S4 : ℝ)) :
    0 < block423V y := by
  have hcert := block423LeftCertificate_eq_true
  unfold block423LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block423LeftBoxes) (lo := block423LeftL) (hi := block423LeftR)
    (w1 := block423W1) (w2 := block423W2) (w3 := block423W3) (w4 := block423W4)
    (s1 := block423S1) (s2 := block423S2) (s3 := block423S3) (s4 := block423S4)
    hboxes hcover block423LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block423RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block423RightChunk000 block423W1 block423W2 block423W3 block423W4 block423S1 block423S2 block423S3 block423S4

theorem block423RightChunk000ParamsCertificate_eq_true :
    block423RightChunk000ParamsCertificate = true := by
  native_decide

theorem block423_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block423RightChunk000L : ℝ) (block423RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block423S1 : ℝ))
    (hy2ne : y ≠ (block423S2 : ℝ))
    (hy3ne : y ≠ (block423S3 : ℝ))
    (hy4ne : y ≠ (block423S4 : ℝ)) :
    0 < block423V y := by
  have hcert := block423RightChunk000Certificate_eq_true
  unfold block423RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block423RightChunk000) (lo := block423RightChunk000L) (hi := block423RightChunk000R)
    (w1 := block423W1) (w2 := block423W2) (w3 := block423W3) (w4 := block423W4)
    (s1 := block423S1) (s2 := block423S2) (s3 := block423S3) (s4 := block423S4)
    hboxes hcover block423RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block423_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block423RightL : ℝ) (block423RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block423S1 : ℝ))
    (hy2ne : y ≠ (block423S2 : ℝ))
    (hy3ne : y ≠ (block423S3 : ℝ))
    (hy4ne : y ≠ (block423S4 : ℝ)) :
    0 < block423V y := by
  have hL : (block423RightChunk000L : ℝ) = (block423RightL : ℝ) := by
    norm_num [block423RightChunk000L, block423RightL]
  have hR : (block423RightChunk000R : ℝ) = (block423RightR : ℝ) := by
    norm_num [block423RightChunk000R, block423RightR]
  have hyc : y ∈ Icc (block423RightChunk000L : ℝ) (block423RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block423_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block423_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block423LeftL : ℝ) (block423LeftR : ℝ) →
    y ≠ 0 → y ≠ (block423S1 : ℝ) → y ≠ (block423S2 : ℝ) →
    y ≠ (block423S3 : ℝ) → y ≠ (block423S4 : ℝ) → 0 < block423V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block423RightL : ℝ) (block423RightR : ℝ) →
    y ≠ 0 → y ≠ (block423S1 : ℝ) → y ≠ (block423S2 : ℝ) →
    y ≠ (block423S3 : ℝ) → y ≠ (block423S4 : ℝ) → 0 < block423V y)

theorem block423_reallog_certificate_proof :
    block423_reallog_certificate := by
  exact ⟨block423_left_V_pos, block423_right_V_pos⟩

end Block423
end M1817475
end Erdos1038Lean
