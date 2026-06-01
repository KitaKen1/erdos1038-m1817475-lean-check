import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block549

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block549

open Set

def block549W1 : Rat := ((7774316206585541 : Rat) / 20000000000000000)
def block549W2 : Rat := (0 : Rat)
def block549W3 : Rat := ((2297118037201143 : Rat) / 5000000000000000)
def block549W4 : Rat := (0 : Rat)
def block549S1 : Rat := ((18174751 : Rat) / 10000000)
def block549S2 : Rat := ((511587 : Rat) / 200000)
def block549S3 : Rat := ((25880219482142857181 : Rat) / 10000000000000000000)
def block549S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block549V (y : ℝ) : ℝ :=
  ratPotential block549W1 block549W2 block549W3 block549W4 block549S1 block549S2 block549S3 block549S4 y

def block549LeftParamsCertificate : Bool :=
  allBoxesSameParams block549LeftBoxes block549W1 block549W2 block549W3 block549W4 block549S1 block549S2 block549S3 block549S4

theorem block549LeftParamsCertificate_eq_true :
    block549LeftParamsCertificate = true := by
  native_decide

theorem block549_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block549LeftL : ℝ) (block549LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block549S1 : ℝ))
    (hy2ne : y ≠ (block549S2 : ℝ))
    (hy3ne : y ≠ (block549S3 : ℝ))
    (hy4ne : y ≠ (block549S4 : ℝ)) :
    0 < block549V y := by
  have hcert := block549LeftCertificate_eq_true
  unfold block549LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block549LeftBoxes) (lo := block549LeftL) (hi := block549LeftR)
    (w1 := block549W1) (w2 := block549W2) (w3 := block549W3) (w4 := block549W4)
    (s1 := block549S1) (s2 := block549S2) (s3 := block549S3) (s4 := block549S4)
    hboxes hcover block549LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block549RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block549RightChunk000 block549W1 block549W2 block549W3 block549W4 block549S1 block549S2 block549S3 block549S4

theorem block549RightChunk000ParamsCertificate_eq_true :
    block549RightChunk000ParamsCertificate = true := by
  native_decide

theorem block549_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block549RightChunk000L : ℝ) (block549RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block549S1 : ℝ))
    (hy2ne : y ≠ (block549S2 : ℝ))
    (hy3ne : y ≠ (block549S3 : ℝ))
    (hy4ne : y ≠ (block549S4 : ℝ)) :
    0 < block549V y := by
  have hcert := block549RightChunk000Certificate_eq_true
  unfold block549RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block549RightChunk000) (lo := block549RightChunk000L) (hi := block549RightChunk000R)
    (w1 := block549W1) (w2 := block549W2) (w3 := block549W3) (w4 := block549W4)
    (s1 := block549S1) (s2 := block549S2) (s3 := block549S3) (s4 := block549S4)
    hboxes hcover block549RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block549_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block549RightL : ℝ) (block549RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block549S1 : ℝ))
    (hy2ne : y ≠ (block549S2 : ℝ))
    (hy3ne : y ≠ (block549S3 : ℝ))
    (hy4ne : y ≠ (block549S4 : ℝ)) :
    0 < block549V y := by
  have hL : (block549RightChunk000L : ℝ) = (block549RightL : ℝ) := by
    norm_num [block549RightChunk000L, block549RightL]
  have hR : (block549RightChunk000R : ℝ) = (block549RightR : ℝ) := by
    norm_num [block549RightChunk000R, block549RightR]
  have hyc : y ∈ Icc (block549RightChunk000L : ℝ) (block549RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block549_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block549_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block549LeftL : ℝ) (block549LeftR : ℝ) →
    y ≠ 0 → y ≠ (block549S1 : ℝ) → y ≠ (block549S2 : ℝ) →
    y ≠ (block549S3 : ℝ) → y ≠ (block549S4 : ℝ) → 0 < block549V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block549RightL : ℝ) (block549RightR : ℝ) →
    y ≠ 0 → y ≠ (block549S1 : ℝ) → y ≠ (block549S2 : ℝ) →
    y ≠ (block549S3 : ℝ) → y ≠ (block549S4 : ℝ) → 0 < block549V y)

theorem block549_reallog_certificate_proof :
    block549_reallog_certificate := by
  exact ⟨block549_left_V_pos, block549_right_V_pos⟩

end Block549
end M1817475
end Erdos1038Lean
