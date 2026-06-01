import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block422

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block422

open Set

def block422W1 : Rat := ((3401894918639373 : Rat) / 5000000000000000)
def block422W2 : Rat := (0 : Rat)
def block422W3 : Rat := ((299088441311331 : Rat) / 1000000000000000)
def block422W4 : Rat := ((838726481300847 : Rat) / 10000000000000000)
def block422S1 : Rat := ((18174751 : Rat) / 10000000)
def block422S2 : Rat := ((511587 : Rat) / 200000)
def block422S3 : Rat := ((131883834017857142939 : Rat) / 50000000000000000000)
def block422S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block422V (y : ℝ) : ℝ :=
  ratPotential block422W1 block422W2 block422W3 block422W4 block422S1 block422S2 block422S3 block422S4 y

def block422LeftParamsCertificate : Bool :=
  allBoxesSameParams block422LeftBoxes block422W1 block422W2 block422W3 block422W4 block422S1 block422S2 block422S3 block422S4

theorem block422LeftParamsCertificate_eq_true :
    block422LeftParamsCertificate = true := by
  native_decide

theorem block422_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block422LeftL : ℝ) (block422LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block422S1 : ℝ))
    (hy2ne : y ≠ (block422S2 : ℝ))
    (hy3ne : y ≠ (block422S3 : ℝ))
    (hy4ne : y ≠ (block422S4 : ℝ)) :
    0 < block422V y := by
  have hcert := block422LeftCertificate_eq_true
  unfold block422LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block422LeftBoxes) (lo := block422LeftL) (hi := block422LeftR)
    (w1 := block422W1) (w2 := block422W2) (w3 := block422W3) (w4 := block422W4)
    (s1 := block422S1) (s2 := block422S2) (s3 := block422S3) (s4 := block422S4)
    hboxes hcover block422LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block422RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block422RightChunk000 block422W1 block422W2 block422W3 block422W4 block422S1 block422S2 block422S3 block422S4

theorem block422RightChunk000ParamsCertificate_eq_true :
    block422RightChunk000ParamsCertificate = true := by
  native_decide

theorem block422_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block422RightChunk000L : ℝ) (block422RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block422S1 : ℝ))
    (hy2ne : y ≠ (block422S2 : ℝ))
    (hy3ne : y ≠ (block422S3 : ℝ))
    (hy4ne : y ≠ (block422S4 : ℝ)) :
    0 < block422V y := by
  have hcert := block422RightChunk000Certificate_eq_true
  unfold block422RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block422RightChunk000) (lo := block422RightChunk000L) (hi := block422RightChunk000R)
    (w1 := block422W1) (w2 := block422W2) (w3 := block422W3) (w4 := block422W4)
    (s1 := block422S1) (s2 := block422S2) (s3 := block422S3) (s4 := block422S4)
    hboxes hcover block422RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block422_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block422RightL : ℝ) (block422RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block422S1 : ℝ))
    (hy2ne : y ≠ (block422S2 : ℝ))
    (hy3ne : y ≠ (block422S3 : ℝ))
    (hy4ne : y ≠ (block422S4 : ℝ)) :
    0 < block422V y := by
  have hL : (block422RightChunk000L : ℝ) = (block422RightL : ℝ) := by
    norm_num [block422RightChunk000L, block422RightL]
  have hR : (block422RightChunk000R : ℝ) = (block422RightR : ℝ) := by
    norm_num [block422RightChunk000R, block422RightR]
  have hyc : y ∈ Icc (block422RightChunk000L : ℝ) (block422RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block422_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block422_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block422LeftL : ℝ) (block422LeftR : ℝ) →
    y ≠ 0 → y ≠ (block422S1 : ℝ) → y ≠ (block422S2 : ℝ) →
    y ≠ (block422S3 : ℝ) → y ≠ (block422S4 : ℝ) → 0 < block422V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block422RightL : ℝ) (block422RightR : ℝ) →
    y ≠ 0 → y ≠ (block422S1 : ℝ) → y ≠ (block422S2 : ℝ) →
    y ≠ (block422S3 : ℝ) → y ≠ (block422S4 : ℝ) → 0 < block422V y)

theorem block422_reallog_certificate_proof :
    block422_reallog_certificate := by
  exact ⟨block422_left_V_pos, block422_right_V_pos⟩

end Block422
end M1817475
end Erdos1038Lean
