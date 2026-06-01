import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block316

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block316

open Set

def block316W1 : Rat := ((595594308695337 : Rat) / 625000000000000)
def block316W2 : Rat := ((3198386925050127 : Rat) / 50000000000000000)
def block316W3 : Rat := ((2563691324952699 : Rat) / 10000000000000000)
def block316W4 : Rat := (0 : Rat)
def block316S1 : Rat := ((18174751 : Rat) / 10000000)
def block316S2 : Rat := ((511587 : Rat) / 200000)
def block316S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block316S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block316V (y : ℝ) : ℝ :=
  ratPotential block316W1 block316W2 block316W3 block316W4 block316S1 block316S2 block316S3 block316S4 y

def block316LeftParamsCertificate : Bool :=
  allBoxesSameParams block316LeftBoxes block316W1 block316W2 block316W3 block316W4 block316S1 block316S2 block316S3 block316S4

theorem block316LeftParamsCertificate_eq_true :
    block316LeftParamsCertificate = true := by
  native_decide

theorem block316_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block316LeftL : ℝ) (block316LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block316S1 : ℝ))
    (hy2ne : y ≠ (block316S2 : ℝ))
    (hy3ne : y ≠ (block316S3 : ℝ))
    (hy4ne : y ≠ (block316S4 : ℝ)) :
    0 < block316V y := by
  have hcert := block316LeftCertificate_eq_true
  unfold block316LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block316LeftBoxes) (lo := block316LeftL) (hi := block316LeftR)
    (w1 := block316W1) (w2 := block316W2) (w3 := block316W3) (w4 := block316W4)
    (s1 := block316S1) (s2 := block316S2) (s3 := block316S3) (s4 := block316S4)
    hboxes hcover block316LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block316RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block316RightChunk000 block316W1 block316W2 block316W3 block316W4 block316S1 block316S2 block316S3 block316S4

theorem block316RightChunk000ParamsCertificate_eq_true :
    block316RightChunk000ParamsCertificate = true := by
  native_decide

theorem block316_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block316RightChunk000L : ℝ) (block316RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block316S1 : ℝ))
    (hy2ne : y ≠ (block316S2 : ℝ))
    (hy3ne : y ≠ (block316S3 : ℝ))
    (hy4ne : y ≠ (block316S4 : ℝ)) :
    0 < block316V y := by
  have hcert := block316RightChunk000Certificate_eq_true
  unfold block316RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block316RightChunk000) (lo := block316RightChunk000L) (hi := block316RightChunk000R)
    (w1 := block316W1) (w2 := block316W2) (w3 := block316W3) (w4 := block316W4)
    (s1 := block316S1) (s2 := block316S2) (s3 := block316S3) (s4 := block316S4)
    hboxes hcover block316RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block316_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block316RightL : ℝ) (block316RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block316S1 : ℝ))
    (hy2ne : y ≠ (block316S2 : ℝ))
    (hy3ne : y ≠ (block316S3 : ℝ))
    (hy4ne : y ≠ (block316S4 : ℝ)) :
    0 < block316V y := by
  have hL : (block316RightChunk000L : ℝ) = (block316RightL : ℝ) := by
    norm_num [block316RightChunk000L, block316RightL]
  have hR : (block316RightChunk000R : ℝ) = (block316RightR : ℝ) := by
    norm_num [block316RightChunk000R, block316RightR]
  have hyc : y ∈ Icc (block316RightChunk000L : ℝ) (block316RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block316_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block316_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block316LeftL : ℝ) (block316LeftR : ℝ) →
    y ≠ 0 → y ≠ (block316S1 : ℝ) → y ≠ (block316S2 : ℝ) →
    y ≠ (block316S3 : ℝ) → y ≠ (block316S4 : ℝ) → 0 < block316V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block316RightL : ℝ) (block316RightR : ℝ) →
    y ≠ 0 → y ≠ (block316S1 : ℝ) → y ≠ (block316S2 : ℝ) →
    y ≠ (block316S3 : ℝ) → y ≠ (block316S4 : ℝ) → 0 < block316V y)

theorem block316_reallog_certificate_proof :
    block316_reallog_certificate := by
  exact ⟨block316_left_V_pos, block316_right_V_pos⟩

end Block316
end M1817475
end Erdos1038Lean
