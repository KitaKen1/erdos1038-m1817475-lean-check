import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block519

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block519

open Set

def block519W1 : Rat := ((4193989008488053 : Rat) / 10000000000000000)
def block519W2 : Rat := (0 : Rat)
def block519W3 : Rat := ((4480264595681997 : Rat) / 10000000000000000)
def block519W4 : Rat := (0 : Rat)
def block519S1 : Rat := ((18174751 : Rat) / 10000000)
def block519S2 : Rat := ((511587 : Rat) / 200000)
def block519S3 : Rat := ((25997514125000000033 : Rat) / 10000000000000000000)
def block519S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block519V (y : ℝ) : ℝ :=
  ratPotential block519W1 block519W2 block519W3 block519W4 block519S1 block519S2 block519S3 block519S4 y

def block519LeftParamsCertificate : Bool :=
  allBoxesSameParams block519LeftBoxes block519W1 block519W2 block519W3 block519W4 block519S1 block519S2 block519S3 block519S4

theorem block519LeftParamsCertificate_eq_true :
    block519LeftParamsCertificate = true := by
  native_decide

theorem block519_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block519LeftL : ℝ) (block519LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block519S1 : ℝ))
    (hy2ne : y ≠ (block519S2 : ℝ))
    (hy3ne : y ≠ (block519S3 : ℝ))
    (hy4ne : y ≠ (block519S4 : ℝ)) :
    0 < block519V y := by
  have hcert := block519LeftCertificate_eq_true
  unfold block519LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block519LeftBoxes) (lo := block519LeftL) (hi := block519LeftR)
    (w1 := block519W1) (w2 := block519W2) (w3 := block519W3) (w4 := block519W4)
    (s1 := block519S1) (s2 := block519S2) (s3 := block519S3) (s4 := block519S4)
    hboxes hcover block519LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block519RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block519RightChunk000 block519W1 block519W2 block519W3 block519W4 block519S1 block519S2 block519S3 block519S4

theorem block519RightChunk000ParamsCertificate_eq_true :
    block519RightChunk000ParamsCertificate = true := by
  native_decide

theorem block519_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block519RightChunk000L : ℝ) (block519RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block519S1 : ℝ))
    (hy2ne : y ≠ (block519S2 : ℝ))
    (hy3ne : y ≠ (block519S3 : ℝ))
    (hy4ne : y ≠ (block519S4 : ℝ)) :
    0 < block519V y := by
  have hcert := block519RightChunk000Certificate_eq_true
  unfold block519RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block519RightChunk000) (lo := block519RightChunk000L) (hi := block519RightChunk000R)
    (w1 := block519W1) (w2 := block519W2) (w3 := block519W3) (w4 := block519W4)
    (s1 := block519S1) (s2 := block519S2) (s3 := block519S3) (s4 := block519S4)
    hboxes hcover block519RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block519_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block519RightL : ℝ) (block519RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block519S1 : ℝ))
    (hy2ne : y ≠ (block519S2 : ℝ))
    (hy3ne : y ≠ (block519S3 : ℝ))
    (hy4ne : y ≠ (block519S4 : ℝ)) :
    0 < block519V y := by
  have hL : (block519RightChunk000L : ℝ) = (block519RightL : ℝ) := by
    norm_num [block519RightChunk000L, block519RightL]
  have hR : (block519RightChunk000R : ℝ) = (block519RightR : ℝ) := by
    norm_num [block519RightChunk000R, block519RightR]
  have hyc : y ∈ Icc (block519RightChunk000L : ℝ) (block519RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block519_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block519_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block519LeftL : ℝ) (block519LeftR : ℝ) →
    y ≠ 0 → y ≠ (block519S1 : ℝ) → y ≠ (block519S2 : ℝ) →
    y ≠ (block519S3 : ℝ) → y ≠ (block519S4 : ℝ) → 0 < block519V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block519RightL : ℝ) (block519RightR : ℝ) →
    y ≠ 0 → y ≠ (block519S1 : ℝ) → y ≠ (block519S2 : ℝ) →
    y ≠ (block519S3 : ℝ) → y ≠ (block519S4 : ℝ) → 0 < block519V y)

theorem block519_reallog_certificate_proof :
    block519_reallog_certificate := by
  exact ⟨block519_left_V_pos, block519_right_V_pos⟩

end Block519
end M1817475
end Erdos1038Lean
