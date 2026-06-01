import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block100

open Set

def block100W1 : Rat := ((261475144049397 : Rat) / 100000000000000)
def block100W2 : Rat := (0 : Rat)
def block100W3 : Rat := ((4901830849901533 : Rat) / 100000000000000000)
def block100W4 : Rat := ((9950799702914183 : Rat) / 50000000000000000)
def block100S1 : Rat := ((18174751 : Rat) / 10000000)
def block100S2 : Rat := ((511587 : Rat) / 200000)
def block100S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block100S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block100V (y : ℝ) : ℝ :=
  ratPotential block100W1 block100W2 block100W3 block100W4 block100S1 block100S2 block100S3 block100S4 y

def block100LeftParamsCertificate : Bool :=
  allBoxesSameParams block100LeftBoxes block100W1 block100W2 block100W3 block100W4 block100S1 block100S2 block100S3 block100S4

theorem block100LeftParamsCertificate_eq_true :
    block100LeftParamsCertificate = true := by
  native_decide

theorem block100_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block100LeftL : ℝ) (block100LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block100S1 : ℝ))
    (hy2ne : y ≠ (block100S2 : ℝ))
    (hy3ne : y ≠ (block100S3 : ℝ))
    (hy4ne : y ≠ (block100S4 : ℝ)) :
    0 < block100V y := by
  have hcert := block100LeftCertificate_eq_true
  unfold block100LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block100LeftBoxes) (lo := block100LeftL) (hi := block100LeftR)
    (w1 := block100W1) (w2 := block100W2) (w3 := block100W3) (w4 := block100W4)
    (s1 := block100S1) (s2 := block100S2) (s3 := block100S3) (s4 := block100S4)
    hboxes hcover block100LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block100RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block100RightChunk000 block100W1 block100W2 block100W3 block100W4 block100S1 block100S2 block100S3 block100S4

theorem block100RightChunk000ParamsCertificate_eq_true :
    block100RightChunk000ParamsCertificate = true := by
  native_decide

theorem block100_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block100RightChunk000L : ℝ) (block100RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block100S1 : ℝ))
    (hy2ne : y ≠ (block100S2 : ℝ))
    (hy3ne : y ≠ (block100S3 : ℝ))
    (hy4ne : y ≠ (block100S4 : ℝ)) :
    0 < block100V y := by
  have hcert := block100RightChunk000Certificate_eq_true
  unfold block100RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block100RightChunk000) (lo := block100RightChunk000L) (hi := block100RightChunk000R)
    (w1 := block100W1) (w2 := block100W2) (w3 := block100W3) (w4 := block100W4)
    (s1 := block100S1) (s2 := block100S2) (s3 := block100S3) (s4 := block100S4)
    hboxes hcover block100RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block100_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block100RightL : ℝ) (block100RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block100S1 : ℝ))
    (hy2ne : y ≠ (block100S2 : ℝ))
    (hy3ne : y ≠ (block100S3 : ℝ))
    (hy4ne : y ≠ (block100S4 : ℝ)) :
    0 < block100V y := by
  have hL : (block100RightChunk000L : ℝ) = (block100RightL : ℝ) := by
    norm_num [block100RightChunk000L, block100RightL]
  have hR : (block100RightChunk000R : ℝ) = (block100RightR : ℝ) := by
    norm_num [block100RightChunk000R, block100RightR]
  have hyc : y ∈ Icc (block100RightChunk000L : ℝ) (block100RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block100_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block100_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block100LeftL : ℝ) (block100LeftR : ℝ) →
    y ≠ 0 → y ≠ (block100S1 : ℝ) → y ≠ (block100S2 : ℝ) →
    y ≠ (block100S3 : ℝ) → y ≠ (block100S4 : ℝ) → 0 < block100V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block100RightL : ℝ) (block100RightR : ℝ) →
    y ≠ 0 → y ≠ (block100S1 : ℝ) → y ≠ (block100S2 : ℝ) →
    y ≠ (block100S3 : ℝ) → y ≠ (block100S4 : ℝ) → 0 < block100V y)

theorem block100_reallog_certificate_proof :
    block100_reallog_certificate := by
  exact ⟨block100_left_V_pos, block100_right_V_pos⟩

end Block100
end M1817475
end Erdos1038Lean
