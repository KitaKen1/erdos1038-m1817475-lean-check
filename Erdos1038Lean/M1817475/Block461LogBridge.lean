import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block461

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block461

open Set

def block461W1 : Rat := ((5664683074958213 : Rat) / 10000000000000000)
def block461W2 : Rat := (0 : Rat)
def block461W3 : Rat := ((870818345662537 : Rat) / 2500000000000000)
def block461W4 : Rat := ((11793493391202807 : Rat) / 200000000000000000)
def block461S1 : Rat := ((18174751 : Rat) / 10000000)
def block461S2 : Rat := ((511587 : Rat) / 200000)
def block461S3 : Rat := ((131121418839285714401 : Rat) / 50000000000000000000)
def block461S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block461V (y : ℝ) : ℝ :=
  ratPotential block461W1 block461W2 block461W3 block461W4 block461S1 block461S2 block461S3 block461S4 y

def block461LeftParamsCertificate : Bool :=
  allBoxesSameParams block461LeftBoxes block461W1 block461W2 block461W3 block461W4 block461S1 block461S2 block461S3 block461S4

theorem block461LeftParamsCertificate_eq_true :
    block461LeftParamsCertificate = true := by
  native_decide

theorem block461_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block461LeftL : ℝ) (block461LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block461S1 : ℝ))
    (hy2ne : y ≠ (block461S2 : ℝ))
    (hy3ne : y ≠ (block461S3 : ℝ))
    (hy4ne : y ≠ (block461S4 : ℝ)) :
    0 < block461V y := by
  have hcert := block461LeftCertificate_eq_true
  unfold block461LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block461LeftBoxes) (lo := block461LeftL) (hi := block461LeftR)
    (w1 := block461W1) (w2 := block461W2) (w3 := block461W3) (w4 := block461W4)
    (s1 := block461S1) (s2 := block461S2) (s3 := block461S3) (s4 := block461S4)
    hboxes hcover block461LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block461RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block461RightChunk000 block461W1 block461W2 block461W3 block461W4 block461S1 block461S2 block461S3 block461S4

theorem block461RightChunk000ParamsCertificate_eq_true :
    block461RightChunk000ParamsCertificate = true := by
  native_decide

theorem block461_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block461RightChunk000L : ℝ) (block461RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block461S1 : ℝ))
    (hy2ne : y ≠ (block461S2 : ℝ))
    (hy3ne : y ≠ (block461S3 : ℝ))
    (hy4ne : y ≠ (block461S4 : ℝ)) :
    0 < block461V y := by
  have hcert := block461RightChunk000Certificate_eq_true
  unfold block461RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block461RightChunk000) (lo := block461RightChunk000L) (hi := block461RightChunk000R)
    (w1 := block461W1) (w2 := block461W2) (w3 := block461W3) (w4 := block461W4)
    (s1 := block461S1) (s2 := block461S2) (s3 := block461S3) (s4 := block461S4)
    hboxes hcover block461RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block461_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block461RightL : ℝ) (block461RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block461S1 : ℝ))
    (hy2ne : y ≠ (block461S2 : ℝ))
    (hy3ne : y ≠ (block461S3 : ℝ))
    (hy4ne : y ≠ (block461S4 : ℝ)) :
    0 < block461V y := by
  have hL : (block461RightChunk000L : ℝ) = (block461RightL : ℝ) := by
    norm_num [block461RightChunk000L, block461RightL]
  have hR : (block461RightChunk000R : ℝ) = (block461RightR : ℝ) := by
    norm_num [block461RightChunk000R, block461RightR]
  have hyc : y ∈ Icc (block461RightChunk000L : ℝ) (block461RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block461_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block461_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block461LeftL : ℝ) (block461LeftR : ℝ) →
    y ≠ 0 → y ≠ (block461S1 : ℝ) → y ≠ (block461S2 : ℝ) →
    y ≠ (block461S3 : ℝ) → y ≠ (block461S4 : ℝ) → 0 < block461V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block461RightL : ℝ) (block461RightR : ℝ) →
    y ≠ 0 → y ≠ (block461S1 : ℝ) → y ≠ (block461S2 : ℝ) →
    y ≠ (block461S3 : ℝ) → y ≠ (block461S4 : ℝ) → 0 < block461V y)

theorem block461_reallog_certificate_proof :
    block461_reallog_certificate := by
  exact ⟨block461_left_V_pos, block461_right_V_pos⟩

end Block461
end M1817475
end Erdos1038Lean
