import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block084

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block084

open Set

def block084W1 : Rat := ((1719874382176849 : Rat) / 500000000000000)
def block084W2 : Rat := (0 : Rat)
def block084W3 : Rat := (0 : Rat)
def block084W4 : Rat := ((2378902827533451 : Rat) / 10000000000000000)
def block084S1 : Rat := ((18174751 : Rat) / 10000000)
def block084S2 : Rat := ((511587 : Rat) / 200000)
def block084S3 : Rat := ((107000619 : Rat) / 40000000)
def block084S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block084V (y : ℝ) : ℝ :=
  ratPotential block084W1 block084W2 block084W3 block084W4 block084S1 block084S2 block084S3 block084S4 y

def block084LeftParamsCertificate : Bool :=
  allBoxesSameParams block084LeftBoxes block084W1 block084W2 block084W3 block084W4 block084S1 block084S2 block084S3 block084S4

theorem block084LeftParamsCertificate_eq_true :
    block084LeftParamsCertificate = true := by
  native_decide

theorem block084_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block084LeftL : ℝ) (block084LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block084S1 : ℝ))
    (hy2ne : y ≠ (block084S2 : ℝ))
    (hy3ne : y ≠ (block084S3 : ℝ))
    (hy4ne : y ≠ (block084S4 : ℝ)) :
    0 < block084V y := by
  have hcert := block084LeftCertificate_eq_true
  unfold block084LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block084LeftBoxes) (lo := block084LeftL) (hi := block084LeftR)
    (w1 := block084W1) (w2 := block084W2) (w3 := block084W3) (w4 := block084W4)
    (s1 := block084S1) (s2 := block084S2) (s3 := block084S3) (s4 := block084S4)
    hboxes hcover block084LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block084RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block084RightChunk000 block084W1 block084W2 block084W3 block084W4 block084S1 block084S2 block084S3 block084S4

theorem block084RightChunk000ParamsCertificate_eq_true :
    block084RightChunk000ParamsCertificate = true := by
  native_decide

theorem block084_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block084RightChunk000L : ℝ) (block084RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block084S1 : ℝ))
    (hy2ne : y ≠ (block084S2 : ℝ))
    (hy3ne : y ≠ (block084S3 : ℝ))
    (hy4ne : y ≠ (block084S4 : ℝ)) :
    0 < block084V y := by
  have hcert := block084RightChunk000Certificate_eq_true
  unfold block084RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block084RightChunk000) (lo := block084RightChunk000L) (hi := block084RightChunk000R)
    (w1 := block084W1) (w2 := block084W2) (w3 := block084W3) (w4 := block084W4)
    (s1 := block084S1) (s2 := block084S2) (s3 := block084S3) (s4 := block084S4)
    hboxes hcover block084RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block084_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block084RightL : ℝ) (block084RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block084S1 : ℝ))
    (hy2ne : y ≠ (block084S2 : ℝ))
    (hy3ne : y ≠ (block084S3 : ℝ))
    (hy4ne : y ≠ (block084S4 : ℝ)) :
    0 < block084V y := by
  have hL : (block084RightChunk000L : ℝ) = (block084RightL : ℝ) := by
    norm_num [block084RightChunk000L, block084RightL]
  have hR : (block084RightChunk000R : ℝ) = (block084RightR : ℝ) := by
    norm_num [block084RightChunk000R, block084RightR]
  have hyc : y ∈ Icc (block084RightChunk000L : ℝ) (block084RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block084_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block084_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block084LeftL : ℝ) (block084LeftR : ℝ) →
    y ≠ 0 → y ≠ (block084S1 : ℝ) → y ≠ (block084S2 : ℝ) →
    y ≠ (block084S3 : ℝ) → y ≠ (block084S4 : ℝ) → 0 < block084V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block084RightL : ℝ) (block084RightR : ℝ) →
    y ≠ 0 → y ≠ (block084S1 : ℝ) → y ≠ (block084S2 : ℝ) →
    y ≠ (block084S3 : ℝ) → y ≠ (block084S4 : ℝ) → 0 < block084V y)

theorem block084_reallog_certificate_proof :
    block084_reallog_certificate := by
  exact ⟨block084_left_V_pos, block084_right_V_pos⟩

end Block084
end M1817475
end Erdos1038Lean
