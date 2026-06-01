import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block051

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block051

open Set

def block051W1 : Rat := ((2695549716100683 : Rat) / 1000000000000000)
def block051W2 : Rat := (0 : Rat)
def block051W3 : Rat := (0 : Rat)
def block051W4 : Rat := ((6692052344014271 : Rat) / 25000000000000000)
def block051S1 : Rat := ((18174751 : Rat) / 10000000)
def block051S2 : Rat := ((511587 : Rat) / 200000)
def block051S3 : Rat := ((107000619 : Rat) / 40000000)
def block051S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block051V (y : ℝ) : ℝ :=
  ratPotential block051W1 block051W2 block051W3 block051W4 block051S1 block051S2 block051S3 block051S4 y

def block051LeftParamsCertificate : Bool :=
  allBoxesSameParams block051LeftBoxes block051W1 block051W2 block051W3 block051W4 block051S1 block051S2 block051S3 block051S4

theorem block051LeftParamsCertificate_eq_true :
    block051LeftParamsCertificate = true := by
  native_decide

theorem block051_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block051LeftL : ℝ) (block051LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block051S1 : ℝ))
    (hy2ne : y ≠ (block051S2 : ℝ))
    (hy3ne : y ≠ (block051S3 : ℝ))
    (hy4ne : y ≠ (block051S4 : ℝ)) :
    0 < block051V y := by
  have hcert := block051LeftCertificate_eq_true
  unfold block051LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block051LeftBoxes) (lo := block051LeftL) (hi := block051LeftR)
    (w1 := block051W1) (w2 := block051W2) (w3 := block051W3) (w4 := block051W4)
    (s1 := block051S1) (s2 := block051S2) (s3 := block051S3) (s4 := block051S4)
    hboxes hcover block051LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block051RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block051RightChunk000 block051W1 block051W2 block051W3 block051W4 block051S1 block051S2 block051S3 block051S4

theorem block051RightChunk000ParamsCertificate_eq_true :
    block051RightChunk000ParamsCertificate = true := by
  native_decide

theorem block051_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block051RightChunk000L : ℝ) (block051RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block051S1 : ℝ))
    (hy2ne : y ≠ (block051S2 : ℝ))
    (hy3ne : y ≠ (block051S3 : ℝ))
    (hy4ne : y ≠ (block051S4 : ℝ)) :
    0 < block051V y := by
  have hcert := block051RightChunk000Certificate_eq_true
  unfold block051RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block051RightChunk000) (lo := block051RightChunk000L) (hi := block051RightChunk000R)
    (w1 := block051W1) (w2 := block051W2) (w3 := block051W3) (w4 := block051W4)
    (s1 := block051S1) (s2 := block051S2) (s3 := block051S3) (s4 := block051S4)
    hboxes hcover block051RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block051_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block051RightL : ℝ) (block051RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block051S1 : ℝ))
    (hy2ne : y ≠ (block051S2 : ℝ))
    (hy3ne : y ≠ (block051S3 : ℝ))
    (hy4ne : y ≠ (block051S4 : ℝ)) :
    0 < block051V y := by
  have hL : (block051RightChunk000L : ℝ) = (block051RightL : ℝ) := by
    norm_num [block051RightChunk000L, block051RightL]
  have hR : (block051RightChunk000R : ℝ) = (block051RightR : ℝ) := by
    norm_num [block051RightChunk000R, block051RightR]
  have hyc : y ∈ Icc (block051RightChunk000L : ℝ) (block051RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block051_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block051_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block051LeftL : ℝ) (block051LeftR : ℝ) →
    y ≠ 0 → y ≠ (block051S1 : ℝ) → y ≠ (block051S2 : ℝ) →
    y ≠ (block051S3 : ℝ) → y ≠ (block051S4 : ℝ) → 0 < block051V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block051RightL : ℝ) (block051RightR : ℝ) →
    y ≠ 0 → y ≠ (block051S1 : ℝ) → y ≠ (block051S2 : ℝ) →
    y ≠ (block051S3 : ℝ) → y ≠ (block051S4 : ℝ) → 0 < block051V y)

theorem block051_reallog_certificate_proof :
    block051_reallog_certificate := by
  exact ⟨block051_left_V_pos, block051_right_V_pos⟩

end Block051
end M1817475
end Erdos1038Lean
