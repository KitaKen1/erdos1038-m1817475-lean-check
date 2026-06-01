import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block486

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block486

open Set

def block486W1 : Rat := ((4984772030667591 : Rat) / 10000000000000000)
def block486W2 : Rat := (0 : Rat)
def block486W3 : Rat := ((30359800107429 : Rat) / 78125000000000)
def block486W4 : Rat := ((3589666908077707 : Rat) / 100000000000000000)
def block486S1 : Rat := ((18174751 : Rat) / 10000000)
def block486S2 : Rat := ((511587 : Rat) / 200000)
def block486S3 : Rat := ((130632691160714285851 : Rat) / 50000000000000000000)
def block486S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block486V (y : ℝ) : ℝ :=
  ratPotential block486W1 block486W2 block486W3 block486W4 block486S1 block486S2 block486S3 block486S4 y

def block486LeftParamsCertificate : Bool :=
  allBoxesSameParams block486LeftBoxes block486W1 block486W2 block486W3 block486W4 block486S1 block486S2 block486S3 block486S4

theorem block486LeftParamsCertificate_eq_true :
    block486LeftParamsCertificate = true := by
  native_decide

theorem block486_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block486LeftL : ℝ) (block486LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block486S1 : ℝ))
    (hy2ne : y ≠ (block486S2 : ℝ))
    (hy3ne : y ≠ (block486S3 : ℝ))
    (hy4ne : y ≠ (block486S4 : ℝ)) :
    0 < block486V y := by
  have hcert := block486LeftCertificate_eq_true
  unfold block486LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block486LeftBoxes) (lo := block486LeftL) (hi := block486LeftR)
    (w1 := block486W1) (w2 := block486W2) (w3 := block486W3) (w4 := block486W4)
    (s1 := block486S1) (s2 := block486S2) (s3 := block486S3) (s4 := block486S4)
    hboxes hcover block486LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block486RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block486RightChunk000 block486W1 block486W2 block486W3 block486W4 block486S1 block486S2 block486S3 block486S4

theorem block486RightChunk000ParamsCertificate_eq_true :
    block486RightChunk000ParamsCertificate = true := by
  native_decide

theorem block486_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block486RightChunk000L : ℝ) (block486RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block486S1 : ℝ))
    (hy2ne : y ≠ (block486S2 : ℝ))
    (hy3ne : y ≠ (block486S3 : ℝ))
    (hy4ne : y ≠ (block486S4 : ℝ)) :
    0 < block486V y := by
  have hcert := block486RightChunk000Certificate_eq_true
  unfold block486RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block486RightChunk000) (lo := block486RightChunk000L) (hi := block486RightChunk000R)
    (w1 := block486W1) (w2 := block486W2) (w3 := block486W3) (w4 := block486W4)
    (s1 := block486S1) (s2 := block486S2) (s3 := block486S3) (s4 := block486S4)
    hboxes hcover block486RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block486_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block486RightL : ℝ) (block486RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block486S1 : ℝ))
    (hy2ne : y ≠ (block486S2 : ℝ))
    (hy3ne : y ≠ (block486S3 : ℝ))
    (hy4ne : y ≠ (block486S4 : ℝ)) :
    0 < block486V y := by
  have hL : (block486RightChunk000L : ℝ) = (block486RightL : ℝ) := by
    norm_num [block486RightChunk000L, block486RightL]
  have hR : (block486RightChunk000R : ℝ) = (block486RightR : ℝ) := by
    norm_num [block486RightChunk000R, block486RightR]
  have hyc : y ∈ Icc (block486RightChunk000L : ℝ) (block486RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block486_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block486_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block486LeftL : ℝ) (block486LeftR : ℝ) →
    y ≠ 0 → y ≠ (block486S1 : ℝ) → y ≠ (block486S2 : ℝ) →
    y ≠ (block486S3 : ℝ) → y ≠ (block486S4 : ℝ) → 0 < block486V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block486RightL : ℝ) (block486RightR : ℝ) →
    y ≠ 0 → y ≠ (block486S1 : ℝ) → y ≠ (block486S2 : ℝ) →
    y ≠ (block486S3 : ℝ) → y ≠ (block486S4 : ℝ) → 0 < block486V y)

theorem block486_reallog_certificate_proof :
    block486_reallog_certificate := by
  exact ⟨block486_left_V_pos, block486_right_V_pos⟩

end Block486
end M1817475
end Erdos1038Lean
