import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block077

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block077

open Set

def block077W1 : Rat := ((32480026826186523 : Rat) / 10000000000000000)
def block077W2 : Rat := (0 : Rat)
def block077W3 : Rat := (0 : Rat)
def block077W4 : Rat := ((1530720336212151 : Rat) / 6250000000000000)
def block077S1 : Rat := ((18174751 : Rat) / 10000000)
def block077S2 : Rat := ((511587 : Rat) / 200000)
def block077S3 : Rat := ((107000619 : Rat) / 40000000)
def block077S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block077V (y : ℝ) : ℝ :=
  ratPotential block077W1 block077W2 block077W3 block077W4 block077S1 block077S2 block077S3 block077S4 y

def block077LeftParamsCertificate : Bool :=
  allBoxesSameParams block077LeftBoxes block077W1 block077W2 block077W3 block077W4 block077S1 block077S2 block077S3 block077S4

theorem block077LeftParamsCertificate_eq_true :
    block077LeftParamsCertificate = true := by
  native_decide

theorem block077_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block077LeftL : ℝ) (block077LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block077S1 : ℝ))
    (hy2ne : y ≠ (block077S2 : ℝ))
    (hy3ne : y ≠ (block077S3 : ℝ))
    (hy4ne : y ≠ (block077S4 : ℝ)) :
    0 < block077V y := by
  have hcert := block077LeftCertificate_eq_true
  unfold block077LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block077LeftBoxes) (lo := block077LeftL) (hi := block077LeftR)
    (w1 := block077W1) (w2 := block077W2) (w3 := block077W3) (w4 := block077W4)
    (s1 := block077S1) (s2 := block077S2) (s3 := block077S3) (s4 := block077S4)
    hboxes hcover block077LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block077RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block077RightChunk000 block077W1 block077W2 block077W3 block077W4 block077S1 block077S2 block077S3 block077S4

theorem block077RightChunk000ParamsCertificate_eq_true :
    block077RightChunk000ParamsCertificate = true := by
  native_decide

theorem block077_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block077RightChunk000L : ℝ) (block077RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block077S1 : ℝ))
    (hy2ne : y ≠ (block077S2 : ℝ))
    (hy3ne : y ≠ (block077S3 : ℝ))
    (hy4ne : y ≠ (block077S4 : ℝ)) :
    0 < block077V y := by
  have hcert := block077RightChunk000Certificate_eq_true
  unfold block077RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block077RightChunk000) (lo := block077RightChunk000L) (hi := block077RightChunk000R)
    (w1 := block077W1) (w2 := block077W2) (w3 := block077W3) (w4 := block077W4)
    (s1 := block077S1) (s2 := block077S2) (s3 := block077S3) (s4 := block077S4)
    hboxes hcover block077RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block077_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block077RightL : ℝ) (block077RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block077S1 : ℝ))
    (hy2ne : y ≠ (block077S2 : ℝ))
    (hy3ne : y ≠ (block077S3 : ℝ))
    (hy4ne : y ≠ (block077S4 : ℝ)) :
    0 < block077V y := by
  have hL : (block077RightChunk000L : ℝ) = (block077RightL : ℝ) := by
    norm_num [block077RightChunk000L, block077RightL]
  have hR : (block077RightChunk000R : ℝ) = (block077RightR : ℝ) := by
    norm_num [block077RightChunk000R, block077RightR]
  have hyc : y ∈ Icc (block077RightChunk000L : ℝ) (block077RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block077_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block077_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block077LeftL : ℝ) (block077LeftR : ℝ) →
    y ≠ 0 → y ≠ (block077S1 : ℝ) → y ≠ (block077S2 : ℝ) →
    y ≠ (block077S3 : ℝ) → y ≠ (block077S4 : ℝ) → 0 < block077V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block077RightL : ℝ) (block077RightR : ℝ) →
    y ≠ 0 → y ≠ (block077S1 : ℝ) → y ≠ (block077S2 : ℝ) →
    y ≠ (block077S3 : ℝ) → y ≠ (block077S4 : ℝ) → 0 < block077V y)

theorem block077_reallog_certificate_proof :
    block077_reallog_certificate := by
  exact ⟨block077_left_V_pos, block077_right_V_pos⟩

end Block077
end M1817475
end Erdos1038Lean
