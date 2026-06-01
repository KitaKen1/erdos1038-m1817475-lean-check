import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block031

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block031

open Set

def block031W1 : Rat := ((23856418198854903 : Rat) / 10000000000000000)
def block031W2 : Rat := (0 : Rat)
def block031W3 : Rat := (0 : Rat)
def block031W4 : Rat := ((7064543242659091 : Rat) / 25000000000000000)
def block031S1 : Rat := ((18174751 : Rat) / 10000000)
def block031S2 : Rat := ((511587 : Rat) / 200000)
def block031S3 : Rat := ((107000619 : Rat) / 40000000)
def block031S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block031V (y : ℝ) : ℝ :=
  ratPotential block031W1 block031W2 block031W3 block031W4 block031S1 block031S2 block031S3 block031S4 y

def block031LeftParamsCertificate : Bool :=
  allBoxesSameParams block031LeftBoxes block031W1 block031W2 block031W3 block031W4 block031S1 block031S2 block031S3 block031S4

theorem block031LeftParamsCertificate_eq_true :
    block031LeftParamsCertificate = true := by
  native_decide

theorem block031_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block031LeftL : ℝ) (block031LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block031S1 : ℝ))
    (hy2ne : y ≠ (block031S2 : ℝ))
    (hy3ne : y ≠ (block031S3 : ℝ))
    (hy4ne : y ≠ (block031S4 : ℝ)) :
    0 < block031V y := by
  have hcert := block031LeftCertificate_eq_true
  unfold block031LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block031LeftBoxes) (lo := block031LeftL) (hi := block031LeftR)
    (w1 := block031W1) (w2 := block031W2) (w3 := block031W3) (w4 := block031W4)
    (s1 := block031S1) (s2 := block031S2) (s3 := block031S3) (s4 := block031S4)
    hboxes hcover block031LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block031RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block031RightChunk000 block031W1 block031W2 block031W3 block031W4 block031S1 block031S2 block031S3 block031S4

theorem block031RightChunk000ParamsCertificate_eq_true :
    block031RightChunk000ParamsCertificate = true := by
  native_decide

theorem block031_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block031RightChunk000L : ℝ) (block031RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block031S1 : ℝ))
    (hy2ne : y ≠ (block031S2 : ℝ))
    (hy3ne : y ≠ (block031S3 : ℝ))
    (hy4ne : y ≠ (block031S4 : ℝ)) :
    0 < block031V y := by
  have hcert := block031RightChunk000Certificate_eq_true
  unfold block031RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block031RightChunk000) (lo := block031RightChunk000L) (hi := block031RightChunk000R)
    (w1 := block031W1) (w2 := block031W2) (w3 := block031W3) (w4 := block031W4)
    (s1 := block031S1) (s2 := block031S2) (s3 := block031S3) (s4 := block031S4)
    hboxes hcover block031RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block031_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block031RightL : ℝ) (block031RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block031S1 : ℝ))
    (hy2ne : y ≠ (block031S2 : ℝ))
    (hy3ne : y ≠ (block031S3 : ℝ))
    (hy4ne : y ≠ (block031S4 : ℝ)) :
    0 < block031V y := by
  have hL : (block031RightChunk000L : ℝ) = (block031RightL : ℝ) := by
    norm_num [block031RightChunk000L, block031RightL]
  have hR : (block031RightChunk000R : ℝ) = (block031RightR : ℝ) := by
    norm_num [block031RightChunk000R, block031RightR]
  have hyc : y ∈ Icc (block031RightChunk000L : ℝ) (block031RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block031_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block031_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block031LeftL : ℝ) (block031LeftR : ℝ) →
    y ≠ 0 → y ≠ (block031S1 : ℝ) → y ≠ (block031S2 : ℝ) →
    y ≠ (block031S3 : ℝ) → y ≠ (block031S4 : ℝ) → 0 < block031V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block031RightL : ℝ) (block031RightR : ℝ) →
    y ≠ 0 → y ≠ (block031S1 : ℝ) → y ≠ (block031S2 : ℝ) →
    y ≠ (block031S3 : ℝ) → y ≠ (block031S4 : ℝ) → 0 < block031V y)

theorem block031_reallog_certificate_proof :
    block031_reallog_certificate := by
  exact ⟨block031_left_V_pos, block031_right_V_pos⟩

end Block031
end M1817475
end Erdos1038Lean
