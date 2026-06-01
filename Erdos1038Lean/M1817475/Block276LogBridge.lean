import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block276

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block276

open Set

def block276W1 : Rat := ((5145239098032731 : Rat) / 5000000000000000)
def block276W2 : Rat := ((7896707261419781 : Rat) / 250000000000000000)
def block276W3 : Rat := ((28908550297307767 : Rat) / 100000000000000000)
def block276W4 : Rat := (0 : Rat)
def block276S1 : Rat := ((18174751 : Rat) / 10000000)
def block276S2 : Rat := ((511587 : Rat) / 200000)
def block276S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block276S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block276V (y : ℝ) : ℝ :=
  ratPotential block276W1 block276W2 block276W3 block276W4 block276S1 block276S2 block276S3 block276S4 y

def block276LeftParamsCertificate : Bool :=
  allBoxesSameParams block276LeftBoxes block276W1 block276W2 block276W3 block276W4 block276S1 block276S2 block276S3 block276S4

theorem block276LeftParamsCertificate_eq_true :
    block276LeftParamsCertificate = true := by
  native_decide

theorem block276_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block276LeftL : ℝ) (block276LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block276S1 : ℝ))
    (hy2ne : y ≠ (block276S2 : ℝ))
    (hy3ne : y ≠ (block276S3 : ℝ))
    (hy4ne : y ≠ (block276S4 : ℝ)) :
    0 < block276V y := by
  have hcert := block276LeftCertificate_eq_true
  unfold block276LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block276LeftBoxes) (lo := block276LeftL) (hi := block276LeftR)
    (w1 := block276W1) (w2 := block276W2) (w3 := block276W3) (w4 := block276W4)
    (s1 := block276S1) (s2 := block276S2) (s3 := block276S3) (s4 := block276S4)
    hboxes hcover block276LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block276RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block276RightChunk000 block276W1 block276W2 block276W3 block276W4 block276S1 block276S2 block276S3 block276S4

theorem block276RightChunk000ParamsCertificate_eq_true :
    block276RightChunk000ParamsCertificate = true := by
  native_decide

theorem block276_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block276RightChunk000L : ℝ) (block276RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block276S1 : ℝ))
    (hy2ne : y ≠ (block276S2 : ℝ))
    (hy3ne : y ≠ (block276S3 : ℝ))
    (hy4ne : y ≠ (block276S4 : ℝ)) :
    0 < block276V y := by
  have hcert := block276RightChunk000Certificate_eq_true
  unfold block276RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block276RightChunk000) (lo := block276RightChunk000L) (hi := block276RightChunk000R)
    (w1 := block276W1) (w2 := block276W2) (w3 := block276W3) (w4 := block276W4)
    (s1 := block276S1) (s2 := block276S2) (s3 := block276S3) (s4 := block276S4)
    hboxes hcover block276RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block276_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block276RightL : ℝ) (block276RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block276S1 : ℝ))
    (hy2ne : y ≠ (block276S2 : ℝ))
    (hy3ne : y ≠ (block276S3 : ℝ))
    (hy4ne : y ≠ (block276S4 : ℝ)) :
    0 < block276V y := by
  have hL : (block276RightChunk000L : ℝ) = (block276RightL : ℝ) := by
    norm_num [block276RightChunk000L, block276RightL]
  have hR : (block276RightChunk000R : ℝ) = (block276RightR : ℝ) := by
    norm_num [block276RightChunk000R, block276RightR]
  have hyc : y ∈ Icc (block276RightChunk000L : ℝ) (block276RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block276_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block276_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block276LeftL : ℝ) (block276LeftR : ℝ) →
    y ≠ 0 → y ≠ (block276S1 : ℝ) → y ≠ (block276S2 : ℝ) →
    y ≠ (block276S3 : ℝ) → y ≠ (block276S4 : ℝ) → 0 < block276V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block276RightL : ℝ) (block276RightR : ℝ) →
    y ≠ 0 → y ≠ (block276S1 : ℝ) → y ≠ (block276S2 : ℝ) →
    y ≠ (block276S3 : ℝ) → y ≠ (block276S4 : ℝ) → 0 < block276V y)

theorem block276_reallog_certificate_proof :
    block276_reallog_certificate := by
  exact ⟨block276_left_V_pos, block276_right_V_pos⟩

end Block276
end M1817475
end Erdos1038Lean
