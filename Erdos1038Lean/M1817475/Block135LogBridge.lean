import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block135

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block135

open Set

def block135W1 : Rat := ((1267334883127533 : Rat) / 500000000000000)
def block135W2 : Rat := (0 : Rat)
def block135W3 : Rat := ((711520688987313 : Rat) / 6250000000000000)
def block135W4 : Rat := ((6329205139518773 : Rat) / 50000000000000000)
def block135S1 : Rat := ((18174751 : Rat) / 10000000)
def block135S2 : Rat := ((511587 : Rat) / 200000)
def block135S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block135S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block135V (y : ℝ) : ℝ :=
  ratPotential block135W1 block135W2 block135W3 block135W4 block135S1 block135S2 block135S3 block135S4 y

def block135LeftParamsCertificate : Bool :=
  allBoxesSameParams block135LeftBoxes block135W1 block135W2 block135W3 block135W4 block135S1 block135S2 block135S3 block135S4

theorem block135LeftParamsCertificate_eq_true :
    block135LeftParamsCertificate = true := by
  native_decide

theorem block135_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block135LeftL : ℝ) (block135LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block135S1 : ℝ))
    (hy2ne : y ≠ (block135S2 : ℝ))
    (hy3ne : y ≠ (block135S3 : ℝ))
    (hy4ne : y ≠ (block135S4 : ℝ)) :
    0 < block135V y := by
  have hcert := block135LeftCertificate_eq_true
  unfold block135LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block135LeftBoxes) (lo := block135LeftL) (hi := block135LeftR)
    (w1 := block135W1) (w2 := block135W2) (w3 := block135W3) (w4 := block135W4)
    (s1 := block135S1) (s2 := block135S2) (s3 := block135S3) (s4 := block135S4)
    hboxes hcover block135LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block135RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block135RightChunk000 block135W1 block135W2 block135W3 block135W4 block135S1 block135S2 block135S3 block135S4

theorem block135RightChunk000ParamsCertificate_eq_true :
    block135RightChunk000ParamsCertificate = true := by
  native_decide

theorem block135_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block135RightChunk000L : ℝ) (block135RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block135S1 : ℝ))
    (hy2ne : y ≠ (block135S2 : ℝ))
    (hy3ne : y ≠ (block135S3 : ℝ))
    (hy4ne : y ≠ (block135S4 : ℝ)) :
    0 < block135V y := by
  have hcert := block135RightChunk000Certificate_eq_true
  unfold block135RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block135RightChunk000) (lo := block135RightChunk000L) (hi := block135RightChunk000R)
    (w1 := block135W1) (w2 := block135W2) (w3 := block135W3) (w4 := block135W4)
    (s1 := block135S1) (s2 := block135S2) (s3 := block135S3) (s4 := block135S4)
    hboxes hcover block135RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block135_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block135RightL : ℝ) (block135RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block135S1 : ℝ))
    (hy2ne : y ≠ (block135S2 : ℝ))
    (hy3ne : y ≠ (block135S3 : ℝ))
    (hy4ne : y ≠ (block135S4 : ℝ)) :
    0 < block135V y := by
  have hL : (block135RightChunk000L : ℝ) = (block135RightL : ℝ) := by
    norm_num [block135RightChunk000L, block135RightL]
  have hR : (block135RightChunk000R : ℝ) = (block135RightR : ℝ) := by
    norm_num [block135RightChunk000R, block135RightR]
  have hyc : y ∈ Icc (block135RightChunk000L : ℝ) (block135RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block135_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block135_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block135LeftL : ℝ) (block135LeftR : ℝ) →
    y ≠ 0 → y ≠ (block135S1 : ℝ) → y ≠ (block135S2 : ℝ) →
    y ≠ (block135S3 : ℝ) → y ≠ (block135S4 : ℝ) → 0 < block135V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block135RightL : ℝ) (block135RightR : ℝ) →
    y ≠ 0 → y ≠ (block135S1 : ℝ) → y ≠ (block135S2 : ℝ) →
    y ≠ (block135S3 : ℝ) → y ≠ (block135S4 : ℝ) → 0 < block135V y)

theorem block135_reallog_certificate_proof :
    block135_reallog_certificate := by
  exact ⟨block135_left_V_pos, block135_right_V_pos⟩

end Block135
end M1817475
end Erdos1038Lean
