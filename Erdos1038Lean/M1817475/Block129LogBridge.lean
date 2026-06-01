import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block129

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block129

open Set

def block129W1 : Rat := ((3195529364131357 : Rat) / 1250000000000000)
def block129W2 : Rat := (0 : Rat)
def block129W3 : Rat := ((2603414432701969 : Rat) / 25000000000000000)
def block129W4 : Rat := ((6881085833917297 : Rat) / 50000000000000000)
def block129S1 : Rat := ((18174751 : Rat) / 10000000)
def block129S2 : Rat := ((511587 : Rat) / 200000)
def block129S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block129S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block129V (y : ℝ) : ℝ :=
  ratPotential block129W1 block129W2 block129W3 block129W4 block129S1 block129S2 block129S3 block129S4 y

def block129LeftParamsCertificate : Bool :=
  allBoxesSameParams block129LeftBoxes block129W1 block129W2 block129W3 block129W4 block129S1 block129S2 block129S3 block129S4

theorem block129LeftParamsCertificate_eq_true :
    block129LeftParamsCertificate = true := by
  native_decide

theorem block129_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block129LeftL : ℝ) (block129LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block129S1 : ℝ))
    (hy2ne : y ≠ (block129S2 : ℝ))
    (hy3ne : y ≠ (block129S3 : ℝ))
    (hy4ne : y ≠ (block129S4 : ℝ)) :
    0 < block129V y := by
  have hcert := block129LeftCertificate_eq_true
  unfold block129LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block129LeftBoxes) (lo := block129LeftL) (hi := block129LeftR)
    (w1 := block129W1) (w2 := block129W2) (w3 := block129W3) (w4 := block129W4)
    (s1 := block129S1) (s2 := block129S2) (s3 := block129S3) (s4 := block129S4)
    hboxes hcover block129LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block129RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block129RightChunk000 block129W1 block129W2 block129W3 block129W4 block129S1 block129S2 block129S3 block129S4

theorem block129RightChunk000ParamsCertificate_eq_true :
    block129RightChunk000ParamsCertificate = true := by
  native_decide

theorem block129_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block129RightChunk000L : ℝ) (block129RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block129S1 : ℝ))
    (hy2ne : y ≠ (block129S2 : ℝ))
    (hy3ne : y ≠ (block129S3 : ℝ))
    (hy4ne : y ≠ (block129S4 : ℝ)) :
    0 < block129V y := by
  have hcert := block129RightChunk000Certificate_eq_true
  unfold block129RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block129RightChunk000) (lo := block129RightChunk000L) (hi := block129RightChunk000R)
    (w1 := block129W1) (w2 := block129W2) (w3 := block129W3) (w4 := block129W4)
    (s1 := block129S1) (s2 := block129S2) (s3 := block129S3) (s4 := block129S4)
    hboxes hcover block129RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block129_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block129RightL : ℝ) (block129RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block129S1 : ℝ))
    (hy2ne : y ≠ (block129S2 : ℝ))
    (hy3ne : y ≠ (block129S3 : ℝ))
    (hy4ne : y ≠ (block129S4 : ℝ)) :
    0 < block129V y := by
  have hL : (block129RightChunk000L : ℝ) = (block129RightL : ℝ) := by
    norm_num [block129RightChunk000L, block129RightL]
  have hR : (block129RightChunk000R : ℝ) = (block129RightR : ℝ) := by
    norm_num [block129RightChunk000R, block129RightR]
  have hyc : y ∈ Icc (block129RightChunk000L : ℝ) (block129RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block129_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block129_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block129LeftL : ℝ) (block129LeftR : ℝ) →
    y ≠ 0 → y ≠ (block129S1 : ℝ) → y ≠ (block129S2 : ℝ) →
    y ≠ (block129S3 : ℝ) → y ≠ (block129S4 : ℝ) → 0 < block129V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block129RightL : ℝ) (block129RightR : ℝ) →
    y ≠ 0 → y ≠ (block129S1 : ℝ) → y ≠ (block129S2 : ℝ) →
    y ≠ (block129S3 : ℝ) → y ≠ (block129S4 : ℝ) → 0 < block129V y)

theorem block129_reallog_certificate_proof :
    block129_reallog_certificate := by
  exact ⟨block129_left_V_pos, block129_right_V_pos⟩

end Block129
end M1817475
end Erdos1038Lean
