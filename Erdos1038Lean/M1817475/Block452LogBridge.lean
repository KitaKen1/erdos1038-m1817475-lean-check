import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block452

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block452

open Set

def block452W1 : Rat := ((369859321524737 : Rat) / 625000000000000)
def block452W2 : Rat := (0 : Rat)
def block452W3 : Rat := ((8392295267664411 : Rat) / 25000000000000000)
def block452W4 : Rat := ((6575664268482999 : Rat) / 100000000000000000)
def block452S1 : Rat := ((18174751 : Rat) / 10000000)
def block452S2 : Rat := ((511587 : Rat) / 200000)
def block452S3 : Rat := ((131297360803571428679 : Rat) / 50000000000000000000)
def block452S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block452V (y : ℝ) : ℝ :=
  ratPotential block452W1 block452W2 block452W3 block452W4 block452S1 block452S2 block452S3 block452S4 y

def block452LeftParamsCertificate : Bool :=
  allBoxesSameParams block452LeftBoxes block452W1 block452W2 block452W3 block452W4 block452S1 block452S2 block452S3 block452S4

theorem block452LeftParamsCertificate_eq_true :
    block452LeftParamsCertificate = true := by
  native_decide

theorem block452_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block452LeftL : ℝ) (block452LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block452S1 : ℝ))
    (hy2ne : y ≠ (block452S2 : ℝ))
    (hy3ne : y ≠ (block452S3 : ℝ))
    (hy4ne : y ≠ (block452S4 : ℝ)) :
    0 < block452V y := by
  have hcert := block452LeftCertificate_eq_true
  unfold block452LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block452LeftBoxes) (lo := block452LeftL) (hi := block452LeftR)
    (w1 := block452W1) (w2 := block452W2) (w3 := block452W3) (w4 := block452W4)
    (s1 := block452S1) (s2 := block452S2) (s3 := block452S3) (s4 := block452S4)
    hboxes hcover block452LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block452RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block452RightChunk000 block452W1 block452W2 block452W3 block452W4 block452S1 block452S2 block452S3 block452S4

theorem block452RightChunk000ParamsCertificate_eq_true :
    block452RightChunk000ParamsCertificate = true := by
  native_decide

theorem block452_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block452RightChunk000L : ℝ) (block452RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block452S1 : ℝ))
    (hy2ne : y ≠ (block452S2 : ℝ))
    (hy3ne : y ≠ (block452S3 : ℝ))
    (hy4ne : y ≠ (block452S4 : ℝ)) :
    0 < block452V y := by
  have hcert := block452RightChunk000Certificate_eq_true
  unfold block452RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block452RightChunk000) (lo := block452RightChunk000L) (hi := block452RightChunk000R)
    (w1 := block452W1) (w2 := block452W2) (w3 := block452W3) (w4 := block452W4)
    (s1 := block452S1) (s2 := block452S2) (s3 := block452S3) (s4 := block452S4)
    hboxes hcover block452RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block452_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block452RightL : ℝ) (block452RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block452S1 : ℝ))
    (hy2ne : y ≠ (block452S2 : ℝ))
    (hy3ne : y ≠ (block452S3 : ℝ))
    (hy4ne : y ≠ (block452S4 : ℝ)) :
    0 < block452V y := by
  have hL : (block452RightChunk000L : ℝ) = (block452RightL : ℝ) := by
    norm_num [block452RightChunk000L, block452RightL]
  have hR : (block452RightChunk000R : ℝ) = (block452RightR : ℝ) := by
    norm_num [block452RightChunk000R, block452RightR]
  have hyc : y ∈ Icc (block452RightChunk000L : ℝ) (block452RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block452_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block452_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block452LeftL : ℝ) (block452LeftR : ℝ) →
    y ≠ 0 → y ≠ (block452S1 : ℝ) → y ≠ (block452S2 : ℝ) →
    y ≠ (block452S3 : ℝ) → y ≠ (block452S4 : ℝ) → 0 < block452V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block452RightL : ℝ) (block452RightR : ℝ) →
    y ≠ 0 → y ≠ (block452S1 : ℝ) → y ≠ (block452S2 : ℝ) →
    y ≠ (block452S3 : ℝ) → y ≠ (block452S4 : ℝ) → 0 < block452V y)

theorem block452_reallog_certificate_proof :
    block452_reallog_certificate := by
  exact ⟨block452_left_V_pos, block452_right_V_pos⟩

end Block452
end M1817475
end Erdos1038Lean
