import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block482

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block482

open Set

def block482W1 : Rat := ((5092335615011359 : Rat) / 10000000000000000)
def block482W2 : Rat := (0 : Rat)
def block482W3 : Rat := ((381507212879133 : Rat) / 1000000000000000)
def block482W4 : Rat := ((2005741973730429 : Rat) / 50000000000000000)
def block482S1 : Rat := ((18174751 : Rat) / 10000000)
def block482S2 : Rat := ((511587 : Rat) / 200000)
def block482S3 : Rat := ((130710887589285714419 : Rat) / 50000000000000000000)
def block482S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block482V (y : ℝ) : ℝ :=
  ratPotential block482W1 block482W2 block482W3 block482W4 block482S1 block482S2 block482S3 block482S4 y

def block482LeftParamsCertificate : Bool :=
  allBoxesSameParams block482LeftBoxes block482W1 block482W2 block482W3 block482W4 block482S1 block482S2 block482S3 block482S4

theorem block482LeftParamsCertificate_eq_true :
    block482LeftParamsCertificate = true := by
  native_decide

theorem block482_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block482LeftL : ℝ) (block482LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block482S1 : ℝ))
    (hy2ne : y ≠ (block482S2 : ℝ))
    (hy3ne : y ≠ (block482S3 : ℝ))
    (hy4ne : y ≠ (block482S4 : ℝ)) :
    0 < block482V y := by
  have hcert := block482LeftCertificate_eq_true
  unfold block482LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block482LeftBoxes) (lo := block482LeftL) (hi := block482LeftR)
    (w1 := block482W1) (w2 := block482W2) (w3 := block482W3) (w4 := block482W4)
    (s1 := block482S1) (s2 := block482S2) (s3 := block482S3) (s4 := block482S4)
    hboxes hcover block482LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block482RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block482RightChunk000 block482W1 block482W2 block482W3 block482W4 block482S1 block482S2 block482S3 block482S4

theorem block482RightChunk000ParamsCertificate_eq_true :
    block482RightChunk000ParamsCertificate = true := by
  native_decide

theorem block482_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block482RightChunk000L : ℝ) (block482RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block482S1 : ℝ))
    (hy2ne : y ≠ (block482S2 : ℝ))
    (hy3ne : y ≠ (block482S3 : ℝ))
    (hy4ne : y ≠ (block482S4 : ℝ)) :
    0 < block482V y := by
  have hcert := block482RightChunk000Certificate_eq_true
  unfold block482RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block482RightChunk000) (lo := block482RightChunk000L) (hi := block482RightChunk000R)
    (w1 := block482W1) (w2 := block482W2) (w3 := block482W3) (w4 := block482W4)
    (s1 := block482S1) (s2 := block482S2) (s3 := block482S3) (s4 := block482S4)
    hboxes hcover block482RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block482_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block482RightL : ℝ) (block482RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block482S1 : ℝ))
    (hy2ne : y ≠ (block482S2 : ℝ))
    (hy3ne : y ≠ (block482S3 : ℝ))
    (hy4ne : y ≠ (block482S4 : ℝ)) :
    0 < block482V y := by
  have hL : (block482RightChunk000L : ℝ) = (block482RightL : ℝ) := by
    norm_num [block482RightChunk000L, block482RightL]
  have hR : (block482RightChunk000R : ℝ) = (block482RightR : ℝ) := by
    norm_num [block482RightChunk000R, block482RightR]
  have hyc : y ∈ Icc (block482RightChunk000L : ℝ) (block482RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block482_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block482_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block482LeftL : ℝ) (block482LeftR : ℝ) →
    y ≠ 0 → y ≠ (block482S1 : ℝ) → y ≠ (block482S2 : ℝ) →
    y ≠ (block482S3 : ℝ) → y ≠ (block482S4 : ℝ) → 0 < block482V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block482RightL : ℝ) (block482RightR : ℝ) →
    y ≠ 0 → y ≠ (block482S1 : ℝ) → y ≠ (block482S2 : ℝ) →
    y ≠ (block482S3 : ℝ) → y ≠ (block482S4 : ℝ) → 0 < block482V y)

theorem block482_reallog_certificate_proof :
    block482_reallog_certificate := by
  exact ⟨block482_left_V_pos, block482_right_V_pos⟩

end Block482
end M1817475
end Erdos1038Lean
