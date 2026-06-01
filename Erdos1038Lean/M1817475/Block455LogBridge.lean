import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block455

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block455

open Set

def block455W1 : Rat := ((1458174220954121 : Rat) / 2500000000000000)
def block455W2 : Rat := (0 : Rat)
def block455W3 : Rat := ((679637343555531 : Rat) / 2000000000000000)
def block455W4 : Rat := ((635636197684997 : Rat) / 10000000000000000)
def block455S1 : Rat := ((18174751 : Rat) / 10000000)
def block455S2 : Rat := ((511587 : Rat) / 200000)
def block455S3 : Rat := ((131238713482142857253 : Rat) / 50000000000000000000)
def block455S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block455V (y : ℝ) : ℝ :=
  ratPotential block455W1 block455W2 block455W3 block455W4 block455S1 block455S2 block455S3 block455S4 y

def block455LeftParamsCertificate : Bool :=
  allBoxesSameParams block455LeftBoxes block455W1 block455W2 block455W3 block455W4 block455S1 block455S2 block455S3 block455S4

theorem block455LeftParamsCertificate_eq_true :
    block455LeftParamsCertificate = true := by
  native_decide

theorem block455_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block455LeftL : ℝ) (block455LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block455S1 : ℝ))
    (hy2ne : y ≠ (block455S2 : ℝ))
    (hy3ne : y ≠ (block455S3 : ℝ))
    (hy4ne : y ≠ (block455S4 : ℝ)) :
    0 < block455V y := by
  have hcert := block455LeftCertificate_eq_true
  unfold block455LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block455LeftBoxes) (lo := block455LeftL) (hi := block455LeftR)
    (w1 := block455W1) (w2 := block455W2) (w3 := block455W3) (w4 := block455W4)
    (s1 := block455S1) (s2 := block455S2) (s3 := block455S3) (s4 := block455S4)
    hboxes hcover block455LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block455RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block455RightChunk000 block455W1 block455W2 block455W3 block455W4 block455S1 block455S2 block455S3 block455S4

theorem block455RightChunk000ParamsCertificate_eq_true :
    block455RightChunk000ParamsCertificate = true := by
  native_decide

theorem block455_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block455RightChunk000L : ℝ) (block455RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block455S1 : ℝ))
    (hy2ne : y ≠ (block455S2 : ℝ))
    (hy3ne : y ≠ (block455S3 : ℝ))
    (hy4ne : y ≠ (block455S4 : ℝ)) :
    0 < block455V y := by
  have hcert := block455RightChunk000Certificate_eq_true
  unfold block455RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block455RightChunk000) (lo := block455RightChunk000L) (hi := block455RightChunk000R)
    (w1 := block455W1) (w2 := block455W2) (w3 := block455W3) (w4 := block455W4)
    (s1 := block455S1) (s2 := block455S2) (s3 := block455S3) (s4 := block455S4)
    hboxes hcover block455RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block455_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block455RightL : ℝ) (block455RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block455S1 : ℝ))
    (hy2ne : y ≠ (block455S2 : ℝ))
    (hy3ne : y ≠ (block455S3 : ℝ))
    (hy4ne : y ≠ (block455S4 : ℝ)) :
    0 < block455V y := by
  have hL : (block455RightChunk000L : ℝ) = (block455RightL : ℝ) := by
    norm_num [block455RightChunk000L, block455RightL]
  have hR : (block455RightChunk000R : ℝ) = (block455RightR : ℝ) := by
    norm_num [block455RightChunk000R, block455RightR]
  have hyc : y ∈ Icc (block455RightChunk000L : ℝ) (block455RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block455_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block455_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block455LeftL : ℝ) (block455LeftR : ℝ) →
    y ≠ 0 → y ≠ (block455S1 : ℝ) → y ≠ (block455S2 : ℝ) →
    y ≠ (block455S3 : ℝ) → y ≠ (block455S4 : ℝ) → 0 < block455V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block455RightL : ℝ) (block455RightR : ℝ) →
    y ≠ 0 → y ≠ (block455S1 : ℝ) → y ≠ (block455S2 : ℝ) →
    y ≠ (block455S3 : ℝ) → y ≠ (block455S4 : ℝ) → 0 < block455V y)

theorem block455_reallog_certificate_proof :
    block455_reallog_certificate := by
  exact ⟨block455_left_V_pos, block455_right_V_pos⟩

end Block455
end M1817475
end Erdos1038Lean
