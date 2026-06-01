import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block557

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block557

open Set

def block557W1 : Rat := ((3809865918733231 : Rat) / 10000000000000000)
def block557W2 : Rat := (0 : Rat)
def block557W3 : Rat := ((1849926851034541 : Rat) / 4000000000000000)
def block557W4 : Rat := (0 : Rat)
def block557S1 : Rat := ((18174751 : Rat) / 10000000)
def block557S2 : Rat := ((511587 : Rat) / 200000)
def block557S3 : Rat := ((129244704553571428769 : Rat) / 50000000000000000000)
def block557S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block557V (y : ℝ) : ℝ :=
  ratPotential block557W1 block557W2 block557W3 block557W4 block557S1 block557S2 block557S3 block557S4 y

def block557LeftParamsCertificate : Bool :=
  allBoxesSameParams block557LeftBoxes block557W1 block557W2 block557W3 block557W4 block557S1 block557S2 block557S3 block557S4

theorem block557LeftParamsCertificate_eq_true :
    block557LeftParamsCertificate = true := by
  native_decide

theorem block557_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block557LeftL : ℝ) (block557LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block557S1 : ℝ))
    (hy2ne : y ≠ (block557S2 : ℝ))
    (hy3ne : y ≠ (block557S3 : ℝ))
    (hy4ne : y ≠ (block557S4 : ℝ)) :
    0 < block557V y := by
  have hcert := block557LeftCertificate_eq_true
  unfold block557LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block557LeftBoxes) (lo := block557LeftL) (hi := block557LeftR)
    (w1 := block557W1) (w2 := block557W2) (w3 := block557W3) (w4 := block557W4)
    (s1 := block557S1) (s2 := block557S2) (s3 := block557S3) (s4 := block557S4)
    hboxes hcover block557LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block557RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block557RightChunk000 block557W1 block557W2 block557W3 block557W4 block557S1 block557S2 block557S3 block557S4

theorem block557RightChunk000ParamsCertificate_eq_true :
    block557RightChunk000ParamsCertificate = true := by
  native_decide

theorem block557_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block557RightChunk000L : ℝ) (block557RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block557S1 : ℝ))
    (hy2ne : y ≠ (block557S2 : ℝ))
    (hy3ne : y ≠ (block557S3 : ℝ))
    (hy4ne : y ≠ (block557S4 : ℝ)) :
    0 < block557V y := by
  have hcert := block557RightChunk000Certificate_eq_true
  unfold block557RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block557RightChunk000) (lo := block557RightChunk000L) (hi := block557RightChunk000R)
    (w1 := block557W1) (w2 := block557W2) (w3 := block557W3) (w4 := block557W4)
    (s1 := block557S1) (s2 := block557S2) (s3 := block557S3) (s4 := block557S4)
    hboxes hcover block557RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block557_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block557RightL : ℝ) (block557RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block557S1 : ℝ))
    (hy2ne : y ≠ (block557S2 : ℝ))
    (hy3ne : y ≠ (block557S3 : ℝ))
    (hy4ne : y ≠ (block557S4 : ℝ)) :
    0 < block557V y := by
  have hL : (block557RightChunk000L : ℝ) = (block557RightL : ℝ) := by
    norm_num [block557RightChunk000L, block557RightL]
  have hR : (block557RightChunk000R : ℝ) = (block557RightR : ℝ) := by
    norm_num [block557RightChunk000R, block557RightR]
  have hyc : y ∈ Icc (block557RightChunk000L : ℝ) (block557RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block557_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block557_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block557LeftL : ℝ) (block557LeftR : ℝ) →
    y ≠ 0 → y ≠ (block557S1 : ℝ) → y ≠ (block557S2 : ℝ) →
    y ≠ (block557S3 : ℝ) → y ≠ (block557S4 : ℝ) → 0 < block557V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block557RightL : ℝ) (block557RightR : ℝ) →
    y ≠ 0 → y ≠ (block557S1 : ℝ) → y ≠ (block557S2 : ℝ) →
    y ≠ (block557S3 : ℝ) → y ≠ (block557S4 : ℝ) → 0 < block557V y)

theorem block557_reallog_certificate_proof :
    block557_reallog_certificate := by
  exact ⟨block557_left_V_pos, block557_right_V_pos⟩

end Block557
end M1817475
end Erdos1038Lean
