import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block152

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block152

open Set

def block152W1 : Rat := ((431559276664557 : Rat) / 200000000000000)
def block152W2 : Rat := (0 : Rat)
def block152W3 : Rat := ((4253164309849669 : Rat) / 25000000000000000)
def block152W4 : Rat := ((1035096017053033 : Rat) / 12500000000000000)
def block152S1 : Rat := ((18174751 : Rat) / 10000000)
def block152S2 : Rat := ((511587 : Rat) / 200000)
def block152S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block152S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block152V (y : ℝ) : ℝ :=
  ratPotential block152W1 block152W2 block152W3 block152W4 block152S1 block152S2 block152S3 block152S4 y

def block152LeftParamsCertificate : Bool :=
  allBoxesSameParams block152LeftBoxes block152W1 block152W2 block152W3 block152W4 block152S1 block152S2 block152S3 block152S4

theorem block152LeftParamsCertificate_eq_true :
    block152LeftParamsCertificate = true := by
  native_decide

theorem block152_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block152LeftL : ℝ) (block152LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block152S1 : ℝ))
    (hy2ne : y ≠ (block152S2 : ℝ))
    (hy3ne : y ≠ (block152S3 : ℝ))
    (hy4ne : y ≠ (block152S4 : ℝ)) :
    0 < block152V y := by
  have hcert := block152LeftCertificate_eq_true
  unfold block152LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block152LeftBoxes) (lo := block152LeftL) (hi := block152LeftR)
    (w1 := block152W1) (w2 := block152W2) (w3 := block152W3) (w4 := block152W4)
    (s1 := block152S1) (s2 := block152S2) (s3 := block152S3) (s4 := block152S4)
    hboxes hcover block152LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block152RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block152RightChunk000 block152W1 block152W2 block152W3 block152W4 block152S1 block152S2 block152S3 block152S4

theorem block152RightChunk000ParamsCertificate_eq_true :
    block152RightChunk000ParamsCertificate = true := by
  native_decide

theorem block152_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block152RightChunk000L : ℝ) (block152RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block152S1 : ℝ))
    (hy2ne : y ≠ (block152S2 : ℝ))
    (hy3ne : y ≠ (block152S3 : ℝ))
    (hy4ne : y ≠ (block152S4 : ℝ)) :
    0 < block152V y := by
  have hcert := block152RightChunk000Certificate_eq_true
  unfold block152RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block152RightChunk000) (lo := block152RightChunk000L) (hi := block152RightChunk000R)
    (w1 := block152W1) (w2 := block152W2) (w3 := block152W3) (w4 := block152W4)
    (s1 := block152S1) (s2 := block152S2) (s3 := block152S3) (s4 := block152S4)
    hboxes hcover block152RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block152_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block152RightL : ℝ) (block152RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block152S1 : ℝ))
    (hy2ne : y ≠ (block152S2 : ℝ))
    (hy3ne : y ≠ (block152S3 : ℝ))
    (hy4ne : y ≠ (block152S4 : ℝ)) :
    0 < block152V y := by
  have hL : (block152RightChunk000L : ℝ) = (block152RightL : ℝ) := by
    norm_num [block152RightChunk000L, block152RightL]
  have hR : (block152RightChunk000R : ℝ) = (block152RightR : ℝ) := by
    norm_num [block152RightChunk000R, block152RightR]
  have hyc : y ∈ Icc (block152RightChunk000L : ℝ) (block152RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block152_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block152_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block152LeftL : ℝ) (block152LeftR : ℝ) →
    y ≠ 0 → y ≠ (block152S1 : ℝ) → y ≠ (block152S2 : ℝ) →
    y ≠ (block152S3 : ℝ) → y ≠ (block152S4 : ℝ) → 0 < block152V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block152RightL : ℝ) (block152RightR : ℝ) →
    y ≠ 0 → y ≠ (block152S1 : ℝ) → y ≠ (block152S2 : ℝ) →
    y ≠ (block152S3 : ℝ) → y ≠ (block152S4 : ℝ) → 0 < block152V y)

theorem block152_reallog_certificate_proof :
    block152_reallog_certificate := by
  exact ⟨block152_left_V_pos, block152_right_V_pos⟩

end Block152
end M1817475
end Erdos1038Lean
