import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block518

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block518

open Set

def block518W1 : Rat := ((4204707991538631 : Rat) / 10000000000000000)
def block518W2 : Rat := (0 : Rat)
def block518W3 : Rat := ((895296798274967 : Rat) / 2000000000000000)
def block518W4 : Rat := (0 : Rat)
def block518S1 : Rat := ((18174751 : Rat) / 10000000)
def block518S2 : Rat := ((511587 : Rat) / 200000)
def block518S3 : Rat := ((130007119732142857307 : Rat) / 50000000000000000000)
def block518S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block518V (y : ℝ) : ℝ :=
  ratPotential block518W1 block518W2 block518W3 block518W4 block518S1 block518S2 block518S3 block518S4 y

def block518LeftParamsCertificate : Bool :=
  allBoxesSameParams block518LeftBoxes block518W1 block518W2 block518W3 block518W4 block518S1 block518S2 block518S3 block518S4

theorem block518LeftParamsCertificate_eq_true :
    block518LeftParamsCertificate = true := by
  native_decide

theorem block518_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block518LeftL : ℝ) (block518LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block518S1 : ℝ))
    (hy2ne : y ≠ (block518S2 : ℝ))
    (hy3ne : y ≠ (block518S3 : ℝ))
    (hy4ne : y ≠ (block518S4 : ℝ)) :
    0 < block518V y := by
  have hcert := block518LeftCertificate_eq_true
  unfold block518LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block518LeftBoxes) (lo := block518LeftL) (hi := block518LeftR)
    (w1 := block518W1) (w2 := block518W2) (w3 := block518W3) (w4 := block518W4)
    (s1 := block518S1) (s2 := block518S2) (s3 := block518S3) (s4 := block518S4)
    hboxes hcover block518LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block518RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block518RightChunk000 block518W1 block518W2 block518W3 block518W4 block518S1 block518S2 block518S3 block518S4

theorem block518RightChunk000ParamsCertificate_eq_true :
    block518RightChunk000ParamsCertificate = true := by
  native_decide

theorem block518_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block518RightChunk000L : ℝ) (block518RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block518S1 : ℝ))
    (hy2ne : y ≠ (block518S2 : ℝ))
    (hy3ne : y ≠ (block518S3 : ℝ))
    (hy4ne : y ≠ (block518S4 : ℝ)) :
    0 < block518V y := by
  have hcert := block518RightChunk000Certificate_eq_true
  unfold block518RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block518RightChunk000) (lo := block518RightChunk000L) (hi := block518RightChunk000R)
    (w1 := block518W1) (w2 := block518W2) (w3 := block518W3) (w4 := block518W4)
    (s1 := block518S1) (s2 := block518S2) (s3 := block518S3) (s4 := block518S4)
    hboxes hcover block518RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block518_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block518RightL : ℝ) (block518RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block518S1 : ℝ))
    (hy2ne : y ≠ (block518S2 : ℝ))
    (hy3ne : y ≠ (block518S3 : ℝ))
    (hy4ne : y ≠ (block518S4 : ℝ)) :
    0 < block518V y := by
  have hL : (block518RightChunk000L : ℝ) = (block518RightL : ℝ) := by
    norm_num [block518RightChunk000L, block518RightL]
  have hR : (block518RightChunk000R : ℝ) = (block518RightR : ℝ) := by
    norm_num [block518RightChunk000R, block518RightR]
  have hyc : y ∈ Icc (block518RightChunk000L : ℝ) (block518RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block518_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block518_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block518LeftL : ℝ) (block518LeftR : ℝ) →
    y ≠ 0 → y ≠ (block518S1 : ℝ) → y ≠ (block518S2 : ℝ) →
    y ≠ (block518S3 : ℝ) → y ≠ (block518S4 : ℝ) → 0 < block518V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block518RightL : ℝ) (block518RightR : ℝ) →
    y ≠ 0 → y ≠ (block518S1 : ℝ) → y ≠ (block518S2 : ℝ) →
    y ≠ (block518S3 : ℝ) → y ≠ (block518S4 : ℝ) → 0 < block518V y)

theorem block518_reallog_certificate_proof :
    block518_reallog_certificate := by
  exact ⟨block518_left_V_pos, block518_right_V_pos⟩

end Block518
end M1817475
end Erdos1038Lean
