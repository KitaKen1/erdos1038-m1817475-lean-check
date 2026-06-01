import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block116

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block116

open Set

def block116W1 : Rat := ((37674774831621 : Rat) / 15625000000000)
def block116W2 : Rat := (0 : Rat)
def block116W3 : Rat := ((1008106101196129 : Rat) / 12500000000000000)
def block116W4 : Rat := ((4202976707971439 : Rat) / 25000000000000000)
def block116S1 : Rat := ((18174751 : Rat) / 10000000)
def block116S2 : Rat := ((511587 : Rat) / 200000)
def block116S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block116S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block116V (y : ℝ) : ℝ :=
  ratPotential block116W1 block116W2 block116W3 block116W4 block116S1 block116S2 block116S3 block116S4 y

def block116LeftParamsCertificate : Bool :=
  allBoxesSameParams block116LeftBoxes block116W1 block116W2 block116W3 block116W4 block116S1 block116S2 block116S3 block116S4

theorem block116LeftParamsCertificate_eq_true :
    block116LeftParamsCertificate = true := by
  native_decide

theorem block116_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block116LeftL : ℝ) (block116LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block116S1 : ℝ))
    (hy2ne : y ≠ (block116S2 : ℝ))
    (hy3ne : y ≠ (block116S3 : ℝ))
    (hy4ne : y ≠ (block116S4 : ℝ)) :
    0 < block116V y := by
  have hcert := block116LeftCertificate_eq_true
  unfold block116LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block116LeftBoxes) (lo := block116LeftL) (hi := block116LeftR)
    (w1 := block116W1) (w2 := block116W2) (w3 := block116W3) (w4 := block116W4)
    (s1 := block116S1) (s2 := block116S2) (s3 := block116S3) (s4 := block116S4)
    hboxes hcover block116LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block116RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block116RightChunk000 block116W1 block116W2 block116W3 block116W4 block116S1 block116S2 block116S3 block116S4

theorem block116RightChunk000ParamsCertificate_eq_true :
    block116RightChunk000ParamsCertificate = true := by
  native_decide

theorem block116_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block116RightChunk000L : ℝ) (block116RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block116S1 : ℝ))
    (hy2ne : y ≠ (block116S2 : ℝ))
    (hy3ne : y ≠ (block116S3 : ℝ))
    (hy4ne : y ≠ (block116S4 : ℝ)) :
    0 < block116V y := by
  have hcert := block116RightChunk000Certificate_eq_true
  unfold block116RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block116RightChunk000) (lo := block116RightChunk000L) (hi := block116RightChunk000R)
    (w1 := block116W1) (w2 := block116W2) (w3 := block116W3) (w4 := block116W4)
    (s1 := block116S1) (s2 := block116S2) (s3 := block116S3) (s4 := block116S4)
    hboxes hcover block116RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block116_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block116RightL : ℝ) (block116RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block116S1 : ℝ))
    (hy2ne : y ≠ (block116S2 : ℝ))
    (hy3ne : y ≠ (block116S3 : ℝ))
    (hy4ne : y ≠ (block116S4 : ℝ)) :
    0 < block116V y := by
  have hL : (block116RightChunk000L : ℝ) = (block116RightL : ℝ) := by
    norm_num [block116RightChunk000L, block116RightL]
  have hR : (block116RightChunk000R : ℝ) = (block116RightR : ℝ) := by
    norm_num [block116RightChunk000R, block116RightR]
  have hyc : y ∈ Icc (block116RightChunk000L : ℝ) (block116RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block116_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block116_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block116LeftL : ℝ) (block116LeftR : ℝ) →
    y ≠ 0 → y ≠ (block116S1 : ℝ) → y ≠ (block116S2 : ℝ) →
    y ≠ (block116S3 : ℝ) → y ≠ (block116S4 : ℝ) → 0 < block116V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block116RightL : ℝ) (block116RightR : ℝ) →
    y ≠ 0 → y ≠ (block116S1 : ℝ) → y ≠ (block116S2 : ℝ) →
    y ≠ (block116S3 : ℝ) → y ≠ (block116S4 : ℝ) → 0 < block116V y)

theorem block116_reallog_certificate_proof :
    block116_reallog_certificate := by
  exact ⟨block116_left_V_pos, block116_right_V_pos⟩

end Block116
end M1817475
end Erdos1038Lean
