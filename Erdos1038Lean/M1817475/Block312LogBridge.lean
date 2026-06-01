import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block312

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block312

open Set

def block312W1 : Rat := ((1929213235101173 : Rat) / 2000000000000000)
def block312W2 : Rat := ((2386235277397811 : Rat) / 40000000000000000)
def block312W3 : Rat := ((6502177380052239 : Rat) / 25000000000000000)
def block312W4 : Rat := (0 : Rat)
def block312S1 : Rat := ((18174751 : Rat) / 10000000)
def block312S2 : Rat := ((511587 : Rat) / 200000)
def block312S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block312S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block312V (y : ℝ) : ℝ :=
  ratPotential block312W1 block312W2 block312W3 block312W4 block312S1 block312S2 block312S3 block312S4 y

def block312LeftParamsCertificate : Bool :=
  allBoxesSameParams block312LeftBoxes block312W1 block312W2 block312W3 block312W4 block312S1 block312S2 block312S3 block312S4

theorem block312LeftParamsCertificate_eq_true :
    block312LeftParamsCertificate = true := by
  native_decide

theorem block312_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block312LeftL : ℝ) (block312LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block312S1 : ℝ))
    (hy2ne : y ≠ (block312S2 : ℝ))
    (hy3ne : y ≠ (block312S3 : ℝ))
    (hy4ne : y ≠ (block312S4 : ℝ)) :
    0 < block312V y := by
  have hcert := block312LeftCertificate_eq_true
  unfold block312LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block312LeftBoxes) (lo := block312LeftL) (hi := block312LeftR)
    (w1 := block312W1) (w2 := block312W2) (w3 := block312W3) (w4 := block312W4)
    (s1 := block312S1) (s2 := block312S2) (s3 := block312S3) (s4 := block312S4)
    hboxes hcover block312LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block312RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block312RightChunk000 block312W1 block312W2 block312W3 block312W4 block312S1 block312S2 block312S3 block312S4

theorem block312RightChunk000ParamsCertificate_eq_true :
    block312RightChunk000ParamsCertificate = true := by
  native_decide

theorem block312_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block312RightChunk000L : ℝ) (block312RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block312S1 : ℝ))
    (hy2ne : y ≠ (block312S2 : ℝ))
    (hy3ne : y ≠ (block312S3 : ℝ))
    (hy4ne : y ≠ (block312S4 : ℝ)) :
    0 < block312V y := by
  have hcert := block312RightChunk000Certificate_eq_true
  unfold block312RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block312RightChunk000) (lo := block312RightChunk000L) (hi := block312RightChunk000R)
    (w1 := block312W1) (w2 := block312W2) (w3 := block312W3) (w4 := block312W4)
    (s1 := block312S1) (s2 := block312S2) (s3 := block312S3) (s4 := block312S4)
    hboxes hcover block312RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block312_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block312RightL : ℝ) (block312RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block312S1 : ℝ))
    (hy2ne : y ≠ (block312S2 : ℝ))
    (hy3ne : y ≠ (block312S3 : ℝ))
    (hy4ne : y ≠ (block312S4 : ℝ)) :
    0 < block312V y := by
  have hL : (block312RightChunk000L : ℝ) = (block312RightL : ℝ) := by
    norm_num [block312RightChunk000L, block312RightL]
  have hR : (block312RightChunk000R : ℝ) = (block312RightR : ℝ) := by
    norm_num [block312RightChunk000R, block312RightR]
  have hyc : y ∈ Icc (block312RightChunk000L : ℝ) (block312RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block312_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block312_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block312LeftL : ℝ) (block312LeftR : ℝ) →
    y ≠ 0 → y ≠ (block312S1 : ℝ) → y ≠ (block312S2 : ℝ) →
    y ≠ (block312S3 : ℝ) → y ≠ (block312S4 : ℝ) → 0 < block312V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block312RightL : ℝ) (block312RightR : ℝ) →
    y ≠ 0 → y ≠ (block312S1 : ℝ) → y ≠ (block312S2 : ℝ) →
    y ≠ (block312S3 : ℝ) → y ≠ (block312S4 : ℝ) → 0 < block312V y)

theorem block312_reallog_certificate_proof :
    block312_reallog_certificate := by
  exact ⟨block312_left_V_pos, block312_right_V_pos⟩

end Block312
end M1817475
end Erdos1038Lean
