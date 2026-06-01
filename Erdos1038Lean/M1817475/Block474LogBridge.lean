import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block474

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block474

open Set

def block474W1 : Rat := ((5307639447990519 : Rat) / 10000000000000000)
def block474W2 : Rat := (0 : Rat)
def block474W3 : Rat := ((14382982496181 : Rat) / 39062500000000)
def block474W4 : Rat := ((23918089211554517 : Rat) / 500000000000000000)
def block474S1 : Rat := ((18174751 : Rat) / 10000000)
def block474S2 : Rat := ((511587 : Rat) / 200000)
def block474S3 : Rat := ((26173456089285714311 : Rat) / 10000000000000000000)
def block474S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block474V (y : ℝ) : ℝ :=
  ratPotential block474W1 block474W2 block474W3 block474W4 block474S1 block474S2 block474S3 block474S4 y

def block474LeftParamsCertificate : Bool :=
  allBoxesSameParams block474LeftBoxes block474W1 block474W2 block474W3 block474W4 block474S1 block474S2 block474S3 block474S4

theorem block474LeftParamsCertificate_eq_true :
    block474LeftParamsCertificate = true := by
  native_decide

theorem block474_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block474LeftL : ℝ) (block474LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block474S1 : ℝ))
    (hy2ne : y ≠ (block474S2 : ℝ))
    (hy3ne : y ≠ (block474S3 : ℝ))
    (hy4ne : y ≠ (block474S4 : ℝ)) :
    0 < block474V y := by
  have hcert := block474LeftCertificate_eq_true
  unfold block474LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block474LeftBoxes) (lo := block474LeftL) (hi := block474LeftR)
    (w1 := block474W1) (w2 := block474W2) (w3 := block474W3) (w4 := block474W4)
    (s1 := block474S1) (s2 := block474S2) (s3 := block474S3) (s4 := block474S4)
    hboxes hcover block474LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block474RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block474RightChunk000 block474W1 block474W2 block474W3 block474W4 block474S1 block474S2 block474S3 block474S4

theorem block474RightChunk000ParamsCertificate_eq_true :
    block474RightChunk000ParamsCertificate = true := by
  native_decide

theorem block474_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block474RightChunk000L : ℝ) (block474RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block474S1 : ℝ))
    (hy2ne : y ≠ (block474S2 : ℝ))
    (hy3ne : y ≠ (block474S3 : ℝ))
    (hy4ne : y ≠ (block474S4 : ℝ)) :
    0 < block474V y := by
  have hcert := block474RightChunk000Certificate_eq_true
  unfold block474RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block474RightChunk000) (lo := block474RightChunk000L) (hi := block474RightChunk000R)
    (w1 := block474W1) (w2 := block474W2) (w3 := block474W3) (w4 := block474W4)
    (s1 := block474S1) (s2 := block474S2) (s3 := block474S3) (s4 := block474S4)
    hboxes hcover block474RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block474_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block474RightL : ℝ) (block474RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block474S1 : ℝ))
    (hy2ne : y ≠ (block474S2 : ℝ))
    (hy3ne : y ≠ (block474S3 : ℝ))
    (hy4ne : y ≠ (block474S4 : ℝ)) :
    0 < block474V y := by
  have hL : (block474RightChunk000L : ℝ) = (block474RightL : ℝ) := by
    norm_num [block474RightChunk000L, block474RightL]
  have hR : (block474RightChunk000R : ℝ) = (block474RightR : ℝ) := by
    norm_num [block474RightChunk000R, block474RightR]
  have hyc : y ∈ Icc (block474RightChunk000L : ℝ) (block474RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block474_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block474_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block474LeftL : ℝ) (block474LeftR : ℝ) →
    y ≠ 0 → y ≠ (block474S1 : ℝ) → y ≠ (block474S2 : ℝ) →
    y ≠ (block474S3 : ℝ) → y ≠ (block474S4 : ℝ) → 0 < block474V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block474RightL : ℝ) (block474RightR : ℝ) →
    y ≠ 0 → y ≠ (block474S1 : ℝ) → y ≠ (block474S2 : ℝ) →
    y ≠ (block474S3 : ℝ) → y ≠ (block474S4 : ℝ) → 0 < block474V y)

theorem block474_reallog_certificate_proof :
    block474_reallog_certificate := by
  exact ⟨block474_left_V_pos, block474_right_V_pos⟩

end Block474
end M1817475
end Erdos1038Lean
