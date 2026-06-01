import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block398

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block398

open Set

def block398W1 : Rat := ((7058084947835509 : Rat) / 10000000000000000)
def block398W2 : Rat := (0 : Rat)
def block398W3 : Rat := ((3738894032016001 : Rat) / 10000000000000000)
def block398W4 : Rat := (0 : Rat)
def block398S1 : Rat := ((18174751 : Rat) / 10000000)
def block398S2 : Rat := ((511587 : Rat) / 200000)
def block398S3 : Rat := ((133095878660714285743 : Rat) / 50000000000000000000)
def block398S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block398V (y : ℝ) : ℝ :=
  ratPotential block398W1 block398W2 block398W3 block398W4 block398S1 block398S2 block398S3 block398S4 y

def block398LeftParamsCertificate : Bool :=
  allBoxesSameParams block398LeftBoxes block398W1 block398W2 block398W3 block398W4 block398S1 block398S2 block398S3 block398S4

theorem block398LeftParamsCertificate_eq_true :
    block398LeftParamsCertificate = true := by
  native_decide

theorem block398_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block398LeftL : ℝ) (block398LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block398S1 : ℝ))
    (hy2ne : y ≠ (block398S2 : ℝ))
    (hy3ne : y ≠ (block398S3 : ℝ))
    (hy4ne : y ≠ (block398S4 : ℝ)) :
    0 < block398V y := by
  have hcert := block398LeftCertificate_eq_true
  unfold block398LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block398LeftBoxes) (lo := block398LeftL) (hi := block398LeftR)
    (w1 := block398W1) (w2 := block398W2) (w3 := block398W3) (w4 := block398W4)
    (s1 := block398S1) (s2 := block398S2) (s3 := block398S3) (s4 := block398S4)
    hboxes hcover block398LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block398RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block398RightChunk000 block398W1 block398W2 block398W3 block398W4 block398S1 block398S2 block398S3 block398S4

theorem block398RightChunk000ParamsCertificate_eq_true :
    block398RightChunk000ParamsCertificate = true := by
  native_decide

theorem block398_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block398RightChunk000L : ℝ) (block398RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block398S1 : ℝ))
    (hy2ne : y ≠ (block398S2 : ℝ))
    (hy3ne : y ≠ (block398S3 : ℝ))
    (hy4ne : y ≠ (block398S4 : ℝ)) :
    0 < block398V y := by
  have hcert := block398RightChunk000Certificate_eq_true
  unfold block398RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block398RightChunk000) (lo := block398RightChunk000L) (hi := block398RightChunk000R)
    (w1 := block398W1) (w2 := block398W2) (w3 := block398W3) (w4 := block398W4)
    (s1 := block398S1) (s2 := block398S2) (s3 := block398S3) (s4 := block398S4)
    hboxes hcover block398RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block398_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block398RightL : ℝ) (block398RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block398S1 : ℝ))
    (hy2ne : y ≠ (block398S2 : ℝ))
    (hy3ne : y ≠ (block398S3 : ℝ))
    (hy4ne : y ≠ (block398S4 : ℝ)) :
    0 < block398V y := by
  have hL : (block398RightChunk000L : ℝ) = (block398RightL : ℝ) := by
    norm_num [block398RightChunk000L, block398RightL]
  have hR : (block398RightChunk000R : ℝ) = (block398RightR : ℝ) := by
    norm_num [block398RightChunk000R, block398RightR]
  have hyc : y ∈ Icc (block398RightChunk000L : ℝ) (block398RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block398_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block398_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block398LeftL : ℝ) (block398LeftR : ℝ) →
    y ≠ 0 → y ≠ (block398S1 : ℝ) → y ≠ (block398S2 : ℝ) →
    y ≠ (block398S3 : ℝ) → y ≠ (block398S4 : ℝ) → 0 < block398V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block398RightL : ℝ) (block398RightR : ℝ) →
    y ≠ 0 → y ≠ (block398S1 : ℝ) → y ≠ (block398S2 : ℝ) →
    y ≠ (block398S3 : ℝ) → y ≠ (block398S4 : ℝ) → 0 < block398V y)

theorem block398_reallog_certificate_proof :
    block398_reallog_certificate := by
  exact ⟨block398_left_V_pos, block398_right_V_pos⟩

end Block398
end M1817475
end Erdos1038Lean
