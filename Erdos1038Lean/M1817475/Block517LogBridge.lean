import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block517

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block517

open Set

def block517W1 : Rat := ((21077301643434687 : Rat) / 50000000000000000)
def block517W2 : Rat := (0 : Rat)
def block517W3 : Rat := ((2795440333953891 : Rat) / 6250000000000000)
def block517W4 : Rat := (0 : Rat)
def block517S1 : Rat := ((18174751 : Rat) / 10000000)
def block517S2 : Rat := ((511587 : Rat) / 200000)
def block517S3 : Rat := ((130026668839285714449 : Rat) / 50000000000000000000)
def block517S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block517V (y : ℝ) : ℝ :=
  ratPotential block517W1 block517W2 block517W3 block517W4 block517S1 block517S2 block517S3 block517S4 y

def block517LeftParamsCertificate : Bool :=
  allBoxesSameParams block517LeftBoxes block517W1 block517W2 block517W3 block517W4 block517S1 block517S2 block517S3 block517S4

theorem block517LeftParamsCertificate_eq_true :
    block517LeftParamsCertificate = true := by
  native_decide

theorem block517_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block517LeftL : ℝ) (block517LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block517S1 : ℝ))
    (hy2ne : y ≠ (block517S2 : ℝ))
    (hy3ne : y ≠ (block517S3 : ℝ))
    (hy4ne : y ≠ (block517S4 : ℝ)) :
    0 < block517V y := by
  have hcert := block517LeftCertificate_eq_true
  unfold block517LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block517LeftBoxes) (lo := block517LeftL) (hi := block517LeftR)
    (w1 := block517W1) (w2 := block517W2) (w3 := block517W3) (w4 := block517W4)
    (s1 := block517S1) (s2 := block517S2) (s3 := block517S3) (s4 := block517S4)
    hboxes hcover block517LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block517RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block517RightChunk000 block517W1 block517W2 block517W3 block517W4 block517S1 block517S2 block517S3 block517S4

theorem block517RightChunk000ParamsCertificate_eq_true :
    block517RightChunk000ParamsCertificate = true := by
  native_decide

theorem block517_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block517RightChunk000L : ℝ) (block517RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block517S1 : ℝ))
    (hy2ne : y ≠ (block517S2 : ℝ))
    (hy3ne : y ≠ (block517S3 : ℝ))
    (hy4ne : y ≠ (block517S4 : ℝ)) :
    0 < block517V y := by
  have hcert := block517RightChunk000Certificate_eq_true
  unfold block517RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block517RightChunk000) (lo := block517RightChunk000L) (hi := block517RightChunk000R)
    (w1 := block517W1) (w2 := block517W2) (w3 := block517W3) (w4 := block517W4)
    (s1 := block517S1) (s2 := block517S2) (s3 := block517S3) (s4 := block517S4)
    hboxes hcover block517RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block517_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block517RightL : ℝ) (block517RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block517S1 : ℝ))
    (hy2ne : y ≠ (block517S2 : ℝ))
    (hy3ne : y ≠ (block517S3 : ℝ))
    (hy4ne : y ≠ (block517S4 : ℝ)) :
    0 < block517V y := by
  have hL : (block517RightChunk000L : ℝ) = (block517RightL : ℝ) := by
    norm_num [block517RightChunk000L, block517RightL]
  have hR : (block517RightChunk000R : ℝ) = (block517RightR : ℝ) := by
    norm_num [block517RightChunk000R, block517RightR]
  have hyc : y ∈ Icc (block517RightChunk000L : ℝ) (block517RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block517_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block517_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block517LeftL : ℝ) (block517LeftR : ℝ) →
    y ≠ 0 → y ≠ (block517S1 : ℝ) → y ≠ (block517S2 : ℝ) →
    y ≠ (block517S3 : ℝ) → y ≠ (block517S4 : ℝ) → 0 < block517V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block517RightL : ℝ) (block517RightR : ℝ) →
    y ≠ 0 → y ≠ (block517S1 : ℝ) → y ≠ (block517S2 : ℝ) →
    y ≠ (block517S3 : ℝ) → y ≠ (block517S4 : ℝ) → 0 < block517V y)

theorem block517_reallog_certificate_proof :
    block517_reallog_certificate := by
  exact ⟨block517_left_V_pos, block517_right_V_pos⟩

end Block517
end M1817475
end Erdos1038Lean
