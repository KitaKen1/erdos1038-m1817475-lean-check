import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block448

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block448

open Set

def block448W1 : Rat := ((1507917735391339 : Rat) / 2500000000000000)
def block448W2 : Rat := (0 : Rat)
def block448W3 : Rat := ((33036499346675313 : Rat) / 100000000000000000)
def block448W4 : Rat := ((3426982236021321 : Rat) / 50000000000000000)
def block448S1 : Rat := ((18174751 : Rat) / 10000000)
def block448S2 : Rat := ((511587 : Rat) / 200000)
def block448S3 : Rat := ((131375557232142857247 : Rat) / 50000000000000000000)
def block448S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block448V (y : ℝ) : ℝ :=
  ratPotential block448W1 block448W2 block448W3 block448W4 block448S1 block448S2 block448S3 block448S4 y

def block448LeftParamsCertificate : Bool :=
  allBoxesSameParams block448LeftBoxes block448W1 block448W2 block448W3 block448W4 block448S1 block448S2 block448S3 block448S4

theorem block448LeftParamsCertificate_eq_true :
    block448LeftParamsCertificate = true := by
  native_decide

theorem block448_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block448LeftL : ℝ) (block448LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block448S1 : ℝ))
    (hy2ne : y ≠ (block448S2 : ℝ))
    (hy3ne : y ≠ (block448S3 : ℝ))
    (hy4ne : y ≠ (block448S4 : ℝ)) :
    0 < block448V y := by
  have hcert := block448LeftCertificate_eq_true
  unfold block448LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block448LeftBoxes) (lo := block448LeftL) (hi := block448LeftR)
    (w1 := block448W1) (w2 := block448W2) (w3 := block448W3) (w4 := block448W4)
    (s1 := block448S1) (s2 := block448S2) (s3 := block448S3) (s4 := block448S4)
    hboxes hcover block448LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block448RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block448RightChunk000 block448W1 block448W2 block448W3 block448W4 block448S1 block448S2 block448S3 block448S4

theorem block448RightChunk000ParamsCertificate_eq_true :
    block448RightChunk000ParamsCertificate = true := by
  native_decide

theorem block448_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block448RightChunk000L : ℝ) (block448RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block448S1 : ℝ))
    (hy2ne : y ≠ (block448S2 : ℝ))
    (hy3ne : y ≠ (block448S3 : ℝ))
    (hy4ne : y ≠ (block448S4 : ℝ)) :
    0 < block448V y := by
  have hcert := block448RightChunk000Certificate_eq_true
  unfold block448RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block448RightChunk000) (lo := block448RightChunk000L) (hi := block448RightChunk000R)
    (w1 := block448W1) (w2 := block448W2) (w3 := block448W3) (w4 := block448W4)
    (s1 := block448S1) (s2 := block448S2) (s3 := block448S3) (s4 := block448S4)
    hboxes hcover block448RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block448_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block448RightL : ℝ) (block448RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block448S1 : ℝ))
    (hy2ne : y ≠ (block448S2 : ℝ))
    (hy3ne : y ≠ (block448S3 : ℝ))
    (hy4ne : y ≠ (block448S4 : ℝ)) :
    0 < block448V y := by
  have hL : (block448RightChunk000L : ℝ) = (block448RightL : ℝ) := by
    norm_num [block448RightChunk000L, block448RightL]
  have hR : (block448RightChunk000R : ℝ) = (block448RightR : ℝ) := by
    norm_num [block448RightChunk000R, block448RightR]
  have hyc : y ∈ Icc (block448RightChunk000L : ℝ) (block448RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block448_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block448_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block448LeftL : ℝ) (block448LeftR : ℝ) →
    y ≠ 0 → y ≠ (block448S1 : ℝ) → y ≠ (block448S2 : ℝ) →
    y ≠ (block448S3 : ℝ) → y ≠ (block448S4 : ℝ) → 0 < block448V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block448RightL : ℝ) (block448RightR : ℝ) →
    y ≠ 0 → y ≠ (block448S1 : ℝ) → y ≠ (block448S2 : ℝ) →
    y ≠ (block448S3 : ℝ) → y ≠ (block448S4 : ℝ) → 0 < block448V y)

theorem block448_reallog_certificate_proof :
    block448_reallog_certificate := by
  exact ⟨block448_left_V_pos, block448_right_V_pos⟩

end Block448
end M1817475
end Erdos1038Lean
