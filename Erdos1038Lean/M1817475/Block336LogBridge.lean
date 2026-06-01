import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block336

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block336

open Set

def block336W1 : Rat := ((374459166683371 : Rat) / 400000000000000)
def block336W2 : Rat := ((1185354027442389 : Rat) / 25000000000000000)
def block336W3 : Rat := ((7244425675038617 : Rat) / 50000000000000000)
def block336W4 : Rat := ((6866303031122961 : Rat) / 50000000000000000)
def block336S1 : Rat := ((18174751 : Rat) / 10000000)
def block336S2 : Rat := ((511587 : Rat) / 200000)
def block336S3 : Rat := ((133565057232142857151 : Rat) / 50000000000000000000)
def block336S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block336V (y : ℝ) : ℝ :=
  ratPotential block336W1 block336W2 block336W3 block336W4 block336S1 block336S2 block336S3 block336S4 y

def block336LeftParamsCertificate : Bool :=
  allBoxesSameParams block336LeftBoxes block336W1 block336W2 block336W3 block336W4 block336S1 block336S2 block336S3 block336S4

theorem block336LeftParamsCertificate_eq_true :
    block336LeftParamsCertificate = true := by
  native_decide

theorem block336_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block336LeftL : ℝ) (block336LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block336S1 : ℝ))
    (hy2ne : y ≠ (block336S2 : ℝ))
    (hy3ne : y ≠ (block336S3 : ℝ))
    (hy4ne : y ≠ (block336S4 : ℝ)) :
    0 < block336V y := by
  have hcert := block336LeftCertificate_eq_true
  unfold block336LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block336LeftBoxes) (lo := block336LeftL) (hi := block336LeftR)
    (w1 := block336W1) (w2 := block336W2) (w3 := block336W3) (w4 := block336W4)
    (s1 := block336S1) (s2 := block336S2) (s3 := block336S3) (s4 := block336S4)
    hboxes hcover block336LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block336RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block336RightChunk000 block336W1 block336W2 block336W3 block336W4 block336S1 block336S2 block336S3 block336S4

theorem block336RightChunk000ParamsCertificate_eq_true :
    block336RightChunk000ParamsCertificate = true := by
  native_decide

theorem block336_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block336RightChunk000L : ℝ) (block336RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block336S1 : ℝ))
    (hy2ne : y ≠ (block336S2 : ℝ))
    (hy3ne : y ≠ (block336S3 : ℝ))
    (hy4ne : y ≠ (block336S4 : ℝ)) :
    0 < block336V y := by
  have hcert := block336RightChunk000Certificate_eq_true
  unfold block336RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block336RightChunk000) (lo := block336RightChunk000L) (hi := block336RightChunk000R)
    (w1 := block336W1) (w2 := block336W2) (w3 := block336W3) (w4 := block336W4)
    (s1 := block336S1) (s2 := block336S2) (s3 := block336S3) (s4 := block336S4)
    hboxes hcover block336RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block336_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block336RightL : ℝ) (block336RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block336S1 : ℝ))
    (hy2ne : y ≠ (block336S2 : ℝ))
    (hy3ne : y ≠ (block336S3 : ℝ))
    (hy4ne : y ≠ (block336S4 : ℝ)) :
    0 < block336V y := by
  have hL : (block336RightChunk000L : ℝ) = (block336RightL : ℝ) := by
    norm_num [block336RightChunk000L, block336RightL]
  have hR : (block336RightChunk000R : ℝ) = (block336RightR : ℝ) := by
    norm_num [block336RightChunk000R, block336RightR]
  have hyc : y ∈ Icc (block336RightChunk000L : ℝ) (block336RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block336_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block336_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block336LeftL : ℝ) (block336LeftR : ℝ) →
    y ≠ 0 → y ≠ (block336S1 : ℝ) → y ≠ (block336S2 : ℝ) →
    y ≠ (block336S3 : ℝ) → y ≠ (block336S4 : ℝ) → 0 < block336V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block336RightL : ℝ) (block336RightR : ℝ) →
    y ≠ 0 → y ≠ (block336S1 : ℝ) → y ≠ (block336S2 : ℝ) →
    y ≠ (block336S3 : ℝ) → y ≠ (block336S4 : ℝ) → 0 < block336V y)

theorem block336_reallog_certificate_proof :
    block336_reallog_certificate := by
  exact ⟨block336_left_V_pos, block336_right_V_pos⟩

end Block336
end M1817475
end Erdos1038Lean
