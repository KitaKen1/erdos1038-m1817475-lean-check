import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block318

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block318

open Set

def block318W1 : Rat := ((236771753376129 : Rat) / 250000000000000)
def block318W2 : Rat := ((661676079206527 : Rat) / 10000000000000000)
def block318W3 : Rat := ((12724543605544167 : Rat) / 50000000000000000)
def block318W4 : Rat := (0 : Rat)
def block318S1 : Rat := ((18174751 : Rat) / 10000000)
def block318S2 : Rat := ((511587 : Rat) / 200000)
def block318S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block318S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block318V (y : ℝ) : ℝ :=
  ratPotential block318W1 block318W2 block318W3 block318W4 block318S1 block318S2 block318S3 block318S4 y

def block318LeftParamsCertificate : Bool :=
  allBoxesSameParams block318LeftBoxes block318W1 block318W2 block318W3 block318W4 block318S1 block318S2 block318S3 block318S4

theorem block318LeftParamsCertificate_eq_true :
    block318LeftParamsCertificate = true := by
  native_decide

theorem block318_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block318LeftL : ℝ) (block318LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block318S1 : ℝ))
    (hy2ne : y ≠ (block318S2 : ℝ))
    (hy3ne : y ≠ (block318S3 : ℝ))
    (hy4ne : y ≠ (block318S4 : ℝ)) :
    0 < block318V y := by
  have hcert := block318LeftCertificate_eq_true
  unfold block318LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block318LeftBoxes) (lo := block318LeftL) (hi := block318LeftR)
    (w1 := block318W1) (w2 := block318W2) (w3 := block318W3) (w4 := block318W4)
    (s1 := block318S1) (s2 := block318S2) (s3 := block318S3) (s4 := block318S4)
    hboxes hcover block318LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block318RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block318RightChunk000 block318W1 block318W2 block318W3 block318W4 block318S1 block318S2 block318S3 block318S4

theorem block318RightChunk000ParamsCertificate_eq_true :
    block318RightChunk000ParamsCertificate = true := by
  native_decide

theorem block318_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block318RightChunk000L : ℝ) (block318RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block318S1 : ℝ))
    (hy2ne : y ≠ (block318S2 : ℝ))
    (hy3ne : y ≠ (block318S3 : ℝ))
    (hy4ne : y ≠ (block318S4 : ℝ)) :
    0 < block318V y := by
  have hcert := block318RightChunk000Certificate_eq_true
  unfold block318RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block318RightChunk000) (lo := block318RightChunk000L) (hi := block318RightChunk000R)
    (w1 := block318W1) (w2 := block318W2) (w3 := block318W3) (w4 := block318W4)
    (s1 := block318S1) (s2 := block318S2) (s3 := block318S3) (s4 := block318S4)
    hboxes hcover block318RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block318_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block318RightL : ℝ) (block318RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block318S1 : ℝ))
    (hy2ne : y ≠ (block318S2 : ℝ))
    (hy3ne : y ≠ (block318S3 : ℝ))
    (hy4ne : y ≠ (block318S4 : ℝ)) :
    0 < block318V y := by
  have hL : (block318RightChunk000L : ℝ) = (block318RightL : ℝ) := by
    norm_num [block318RightChunk000L, block318RightL]
  have hR : (block318RightChunk000R : ℝ) = (block318RightR : ℝ) := by
    norm_num [block318RightChunk000R, block318RightR]
  have hyc : y ∈ Icc (block318RightChunk000L : ℝ) (block318RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block318_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block318_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block318LeftL : ℝ) (block318LeftR : ℝ) →
    y ≠ 0 → y ≠ (block318S1 : ℝ) → y ≠ (block318S2 : ℝ) →
    y ≠ (block318S3 : ℝ) → y ≠ (block318S4 : ℝ) → 0 < block318V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block318RightL : ℝ) (block318RightR : ℝ) →
    y ≠ 0 → y ≠ (block318S1 : ℝ) → y ≠ (block318S2 : ℝ) →
    y ≠ (block318S3 : ℝ) → y ≠ (block318S4 : ℝ) → 0 < block318V y)

theorem block318_reallog_certificate_proof :
    block318_reallog_certificate := by
  exact ⟨block318_left_V_pos, block318_right_V_pos⟩

end Block318
end M1817475
end Erdos1038Lean
