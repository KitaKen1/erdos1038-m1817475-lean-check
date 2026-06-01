import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block338

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block338

open Set

def block338W1 : Rat := ((2329232673137199 : Rat) / 2500000000000000)
def block338W2 : Rat := ((47492180344329 : Rat) / 1000000000000000)
def block338W3 : Rat := ((7268655608047789 : Rat) / 50000000000000000)
def block338W4 : Rat := ((2750185185162643 : Rat) / 20000000000000000)
def block338S1 : Rat := ((18174751 : Rat) / 10000000)
def block338S2 : Rat := ((511587 : Rat) / 200000)
def block338S3 : Rat := ((133525959017857142867 : Rat) / 50000000000000000000)
def block338S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block338V (y : ℝ) : ℝ :=
  ratPotential block338W1 block338W2 block338W3 block338W4 block338S1 block338S2 block338S3 block338S4 y

def block338LeftParamsCertificate : Bool :=
  allBoxesSameParams block338LeftBoxes block338W1 block338W2 block338W3 block338W4 block338S1 block338S2 block338S3 block338S4

theorem block338LeftParamsCertificate_eq_true :
    block338LeftParamsCertificate = true := by
  native_decide

theorem block338_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block338LeftL : ℝ) (block338LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block338S1 : ℝ))
    (hy2ne : y ≠ (block338S2 : ℝ))
    (hy3ne : y ≠ (block338S3 : ℝ))
    (hy4ne : y ≠ (block338S4 : ℝ)) :
    0 < block338V y := by
  have hcert := block338LeftCertificate_eq_true
  unfold block338LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block338LeftBoxes) (lo := block338LeftL) (hi := block338LeftR)
    (w1 := block338W1) (w2 := block338W2) (w3 := block338W3) (w4 := block338W4)
    (s1 := block338S1) (s2 := block338S2) (s3 := block338S3) (s4 := block338S4)
    hboxes hcover block338LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block338RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block338RightChunk000 block338W1 block338W2 block338W3 block338W4 block338S1 block338S2 block338S3 block338S4

theorem block338RightChunk000ParamsCertificate_eq_true :
    block338RightChunk000ParamsCertificate = true := by
  native_decide

theorem block338_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block338RightChunk000L : ℝ) (block338RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block338S1 : ℝ))
    (hy2ne : y ≠ (block338S2 : ℝ))
    (hy3ne : y ≠ (block338S3 : ℝ))
    (hy4ne : y ≠ (block338S4 : ℝ)) :
    0 < block338V y := by
  have hcert := block338RightChunk000Certificate_eq_true
  unfold block338RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block338RightChunk000) (lo := block338RightChunk000L) (hi := block338RightChunk000R)
    (w1 := block338W1) (w2 := block338W2) (w3 := block338W3) (w4 := block338W4)
    (s1 := block338S1) (s2 := block338S2) (s3 := block338S3) (s4 := block338S4)
    hboxes hcover block338RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block338_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block338RightL : ℝ) (block338RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block338S1 : ℝ))
    (hy2ne : y ≠ (block338S2 : ℝ))
    (hy3ne : y ≠ (block338S3 : ℝ))
    (hy4ne : y ≠ (block338S4 : ℝ)) :
    0 < block338V y := by
  have hL : (block338RightChunk000L : ℝ) = (block338RightL : ℝ) := by
    norm_num [block338RightChunk000L, block338RightL]
  have hR : (block338RightChunk000R : ℝ) = (block338RightR : ℝ) := by
    norm_num [block338RightChunk000R, block338RightR]
  have hyc : y ∈ Icc (block338RightChunk000L : ℝ) (block338RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block338_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block338_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block338LeftL : ℝ) (block338LeftR : ℝ) →
    y ≠ 0 → y ≠ (block338S1 : ℝ) → y ≠ (block338S2 : ℝ) →
    y ≠ (block338S3 : ℝ) → y ≠ (block338S4 : ℝ) → 0 < block338V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block338RightL : ℝ) (block338RightR : ℝ) →
    y ≠ 0 → y ≠ (block338S1 : ℝ) → y ≠ (block338S2 : ℝ) →
    y ≠ (block338S3 : ℝ) → y ≠ (block338S4 : ℝ) → 0 < block338V y)

theorem block338_reallog_certificate_proof :
    block338_reallog_certificate := by
  exact ⟨block338_left_V_pos, block338_right_V_pos⟩

end Block338
end M1817475
end Erdos1038Lean
