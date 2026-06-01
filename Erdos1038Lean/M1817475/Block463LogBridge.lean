import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block463

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block463

open Set

def block463W1 : Rat := ((1402449123692501 : Rat) / 2500000000000000)
def block463W2 : Rat := (0 : Rat)
def block463W3 : Rat := ((28095645439721 : Rat) / 80000000000000)
def block463W4 : Rat := ((11481144808228247 : Rat) / 200000000000000000)
def block463S1 : Rat := ((18174751 : Rat) / 10000000)
def block463S2 : Rat := ((511587 : Rat) / 200000)
def block463S3 : Rat := ((131082320625000000117 : Rat) / 50000000000000000000)
def block463S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block463V (y : ℝ) : ℝ :=
  ratPotential block463W1 block463W2 block463W3 block463W4 block463S1 block463S2 block463S3 block463S4 y

def block463LeftParamsCertificate : Bool :=
  allBoxesSameParams block463LeftBoxes block463W1 block463W2 block463W3 block463W4 block463S1 block463S2 block463S3 block463S4

theorem block463LeftParamsCertificate_eq_true :
    block463LeftParamsCertificate = true := by
  native_decide

theorem block463_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block463LeftL : ℝ) (block463LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block463S1 : ℝ))
    (hy2ne : y ≠ (block463S2 : ℝ))
    (hy3ne : y ≠ (block463S3 : ℝ))
    (hy4ne : y ≠ (block463S4 : ℝ)) :
    0 < block463V y := by
  have hcert := block463LeftCertificate_eq_true
  unfold block463LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block463LeftBoxes) (lo := block463LeftL) (hi := block463LeftR)
    (w1 := block463W1) (w2 := block463W2) (w3 := block463W3) (w4 := block463W4)
    (s1 := block463S1) (s2 := block463S2) (s3 := block463S3) (s4 := block463S4)
    hboxes hcover block463LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block463RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block463RightChunk000 block463W1 block463W2 block463W3 block463W4 block463S1 block463S2 block463S3 block463S4

theorem block463RightChunk000ParamsCertificate_eq_true :
    block463RightChunk000ParamsCertificate = true := by
  native_decide

theorem block463_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block463RightChunk000L : ℝ) (block463RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block463S1 : ℝ))
    (hy2ne : y ≠ (block463S2 : ℝ))
    (hy3ne : y ≠ (block463S3 : ℝ))
    (hy4ne : y ≠ (block463S4 : ℝ)) :
    0 < block463V y := by
  have hcert := block463RightChunk000Certificate_eq_true
  unfold block463RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block463RightChunk000) (lo := block463RightChunk000L) (hi := block463RightChunk000R)
    (w1 := block463W1) (w2 := block463W2) (w3 := block463W3) (w4 := block463W4)
    (s1 := block463S1) (s2 := block463S2) (s3 := block463S3) (s4 := block463S4)
    hboxes hcover block463RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block463_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block463RightL : ℝ) (block463RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block463S1 : ℝ))
    (hy2ne : y ≠ (block463S2 : ℝ))
    (hy3ne : y ≠ (block463S3 : ℝ))
    (hy4ne : y ≠ (block463S4 : ℝ)) :
    0 < block463V y := by
  have hL : (block463RightChunk000L : ℝ) = (block463RightL : ℝ) := by
    norm_num [block463RightChunk000L, block463RightL]
  have hR : (block463RightChunk000R : ℝ) = (block463RightR : ℝ) := by
    norm_num [block463RightChunk000R, block463RightR]
  have hyc : y ∈ Icc (block463RightChunk000L : ℝ) (block463RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block463_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block463_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block463LeftL : ℝ) (block463LeftR : ℝ) →
    y ≠ 0 → y ≠ (block463S1 : ℝ) → y ≠ (block463S2 : ℝ) →
    y ≠ (block463S3 : ℝ) → y ≠ (block463S4 : ℝ) → 0 < block463V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block463RightL : ℝ) (block463RightR : ℝ) →
    y ≠ 0 → y ≠ (block463S1 : ℝ) → y ≠ (block463S2 : ℝ) →
    y ≠ (block463S3 : ℝ) → y ≠ (block463S4 : ℝ) → 0 < block463V y)

theorem block463_reallog_certificate_proof :
    block463_reallog_certificate := by
  exact ⟨block463_left_V_pos, block463_right_V_pos⟩

end Block463
end M1817475
end Erdos1038Lean
