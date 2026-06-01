import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block360

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block360

open Set

def block360W1 : Rat := ((8863763323022047 : Rat) / 10000000000000000)
def block360W2 : Rat := ((2968283997052271 : Rat) / 62500000000000000)
def block360W3 : Rat := ((15170427436261683 : Rat) / 100000000000000000)
def block360W4 : Rat := ((1738420445898041 : Rat) / 12500000000000000)
def block360S1 : Rat := ((18174751 : Rat) / 10000000)
def block360S2 : Rat := ((511587 : Rat) / 200000)
def block360S3 : Rat := ((133095878660714285743 : Rat) / 50000000000000000000)
def block360S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block360V (y : ℝ) : ℝ :=
  ratPotential block360W1 block360W2 block360W3 block360W4 block360S1 block360S2 block360S3 block360S4 y

def block360LeftParamsCertificate : Bool :=
  allBoxesSameParams block360LeftBoxes block360W1 block360W2 block360W3 block360W4 block360S1 block360S2 block360S3 block360S4

theorem block360LeftParamsCertificate_eq_true :
    block360LeftParamsCertificate = true := by
  native_decide

theorem block360_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block360LeftL : ℝ) (block360LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block360S1 : ℝ))
    (hy2ne : y ≠ (block360S2 : ℝ))
    (hy3ne : y ≠ (block360S3 : ℝ))
    (hy4ne : y ≠ (block360S4 : ℝ)) :
    0 < block360V y := by
  have hcert := block360LeftCertificate_eq_true
  unfold block360LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block360LeftBoxes) (lo := block360LeftL) (hi := block360LeftR)
    (w1 := block360W1) (w2 := block360W2) (w3 := block360W3) (w4 := block360W4)
    (s1 := block360S1) (s2 := block360S2) (s3 := block360S3) (s4 := block360S4)
    hboxes hcover block360LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block360RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block360RightChunk000 block360W1 block360W2 block360W3 block360W4 block360S1 block360S2 block360S3 block360S4

theorem block360RightChunk000ParamsCertificate_eq_true :
    block360RightChunk000ParamsCertificate = true := by
  native_decide

theorem block360_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block360RightChunk000L : ℝ) (block360RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block360S1 : ℝ))
    (hy2ne : y ≠ (block360S2 : ℝ))
    (hy3ne : y ≠ (block360S3 : ℝ))
    (hy4ne : y ≠ (block360S4 : ℝ)) :
    0 < block360V y := by
  have hcert := block360RightChunk000Certificate_eq_true
  unfold block360RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block360RightChunk000) (lo := block360RightChunk000L) (hi := block360RightChunk000R)
    (w1 := block360W1) (w2 := block360W2) (w3 := block360W3) (w4 := block360W4)
    (s1 := block360S1) (s2 := block360S2) (s3 := block360S3) (s4 := block360S4)
    hboxes hcover block360RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block360_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block360RightL : ℝ) (block360RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block360S1 : ℝ))
    (hy2ne : y ≠ (block360S2 : ℝ))
    (hy3ne : y ≠ (block360S3 : ℝ))
    (hy4ne : y ≠ (block360S4 : ℝ)) :
    0 < block360V y := by
  have hL : (block360RightChunk000L : ℝ) = (block360RightL : ℝ) := by
    norm_num [block360RightChunk000L, block360RightL]
  have hR : (block360RightChunk000R : ℝ) = (block360RightR : ℝ) := by
    norm_num [block360RightChunk000R, block360RightR]
  have hyc : y ∈ Icc (block360RightChunk000L : ℝ) (block360RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block360_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block360_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block360LeftL : ℝ) (block360LeftR : ℝ) →
    y ≠ 0 → y ≠ (block360S1 : ℝ) → y ≠ (block360S2 : ℝ) →
    y ≠ (block360S3 : ℝ) → y ≠ (block360S4 : ℝ) → 0 < block360V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block360RightL : ℝ) (block360RightR : ℝ) →
    y ≠ 0 → y ≠ (block360S1 : ℝ) → y ≠ (block360S2 : ℝ) →
    y ≠ (block360S3 : ℝ) → y ≠ (block360S4 : ℝ) → 0 < block360V y)

theorem block360_reallog_certificate_proof :
    block360_reallog_certificate := by
  exact ⟨block360_left_V_pos, block360_right_V_pos⟩

end Block360
end M1817475
end Erdos1038Lean
