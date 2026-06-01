import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block384

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block384

open Set

def block384W1 : Rat := ((8429180103914411 : Rat) / 10000000000000000)
def block384W2 : Rat := ((925197128691713 : Rat) / 20000000000000000)
def block384W3 : Rat := ((318738628916679 : Rat) / 2000000000000000)
def block384W4 : Rat := ((3518598311612653 : Rat) / 25000000000000000)
def block384S1 : Rat := ((18174751 : Rat) / 10000000)
def block384S2 : Rat := ((511587 : Rat) / 200000)
def block384S3 : Rat := ((26525340017857142867 : Rat) / 10000000000000000000)
def block384S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block384V (y : ℝ) : ℝ :=
  ratPotential block384W1 block384W2 block384W3 block384W4 block384S1 block384S2 block384S3 block384S4 y

def block384LeftParamsCertificate : Bool :=
  allBoxesSameParams block384LeftBoxes block384W1 block384W2 block384W3 block384W4 block384S1 block384S2 block384S3 block384S4

theorem block384LeftParamsCertificate_eq_true :
    block384LeftParamsCertificate = true := by
  native_decide

theorem block384_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block384LeftL : ℝ) (block384LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block384S1 : ℝ))
    (hy2ne : y ≠ (block384S2 : ℝ))
    (hy3ne : y ≠ (block384S3 : ℝ))
    (hy4ne : y ≠ (block384S4 : ℝ)) :
    0 < block384V y := by
  have hcert := block384LeftCertificate_eq_true
  unfold block384LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block384LeftBoxes) (lo := block384LeftL) (hi := block384LeftR)
    (w1 := block384W1) (w2 := block384W2) (w3 := block384W3) (w4 := block384W4)
    (s1 := block384S1) (s2 := block384S2) (s3 := block384S3) (s4 := block384S4)
    hboxes hcover block384LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block384RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block384RightChunk000 block384W1 block384W2 block384W3 block384W4 block384S1 block384S2 block384S3 block384S4

theorem block384RightChunk000ParamsCertificate_eq_true :
    block384RightChunk000ParamsCertificate = true := by
  native_decide

theorem block384_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block384RightChunk000L : ℝ) (block384RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block384S1 : ℝ))
    (hy2ne : y ≠ (block384S2 : ℝ))
    (hy3ne : y ≠ (block384S3 : ℝ))
    (hy4ne : y ≠ (block384S4 : ℝ)) :
    0 < block384V y := by
  have hcert := block384RightChunk000Certificate_eq_true
  unfold block384RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block384RightChunk000) (lo := block384RightChunk000L) (hi := block384RightChunk000R)
    (w1 := block384W1) (w2 := block384W2) (w3 := block384W3) (w4 := block384W4)
    (s1 := block384S1) (s2 := block384S2) (s3 := block384S3) (s4 := block384S4)
    hboxes hcover block384RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block384_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block384RightL : ℝ) (block384RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block384S1 : ℝ))
    (hy2ne : y ≠ (block384S2 : ℝ))
    (hy3ne : y ≠ (block384S3 : ℝ))
    (hy4ne : y ≠ (block384S4 : ℝ)) :
    0 < block384V y := by
  have hL : (block384RightChunk000L : ℝ) = (block384RightL : ℝ) := by
    norm_num [block384RightChunk000L, block384RightL]
  have hR : (block384RightChunk000R : ℝ) = (block384RightR : ℝ) := by
    norm_num [block384RightChunk000R, block384RightR]
  have hyc : y ∈ Icc (block384RightChunk000L : ℝ) (block384RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block384_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block384_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block384LeftL : ℝ) (block384LeftR : ℝ) →
    y ≠ 0 → y ≠ (block384S1 : ℝ) → y ≠ (block384S2 : ℝ) →
    y ≠ (block384S3 : ℝ) → y ≠ (block384S4 : ℝ) → 0 < block384V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block384RightL : ℝ) (block384RightR : ℝ) →
    y ≠ 0 → y ≠ (block384S1 : ℝ) → y ≠ (block384S2 : ℝ) →
    y ≠ (block384S3 : ℝ) → y ≠ (block384S4 : ℝ) → 0 < block384V y)

theorem block384_reallog_certificate_proof :
    block384_reallog_certificate := by
  exact ⟨block384_left_V_pos, block384_right_V_pos⟩

end Block384
end M1817475
end Erdos1038Lean
