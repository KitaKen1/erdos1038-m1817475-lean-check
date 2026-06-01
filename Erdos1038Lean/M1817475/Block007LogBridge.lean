import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block007

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block007

open Set

def block007W1 : Rat := ((268800522615757 : Rat) / 25000000000000)
def block007W2 : Rat := (0 : Rat)
def block007W3 : Rat := (0 : Rat)
def block007W4 : Rat := ((25070377381274317 : Rat) / 100000000000000000)
def block007S1 : Rat := ((18174751 : Rat) / 10000000)
def block007S2 : Rat := ((511587 : Rat) / 200000)
def block007S3 : Rat := ((107000619 : Rat) / 40000000)
def block007S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block007V (y : ℝ) : ℝ :=
  ratPotential block007W1 block007W2 block007W3 block007W4 block007S1 block007S2 block007S3 block007S4 y

def block007LeftParamsCertificate : Bool :=
  allBoxesSameParams block007LeftBoxes block007W1 block007W2 block007W3 block007W4 block007S1 block007S2 block007S3 block007S4

theorem block007LeftParamsCertificate_eq_true :
    block007LeftParamsCertificate = true := by
  native_decide

theorem block007_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block007LeftL : ℝ) (block007LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block007S1 : ℝ))
    (hy2ne : y ≠ (block007S2 : ℝ))
    (hy3ne : y ≠ (block007S3 : ℝ))
    (hy4ne : y ≠ (block007S4 : ℝ)) :
    0 < block007V y := by
  have hcert := block007LeftCertificate_eq_true
  unfold block007LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block007LeftBoxes) (lo := block007LeftL) (hi := block007LeftR)
    (w1 := block007W1) (w2 := block007W2) (w3 := block007W3) (w4 := block007W4)
    (s1 := block007S1) (s2 := block007S2) (s3 := block007S3) (s4 := block007S4)
    hboxes hcover block007LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block007RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block007RightChunk000 block007W1 block007W2 block007W3 block007W4 block007S1 block007S2 block007S3 block007S4

theorem block007RightChunk000ParamsCertificate_eq_true :
    block007RightChunk000ParamsCertificate = true := by
  native_decide

theorem block007_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block007RightChunk000L : ℝ) (block007RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block007S1 : ℝ))
    (hy2ne : y ≠ (block007S2 : ℝ))
    (hy3ne : y ≠ (block007S3 : ℝ))
    (hy4ne : y ≠ (block007S4 : ℝ)) :
    0 < block007V y := by
  have hcert := block007RightChunk000Certificate_eq_true
  unfold block007RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block007RightChunk000) (lo := block007RightChunk000L) (hi := block007RightChunk000R)
    (w1 := block007W1) (w2 := block007W2) (w3 := block007W3) (w4 := block007W4)
    (s1 := block007S1) (s2 := block007S2) (s3 := block007S3) (s4 := block007S4)
    hboxes hcover block007RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block007_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block007RightL : ℝ) (block007RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block007S1 : ℝ))
    (hy2ne : y ≠ (block007S2 : ℝ))
    (hy3ne : y ≠ (block007S3 : ℝ))
    (hy4ne : y ≠ (block007S4 : ℝ)) :
    0 < block007V y := by
  have hL : (block007RightChunk000L : ℝ) = (block007RightL : ℝ) := by
    norm_num [block007RightChunk000L, block007RightL]
  have hR : (block007RightChunk000R : ℝ) = (block007RightR : ℝ) := by
    norm_num [block007RightChunk000R, block007RightR]
  have hyc : y ∈ Icc (block007RightChunk000L : ℝ) (block007RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block007_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block007_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block007LeftL : ℝ) (block007LeftR : ℝ) →
    y ≠ 0 → y ≠ (block007S1 : ℝ) → y ≠ (block007S2 : ℝ) →
    y ≠ (block007S3 : ℝ) → y ≠ (block007S4 : ℝ) → 0 < block007V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block007RightL : ℝ) (block007RightR : ℝ) →
    y ≠ 0 → y ≠ (block007S1 : ℝ) → y ≠ (block007S2 : ℝ) →
    y ≠ (block007S3 : ℝ) → y ≠ (block007S4 : ℝ) → 0 < block007V y)

theorem block007_reallog_certificate_proof :
    block007_reallog_certificate := by
  exact ⟨block007_left_V_pos, block007_right_V_pos⟩

end Block007
end M1817475
end Erdos1038Lean
