import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block520

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block520

open Set

def block520W1 : Rat := ((261456451045941 : Rat) / 625000000000000)
def block520W2 : Rat := (0 : Rat)
def block520W3 : Rat := ((44840463513102713 : Rat) / 100000000000000000)
def block520W4 : Rat := (0 : Rat)
def block520S1 : Rat := ((18174751 : Rat) / 10000000)
def block520S2 : Rat := ((511587 : Rat) / 200000)
def block520S3 : Rat := ((129968021517857143023 : Rat) / 50000000000000000000)
def block520S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block520V (y : ℝ) : ℝ :=
  ratPotential block520W1 block520W2 block520W3 block520W4 block520S1 block520S2 block520S3 block520S4 y

def block520LeftParamsCertificate : Bool :=
  allBoxesSameParams block520LeftBoxes block520W1 block520W2 block520W3 block520W4 block520S1 block520S2 block520S3 block520S4

theorem block520LeftParamsCertificate_eq_true :
    block520LeftParamsCertificate = true := by
  native_decide

theorem block520_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block520LeftL : ℝ) (block520LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block520S1 : ℝ))
    (hy2ne : y ≠ (block520S2 : ℝ))
    (hy3ne : y ≠ (block520S3 : ℝ))
    (hy4ne : y ≠ (block520S4 : ℝ)) :
    0 < block520V y := by
  have hcert := block520LeftCertificate_eq_true
  unfold block520LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block520LeftBoxes) (lo := block520LeftL) (hi := block520LeftR)
    (w1 := block520W1) (w2 := block520W2) (w3 := block520W3) (w4 := block520W4)
    (s1 := block520S1) (s2 := block520S2) (s3 := block520S3) (s4 := block520S4)
    hboxes hcover block520LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block520RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block520RightChunk000 block520W1 block520W2 block520W3 block520W4 block520S1 block520S2 block520S3 block520S4

theorem block520RightChunk000ParamsCertificate_eq_true :
    block520RightChunk000ParamsCertificate = true := by
  native_decide

theorem block520_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block520RightChunk000L : ℝ) (block520RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block520S1 : ℝ))
    (hy2ne : y ≠ (block520S2 : ℝ))
    (hy3ne : y ≠ (block520S3 : ℝ))
    (hy4ne : y ≠ (block520S4 : ℝ)) :
    0 < block520V y := by
  have hcert := block520RightChunk000Certificate_eq_true
  unfold block520RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block520RightChunk000) (lo := block520RightChunk000L) (hi := block520RightChunk000R)
    (w1 := block520W1) (w2 := block520W2) (w3 := block520W3) (w4 := block520W4)
    (s1 := block520S1) (s2 := block520S2) (s3 := block520S3) (s4 := block520S4)
    hboxes hcover block520RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block520_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block520RightL : ℝ) (block520RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block520S1 : ℝ))
    (hy2ne : y ≠ (block520S2 : ℝ))
    (hy3ne : y ≠ (block520S3 : ℝ))
    (hy4ne : y ≠ (block520S4 : ℝ)) :
    0 < block520V y := by
  have hL : (block520RightChunk000L : ℝ) = (block520RightL : ℝ) := by
    norm_num [block520RightChunk000L, block520RightL]
  have hR : (block520RightChunk000R : ℝ) = (block520RightR : ℝ) := by
    norm_num [block520RightChunk000R, block520RightR]
  have hyc : y ∈ Icc (block520RightChunk000L : ℝ) (block520RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block520_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block520_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block520LeftL : ℝ) (block520LeftR : ℝ) →
    y ≠ 0 → y ≠ (block520S1 : ℝ) → y ≠ (block520S2 : ℝ) →
    y ≠ (block520S3 : ℝ) → y ≠ (block520S4 : ℝ) → 0 < block520V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block520RightL : ℝ) (block520RightR : ℝ) →
    y ≠ 0 → y ≠ (block520S1 : ℝ) → y ≠ (block520S2 : ℝ) →
    y ≠ (block520S3 : ℝ) → y ≠ (block520S4 : ℝ) → 0 < block520V y)

theorem block520_reallog_certificate_proof :
    block520_reallog_certificate := by
  exact ⟨block520_left_V_pos, block520_right_V_pos⟩

end Block520
end M1817475
end Erdos1038Lean
