import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block370

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block370

open Set

def block370W1 : Rat := ((542212277280583 : Rat) / 625000000000000)
def block370W2 : Rat := ((11785767859639631 : Rat) / 250000000000000000)
def block370W3 : Rat := ((3870465086062707 : Rat) / 25000000000000000)
def block370W4 : Rat := ((1397510426181841 : Rat) / 10000000000000000)
def block370S1 : Rat := ((18174751 : Rat) / 10000000)
def block370S2 : Rat := ((511587 : Rat) / 200000)
def block370S3 : Rat := ((132900387589285714323 : Rat) / 50000000000000000000)
def block370S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block370V (y : ℝ) : ℝ :=
  ratPotential block370W1 block370W2 block370W3 block370W4 block370S1 block370S2 block370S3 block370S4 y

def block370LeftParamsCertificate : Bool :=
  allBoxesSameParams block370LeftBoxes block370W1 block370W2 block370W3 block370W4 block370S1 block370S2 block370S3 block370S4

theorem block370LeftParamsCertificate_eq_true :
    block370LeftParamsCertificate = true := by
  native_decide

theorem block370_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block370LeftL : ℝ) (block370LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block370S1 : ℝ))
    (hy2ne : y ≠ (block370S2 : ℝ))
    (hy3ne : y ≠ (block370S3 : ℝ))
    (hy4ne : y ≠ (block370S4 : ℝ)) :
    0 < block370V y := by
  have hcert := block370LeftCertificate_eq_true
  unfold block370LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block370LeftBoxes) (lo := block370LeftL) (hi := block370LeftR)
    (w1 := block370W1) (w2 := block370W2) (w3 := block370W3) (w4 := block370W4)
    (s1 := block370S1) (s2 := block370S2) (s3 := block370S3) (s4 := block370S4)
    hboxes hcover block370LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block370RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block370RightChunk000 block370W1 block370W2 block370W3 block370W4 block370S1 block370S2 block370S3 block370S4

theorem block370RightChunk000ParamsCertificate_eq_true :
    block370RightChunk000ParamsCertificate = true := by
  native_decide

theorem block370_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block370RightChunk000L : ℝ) (block370RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block370S1 : ℝ))
    (hy2ne : y ≠ (block370S2 : ℝ))
    (hy3ne : y ≠ (block370S3 : ℝ))
    (hy4ne : y ≠ (block370S4 : ℝ)) :
    0 < block370V y := by
  have hcert := block370RightChunk000Certificate_eq_true
  unfold block370RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block370RightChunk000) (lo := block370RightChunk000L) (hi := block370RightChunk000R)
    (w1 := block370W1) (w2 := block370W2) (w3 := block370W3) (w4 := block370W4)
    (s1 := block370S1) (s2 := block370S2) (s3 := block370S3) (s4 := block370S4)
    hboxes hcover block370RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block370_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block370RightL : ℝ) (block370RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block370S1 : ℝ))
    (hy2ne : y ≠ (block370S2 : ℝ))
    (hy3ne : y ≠ (block370S3 : ℝ))
    (hy4ne : y ≠ (block370S4 : ℝ)) :
    0 < block370V y := by
  have hL : (block370RightChunk000L : ℝ) = (block370RightL : ℝ) := by
    norm_num [block370RightChunk000L, block370RightL]
  have hR : (block370RightChunk000R : ℝ) = (block370RightR : ℝ) := by
    norm_num [block370RightChunk000R, block370RightR]
  have hyc : y ∈ Icc (block370RightChunk000L : ℝ) (block370RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block370_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block370_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block370LeftL : ℝ) (block370LeftR : ℝ) →
    y ≠ 0 → y ≠ (block370S1 : ℝ) → y ≠ (block370S2 : ℝ) →
    y ≠ (block370S3 : ℝ) → y ≠ (block370S4 : ℝ) → 0 < block370V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block370RightL : ℝ) (block370RightR : ℝ) →
    y ≠ 0 → y ≠ (block370S1 : ℝ) → y ≠ (block370S2 : ℝ) →
    y ≠ (block370S3 : ℝ) → y ≠ (block370S4 : ℝ) → 0 < block370V y)

theorem block370_reallog_certificate_proof :
    block370_reallog_certificate := by
  exact ⟨block370_left_V_pos, block370_right_V_pos⟩

end Block370
end M1817475
end Erdos1038Lean
