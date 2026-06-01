import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block004

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block004

open Set

def block004W1 : Rat := ((1549788951109419 : Rat) / 125000000000000)
def block004W2 : Rat := (0 : Rat)
def block004W3 : Rat := (0 : Rat)
def block004W4 : Rat := ((1556831174919787 : Rat) / 6250000000000000)
def block004S1 : Rat := ((18174751 : Rat) / 10000000)
def block004S2 : Rat := ((511587 : Rat) / 200000)
def block004S3 : Rat := ((107000619 : Rat) / 40000000)
def block004S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block004V (y : ℝ) : ℝ :=
  ratPotential block004W1 block004W2 block004W3 block004W4 block004S1 block004S2 block004S3 block004S4 y

def block004LeftParamsCertificate : Bool :=
  allBoxesSameParams block004LeftBoxes block004W1 block004W2 block004W3 block004W4 block004S1 block004S2 block004S3 block004S4

theorem block004LeftParamsCertificate_eq_true :
    block004LeftParamsCertificate = true := by
  native_decide

theorem block004_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block004LeftL : ℝ) (block004LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block004S1 : ℝ))
    (hy2ne : y ≠ (block004S2 : ℝ))
    (hy3ne : y ≠ (block004S3 : ℝ))
    (hy4ne : y ≠ (block004S4 : ℝ)) :
    0 < block004V y := by
  have hcert := block004LeftCertificate_eq_true
  unfold block004LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block004LeftBoxes) (lo := block004LeftL) (hi := block004LeftR)
    (w1 := block004W1) (w2 := block004W2) (w3 := block004W3) (w4 := block004W4)
    (s1 := block004S1) (s2 := block004S2) (s3 := block004S3) (s4 := block004S4)
    hboxes hcover block004LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block004RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block004RightChunk000 block004W1 block004W2 block004W3 block004W4 block004S1 block004S2 block004S3 block004S4

theorem block004RightChunk000ParamsCertificate_eq_true :
    block004RightChunk000ParamsCertificate = true := by
  native_decide

theorem block004_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block004RightChunk000L : ℝ) (block004RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block004S1 : ℝ))
    (hy2ne : y ≠ (block004S2 : ℝ))
    (hy3ne : y ≠ (block004S3 : ℝ))
    (hy4ne : y ≠ (block004S4 : ℝ)) :
    0 < block004V y := by
  have hcert := block004RightChunk000Certificate_eq_true
  unfold block004RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block004RightChunk000) (lo := block004RightChunk000L) (hi := block004RightChunk000R)
    (w1 := block004W1) (w2 := block004W2) (w3 := block004W3) (w4 := block004W4)
    (s1 := block004S1) (s2 := block004S2) (s3 := block004S3) (s4 := block004S4)
    hboxes hcover block004RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block004_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block004RightL : ℝ) (block004RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block004S1 : ℝ))
    (hy2ne : y ≠ (block004S2 : ℝ))
    (hy3ne : y ≠ (block004S3 : ℝ))
    (hy4ne : y ≠ (block004S4 : ℝ)) :
    0 < block004V y := by
  have hL : (block004RightChunk000L : ℝ) = (block004RightL : ℝ) := by
    norm_num [block004RightChunk000L, block004RightL]
  have hR : (block004RightChunk000R : ℝ) = (block004RightR : ℝ) := by
    norm_num [block004RightChunk000R, block004RightR]
  have hyc : y ∈ Icc (block004RightChunk000L : ℝ) (block004RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block004_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block004_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block004LeftL : ℝ) (block004LeftR : ℝ) →
    y ≠ 0 → y ≠ (block004S1 : ℝ) → y ≠ (block004S2 : ℝ) →
    y ≠ (block004S3 : ℝ) → y ≠ (block004S4 : ℝ) → 0 < block004V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block004RightL : ℝ) (block004RightR : ℝ) →
    y ≠ 0 → y ≠ (block004S1 : ℝ) → y ≠ (block004S2 : ℝ) →
    y ≠ (block004S3 : ℝ) → y ≠ (block004S4 : ℝ) → 0 < block004V y)

theorem block004_reallog_certificate_proof :
    block004_reallog_certificate := by
  exact ⟨block004_left_V_pos, block004_right_V_pos⟩

end Block004
end M1817475
end Erdos1038Lean
