import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block041

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block041

open Set

def block041W1 : Rat := ((12655194059099133 : Rat) / 5000000000000000)
def block041W2 : Rat := (0 : Rat)
def block041W3 : Rat := (0 : Rat)
def block041W4 : Rat := ((13768175094035773 : Rat) / 50000000000000000)
def block041S1 : Rat := ((18174751 : Rat) / 10000000)
def block041S2 : Rat := ((511587 : Rat) / 200000)
def block041S3 : Rat := ((107000619 : Rat) / 40000000)
def block041S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block041V (y : ℝ) : ℝ :=
  ratPotential block041W1 block041W2 block041W3 block041W4 block041S1 block041S2 block041S3 block041S4 y

def block041LeftParamsCertificate : Bool :=
  allBoxesSameParams block041LeftBoxes block041W1 block041W2 block041W3 block041W4 block041S1 block041S2 block041S3 block041S4

theorem block041LeftParamsCertificate_eq_true :
    block041LeftParamsCertificate = true := by
  native_decide

theorem block041_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block041LeftL : ℝ) (block041LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block041S1 : ℝ))
    (hy2ne : y ≠ (block041S2 : ℝ))
    (hy3ne : y ≠ (block041S3 : ℝ))
    (hy4ne : y ≠ (block041S4 : ℝ)) :
    0 < block041V y := by
  have hcert := block041LeftCertificate_eq_true
  unfold block041LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block041LeftBoxes) (lo := block041LeftL) (hi := block041LeftR)
    (w1 := block041W1) (w2 := block041W2) (w3 := block041W3) (w4 := block041W4)
    (s1 := block041S1) (s2 := block041S2) (s3 := block041S3) (s4 := block041S4)
    hboxes hcover block041LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block041RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block041RightChunk000 block041W1 block041W2 block041W3 block041W4 block041S1 block041S2 block041S3 block041S4

theorem block041RightChunk000ParamsCertificate_eq_true :
    block041RightChunk000ParamsCertificate = true := by
  native_decide

theorem block041_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block041RightChunk000L : ℝ) (block041RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block041S1 : ℝ))
    (hy2ne : y ≠ (block041S2 : ℝ))
    (hy3ne : y ≠ (block041S3 : ℝ))
    (hy4ne : y ≠ (block041S4 : ℝ)) :
    0 < block041V y := by
  have hcert := block041RightChunk000Certificate_eq_true
  unfold block041RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block041RightChunk000) (lo := block041RightChunk000L) (hi := block041RightChunk000R)
    (w1 := block041W1) (w2 := block041W2) (w3 := block041W3) (w4 := block041W4)
    (s1 := block041S1) (s2 := block041S2) (s3 := block041S3) (s4 := block041S4)
    hboxes hcover block041RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block041_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block041RightL : ℝ) (block041RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block041S1 : ℝ))
    (hy2ne : y ≠ (block041S2 : ℝ))
    (hy3ne : y ≠ (block041S3 : ℝ))
    (hy4ne : y ≠ (block041S4 : ℝ)) :
    0 < block041V y := by
  have hL : (block041RightChunk000L : ℝ) = (block041RightL : ℝ) := by
    norm_num [block041RightChunk000L, block041RightL]
  have hR : (block041RightChunk000R : ℝ) = (block041RightR : ℝ) := by
    norm_num [block041RightChunk000R, block041RightR]
  have hyc : y ∈ Icc (block041RightChunk000L : ℝ) (block041RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block041_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block041_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block041LeftL : ℝ) (block041LeftR : ℝ) →
    y ≠ 0 → y ≠ (block041S1 : ℝ) → y ≠ (block041S2 : ℝ) →
    y ≠ (block041S3 : ℝ) → y ≠ (block041S4 : ℝ) → 0 < block041V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block041RightL : ℝ) (block041RightR : ℝ) →
    y ≠ 0 → y ≠ (block041S1 : ℝ) → y ≠ (block041S2 : ℝ) →
    y ≠ (block041S3 : ℝ) → y ≠ (block041S4 : ℝ) → 0 < block041V y)

theorem block041_reallog_certificate_proof :
    block041_reallog_certificate := by
  exact ⟨block041_left_V_pos, block041_right_V_pos⟩

end Block041
end M1817475
end Erdos1038Lean
