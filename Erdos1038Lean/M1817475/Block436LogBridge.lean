import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block436

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block436

open Set

def block436W1 : Rat := ((319122846583069 : Rat) / 500000000000000)
def block436W2 : Rat := (0 : Rat)
def block436W3 : Rat := ((15756381475683487 : Rat) / 50000000000000000)
def block436W4 : Rat := ((762681529705649 : Rat) / 10000000000000000)
def block436S1 : Rat := ((18174751 : Rat) / 10000000)
def block436S2 : Rat := ((511587 : Rat) / 200000)
def block436S3 : Rat := ((131610146517857142951 : Rat) / 50000000000000000000)
def block436S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block436V (y : ℝ) : ℝ :=
  ratPotential block436W1 block436W2 block436W3 block436W4 block436S1 block436S2 block436S3 block436S4 y

def block436LeftParamsCertificate : Bool :=
  allBoxesSameParams block436LeftBoxes block436W1 block436W2 block436W3 block436W4 block436S1 block436S2 block436S3 block436S4

theorem block436LeftParamsCertificate_eq_true :
    block436LeftParamsCertificate = true := by
  native_decide

theorem block436_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block436LeftL : ℝ) (block436LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block436S1 : ℝ))
    (hy2ne : y ≠ (block436S2 : ℝ))
    (hy3ne : y ≠ (block436S3 : ℝ))
    (hy4ne : y ≠ (block436S4 : ℝ)) :
    0 < block436V y := by
  have hcert := block436LeftCertificate_eq_true
  unfold block436LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block436LeftBoxes) (lo := block436LeftL) (hi := block436LeftR)
    (w1 := block436W1) (w2 := block436W2) (w3 := block436W3) (w4 := block436W4)
    (s1 := block436S1) (s2 := block436S2) (s3 := block436S3) (s4 := block436S4)
    hboxes hcover block436LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block436RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block436RightChunk000 block436W1 block436W2 block436W3 block436W4 block436S1 block436S2 block436S3 block436S4

theorem block436RightChunk000ParamsCertificate_eq_true :
    block436RightChunk000ParamsCertificate = true := by
  native_decide

theorem block436_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block436RightChunk000L : ℝ) (block436RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block436S1 : ℝ))
    (hy2ne : y ≠ (block436S2 : ℝ))
    (hy3ne : y ≠ (block436S3 : ℝ))
    (hy4ne : y ≠ (block436S4 : ℝ)) :
    0 < block436V y := by
  have hcert := block436RightChunk000Certificate_eq_true
  unfold block436RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block436RightChunk000) (lo := block436RightChunk000L) (hi := block436RightChunk000R)
    (w1 := block436W1) (w2 := block436W2) (w3 := block436W3) (w4 := block436W4)
    (s1 := block436S1) (s2 := block436S2) (s3 := block436S3) (s4 := block436S4)
    hboxes hcover block436RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block436_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block436RightL : ℝ) (block436RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block436S1 : ℝ))
    (hy2ne : y ≠ (block436S2 : ℝ))
    (hy3ne : y ≠ (block436S3 : ℝ))
    (hy4ne : y ≠ (block436S4 : ℝ)) :
    0 < block436V y := by
  have hL : (block436RightChunk000L : ℝ) = (block436RightL : ℝ) := by
    norm_num [block436RightChunk000L, block436RightL]
  have hR : (block436RightChunk000R : ℝ) = (block436RightR : ℝ) := by
    norm_num [block436RightChunk000R, block436RightR]
  have hyc : y ∈ Icc (block436RightChunk000L : ℝ) (block436RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block436_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block436_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block436LeftL : ℝ) (block436LeftR : ℝ) →
    y ≠ 0 → y ≠ (block436S1 : ℝ) → y ≠ (block436S2 : ℝ) →
    y ≠ (block436S3 : ℝ) → y ≠ (block436S4 : ℝ) → 0 < block436V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block436RightL : ℝ) (block436RightR : ℝ) →
    y ≠ 0 → y ≠ (block436S1 : ℝ) → y ≠ (block436S2 : ℝ) →
    y ≠ (block436S3 : ℝ) → y ≠ (block436S4 : ℝ) → 0 < block436V y)

theorem block436_reallog_certificate_proof :
    block436_reallog_certificate := by
  exact ⟨block436_left_V_pos, block436_right_V_pos⟩

end Block436
end M1817475
end Erdos1038Lean
