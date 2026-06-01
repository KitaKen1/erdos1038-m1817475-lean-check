import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block131

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block131

open Set

def block131W1 : Rat := ((25485852585364293 : Rat) / 10000000000000000)
def block131W2 : Rat := (0 : Rat)
def block131W3 : Rat := ((10739714228807083 : Rat) / 100000000000000000)
def block131W4 : Rat := ((13393713001581653 : Rat) / 100000000000000000)
def block131S1 : Rat := ((18174751 : Rat) / 10000000)
def block131S2 : Rat := ((511587 : Rat) / 200000)
def block131S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block131S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block131V (y : ℝ) : ℝ :=
  ratPotential block131W1 block131W2 block131W3 block131W4 block131S1 block131S2 block131S3 block131S4 y

def block131LeftParamsCertificate : Bool :=
  allBoxesSameParams block131LeftBoxes block131W1 block131W2 block131W3 block131W4 block131S1 block131S2 block131S3 block131S4

theorem block131LeftParamsCertificate_eq_true :
    block131LeftParamsCertificate = true := by
  native_decide

theorem block131_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block131LeftL : ℝ) (block131LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block131S1 : ℝ))
    (hy2ne : y ≠ (block131S2 : ℝ))
    (hy3ne : y ≠ (block131S3 : ℝ))
    (hy4ne : y ≠ (block131S4 : ℝ)) :
    0 < block131V y := by
  have hcert := block131LeftCertificate_eq_true
  unfold block131LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block131LeftBoxes) (lo := block131LeftL) (hi := block131LeftR)
    (w1 := block131W1) (w2 := block131W2) (w3 := block131W3) (w4 := block131W4)
    (s1 := block131S1) (s2 := block131S2) (s3 := block131S3) (s4 := block131S4)
    hboxes hcover block131LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block131RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block131RightChunk000 block131W1 block131W2 block131W3 block131W4 block131S1 block131S2 block131S3 block131S4

theorem block131RightChunk000ParamsCertificate_eq_true :
    block131RightChunk000ParamsCertificate = true := by
  native_decide

theorem block131_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block131RightChunk000L : ℝ) (block131RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block131S1 : ℝ))
    (hy2ne : y ≠ (block131S2 : ℝ))
    (hy3ne : y ≠ (block131S3 : ℝ))
    (hy4ne : y ≠ (block131S4 : ℝ)) :
    0 < block131V y := by
  have hcert := block131RightChunk000Certificate_eq_true
  unfold block131RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block131RightChunk000) (lo := block131RightChunk000L) (hi := block131RightChunk000R)
    (w1 := block131W1) (w2 := block131W2) (w3 := block131W3) (w4 := block131W4)
    (s1 := block131S1) (s2 := block131S2) (s3 := block131S3) (s4 := block131S4)
    hboxes hcover block131RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block131_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block131RightL : ℝ) (block131RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block131S1 : ℝ))
    (hy2ne : y ≠ (block131S2 : ℝ))
    (hy3ne : y ≠ (block131S3 : ℝ))
    (hy4ne : y ≠ (block131S4 : ℝ)) :
    0 < block131V y := by
  have hL : (block131RightChunk000L : ℝ) = (block131RightL : ℝ) := by
    norm_num [block131RightChunk000L, block131RightL]
  have hR : (block131RightChunk000R : ℝ) = (block131RightR : ℝ) := by
    norm_num [block131RightChunk000R, block131RightR]
  have hyc : y ∈ Icc (block131RightChunk000L : ℝ) (block131RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block131_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block131_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block131LeftL : ℝ) (block131LeftR : ℝ) →
    y ≠ 0 → y ≠ (block131S1 : ℝ) → y ≠ (block131S2 : ℝ) →
    y ≠ (block131S3 : ℝ) → y ≠ (block131S4 : ℝ) → 0 < block131V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block131RightL : ℝ) (block131RightR : ℝ) →
    y ≠ 0 → y ≠ (block131S1 : ℝ) → y ≠ (block131S2 : ℝ) →
    y ≠ (block131S3 : ℝ) → y ≠ (block131S4 : ℝ) → 0 < block131V y)

theorem block131_reallog_certificate_proof :
    block131_reallog_certificate := by
  exact ⟨block131_left_V_pos, block131_right_V_pos⟩

end Block131
end M1817475
end Erdos1038Lean
