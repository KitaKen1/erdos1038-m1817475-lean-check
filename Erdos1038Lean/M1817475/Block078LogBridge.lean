import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block078

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block078

open Set

def block078W1 : Rat := ((26192094644433 : Rat) / 8000000000000)
def block078W2 : Rat := (0 : Rat)
def block078W3 : Rat := (0 : Rat)
def block078W4 : Rat := ((76231017710379 : Rat) / 312500000000000)
def block078S1 : Rat := ((18174751 : Rat) / 10000000)
def block078S2 : Rat := ((511587 : Rat) / 200000)
def block078S3 : Rat := ((107000619 : Rat) / 40000000)
def block078S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block078V (y : ℝ) : ℝ :=
  ratPotential block078W1 block078W2 block078W3 block078W4 block078S1 block078S2 block078S3 block078S4 y

def block078LeftParamsCertificate : Bool :=
  allBoxesSameParams block078LeftBoxes block078W1 block078W2 block078W3 block078W4 block078S1 block078S2 block078S3 block078S4

theorem block078LeftParamsCertificate_eq_true :
    block078LeftParamsCertificate = true := by
  native_decide

theorem block078_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block078LeftL : ℝ) (block078LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block078S1 : ℝ))
    (hy2ne : y ≠ (block078S2 : ℝ))
    (hy3ne : y ≠ (block078S3 : ℝ))
    (hy4ne : y ≠ (block078S4 : ℝ)) :
    0 < block078V y := by
  have hcert := block078LeftCertificate_eq_true
  unfold block078LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block078LeftBoxes) (lo := block078LeftL) (hi := block078LeftR)
    (w1 := block078W1) (w2 := block078W2) (w3 := block078W3) (w4 := block078W4)
    (s1 := block078S1) (s2 := block078S2) (s3 := block078S3) (s4 := block078S4)
    hboxes hcover block078LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block078RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block078RightChunk000 block078W1 block078W2 block078W3 block078W4 block078S1 block078S2 block078S3 block078S4

theorem block078RightChunk000ParamsCertificate_eq_true :
    block078RightChunk000ParamsCertificate = true := by
  native_decide

theorem block078_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block078RightChunk000L : ℝ) (block078RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block078S1 : ℝ))
    (hy2ne : y ≠ (block078S2 : ℝ))
    (hy3ne : y ≠ (block078S3 : ℝ))
    (hy4ne : y ≠ (block078S4 : ℝ)) :
    0 < block078V y := by
  have hcert := block078RightChunk000Certificate_eq_true
  unfold block078RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block078RightChunk000) (lo := block078RightChunk000L) (hi := block078RightChunk000R)
    (w1 := block078W1) (w2 := block078W2) (w3 := block078W3) (w4 := block078W4)
    (s1 := block078S1) (s2 := block078S2) (s3 := block078S3) (s4 := block078S4)
    hboxes hcover block078RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block078_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block078RightL : ℝ) (block078RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block078S1 : ℝ))
    (hy2ne : y ≠ (block078S2 : ℝ))
    (hy3ne : y ≠ (block078S3 : ℝ))
    (hy4ne : y ≠ (block078S4 : ℝ)) :
    0 < block078V y := by
  have hL : (block078RightChunk000L : ℝ) = (block078RightL : ℝ) := by
    norm_num [block078RightChunk000L, block078RightL]
  have hR : (block078RightChunk000R : ℝ) = (block078RightR : ℝ) := by
    norm_num [block078RightChunk000R, block078RightR]
  have hyc : y ∈ Icc (block078RightChunk000L : ℝ) (block078RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block078_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block078_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block078LeftL : ℝ) (block078LeftR : ℝ) →
    y ≠ 0 → y ≠ (block078S1 : ℝ) → y ≠ (block078S2 : ℝ) →
    y ≠ (block078S3 : ℝ) → y ≠ (block078S4 : ℝ) → 0 < block078V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block078RightL : ℝ) (block078RightR : ℝ) →
    y ≠ 0 → y ≠ (block078S1 : ℝ) → y ≠ (block078S2 : ℝ) →
    y ≠ (block078S3 : ℝ) → y ≠ (block078S4 : ℝ) → 0 < block078V y)

theorem block078_reallog_certificate_proof :
    block078_reallog_certificate := by
  exact ⟨block078_left_V_pos, block078_right_V_pos⟩

end Block078
end M1817475
end Erdos1038Lean
