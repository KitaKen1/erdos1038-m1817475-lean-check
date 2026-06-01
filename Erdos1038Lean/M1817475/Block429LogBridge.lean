import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block429

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block429

open Set

def block429W1 : Rat := ((6591128418710827 : Rat) / 10000000000000000)
def block429W2 : Rat := (0 : Rat)
def block429W3 : Rat := ((6138143388182441 : Rat) / 20000000000000000)
def block429W4 : Rat := ((4011764188478043 : Rat) / 50000000000000000)
def block429S1 : Rat := ((18174751 : Rat) / 10000000)
def block429S2 : Rat := ((511587 : Rat) / 200000)
def block429S3 : Rat := ((26349398053571428589 : Rat) / 10000000000000000000)
def block429S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block429V (y : ℝ) : ℝ :=
  ratPotential block429W1 block429W2 block429W3 block429W4 block429S1 block429S2 block429S3 block429S4 y

def block429LeftParamsCertificate : Bool :=
  allBoxesSameParams block429LeftBoxes block429W1 block429W2 block429W3 block429W4 block429S1 block429S2 block429S3 block429S4

theorem block429LeftParamsCertificate_eq_true :
    block429LeftParamsCertificate = true := by
  native_decide

theorem block429_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block429LeftL : ℝ) (block429LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block429S1 : ℝ))
    (hy2ne : y ≠ (block429S2 : ℝ))
    (hy3ne : y ≠ (block429S3 : ℝ))
    (hy4ne : y ≠ (block429S4 : ℝ)) :
    0 < block429V y := by
  have hcert := block429LeftCertificate_eq_true
  unfold block429LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block429LeftBoxes) (lo := block429LeftL) (hi := block429LeftR)
    (w1 := block429W1) (w2 := block429W2) (w3 := block429W3) (w4 := block429W4)
    (s1 := block429S1) (s2 := block429S2) (s3 := block429S3) (s4 := block429S4)
    hboxes hcover block429LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block429RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block429RightChunk000 block429W1 block429W2 block429W3 block429W4 block429S1 block429S2 block429S3 block429S4

theorem block429RightChunk000ParamsCertificate_eq_true :
    block429RightChunk000ParamsCertificate = true := by
  native_decide

theorem block429_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block429RightChunk000L : ℝ) (block429RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block429S1 : ℝ))
    (hy2ne : y ≠ (block429S2 : ℝ))
    (hy3ne : y ≠ (block429S3 : ℝ))
    (hy4ne : y ≠ (block429S4 : ℝ)) :
    0 < block429V y := by
  have hcert := block429RightChunk000Certificate_eq_true
  unfold block429RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block429RightChunk000) (lo := block429RightChunk000L) (hi := block429RightChunk000R)
    (w1 := block429W1) (w2 := block429W2) (w3 := block429W3) (w4 := block429W4)
    (s1 := block429S1) (s2 := block429S2) (s3 := block429S3) (s4 := block429S4)
    hboxes hcover block429RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block429_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block429RightL : ℝ) (block429RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block429S1 : ℝ))
    (hy2ne : y ≠ (block429S2 : ℝ))
    (hy3ne : y ≠ (block429S3 : ℝ))
    (hy4ne : y ≠ (block429S4 : ℝ)) :
    0 < block429V y := by
  have hL : (block429RightChunk000L : ℝ) = (block429RightL : ℝ) := by
    norm_num [block429RightChunk000L, block429RightL]
  have hR : (block429RightChunk000R : ℝ) = (block429RightR : ℝ) := by
    norm_num [block429RightChunk000R, block429RightR]
  have hyc : y ∈ Icc (block429RightChunk000L : ℝ) (block429RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block429_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block429_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block429LeftL : ℝ) (block429LeftR : ℝ) →
    y ≠ 0 → y ≠ (block429S1 : ℝ) → y ≠ (block429S2 : ℝ) →
    y ≠ (block429S3 : ℝ) → y ≠ (block429S4 : ℝ) → 0 < block429V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block429RightL : ℝ) (block429RightR : ℝ) →
    y ≠ 0 → y ≠ (block429S1 : ℝ) → y ≠ (block429S2 : ℝ) →
    y ≠ (block429S3 : ℝ) → y ≠ (block429S4 : ℝ) → 0 < block429V y)

theorem block429_reallog_certificate_proof :
    block429_reallog_certificate := by
  exact ⟨block429_left_V_pos, block429_right_V_pos⟩

end Block429
end M1817475
end Erdos1038Lean
