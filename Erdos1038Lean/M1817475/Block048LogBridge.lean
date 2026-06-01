import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block048

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block048

open Set

def block048W1 : Rat := ((26439567113407243 : Rat) / 10000000000000000)
def block048W2 : Rat := (0 : Rat)
def block048W3 : Rat := (0 : Rat)
def block048W4 : Rat := ((675098593198517 : Rat) / 2500000000000000)
def block048S1 : Rat := ((18174751 : Rat) / 10000000)
def block048S2 : Rat := ((511587 : Rat) / 200000)
def block048S3 : Rat := ((107000619 : Rat) / 40000000)
def block048S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block048V (y : ℝ) : ℝ :=
  ratPotential block048W1 block048W2 block048W3 block048W4 block048S1 block048S2 block048S3 block048S4 y

def block048LeftParamsCertificate : Bool :=
  allBoxesSameParams block048LeftBoxes block048W1 block048W2 block048W3 block048W4 block048S1 block048S2 block048S3 block048S4

theorem block048LeftParamsCertificate_eq_true :
    block048LeftParamsCertificate = true := by
  native_decide

theorem block048_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block048LeftL : ℝ) (block048LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block048S1 : ℝ))
    (hy2ne : y ≠ (block048S2 : ℝ))
    (hy3ne : y ≠ (block048S3 : ℝ))
    (hy4ne : y ≠ (block048S4 : ℝ)) :
    0 < block048V y := by
  have hcert := block048LeftCertificate_eq_true
  unfold block048LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block048LeftBoxes) (lo := block048LeftL) (hi := block048LeftR)
    (w1 := block048W1) (w2 := block048W2) (w3 := block048W3) (w4 := block048W4)
    (s1 := block048S1) (s2 := block048S2) (s3 := block048S3) (s4 := block048S4)
    hboxes hcover block048LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block048RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block048RightChunk000 block048W1 block048W2 block048W3 block048W4 block048S1 block048S2 block048S3 block048S4

theorem block048RightChunk000ParamsCertificate_eq_true :
    block048RightChunk000ParamsCertificate = true := by
  native_decide

theorem block048_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block048RightChunk000L : ℝ) (block048RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block048S1 : ℝ))
    (hy2ne : y ≠ (block048S2 : ℝ))
    (hy3ne : y ≠ (block048S3 : ℝ))
    (hy4ne : y ≠ (block048S4 : ℝ)) :
    0 < block048V y := by
  have hcert := block048RightChunk000Certificate_eq_true
  unfold block048RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block048RightChunk000) (lo := block048RightChunk000L) (hi := block048RightChunk000R)
    (w1 := block048W1) (w2 := block048W2) (w3 := block048W3) (w4 := block048W4)
    (s1 := block048S1) (s2 := block048S2) (s3 := block048S3) (s4 := block048S4)
    hboxes hcover block048RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block048_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block048RightL : ℝ) (block048RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block048S1 : ℝ))
    (hy2ne : y ≠ (block048S2 : ℝ))
    (hy3ne : y ≠ (block048S3 : ℝ))
    (hy4ne : y ≠ (block048S4 : ℝ)) :
    0 < block048V y := by
  have hL : (block048RightChunk000L : ℝ) = (block048RightL : ℝ) := by
    norm_num [block048RightChunk000L, block048RightL]
  have hR : (block048RightChunk000R : ℝ) = (block048RightR : ℝ) := by
    norm_num [block048RightChunk000R, block048RightR]
  have hyc : y ∈ Icc (block048RightChunk000L : ℝ) (block048RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block048_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block048_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block048LeftL : ℝ) (block048LeftR : ℝ) →
    y ≠ 0 → y ≠ (block048S1 : ℝ) → y ≠ (block048S2 : ℝ) →
    y ≠ (block048S3 : ℝ) → y ≠ (block048S4 : ℝ) → 0 < block048V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block048RightL : ℝ) (block048RightR : ℝ) →
    y ≠ 0 → y ≠ (block048S1 : ℝ) → y ≠ (block048S2 : ℝ) →
    y ≠ (block048S3 : ℝ) → y ≠ (block048S4 : ℝ) → 0 < block048V y)

theorem block048_reallog_certificate_proof :
    block048_reallog_certificate := by
  exact ⟨block048_left_V_pos, block048_right_V_pos⟩

end Block048
end M1817475
end Erdos1038Lean
