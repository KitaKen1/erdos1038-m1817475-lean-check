import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block056

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block056

open Set

def block056W1 : Rat := ((2786268134675323 : Rat) / 1000000000000000)
def block056W2 : Rat := (0 : Rat)
def block056W3 : Rat := (0 : Rat)
def block056W4 : Rat := ((329555054626389 : Rat) / 1250000000000000)
def block056S1 : Rat := ((18174751 : Rat) / 10000000)
def block056S2 : Rat := ((511587 : Rat) / 200000)
def block056S3 : Rat := ((107000619 : Rat) / 40000000)
def block056S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block056V (y : ℝ) : ℝ :=
  ratPotential block056W1 block056W2 block056W3 block056W4 block056S1 block056S2 block056S3 block056S4 y

def block056LeftParamsCertificate : Bool :=
  allBoxesSameParams block056LeftBoxes block056W1 block056W2 block056W3 block056W4 block056S1 block056S2 block056S3 block056S4

theorem block056LeftParamsCertificate_eq_true :
    block056LeftParamsCertificate = true := by
  native_decide

theorem block056_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block056LeftL : ℝ) (block056LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block056S1 : ℝ))
    (hy2ne : y ≠ (block056S2 : ℝ))
    (hy3ne : y ≠ (block056S3 : ℝ))
    (hy4ne : y ≠ (block056S4 : ℝ)) :
    0 < block056V y := by
  have hcert := block056LeftCertificate_eq_true
  unfold block056LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block056LeftBoxes) (lo := block056LeftL) (hi := block056LeftR)
    (w1 := block056W1) (w2 := block056W2) (w3 := block056W3) (w4 := block056W4)
    (s1 := block056S1) (s2 := block056S2) (s3 := block056S3) (s4 := block056S4)
    hboxes hcover block056LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block056RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block056RightChunk000 block056W1 block056W2 block056W3 block056W4 block056S1 block056S2 block056S3 block056S4

theorem block056RightChunk000ParamsCertificate_eq_true :
    block056RightChunk000ParamsCertificate = true := by
  native_decide

theorem block056_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block056RightChunk000L : ℝ) (block056RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block056S1 : ℝ))
    (hy2ne : y ≠ (block056S2 : ℝ))
    (hy3ne : y ≠ (block056S3 : ℝ))
    (hy4ne : y ≠ (block056S4 : ℝ)) :
    0 < block056V y := by
  have hcert := block056RightChunk000Certificate_eq_true
  unfold block056RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block056RightChunk000) (lo := block056RightChunk000L) (hi := block056RightChunk000R)
    (w1 := block056W1) (w2 := block056W2) (w3 := block056W3) (w4 := block056W4)
    (s1 := block056S1) (s2 := block056S2) (s3 := block056S3) (s4 := block056S4)
    hboxes hcover block056RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block056_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block056RightL : ℝ) (block056RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block056S1 : ℝ))
    (hy2ne : y ≠ (block056S2 : ℝ))
    (hy3ne : y ≠ (block056S3 : ℝ))
    (hy4ne : y ≠ (block056S4 : ℝ)) :
    0 < block056V y := by
  have hL : (block056RightChunk000L : ℝ) = (block056RightL : ℝ) := by
    norm_num [block056RightChunk000L, block056RightL]
  have hR : (block056RightChunk000R : ℝ) = (block056RightR : ℝ) := by
    norm_num [block056RightChunk000R, block056RightR]
  have hyc : y ∈ Icc (block056RightChunk000L : ℝ) (block056RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block056_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block056_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block056LeftL : ℝ) (block056LeftR : ℝ) →
    y ≠ 0 → y ≠ (block056S1 : ℝ) → y ≠ (block056S2 : ℝ) →
    y ≠ (block056S3 : ℝ) → y ≠ (block056S4 : ℝ) → 0 < block056V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block056RightL : ℝ) (block056RightR : ℝ) →
    y ≠ 0 → y ≠ (block056S1 : ℝ) → y ≠ (block056S2 : ℝ) →
    y ≠ (block056S3 : ℝ) → y ≠ (block056S4 : ℝ) → 0 < block056V y)

theorem block056_reallog_certificate_proof :
    block056_reallog_certificate := by
  exact ⟨block056_left_V_pos, block056_right_V_pos⟩

end Block056
end M1817475
end Erdos1038Lean
