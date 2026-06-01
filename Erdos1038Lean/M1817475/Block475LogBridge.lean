import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block475

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block475

open Set

def block475W1 : Rat := ((5278623205509281 : Rat) / 10000000000000000)
def block475W2 : Rat := (0 : Rat)
def block475W3 : Rat := ((18500367016628233 : Rat) / 50000000000000000)
def block475W4 : Rat := ((1169194612632389 : Rat) / 25000000000000000)
def block475S1 : Rat := ((18174751 : Rat) / 10000000)
def block475S2 : Rat := ((511587 : Rat) / 200000)
def block475S3 : Rat := ((130847731339285714413 : Rat) / 50000000000000000000)
def block475S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block475V (y : ℝ) : ℝ :=
  ratPotential block475W1 block475W2 block475W3 block475W4 block475S1 block475S2 block475S3 block475S4 y

def block475LeftParamsCertificate : Bool :=
  allBoxesSameParams block475LeftBoxes block475W1 block475W2 block475W3 block475W4 block475S1 block475S2 block475S3 block475S4

theorem block475LeftParamsCertificate_eq_true :
    block475LeftParamsCertificate = true := by
  native_decide

theorem block475_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block475LeftL : ℝ) (block475LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block475S1 : ℝ))
    (hy2ne : y ≠ (block475S2 : ℝ))
    (hy3ne : y ≠ (block475S3 : ℝ))
    (hy4ne : y ≠ (block475S4 : ℝ)) :
    0 < block475V y := by
  have hcert := block475LeftCertificate_eq_true
  unfold block475LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block475LeftBoxes) (lo := block475LeftL) (hi := block475LeftR)
    (w1 := block475W1) (w2 := block475W2) (w3 := block475W3) (w4 := block475W4)
    (s1 := block475S1) (s2 := block475S2) (s3 := block475S3) (s4 := block475S4)
    hboxes hcover block475LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block475RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block475RightChunk000 block475W1 block475W2 block475W3 block475W4 block475S1 block475S2 block475S3 block475S4

theorem block475RightChunk000ParamsCertificate_eq_true :
    block475RightChunk000ParamsCertificate = true := by
  native_decide

theorem block475_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block475RightChunk000L : ℝ) (block475RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block475S1 : ℝ))
    (hy2ne : y ≠ (block475S2 : ℝ))
    (hy3ne : y ≠ (block475S3 : ℝ))
    (hy4ne : y ≠ (block475S4 : ℝ)) :
    0 < block475V y := by
  have hcert := block475RightChunk000Certificate_eq_true
  unfold block475RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block475RightChunk000) (lo := block475RightChunk000L) (hi := block475RightChunk000R)
    (w1 := block475W1) (w2 := block475W2) (w3 := block475W3) (w4 := block475W4)
    (s1 := block475S1) (s2 := block475S2) (s3 := block475S3) (s4 := block475S4)
    hboxes hcover block475RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block475_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block475RightL : ℝ) (block475RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block475S1 : ℝ))
    (hy2ne : y ≠ (block475S2 : ℝ))
    (hy3ne : y ≠ (block475S3 : ℝ))
    (hy4ne : y ≠ (block475S4 : ℝ)) :
    0 < block475V y := by
  have hL : (block475RightChunk000L : ℝ) = (block475RightL : ℝ) := by
    norm_num [block475RightChunk000L, block475RightL]
  have hR : (block475RightChunk000R : ℝ) = (block475RightR : ℝ) := by
    norm_num [block475RightChunk000R, block475RightR]
  have hyc : y ∈ Icc (block475RightChunk000L : ℝ) (block475RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block475_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block475_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block475LeftL : ℝ) (block475LeftR : ℝ) →
    y ≠ 0 → y ≠ (block475S1 : ℝ) → y ≠ (block475S2 : ℝ) →
    y ≠ (block475S3 : ℝ) → y ≠ (block475S4 : ℝ) → 0 < block475V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block475RightL : ℝ) (block475RightR : ℝ) →
    y ≠ 0 → y ≠ (block475S1 : ℝ) → y ≠ (block475S2 : ℝ) →
    y ≠ (block475S3 : ℝ) → y ≠ (block475S4 : ℝ) → 0 < block475V y)

theorem block475_reallog_certificate_proof :
    block475_reallog_certificate := by
  exact ⟨block475_left_V_pos, block475_right_V_pos⟩

end Block475
end M1817475
end Erdos1038Lean
