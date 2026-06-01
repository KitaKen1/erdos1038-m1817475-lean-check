import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block457

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block457

open Set

def block457W1 : Rat := ((5776122880916411 : Rat) / 10000000000000000)
def block457W2 : Rat := (0 : Rat)
def block457W3 : Rat := ((3426391236583687 : Rat) / 10000000000000000)
def block457W4 : Rat := ((1551156508761161 : Rat) / 25000000000000000)
def block457S1 : Rat := ((18174751 : Rat) / 10000000)
def block457S2 : Rat := ((511587 : Rat) / 200000)
def block457S3 : Rat := ((131199615267857142969 : Rat) / 50000000000000000000)
def block457S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block457V (y : ℝ) : ℝ :=
  ratPotential block457W1 block457W2 block457W3 block457W4 block457S1 block457S2 block457S3 block457S4 y

def block457LeftParamsCertificate : Bool :=
  allBoxesSameParams block457LeftBoxes block457W1 block457W2 block457W3 block457W4 block457S1 block457S2 block457S3 block457S4

theorem block457LeftParamsCertificate_eq_true :
    block457LeftParamsCertificate = true := by
  native_decide

theorem block457_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block457LeftL : ℝ) (block457LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block457S1 : ℝ))
    (hy2ne : y ≠ (block457S2 : ℝ))
    (hy3ne : y ≠ (block457S3 : ℝ))
    (hy4ne : y ≠ (block457S4 : ℝ)) :
    0 < block457V y := by
  have hcert := block457LeftCertificate_eq_true
  unfold block457LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block457LeftBoxes) (lo := block457LeftL) (hi := block457LeftR)
    (w1 := block457W1) (w2 := block457W2) (w3 := block457W3) (w4 := block457W4)
    (s1 := block457S1) (s2 := block457S2) (s3 := block457S3) (s4 := block457S4)
    hboxes hcover block457LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block457RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block457RightChunk000 block457W1 block457W2 block457W3 block457W4 block457S1 block457S2 block457S3 block457S4

theorem block457RightChunk000ParamsCertificate_eq_true :
    block457RightChunk000ParamsCertificate = true := by
  native_decide

theorem block457_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block457RightChunk000L : ℝ) (block457RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block457S1 : ℝ))
    (hy2ne : y ≠ (block457S2 : ℝ))
    (hy3ne : y ≠ (block457S3 : ℝ))
    (hy4ne : y ≠ (block457S4 : ℝ)) :
    0 < block457V y := by
  have hcert := block457RightChunk000Certificate_eq_true
  unfold block457RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block457RightChunk000) (lo := block457RightChunk000L) (hi := block457RightChunk000R)
    (w1 := block457W1) (w2 := block457W2) (w3 := block457W3) (w4 := block457W4)
    (s1 := block457S1) (s2 := block457S2) (s3 := block457S3) (s4 := block457S4)
    hboxes hcover block457RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block457_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block457RightL : ℝ) (block457RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block457S1 : ℝ))
    (hy2ne : y ≠ (block457S2 : ℝ))
    (hy3ne : y ≠ (block457S3 : ℝ))
    (hy4ne : y ≠ (block457S4 : ℝ)) :
    0 < block457V y := by
  have hL : (block457RightChunk000L : ℝ) = (block457RightL : ℝ) := by
    norm_num [block457RightChunk000L, block457RightL]
  have hR : (block457RightChunk000R : ℝ) = (block457RightR : ℝ) := by
    norm_num [block457RightChunk000R, block457RightR]
  have hyc : y ∈ Icc (block457RightChunk000L : ℝ) (block457RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block457_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block457_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block457LeftL : ℝ) (block457LeftR : ℝ) →
    y ≠ 0 → y ≠ (block457S1 : ℝ) → y ≠ (block457S2 : ℝ) →
    y ≠ (block457S3 : ℝ) → y ≠ (block457S4 : ℝ) → 0 < block457V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block457RightL : ℝ) (block457RightR : ℝ) →
    y ≠ 0 → y ≠ (block457S1 : ℝ) → y ≠ (block457S2 : ℝ) →
    y ≠ (block457S3 : ℝ) → y ≠ (block457S4 : ℝ) → 0 < block457V y)

theorem block457_reallog_certificate_proof :
    block457_reallog_certificate := by
  exact ⟨block457_left_V_pos, block457_right_V_pos⟩

end Block457
end M1817475
end Erdos1038Lean
