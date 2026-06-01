import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block493

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block493

open Set

def block493W1 : Rat := ((299994775919221 : Rat) / 625000000000000)
def block493W2 : Rat := (0 : Rat)
def block493W3 : Rat := ((4014376377794891 : Rat) / 10000000000000000)
def block493W4 : Rat := ((14085941399310159 : Rat) / 500000000000000000)
def block493S1 : Rat := ((18174751 : Rat) / 10000000)
def block493S2 : Rat := ((511587 : Rat) / 200000)
def block493S3 : Rat := ((130495847410714285857 : Rat) / 50000000000000000000)
def block493S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block493V (y : ℝ) : ℝ :=
  ratPotential block493W1 block493W2 block493W3 block493W4 block493S1 block493S2 block493S3 block493S4 y

def block493LeftParamsCertificate : Bool :=
  allBoxesSameParams block493LeftBoxes block493W1 block493W2 block493W3 block493W4 block493S1 block493S2 block493S3 block493S4

theorem block493LeftParamsCertificate_eq_true :
    block493LeftParamsCertificate = true := by
  native_decide

theorem block493_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block493LeftL : ℝ) (block493LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block493S1 : ℝ))
    (hy2ne : y ≠ (block493S2 : ℝ))
    (hy3ne : y ≠ (block493S3 : ℝ))
    (hy4ne : y ≠ (block493S4 : ℝ)) :
    0 < block493V y := by
  have hcert := block493LeftCertificate_eq_true
  unfold block493LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block493LeftBoxes) (lo := block493LeftL) (hi := block493LeftR)
    (w1 := block493W1) (w2 := block493W2) (w3 := block493W3) (w4 := block493W4)
    (s1 := block493S1) (s2 := block493S2) (s3 := block493S3) (s4 := block493S4)
    hboxes hcover block493LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block493RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block493RightChunk000 block493W1 block493W2 block493W3 block493W4 block493S1 block493S2 block493S3 block493S4

theorem block493RightChunk000ParamsCertificate_eq_true :
    block493RightChunk000ParamsCertificate = true := by
  native_decide

theorem block493_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block493RightChunk000L : ℝ) (block493RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block493S1 : ℝ))
    (hy2ne : y ≠ (block493S2 : ℝ))
    (hy3ne : y ≠ (block493S3 : ℝ))
    (hy4ne : y ≠ (block493S4 : ℝ)) :
    0 < block493V y := by
  have hcert := block493RightChunk000Certificate_eq_true
  unfold block493RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block493RightChunk000) (lo := block493RightChunk000L) (hi := block493RightChunk000R)
    (w1 := block493W1) (w2 := block493W2) (w3 := block493W3) (w4 := block493W4)
    (s1 := block493S1) (s2 := block493S2) (s3 := block493S3) (s4 := block493S4)
    hboxes hcover block493RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block493_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block493RightL : ℝ) (block493RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block493S1 : ℝ))
    (hy2ne : y ≠ (block493S2 : ℝ))
    (hy3ne : y ≠ (block493S3 : ℝ))
    (hy4ne : y ≠ (block493S4 : ℝ)) :
    0 < block493V y := by
  have hL : (block493RightChunk000L : ℝ) = (block493RightL : ℝ) := by
    norm_num [block493RightChunk000L, block493RightL]
  have hR : (block493RightChunk000R : ℝ) = (block493RightR : ℝ) := by
    norm_num [block493RightChunk000R, block493RightR]
  have hyc : y ∈ Icc (block493RightChunk000L : ℝ) (block493RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block493_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block493_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block493LeftL : ℝ) (block493LeftR : ℝ) →
    y ≠ 0 → y ≠ (block493S1 : ℝ) → y ≠ (block493S2 : ℝ) →
    y ≠ (block493S3 : ℝ) → y ≠ (block493S4 : ℝ) → 0 < block493V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block493RightL : ℝ) (block493RightR : ℝ) →
    y ≠ 0 → y ≠ (block493S1 : ℝ) → y ≠ (block493S2 : ℝ) →
    y ≠ (block493S3 : ℝ) → y ≠ (block493S4 : ℝ) → 0 < block493V y)

theorem block493_reallog_certificate_proof :
    block493_reallog_certificate := by
  exact ⟨block493_left_V_pos, block493_right_V_pos⟩

end Block493
end M1817475
end Erdos1038Lean
