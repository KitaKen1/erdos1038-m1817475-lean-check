import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block454

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block454

open Set

def block454W1 : Rat := ((2930600323885573 : Rat) / 5000000000000000)
def block454W2 : Rat := (0 : Rat)
def block454W3 : Rat := ((33841437903256977 : Rat) / 100000000000000000)
def block454W4 : Rat := ((1286335329433573 : Rat) / 20000000000000000)
def block454S1 : Rat := ((18174751 : Rat) / 10000000)
def block454S2 : Rat := ((511587 : Rat) / 200000)
def block454S3 : Rat := ((26251652517857142879 : Rat) / 10000000000000000000)
def block454S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block454V (y : ℝ) : ℝ :=
  ratPotential block454W1 block454W2 block454W3 block454W4 block454S1 block454S2 block454S3 block454S4 y

def block454LeftParamsCertificate : Bool :=
  allBoxesSameParams block454LeftBoxes block454W1 block454W2 block454W3 block454W4 block454S1 block454S2 block454S3 block454S4

theorem block454LeftParamsCertificate_eq_true :
    block454LeftParamsCertificate = true := by
  native_decide

theorem block454_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block454LeftL : ℝ) (block454LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block454S1 : ℝ))
    (hy2ne : y ≠ (block454S2 : ℝ))
    (hy3ne : y ≠ (block454S3 : ℝ))
    (hy4ne : y ≠ (block454S4 : ℝ)) :
    0 < block454V y := by
  have hcert := block454LeftCertificate_eq_true
  unfold block454LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block454LeftBoxes) (lo := block454LeftL) (hi := block454LeftR)
    (w1 := block454W1) (w2 := block454W2) (w3 := block454W3) (w4 := block454W4)
    (s1 := block454S1) (s2 := block454S2) (s3 := block454S3) (s4 := block454S4)
    hboxes hcover block454LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block454RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block454RightChunk000 block454W1 block454W2 block454W3 block454W4 block454S1 block454S2 block454S3 block454S4

theorem block454RightChunk000ParamsCertificate_eq_true :
    block454RightChunk000ParamsCertificate = true := by
  native_decide

theorem block454_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block454RightChunk000L : ℝ) (block454RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block454S1 : ℝ))
    (hy2ne : y ≠ (block454S2 : ℝ))
    (hy3ne : y ≠ (block454S3 : ℝ))
    (hy4ne : y ≠ (block454S4 : ℝ)) :
    0 < block454V y := by
  have hcert := block454RightChunk000Certificate_eq_true
  unfold block454RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block454RightChunk000) (lo := block454RightChunk000L) (hi := block454RightChunk000R)
    (w1 := block454W1) (w2 := block454W2) (w3 := block454W3) (w4 := block454W4)
    (s1 := block454S1) (s2 := block454S2) (s3 := block454S3) (s4 := block454S4)
    hboxes hcover block454RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block454_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block454RightL : ℝ) (block454RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block454S1 : ℝ))
    (hy2ne : y ≠ (block454S2 : ℝ))
    (hy3ne : y ≠ (block454S3 : ℝ))
    (hy4ne : y ≠ (block454S4 : ℝ)) :
    0 < block454V y := by
  have hL : (block454RightChunk000L : ℝ) = (block454RightL : ℝ) := by
    norm_num [block454RightChunk000L, block454RightL]
  have hR : (block454RightChunk000R : ℝ) = (block454RightR : ℝ) := by
    norm_num [block454RightChunk000R, block454RightR]
  have hyc : y ∈ Icc (block454RightChunk000L : ℝ) (block454RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block454_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block454_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block454LeftL : ℝ) (block454LeftR : ℝ) →
    y ≠ 0 → y ≠ (block454S1 : ℝ) → y ≠ (block454S2 : ℝ) →
    y ≠ (block454S3 : ℝ) → y ≠ (block454S4 : ℝ) → 0 < block454V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block454RightL : ℝ) (block454RightR : ℝ) →
    y ≠ 0 → y ≠ (block454S1 : ℝ) → y ≠ (block454S2 : ℝ) →
    y ≠ (block454S3 : ℝ) → y ≠ (block454S4 : ℝ) → 0 < block454V y)

theorem block454_reallog_certificate_proof :
    block454_reallog_certificate := by
  exact ⟨block454_left_V_pos, block454_right_V_pos⟩

end Block454
end M1817475
end Erdos1038Lean
