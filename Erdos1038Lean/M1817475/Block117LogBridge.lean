import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block117

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block117

open Set

def block117W1 : Rat := ((4779610570296919 : Rat) / 2000000000000000)
def block117W2 : Rat := (0 : Rat)
def block117W3 : Rat := ((8346581464692011 : Rat) / 100000000000000000)
def block117W4 : Rat := ((16576423598588647 : Rat) / 100000000000000000)
def block117S1 : Rat := ((18174751 : Rat) / 10000000)
def block117S2 : Rat := ((511587 : Rat) / 200000)
def block117S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block117S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block117V (y : ℝ) : ℝ :=
  ratPotential block117W1 block117W2 block117W3 block117W4 block117S1 block117S2 block117S3 block117S4 y

def block117LeftParamsCertificate : Bool :=
  allBoxesSameParams block117LeftBoxes block117W1 block117W2 block117W3 block117W4 block117S1 block117S2 block117S3 block117S4

theorem block117LeftParamsCertificate_eq_true :
    block117LeftParamsCertificate = true := by
  native_decide

theorem block117_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block117LeftL : ℝ) (block117LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block117S1 : ℝ))
    (hy2ne : y ≠ (block117S2 : ℝ))
    (hy3ne : y ≠ (block117S3 : ℝ))
    (hy4ne : y ≠ (block117S4 : ℝ)) :
    0 < block117V y := by
  have hcert := block117LeftCertificate_eq_true
  unfold block117LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block117LeftBoxes) (lo := block117LeftL) (hi := block117LeftR)
    (w1 := block117W1) (w2 := block117W2) (w3 := block117W3) (w4 := block117W4)
    (s1 := block117S1) (s2 := block117S2) (s3 := block117S3) (s4 := block117S4)
    hboxes hcover block117LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block117RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block117RightChunk000 block117W1 block117W2 block117W3 block117W4 block117S1 block117S2 block117S3 block117S4

theorem block117RightChunk000ParamsCertificate_eq_true :
    block117RightChunk000ParamsCertificate = true := by
  native_decide

theorem block117_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block117RightChunk000L : ℝ) (block117RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block117S1 : ℝ))
    (hy2ne : y ≠ (block117S2 : ℝ))
    (hy3ne : y ≠ (block117S3 : ℝ))
    (hy4ne : y ≠ (block117S4 : ℝ)) :
    0 < block117V y := by
  have hcert := block117RightChunk000Certificate_eq_true
  unfold block117RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block117RightChunk000) (lo := block117RightChunk000L) (hi := block117RightChunk000R)
    (w1 := block117W1) (w2 := block117W2) (w3 := block117W3) (w4 := block117W4)
    (s1 := block117S1) (s2 := block117S2) (s3 := block117S3) (s4 := block117S4)
    hboxes hcover block117RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block117_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block117RightL : ℝ) (block117RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block117S1 : ℝ))
    (hy2ne : y ≠ (block117S2 : ℝ))
    (hy3ne : y ≠ (block117S3 : ℝ))
    (hy4ne : y ≠ (block117S4 : ℝ)) :
    0 < block117V y := by
  have hL : (block117RightChunk000L : ℝ) = (block117RightL : ℝ) := by
    norm_num [block117RightChunk000L, block117RightL]
  have hR : (block117RightChunk000R : ℝ) = (block117RightR : ℝ) := by
    norm_num [block117RightChunk000R, block117RightR]
  have hyc : y ∈ Icc (block117RightChunk000L : ℝ) (block117RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block117_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block117_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block117LeftL : ℝ) (block117LeftR : ℝ) →
    y ≠ 0 → y ≠ (block117S1 : ℝ) → y ≠ (block117S2 : ℝ) →
    y ≠ (block117S3 : ℝ) → y ≠ (block117S4 : ℝ) → 0 < block117V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block117RightL : ℝ) (block117RightR : ℝ) →
    y ≠ 0 → y ≠ (block117S1 : ℝ) → y ≠ (block117S2 : ℝ) →
    y ≠ (block117S3 : ℝ) → y ≠ (block117S4 : ℝ) → 0 < block117V y)

theorem block117_reallog_certificate_proof :
    block117_reallog_certificate := by
  exact ⟨block117_left_V_pos, block117_right_V_pos⟩

end Block117
end M1817475
end Erdos1038Lean
