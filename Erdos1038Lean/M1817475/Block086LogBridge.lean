import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block086

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block086

open Set

def block086W1 : Rat := ((34990008331997027 : Rat) / 10000000000000000)
def block086W2 : Rat := (0 : Rat)
def block086W3 : Rat := (0 : Rat)
def block086W4 : Rat := ((736860852193377 : Rat) / 3125000000000000)
def block086S1 : Rat := ((18174751 : Rat) / 10000000)
def block086S2 : Rat := ((511587 : Rat) / 200000)
def block086S3 : Rat := ((107000619 : Rat) / 40000000)
def block086S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block086V (y : ℝ) : ℝ :=
  ratPotential block086W1 block086W2 block086W3 block086W4 block086S1 block086S2 block086S3 block086S4 y

def block086LeftParamsCertificate : Bool :=
  allBoxesSameParams block086LeftBoxes block086W1 block086W2 block086W3 block086W4 block086S1 block086S2 block086S3 block086S4

theorem block086LeftParamsCertificate_eq_true :
    block086LeftParamsCertificate = true := by
  native_decide

theorem block086_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block086LeftL : ℝ) (block086LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block086S1 : ℝ))
    (hy2ne : y ≠ (block086S2 : ℝ))
    (hy3ne : y ≠ (block086S3 : ℝ))
    (hy4ne : y ≠ (block086S4 : ℝ)) :
    0 < block086V y := by
  have hcert := block086LeftCertificate_eq_true
  unfold block086LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block086LeftBoxes) (lo := block086LeftL) (hi := block086LeftR)
    (w1 := block086W1) (w2 := block086W2) (w3 := block086W3) (w4 := block086W4)
    (s1 := block086S1) (s2 := block086S2) (s3 := block086S3) (s4 := block086S4)
    hboxes hcover block086LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block086RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block086RightChunk000 block086W1 block086W2 block086W3 block086W4 block086S1 block086S2 block086S3 block086S4

theorem block086RightChunk000ParamsCertificate_eq_true :
    block086RightChunk000ParamsCertificate = true := by
  native_decide

theorem block086_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block086RightChunk000L : ℝ) (block086RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block086S1 : ℝ))
    (hy2ne : y ≠ (block086S2 : ℝ))
    (hy3ne : y ≠ (block086S3 : ℝ))
    (hy4ne : y ≠ (block086S4 : ℝ)) :
    0 < block086V y := by
  have hcert := block086RightChunk000Certificate_eq_true
  unfold block086RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block086RightChunk000) (lo := block086RightChunk000L) (hi := block086RightChunk000R)
    (w1 := block086W1) (w2 := block086W2) (w3 := block086W3) (w4 := block086W4)
    (s1 := block086S1) (s2 := block086S2) (s3 := block086S3) (s4 := block086S4)
    hboxes hcover block086RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block086_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block086RightL : ℝ) (block086RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block086S1 : ℝ))
    (hy2ne : y ≠ (block086S2 : ℝ))
    (hy3ne : y ≠ (block086S3 : ℝ))
    (hy4ne : y ≠ (block086S4 : ℝ)) :
    0 < block086V y := by
  have hL : (block086RightChunk000L : ℝ) = (block086RightL : ℝ) := by
    norm_num [block086RightChunk000L, block086RightL]
  have hR : (block086RightChunk000R : ℝ) = (block086RightR : ℝ) := by
    norm_num [block086RightChunk000R, block086RightR]
  have hyc : y ∈ Icc (block086RightChunk000L : ℝ) (block086RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block086_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block086_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block086LeftL : ℝ) (block086LeftR : ℝ) →
    y ≠ 0 → y ≠ (block086S1 : ℝ) → y ≠ (block086S2 : ℝ) →
    y ≠ (block086S3 : ℝ) → y ≠ (block086S4 : ℝ) → 0 < block086V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block086RightL : ℝ) (block086RightR : ℝ) →
    y ≠ 0 → y ≠ (block086S1 : ℝ) → y ≠ (block086S2 : ℝ) →
    y ≠ (block086S3 : ℝ) → y ≠ (block086S4 : ℝ) → 0 < block086V y)

theorem block086_reallog_certificate_proof :
    block086_reallog_certificate := by
  exact ⟨block086_left_V_pos, block086_right_V_pos⟩

end Block086
end M1817475
end Erdos1038Lean
