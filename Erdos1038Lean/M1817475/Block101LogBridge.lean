import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block101

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block101

open Set

def block101W1 : Rat := ((13059035029177273 : Rat) / 5000000000000000)
def block101W2 : Rat := (0 : Rat)
def block101W3 : Rat := ((200862572331579 : Rat) / 4000000000000000)
def block101W4 : Rat := ((1974887068458007 : Rat) / 10000000000000000)
def block101S1 : Rat := ((18174751 : Rat) / 10000000)
def block101S2 : Rat := ((511587 : Rat) / 200000)
def block101S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block101S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block101V (y : ℝ) : ℝ :=
  ratPotential block101W1 block101W2 block101W3 block101W4 block101S1 block101S2 block101S3 block101S4 y

def block101LeftParamsCertificate : Bool :=
  allBoxesSameParams block101LeftBoxes block101W1 block101W2 block101W3 block101W4 block101S1 block101S2 block101S3 block101S4

theorem block101LeftParamsCertificate_eq_true :
    block101LeftParamsCertificate = true := by
  native_decide

theorem block101_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block101LeftL : ℝ) (block101LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block101S1 : ℝ))
    (hy2ne : y ≠ (block101S2 : ℝ))
    (hy3ne : y ≠ (block101S3 : ℝ))
    (hy4ne : y ≠ (block101S4 : ℝ)) :
    0 < block101V y := by
  have hcert := block101LeftCertificate_eq_true
  unfold block101LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block101LeftBoxes) (lo := block101LeftL) (hi := block101LeftR)
    (w1 := block101W1) (w2 := block101W2) (w3 := block101W3) (w4 := block101W4)
    (s1 := block101S1) (s2 := block101S2) (s3 := block101S3) (s4 := block101S4)
    hboxes hcover block101LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block101RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block101RightChunk000 block101W1 block101W2 block101W3 block101W4 block101S1 block101S2 block101S3 block101S4

theorem block101RightChunk000ParamsCertificate_eq_true :
    block101RightChunk000ParamsCertificate = true := by
  native_decide

theorem block101_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block101RightChunk000L : ℝ) (block101RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block101S1 : ℝ))
    (hy2ne : y ≠ (block101S2 : ℝ))
    (hy3ne : y ≠ (block101S3 : ℝ))
    (hy4ne : y ≠ (block101S4 : ℝ)) :
    0 < block101V y := by
  have hcert := block101RightChunk000Certificate_eq_true
  unfold block101RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block101RightChunk000) (lo := block101RightChunk000L) (hi := block101RightChunk000R)
    (w1 := block101W1) (w2 := block101W2) (w3 := block101W3) (w4 := block101W4)
    (s1 := block101S1) (s2 := block101S2) (s3 := block101S3) (s4 := block101S4)
    hboxes hcover block101RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block101_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block101RightL : ℝ) (block101RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block101S1 : ℝ))
    (hy2ne : y ≠ (block101S2 : ℝ))
    (hy3ne : y ≠ (block101S3 : ℝ))
    (hy4ne : y ≠ (block101S4 : ℝ)) :
    0 < block101V y := by
  have hL : (block101RightChunk000L : ℝ) = (block101RightL : ℝ) := by
    norm_num [block101RightChunk000L, block101RightL]
  have hR : (block101RightChunk000R : ℝ) = (block101RightR : ℝ) := by
    norm_num [block101RightChunk000R, block101RightR]
  have hyc : y ∈ Icc (block101RightChunk000L : ℝ) (block101RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block101_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block101_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block101LeftL : ℝ) (block101LeftR : ℝ) →
    y ≠ 0 → y ≠ (block101S1 : ℝ) → y ≠ (block101S2 : ℝ) →
    y ≠ (block101S3 : ℝ) → y ≠ (block101S4 : ℝ) → 0 < block101V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block101RightL : ℝ) (block101RightR : ℝ) →
    y ≠ 0 → y ≠ (block101S1 : ℝ) → y ≠ (block101S2 : ℝ) →
    y ≠ (block101S3 : ℝ) → y ≠ (block101S4 : ℝ) → 0 < block101V y)

theorem block101_reallog_certificate_proof :
    block101_reallog_certificate := by
  exact ⟨block101_left_V_pos, block101_right_V_pos⟩

end Block101
end M1817475
end Erdos1038Lean
