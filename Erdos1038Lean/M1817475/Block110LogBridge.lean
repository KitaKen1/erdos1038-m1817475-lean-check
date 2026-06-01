import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block110

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block110

open Set

def block110W1 : Rat := ((2536923516702099 : Rat) / 1000000000000000)
def block110W2 : Rat := (0 : Rat)
def block110W3 : Rat := ((6465728604261413 : Rat) / 100000000000000000)
def block110W4 : Rat := ((909079197643261 : Rat) / 5000000000000000)
def block110S1 : Rat := ((18174751 : Rat) / 10000000)
def block110S2 : Rat := ((511587 : Rat) / 200000)
def block110S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block110S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block110V (y : ℝ) : ℝ :=
  ratPotential block110W1 block110W2 block110W3 block110W4 block110S1 block110S2 block110S3 block110S4 y

def block110LeftParamsCertificate : Bool :=
  allBoxesSameParams block110LeftBoxes block110W1 block110W2 block110W3 block110W4 block110S1 block110S2 block110S3 block110S4

theorem block110LeftParamsCertificate_eq_true :
    block110LeftParamsCertificate = true := by
  native_decide

theorem block110_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block110LeftL : ℝ) (block110LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block110S1 : ℝ))
    (hy2ne : y ≠ (block110S2 : ℝ))
    (hy3ne : y ≠ (block110S3 : ℝ))
    (hy4ne : y ≠ (block110S4 : ℝ)) :
    0 < block110V y := by
  have hcert := block110LeftCertificate_eq_true
  unfold block110LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block110LeftBoxes) (lo := block110LeftL) (hi := block110LeftR)
    (w1 := block110W1) (w2 := block110W2) (w3 := block110W3) (w4 := block110W4)
    (s1 := block110S1) (s2 := block110S2) (s3 := block110S3) (s4 := block110S4)
    hboxes hcover block110LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block110RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block110RightChunk000 block110W1 block110W2 block110W3 block110W4 block110S1 block110S2 block110S3 block110S4

theorem block110RightChunk000ParamsCertificate_eq_true :
    block110RightChunk000ParamsCertificate = true := by
  native_decide

theorem block110_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block110RightChunk000L : ℝ) (block110RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block110S1 : ℝ))
    (hy2ne : y ≠ (block110S2 : ℝ))
    (hy3ne : y ≠ (block110S3 : ℝ))
    (hy4ne : y ≠ (block110S4 : ℝ)) :
    0 < block110V y := by
  have hcert := block110RightChunk000Certificate_eq_true
  unfold block110RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block110RightChunk000) (lo := block110RightChunk000L) (hi := block110RightChunk000R)
    (w1 := block110W1) (w2 := block110W2) (w3 := block110W3) (w4 := block110W4)
    (s1 := block110S1) (s2 := block110S2) (s3 := block110S3) (s4 := block110S4)
    hboxes hcover block110RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block110_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block110RightL : ℝ) (block110RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block110S1 : ℝ))
    (hy2ne : y ≠ (block110S2 : ℝ))
    (hy3ne : y ≠ (block110S3 : ℝ))
    (hy4ne : y ≠ (block110S4 : ℝ)) :
    0 < block110V y := by
  have hL : (block110RightChunk000L : ℝ) = (block110RightL : ℝ) := by
    norm_num [block110RightChunk000L, block110RightL]
  have hR : (block110RightChunk000R : ℝ) = (block110RightR : ℝ) := by
    norm_num [block110RightChunk000R, block110RightR]
  have hyc : y ∈ Icc (block110RightChunk000L : ℝ) (block110RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block110_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block110_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block110LeftL : ℝ) (block110LeftR : ℝ) →
    y ≠ 0 → y ≠ (block110S1 : ℝ) → y ≠ (block110S2 : ℝ) →
    y ≠ (block110S3 : ℝ) → y ≠ (block110S4 : ℝ) → 0 < block110V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block110RightL : ℝ) (block110RightR : ℝ) →
    y ≠ 0 → y ≠ (block110S1 : ℝ) → y ≠ (block110S2 : ℝ) →
    y ≠ (block110S3 : ℝ) → y ≠ (block110S4 : ℝ) → 0 < block110V y)

theorem block110_reallog_certificate_proof :
    block110_reallog_certificate := by
  exact ⟨block110_left_V_pos, block110_right_V_pos⟩

end Block110
end M1817475
end Erdos1038Lean
