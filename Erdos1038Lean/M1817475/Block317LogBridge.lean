import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block317

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block317

open Set

def block317W1 : Rat := ((9500216801353673 : Rat) / 10000000000000000)
def block317W2 : Rat := ((3253200780044583 : Rat) / 50000000000000000)
def block317W3 : Rat := ((2554316083842521 : Rat) / 10000000000000000)
def block317W4 : Rat := (0 : Rat)
def block317S1 : Rat := ((18174751 : Rat) / 10000000)
def block317S2 : Rat := ((511587 : Rat) / 200000)
def block317S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block317S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block317V (y : ℝ) : ℝ :=
  ratPotential block317W1 block317W2 block317W3 block317W4 block317S1 block317S2 block317S3 block317S4 y

def block317LeftParamsCertificate : Bool :=
  allBoxesSameParams block317LeftBoxes block317W1 block317W2 block317W3 block317W4 block317S1 block317S2 block317S3 block317S4

theorem block317LeftParamsCertificate_eq_true :
    block317LeftParamsCertificate = true := by
  native_decide

theorem block317_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block317LeftL : ℝ) (block317LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block317S1 : ℝ))
    (hy2ne : y ≠ (block317S2 : ℝ))
    (hy3ne : y ≠ (block317S3 : ℝ))
    (hy4ne : y ≠ (block317S4 : ℝ)) :
    0 < block317V y := by
  have hcert := block317LeftCertificate_eq_true
  unfold block317LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block317LeftBoxes) (lo := block317LeftL) (hi := block317LeftR)
    (w1 := block317W1) (w2 := block317W2) (w3 := block317W3) (w4 := block317W4)
    (s1 := block317S1) (s2 := block317S2) (s3 := block317S3) (s4 := block317S4)
    hboxes hcover block317LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block317RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block317RightChunk000 block317W1 block317W2 block317W3 block317W4 block317S1 block317S2 block317S3 block317S4

theorem block317RightChunk000ParamsCertificate_eq_true :
    block317RightChunk000ParamsCertificate = true := by
  native_decide

theorem block317_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block317RightChunk000L : ℝ) (block317RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block317S1 : ℝ))
    (hy2ne : y ≠ (block317S2 : ℝ))
    (hy3ne : y ≠ (block317S3 : ℝ))
    (hy4ne : y ≠ (block317S4 : ℝ)) :
    0 < block317V y := by
  have hcert := block317RightChunk000Certificate_eq_true
  unfold block317RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block317RightChunk000) (lo := block317RightChunk000L) (hi := block317RightChunk000R)
    (w1 := block317W1) (w2 := block317W2) (w3 := block317W3) (w4 := block317W4)
    (s1 := block317S1) (s2 := block317S2) (s3 := block317S3) (s4 := block317S4)
    hboxes hcover block317RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block317_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block317RightL : ℝ) (block317RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block317S1 : ℝ))
    (hy2ne : y ≠ (block317S2 : ℝ))
    (hy3ne : y ≠ (block317S3 : ℝ))
    (hy4ne : y ≠ (block317S4 : ℝ)) :
    0 < block317V y := by
  have hL : (block317RightChunk000L : ℝ) = (block317RightL : ℝ) := by
    norm_num [block317RightChunk000L, block317RightL]
  have hR : (block317RightChunk000R : ℝ) = (block317RightR : ℝ) := by
    norm_num [block317RightChunk000R, block317RightR]
  have hyc : y ∈ Icc (block317RightChunk000L : ℝ) (block317RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block317_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block317_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block317LeftL : ℝ) (block317LeftR : ℝ) →
    y ≠ 0 → y ≠ (block317S1 : ℝ) → y ≠ (block317S2 : ℝ) →
    y ≠ (block317S3 : ℝ) → y ≠ (block317S4 : ℝ) → 0 < block317V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block317RightL : ℝ) (block317RightR : ℝ) →
    y ≠ 0 → y ≠ (block317S1 : ℝ) → y ≠ (block317S2 : ℝ) →
    y ≠ (block317S3 : ℝ) → y ≠ (block317S4 : ℝ) → 0 < block317V y)

theorem block317_reallog_certificate_proof :
    block317_reallog_certificate := by
  exact ⟨block317_left_V_pos, block317_right_V_pos⟩

end Block317
end M1817475
end Erdos1038Lean
