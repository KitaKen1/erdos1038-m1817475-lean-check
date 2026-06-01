import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block248

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block248

open Set

def block248W1 : Rat := ((8550291642847413 : Rat) / 10000000000000000)
def block248W2 : Rat := ((8713208822094119 : Rat) / 100000000000000000)
def block248W3 : Rat := ((2326808457861917 : Rat) / 50000000000000000)
def block248W4 : Rat := ((50727624133991 : Rat) / 250000000000000)
def block248S1 : Rat := ((18174751 : Rat) / 10000000)
def block248S2 : Rat := ((511587 : Rat) / 200000)
def block248S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block248S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block248V (y : ℝ) : ℝ :=
  ratPotential block248W1 block248W2 block248W3 block248W4 block248S1 block248S2 block248S3 block248S4 y

def block248LeftParamsCertificate : Bool :=
  allBoxesSameParams block248LeftBoxes block248W1 block248W2 block248W3 block248W4 block248S1 block248S2 block248S3 block248S4

theorem block248LeftParamsCertificate_eq_true :
    block248LeftParamsCertificate = true := by
  native_decide

theorem block248_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block248LeftL : ℝ) (block248LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block248S1 : ℝ))
    (hy2ne : y ≠ (block248S2 : ℝ))
    (hy3ne : y ≠ (block248S3 : ℝ))
    (hy4ne : y ≠ (block248S4 : ℝ)) :
    0 < block248V y := by
  have hcert := block248LeftCertificate_eq_true
  unfold block248LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block248LeftBoxes) (lo := block248LeftL) (hi := block248LeftR)
    (w1 := block248W1) (w2 := block248W2) (w3 := block248W3) (w4 := block248W4)
    (s1 := block248S1) (s2 := block248S2) (s3 := block248S3) (s4 := block248S4)
    hboxes hcover block248LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block248RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block248RightChunk000 block248W1 block248W2 block248W3 block248W4 block248S1 block248S2 block248S3 block248S4

theorem block248RightChunk000ParamsCertificate_eq_true :
    block248RightChunk000ParamsCertificate = true := by
  native_decide

theorem block248_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block248RightChunk000L : ℝ) (block248RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block248S1 : ℝ))
    (hy2ne : y ≠ (block248S2 : ℝ))
    (hy3ne : y ≠ (block248S3 : ℝ))
    (hy4ne : y ≠ (block248S4 : ℝ)) :
    0 < block248V y := by
  have hcert := block248RightChunk000Certificate_eq_true
  unfold block248RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block248RightChunk000) (lo := block248RightChunk000L) (hi := block248RightChunk000R)
    (w1 := block248W1) (w2 := block248W2) (w3 := block248W3) (w4 := block248W4)
    (s1 := block248S1) (s2 := block248S2) (s3 := block248S3) (s4 := block248S4)
    hboxes hcover block248RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block248_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block248RightL : ℝ) (block248RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block248S1 : ℝ))
    (hy2ne : y ≠ (block248S2 : ℝ))
    (hy3ne : y ≠ (block248S3 : ℝ))
    (hy4ne : y ≠ (block248S4 : ℝ)) :
    0 < block248V y := by
  have hL : (block248RightChunk000L : ℝ) = (block248RightL : ℝ) := by
    norm_num [block248RightChunk000L, block248RightL]
  have hR : (block248RightChunk000R : ℝ) = (block248RightR : ℝ) := by
    norm_num [block248RightChunk000R, block248RightR]
  have hyc : y ∈ Icc (block248RightChunk000L : ℝ) (block248RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block248_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block248_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block248LeftL : ℝ) (block248LeftR : ℝ) →
    y ≠ 0 → y ≠ (block248S1 : ℝ) → y ≠ (block248S2 : ℝ) →
    y ≠ (block248S3 : ℝ) → y ≠ (block248S4 : ℝ) → 0 < block248V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block248RightL : ℝ) (block248RightR : ℝ) →
    y ≠ 0 → y ≠ (block248S1 : ℝ) → y ≠ (block248S2 : ℝ) →
    y ≠ (block248S3 : ℝ) → y ≠ (block248S4 : ℝ) → 0 < block248V y)

theorem block248_reallog_certificate_proof :
    block248_reallog_certificate := by
  exact ⟨block248_left_V_pos, block248_right_V_pos⟩

end Block248
end M1817475
end Erdos1038Lean
