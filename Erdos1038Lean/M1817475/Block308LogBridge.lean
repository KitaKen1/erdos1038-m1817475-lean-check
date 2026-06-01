import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block308

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block308

open Set

def block308W1 : Rat := ((48808347580043 : Rat) / 50000000000000)
def block308W2 : Rat := ((3466224433312951 : Rat) / 62500000000000000)
def block308W3 : Rat := ((26375409287497287 : Rat) / 100000000000000000)
def block308W4 : Rat := (0 : Rat)
def block308S1 : Rat := ((18174751 : Rat) / 10000000)
def block308S2 : Rat := ((511587 : Rat) / 200000)
def block308S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block308S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block308V (y : ℝ) : ℝ :=
  ratPotential block308W1 block308W2 block308W3 block308W4 block308S1 block308S2 block308S3 block308S4 y

def block308LeftParamsCertificate : Bool :=
  allBoxesSameParams block308LeftBoxes block308W1 block308W2 block308W3 block308W4 block308S1 block308S2 block308S3 block308S4

theorem block308LeftParamsCertificate_eq_true :
    block308LeftParamsCertificate = true := by
  native_decide

theorem block308_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block308LeftL : ℝ) (block308LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block308S1 : ℝ))
    (hy2ne : y ≠ (block308S2 : ℝ))
    (hy3ne : y ≠ (block308S3 : ℝ))
    (hy4ne : y ≠ (block308S4 : ℝ)) :
    0 < block308V y := by
  have hcert := block308LeftCertificate_eq_true
  unfold block308LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block308LeftBoxes) (lo := block308LeftL) (hi := block308LeftR)
    (w1 := block308W1) (w2 := block308W2) (w3 := block308W3) (w4 := block308W4)
    (s1 := block308S1) (s2 := block308S2) (s3 := block308S3) (s4 := block308S4)
    hboxes hcover block308LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block308RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block308RightChunk000 block308W1 block308W2 block308W3 block308W4 block308S1 block308S2 block308S3 block308S4

theorem block308RightChunk000ParamsCertificate_eq_true :
    block308RightChunk000ParamsCertificate = true := by
  native_decide

theorem block308_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block308RightChunk000L : ℝ) (block308RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block308S1 : ℝ))
    (hy2ne : y ≠ (block308S2 : ℝ))
    (hy3ne : y ≠ (block308S3 : ℝ))
    (hy4ne : y ≠ (block308S4 : ℝ)) :
    0 < block308V y := by
  have hcert := block308RightChunk000Certificate_eq_true
  unfold block308RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block308RightChunk000) (lo := block308RightChunk000L) (hi := block308RightChunk000R)
    (w1 := block308W1) (w2 := block308W2) (w3 := block308W3) (w4 := block308W4)
    (s1 := block308S1) (s2 := block308S2) (s3 := block308S3) (s4 := block308S4)
    hboxes hcover block308RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block308_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block308RightL : ℝ) (block308RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block308S1 : ℝ))
    (hy2ne : y ≠ (block308S2 : ℝ))
    (hy3ne : y ≠ (block308S3 : ℝ))
    (hy4ne : y ≠ (block308S4 : ℝ)) :
    0 < block308V y := by
  have hL : (block308RightChunk000L : ℝ) = (block308RightL : ℝ) := by
    norm_num [block308RightChunk000L, block308RightL]
  have hR : (block308RightChunk000R : ℝ) = (block308RightR : ℝ) := by
    norm_num [block308RightChunk000R, block308RightR]
  have hyc : y ∈ Icc (block308RightChunk000L : ℝ) (block308RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block308_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block308_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block308LeftL : ℝ) (block308LeftR : ℝ) →
    y ≠ 0 → y ≠ (block308S1 : ℝ) → y ≠ (block308S2 : ℝ) →
    y ≠ (block308S3 : ℝ) → y ≠ (block308S4 : ℝ) → 0 < block308V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block308RightL : ℝ) (block308RightR : ℝ) →
    y ≠ 0 → y ≠ (block308S1 : ℝ) → y ≠ (block308S2 : ℝ) →
    y ≠ (block308S3 : ℝ) → y ≠ (block308S4 : ℝ) → 0 < block308V y)

theorem block308_reallog_certificate_proof :
    block308_reallog_certificate := by
  exact ⟨block308_left_V_pos, block308_right_V_pos⟩

end Block308
end M1817475
end Erdos1038Lean
