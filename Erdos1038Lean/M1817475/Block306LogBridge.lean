import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block306

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block306

open Set

def block306W1 : Rat := ((9819114716366159 : Rat) / 10000000000000000)
def block306W2 : Rat := ((5340425090548557 : Rat) / 100000000000000000)
def block306W3 : Rat := ((1327843083731817 : Rat) / 5000000000000000)
def block306W4 : Rat := (0 : Rat)
def block306S1 : Rat := ((18174751 : Rat) / 10000000)
def block306S2 : Rat := ((511587 : Rat) / 200000)
def block306S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block306S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block306V (y : ℝ) : ℝ :=
  ratPotential block306W1 block306W2 block306W3 block306W4 block306S1 block306S2 block306S3 block306S4 y

def block306LeftParamsCertificate : Bool :=
  allBoxesSameParams block306LeftBoxes block306W1 block306W2 block306W3 block306W4 block306S1 block306S2 block306S3 block306S4

theorem block306LeftParamsCertificate_eq_true :
    block306LeftParamsCertificate = true := by
  native_decide

theorem block306_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block306LeftL : ℝ) (block306LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block306S1 : ℝ))
    (hy2ne : y ≠ (block306S2 : ℝ))
    (hy3ne : y ≠ (block306S3 : ℝ))
    (hy4ne : y ≠ (block306S4 : ℝ)) :
    0 < block306V y := by
  have hcert := block306LeftCertificate_eq_true
  unfold block306LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block306LeftBoxes) (lo := block306LeftL) (hi := block306LeftR)
    (w1 := block306W1) (w2 := block306W2) (w3 := block306W3) (w4 := block306W4)
    (s1 := block306S1) (s2 := block306S2) (s3 := block306S3) (s4 := block306S4)
    hboxes hcover block306LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block306RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block306RightChunk000 block306W1 block306W2 block306W3 block306W4 block306S1 block306S2 block306S3 block306S4

theorem block306RightChunk000ParamsCertificate_eq_true :
    block306RightChunk000ParamsCertificate = true := by
  native_decide

theorem block306_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block306RightChunk000L : ℝ) (block306RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block306S1 : ℝ))
    (hy2ne : y ≠ (block306S2 : ℝ))
    (hy3ne : y ≠ (block306S3 : ℝ))
    (hy4ne : y ≠ (block306S4 : ℝ)) :
    0 < block306V y := by
  have hcert := block306RightChunk000Certificate_eq_true
  unfold block306RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block306RightChunk000) (lo := block306RightChunk000L) (hi := block306RightChunk000R)
    (w1 := block306W1) (w2 := block306W2) (w3 := block306W3) (w4 := block306W4)
    (s1 := block306S1) (s2 := block306S2) (s3 := block306S3) (s4 := block306S4)
    hboxes hcover block306RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block306_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block306RightL : ℝ) (block306RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block306S1 : ℝ))
    (hy2ne : y ≠ (block306S2 : ℝ))
    (hy3ne : y ≠ (block306S3 : ℝ))
    (hy4ne : y ≠ (block306S4 : ℝ)) :
    0 < block306V y := by
  have hL : (block306RightChunk000L : ℝ) = (block306RightL : ℝ) := by
    norm_num [block306RightChunk000L, block306RightL]
  have hR : (block306RightChunk000R : ℝ) = (block306RightR : ℝ) := by
    norm_num [block306RightChunk000R, block306RightR]
  have hyc : y ∈ Icc (block306RightChunk000L : ℝ) (block306RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block306_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block306_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block306LeftL : ℝ) (block306LeftR : ℝ) →
    y ≠ 0 → y ≠ (block306S1 : ℝ) → y ≠ (block306S2 : ℝ) →
    y ≠ (block306S3 : ℝ) → y ≠ (block306S4 : ℝ) → 0 < block306V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block306RightL : ℝ) (block306RightR : ℝ) →
    y ≠ 0 → y ≠ (block306S1 : ℝ) → y ≠ (block306S2 : ℝ) →
    y ≠ (block306S3 : ℝ) → y ≠ (block306S4 : ℝ) → 0 < block306V y)

theorem block306_reallog_certificate_proof :
    block306_reallog_certificate := by
  exact ⟨block306_left_V_pos, block306_right_V_pos⟩

end Block306
end M1817475
end Erdos1038Lean
