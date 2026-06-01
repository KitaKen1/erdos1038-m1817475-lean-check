import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block386

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block386

open Set

def block386W1 : Rat := ((8391843467619307 : Rat) / 10000000000000000)
def block386W2 : Rat := ((23076484475740223 : Rat) / 500000000000000000)
def block386W3 : Rat := ((1000732136480147 : Rat) / 6250000000000000)
def block386W4 : Rat := ((140808450078083 : Rat) / 1000000000000000)
def block386S1 : Rat := ((18174751 : Rat) / 10000000)
def block386S2 : Rat := ((511587 : Rat) / 200000)
def block386S3 : Rat := ((132587601875000000051 : Rat) / 50000000000000000000)
def block386S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block386V (y : ℝ) : ℝ :=
  ratPotential block386W1 block386W2 block386W3 block386W4 block386S1 block386S2 block386S3 block386S4 y

def block386LeftParamsCertificate : Bool :=
  allBoxesSameParams block386LeftBoxes block386W1 block386W2 block386W3 block386W4 block386S1 block386S2 block386S3 block386S4

theorem block386LeftParamsCertificate_eq_true :
    block386LeftParamsCertificate = true := by
  native_decide

theorem block386_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block386LeftL : ℝ) (block386LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block386S1 : ℝ))
    (hy2ne : y ≠ (block386S2 : ℝ))
    (hy3ne : y ≠ (block386S3 : ℝ))
    (hy4ne : y ≠ (block386S4 : ℝ)) :
    0 < block386V y := by
  have hcert := block386LeftCertificate_eq_true
  unfold block386LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block386LeftBoxes) (lo := block386LeftL) (hi := block386LeftR)
    (w1 := block386W1) (w2 := block386W2) (w3 := block386W3) (w4 := block386W4)
    (s1 := block386S1) (s2 := block386S2) (s3 := block386S3) (s4 := block386S4)
    hboxes hcover block386LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block386RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block386RightChunk000 block386W1 block386W2 block386W3 block386W4 block386S1 block386S2 block386S3 block386S4

theorem block386RightChunk000ParamsCertificate_eq_true :
    block386RightChunk000ParamsCertificate = true := by
  native_decide

theorem block386_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block386RightChunk000L : ℝ) (block386RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block386S1 : ℝ))
    (hy2ne : y ≠ (block386S2 : ℝ))
    (hy3ne : y ≠ (block386S3 : ℝ))
    (hy4ne : y ≠ (block386S4 : ℝ)) :
    0 < block386V y := by
  have hcert := block386RightChunk000Certificate_eq_true
  unfold block386RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block386RightChunk000) (lo := block386RightChunk000L) (hi := block386RightChunk000R)
    (w1 := block386W1) (w2 := block386W2) (w3 := block386W3) (w4 := block386W4)
    (s1 := block386S1) (s2 := block386S2) (s3 := block386S3) (s4 := block386S4)
    hboxes hcover block386RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block386_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block386RightL : ℝ) (block386RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block386S1 : ℝ))
    (hy2ne : y ≠ (block386S2 : ℝ))
    (hy3ne : y ≠ (block386S3 : ℝ))
    (hy4ne : y ≠ (block386S4 : ℝ)) :
    0 < block386V y := by
  have hL : (block386RightChunk000L : ℝ) = (block386RightL : ℝ) := by
    norm_num [block386RightChunk000L, block386RightL]
  have hR : (block386RightChunk000R : ℝ) = (block386RightR : ℝ) := by
    norm_num [block386RightChunk000R, block386RightR]
  have hyc : y ∈ Icc (block386RightChunk000L : ℝ) (block386RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block386_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block386_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block386LeftL : ℝ) (block386LeftR : ℝ) →
    y ≠ 0 → y ≠ (block386S1 : ℝ) → y ≠ (block386S2 : ℝ) →
    y ≠ (block386S3 : ℝ) → y ≠ (block386S4 : ℝ) → 0 < block386V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block386RightL : ℝ) (block386RightR : ℝ) →
    y ≠ 0 → y ≠ (block386S1 : ℝ) → y ≠ (block386S2 : ℝ) →
    y ≠ (block386S3 : ℝ) → y ≠ (block386S4 : ℝ) → 0 < block386V y)

theorem block386_reallog_certificate_proof :
    block386_reallog_certificate := by
  exact ⟨block386_left_V_pos, block386_right_V_pos⟩

end Block386
end M1817475
end Erdos1038Lean
