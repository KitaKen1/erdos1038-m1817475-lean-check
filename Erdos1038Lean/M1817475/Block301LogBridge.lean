import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block301

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block301

open Set

def block301W1 : Rat := ((9961690344739003 : Rat) / 10000000000000000)
def block301W2 : Rat := ((1209732569851063 : Rat) / 25000000000000000)
def block301W3 : Rat := ((337562381684057 : Rat) / 1250000000000000)
def block301W4 : Rat := (0 : Rat)
def block301S1 : Rat := ((18174751 : Rat) / 10000000)
def block301S2 : Rat := ((511587 : Rat) / 200000)
def block301S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block301S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block301V (y : ℝ) : ℝ :=
  ratPotential block301W1 block301W2 block301W3 block301W4 block301S1 block301S2 block301S3 block301S4 y

def block301LeftParamsCertificate : Bool :=
  allBoxesSameParams block301LeftBoxes block301W1 block301W2 block301W3 block301W4 block301S1 block301S2 block301S3 block301S4

theorem block301LeftParamsCertificate_eq_true :
    block301LeftParamsCertificate = true := by
  native_decide

theorem block301_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block301LeftL : ℝ) (block301LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block301S1 : ℝ))
    (hy2ne : y ≠ (block301S2 : ℝ))
    (hy3ne : y ≠ (block301S3 : ℝ))
    (hy4ne : y ≠ (block301S4 : ℝ)) :
    0 < block301V y := by
  have hcert := block301LeftCertificate_eq_true
  unfold block301LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block301LeftBoxes) (lo := block301LeftL) (hi := block301LeftR)
    (w1 := block301W1) (w2 := block301W2) (w3 := block301W3) (w4 := block301W4)
    (s1 := block301S1) (s2 := block301S2) (s3 := block301S3) (s4 := block301S4)
    hboxes hcover block301LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block301RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block301RightChunk000 block301W1 block301W2 block301W3 block301W4 block301S1 block301S2 block301S3 block301S4

theorem block301RightChunk000ParamsCertificate_eq_true :
    block301RightChunk000ParamsCertificate = true := by
  native_decide

theorem block301_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block301RightChunk000L : ℝ) (block301RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block301S1 : ℝ))
    (hy2ne : y ≠ (block301S2 : ℝ))
    (hy3ne : y ≠ (block301S3 : ℝ))
    (hy4ne : y ≠ (block301S4 : ℝ)) :
    0 < block301V y := by
  have hcert := block301RightChunk000Certificate_eq_true
  unfold block301RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block301RightChunk000) (lo := block301RightChunk000L) (hi := block301RightChunk000R)
    (w1 := block301W1) (w2 := block301W2) (w3 := block301W3) (w4 := block301W4)
    (s1 := block301S1) (s2 := block301S2) (s3 := block301S3) (s4 := block301S4)
    hboxes hcover block301RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block301_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block301RightL : ℝ) (block301RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block301S1 : ℝ))
    (hy2ne : y ≠ (block301S2 : ℝ))
    (hy3ne : y ≠ (block301S3 : ℝ))
    (hy4ne : y ≠ (block301S4 : ℝ)) :
    0 < block301V y := by
  have hL : (block301RightChunk000L : ℝ) = (block301RightL : ℝ) := by
    norm_num [block301RightChunk000L, block301RightL]
  have hR : (block301RightChunk000R : ℝ) = (block301RightR : ℝ) := by
    norm_num [block301RightChunk000R, block301RightR]
  have hyc : y ∈ Icc (block301RightChunk000L : ℝ) (block301RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block301_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block301_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block301LeftL : ℝ) (block301LeftR : ℝ) →
    y ≠ 0 → y ≠ (block301S1 : ℝ) → y ≠ (block301S2 : ℝ) →
    y ≠ (block301S3 : ℝ) → y ≠ (block301S4 : ℝ) → 0 < block301V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block301RightL : ℝ) (block301RightR : ℝ) →
    y ≠ 0 → y ≠ (block301S1 : ℝ) → y ≠ (block301S2 : ℝ) →
    y ≠ (block301S3 : ℝ) → y ≠ (block301S4 : ℝ) → 0 < block301V y)

theorem block301_reallog_certificate_proof :
    block301_reallog_certificate := by
  exact ⟨block301_left_V_pos, block301_right_V_pos⟩

end Block301
end M1817475
end Erdos1038Lean
